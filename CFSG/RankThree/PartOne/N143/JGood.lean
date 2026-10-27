module

public import CFSG.RankThree.PartOne.N143.Statements
public import CFSG.RankThree.PartOne.S12.Sec141Row
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cent_of_generic {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hp := h.prime
  have hZ := hG.center_pPrime
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R := h.restr_of_generic hG
  have hdvd : p ∣ Nat.card L := by
    have hEcard := R.card_E hp (Sec12Three.orderOf_c h) hcL
    have h3 := h.pow_three_dvd_card_E
    rw [hEcard] at h3
    have h4 : p ^ 2 ∣ Nat.card ↥(E ⊓ L) := by
      have : p * p ^ 2 ∣ p * Nat.card ↥(E ⊓ L) := by
        rw [← pow_succ', mul_comm]
        exact h3
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
    exact ((dvd_pow_self p (by norm_num)).trans h4).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = {x | x ∈ Subgroup.centralizer ({c} : Set G) ∧ x ^ p = 1} :=
    ⟨_, rfl⟩
  have hPM : Subgroup.closure S ≤ Subgroup.zpowers c ⊔ L := by
    refine (Subgroup.closure_le _).2 ?_
    rw [hS]
    rintro x ⟨hxc, hxp⟩
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x = p := orderOf_eq_prime hxp hx1
      have hxN : x ∈ cNormalizer c := by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcx : c * x = x * c := (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm
        exact (Commute.zpow_left (hcx : Commute c x) j).eq
      exact hG.pElements x hxN hord
  have hLP : L ≤ Subgroup.closure S := by
    refine (Sec13Base.le_closure_pElements hp hG.quasisimple hZ hdvd).trans
      (Subgroup.closure_mono ?_)
    rw [hS]
    rintro y ⟨hyL, hyp⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (Sec12Three.comm_c_L h y hyL).symm, hyp⟩
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hG.quasisimple.1
  have hZc : ∀ z ∈ Subgroup.zpowers c, ∀ w ∈ L ⊔ Subgroup.zpowers c, z * w = w * z := by
    intro z hz w hw
    obtain ⟨l, hl, z', hz', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun l hl z hz => (Sec12Three.zpowers_comm_L h z hz l hl).symm) hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    rw [← mul_assoc, (Sec12Three.zpowers_comm_L h _ hz l hl), mul_assoc, mul_assoc,
      (Commute.zpow_zpow_self c i j).eq]
  have hPP : ⁅Subgroup.closure S, Subgroup.closure S⁆ = L := by
    apply le_antisymm
    · calc ⁅Subgroup.closure S, Subgroup.closure S⁆
          ≤ ⁅L ⊔ Subgroup.zpowers c, L ⊔ Subgroup.zpowers c⁆ :=
            Subgroup.commutator_mono (hPM.trans_eq (sup_comm _ _)) (hPM.trans_eq (sup_comm _ _))
        _ ≤ ⁅L, L⁆ := Sec13Base.commutator_sup_le_of_central hZc
        _ = L := hperf
    · calc L = ⁅L, L⁆ := hperf.symm
        _ ≤ ⁅Subgroup.closure S, Subgroup.closure S⁆ := Subgroup.commutator_mono hLP hLP
  have hconjP : ∀ g ∈ Subgroup.centralizer ({c} : Set G),
      (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rw [hS]
    rintro y ⟨hyc, hyp⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact (Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hg hyc)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hg)
    · show (g * y * g⁻¹) ^ p = 1
      rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  have hconjL : ∀ g ∈ Subgroup.centralizer ({c} : Set G),
      L.map (MulAut.conj g).toMonoidHom ≤ L := by
    intro g hg
    rw [← hPP, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (hconjP g hg) (hconjP g hg)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact hconjL x hx ⟨l, hl, rfl⟩
  · intro hl
    have := hconjL x⁻¹ ((Subgroup.centralizer ({c} : Set G)).inv_mem hx) ⟨x * l * x⁻¹, hl, rfl⟩
    simpa [mul_assoc] using this

structure JGood (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G) : Prop where
  hyp : Sec12Hyp G p A c J A
  facts12 : Sec12Facts G p A c J A
  generic : Sec12TwoGeneric p c J A
  weyl : Nonempty (torusImage A J ≃* Equiv.Perm (Fin 3))
  model : IsLThreeTypeAt p J
  cent : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (J : Set G)
  mem : J ∈ thetaCompZeroStarE p A

theorem jGood_of_mem (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} (hctx : HessCtx p A c L)
    {J : Subgroup G} (hJ : J ∈ thetaCompZeroStarE p A) : ∃ c' : G, JGood p A c' J := by
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hctx.facts13.reinstantiate J hJ
  have hBA : B = A := by
    refine Subgroup.eq_of_le_of_card_ge hB.1 (le_of_eq ?_)
    rw [hctx.hyp.A_card, hB.2.2.1]
  rw [hBA] at h' hF'
  have hIz : J ∈ sectionTenZeroStar p A := Sec12Three.L_mem_zeroStar h'
  have hmodel : IsLThreeTypeAt p J := hctx.allL3 J hIz
  obtain ⟨hG, hweyl, -⟩ := Sec141Row.rowOne_data hRow1 h107 h109 h122 h' hmodel
  exact ⟨c', ⟨h', hF', hG, hweyl, hmodel, cent_of_generic h' hG, hJ⟩⟩

@[expose] def Tof (A J : Subgroup G) : Subgroup G := ⁅A, J ⊓ torusNormalizer A⁆

omit [Finite G] in
theorem Tof_le (A J : Subgroup G) : Tof A J ≤ A := by
  rw [Tof, Subgroup.commutator_le]
  intro a ha w hw
  have hwN : w ∈ torusNormalizer A := (Subgroup.mem_inf.1 hw).2
  have h1 : w * a⁻¹ * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hwN (a⁻¹)).1 (A.inv_mem ha)
  have : ⁅a, w⁆ = a * (w * a⁻¹ * w⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact A.mul_mem ha h1

variable {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G}

theorem JGood.A_eq (h : JGood p A c J) :
    A = Subgroup.zpowers c ⊔ Tof A J ∧ Subgroup.zpowers c ⊓ Tof A J = ⊥ := by
  rcases h.facts12.four.2 with h1 | ⟨⟨-, h2⟩, -⟩
  · exact h1
  · exfalso
    obtain ⟨e1⟩ := h.weyl
    obtain ⟨e2⟩ := h2
    have := Nat.card_congr (e1.symm.trans e2).toEquiv
    simp [Nat.card_eq_fintype_card, Fintype.card_perm] at this
    revert this
    decide

theorem JGood.card_Tof (h : JGood p A c J) : Nat.card (Tof A J) = p ^ 2 := by
  have hp := h.hyp.prime
  obtain ⟨hA, hdisj⟩ := h.A_eq
  have hcT : c ∉ Tof A J := fun hc => by
    have : c ∈ Subgroup.zpowers c ⊓ Tof A J := ⟨Subgroup.mem_zpowers c, hc⟩
    rw [hdisj] at this
    exact h.hyp.c_ne_one (Subgroup.mem_bot.1 this)
  have hfp : c ^ p = 1 := Sec12Three.pow_eq_one_of_mem_A h.hyp h.hyp.c_mem
  have hcomm : ∀ e ∈ Tof A J, e * c = c * e := fun e he =>
    Sec12Three.mul_comm_of_mem_A h.hyp (Tof_le A J he) h.hyp.c_mem
  have h1 := Planes.card_sup_zpowers hp (Tof A J) hfp hcT hcomm
  rw [sup_comm, ← hA, h.hyp.A_card] at h1
  have hp0 : 0 < p := hp.pos
  have : p * Nat.card (Tof A J) = p * p ^ 2 := by
    calc p * Nat.card (Tof A J) = Nat.card (Tof A J) * p := mul_comm _ _
      _ = p ^ 3 := h1.symm
      _ = p * p ^ 2 := by ring
  exact Nat.eq_of_mul_eq_mul_left hp0 this

@[expose] def IsScalarOn (A : Subgroup G) (u : G) : Prop :=
  ∃ k : ℕ, ∀ a ∈ A, u * a * u⁻¹ = a ^ k

theorem JGood.mem_cNormalizer_of_scalar (h : JGood p A c J) {u : G} (hu : IsScalarOn A u) :
    u ∈ cNormalizer c := by
  obtain ⟨k, hk⟩ := hu
  refine Subgroup.mem_normalizer_fintype (S := (Subgroup.zpowers c : Set G)) ?_
  intro n hn
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have : u * c ^ i * u⁻¹ = (u * c * u⁻¹) ^ i := (conj_zpow).symm
  rw [this, hk c h.hyp.c_mem]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) k) i

theorem JGood.mem_normalizer_of_scalar (h : JGood p A c J) {u : G} (hu : u ∈ torusNormalizer A)
    (hs : IsScalarOn A u) : u ∈ Subgroup.normalizer (J : Set G) :=
  h.facts12.twoB ⟨h.mem_cNormalizer_of_scalar hs, hu⟩

theorem JGood.mem_normalizer_mul_of_scalar (h : JGood p A c J) {j u : G} (hj : j ∈ J)
    (hu : u ∈ torusNormalizer A) (hs : IsScalarOn A u) :
    j * u ∈ Subgroup.normalizer (J : Set G) :=
  Subgroup.mul_mem _ (Subgroup.le_normalizer hj) (h.mem_normalizer_of_scalar hu hs)

theorem JGood.centralizer_A_le_normalizer (h : JGood p A c J) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J : Set G) := fun _ hx =>
  h.cent (Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 hx c h.hyp.c_mem).symm))

theorem JGood.conj_mem_inf_centralizer (h : JGood p A c J) {x d : G}
    (hx : x ∈ Subgroup.centralizer (A : Set G)) (hd : d ∈ J ⊓ Subgroup.centralizer (A : Set G)) :
    x * d * x⁻¹ ∈ J ⊓ Subgroup.centralizer (A : Set G) := by
  refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hd.2) (Subgroup.inv_mem _ hx)⟩
  exact (Subgroup.mem_normalizer_iff.1 (h.centralizer_A_le_normalizer hx) d).1 hd.1

end CFSG.RankThree.PartOne.N143
