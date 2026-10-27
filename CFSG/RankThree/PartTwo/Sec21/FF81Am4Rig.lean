module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Cor
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Am4End

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

namespace Am4

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}
  {fL : K3 →* G} {g : G}

structure Setup (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ : G) (fL : K3 →* G) (g : G) : Prop where
  hD : Data b L B b₁ b₂ b₃ t₀
  inj : Function.Injective fL
  range : fL.range = L
  e0 : fL (nsElt 0) = b₃
  e1 : fL (nsElt 1) = b₂
  e2 : fL (nsElt 2) = b₁
  hg : GData b b₁ b₂ b₃ t₀ fL g

def thetaM (fL : K3 →* G) (g : G) : K3 →* G := (MulAut.conj g).toMonoidHom.comp fL

theorem thetaM_apply (x : K3) : thetaM fL g x = g * fL x * g⁻¹ := rfl

theorem Setup.thetaM_injective (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    Function.Injective (thetaM fL g) :=
  (MulAut.conj g).injective.comp hs.inj

theorem Setup.fL_mem (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (x : K3) : fL x ∈ L :=
  hs.range ▸ ⟨x, rfl⟩

theorem Setup.thetaM_tM (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : thetaM fL g tM = t₀ := hs.hg.tM

theorem Setup.thetaM_mem_cen (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (x : K3) :
    thetaM fL g x ∈ Cen b₃ := by
  have hb := hs.hD.h4.basis
  have hc : fL x * b = b * fL x := Subgroup.mem_centralizer_singleton_iff.mp
    (hb.hyp.hLC (hs.fL_mem x))
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [thetaM_apply, ← hs.hg.c0]
  calc g * fL x * g⁻¹ * (g * b * g⁻¹) = g * (fL x * b) * g⁻¹ := by group
    _ = g * (b * fL x) * g⁻¹ := by rw [hc]
    _ = g * b * g⁻¹ * (g * fL x * g⁻¹) := by group

theorem Setup.exists_thetaM_eq (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {r : G} (hr : r ∈ Cen b₃)
    {k : ℕ} (hk : r ^ (2 ^ k) = 1) : ∃ x : K3, thetaM fL g x = r := by
  have hb := hs.hD.h4.basis
  have hrc : r * b₃ = b₃ * r := Subgroup.mem_centralizer_singleton_iff.mp hr
  have hcen : g⁻¹ * r * g ∈ Cen b := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h0 : g * b * g⁻¹ = b₃ := hs.hg.c0
    calc g⁻¹ * r * g * b = g⁻¹ * (r * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (r * b₃) * g := by rw [h0]
      _ = g⁻¹ * (b₃ * r) * g := by rw [hrc]
      _ = b * (g⁻¹ * r * g) := by rw [← h0]; group
  have hpow : (g⁻¹ * r * g) ^ (2 ^ k) = 1 := by
    rw [show g⁻¹ * r * g = (MulAut.conj g⁻¹) r by simp [MulAut.conj_apply], ← map_pow, hk,
      map_one]
  have hL : g⁻¹ * r * g ∈ L := hb.mem_of_pow_two hcen hpow
  rw [← hs.range] at hL
  obtain ⟨x, hx⟩ := hL
  refine ⟨x, ?_⟩
  rw [thetaM_apply, hx]
  group

abbrev Rp (t₀ b₃ : G) : Subgroup G := Op 2 (Cen t₀) ⊓ Cen b₃

theorem Setup.card_Rp
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : Nat.card ↥(Rp t₀ b₃) = 32 := by
  have hD := hs.hD
  have hB := hD.h4.basis
  obtain ⟨-, -, h32, -⟩ := hD.h4.ff81_4_3_T kf_sp6Transv hD.h42
  obtain ⟨n, hnL, -, hn2, -⟩ := hB.monoL
  have heq : conjBy n (Op 2 (Cen t₀) ⊓ Cen b₂) = Op 2 (Cen t₀) ⊓ Cen b₃ := by
    rw [conjBy_op_two_inf_cen (hD.h4.L_le_cen hnL), hn2]
  show Nat.card ↥(Op 2 (Cen t₀) ⊓ Cen b₃) = 32
  rw [← heq, card_conjBy]
  exact h32

theorem Rp_normal {x : G} (hxt : x ∈ Cen t₀) (hxb : x ∈ Cen b₃) {r : G} (hr : r ∈ Rp t₀ b₃) :
    x * r * x⁻¹ ∈ Rp t₀ b₃ :=
  ⟨op_two_conj hxt hr.1, (Cen b₃).mul_mem ((Cen b₃).mul_mem hxb hr.2) ((Cen b₃).inv_mem hxb)⟩

theorem Rp_two_pow {r : G} (hr : r ∈ Rp t₀ b₃) : ∃ k : ℕ, r ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := op_two_isPGroup t₀ ⟨r, hr.1⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

def Qsub (fL : K3 →* G) (g t₀ b₃ : G) : Subgroup K3 := (Rp t₀ b₃).comap (thetaM fL g)

theorem mem_Qsub {x : K3} : x ∈ Qsub fL g t₀ b₃ ↔ thetaM fL g x ∈ Rp t₀ b₃ := Iff.rfl

theorem Setup.map_Qsub (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    (Qsub fL g t₀ b₃).map (thetaM fL g) = Rp t₀ b₃ := by
  rw [Qsub, Subgroup.map_comap_eq]
  refine inf_eq_right.mpr fun r hr => ?_
  obtain ⟨k, hk⟩ := Rp_two_pow hr
  exact hs.exists_thetaM_eq hr.2 hk

theorem Setup.card_Qsub
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : Nat.card ↥(Qsub fL g t₀ b₃) = 32 := by
  rw [← Subgroup.card_map_of_injective hs.thetaM_injective, hs.map_Qsub]
  exact hs.card_Rp

theorem Setup.Q_le_P (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : Qsub fL g t₀ b₃ ≤ P3 := by
  intro x hx
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  apply hs.thetaM_injective
  rw [map_mul, map_mul, hs.thetaM_tM]
  exact Subgroup.mem_centralizer_singleton_iff.mp ((op_two_le t₀) hx.1)

theorem Setup.thetaM_mem_cen_t₀ (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {x : K3} (hx : x ∈ P3) :
    thetaM fL g x ∈ Cen t₀ := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [← hs.thetaM_tM, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]

theorem Setup.Q_normal (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {x : K3} (hx : x ∈ P3) {q : K3}
    (hq : q ∈ Qsub fL g t₀ b₃) : x * q * x⁻¹ ∈ Qsub fL g t₀ b₃ := by
  rw [mem_Qsub, map_mul, map_mul, map_inv]
  exact Rp_normal (hs.thetaM_mem_cen_t₀ hx) (hs.thetaM_mem_cen x) hq

theorem Setup.Q_two_pow (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {q : K3}
    (hq : q ∈ Qsub fL g t₀ b₃) : ∃ k : ℕ, q ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := Rp_two_pow hq
  refine ⟨k, hs.thetaM_injective ?_⟩
  rw [map_pow, hk, map_one]

theorem Setup.Q_comm (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {x y : K3}
    (hx : x ∈ Qsub fL g t₀ b₃) (hy : y ∈ Qsub fL g t₀ b₃) : x * y = y * x := by
  apply hs.thetaM_injective
  rw [map_mul, map_mul]
  exact comm_of_isElemAb hs.hD.h43.2.1 _ hx.1 _ hy.1

theorem Setup.tM_mem_Q (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : tM ∈ Qsub fL g t₀ b₃ := by
  have hb := hs.hD.h4.basis
  rw [mem_Qsub, hs.thetaM_tM]
  refine ⟨mem_op_two_self hs.hD.h4.ht₀, ?_⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have := Subgroup.mem_centralizer_iff.mp hs.hD.h4.ht₀L b₃ hb.hb₃
  exact this.symm

theorem Setup.fL_tM_comm₂ (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : fL tM * b₂ = b₂ * fL tM := by
  rw [← hs.e1, ← map_mul, ← map_mul]
  exact congrArg fL (commute_longBlock (j := (2 : Fin 3)) (k := (1 : Fin 3)) (by decide)
    (sl2Upper 1) zThreeSL).eq

theorem Setup.fL_tM_comm₃ (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : fL tM * b₃ = b₃ * fL tM := by
  rw [← hs.e0, ← map_mul, ← map_mul]
  exact congrArg fL (commute_longBlock (j := (2 : Fin 3)) (k := (0 : Fin 3)) (by decide)
    (sl2Upper 1) zThreeSL).eq

theorem Setup.fL_tM_inv₁ (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    fL tM * b₁ * (fL tM)⁻¹ = b₁⁻¹ := by
  rw [← hs.e2, ← map_mul fL, ← map_inv fL, ← map_mul fL, tM_conj_nsElt, map_inv fL]

theorem Setup.orderOf_fL_tM (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : orderOf (fL tM) = 2 := by
  have h1 : fL tM ≠ 1 := by
    intro h
    have : tM = 1 := hs.inj (by rw [h, map_one])
    have h2 : ι₂ (sl2Upper 1) = ι₂ 1 := by rw [map_one]; exact this
    have h3 : sl2Upper (1 : ZMod 2) = 1 := ι₂_injective h2
    exact absurd h3 (by decide)
  exact orderOf_eq_prime (by rw [sq, ← map_mul, tM_mul_self, map_one]) h1

theorem Setup.transv
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    Nat.card ↥P3 = 23040 ∧ ∀ D : Subgroup K3, D ≤ P3 → IsPGroup 2 D →
      (∀ x ∈ P3, ∀ d ∈ D, x * d * x⁻¹ ∈ D) → D ≤ Subgroup.zpowers tM ∨ Nat.card D = 32 := by
  have hB := hs.hD.h4.basis
  have hset : ({b₃, b₁, b₂} : Set G) = {b₁, b₂, b₃} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hset' : ({b₃, b₃⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) = {b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have helem : IsElemAb 3 3 (Subgroup.closure {b₃, b₁, b₂}) := by rw [hset]; exact hB.elem
  have hself : L ⊓ CenS (Subgroup.closure {b₃, b₁, b₂}) = Subgroup.closure {b₃, b₁, b₂} := by
    rw [hset]; exact hB.selfcen
  have hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₃, b₁, b₂}) → ∀ x ∈ ({b₃, b₁, b₂} : Set G),
      n * x * n⁻¹ ∈ ({b₃, b₃⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) := by
    rw [hset, hset']; exact hB.monoL_stab
  obtain ⟨-, -, hK⟩ := kf_sp6Transv G L hB.hyp.model b₃ b₁ b₂ hB.hb₃ hB.hb₁ hB.hb₂ helem hself
    hmono
  obtain ⟨hcard, hdich⟩ := hK (fL tM) (hs.fL_mem tM) hs.orderOf_fL_tM hs.fL_tM_comm₃
    hs.fL_tM_comm₂ hs.fL_tM_inv₁
  have hmap : P3.map fL = L ⊓ Cen (fL tM) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hs.fL_mem y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hy]
    · rintro ⟨hxL, hxc⟩
      rw [← hs.range] at hxL
      obtain ⟨y, rfl⟩ := hxL
      refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (hs.inj ?_), rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxc
  refine ⟨?_, fun D hDP hD2 hDN => ?_⟩
  · rw [← Subgroup.card_map_of_injective hs.inj, hmap]; exact hcard
  · have hR : D.map fL ≤ L ⊓ Cen (fL tM) := by rw [← hmap]; exact Subgroup.map_mono hDP
    have hR2 : IsPGroup 2 ↥(D.map fL) := hD2.map fL
    have hRN : L ⊓ Cen (fL tM) ≤ Nor (D.map fL) := by
      intro x hx
      rw [← hmap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      obtain ⟨d, hd, rfl⟩ := hr
      exact ⟨y * d * y⁻¹, hDN y hy d hd, by rw [map_mul, map_mul, map_inv]⟩
    rcases hdich (D.map fL) hR hR2 hRN with h | ⟨h32, -⟩
    · left
      intro d hd
      have h1 : fL d ∈ Subgroup.zpowers (fL tM) := h ⟨d, hd, rfl⟩
      rw [← MonoidHom.map_zpowers] at h1
      obtain ⟨e, he, hed⟩ := h1
      exact (hs.inj hed) ▸ he
    · right
      rw [← Subgroup.card_map_of_injective hs.inj]; exact h32

abbrev S3 : Subgroup K3 := complSp (ZMod 2) (2 : Fin 3)

theorem S3_le_P3 : S3 ≤ P3 := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_tM_of_mem_complSp hy).eq.symm

theorem S3_normal_isPGroup_eq_bot {N : Subgroup K3} (hNS : N ≤ S3)
    (hN : ∀ y ∈ S3, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hp : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨φ⟩ := nonempty_sp4_mulEquiv_perm
  let e : ↥S3 ≃* Equiv.Perm (Fin 6) :=
    (complSpEquiv (K := ZMod 2) (m := 2) (2 : Fin 3)).symm.trans φ
  have hNn : (N.subgroupOf S3).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
  have hp' : IsPGroup 2 ↥(N.subgroupOf S3) :=
    hp.of_injective (Subgroup.subgroupOfEquivOfLe hNS).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNS).injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(N.subgroupOf S3) := hp'.isNilpotent
  have hsol : Group.IsSolvable ↥(N.subgroupOf S3) := inferInstance
  have hle := CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hNn hsol
  rw [CFSG.RankThree.CASymplecticSubfield.solvableRadical_eq_bot_of_mulEquiv_perm_six e,
    le_bot_iff] at hle
  rw [eq_bot_iff]
  intro n hn
  have : (⟨n, hNS hn⟩ : ↥S3) ∈ N.subgroupOf S3 := hn
  rw [hle, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem Setup.Q_inf_S
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) : Qsub fL g t₀ b₃ ⊓ S3 = ⊥ := by
  refine S3_normal_isPGroup_eq_bot inf_le_right (fun y hy n hn => ⟨?_, ?_⟩) ?_
  · exact hs.Q_normal (S3_le_P3 hy) hn.1
  · exact S3.mul_mem (S3.mul_mem hy hn.2) (S3.inv_mem hy)
  · intro x
    obtain ⟨k, hk⟩ := hs.Q_two_pow x.2.1
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem Setup.decomp
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    ∀ x ∈ P3, ∃ q ∈ Qsub fL g t₀ b₃, ∃ y ∈ S3, x = q * y := by
  set Q := Qsub fL g t₀ b₃ with hQ
  have hN : S3 ≤ Subgroup.normalizer (Q : Set K3) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun q hq => hs.Q_normal (S3_le_P3 hy) hq
  have hcardsup :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hN
  rw [inf_comm, hs.Q_inf_S, Subgroup.card_bot, mul_one, card_complSp, hs.card_Qsub] at hcardsup
  have hsup : S3 ⊔ Q = P3 :=
    Subgroup.eq_of_le_of_card_ge (sup_le S3_le_P3 hs.Q_le_P) (by
      rw [hs.transv.1, hcardsup])
  let U : Subgroup K3 :=
    { carrier := {x | ∃ q ∈ Q, ∃ y ∈ S3, x = q * y}
      mul_mem' := by
        rintro _ _ ⟨q₁, hq₁, y₁, hy₁, rfl⟩ ⟨q₂, hq₂, y₂, hy₂, rfl⟩
        refine ⟨q₁ * (y₁ * q₂ * y₁⁻¹), Q.mul_mem hq₁ (hs.Q_normal (S3_le_P3 hy₁) hq₂),
          y₁ * y₂, S3.mul_mem hy₁ hy₂, by group⟩
      one_mem' := ⟨1, Q.one_mem, 1, S3.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨q, hq, y, hy, rfl⟩
        refine ⟨y⁻¹ * q⁻¹ * y⁻¹⁻¹, ?_, y⁻¹, S3.inv_mem hy, by group⟩
        exact hs.Q_normal (S3_le_P3 (S3.inv_mem hy)) (Q.inv_mem hq) }
  have hU : S3 ⊔ Q ≤ U := sup_le (fun y hy => ⟨1, Q.one_mem, y, hy, by simp⟩)
    (fun q hq => ⟨q, hq, 1, S3.one_mem, by simp⟩)
  intro x hx
  exact hU (hsup ▸ hx)

theorem Setup.pow_mul_mem
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {q n : K3} (hq : q ∈ Qsub fL g t₀ b₃) (hn : n ∈ S3)
    (m : ℕ) : ∃ q' ∈ Qsub fL g t₀ b₃, (q * n) ^ m = q' * n ^ m := by
  induction m with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ m ih =>
    obtain ⟨q', hq', h⟩ := ih
    refine ⟨q' * (n ^ m * q * (n ^ m)⁻¹), Subgroup.mul_mem _ hq'
      (hs.Q_normal (S3_le_P3 (S3.pow_mem hn m)) hq), ?_⟩
    rw [pow_succ (q * n) m, h, pow_succ n m]
    group

theorem Setup.le_Q
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) {W : Subgroup K3} (hW : W ≤ P3) (hW2 : IsPGroup 2 W)
    (hWS : ∀ y ∈ S3, ∀ w ∈ W, y * w * y⁻¹ ∈ W) : W ≤ Qsub fL g t₀ b₃ := by
  set Q := Qsub fL g t₀ b₃ with hQ
  let WS : Subgroup K3 :=
    { carrier := {y | y ∈ S3 ∧ ∃ q ∈ Q, q * y ∈ W}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, q₁, hq₁, h₁⟩ ⟨hy₂, q₂, hq₂, h₂⟩
        refine ⟨S3.mul_mem hy₁ hy₂, q₁ * (y₁ * q₂ * y₁⁻¹),
          Q.mul_mem hq₁ (hs.Q_normal (S3_le_P3 hy₁) hq₂), ?_⟩
        have := W.mul_mem h₁ h₂
        convert this using 1
        group
      one_mem' := ⟨S3.one_mem, 1, Q.one_mem, by simpa using W.one_mem⟩
      inv_mem' := by
        rintro y ⟨hy, q, hq, h⟩
        refine ⟨S3.inv_mem hy, y⁻¹ * q⁻¹ * y⁻¹⁻¹,
          hs.Q_normal (S3_le_P3 (S3.inv_mem hy)) (Q.inv_mem hq), ?_⟩
        have := W.inv_mem h
        convert this using 1
        group }
  have hWSle : WS ≤ S3 := fun y hy => hy.1
  have hWSN : ∀ y ∈ S3, ∀ n ∈ WS, y * n * y⁻¹ ∈ WS := by
    rintro y hy n ⟨hn, q, hq, h⟩
    refine ⟨S3.mul_mem (S3.mul_mem hy hn) (S3.inv_mem hy), y * q * y⁻¹,
      hs.Q_normal (S3_le_P3 hy) hq, ?_⟩
    have := hWS y hy _ h
    convert this using 1
    group
  have hWS2 : IsPGroup 2 WS := by
    rintro ⟨n, hn, q, hq, h⟩
    obtain ⟨k, hk⟩ := hW2 ⟨q * n, h⟩
    have hk' : (q * n) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨q', hq', hq'e⟩ := hs.pow_mul_mem hq hn (2 ^ k)
    rw [hk'] at hq'e
    have hnk : n ^ (2 ^ k) = q'⁻¹ := eq_inv_of_mul_eq_one_right hq'e.symm
    have hmem : n ^ (2 ^ k) ∈ Q ⊓ S3 :=
      ⟨by rw [hnk]; exact Q.inv_mem hq', S3.pow_mem hn _⟩
    rw [hs.Q_inf_S, Subgroup.mem_bot] at hmem
    exact ⟨k, Subtype.ext (by simpa using hmem)⟩
  have hbot := S3_normal_isPGroup_eq_bot hWSle hWSN hWS2
  intro w hw
  obtain ⟨q, hq, y, hy, rfl⟩ := hs.decomp w (hW hw)
  have hyWS : y ∈ WS := ⟨hy, q, hq, hw⟩
  rw [hbot, Subgroup.mem_bot] at hyWS
  rw [hyWS, mul_one]
  exact hq

noncomputable def Phi2 {t₀ : G} (T : ThetaData t₀ fL) : ↥P3 →* G := T.Θ.comp shiftHom

theorem Phi2_apply {t₀ : G} (T : ThetaData t₀ fL) (x : ↥P3) :
    Phi2 T x = T.Θ (shiftHom x) := rfl

theorem tM_mem_P3 : tM ∈ P3 := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem tM_ne_one : tM ≠ 1 := by
  intro h
  have h2 : ι₂ (sl2Upper 1) = ι₂ 1 := by rw [map_one]; exact h
  exact absurd (ι₂_injective h2) (by decide)

theorem shiftHom_tM : shiftHom ⟨tM, tM_mem_P3⟩ = ⟨tvec, tvec_mem_Pvec⟩ :=
  Subtype.ext shiftEmb_tM

theorem Setup.agree_tM (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) :
    thetaM fL g tM = Phi2 T ⟨tM, tM_mem_P3⟩ := by
  rw [Phi2_apply, shiftHom_tM, T.tvec, hs.thetaM_tM]

theorem Setup.agree_S (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) {y : K3}
    (hy : y ∈ S3) : thetaM fL g y = Phi2 T ⟨y, S3_le_P3 hy⟩ := by
  have hy' : y ∈ embS.range := by rw [range_embS]; exact hy
  obtain ⟨z, rfl⟩ := hy'
  have h1 : shiftHom ⟨embS z, S3_le_P3 hy⟩ = initHom (embS' z) :=
    Subtype.ext (shiftEmb_embS z)
  rw [Phi2_apply, h1, T.init, thetaM_apply, hs.hg.S z]

theorem Setup.Phi2_mem_cen (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) (x : ↥P3) :
    Phi2 T x ∈ Cen b₃ := by
  have hcomm : shiftHom x * initHom (nsElt 0) = initHom (nsElt 0) * shiftHom x := by
    apply Subtype.ext
    show shiftEmb x.1 * initEmb (nsElt 0) = initEmb (nsElt 0) * shiftEmb x.1
    have h0 : initEmb (nsElt (K := ZMod 2) (n := 3) 0) = nsElt (K := ZMod 2) (n := 4) 0 :=
      initEmb_nsElt 0
    have hmem : shiftEmb x.1 ∈ complSp (ZMod 2) (0 : Fin 4) := by
      rw [← range_shiftEmb]; exact ⟨x.1, rfl⟩
    rw [h0]
    exact (commute_of_mem_longRootSp2_of_mem_complSp (k := (0 : Fin 4)) (x := nsElt 0)
      ⟨zThreeSL, rfl⟩ hmem).eq.symm
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [Phi2_apply, ← hs.e0, ← T.init, ← map_mul, ← map_mul, hcomm]

theorem Setup.exists_Q
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) {q : K3}
    (hq : q ∈ Qsub fL g t₀ b₃) :
    ∃ q' ∈ Qsub fL g t₀ b₃, thetaM fL g q' = Phi2 T ⟨q, hs.Q_le_P hq⟩ := by
  set Q := Qsub fL g t₀ b₃ with hQ
  let Q' : Subgroup ↥P3 := Q.subgroupOf P3
  let W : Subgroup K3 := (Q'.map (Phi2 T)).comap (thetaM fL g)
  have h2pow : ∀ x : ↥P3, x ∈ Q' → ∃ k : ℕ, (Phi2 T x) ^ (2 ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hs.Q_two_pow hx
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : x ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  set x₀ : ↥P3 := ⟨q, hs.Q_le_P hq⟩ with hx₀
  have hx₀Q : x₀ ∈ Q' := hq
  obtain ⟨k, hk⟩ := h2pow x₀ hx₀Q
  obtain ⟨x', hx'⟩ := hs.exists_thetaM_eq (hs.Phi2_mem_cen T x₀) hk
  have hx'W : x' ∈ W := ⟨x₀, hx₀Q, hx'.symm⟩
  have hWP : W ≤ P3 := by
    rintro x ⟨y, -, hy⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr (hs.thetaM_injective ?_)
    rw [map_mul, map_mul, hs.thetaM_tM, ← hy]
    exact Subgroup.mem_centralizer_singleton_iff.mp (T.cen _)
  have hW2 : IsPGroup 2 W := by
    rintro ⟨x, y, hy, hyx⟩
    obtain ⟨k, hk⟩ := h2pow y hy
    refine ⟨k, Subtype.ext (hs.thetaM_injective ?_)⟩
    show thetaM fL g (x ^ (2 ^ k)) = thetaM fL g 1
    rw [map_pow, map_one, ← hyx]
    exact hk
  have hWS : ∀ y ∈ S3, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro y hy w hw
    obtain ⟨q', hq', hq'w⟩ := hw
    have hmem : (⟨y, S3_le_P3 hy⟩ * q' * ⟨y, S3_le_P3 hy⟩⁻¹ : ↥P3) ∈ Q' := by
      have hq'' : (q' : K3) ∈ Q := hq'
      rw [Subgroup.mem_subgroupOf]
      have := hs.Q_normal (S3_le_P3 hy) hq''
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    refine ⟨_, hmem, ?_⟩
    have hy' := hs.agree_S T hy
    calc Phi2 T (⟨y, S3_le_P3 hy⟩ * q' * ⟨y, S3_le_P3 hy⟩⁻¹)
        = Phi2 T ⟨y, S3_le_P3 hy⟩ * Phi2 T q' * (Phi2 T ⟨y, S3_le_P3 hy⟩)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = thetaM fL g y * thetaM fL g w * (thetaM fL g y)⁻¹ := by rw [hq'w, hy']
      _ = thetaM fL g (y * w * y⁻¹) := by rw [map_mul, map_mul, map_inv]
  exact ⟨x', hs.le_Q hWP hW2 hWS hx'W, hx'⟩

theorem Setup.dich
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (D' : Subgroup ↥P3)
    (hD'Q : D' ≤ (Qsub fL g t₀ b₃).subgroupOf P3)
    (hD'S : ∀ s ∈ S3.subgroupOf P3, ∀ d ∈ D', s * d * s⁻¹ ∈ D') :
    D' ≤ Subgroup.zpowers (⟨tM, tM_mem_P3⟩ : ↥P3) ∨ D' = (Qsub fL g t₀ b₃).subgroupOf P3 := by
  set Q := Qsub fL g t₀ b₃ with hQ
  set D : Subgroup K3 := D'.map P3.subtype with hD
  have hDQ : D ≤ Q := by
    intro d hd
    obtain ⟨d', hd', hdd⟩ := Subgroup.mem_map.mp hd
    rw [← hdd]
    exact hD'Q hd'
  have hDP : D ≤ P3 := Subgroup.map_subtype_le _
  have hD2 : IsPGroup 2 D := by
    rintro ⟨d, hd⟩
    obtain ⟨k, hk⟩ := hs.Q_two_pow (hDQ hd)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hDS : ∀ y ∈ S3, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro y hy d hd
    obtain ⟨d', hd', hdd⟩ := Subgroup.mem_map.mp hd
    have hyS' : (⟨y, S3_le_P3 hy⟩ : ↥P3) ∈ S3.subgroupOf P3 := hy
    have hmem := hD'S _ hyS' d' hd'
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    rw [← hdd]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  have hDN : ∀ x ∈ P3, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    obtain ⟨q, hq, y, hy, rfl⟩ := hs.decomp x hx
    have h1 := hDS y hy d hd
    have h2 : q * (y * d * y⁻¹) * q⁻¹ = y * d * y⁻¹ := by
      rw [hs.Q_comm hq (hDQ h1)]; group
    rw [show q * y * d * (q * y)⁻¹ = q * (y * d * y⁻¹) * q⁻¹ by group, h2]
    exact h1
  rcases hs.transv.2 D hDP hD2 hDN with h | h
  · left
    intro d' hd'
    have hdD : (d' : K3) ∈ D := Subgroup.mem_map.mpr ⟨d', hd', rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h hdD)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simpa using hk
  · right
    have hDeq : D = Q := Subgroup.eq_of_le_of_card_ge hDQ (by rw [h, hs.card_Qsub])
    refine le_antisymm hD'Q (fun q' hq' => ?_)
    have hqD : (q' : K3) ∈ D := hDeq ▸ hq'
    obtain ⟨d', hd', hd'q⟩ := Subgroup.mem_map.mp hqD
    have hdq : d' = q' := Subtype.ext hd'q
    exact hdq ▸ hd'

theorem Setup.agree_Q
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) (q : ↥P3)
    (hq : q ∈ (Qsub fL g t₀ b₃).subgroupOf P3) : thetaM fL g q = Phi2 T q := by
  have hφ₁ : Function.Injective ((thetaM fL g).comp P3.subtype) :=
    hs.thetaM_injective.comp Subtype.val_injective
  refine eq_on_of_uniserial ((thetaM fL g).comp P3.subtype) (Phi2 T) hφ₁
    ((Qsub fL g t₀ b₃).subgroupOf P3) (S3.subgroupOf P3) ⟨tM, tM_mem_P3⟩ hs.tM_mem_Q ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ (hs.dich) q hq
  · intro x hx y hy
    exact Subtype.ext (hs.Q_comm hx hy)
  · intro s hs' q hq
    have hq' : (q : K3) ∈ Qsub fL g t₀ b₃ := hq
    have := hs.Q_normal s.2 hq'
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  · intro s hs'
    exact hs.agree_S T hs'
  · exact hs.agree_tM T
  · intro q hq
    obtain ⟨q₁, hq₁, h⟩ := hs.exists_Q T hq
    exact ⟨⟨q₁, hs.Q_le_P hq₁⟩, hq₁, h⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.Q_le_P).toEquiv]
    exact hs.card_Qsub
  · intro h
    exact tM_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext tM_mul_self

theorem Setup.agree
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) (x : ↥P3) :
    thetaM fL g x = Phi2 T x := by
  obtain ⟨q, hq, y, hy, hxy⟩ := hs.decomp x.1 x.2
  have hx : x = ⟨q, hs.Q_le_P hq⟩ * ⟨y, S3_le_P3 hy⟩ := Subtype.ext hxy
  have h1 : thetaM fL g q = Phi2 T ⟨q, hs.Q_le_P hq⟩ := hs.agree_Q T ⟨q, hs.Q_le_P hq⟩ hq
  have h2 : thetaM fL g y = Phi2 T ⟨y, S3_le_P3 hy⟩ := hs.agree_S T hy
  have h3 : thetaM fL g x.1 = thetaM fL g q * thetaM fL g y := by rw [hxy, map_mul]
  have h4 : Phi2 T x = Phi2 T ⟨q, hs.Q_le_P hq⟩ * Phi2 T ⟨y, S3_le_P3 hy⟩ := by
    rw [hx, map_mul]
  rw [h4, ← h1, ← h2, ← h3]

end Am4

end CFSG.RankThree.PartTwo.Sec21.FF81
