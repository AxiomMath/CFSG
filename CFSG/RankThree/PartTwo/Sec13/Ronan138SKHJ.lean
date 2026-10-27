module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec13.Item137ProofM12
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Ronan138SNorm
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofCasesB
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_nine_dvd_card_sub_one {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) (h9 : ¬ Sec4.ModNine π (p ^ f)) :
    ¬ 9 ∣ Nat.card K - 1 := by
  rw [hK.card]
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  cases π
  · change p ^ f % 3 = 2 at hq
    change ¬ p ^ f % 9 = 8 at h9
    change ¬ 9 ∣ (p ^ f) ^ 2 - 1
    have h2 : (p ^ f) ^ 2 % 9 = 4 ∨ (p ^ f) ^ 2 % 9 = 7 := by
      rw [Nat.pow_mod]
      have : p ^ f % 9 = 2 ∨ p ^ f % 9 = 5 := by omega
      rcases this with h | h <;> rw [h] <;> norm_num
    have h3 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
    omega
  · change p ^ f % 3 = 1 at hq
    change ¬ p ^ f % 9 = 1 at h9
    change ¬ 9 ∣ p ^ f - 1
    omega

theorem isSolvable_inf_centralizer_of_hyp138 {A L E : Subgroup G} {c : G}
    (hH : Hyp138 A c L E) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) {d : G} (hdL : d ∈ L)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨h, hL3, hcE, hE3, -, hEN, -, -, hC⟩ := hH
  obtain ⟨p', e', _, he', hiso⟩ := hL3
  have hnot := not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he' hiso
  obtain ⟨π, p, f, K, _, hK, hq, φ, -⟩ := hC
  obtain ⟨π₀, K₀, _, hK₀, hq₀, ⟨φ₀⟩⟩ := exists_projImage_model he' hiso
  have hMod : ¬ Sec4.ModNine π (p ^ f) := by
    intro h9
    have := modNine_of_mulEquiv hK hq hK₀ hq₀ φ φ₀ h9
    cases π₀
    · exact hnot (Or.inr this)
    · exact hnot (Or.inl this)
  have h9 := not_nine_dvd_card_sub_one hK hq hMod
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π' := QuotientGroup.mk' θ with hπ'
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hdbar1 : π' d' ≠ 1 := by
    intro h1
    rw [hπ', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := Item134SylowBarProof.eq_one_of_mem_theta_of_pow h1 (k := 1) (by simpa using hd'3)
    exact hd1 (congrArg Subtype.val this)
  set y : Matrix.ProjGenLinGroup (Fin 3) K := (φ (π' d')).1 with hy
  have hyS : y ∈ CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ f) K) := (φ _).2
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← Subgroup.coe_pow, ← map_pow, ← map_pow, hd'3, map_one, map_one]
    rfl
  have hy1 : y ≠ 1 := by
    intro h1
    apply hdbar1
    have : φ (π' d') = 1 := Subtype.ext h1
    rwa [MulEquiv.map_eq_one_iff] at this
  have hsol := Sec15.KSL3Two.isSolvable_inf_centralizer hK hq h9 hyS hy3 hy1
  set Cbar := Subgroup.centralizer ({π' d'} : Set (↥L ⧸ θ)) with hCbar
  have hCsol : Group.IsSolvable ↥Cbar := by
    let ψ : ↥Cbar →* ↥(CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ f) K) ⊓
        Subgroup.centralizer ({y} : Set (Matrix.ProjGenLinGroup (Fin 3) K))) :=
      { toFun := fun z => ⟨(φ z).1, Subgroup.mem_inf.mpr ⟨(φ z).2, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2
          have h1 := congrArg (fun w => (φ w).1) hz
          simp only [map_mul, Subgroup.coe_mul] at h1
          exact h1⟩⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          simp }
    refine solvable_of_solvable_injective (f := ψ) (fun a b hab => ?_)
    have h1 : (φ a).1 = (φ b).1 := congrArg (fun w => w.1) hab
    exact Subtype.ext (φ.injective (Subtype.ext h1))
  set M := L ⊓ Subgroup.centralizer ({d} : Set G) with hM
  set g₀ : ↥M →* ↥L ⧸ θ := π'.comp (Subgroup.inclusion (inf_le_left : M ≤ L)) with hg₀
  have hg₀C : ∀ m : ↥M, g₀ m ∈ Cbar := by
    intro m
    rw [hCbar, Subgroup.mem_centralizer_singleton_iff, hg₀, MonoidHom.comp_apply, ← map_mul,
      ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp m.2).2)
  set g : ↥M →* ↥Cbar := g₀.codRestrict Cbar hg₀C with hg
  have hker : Group.IsSolvable ↥g.ker := by
    have hθs := (Sec6.theta_solvable_and_not_dvd L).1
    have hmem : ∀ m : ↥g.ker, ((m : ↥M) : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      intro m
      have hm := m.2
      rw [MonoidHom.mem_ker] at hm
      have h1 : g₀ m = 1 := congrArg Subtype.val hm
      rw [hg₀, MonoidHom.comp_apply, hπ', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    let ι : ↥g.ker →* ↥(inSubgroup (aschbacherSolvableCore 3) L) :=
      { toFun := fun m => ⟨((m : ↥M) : G), hmem m⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    refine solvable_of_solvable_injective (f := ι) (fun a b hab => ?_)
    have h1 : ((a : ↥M) : G) = ((b : ↥M) : G) :=
      congrArg (fun w : ↥(inSubgroup (aschbacherSolvableCore 3) L) => (w : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  exact solvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

theorem not_isSolvable_of_isQuasisimple' {T : Type} [Group T] (hq : CFSG.IsQuasisimple T) :
    ¬ Group.IsSolvable T := by
  intro hsol
  have : Group.IsPerfect T := hq.1
  obtain ⟨x, y, hxy⟩ := hq.2.2
  have : Nontrivial (T ⧸ Subgroup.center T) := by
    refine ⟨⟨x * y, y * x, hxy⟩⟩
  have : Group.IsSolvable (T ⧸ Subgroup.center T) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center T))
  exact Group.IsPerfect.not_isSolvable (T ⧸ Subgroup.center T) this

theorem false_of_hj
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15) (h48 : Sec4.Item4_8)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : E ⊓ L ∉ omegaA E) {e : G} {K : Subgroup G}
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (heF : e ∈ F)
    (hφ : Nonempty (lBarA e K E ≃*
      Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d := ⁅x, y⁆ with hd
  obtain ⟨h, -, -, hE3, -, hEN, hEC, -, -⟩ := hfr.hH
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  obtain ⟨φ⟩ := hφ
  have hspor' := hspor
  obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := hspor'
  obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hJ2p φ
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    center_eq_bot_of_mulEquiv φK hJ2z
  have heK : e ∉ K := not_mem_of_center_inf_commutator hD φ (by rw [hJ2z, bot_inf_eq])
  have hEK9 : Nat.card (E ⊓ K : Subgroup G) = 9 := card_inf_eq_nine hD hJ2p φ
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := hD.le_centralizer
  have hKc : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)
  have heZ : e ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨heE, heF⟩
  obtain ⟨α, β, heq⟩ := hfr.hZgen e heZ
  have hα : ¬ 3 ∣ α := by
    rintro ⟨m, rfl⟩
    apply hdΩ
    rw [hfr.hEL]
    have he' : e = d ^ β := by rw [heq, pow_mul, hfr.hc3, one_pow, one_mul]
    rw [← zpowers_eq_of_mem he3 he1 hfr.hd3 hfr.hd1 (he' ▸ pow_mem (Subgroup.mem_zpowers d) β)]
    exact heΩ
  have hβ : ¬ 3 ∣ β := by
    rintro ⟨m, rfl⟩
    apply hcΩ
    have he' : e = c ^ α := by rw [heq, pow_mul, hfr.hd3, one_pow, mul_one]
    rw [← zpowers_eq_of_mem he3 he1 hfr.hc3 hfr.hc1 (he' ▸ pow_mem (Subgroup.mem_zpowers c) α)]
    exact heΩ
  have hcd : c * d = d * c := hfr.hEab c hfr.hcE d hfr.hdE
  have hcexpr : c = (e * (d ^ β)⁻¹) ^ α := by
    have h1 : e * (d ^ β)⁻¹ = c ^ α := by rw [heq, mul_inv_cancel_right]
    rw [h1, ← pow_mul]
    have hαα : α * α % 3 = 1 := by
      have : α % 3 = 1 ∨ α % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    conv_rhs => rw [← Nat.div_add_mod (α * α) 3, hαα, pow_add, pow_mul, hfr.hc3, one_pow,
      one_mul, pow_one]
  set P := E ⊔ F with hP
  have hPNE : P ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_card le_sup_left hfr.hE27
    hfr.h81
  have hEN' : E ≤ Subgroup.normalizer (F : Set G) :=
    le_sup_left.trans (le_normalizer_of_card le_sup_right hfr.hF27 hfr.h81)
  have hPe : ∀ z ∈ P, z * e = e * z := by
    have hPC : P ≤ Subgroup.centralizer ({e} : Set G) := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hfr.hEab a ha e heE))
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hfr.hFab a ha e heF))
    exact fun z hz => Subgroup.mem_centralizer_singleton_iff.mp (hPC hz)
  obtain ⟨b, hbEK, hb1⟩ : ∃ b ∈ E ⊓ K, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E ⊓ K = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [this, Subgroup.card_bot] at hEK9
    norm_num at hEK9
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := fun z hz =>
    mem_normalizer_of_mem_lA hK he3 heK (Subgroup.mem_inf.mp hbEK).1
      (Subgroup.mem_inf.mp hbEK).2 hb1 (hPNE hz) (hPe z hz)
  have hdK : d ∈ K := by
    obtain ⟨b₀, hb₀B, hb₀F⟩ : ∃ b₀ ∈ E ⊓ K, b₀ ∉ F := by
      by_contra hall
      push Not at hall
      have hle : E ⊓ K ≤ E ⊓ F := fun z hz => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1,
        hall z hz⟩
      have heq' : E ⊓ K = E ⊓ F := Subgroup.eq_of_le_of_card_ge hle (by rw [hEK9, hfr.h9])
      exact heK (Subgroup.mem_inf.mp (heq' ▸ heZ : e ∈ E ⊓ K)).2
    obtain ⟨k, hk, hyk⟩ := conj_y_eq_of_not_mem hfr.frame hfr.hxE hfr.hyF hfr.hE27 hfr.hF27
      hfr.h9 hfr.hFN hfr.hEab (Subgroup.mem_inf.mp hb₀B).1 hb₀F
    have hyP : y ∈ P := Subgroup.mem_sup_right hfr.hyF
    have hyb : y * b₀ * y⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hPNK hyP) b₀).mp (Subgroup.mem_inf.mp hb₀B).2
    have hdk : d ^ k ∈ K := by
      have := K.mul_mem (K.inv_mem (Subgroup.mem_inf.mp hb₀B).2) hyb
      rwa [hyk, inv_mul_cancel_left] at this
    exact Subgroup.zpowers_le.mpr hdk (mem_zpowers_pow_of_not_dvd hfr.hd3 hk)
  have hEdec : E = Subgroup.zpowers e ⊔ (E ⊓ K) := by
    have hle : Subgroup.zpowers e ⊔ (E ⊓ K) ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine he3
      (fun heB : e ∈ E ⊓ K => heK heB.2) le_rfl hEK9
      (fun b hb => hE3.2 b hb.1) (fun b hb => hD.commute hD.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hfr.hE27, hcard])).symm
  have hinner : ∀ σ : MulAut (K ⧸ aschbacherSolvableCore 3 K), σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* _).range := fun σ hσ =>
    Sec15.Proof155w3.mem_range_conj_of_pow_three ⟨φK⟩ hσ
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [hfr.h81]; norm_num)
  have hPexp : ∀ z ∈ P, z ^ 3 = 1 := fun z hz =>
    pow_three_of_mem_sup hfr.hFN hEN' hE3 hfr.hF.1.2.1 hz
  have hPeK := le_zpowers_sup_of_inner hZK hinner hE3 hXF.1.2.1 hEdec hKe le_sup_left hP3 hPexp
    hPNK hPe
  have heP : e ∈ P := Subgroup.mem_sup_left heE
  have hPeq : P = Subgroup.zpowers e ⊔ (P ⊓ K) := by
    refine le_antisymm (fun z hz => ?_) (sup_le (Subgroup.zpowers_le.mpr heP) inf_le_left)
    obtain ⟨i, k, hk, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup hKe (hPeK hz)
    have hkP : k ∈ P := by
      have := P.mul_mem (P.inv_mem (P.zpow_mem heP i)) hz
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers e i))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hkP, hk⟩))
  have hPK27 : Nat.card (P ⊓ K : Subgroup G) = 27 := by
    have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ k ∈ P ⊓ K, a * k = k * a := by
      intro a ha k hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (hKc k (Subgroup.mem_inf.mp hk).2).symm j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [← hPeq, hfr.h81, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot he3 heK).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three he3 he1] at hcard
    omega
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 K))
  have hS₀ : Nat.card (S₀ : Subgroup K) = 27 := by
    set Qb₀ : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
      S₀.mapSurjective (QuotientGroup.mk'_surjective _)
    have hQb₀ : (Qb₀ : Subgroup _) =
        (S₀ : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
      Sylow.coe_mapSurjective _ _
    obtain ⟨⟨hHeis₀, -⟩, -⟩ := h415 _ ⟨φK⟩ Qb₀ _ rfl _ rfl
    rw [← card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three S₀.isPGroup'), ← hQb₀]
    exact hHeis₀.2.1
  have hSylPK : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ K) K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right ?_
    rw [hPK27, ← hS₀, Sylow.card_eq_multiplicity]
  obtain ⟨SK, hSK⟩ := hSylPK
  have hdP : ∀ z ∈ P, z * d = d * z := by
    have hPC : P ≤ Subgroup.centralizer ({d} : Set G) := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hfr.hEab a ha d hfr.hdE))
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (hfr.hFab a ha d (Subgroup.mem_inf.mp hfr.hdZ).2))
    exact fun z hz => Subgroup.mem_centralizer_singleton_iff.mp (hPC hz)
  have hc : ∃ S : Sylow 3 ↥K, (⟨d, hdK⟩ : ↥K) ∈ (S : Subgroup ↥K) ∧
      (S : Subgroup ↥K) ≤ Subgroup.centralizer {(⟨d, hdK⟩ : ↥K)} := by
    refine ⟨SK, ?_, fun s hs => ?_⟩
    · have hdPK : d ∈ P ⊓ K := Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hfr.hdE, hdK⟩
      rw [← hSK] at hdPK
      obtain ⟨s, hs, hsd⟩ := hdPK
      have hs' : s = ⟨d, hdK⟩ := Subtype.ext hsd
      rw [← hs']
      exact hs
    · have hsP : (s : G) ∈ P ⊓ K := hSK ▸ Subgroup.mem_map_of_mem _ hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hdP s (Subgroup.mem_inf.mp hsP).1)
  obtain ⟨hJq, -, hdJ, -⟩ := residual_facts h415 ⟨φK⟩ hdK hfr.hd1 hc
  have hKcd : K ⊓ Subgroup.centralizer ({c} : Set G) = K ⊓ Subgroup.centralizer ({d} : Set G) := by
    ext k
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hk, hkc⟩
      refine ⟨hk, ?_⟩
      have hke := hKc k hk
      have hkcα : k * c ^ α = c ^ α * k := (Commute.pow_right hkc α).eq
      have hkdβ : k * d ^ β = d ^ β * k := by
        have h1 : d ^ β = (c ^ α)⁻¹ * e := by rw [heq, inv_mul_cancel_left]
        rw [h1]
        have : Commute k ((c ^ α)⁻¹ * e) := (Commute.inv_right hkcα).mul_right hke
        exact this.eq
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_pow_of_not_dvd hfr.hd3 hβ)
      have := (Commute.zpow_right (show Commute k (d ^ β) from hkdβ) n).eq
      rwa [hn] at this
    · rintro ⟨hk, hkd⟩
      refine ⟨hk, ?_⟩
      rw [hcexpr]
      have : Commute k (e * (d ^ β)⁻¹) :=
        (show Commute k e from hKc k hk).mul_right
          (Commute.inv_right (Commute.pow_right (show Commute k d from hkd) β))
      exact (this.pow_right α).eq
  set J := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({c} : Set G)) :=
    h.toPartTwoStanding.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one h.toPartTwoStanding.toTheoremFourHyp hfr.hc1)
  have hE27' : Late.IsE27 E := ⟨hE3, hfr.hE27⟩
  have hJq' : IsQuasisimple (↥(inSubgroup perfectResidual
      (K ⊓ Subgroup.centralizer ({c} : Set G))) ⧸ aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)))) := by
    rw [hKcd]
    exact hJq
  obtain ⟨K'', hK'', hJK''⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hE27' heE
    hfr.hcE he1 hK.1 hJq'
  rw [hKcd] at hJK''
  have hL := h.mem_thetaComponentsAt
  have hK''L : K'' = L := by
    by_contra hne
    have hK''C : K'' ≤ Sec4.thetaQuotCentralizer L := by
      have h1 := hK''
      have h2 := hL
      rw [thetaComponentsAt_eq_thetaComponentsIn] at h1 h2
      exact Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in h1 h2 hne
    have hdC : d ∈ Sec4.thetaQuotCentralizer L := hK''C (hJK'' hdJ)
    have hCE := sectionCentralizer_eq_inf hEN
    rw [hEC] at hCE
    have hd' : d ∈ ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hfr.hdE, hdC⟩
    rw [← hCE] at hd'
    exact hfr.hdc hd'
  subst hK''L
  have hJCd : J ≤ K'' ⊓ Subgroup.centralizer ({d} : Set G) :=
    le_inf hJK'' ((Subgroup.map_subtype_le _).trans inf_le_right)
  have hsol := isSolvable_inf_centralizer_of_hyp138 hfr.hH hfr.hPGL hfr.hdL hfr.hd3 hfr.hd1
  have hJsol : Group.IsSolvable ↥J :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hJCd) (Subgroup.inclusion_injective _)
  have hJθsol : Group.IsSolvable (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  exact not_isSolvable_of_isQuasisimple' hJq hJθsol

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
