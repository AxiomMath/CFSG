module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_comm_mem_of_relIndex_two {B J : Subgroup G} (h2 : J.relIndex B = 2)
    {a : G} (haJ : a ∈ normalizer (J : Set G)) {b : G} (hb : b ∈ B) (hab : a * b * a⁻¹ ∈ B) :
    a * b * a⁻¹ * b⁻¹ ∈ J := by
  obtain ⟨a₀, -, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp h2
  have hJ : ∀ y, y ∈ J ↔ a * y * a⁻¹ ∈ J := fun y => Subgroup.mem_normalizer_iff.mp haJ y
  by_cases hbJ : b ∈ J
  · exact J.mul_mem ((hJ b).mp hbJ) (J.inv_mem hbJ)
  · have huJ : a * b * a⁻¹ ∉ J := fun hu => hbJ ((hJ b).mpr hu)
    have h1 : b * a₀ ∈ J := by
      rcases hxor b hb with h | h
      · exact h.1
      · exact absurd h.1 hbJ
    have h2' : a * b * a⁻¹ * a₀ ∈ J := by
      rcases hxor (a * b * a⁻¹) hab with h | h
      · exact h.1
      · exact absurd h.1 huJ
    have e : a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹ * a₀) * (b * a₀)⁻¹ := by group
    rw [e]
    exact J.mul_mem h2' (J.inv_mem h1)

private theorem nineThree_eq_of_relIndex_two {B J₁ J₂ : Subgroup G} (h : J₁ ≤ J₂) (h₂B : J₂ ≤ B)
    (h1 : J₁.relIndex B = 2) (h2 : J₂.relIndex B = 2) : J₁ = J₂ := by
  have h3 := Subgroup.relIndex_mul_relIndex J₁ J₂ B h h₂B
  rw [h1, h2] at h3
  have h4 : J₁.relIndex J₂ = 1 := by omega
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp h4)

namespace Nine3Choice

theorem conj_mem_nineDelta (hc : Nine3Choice V T A K S X p g x) {B : Subgroup G}
    (hB : B ∈ nineDelta V S) : conjSubgroup B g ∈ nineDelta V S :=
  (mem_nineDeltaStab.mp hc.g_mem B).mp hB

theorem conj_inv_mem_nineDelta (hc : Nine3Choice V T A K S X p g x) {B : Subgroup G}
    (hB : B ∈ nineDelta V S) : conjSubgroup B g⁻¹ ∈ nineDelta V S :=
  (mem_nineDeltaStab.mp ((nineDeltaStab V S).inv_mem hc.g_mem) B).mp hB

theorem nineI_le_conj_S (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineI V K ≤ conjSubgroup S g := by
  refine le_trans ?_ hc.S₀
  refine le_inf (le_inf ?_ ?_) ?_
  · exact Nine3Core.nineI_le_pCoreOf.trans hc.core.pCoreOf_le_S
  · exact hc.core.nineI_le_centralizer
  · exact hI.le_normalizer hc.core.A_mem_nineOmegaIn

theorem relIndex_conj_pCoreOf (hc : Nine3Choice V T A K S X p g x) {B : Subgroup G}
    (hB : B ∈ nineDelta V S) (hBA : B ≠ A) :
    (conjSubgroup (pCoreOf 2 K) g).relIndex B = 2 := by
  have hB' : conjSubgroup B g⁻¹ ∈ nineDelta V S := hc.conj_inv_mem_nineDelta hB
  have hB'V : conjSubgroup B g⁻¹ ≠ V := by
    intro e
    apply hBA
    have h1 := congrArg (fun C => conjSubgroup C g) e
    simp only [E3.conjSubgroup_inv_conj] at h1
    rw [h1, hc.V_g]
  have hB'Ω : conjSubgroup B g⁻¹ ∈ nineOmegaIn V K S :=
    (hc.core.mem_nineDelta_iff.mp hB').resolve_left hB'V
  have h2 := nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hB'Ω
  have h3 := E3.relIndex_conjSubgroup (pCoreOf 2 K) (conjSubgroup B g⁻¹) g
  rw [E3.conjSubgroup_inv_conj] at h3
  rw [h3]
  exact h2

theorem inf_pCoreOf_eq_inf_conj (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {B : Subgroup G} (hB : B ∈ nineOmegaIn V K S) (hBA : B ≠ A) :
    B ⊓ pCoreOf 2 K = B ⊓ conjSubgroup (pCoreOf 2 K) g := by
  have hBΔ : B ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hB)
  have h2g : (B ⊓ conjSubgroup (pCoreOf 2 K) g).relIndex B = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact hc.relIndex_conj_pCoreOf hBΔ hBA
  have h2 : (B ⊓ pCoreOf 2 K).relIndex B = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hB
  have hle : B ⊓ pCoreOf 2 K ≤ B ⊓ conjSubgroup (pCoreOf 2 K) g := by
    rw [← hI.comm B hB, Subgroup.commutator_le]
    intro a ha b hb
    have hcomm : ⁅a, b⁆ ∈ B ⊓ pCoreOf 2 K := by
      rw [← hI.comm B hB]
      exact Subgroup.commutator_mem_commutator ha hb
    have haB : a ∈ normalizer (B : Set G) := hI.le_normalizer hB ha
    have hab : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp haB b).mp hb
    have haRg : a ∈ normalizer (conjSubgroup (pCoreOf 2 K) g : Set G) := by
      have haS : a ∈ conjSubgroup S g := hc.nineI_le_conj_S hI ha
      rw [← E3.conjSubgroup_normalizer, mem_conjSubgroup_iff]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
        (hc.core.S_le_K (mem_conjSubgroup_iff.mp haS))
    have haJ : a ∈ normalizer ((B ⊓ conjSubgroup (pCoreOf 2 K) g : Subgroup G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_inf,
        conjSubgroup_eq_iff_mem_normalizer.mpr haB,
        conjSubgroup_eq_iff_mem_normalizer.mpr haRg]
    have h3 := nineThree_comm_mem_of_relIndex_two h2g haJ hb hab
    rw [commutatorElement_def]
    exact h3
  exact nineThree_eq_of_relIndex_two hle inf_le_left h2 h2g


theorem nineW0_le_pCoreOf (hc : Nine3Choice V T A K S X p g x) :
    nineW0 V K S g ≤ pCoreOf 2 K :=
  sup_le (inf_le_left.trans hc.core.V_le_pCoreOf) (iSup₂_le fun _ _ => inf_le_right)

theorem nineW0_le_conj (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineW0 V K S g ≤ conjSubgroup (pCoreOf 2 K) g := by
  refine sup_le inf_le_right (iSup₂_le fun B hB => ?_)
  by_cases hBA : B = A
  · intro y hy
    rw [hBA] at hy
    obtain ⟨hyA, -⟩ := Subgroup.mem_inf.mp hy
    have hyV : g * y * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp (hc.V_g ▸ hyA)
    exact mem_conjSubgroup_iff.mpr (hc.core.V_le_pCoreOf hyV)
  · exact (hc.inf_pCoreOf_eq_inf_conj hI hB hBA).le.trans inf_le_right

theorem nineW0_le_nineW (hc : Nine3Choice V T A K S X p g x) : nineW0 V K S g ≤ nineW V S := by
  refine sup_le (inf_le_left.trans ?_) (iSup₂_le fun B hB => inf_le_left.trans ?_)
  · exact le_iSup₂_of_le V hc.core.V_mem_nineDelta le_rfl
  · exact le_iSup₂_of_le B (hc.core.mem_nineDelta_iff.mpr (Or.inr hB)) le_rfl

theorem inf_nineW0_V (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    V ⊓ nineW0 V K S g = nineV1 V K g := by
  refine le_antisymm ?_ (le_inf inf_le_left le_sup_left)
  exact inf_le_inf le_rfl (hc.nineW0_le_conj hI)

theorem inf_nineW0_of_mem (hc : Nine3Choice V T A K S X p g x) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : B ⊓ nineW0 V K S g = B ⊓ pCoreOf 2 K := by
  refine le_antisymm (inf_le_inf le_rfl hc.nineW0_le_pCoreOf) (le_inf inf_le_left ?_)
  exact le_trans (le_iSup₂_of_le B hB le_rfl :
    B ⊓ pCoreOf 2 K ≤ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) le_sup_right

theorem nineW0_le_centralizer (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineW0 V K S g ≤ centralizer (nineI V K : Set G) := by
  refine sup_le ?_ (iSup₂_le fun B hB y hy => ?_)
  · exact inf_le_left.trans (Subgroup.le_centralizer_iff.mp hc.core.nineI_le_centralizer)
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hI.commute_inf hc.core hB ha hy

theorem not_A_le_sup (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    ¬ A ≤ V ⊔ nineW0 V K S g := by
  intro hA
  have hVC : V ≤ centralizer (nineI V K : Set G) :=
    Subgroup.le_centralizer_iff.mp hc.core.nineI_le_centralizer
  have hAC : A ≤ centralizer (nineI V K : Set G) :=
    hA.trans (sup_le hVC (hc.nineW0_le_centralizer hI))
  have hcomm : ⁅nineI V K, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mp hAC)
  rw [hI.comm A hc.core.A_mem_nineOmegaIn] at hcomm
  have h2 := nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hc.core.A_mem_nineOmegaIn
  rw [← Subgroup.inf_relIndex_right, inf_comm, hcomm, Subgroup.relIndex_bot_left] at h2
  have hcard : Nat.card A = Nat.card V := by
    obtain ⟨a, ha⟩ : IsGConj V A := hc.core.conj
    rw [ha, E3.card_conjSubgroup]
  have hV3 : 2 < Nat.card V := hc.core.hyp7.2.1
  omega

theorem relIndex_inf_nineW0 (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {B : Subgroup G} (hB : B ∈ nineDelta V S) : (B ⊓ nineW0 V K S g).relIndex B = 2 := by
  rcases hc.core.mem_nineDelta_iff.mp hB with hBV | hΩ
  · rw [hBV, hc.inf_nineW0_V hI, nineV1, Subgroup.inf_relIndex_left]
    exact hc.relIndex_conj_pCoreOf hc.core.V_mem_nineDelta hc.core.ne.symm
  · rw [hc.inf_nineW0_of_mem hΩ, Subgroup.inf_relIndex_left]
    exact nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hΩ

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
