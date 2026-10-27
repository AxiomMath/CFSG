module

public import CFSG.Quasithin.Background.C2PushY
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.Quasithin.C2Push

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Components

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_ne_bot_of_isComponent {K : Subgroup X} (hK : CFSG.IsComponent K) :
    ⁅K, K⁆ ≠ ⊥ := by
  intro h
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hbot : K = ⊥ := hperf ▸ h
  have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hbot

theorem eq_of_isComponent_of_le {K K' : Subgroup X} (hK : CFSG.IsComponent K)
    (hK' : CFSG.IsComponent K') (h : K ≤ K') : K = K' := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hK' hK.2 with h1 | h1
  · exact le_antisymm h h1
  · exact absurd (le_bot_iff.mp (h1 ▸ Subgroup.commutator_mono h le_rfl))
      (commutator_ne_bot_of_isComponent hK)

end Components

theorem isComponent_imageOTwoQuot_of_isSubnormal {M B : Subgroup G} (hsub : IsSubnormal B M)
    (hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) :
    CFSG.IsComponent (imageOTwoQuot M B) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hsub
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hBq, ?_⟩
  have h1 := (isSubnormal_iff_subgroupOf (A4.subnormal_le hsub)).mp hsub
  exact h1.map (QuotientGroup.mk'_surjective _)

theorem le_of_perfect_le_sup {A R P : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRA : R ≤ Subgroup.normalizer (A : Set G)) (hP : ⁅P, P⁆ = P) (hPY : P ≤ A ⊔ R) : P ≤ A := by
  have h1 : oTwoUpper P ≤ A := by
    refine (oTwoUpper_mono hPY).trans (oTwoUpper_le_of_pow_mem fun y hy => ?_)
    have hy' : y ∈ (↑(A ⊔ R) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A R hRA] at hy'
    obtain ⟨a, ha, r, hr, rfl⟩ := hy'
    obtain ⟨j, hj⟩ := hR2 ⟨r, hr⟩
    have hj' : r ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨a', ha', h⟩ := A4.exists_pow_mul_eq ha (hRA hr) (2 ^ j)
    exact ⟨j, by rw [h, hj', mul_one]; exact ha'⟩
  calc P = oTwoUpper P := (C2Nine.oTwoUpper_eq_of_perfect hP).symm
    _ ≤ A := h1

theorem exists_eq_conjByElt_of_isBlock2 {M R L B : Subgroup G} (hR : IsTwoRadicalIn M R)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hB : IsBlock2 (conjClosure L R ⊔ R) B)
    (hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : ∃ r ∈ R, B = conjByElt r L := by
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hRM : R ≤ M := hR.1
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : Y ≤ M := conjClosure_sup_le hRM hLM
  have hRY : R ≤ Y := le_sup_right
  have hLY : L ≤ Y := (le_conjClosure L R).trans le_sup_left
  have hLY' : L ∈ cComp Y := cComp_mem_of_le hL hLY hYM
  have hBsubY : IsSubnormal B Y := IsBlock2.isSubnormal hB
  have hBperf : ⁅B, B⁆ = B :=
    C1GN.isShort2_perfect_of_perfect_quotient hB.1 (Group.isPerfect_def.mp hBq.1)
  have hBY₀ : B ≤ conjClosure L R :=
    le_of_perfect_le_sup hR.isPGroup (le_normalizer_conjClosure L R) hBperf hB.2.1
  have hLc : CFSG.IsComponent (imageOTwoQuot Y L) := isComponent_imageOTwoQuot hLY' hLq
  have hBc : CFSG.IsComponent (imageOTwoQuot Y B) :=
    isComponent_imageOTwoQuot_of_isSubnormal hBsubY hBq
  have hconjc : ∀ r ∈ R, CFSG.IsComponent (imageOTwoQuot Y (conjByElt r L)) := by
    intro r hr
    rw [imageOTwoQuot_conjByElt (hRY hr) hLY]
    exact CFSG.LocalCores.isComponent_map_mulEquiv _ hLc
  have hex : ∃ r ∈ R, imageOTwoQuot Y B ≤ imageOTwoQuot Y (conjByElt r L) := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ r ∈ R, ⁅imageOTwoQuot Y B, imageOTwoQuot Y (conjByElt r L)⁆ = ⊥ := by
      intro r hr
      rcases CFSG.LocalCores.component_subnormal_subgroup hBc (hconjc r hr).2 with h | h
      · exact absurd h (hcon r hr)
      · exact h
    set C : Subgroup G := preimageOTwoQuot Y
      (Subgroup.centralizer (imageOTwoQuot Y B : Set (OTwoQuot Y))) ⊓ Y with hC
    have hYC : conjClosure L R ≤ C := by
      refine conjClosure_le fun h hh z hz => ?_
      have hYmem : h * z * h⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem (hRY hh) (hLY hz)) (Y.inv_mem (hRY hh))
      refine ⟨mem_preimageOTwoQuot_iff.mpr ⟨hYmem, ?_⟩, hYmem⟩
      have hmem : (QuotientGroup.mk ⟨h * z * h⁻¹, hYmem⟩ : OTwoQuot Y) ∈
          imageOTwoQuot Y (conjByElt h L) :=
        mem_imageOTwoQuot_iff.mpr ⟨h * z * h⁻¹, hYmem,
          Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩, rfl⟩
      exact (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm h hh))) hmem
    refine commutator_ne_bot_of_isComponent hBc ?_
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨b, hb, hbB, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨hb1, -⟩ := hYC (hBY₀ hbB)
    obtain ⟨_, hcen⟩ := mem_preimageOTwoQuot_iff.mp hb1
    have := Subgroup.mem_centralizer_iff.mp hcen v hv
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr this.symm)
  obtain ⟨r, hr, hBr⟩ := hex
  have hBeq : imageOTwoQuot Y B = imageOTwoQuot Y (conjByElt r L) :=
    eq_of_isComponent_of_le hBc (hconjc r hr) hBr
  have hcrY : conjByElt r L ≤ Y := (conjByElt_le_conjClosure hr).trans le_sup_left
  have hcr : conjByElt r L ∈ cComp Y :=
    cComp_mem_of_le (C2Nine.conjByElt_mem_cComp hL (Subgroup.le_normalizer (hRM hr))) hcrY hYM
  have hBle : B ≤ conjByElt r L ⊔ pCoreOf 2 Y := by
    intro b hb
    have hbY : b ∈ Y := hB.2.1 hb
    have h1 : (QuotientGroup.mk ⟨b, hbY⟩ : OTwoQuot Y) ∈
        imageOTwoQuot Y (conjByElt r L ⊔ pCoreOf 2 Y) := by
      refine imageOTwoQuot_mono le_sup_left ?_
      rw [← hBeq]
      exact mem_imageOTwoQuot_iff.mpr ⟨b, hbY, hb, rfl⟩
    exact mem_of_mk_mem_imageOTwoQuot le_sup_right h1
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 Y) := by
    have hp : IsPGroup 2 ↥(pCoreOf 2 Y) := pCoreOf_isPGroup 2 Y
    have : Group.IsNilpotent ↥(pCoreOf 2 Y) := hp.isNilpotent
    infer_instance
  have hpc : perfectCore (conjByElt r L ⊔ pCoreOf 2 Y) = conjByElt r L :=
    (cComp_commutator_perfectCore hcr (pCoreOf_le 2 Y) hsolv
      (hcrY.trans (le_normalizer_pCoreOf 2 Y))).2
  have hBL : B ≤ conjByElt r L := by
    have := perfectCore_mono hBle
    rwa [perfectCore_eq_self_of_perfect hBperf, hpc] at this
  have hBne : B ≠ ⊥ := by
    intro hB0
    refine commutator_ne_bot_of_isComponent hBc ?_
    have : imageOTwoQuot Y B = ⊥ := by simp [imageOTwoQuot, hB0]
    rw [this]
    simp
  refine ⟨r, hr, ?_⟩
  by_contra hne
  exact not_subnormal_of_mem_cComp hcr (lt_of_le_of_ne hBL hne) hBne hBperf hBsubY

theorem isShort2_of_isBlock2_conjClosure_sup {M R L B : Subgroup G} (hR : IsTwoRadicalIn M R)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hB : IsBlock2 (conjClosure L R ⊔ R) B)
    (hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : IsShort2 L := by
  obtain ⟨r, hr, hBr⟩ := exists_eq_conjByElt_of_isBlock2 hR hL hLq hB hBq
  have hrY : r⁻¹ ∈ conjClosure L R ⊔ R := (conjClosure L R ⊔ R).inv_mem (Subgroup.mem_sup_right hr)
  have h1 := IsBlock2.conjByElt_of_mem hB hrY
  have h2 : conjByElt r⁻¹ B = L := by
    ext x
    rw [hBr, mem_conjByElt, mem_conjByElt]
    simp [mul_assoc]
  rw [h2] at h1
  exact h1.1

end CFSG.Quasithin.C2Push
