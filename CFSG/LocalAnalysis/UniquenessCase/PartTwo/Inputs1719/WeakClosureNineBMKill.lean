module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

set_option maxRecDepth 100000

theorem commutator_mem_of_abelian {G : Type*} [Group G] {N H : Subgroup G}
    (hH : H ≤ normalizer (N : Set G)) (hab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) {x y : G}
    (hx : x ∈ N ⊔ H) (hy : y ∈ N ⊔ H) : ⁅x, y⁆ ∈ N := by
  have hmem : ∀ {z : G}, z ∈ N ⊔ H → z ∈ (N : Set G) * (H : Set G) := fun hz => by
    rw [← coe_mul_of_right_le_normalizer_left N H hH]
    exact hz
  obtain ⟨n₁, hn₁, h₁, hh₁, rfl⟩ := hmem hx
  obtain ⟨n₂, hn₂, h₂, hh₂, rfl⟩ := hmem hy
  have hc : h₂ * h₁⁻¹ = h₁⁻¹ * h₂ :=
    calc h₂ * h₁⁻¹ = h₁⁻¹ * (h₁ * h₂) * h₁⁻¹ := by group
      _ = h₁⁻¹ * (h₂ * h₁) * h₁⁻¹ := by rw [hab h₁ hh₁ h₂ hh₂]
      _ = h₁⁻¹ * h₂ := by group
  have e : ⁅n₁ * h₁, n₂ * h₂⁆ =
      n₁ * (h₁ * n₂ * h₁⁻¹) * (h₂ * n₁⁻¹ * h₂⁻¹) * n₂⁻¹ := by
    rw [commutatorElement_def]
    calc n₁ * h₁ * (n₂ * h₂) * (n₁ * h₁)⁻¹ * (n₂ * h₂)⁻¹
        = n₁ * h₁ * n₂ * (h₂ * h₁⁻¹) * n₁⁻¹ * h₂⁻¹ * n₂⁻¹ := by group
      _ = n₁ * h₁ * n₂ * (h₁⁻¹ * h₂) * n₁⁻¹ * h₂⁻¹ * n₂⁻¹ := by rw [hc]
      _ = n₁ * (h₁ * n₂ * h₁⁻¹) * (h₂ * n₁⁻¹ * h₂⁻¹) * n₂⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hn₁ ((mem_normalizer_iff.1 (hH hh₁) n₂).1 hn₂))
    ((mem_normalizer_iff.1 (hH hh₂) _).1 (inv_mem hn₁))) (inv_mem hn₂)

section Main

variable {i : Fin 4} {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D)
  (hC : KChk tLit D = true) (hTp : IsPGroup 2 (Tb i)) {ws : List (List (List ℕ))}
  (hO2 : O2Chk D ws = true)
include hT hE hC hTp hO2

theorem pCoreOf_eq_Qx : pCoreOf 2 (Kx i D) = Qx i D :=
  le_antisymm (pCoreOf_le_Qx hT hE hC hTp hO2) (Qx_le_pCoreOf hT hE hC)

omit hTp hO2 in
theorem relIndex_Qx_Mx : (Qx i D).relIndex (Mx i D) = 3 ^ D.yn := by
  have h := relIndex_mul_card (Qx i D) (Mx i D)
  rw [inf_eq_left.2 le_sup_left, card_Qx hT hE hC, card_Mx hT hE hC] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ D.qn) (by rw [h]; ring)

omit hT hC hTp hO2 in
theorem relIndex_Qx_U {U : Subgroup ↥(GB i)} {UL : List (List ℕ)} (hU : XDesc U UL)
    (hnd : UL.Nodup) :
    (Qx i D).relIndex U * (UL.filter D.qLit.contains).length = UL.length := by
  have hd : XDesc (Qx i D ⊓ U) (UL.filter D.qLit.contains) := by
    refine ⟨fun x => ?_, fun c hc => ?_⟩
    · rw [mem_inf, List.mem_filter, ← hU.mem, List.contains_iff_mem, ← hE.q.mem]
      exact and_comm
    · rw [List.mem_filter, List.contains_iff_mem] at hc
      obtain ⟨x, hx, rfl⟩ := hU.surj c hc.1
      exact ⟨x, ⟨(hE.q.mem _).2 hc.2, hx⟩, rfl⟩
  rw [← hd.card (hnd.filter _), ← hU.card hnd]
  exact relIndex_mul_card _ _

@[expose] def FaithChk (D : KData) (UL : List (List ℕ)) : Bool :=
  UL.all fun a => D.qLit.contains a || D.yLit.any fun y => !(D.qLit.contains (ccommut a y))

omit hTp hO2 in
theorem faithful_of_chk {U : Subgroup ↥(GB i)} {UL : List (List ℕ)} (hU : XDesc U UL)
    (h : FaithChk D UL = true) {R : Subgroup ↥(GB i)} (hYR : Yx i D ≤ R) :
    ∀ a ∈ U, (∀ x ∈ R, ⁅a, x⁆ ∈ Qx i D) → a ∈ Qx i D := by
  intro a ha hax
  simp only [FaithChk, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    Bool.not_eq_true'] at h
  rcases h _ ((hU.mem a).1 ha) with h1 | ⟨y, hy, h2⟩
  · exact (hE.q.mem _).2 h1
  · exfalso
    obtain ⟨yX, hyY, rfl⟩ : ∃ yX : ↥(GB i), yX ∈ Yx i D ∧ code yX.1 = y := by
      obtain ⟨σ, hσ, rfl⟩ := hE.y.surj y hy
      exact ⟨⟨σ, kY_le_GB hT hC hσ⟩, hσ, rfl⟩
    have h3 := hax yX (hYR hyY)
    have h4 : code (⁅a, yX⁆ : ↥(GB i)).1 ∈ D.qLit := (hE.q.mem _).1 h3
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, code_commut] at h4
    rw [List.contains_iff_mem.2 h4] at h2
    exact Bool.noConfusion h2

theorem kill761_of_chk {U : Subgroup ↥(GB i)} {UL : List (List ℕ)} (hU : XDesc U UL)
    (hnd : UL.Nodup) (hUK : U ≤ Kx i D) (hidx : UL.length ≠ 2 * (UL.filter D.qLit.contains).length)
    (hf : FaithChk D UL = true) : Kill761 U (Kx i D) := by
  unfold Kill761
  rw [pCoreOf_eq_Qx hT hE hC hTp hO2]
  refine ⟨Mx i D, le_sup_left, Mx_le_Kx hT hE hC, hUK.trans (Kx_le_normMx hT hE hC), ?_,
    faithful_of_chk hT hE hC hU hf le_sup_right, ?_⟩
  · rw [relIndex_Qx_Mx hT hE hC]
    exact Odd.pow (by decide)
  · intro h2
    apply hidx
    have := relIndex_Qx_U hE hU hnd
    rw [h2] at this
    exact this.symm

@[expose] def K763Chk (D : KData) (UL : List (List ℕ)) : Bool :=
  UL.length == 2 * (UL.filter D.qLit.contains).length && D.yn == 2 &&
  D.yGen.all fun y => UL.any fun u =>
    D.qLit.contains (Core.cmul (cinv (ccommut (Core.cmul y y) u)) y)

theorem kill763_of_chk {U : Subgroup ↥(GB i)} {UL : List (List ℕ)} (hU : XDesc U UL)
    (hnd : UL.Nodup) (hUK : U ≤ Kx i D) (h3 : K763Chk D UL = true)
    (hf : FaithChk D UL = true) : Kill763 U (Kx i D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [K763Chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem] at h3
  obtain ⟨⟨hidx, hyn⟩, hgen⟩ := h3
  unfold Kill763
  rw [pCoreOf_eq_Qx hT hE hC hTp hO2]
  have hY9 : Nat.card (Yx i D) = 3 ^ 2 := by rw [card_Yx hT hE hC, hyn]
  have hab : ∀ x ∈ Yx i D, ∀ y ∈ Yx i D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hY9).is_comm.comm
      ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨?_, Mx i D, le_sup_left, Mx_le_Kx hT hE hC, hUK.trans (Kx_le_normMx hT hE hC), ?_, ?_,
    fun y hy => pow_three_mem_Qx hT hE hC hy,
    fun y hy z hz => commutator_mem_of_abelian (Yx_le_normQx hT hE hC) hab hy hz, ?_⟩
  · have := relIndex_Qx_U hE hU hnd
    rw [hidx] at this
    have hpos : 0 < (UL.filter D.qLit.contains).length := by
      refine List.length_pos_of_mem (List.mem_filter.2 ⟨(hU.mem 1).1 (one_mem U), ?_⟩)
      rw [List.contains_iff_mem, Subgroup.coe_one, code_one, ← code_one]
      exact (hE.q.mem 1).1 (one_mem _)
    exact Nat.eq_of_mul_eq_mul_right hpos this
  ·
    refine sup_le le_sup_right ?_
    intro y hy
    have key : closureC D.yGen ≤ (⁅Mx i D, U⁆ ⊔ Qx i D).map (GB i).subtype := by
      apply closureC_le
      intro σ hσ
      obtain ⟨u, hu, hq⟩ := hgen _ hσ
      have hσG : σ ∈ GB i := kY_le_GB hT hC (subset_closureC hσ)
      obtain ⟨uX, huU, rfl⟩ := hU.surj u hu
      set yX : ↥(GB i) := ⟨σ, hσG⟩
      obtain ⟨qX, hqQ, hqc⟩ : ∃ qX : ↥(GB i), qX ∈ Qx i D ∧
          code qX.1 = Core.cmul (cinv (ccommut (Core.cmul (code σ) (code σ)) (code uX.1)))
            (code σ) := by
        obtain ⟨τ, hτ, hτc⟩ := hE.q.surj _ hq
        exact ⟨⟨τ, kQ_le_GB hT hE hC hτ⟩, hτ, hτc⟩
      have hyM : yX ∈ Mx i D := mem_sup_right (subset_closureC hσ)
      have hcm : ⁅yX * yX, uX⁆ ∈ ⁅Mx i D, U⁆ := commutator_mem_commutator (mul_mem hyM hyM) huU
      have hq' : (qX : P16) = (⁅σ * σ, (uX : P16)⁆)⁻¹ * σ := by
        apply code_injective
        rw [hqc, code_mul, code_inv, commutatorElement_def, code_commut, code_mul]
      have he : yX = ⁅yX * yX, uX⁆ * qX := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hq']
        change σ = ⁅σ * σ, (uX : P16)⁆ * (⁅σ * σ, (uX : P16)⁆⁻¹ * σ)
        group
      refine ⟨yX, ?_, rfl⟩
      rw [he]
      exact mul_mem (mem_sup_left hcm) (mem_sup_right hqQ)
    obtain ⟨w, hw, hwy⟩ := key hy
    have : w = y := Subtype.ext hwy
    rw [← this]
    exact hw
  · exact faithful_of_chk hT hE hC hU hf le_sup_right
  · rw [relIndex_Qx_Mx hT hE hC, hyn]
    decide

end Main

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
