module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Setting
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple
public import CFSG.Quasithin.Vol2.Ch10SecA312LA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.L436
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (tA)
open scoped Pointwise commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

theorem almostSimple (h : Setting L T P₀ P₁ n w) :
    CFSG.Quasithin.Vol2.Ch11.SecE3.AlmostSimple L :=
  CFSG.LocalAnalysis.WeakClosure81.almostSimple_of_normal_simple_sup_sylow
    h.normal h.simple h.nonabelian h.centralizer_eq h.sylow h.sup_eq

theorem pCoreOf_top_eq_bot (h : Setting L T P₀ P₁ n w) : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ :=
  CFSG.LocalAnalysis.WeakClosure81.pCoreOf_top_eq_bot_of_almostSimple
    h.normal h.simple h.nonabelian h.centralizer_eq

theorem tA_eq (h : Setting L T P₀ P₁ n w) (A : Subgroup Q) :
    tA T A = T ⊓ centralizer (A : Set Q) := by
  have hO : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := pCoreOf_top_eq_bot h
  ext t
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_tA, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff_commutator_eq_one', hO, Subgroup.normalizer_eq_top]
  simp only [Subgroup.mem_top, true_and, Subgroup.mem_bot]
  rfl

theorem le_normalizer_inf (h : Setting L T P₀ P₁ n w) :
    T ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  haveI : L.Normal := h.normal
  intro t ht
  refine Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := L) ⟨?_, ?_⟩
  · exact Subgroup.le_normalizer ht
  · exact Subgroup.le_normalizer_of_normal (H := L) (K := T) ht

theorem rad_le_inf (h : Setting L T P₀ P₁ n w) {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    pCoreOf 2 (perfectCore P) ≤ T ⊓ L := by
  rcases hP with rfl | rfl
  · rw [h.concl₀.S_eq]
    exact le_sup_left
  · rw [h.concl₁.S_eq]
    exact le_sup_left

theorem rad_comm (h : Setting L T P₀ P₁ n w) {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁)
    {x y : Q} (hx : x ∈ pCoreOf 2 (perfectCore P)) (hy : y ∈ pCoreOf 2 (perfectCore P)) :
    x * y = y * x := by
  rcases hP with rfl | rfl
  · have hx2 : x * x = 1 := by simpa [pow_two] using h.concl₀.V_sq x hx
    have hy2 : y * y = 1 := by simpa [pow_two] using h.concl₀.V_sq y hy
    have hxy2 : (x * y) * (x * y) = 1 := by
      simpa [pow_two] using h.concl₀.V_sq (x * y) (mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy2).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hx2,
          inv_eq_of_mul_eq_one_right hy2]
  · have hx2 : x * x = 1 := by simpa [pow_two] using h.concl₁.V_sq x hx
    have hy2 : y * y = 1 := by simpa [pow_two] using h.concl₁.V_sq y hy
    have hxy2 : (x * y) * (x * y) = 1 := by
      simpa [pow_two] using h.concl₁.V_sq (x * y) (mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy2).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hx2,
          inv_eq_of_mul_eq_one_right hy2]

theorem sp4Q₁_one (h : Setting L T P₀ P₁ n w) :
    sp4Q₁ L P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) = pCoreOf 2 (perfectCore P₀) := by
  unfold sp4Q₁
  rw [h.k₂₁]

theorem sp4Q₁_zero (h : Setting L T P₀ P₁ n w) :
    sp4Q₁ L P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) = pCoreOf 2 (perfectCore P₁) := by
  unfold sp4Q₁
  rw [h.k₂₀]

theorem sp4C_zero_eq (h : Setting L T P₀ P₁ n w) :
    sp4C P₀ (pCoreOf 2 (perfectCore P₀)) = sp4Z P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) := by
  have h' : sp4C P₀ (pCoreOf 2 (perfectCore P₀)) =
      sp4Q₁ L P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) ⊓
        centralizer (sp4K₂ L P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) : Set Q) := by
    unfold sp4C
    rw [sp4Q₁_one h, h.k₂₁]
  exact h'.trans h.concl₁.Q₁_cent

theorem sp4C_one_eq (h : Setting L T P₀ P₁ n w) :
    sp4C P₁ (pCoreOf 2 (perfectCore P₁)) = sp4Z P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) := by
  have h' : sp4C P₁ (pCoreOf 2 (perfectCore P₁)) =
      sp4Q₁ L P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) ⊓
        centralizer (sp4K₂ L P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) : Set Q) := by
    unfold sp4C
    rw [sp4Q₁_zero h, h.k₂₀]
  exact h'.trans h.concl₀.Q₁_cent

private theorem sp4C_le_rad {P R : Subgroup Q} : sp4C P R ≤ R := by
  unfold sp4C
  exact inf_le_left

private theorem sp4Z_le_rad {P R : Subgroup Q}
    (hc : Sp4ParConcl n L P (T ⊓ L) R) : sp4Z P (T ⊓ L) R ≤ R := by
  have h1 : sp4Z P (T ⊓ L) R ≤ sp4C P R ⊔ sp4Z P (T ⊓ L) R := le_sup_right
  rw [← hc.cent_S] at h1
  exact h1.trans inf_le_left

theorem w_zero (h : Setting L T P₀ P₁ n w) : w 0 = 1 := by
  have h1 : w 0 = w 0 * w 0 := by simpa using h.w_add 0 0
  exact mul_left_cancel (by rw [← h1, mul_one])

theorem w_mem (h : Setting L T P₀ P₁ n w) (x : F × F) :
    w x ∈ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) := by
  obtain ⟨b, c⟩ := x
  have hfst : w (b, 0) ∈ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) := by
    refine ⟨sp4C_le_rad (P := P₀) (R := pCoreOf 2 (perfectCore P₀)) (h.w_fst b), ?_⟩
    exact sp4Z_le_rad (P := P₁) (R := pCoreOf 2 (perfectCore P₁)) h.concl₁ (by
      rw [← h.sp4C_zero_eq]
      exact h.w_fst b)
  have hsnd : w (0, c) ∈ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) := by
    refine ⟨?_, sp4C_le_rad (P := P₁) (R := pCoreOf 2 (perfectCore P₁)) (h.w_snd c)⟩
    exact sp4Z_le_rad (P := P₀) (R := pCoreOf 2 (perfectCore P₀)) h.concl₀ (by
      rw [← h.sp4C_one_eq]
      exact h.w_snd c)
  rw [show w (b, c) = w (b, 0) * w (0, c) by
    simpa using h.w_add (b, 0) (0, c)]
  exact mul_mem hfst hsnd

theorem inf_ne_bot (h : Setting L T P₀ P₁ n w) : T ⊓ L ≠ ⊥ := by
  intro hbot
  have hm1 : w ((1 : F), 0) ∈ T ⊓ L :=
    (rad_le_inf h (Or.inl rfl)) (Subgroup.mem_inf.mp (w_mem h (1, 0))).1
  have hm0 : w ((0 : F), 0) ∈ T ⊓ L :=
    (rad_le_inf h (Or.inl rfl)) (Subgroup.mem_inf.mp (w_mem h (0, 0))).1
  have h1 : w ((1 : F), 0) = 1 := by
    rw [hbot] at hm1
    exact Subgroup.mem_bot.mp hm1
  have h0 : w ((0 : F), 0) = 1 := by
    rw [hbot] at hm0
    exact Subgroup.mem_bot.mp hm0
  exact one_ne_zero (congrArg Prod.fst (h.w_injective (h1.trans h0.symm)))

theorem isPSL_modO2 (h : Setting L T P₀ P₁ n w) {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    IsPSL 2 2 n (ModO2 (perfectCore P)) := by
  rcases hP with hc | hc
  · rw [hc]
    have hpsl := h.concl₁.psl
    rw [h.k₂₁] at hpsl
    exact hpsl
  · rw [hc]
    have hpsl := h.concl₀.psl
    rw [h.k₂₀] at hpsl
    exact hpsl

theorem isSimpleGroup_modO2 (h : Setting L T P₀ P₁ n w) {P : Subgroup Q}
    (hP : P = P₀ ∨ P = P₁) : IsSimpleGroup (ModO2 (perfectCore P)) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n (isPSL_modO2 h hP)).2

theorem nonabelian_modO2 (h : Setting L T P₀ P₁ n w) {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    ∃ a b : ModO2 (perfectCore P), a * b ≠ b * a :=
  CFSG.Quasithin.Vol2.Ch10.A312LF.nonabelian_of_isPSL (isPSL_modO2 h hP)

theorem rad_inf_rad (h : Setting L T P₀ P₁ n w) :
    pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) =
      sp4C P₀ (pCoreOf 2 (perfectCore P₀)) ⊔ sp4C P₁ (pCoreOf 2 (perfectCore P₁)) := by
  have h1 : pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) =
      sp4C P₀ (pCoreOf 2 (perfectCore P₀)) ⊔
        sp4Z P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) := by
    rw [← sp4Q₁_zero h]
    exact h.concl₀.V_inf_Q₁
  rw [h1, sp4C_one_eq h]

theorem sp4C_inf_sp4C (h : Setting L T P₀ P₁ n w) :
    sp4C P₀ (pCoreOf 2 (perfectCore P₀)) ⊓ sp4C P₁ (pCoreOf 2 (perfectCore P₁)) = ⊥ := by
  rw [sp4C_one_eq h]
  exact h.concl₀.C_inf_Z

theorem mem_sp4C_zero_iff (h : Setting L T P₀ P₁ n w) {v : Q} :
    v ∈ sp4C P₀ (pCoreOf 2 (perfectCore P₀)) ↔ ∃ b : F, w (b, 0) = v := by
  constructor
  · intro hv
    let f : F → ↥(sp4C P₀ (pCoreOf 2 (perfectCore P₀))) :=
      fun b => ⟨w (b, 0), h.w_fst b⟩
    have hinj : Function.Injective f := by
      intro b b' hbb
      have h1 : w (b, 0) = w (b', 0) := congrArg Subtype.val hbb
      have h2 : ((b, 0) : F × F) = (b', 0) := h.w_injective h1
      simpa using h2
    have hcard : Nat.card F = Nat.card ↥(sp4C P₀ (pCoreOf 2 (perfectCore P₀))) := by
      rw [h.card_F, h.concl₀.card_C]
    have hbij : Function.Bijective f :=
      (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
    obtain ⟨b, hb⟩ := hbij.2 ⟨v, hv⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, rfl⟩
    exact h.w_fst b

theorem mem_sp4C_one_iff (h : Setting L T P₀ P₁ n w) {v : Q} :
    v ∈ sp4C P₁ (pCoreOf 2 (perfectCore P₁)) ↔ ∃ c : F, w (0, c) = v := by
  constructor
  · intro hv
    let f : F → ↥(sp4C P₁ (pCoreOf 2 (perfectCore P₁))) :=
      fun c => ⟨w (0, c), h.w_snd c⟩
    have hinj : Function.Injective f := by
      intro c c' hcc
      have h1 : w (0, c) = w (0, c') := congrArg Subtype.val hcc
      have h2 : ((0, c) : F × F) = (0, c') := h.w_injective h1
      simpa using h2
    have hcard : Nat.card F = Nat.card ↥(sp4C P₁ (pCoreOf 2 (perfectCore P₁))) := by
      rw [h.card_F, h.concl₁.card_C]
    have hbij : Function.Bijective f :=
      (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
    obtain ⟨c, hc⟩ := hbij.2 ⟨v, hv⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact h.w_snd c

theorem exists_w_eq (h : Setting L T P₀ P₁ n w) {v : Q}
    (hv : v ∈ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁)) : ∃ x : F × F, w x = v := by
  rw [rad_inf_rad h] at hv
  have hC₁R : sp4C P₁ (pCoreOf 2 (perfectCore P₁)) ≤ pCoreOf 2 (perfectCore P₀) := by
    rw [sp4C_one_eq h]
    exact sp4Z_le_rad (P := P₀) (R := pCoreOf 2 (perfectCore P₀)) h.concl₀
  have hcomm : ⁅sp4C P₀ (pCoreOf 2 (perfectCore P₀)),
      sp4C P₁ (pCoreOf 2 (perfectCore P₁))⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact rad_comm h (Or.inl rfl) (sp4C_le_rad hx) (hC₁R hy)
  have hnorm : sp4C P₀ (pCoreOf 2 (perfectCore P₀)) ≤
      Subgroup.normalizer (sp4C P₁ (pCoreOf 2 (perfectCore P₁)) : Set Q) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (hcomm.trans bot_le)
  have hprod : v ∈ (sp4C P₀ (pCoreOf 2 (perfectCore P₀)) : Set Q) *
      (sp4C P₁ (pCoreOf 2 (perfectCore P₁)) : Set Q) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact hv
  obtain ⟨c₀, hc₀, c₁, hc₁, hc⟩ := Set.mem_mul.mp hprod
  obtain ⟨b, hb⟩ := (mem_sp4C_zero_iff h (v := c₀)).mp hc₀
  obtain ⟨c, hc'⟩ := (mem_sp4C_one_iff h (v := c₁)).mp hc₁
  refine ⟨(b, c), ?_⟩
  calc w (b, c) = w (b, 0) * w (0, c) := by
        simpa using h.w_add (b, 0) (0, c)
    _ = c₀ * c₁ := by rw [hb, hc']
    _ = v := hc

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting
