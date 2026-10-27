module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Tis
import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open Matrix

variable {F : Type} [Field F]

lemma wcgapsc_coe_sp4Z (b c : F) :
    (((sp4Z b c : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 1 (sym2 b c 0) 0 1 := by
  rw [sp4Z, coe_tau]

lemma wcgapsc_sp4Z_add (b c b' c' : F) :
    sp4Z b c * sp4Z b' c' = sp4Z (b + b') (c + c') := by
  rw [sp4Z, sp4Z, sp4Z, tau_mul_tau]
  refine tau_congr _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2, add_comm, add_left_comm]

lemma wcgapsc_sp4Z_zero : sp4Z (0 : F) 0 = 1 := by
  apply statedSp_ext
  rw [wcgapsc_coe_sp4Z]
  rw [show sym2 (0 : F) 0 0 = 0 from by ext i j; fin_cases i <;> fin_cases j <;> simp [sym2],
    fromBlocks_one]
  rfl

lemma wcgapsc_sp4Z_neg (b c : F) : sp4Z (-b) (-c) = (sp4Z b c)⁻¹ := by
  have h : sp4Z b c * sp4Z (-b) (-c) = 1 := by
    rw [wcgapsc_sp4Z_add, add_neg_cancel, add_neg_cancel, wcgapsc_sp4Z_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma wcgapsc_sp4Z_eq_one_iff (b c : F) : sp4Z b c = 1 ↔ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have h' : sym2 b c 0 = 0 := by
      have hh : tau (sym2_transpose b c 0) = tau (sym2_transpose 0 0 0) := by
        show sp4Z b c = sp4Z 0 0
        rw [h, wcgapsc_sp4Z_zero]
      have h2 := tau_injective (sym2_transpose b c 0) (sym2_transpose 0 0 0) hh
      rw [h2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sym2]
    exact ⟨by simpa [sym2] using congrFun₂ h' 0 0,
      by simpa [sym2] using congrFun₂ h' 0 1⟩
  · rintro ⟨rfl, rfl⟩
    exact wcgapsc_sp4Z_zero

lemma wcgapsc_sp4Z_injective {b c b' c' : F} (h : sp4Z b c = sp4Z b' c') :
    b = b' ∧ c = c' := by
  have h' : sym2 b c 0 = sym2 b' c' 0 := by
    apply tau_injective (sym2_transpose b c 0) (sym2_transpose b' c' 0)
    show sp4Z b c = sp4Z b' c'
    exact h
  exact ⟨by simpa [sym2] using congrFun₂ h' 0 0, by simpa [sym2] using congrFun₂ h' 0 1⟩

lemma wcgapsc_sp4Z_mem_unipotent (b c : F) : sp4Z b c ∈ unipotent 2 F :=
  tau_mem_unipotent (sym2_transpose b c 0)

lemma wcgapsc_sp4Z_mem_center_iff [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {g : StatedSp 2 F} :
    g ∈ unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
        Set (StatedSp 2 F)) ↔ ∃ b c : F, g = sp4Z b c := by
  have hcenter := (unique_symplectic_four_Sylow_center (K := F) 4 hF).2.2.2.2.2.2.2.1
  constructor
  · rintro ⟨hU, hC⟩
    have hmem : (⟨g, hU⟩ : unipotent 2 F) ∈ Subgroup.center (unipotent 2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC y y.2)
    obtain ⟨b, c, hbc⟩ := (hcenter ⟨g, hU⟩).mp hmem
    exact ⟨b, c, hbc⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨wcgapsc_sp4Z_mem_unipotent b c, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hmem : (⟨sp4Z b c, wcgapsc_sp4Z_mem_unipotent b c⟩ : unipotent 2 F) ∈
        Subgroup.center (unipotent 2 F) :=
      (hcenter _).mpr ⟨b, c, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩)

lemma wcgapsc_addHom_ext [Finite F] (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) {L M : F →+ F} (h1 : L 1 = M 1) (hω' : L ω = M ω) :
    L = M := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  ext x
  have hx : x ∈ ({0, 1, ω, ω ^ 2} : Finset F) := by
    rw [← TauCeti.univ_eq_zero_one_root_sq hF hω]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  have hω2 : ω ^ 2 = -(ω + 1) := by
    rw [eq_neg_iff_add_eq_zero, ← add_assoc]
    exact hω
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · exact h1
  · exact hω'
  · calc L (ω ^ 2) = L (-(ω + 1)) := by rw [hω2]
      _ = -(L (ω + 1)) := by simp only [map_neg]
      _ = -(L ω + L 1) := by rw [map_add]
      _ = -(M ω + M 1) := by rw [hω', h1]
      _ = M (-(ω + 1)) := by simp only [map_neg, map_add]
      _ = M (ω ^ 2) := by rw [hω2]

theorem wcgapsc_graph_cases [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (L : F →+ F) (hL : Function.Injective L) :
    (∃ a : F, a ≠ 0 ∧ ∀ x, L x = a * x) ∨
    (∃ b : F, b ≠ 0 ∧ ∀ x, L x = b * x ^ 2) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hF
  set u := L 1 with hu
  set v := L ω with hv
  have hu_ne : u ≠ 0 := by
    intro h
    have h1 : L 1 = L 0 := by rw [← hu, h, L.map_zero]
    exact one_ne_zero (hL h1)
  have hωω : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact hω
    rwa [CharTwo.neg_eq] at h
  have hω3 : ω ^ 3 = 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
    have hexp : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    exact sub_eq_zero.mp (hexp ▸ h)
  set a := v + u * ω ^ 2 with ha
  set b := v + u * ω with hb
  let M : F →+ F :=
    { toFun := fun x => a * x + b * x ^ 2
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [CharTwo.add_sq]
        ring }
  have hM1 : M 1 = u := by
    show a * 1 + b * 1 ^ 2 = u
    rw [ha, hb]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    calc (v + u * ω ^ 2) * 1 + (v + u * ω) * 1 ^ 2
        = u * (ω ^ 2 + ω) + 2 * v := by ring
      _ = u * (ω ^ 2 + ω) + 0 := by rw [h2, zero_mul]
      _ = u * (ω ^ 2 + ω) := add_zero _
      _ = u * 1 := by rw [hωω]
      _ = u := mul_one u
  have hMω : M ω = v := by
    show a * ω + b * ω ^ 2 = v
    rw [ha, hb]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    calc (v + u * ω ^ 2) * ω + (v + u * ω) * ω ^ 2
        = v * (ω + ω ^ 2) + u * ω ^ 3 + u * ω ^ 3 := by ring
      _ = v * 1 + u * 1 + u * 1 := by
            rw [show ω + ω ^ 2 = 1 from by rw [add_comm, hωω], hω3]
      _ = v := by
            simp only [mul_one]
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hLM : L = M :=
    wcgapsc_addHom_ext hF hω (L := L) (M := M) (by rw [hM1, hu]) (by rw [hMω, hv])
  have hform : ∀ x, L x = a * x + b * x ^ 2 := by
    intro x
    rw [hLM]
    rfl
  have hab : a = 0 ∨ b = 0 := by
    by_contra h
    rw [not_or] at h
    obtain ⟨ha0, hb0⟩ := h
    have hx0 : a * b⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hb0)
    have hzero : L (a * b⁻¹) = 0 := by
      rw [hform]
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      rw [show a * (a * b⁻¹) + b * (a * b⁻¹) ^ 2 = (2 : F) * (a ^ 2 * b⁻¹) by
        field_simp
        ring]
      rw [h2, zero_mul]
    exact hx0 (hL (by rw [hzero, L.map_zero]))
  rcases hab with ha0 | hb0
  · right
    have hb_ne : b ≠ 0 := by
      intro hb0'
      have h : u = 0 := by
        rw [← hM1]
        show a * 1 + b * 1 ^ 2 = 0
        rw [ha0, hb0']
        ring
      exact hu_ne h
    refine ⟨b, hb_ne, fun x => ?_⟩
    rw [hform, ha0, zero_mul, zero_add]
  · left
    have ha_ne : a ≠ 0 := by
      intro ha0'
      have h : u = 0 := by
        rw [← hM1]
        show a * 1 + b * 1 ^ 2 = 0
        rw [ha0', hb0]
        ring
      exact hu_ne h
    refine ⟨a, ha_ne, fun x => ?_⟩
    rw [hform, hb0, zero_mul, add_zero]

end CFSG.LocalAnalysis.WeakClosure81

end
