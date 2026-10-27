module

public import CFSG.Quasithin.Background.D2Z3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

section Blocks

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem centR_pow_three (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) {y : MulAut V} (hy : y ∈ centR X a) : y ^ 3 = 1 := by
  by_cases hne : centR X a = ⊥
  · rw [hne, Subgroup.mem_bot] at hy
    rw [hy]; simp
  · obtain ⟨hcard, -⟩ := centR_data hV h k hne
    have := pow_card_eq_one' (G := ↥(centR X a)) (x := ⟨y, hy⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this

omit [Finite V] in
theorem centR_le_pCoreOf (X : Subgroup (MulAut V)) (t : MulAut V) : centR X t ≤ pCoreOf 3 X :=
  inf_le_left

omit [Finite V] in
theorem KleinData.mul_mem_A {A : Subgroup (MulAut V)} {a b : MulAut V} (k : KleinData A a b) :
    a * b ∈ A := A.mul_mem k.ha k.hb

omit [Finite V] in
theorem Nt_inv_P (hcomm : ∀ x ∈ pCoreOf 3 X, ∀ y ∈ pCoreOf 3 X, x * y = y * x) (t : MulAut V)
    {g : MulAut V} (hg : g ∈ pCoreOf 3 X) :
    ∀ w ∈ commV (centR X t), g w ∈ commV (centR X t) := by
  intro w hw
  refine commV_smul_mem (fun p hp => ?_) hw
  have := hcomm g hg p (centR_le_pCoreOf X t hp)
  rw [this, mul_inv_cancel_right]
  exact hp

theorem Nt_inv_A (h : D214Hyp X A r) {t g : MulAut V} (ht : t ∈ A) (hg : g ∈ A) :
    ∀ w ∈ commV (centR X t), g w ∈ commV (centR X t) := fun _ hw =>
  commV_smul_mem (fun _ hp => h.centR_conj ht hg hp) hw

omit [Finite V] in
theorem fixV_inv_comm {g t : MulAut V} (hc : g * t = t * g) :
    ∀ w ∈ fixV (Subgroup.zpowers t), g w ∈ fixV (Subgroup.zpowers t) := by
  intro w hw
  rw [mem_fixV_zpowers_iff] at hw ⊢
  have h1 : t (g w) = g (t w) := by
    calc t (g w) = (t * g) w := rfl
      _ = (g * t) w := by rw [hc]
      _ = g (t w) := rfl
  rw [h1, hw]

omit [Finite V] in
theorem fixV_klein {A : Subgroup (MulAut V)} {a b : MulAut V} (k : KleinData A a b) :
    fixV A = fixV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers b) := by
  apply le_antisymm
  · exact le_inf (fixV_anti (Subgroup.zpowers_le.mpr k.ha)) (fixV_anti (Subgroup.zpowers_le.mpr k.hb))
  · intro w hw g hg
    have hwa : a w = w := mem_fixV_zpowers_iff.mp hw.1
    have hwb : b w = w := mem_fixV_zpowers_iff.mp hw.2
    rcases k.mem g hg with rfl | rfl | rfl | rfl
    · rfl
    · exact hwa
    · exact hwb
    · show (a * b) w = w
      rw [MulAut.mul_apply, hwb, hwa]

theorem E_le_of_invariant (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t t' : MulAut V}
    (k : KleinData A t t') (hne : centR X t ≠ ⊥) {W : Subgroup V}
    (hWle : W ≤ commV (centR X t)) (hWt : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ W, x w ∈ W)
    (hWQ : ∀ q ∈ centR X t, ∀ w ∈ W, q w ∈ W) (hW0 : W ≠ ⊥) :
    commV (centR X t) ⊓ fixV (Subgroup.zpowers t) ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hcard, -⟩ := centR_data hV h k hne
  obtain ⟨hE2, -⟩ := commV_centR_facts hV h k hne
  obtain ⟨y, hyQ, hy1, hyz, -⟩ := exists_generator_of_prime_card (p := 3) hcard
  have hdisj := (commV_card_three hV hcard).2.1
  set C := W ⊓ fixV (Subgroup.zpowers t) with hC
  have hCne : C ≠ ⊥ := by
    obtain ⟨w, hw, hw1, htw⟩ := exists_fixed_of_invariant hV k.ha2
      (fun w hw => hWt t (Subgroup.mem_zpowers t) w hw) hW0
    intro hbot
    have : w ∈ C := ⟨hw, mem_fixV_zpowers_iff.mpr htw⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hw1 this
  have hCinv : ∀ w ∈ C, y w ∈ C := by
    intro w hw
    refine ⟨hWQ y hyQ w hw.1, ?_⟩
    have hc : y * t = t * y := (mem_centR.mp hyQ).2
    exact fixV_inv_comm hc w hw.2
  have hCfree : ∀ w ∈ C, y w = w → w = 1 := by
    intro w hw hyw
    have hwF : w ∈ fixV (centR X t) := by
      rw [← hyz]
      exact mem_fixV_zpowers_iff.mpr hyw
    have : w ∈ commV (centR X t) ⊓ fixV (centR X t) := ⟨hWle hw.1, hwF⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  have h2 : 2 ≤ rk C := two_le_rk_of_free hV hCinv hCfree hCne
  have hCE : C ≤ commV (centR X t) ⊓ fixV (Subgroup.zpowers t) :=
    inf_le_inf hWle le_rfl
  have hCeq := eq_of_le_of_rk_le hV hCE (by omega)
  rw [← hCeq]
  exact inf_le_left

theorem Nt_disjoint_or_eq (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r)
    (hcomm : ∀ x ∈ pCoreOf 3 X, ∀ y ∈ pCoreOf 3 X, x * y = y * x) {t t' : MulAut V}
    (k : KleinData A t t') (hne : centR X t ≠ ⊥) (hne' : centR X t' ≠ ⊥) :
    commV (centR X t) ⊓ commV (centR X t') = ⊥ ∨ commV (centR X t) = commV (centR X t') := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_cases hW : commV (centR X t) ⊓ commV (centR X t') = ⊥
  · exact Or.inl hW
  right
  set W := commV (centR X t) ⊓ commV (centR X t') with hWdef
  obtain ⟨hcard, -⟩ := centR_data hV h k hne
  obtain ⟨hcard', -⟩ := centR_data hV h k.symm hne'
  obtain ⟨hE2, hN4, -, -⟩ := commV_centR_facts hV h k hne
  obtain ⟨hE2', hN4', -, -⟩ := commV_centR_facts hV h k.symm hne'
  obtain ⟨y', hy'Q, hy'1, hy'z, -⟩ := exists_generator_of_prime_card (p := 3) hcard'
  have hWt : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ W, x w ∈ W := by
    intro x hx w hw
    have hxA : x ∈ A := Subgroup.zpowers_le.mpr k.ha hx
    exact ⟨Nt_inv_A h k.ha hxA w hw.1, Nt_inv_A h k.symm.ha hxA w hw.2⟩
  have hWQ : ∀ q ∈ centR X t, ∀ w ∈ W, q w ∈ W := fun q hq w hw =>
    ⟨Nt_inv_P hcomm t (centR_le_pCoreOf X t hq) w hw.1,
      Nt_inv_P hcomm t' (centR_le_pCoreOf X t hq) w hw.2⟩
  have hWQ' : ∀ q ∈ centR X t', ∀ w ∈ W, q w ∈ W := fun q hq w hw =>
    ⟨Nt_inv_P hcomm t (centR_le_pCoreOf X t' hq) w hw.1,
      Nt_inv_P hcomm t' (centR_le_pCoreOf X t' hq) w hw.2⟩
  have hEt : commV (centR X t) ⊓ fixV (Subgroup.zpowers t) ≤ W :=
    E_le_of_invariant hV h k hne inf_le_left hWt hWQ hW
  have hy'inv : ∀ g ∈ Subgroup.zpowers y', ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    rw [hy'z] at hg
    exact hWQ' g hg w hw
  have hfix : W ⊓ fixV (Subgroup.zpowers y') = ⊥ := by
    rw [hy'z, eq_bot_iff]
    intro w ⟨hw, hwF⟩
    have hdisj' := (commV_card_three hV hcard').2.1
    have : w ∈ commV (centR X t') ⊓ fixV (centR X t') := ⟨hw.2, hwF⟩
    rw [hdisj', Subgroup.mem_bot] at this
    exact this
  have hinv : t * y' * t⁻¹ = y'⁻¹ := inverts_centR hV h k.symm y' hy'Q
  have hrkW := rk_eq_two_mul_sub hV (W := W) k.ha2 hinv hWt hy'inv hfix
  have hsum := rk_commSub_add_rk_inf_fixV hWt
  have hWF : W ⊓ fixV (Subgroup.zpowers t) = commV (centR X t) ⊓ fixV (Subgroup.zpowers t) := by
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · exact le_inf hEt inf_le_right
  rw [hWF] at hsum
  have hrk4 : rk W = 4 := by omega
  have hWt_eq : W = commV (centR X t) := eq_of_le_of_rk_le hV inf_le_left (by omega)
  have hWt'_eq : W = commV (centR X t') := eq_of_le_of_rk_le hV inf_le_right (by omega)
  exact hWt_eq.symm.trans hWt'_eq

end Blocks

end CFSG.Quasithin
