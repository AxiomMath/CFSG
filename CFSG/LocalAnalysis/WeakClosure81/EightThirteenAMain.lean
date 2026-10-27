module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenAComm
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenADecomp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem normalizerMonoidHom_eq_one_iff {V : Subgroup G} {x : G}
    (hx : x ∈ normalizer (V : Set G)) :
    V.normalizerMonoidHom ⟨x, hx⟩ = 1 ↔ ∀ v ∈ V, x * v = v * x := by
  constructor
  · intro h v hv
    have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
    simp at this
    exact mul_inv_eq_iff_eq_mul.mp this
  · intro h
    ext w
    simp
    exact mul_inv_eq_iff_eq_mul.mpr (h w w.2)

theorem Sit813.exists_fixed_of_noncentral_decomp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (hAV : ∀ a ∈ A, ∀ w ∈ V, a * w = w * a)
    (hNV : ∀ n ∈ oTwoMod (cGrp H T) K, ∀ w ∈ V, n * w = w * n) {a k t : G} (ha : a ∈ A)
    (hk : k ∈ K ⊓ normalizer (V : Set G)) (ht : t ∈ rGrp H T K) (hat : a = k * t)
    (hkV : ∃ w ∈ V, k * w ≠ w * k) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ y ∈ K ⊓ normalizer (V : Set G), y * v * y⁻¹ = v := by
  classical
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  have hkM : k ∈ normalizer (V : Set G) := (Subgroup.mem_inf.mp hk).2
  have htT : t ∈ T := Sit813.rGrp_le_T ht
  have htM : t ∈ normalizer (V : Set G) := h.le_normalizer_T htT
  have haM : a ∈ normalizer (V : Set G) := h.a_le_normalizer_V ha
  obtain ⟨e, he⟩ : ∃ e : ℕ, t ^ (2 ^ e) = 1 := by
    obtain ⟨e, he⟩ := h.minCex.hyp.sylow.isPGroup (⟨t, htT⟩ : ↥T)
    have := congrArg Subtype.val he
    exact ⟨e, by simpa using this⟩
  let ρ : ↥(normalizer (V : Set G)) →* MulAut ↥V := V.normalizerMonoidHom
  have hρ : ∀ (x : ↥(normalizer (V : Set G))) (v : ↥V),
      ((ρ x v : ↥V) : G) = (x : G) * v * (x : G)⁻¹ := by
    intro x v
    simp [ρ]
  have hρ1 : ∀ x : ↥(normalizer (V : Set G)), ρ x = 1 ↔ ∀ v ∈ V, (x : G) * v = v * x :=
    fun x => normalizerMonoidHom_eq_one_iff x.2
  let ka : ↥(normalizer (V : Set G)) := ⟨k, hkM⟩
  let ta : ↥(normalizer (V : Set G)) := ⟨t, htM⟩
  have hρa : ρ (ka * ta) = 1 := (hρ1 (ka * ta)).mpr (fun v hv => by
    have h1 : (ka * ta : ↥(normalizer (V : Set G))) = ⟨a, haM⟩ := Subtype.ext hat.symm
    rw [h1]
    exact hAV a ha v hv)
  have hkt : ρ ka = (ρ ta)⁻¹ := by
    rw [map_mul] at hρa
    exact eq_inv_of_mul_eq_one_left hρa
  have hρt : ρ ta ^ (2 ^ e) = 1 := by
    rw [← map_pow]
    have : ta ^ (2 ^ e) = 1 := Subtype.ext (by simpa using he)
    rw [this, map_one]
  have hρk : ρ (ka ^ (2 ^ e)) = 1 := by
    rw [map_pow, hkt, inv_pow, hρt, inv_one]
  have hze : ∀ v ∈ V, k ^ (2 ^ e) * v = v * k ^ (2 ^ e) := by
    intro v hv
    have := (hρ1 (ka ^ (2 ^ e))).mp hρk v hv
    simpa using this
  have hzX : ∀ x ∈ K ⊓ normalizer (V : Set G), ∀ v ∈ V,
      k * (x * v * x⁻¹) * k⁻¹ = x * (k * v * k⁻¹) * x⁻¹ := by
    intro x hx v hv
    have hxK : x ∈ K := (Subgroup.mem_inf.mp hx).1
    have hxM : x ∈ normalizer (V : Set G) := (Subgroup.mem_inf.mp hx).2
    let xa : ↥(normalizer (V : Set G)) := ⟨x, hxM⟩
    have hcomm1 : ρ (ta * xa * ta⁻¹ * xa⁻¹) = 1 := (hρ1 _).mpr (fun w hw =>
      hNV _ ((Sit813.mem_rGrp_iff.mp ht).2.2 x hxK) w hw)
    have hcomm2 : Commute (ρ ta) (ρ xa) := by
      rw [← commutatorElement_eq_one_iff_commute]
      simpa only [commutatorElement_def, map_mul, map_inv] using hcomm1
    have hcomm3 : ρ ka * ρ xa = ρ xa * ρ ka := by
      rw [hkt]
      exact hcomm2.inv_left.eq
    have h3 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hcomm3
    simpa [hρ] using h3
  exact exists_fixed_of_commuting_two_element (X := K ⊓ normalizer (V : Set G)) hV
    h.card_V_eq_eight inf_le_right hkM e hze hkV hzX

theorem Sit813.exists_fixed_of_commute_A {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (hAV : ∀ a ∈ A, ∀ w ∈ V, a * w = w * a) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ k ∈ K ⊓ normalizer (V : Set G), k * v * k⁻¹ = v := by
  by_cases hNV : ∀ n ∈ oTwoMod (cGrp H T) K, ∀ w ∈ V, n * w = w * n
  · by_cases hnc : ∃ a ∈ A, ∃ k ∈ K ⊓ normalizer (V : Set G), ∃ t ∈ rGrp H T K,
        a = k * t ∧ ∃ w ∈ V, k * w ≠ w * k
    · obtain ⟨a, ha, k, hk, t, ht, hat, hkw⟩ := hnc
      exact h.exists_fixed_of_noncentral_decomp hAV hNV ha hk ht hat hkw
    · push Not at hnc
      exact h.exists_fixed_of_central_decomp hNV fun a ha k hk t ht hat => hnc a ha k hk t ht hat
  · push Not at hNV
    exact h.exists_fixed_of_noncomm_oTwoMod hNV

theorem Sit813.commutator_A_ne {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∃ a ∈ A, ∃ w ∈ V, a * w ≠ w * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hvV, hv1, hvfix⟩ := h.exists_fixed_of_commute_A hcon
  obtain ⟨a, ha, w, hw, hne⟩ := Five.five_conjugates h.fiveData hvV hv1 hvfix
  exact hne (hcon a ha w hw)

end CFSG.LocalAnalysis.WeakClosure81

end
