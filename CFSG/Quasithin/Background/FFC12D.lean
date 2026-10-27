module

public import CFSG.Quasithin.Background.FFC12A
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonUnipotent

public section

namespace CFSG.Quasithin

open CFSG.Glauberman.Dickson

namespace B69

variable {K : Type} [Field K]

@[expose] def lowerUniSL2 (s : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def weylElemSL2 (c : K) (hc : c ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -c⁻¹; c, 0], by simp [Matrix.det_fin_two, hc]⟩

theorem lowerUniSL2_coe (s : K) : (lowerUniSL2 s : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] := rfl
theorem weylElemSL2_coe (c : K) (hc : c ≠ 0) : (weylElemSL2 c hc : Matrix (Fin 2) (Fin 2) K) = !![0, -c⁻¹; c, 0] := rfl

theorem upper_mul_mul_upper_eq_weyl (g : Matrix.SpecialLinearGroup (Fin 2) K) (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    unipotentSLAddChar K (-((g : Matrix (Fin 2) (Fin 2) K) 0 0) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) * g *
      unipotentSLAddChar K (-((g : Matrix (Fin 2) (Fin 2) K) 1 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) =
    weylElemSL2 ((g : Matrix (Fin 2) (Fin 2) K) 1 0) hc := by
  have hdet := g.property
  rw [Matrix.det_fin_two] at hdet
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = !![(g : Matrix (Fin 2) (Fin 2) K) 0 0, (g : Matrix (Fin 2) (Fin 2) K) 0 1;
      (g : Matrix (Fin 2) (Fin 2) K) 1 0, (g : Matrix (Fin 2) (Fin 2) K) 1 1] := Matrix.eta_fin_two _
  generalize (g : Matrix (Fin 2) (Fin 2) K) 0 0 = a at hg hdet hc ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) K) 0 1 = b at hg hdet hc ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) K) 1 0 = c at hg hdet hc ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) K) 1 1 = d at hg hdet hc ⊢
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, weylElemSL2_coe]
  simp only [unipotentSLAddChar_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> first | ring1 | linear_combination hdet | linear_combination (-1 : K) * hdet

theorem weylElemSL2_mul_upper (c : K) (hc : c ≠ 0) (t : K) :
    weylElemSL2 c hc * unipotentSLAddChar K t = lowerUniSL2 (-(c ^ 2) * t) * weylElemSL2 c hc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, weylElemSL2_coe, lowerUniSL2_coe,
    unipotentSLAddChar_coe]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp
  field_simp

theorem upperUni_mul_lowerUni_mul_upperUni (c : K) (hc : c ≠ 0) :
    unipotentSLAddChar K (-c⁻¹) * lowerUniSL2 c * unipotentSLAddChar K (-c⁻¹) = weylElemSL2 c hc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, weylElemSL2_coe, lowerUniSL2_coe,
    unipotentSLAddChar_coe]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [hc]

theorem sl2_overgroup_upperUni (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (hU : ∀ t : K, unipotentSLAddChar K t ∈ R) :
    R = ⊤ ∨ ∀ g ∈ R, ∀ t : K, ∃ t' : K,
      g * unipotentSLAddChar K t * g⁻¹ = unipotentSLAddChar K t' := by
  by_cases h : ∀ g ∈ R, (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · right
    intro g hg t
    exact ⟨_, unipotentSLAddChar_conj_of_lowerLeft_eq_zero g (h g hg) t⟩
  · left
    push Not at h
    obtain ⟨g₀, hg₀R, hg₀⟩ := h
    have hw₀ : weylElemSL2 ((g₀ : Matrix (Fin 2) (Fin 2) K) 1 0) hg₀ ∈ R := by
      rw [← upper_mul_mul_upper_eq_weyl g₀ hg₀]
      exact R.mul_mem (R.mul_mem (hU _) hg₀R) (hU _)
    have hlow : ∀ s : K, lowerUniSL2 s ∈ R := by
      intro s
      set c₀ : K := (g₀ : Matrix (Fin 2) (Fin 2) K) 1 0 with hc₀
      have h1 : lowerUniSL2 (-(c₀ ^ 2) * (-s / c₀ ^ 2)) = weylElemSL2 c₀ hg₀ * unipotentSLAddChar K (-s / c₀ ^ 2) *
          (weylElemSL2 c₀ hg₀)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, weylElemSL2_mul_upper]
      have h2 : -(c₀ ^ 2) * (-s / c₀ ^ 2) = s := by field_simp
      rw [h2] at h1
      rw [h1]
      exact R.mul_mem (R.mul_mem hw₀ (hU _)) (R.inv_mem hw₀)
    have hw : ∀ (c : K) (hc : c ≠ 0), weylElemSL2 c hc ∈ R := by
      intro c hc
      rw [← upperUni_mul_lowerUni_mul_upperUni c hc]
      exact R.mul_mem (R.mul_mem (hU _) (hlow _)) (hU _)
    have hbig : ∀ h : Matrix.SpecialLinearGroup (Fin 2) K,
        (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → h ∈ R := by
      intro h hh
      have e := upper_mul_mul_upper_eq_weyl h hh
      have hm : unipotentSLAddChar K (-((h : Matrix (Fin 2) (Fin 2) K) 0 0) / (h : Matrix (Fin 2) (Fin 2) K) 1 0) *
          h * unipotentSLAddChar K (-((h : Matrix (Fin 2) (Fin 2) K) 1 1) / (h : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ R := by
        rw [e]
        exact hw _ hh
      have h3 : h = (unipotentSLAddChar K (-((h : Matrix (Fin 2) (Fin 2) K) 0 0) / (h : Matrix (Fin 2) (Fin 2) K) 1 0))⁻¹ *
          (unipotentSLAddChar K (-((h : Matrix (Fin 2) (Fin 2) K) 0 0) / (h : Matrix (Fin 2) (Fin 2) K) 1 0) *
          h * unipotentSLAddChar K (-((h : Matrix (Fin 2) (Fin 2) K) 1 1) / (h : Matrix (Fin 2) (Fin 2) K) 1 0)) *
          (unipotentSLAddChar K (-((h : Matrix (Fin 2) (Fin 2) K) 1 1) / (h : Matrix (Fin 2) (Fin 2) K) 1 0))⁻¹ := by
        group
      rw [h3]
      exact R.mul_mem (R.mul_mem (R.inv_mem (hU _)) hm) (R.inv_mem (hU _))
    rw [eq_top_iff]
    intro h _
    by_cases hh : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · have hdet := h.property
      rw [Matrix.det_fin_two, hh, mul_zero, sub_zero] at hdet
      have h11 : (h : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
      have hw1 := hw 1 one_ne_zero
      have hprod : h * weylElemSL2 1 one_ne_zero ∈ R := by
        apply hbig
        rw [Matrix.SpecialLinearGroup.coe_mul, weylElemSL2_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two, hh, h11]
      have h3 : h = (h * weylElemSL2 1 one_ne_zero) * (weylElemSL2 1 one_ne_zero)⁻¹ := by group
      rw [h3]
      exact R.mul_mem hprod (R.inv_mem hw1)
    · exact hbig h hh

@[expose] def upperUniSL2 (K : Type) [Field K] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := Set.range (unipotentSLAddChar K)
  one_mem' := ⟨0, AddChar.map_zero_eq_one _⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, AddChar.map_add_eq_mul _ a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, AddChar.map_neg_eq_inv _ a⟩

theorem unipotentSLAddChar_injective : Function.Injective (unipotentSLAddChar K) := by
  intro a b hab
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hab
  simpa using this

theorem card_upperUniSL2 [Finite K] : Nat.card (upperUniSL2 K) = Nat.card K :=
  (Nat.card_congr (Equiv.ofInjective (unipotentSLAddChar K) unipotentSLAddChar_injective)).symm

theorem upperUniSL2_isPGroup_index [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e) :
    IsPGroup 2 (upperUniSL2 K) ∧ ¬ 2 ∣ (upperUniSL2 K).index := by
  have h1 : IsPGroup 2 (upperUniSL2 K) := IsPGroup.of_card (n := e) (by rw [card_upperUniSL2, hK])
  refine ⟨h1, ?_⟩
  have h2 := Subgroup.card_mul_index (upperUniSL2 K)
  rw [card_upperUniSL2, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K] at h2
  have h3 : (upperUniSL2 K).index = Nat.card K ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  rw [h3]
  intro h2d
  exact (Nat.not_even_iff_odd.2 (odd_card_sq_sub_one he hK)) (even_iff_two_dvd.2 h2d)

theorem exists_conj_upperUniSL2_eq [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e) {Λ : Type*}
    [Group Λ] (π : Matrix.SpecialLinearGroup (Fin 2) K →* Λ) (hπ : Function.Surjective π)
    {U : Subgroup Λ} (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) K, ∀ w : Λ,
      w ∈ U ↔ ∃ t : K, w = π (s * unipotentSLAddChar K t * s⁻¹) := by
  have : Finite Λ := Finite.of_surjective π hπ
  obtain ⟨hP, hI⟩ := upperUniSL2_isPGroup_index he hK
  let P₀ : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K) := hP.toSylow hI
  let P₁ : Sylow 2 Λ := P₀.mapSurjective hπ
  let PU : Sylow 2 Λ := hUp.toSylow hUi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Λ P₁ PU
  obtain ⟨s, rfl⟩ := hπ g
  refine ⟨s, fun w => ?_⟩
  have hU : (PU : Subgroup Λ) = U := rfl
  have h1 : (PU : Subgroup Λ) = ((π s) • P₁ : Sylow 2 Λ) := by rw [hg]
  rw [← hU, h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have h2 : (P₁ : Subgroup Λ) = (upperUniSL2 K).map π := rfl
  have hconj : ∀ (g x : Λ), (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    intro g x
    simp [MulAut.smul_def, MulAut.conj_symm_apply]
  rw [h2]
  constructor
  · intro hw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 hw
    obtain ⟨t, rfl⟩ := hy
    refine ⟨t, ?_⟩
    have : w = π s * π (unipotentSLAddChar K t) * (π s)⁻¹ := by
      have e1 : (MulAut.conj (π s))⁻¹ • w = π (unipotentSLAddChar K t) := hyw.symm
      rw [hconj] at e1
      calc w = π s * ((π s)⁻¹ * w * π s) * (π s)⁻¹ := by group
        _ = _ := by rw [e1]
    rw [this]
    simp [map_mul, map_inv]
  · rintro ⟨t, rfl⟩
    refine Subgroup.mem_map.2 ⟨unipotentSLAddChar K t, ⟨t, rfl⟩, ?_⟩
    rw [hconj]
    simp [map_mul, map_inv]
    group

theorem overgroup_sylow_of_quotient_sl2 [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e)
    {Λ : Type*} [Group Λ] (π : Matrix.SpecialLinearGroup (Fin 2) K →* Λ)
    (hπ : Function.Surjective π) {U R : Subgroup Λ} (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (hUR : U ≤ R) : R = ⊤ ∨ R ≤ Subgroup.normalizer (U : Set Λ) := by
  obtain ⟨s, hs⟩ := exists_conj_upperUniSL2_eq he hK π hπ hUp hUi
  let R'' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (R.comap π).comap (MulAut.conj s).toMonoidHom
  have hmem : ∀ g, g ∈ R'' ↔ π (s * g * s⁻¹) ∈ R := fun g => Iff.rfl
  have hU'' : ∀ t, unipotentSLAddChar K t ∈ R'' := by
    intro t
    rw [hmem]
    exact hUR ((hs _).2 ⟨t, rfl⟩)
  have hback : ∀ y : Matrix.SpecialLinearGroup (Fin 2) K, π y ∈ R → s⁻¹ * y * s ∈ R'' := by
    intro y hy
    rw [hmem]
    have : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rw [this]
    exact hy
  rcases sl2_overgroup_upperUni R'' hU'' with h | h
  · left
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hπ x
    have hg : s⁻¹ * y * s ∈ R'' := by rw [h]; trivial
    rw [hmem] at hg
    have : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rw [this] at hg
    exact hg
  · right
    have key : ∀ y : Matrix.SpecialLinearGroup (Fin 2) K, π y ∈ R → ∀ w ∈ U,
        π y * w * (π y)⁻¹ ∈ U := by
      intro y hy w hw
      obtain ⟨t, rfl⟩ := (hs w).1 hw
      obtain ⟨t', ht'⟩ := h _ (hback y hy) t
      refine (hs _).2 ⟨t', ?_⟩
      have e1 : y * (s * unipotentSLAddChar K t * s⁻¹) * y⁻¹ =
          s * ((s⁻¹ * y * s) * unipotentSLAddChar K t * (s⁻¹ * y * s)⁻¹) * s⁻¹ := by group
      rw [← map_inv, ← map_mul, ← map_mul, e1, ht']
    intro x hx
    obtain ⟨y, rfl⟩ := hπ x
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact fun hw => key y hx w hw
    · intro hw
      have hy' : π y⁻¹ ∈ R := by rw [map_inv]; exact R.inv_mem hx
      have := key y⁻¹ hy' _ hw
      rw [map_inv] at this
      simpa [mul_assoc] using this

end B69

end CFSG.Quasithin
