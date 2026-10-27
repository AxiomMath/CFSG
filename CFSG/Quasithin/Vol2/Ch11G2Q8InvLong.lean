module

public import CFSG.Quasithin.Vol2.Ch11G2Q8SiegelM

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

theorem exists_g2Act_eu_eq [Finite F] {w : Ix3 → F} (hw : w ≠ 0) :
    ∃ g : ↥(cayleyGroup F), g2Act g (eu 0 1) = w := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (normQ w)
  have hx : zI w + r • cayleyOne F ∈ CFSG.QuasithinUnique.Bridge.Alt57Model.nullPts F := by
    refine ⟨fun h0 => hw ?_, ?_, ?_⟩
    · have hz : zP (0 : quasithinZorn F) = 0 := by
        simpa using zP_smul (0 : F) (0 : quasithinZorn F)
      have h1 := congrArg zP h0
      rwa [zP_add, zP_zI, zP_smul, zP_one, smul_zero, add_zero, hz] at h1
    · rw [cayleyOne_eq, zmk_smul, zI, zmk_add, cayleyTr_zmk]
      linear_combination r * h2
    · rw [norm_add_smul_one (cayleyTr_zI w), cayleyNorm_zI, hr]
      linear_combination r * r * h2
  rw [← CFSG.QuasithinUnique.Bridge.Alt57Model.orbit_zU0_eq] at hx
  obtain ⟨g, hg⟩ := hx
  have hg' : g • zU0 F = zI w + r • cayleyOne F := hg
  refine ⟨g, ?_⟩
  rw [g2Act_apply, zI_eu]
  change zP (g • zU0 F) = w
  rw [hg', zP_add, zP_zI, zP_smul, zP_one, smul_zero, add_zero]

omit [CharP F 2] in
theorem polarQ_sub_left (x x' y : Ix3 → F) : polarQ (x - x') y = polarQ x y - polarQ x' y := by
  simp only [polarQ, Pi.sub_apply]
  ring

omit [CharP F 2] in
theorem polarQ_sub_right (x y y' : Ix3 → F) : polarQ x (y - y') = polarQ x y - polarQ x y' := by
  simp only [polarQ, Pi.sub_apply]
  ring

omit [CharP F 2] in
theorem eq_zero_of_polarQ {x : Ix3 → F} (h : ∀ y, polarQ x y = 0) : x = 0 := by
  have e0 := h (q6 0 0 0 1 0 0)
  have e1 := h (q6 0 0 0 0 1 0)
  have e2 := h (q6 0 0 0 0 0 1)
  have e3 := h (q6 1 0 0 0 0 0)
  have e4 := h (q6 0 1 0 0 0 0)
  have e5 := h (q6 0 0 1 0 0 0)
  simp [polarQ, q6] at e0 e1 e2 e3 e4 e5
  funext j
  rcases j with j | j <;> fin_cases j <;> assumption

omit [CharP F 2] in
theorem polarQ_F3 {x y : Ix3 → F} (hx : x ∈ stdF F 3) (hy : y ∈ stdF F 3) : polarQ x y = 0 := by
  obtain ⟨a1, a2, a3⟩ := mem_stdF_three.mp hx
  obtain ⟨b1, b2, b3⟩ := mem_stdF_three.mp hy
  simp only [polarQ, a1, a2, a3, b1, b2, b3]
  ring

theorem fix_F3_of_comm_le {y : ↥(cayleyGroup F)} (hy : ∀ z, g2Act y z - z ∈ stdF F 3)
    {w : Ix3 → F} (hw : w ∈ stdF F 3) : g2Act y w = w := by
  have h1 : ∀ z, polarQ (g2Act y w - w) (g2Act y z) = 0 := by
    intro z
    rw [polarQ_sub_left, polarQ_g2Act, ← polarQ_sub_right]
    have h2 : z - g2Act y z = -(g2Act y z - z) := by abel
    rw [h2, show polarQ w (-(g2Act y z - z)) = -polarQ w (g2Act y z - z) by
      simp only [polarQ, Pi.neg_apply]; ring, polarQ_F3 hw (hy z), neg_zero]
  have h3 : g2Act y w - w = 0 := eq_zero_of_polarQ fun z => by
    rw [← g2Act_apply_inv y z]
    exact h1 _
  exact sub_eq_zero.mp h3

@[expose] def commMap (y : ↥(cayleyGroup F)) : (Ix3 → F) →+ (Ix3 → F) where
  toFun z := g2Act y z - z
  map_zero' := by rw [map_zero, sub_zero]
  map_add' a b := by
    rw [map_add]
    abel

theorem commMap_apply (y : ↥(cayleyGroup F)) (z : Ix3 → F) : commMap y z = g2Act y z - z := rfl

@[expose] def fixQ (y : ↥(cayleyGroup F)) : AddSubgroup (Ix3 → F) := (commMap y).ker

theorem mem_fixQ {y : ↥(cayleyGroup F)} {w : Ix3 → F} : w ∈ fixQ y ↔ g2Act y w = w := by
  rw [fixQ, AddMonoidHom.mem_ker, commMap_apply, sub_eq_zero]

@[expose] def commQ (y : ↥(cayleyGroup F)) : AddSubgroup (Ix3 → F) := (commMap y).range

theorem mem_commQ {y : ↥(cayleyGroup F)} {w : Ix3 → F} :
    w ∈ commQ y ↔ ∃ z, g2Act y z - z = w := by
  rw [commQ, AddMonoidHom.mem_range]
  simp only [commMap_apply]

theorem card_commQ_mul_card_fixQ [Finite F] (y : ↥(cayleyGroup F)) :
    Nat.card (commQ y) * Nat.card (fixQ y) = Nat.card (Ix3 → F) := by
  rw [commQ, fixQ, ← Nat.card_congr
    (QuotientAddGroup.quotientKerEquivRange (commMap y)).toEquiv,
    ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]

theorem card_fix_mul_le [Finite F] {y : ↥(cayleyGroup F)} (φ : (Fin 3 → F) →+ (Ix3 → F))
    (hφ : ∀ t, φ t ∈ fixQ y → t = 0) :
    Nat.card (fixQ y) * Nat.card F ^ 3 ≤ Nat.card (Ix3 → F) := by
  let ψ : ↥(fixQ y) × (Fin 3 → F) → Ix3 → F := fun p => p.1.1 + φ p.2
  have hψ : Function.Injective ψ := by
    rintro ⟨⟨x, hx⟩, t⟩ ⟨⟨x', hx'⟩, t'⟩ h
    simp only [ψ] at h
    have h1 : φ (t - t') ∈ fixQ y := by
      rw [map_sub, show φ t - φ t' = x' - x by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, ← h, add_comm]]
      exact (fixQ y).sub_mem hx' hx
    have htt : t = t' := sub_eq_zero.mp (hφ _ h1)
    subst htt
    have hxx : x = x' := add_right_cancel h
    subst hxx
    rfl
  have h1 := Nat.card_le_card_of_injective ψ hψ
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_fin] at h1

omit [Field F] [CharP F 2] in
theorem card_Q [Finite F] : Nat.card (Ix3 → F) = Nat.card F ^ 6 := by
  rw [Nat.card_fun]
  simp

theorem eq_of_levi1Mat_eq_one {g : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F)
    (hM : levi1Mat g = 1) : ∃ α β γ p q' : F,
      g = g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0) := by
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hg
  rw [levi1Mat_decomp hA, levi1Mat_g2A hA] at hM
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp at e00 e01 e10 e11
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hU : ((uSL ((A : Matrix (Fin 3) (Fin 3) F) 0 1) ((A : Matrix (Fin 3) (Fin 3) F) 0 2) 0 :
      SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, (A : Matrix (Fin 3) (Fin 3) F) 0 1,
        (A : Matrix (Fin 3) (Fin 3) F) 0 2; 0, 1, 0; 0, 0, 1] := rfl
  have hAeq :
      A = uSL ((A : Matrix (Fin 3) (Fin 3) F) 0 1) ((A : Matrix (Fin 3) (Fin 3) F) 0 2) 0 := by
    ext i j
    rw [hU]
    fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, e00, e01, e10, e11]
  refine ⟨α, β, γ, (A : Matrix (Fin 3) (Fin 3) F) 0 1, (A : Matrix (Fin 3) (Fin 3) F) 0 2, ?_⟩
  rw [← hAeq]

theorem g2Act_kerElt (α β γ p q' a b c d e f : F) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)) (q6 a b c d e f) =
      q6 ((a + p * b + q' * c + β * (f + q' * d) + γ * (e + p * d)) + α * α * d)
        (b + γ * d) (c + β * d) d
        ((e + p * d + (β * b + γ * c) * β) + α * (c + β * d))
        ((f + q' * d + (β * b + γ * c) * γ) + α * (b + γ * d)) := by
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_g2A_uSL]
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2]
  rw [g2Act_y12q, g2Act_x0q]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

omit [CharP F 2] in
theorem q6_add' (a b c d e f a' b' c' d' e' f' : F) :
    q6 a b c d e f + q6 a' b' c' d' e' f' =
      q6 (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') := by
  funext j
  rcases j with j | j <;> fin_cases j <;> rfl

@[expose] def q6Hom (f₀ f₁ f₂ f₃ f₄ f₅ : (Fin 3 → F) →+ F) : (Fin 3 → F) →+ (Ix3 → F) where
  toFun t := q6 (f₀ t) (f₁ t) (f₂ t) (f₃ t) (f₄ t) (f₅ t)
  map_zero' := by simp only [map_zero, q6_zero]
  map_add' t t' := by simp only [map_add, q6_add']

omit [CharP F 2] in
theorem q6Hom_apply (f₀ f₁ f₂ f₃ f₄ f₅ : (Fin 3 → F) →+ F) (t : Fin 3 → F) :
    q6Hom f₀ f₁ f₂ f₃ f₄ f₅ t = q6 (f₀ t) (f₁ t) (f₂ t) (f₃ t) (f₄ t) (f₅ t) := rfl

theorem kerElt_eq [Finite F] {α β γ p q' : F}
    (hfix : Nat.card F ^ 4 ≤
      Nat.card (fixQ (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)))) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have key : ∀ φ : (Fin 3 → F) →+ (Ix3 → F),
      (∀ t, φ t ∈ fixQ (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)) → t = 0) → False := by
    intro φ hφ
    have h1 := card_fix_mul_le φ hφ
    rw [card_Q] at h1
    have h3 : Nat.card F ^ 4 * Nat.card F ^ 3 ≤ Nat.card F ^ 6 :=
      le_trans (Nat.mul_le_mul_right _ hfix) h1
    rw [← pow_add] at h3
    have h4 : Nat.card F ^ 6 < Nat.card F ^ (4 + 3) := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have ev : ∀ i : Fin 3, ∃ f : (Fin 3 → F) →+ F, ∀ t, f t = t i := fun i =>
    ⟨Pi.evalAddMonoidHom (fun _ => F) i, fun _ => rfl⟩
  obtain ⟨π₀, hπ₀⟩ := ev 0
  obtain ⟨π₁, hπ₁⟩ := ev 1
  obtain ⟨π₂, hπ₂⟩ := ev 2
  have hzero : ∀ t : Fin 3 → F, t 0 = 0 → t 1 = 0 → t 2 = 0 → t = 0 := by
    intro t h0 h1 h3
    funext i
    fin_cases i <;> assumption
  have hβ : β = 0 := by
    by_contra hβ
    refine key (q6Hom 0 π₁ 0 π₂ 0 π₀) fun t ht => ?_
    rw [mem_fixQ, q6Hom_apply, g2Act_kerElt] at ht
    simp only [AddMonoidHom.zero_apply, hπ₀, hπ₁, hπ₂] at ht
    obtain ⟨e0, -, e2, -, e4, -⟩ := q6_inj ht
    have t2 : t 2 = 0 := (mul_eq_zero.mp (by linear_combination e2)).resolve_left hβ
    have t1 : t 1 = 0 := by
      have : β * β * t 1 = 0 := by linear_combination e4 - (p + α * β) * t2
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hβ hβ)
    have t0 : t 0 = 0 := by
      have : β * t 0 = 0 := by
        linear_combination e0 - p * t1 - (β * q' + γ * p + α * α) * t2
      exact (mul_eq_zero.mp this).resolve_left hβ
    exact hzero t t0 t1 t2
  subst hβ
  have hγ : γ = 0 := by
    by_contra hγ
    refine key (q6Hom 0 0 π₂ π₁ π₀ 0) fun t ht => ?_
    rw [mem_fixQ, q6Hom_apply, g2Act_kerElt] at ht
    simp only [AddMonoidHom.zero_apply, hπ₀, hπ₁, hπ₂] at ht
    obtain ⟨e0, e1, -, -, -, e5⟩ := q6_inj ht
    have t1 : t 1 = 0 := (mul_eq_zero.mp (by linear_combination e1)).resolve_left hγ
    have t2 : t 2 = 0 := by
      have : γ * γ * t 2 = 0 := by linear_combination e5 - (q' + α * γ) * t1
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hγ hγ)
    have t0 : t 0 = 0 := by
      have : γ * t 0 = 0 := by
        linear_combination e0 - q' * t2 - (γ * p + α * α) * t1
      exact (mul_eq_zero.mp this).resolve_left hγ
    exact hzero t t0 t1 t2
  subst hγ
  refine ⟨?_, rfl, rfl⟩
  by_contra hα
  refine key (q6Hom 0 π₀ π₁ π₂ 0 0) fun t ht => ?_
  rw [mem_fixQ, q6Hom_apply, g2Act_kerElt] at ht
  simp only [AddMonoidHom.zero_apply, hπ₀, hπ₁, hπ₂] at ht
  obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj ht
  have t2 : t 2 = 0 := by
    have : α ^ 3 * t 2 = 0 := by
      linear_combination α * e0 - p * e5 - q' * e4 + p * q' * t 2 * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hα)
  have t1 : t 1 = 0 := by
    have : α * t 1 = 0 := by linear_combination e4 - p * t2
    exact (mul_eq_zero.mp this).resolve_left hα
  have t0 : t 0 = 0 := by
    have : α * t 0 = 0 := by linear_combination e5 - q' * t2
    exact (mul_eq_zero.mp this).resolve_left hα
  exact hzero t t0 t1 t2

omit [CharP F 2] in
theorem uSL_mul_blockSL {p q' : F} (N : SpecialLinearGroup (Fin 2) F)
    (h1 : (N : Matrix (Fin 2) (Fin 2) F) 1 1 = q') (h2 : (N : Matrix (Fin 2) (Fin 2) F) 0 1 = -p)
    (h3 : p * (N : Matrix (Fin 2) (Fin 2) F) 1 0 + q' * (N : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) :
    uSL p q' 0 * blockSL N = blockSL N * tv 0 2 (by decide) 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have eN : ((blockSL N : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, (N : Matrix (Fin 2) (Fin 2) F) 1 1, (N : Matrix (Fin 2) (Fin 2) F) 1 0;
        0, (N : Matrix (Fin 2) (Fin 2) F) 0 1, (N : Matrix (Fin 2) (Fin 2) F) 0 0] := rfl
  have eT : ((tv 0 2 (by decide) (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.transvection 0 2 1 := rfl
  show ((uSL p q' 0 : SL3 F) * (blockSL N : Matrix (Fin 3) (Fin 3) F)) i j =
    ((blockSL N : Matrix (Fin 3) (Fin 3) F) * (tv 0 2 (by decide) (1 : F) : SL3 F)) i j
  rw [eN, eT, CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL, h1, h2]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.transvection, mul_comm p q', h3]

omit [CharP F 2] in
theorem exists_blockSL (p q' : F) (hpq : p ≠ 0 ∨ q' ≠ 0) :
    ∃ N : SpecialLinearGroup (Fin 2) F, (N : Matrix (Fin 2) (Fin 2) F) 1 1 = q' ∧
      (N : Matrix (Fin 2) (Fin 2) F) 0 1 = -p ∧
      p * (N : Matrix (Fin 2) (Fin 2) F) 1 0 + q' * (N : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
  by_cases hq : q' = 0
  · subst hq
    have hp : p ≠ 0 := hpq.resolve_right (not_not.mpr rfl)
    refine ⟨⟨!![0, -p; p⁻¹, 0], by simp [det_fin_two, hp]⟩, rfl, rfl, ?_⟩
    simp [hp]
  · refine ⟨⟨!![q'⁻¹, -p; 0, q'], by simp [det_fin_two, hq]⟩, rfl, rfl, ?_⟩
    simp [hq]

omit [CharP F 2] in
theorem card_le_of_three [Finite F] (S : AddSubgroup (Ix3 → F)) {x₁ x₂ x₃ : Ix3 → F}
    (hS : ∀ a b c : F, a • x₁ + b • x₂ + c • x₃ ∈ S)
    (hind : ∀ a b c : F, a • x₁ + b • x₂ + c • x₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    Nat.card F ^ 3 ≤ Nat.card S := by
  let ψ : (Fin 3 → F) → S := fun t => ⟨t 0 • x₁ + t 1 • x₂ + t 2 • x₃, hS _ _ _⟩
  have hψ : Function.Injective ψ := by
    intro t t' h
    have h1 : t 0 • x₁ + t 1 • x₂ + t 2 • x₃ = t' 0 • x₁ + t' 1 • x₂ + t' 2 • x₃ :=
      congrArg Subtype.val h
    have h2 : (t 0 - t' 0) • x₁ + (t 1 - t' 1) • x₂ + (t 2 - t' 2) • x₃ = 0 := by
      have e : (t 0 - t' 0) • x₁ + (t 1 - t' 1) • x₂ + (t 2 - t' 2) • x₃ =
          (t 0 • x₁ + t 1 • x₂ + t 2 • x₃) - (t' 0 • x₁ + t' 1 • x₂ + t' 2 • x₃) := by
        simp only [sub_smul]
        abel
      rw [e, h1, sub_self]
    obtain ⟨e0, e1, e2⟩ := hind _ _ _ h2
    funext i
    fin_cases i
    · exact sub_eq_zero.mp e0
    · exact sub_eq_zero.mp e1
    · exact sub_eq_zero.mp e2
  have h1 := Nat.card_le_card_of_injective ψ hψ
  rwa [Nat.card_fun, Nat.card_fin] at h1

theorem levi1Mat_eq_one_of_comm [Finite F] {y : ↥(cayleyGroup F)} (hy : y ∈ stabV0 F)
    (hc : Nat.card (commQ y) < Nat.card F ^ 3) {z₀ : Ix3 → F}
    (hz₀ : g2Act y z₀ - z₀ = eu 0 1) : levi1Mat y = 1 := by
  have hu : eu (0 : Fin 3) (1 : F) ∈ stdF F 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have hu0 : eu (0 : Fin 3) (1 : F) ≠ 0 := by
    intro h0
    have := congrFun h0 (.inl 0)
    simp at this
  have hvu : vpart (eu (0 : Fin 3) (1 : F)) = 0 := by
    funext i
    fin_cases i <;> rfl
  have key : ∀ v ∈ stdF F 3, vpart (g2Act y v - v) = 0 := by
    intro v hv
    by_contra hne
    have hw' : g2Act y v - v ∈ stdF F 3 := (stdF F 3).sub_mem (mapsF3_of_mem hy v hv) hv
    have hF3 : ∀ z, g2Act y z - z ∈ stdF F 3 := by
      intro z
      by_contra hz
      refine absurd hc (not_lt.mpr (card_le_of_three (commQ y) (x₁ := eu 0 1)
        (x₂ := g2Act y v - v) (x₃ := g2Act y z - z) (fun a b c => ?_) (fun a b c habc => ?_)))
      · refine mem_commQ.mpr ⟨a • z₀ + b • v + c • z, ?_⟩
        rw [map_add, map_add, g2Act_smul, g2Act_smul, g2Act_smul, ← hz₀]
        simp only [smul_sub]
        abel
      · have hc0 : c = 0 := by
          by_contra hc0
          apply hz
          have e : c • (g2Act y z - z) = -(a • eu 0 1 + b • (g2Act y v - v)) :=
            eq_neg_of_add_eq_zero_right habc
          have hmem : c • (g2Act y z - z) ∈ stdF F 3 := by
            rw [e]
            exact (stdF F 3).neg_mem ((stdF F 3).add_mem ((stdF F 3).smul_mem a hu)
              ((stdF F 3).smul_mem b hw'))
          exact (Submodule.smul_mem_iff _ hc0).mp hmem
        subst hc0
        rw [zero_smul, add_zero] at habc
        have hb : b = 0 := by
          have h1 := congrArg vpart habc
          rw [vpart_add, vpart_smul, vpart_smul, hvu, smul_zero, zero_add] at h1
          have h0 : vpart (0 : Ix3 → F) = 0 := by
            funext i
            fin_cases i <;> rfl
          rw [h0, smul_eq_zero] at h1
          exact h1.resolve_right hne
        subst hb
        rw [zero_smul, add_zero, smul_eq_zero] at habc
        exact ⟨habc.resolve_right hu0, rfl, rfl⟩
    apply hne
    rw [fix_F3_of_comm_le hF3 hv, sub_self]
    funext i
    fin_cases i <;> rfl
  ext i j
  rw [levi1Mat_apply]
  have hmem : q6 (0 : F) 0 0 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) ∈ stdF F 3 :=
    mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have h1 := vpart_add (g2Act y (q6 (0 : F) 0 0 0 (if j = 0 then 1 else 0)
    (if j = 1 then 1 else 0)) - q6 (0 : F) 0 0 0 (if j = 0 then 1 else 0)
    (if j = 1 then 1 else 0)) (q6 (0 : F) 0 0 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0))
  rw [sub_add_cancel, key _ hmem, zero_add] at h1
  rw [h1]
  fin_cases i <;> fin_cases j <;> simp [vpart, q6]

theorem eq_conj_tL_of_fix [Finite F] {h : ↥(cayleyGroup F)} (hh : h * h = 1) (h1 : h ≠ 1)
    (hfix : Nat.card F ^ 4 ≤ Nat.card (fixQ h)) : ∃ x, h = x * tL 1 * x⁻¹ := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hneg : ∀ x : Ix3 → F, -x = x := fun x => by
    funext j
    exact CharTwo.neg_eq (x j)
  obtain ⟨w, hw⟩ : ∃ w, g2Act h w ≠ w := by
    by_contra hne
    exact h1 (cayley_eq_one fun w => by_contra fun hw => hne ⟨w, hw⟩)
  have h2 : g2Act h (g2Act h w) = w := by
    rw [← g2Act_mul_apply, hh, map_one]
    rfl
  have hx0 : g2Act h (g2Act h w - w) = g2Act h w - w := by
    rw [map_sub, h2]
    exact (neg_sub _ _).symm.trans (hneg _)
  obtain ⟨g, hg⟩ := exists_g2Act_eu_eq (sub_ne_zero.mpr hw)
  obtain ⟨h', hh'⟩ : ∃ h', h' = g⁻¹ * h * g := ⟨_, rfl⟩
  have hact : ∀ v, g2Act h' v = g2Act g⁻¹ (g2Act h (g2Act g v)) := by
    intro v
    rw [hh', g2Act_mul_apply, g2Act_mul_apply]
  have hS : h' ∈ stabV0 F := by
    show g2Act h' (eu 0 1) = eu 0 1
    rw [hact, hg, hx0, ← hg, g2Act_inv_apply]
  have hz0 : g2Act h' (g2Act g⁻¹ w) - g2Act g⁻¹ w = eu 0 1 := by
    rw [hact, g2Act_apply_inv, ← map_sub, ← hg, g2Act_inv_apply]
  have hfix' : Nat.card F ^ 4 ≤ Nat.card (fixQ h') := by
    refine hfix.trans (Nat.card_le_card_of_injective
      (fun v : fixQ h => (⟨g2Act g⁻¹ v.1, ?_⟩ : fixQ h')) ?_)
    · rw [mem_fixQ, hact, g2Act_apply_inv, mem_fixQ.mp v.2]
    · intro a b hab
      have hab' : g2Act g⁻¹ a.1 = g2Act g⁻¹ b.1 := congrArg Subtype.val hab
      have h3 := congrArg (g2Act g) hab'
      rw [g2Act_apply_inv, g2Act_apply_inv] at h3
      exact Subtype.ext h3
  have hcomm : Nat.card (commQ h') < Nat.card F ^ 3 := by
    by_contra hlt
    have h3 := Nat.mul_le_mul (not_lt.mp hlt) hfix'
    rw [card_commQ_mul_card_fixQ, ← pow_add, card_Q] at h3
    have h4 : Nat.card F ^ 6 < Nat.card F ^ (3 + 4) := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  obtain ⟨α, β, γ, p, q', hform⟩ :=
    eq_of_levi1Mat_eq_one hS (levi1Mat_eq_one_of_comm hS hcomm hz0)
  rw [hform] at hfix'
  obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq hfix'
  have hz3 : (![0, 0, 0] : Fin 3 → F) = 0 := by
    funext i
    fin_cases i <;> rfl
  rw [hz3, g2X_zero, g2Y_zero, one_mul, one_mul] at hform
  have hne : h' ≠ 1 := by
    intro h0
    apply h1
    rw [hh'] at h0
    calc h = g * (g⁻¹ * h * g) * g⁻¹ := by group
      _ = 1 := by rw [h0]; group
  have hpq : p ≠ 0 ∨ q' ≠ 0 := by
    by_contra hpq
    obtain ⟨hp, hq'⟩ := not_or.mp hpq
    rw [not_not] at hp hq'
    subst hp hq'
    exact hne (by rw [hform, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one])
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_blockSL p q' hpq
  have hB := uSL_mul_blockSL N hN1 hN2 hN3
  have h5 : h' = g2A (blockSL N) * tL 1 * (g2A (blockSL N))⁻¹ := by
    rw [hform]
    apply eq_mul_inv_of_mul_eq
    show g2A (uSL p q' 0) * g2A (blockSL N) = g2A (blockSL N) * g2A (tv 0 2 (by decide) 1)
    rw [← map_mul, hB, map_mul]
  refine ⟨g * g2A (blockSL N), ?_⟩
  calc h = g * h' * g⁻¹ := by rw [hh']; group
    _ = g * g2A (blockSL N) * tL 1 * (g * g2A (blockSL N))⁻¹ := by rw [h5]; group

end CFSG.Quasithin.Vol2.Ch11.G2Q8
