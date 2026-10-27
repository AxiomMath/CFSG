module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W9
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4SixA
public import CFSG.Quasithin.H13.U3S1348H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Induced

variable {Q : Type} [CommGroup Q] {W : Type} [Group W] [Finite W]

theorem exists_indHom627 {N Z : Subgroup Q} (β : ↥N →* W) (hβs : Function.Surjective β)
    (hβk : ∀ n, β n = 1 ↔ (n : Q) ∈ Z) {Y : Subgroup (MulAut Q)}
    (hYN : ∀ y ∈ Y, ∀ n ∈ N, y n ∈ N) (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y z ∈ Z) :
    ∃ ψ : ↥Y →* MulAut W, ∀ (y : ↥Y) (n : ↥N),
      ψ y (β n) = β ⟨(y : MulAut Q) n, hYN y y.2 n n.2⟩ := by
  classical
  have hex : ∀ y : ↥Y, ∃ δW : MulAut W, ∀ n : ↥N,
      δW (β n) = β ⟨(y : MulAut Q) n, hYN y y.2 n n.2⟩ := fun y =>
    exists_induced627 β hβs (hYN y y.2) (fun n hn => hYN (y : MulAut Q)⁻¹ (Y.inv_mem y.2) n hn)
      fun n hn => (hβk _).mpr (hYZ y y.2 n ((hβk n).mp hn))
  choose f hf using hex
  have hext : ∀ φ₁ φ₂ : MulAut W, (∀ n : ↥N, φ₁ (β n) = φ₂ (β n)) → φ₁ = φ₂ :=
    fun φ₁ φ₂ h => MulEquiv.ext fun w => by
      obtain ⟨n, rfl⟩ := hβs w
      exact h n
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · exact hext _ _ fun n => (hf 1 n).trans (congrArg β (Subtype.ext rfl))
  · intro y₁ y₂
    refine hext _ _ fun n => ?_
    rw [hf, MulAut.mul_apply, hf, hf]
    rfl

end Induced

theorem exists_omega627 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (∀ c : K, c ≠ 0 → c ^ 3 = 1) ∧
      ∀ c : K, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hcube : ∀ c : K, c ≠ 0 → c ^ 3 = 1 := fun c hc => by
    have := FiniteField.pow_card_sub_one_eq_one c hc
    rwa [hK'] at this
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun c _ => by
      by_cases h0 : c = 0
      · simp [h0]
      · simp [hcon c h0]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hK'] at h1
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  have hω3 := hcube ω hω0
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [hω3, sub_self] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  refine ⟨ω, hωq, hω3, hω1, hcube, fun c => ?_⟩
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  have h1 : (c - 1) * (c - ω) * (c - ω ^ 2) = c ^ 3 - 1 := by
    linear_combination (-c ^ 2 + c) * hωq + (c - 1) * hω3
  rw [hcube c hc0, sub_self] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

section SL34

variable {Q : Type} [CommGroup Q]

theorem exists_E9_sl34_627 {L : Subgroup (MulAut Q)}
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 2) {δ : MulAut Q}
    (hδL : δ ∈ Subgroup.normalizer (L : Set (MulAut Q))) (hδ3 : δ ^ 3 = 1) :
    ∃ t₁ ∈ L, ∃ t₂ ∈ L, ∃ ℓ ∈ L, orderOf t₁ = 3 ∧ orderOf t₂ = 3 ∧ Commute t₁ t₂ ∧
      Commute t₁ (δ * ℓ) ∧ Commute t₂ (δ * ℓ) ∧ (δ * ℓ) ^ 3 = 1 ∧
      ∀ a ∈ Subgroup.zpowers t₁, ∀ b ∈ Subgroup.zpowers t₂, a * b = 1 → a = 1 ∧ b = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hK4, π, hπ⟩ := hnat
  have hK4' : Nat.card K = 4 := by simpa using hK4
  obtain ⟨ω, hωq, hω3, hω1, hcube, hall⟩ := exists_omega627 hK4'
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  obtain ⟨-, hLN, β, hβs, hβk, hβe⟩ := natReal627 hπ
  set e : ↥(StatedSL 3 K) ≃* ↥L := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ with he
  set Λ : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥L :=
    (specialLinearGroupEquivStatedSL 3 K).trans e with hΛ
  have hΛβ : ∀ (A : Matrix.SpecialLinearGroup (Fin 3) K) (n : ↥(commV L)),
      Multiplicative.toAdd (β ⟨((Λ A : ↥L) : MulAut Q) n, hLN _ n n.2⟩) =
        (A : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (β n)) := fun A n =>
    hβe (specialLinearGroupEquivStatedSL 3 K A) n (hLN _ n n.2)
  set NL := Subgroup.normalizer (L : Set (MulAut Q)) with hNL
  have hNN : ∀ y ∈ NL, ∀ n ∈ commV L, y n ∈ commV L := by
    intro y hy n hn
    have hLy : L.map (MulAut.conj y).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
    have h1 := commV_conj627 L y
    rw [hLy] at h1
    rw [h1]
    exact ⟨n, hn, rfl⟩
  have hNZ : ∀ y ∈ NL, ∀ z ∈ fixV L ⊓ commV L, y z ∈ fixV L ⊓ commV L := by
    intro y hy z hz
    refine ⟨?_, hNN y hy z hz.2⟩
    have hLy : L.map (MulAut.conj y).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
    have h1 := fixV_conj627 L y
    rw [hLy] at h1
    rw [h1]
    exact ⟨z, hz.1, rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_indHom627 β hβs hβk hNN hNZ
  have hLNL : ∀ x ∈ L, x ∈ NL := fun x hx => Subgroup.le_normalizer hx
  have hψΛ : ∀ (A : Matrix.SpecialLinearGroup (Fin 3) K) (w : Multiplicative (Fin 3 → K)),
      Multiplicative.toAdd (ψ ⟨((Λ A : ↥L) : MulAut Q), hLNL _ (Λ A).2⟩ w) =
        (A : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd w) := by
    intro A w
    obtain ⟨n, rfl⟩ := hβs w
    rw [hψ]
    exact hΛβ A n
  have hfaith : ∀ (x : MulAut Q) (hx : x ∈ L), ψ ⟨x, hLNL x hx⟩ = 1 → x = 1 := by
    intro x hx h1
    set A := Λ.symm ⟨x, hx⟩ with hA
    have hxA : ((Λ A : ↥L) : MulAut Q) = x := by rw [hA, MulEquiv.apply_symm_apply]
    have hA1 : A = 1 := by
      by_contra hne
      have hne' : (A : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun h => hne (Subtype.ext h)
      obtain ⟨v, hv⟩ := exists_mulVec_ne627 hne'
      apply hv
      have h2 := hψΛ A (Multiplicative.ofAdd v)
      have h3 : (⟨((Λ A : ↥L) : MulAut Q), hLNL _ (Λ A).2⟩ : ↥NL) = ⟨x, hLNL x hx⟩ :=
        Subtype.ext hxA
      rw [h3, h1] at h2
      exact h2.symm
    rw [← hxA, hA1, map_one, Subgroup.coe_one]
  have hsdet : (Matrix.scalar (Fin 3) ω).det = 1 := by
    simp [hω3]
  set s : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Matrix.scalar (Fin 3) ω, hsdet⟩ with hs
  have hsc : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨ω, by simpa using hω3, rfl⟩
  set z : MulAut Q := ((Λ s : ↥L) : MulAut Q) with hz
  have hzL : z ∈ L := (Λ s).2
  have hzc : ∀ x ∈ L, z * x = x * z := by
    intro x hx
    have h1 := Subgroup.mem_center_iff.mp hsc (Λ.symm ⟨x, hx⟩)
    have h2 := congrArg (fun A => ((Λ A : ↥L) : MulAut Q)) h1
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h2
    exact h2.symm
  have hyL : δ * z * δ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hδL z).mp hzL
  have hyc : Λ.symm ⟨δ * z * δ⁻¹, hyL⟩ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply Λ.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    have hxL : ((Λ B : ↥L) : MulAut Q) ∈ L := (Λ B).2
    have hx' : δ⁻¹ * ((Λ B : ↥L) : MulAut Q) * δ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hδL) _).mp hxL
      simpa using this
    have h1 := hzc _ hx'
    calc ((Λ B : ↥L) : MulAut Q) * (δ * z * δ⁻¹)
        = δ * ((δ⁻¹ * ((Λ B : ↥L) : MulAut Q) * δ) * z) * δ⁻¹ := by group
      _ = δ * (z * (δ⁻¹ * ((Λ B : ↥L) : MulAut Q) * δ)) * δ⁻¹ := by rw [h1]
      _ = δ * z * δ⁻¹ * ((Λ B : ↥L) : MulAut Q) := by group
  obtain ⟨r, hr3, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hyc
  have hr3' : r ^ 3 = 1 := by simpa using hr3
  have hyeq : ∀ A : Matrix.SpecialLinearGroup (Fin 3) K,
      (A : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) r →
        δ * z * δ⁻¹ = ((Λ A : ↥L) : MulAut Q) := by
    intro A hA
    have : A = Λ.symm ⟨δ * z * δ⁻¹, hyL⟩ := Subtype.ext (hA.trans hrA)
    rw [this, MulEquiv.apply_symm_apply]
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 : Λ s = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    have h3 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K =>
      (A : Matrix (Fin 3) (Fin 3) K) 0 0) h2
    simp [hs] at h3
    exact hω1 h3
  have hz3 : z ^ 3 = 1 := by
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      show (Matrix.scalar (Fin 3) ω) ^ 3 = 1
      rw [← map_pow, hω3, map_one]
    rw [hz, ← Subgroup.coe_pow, ← map_pow, hs3, map_one, Subgroup.coe_one]
  have hδz : δ * z * δ⁻¹ = z := by
    rcases hall r with h0 | h1 | hω | hω2
    · rw [h0] at hr3'
      simp at hr3'
    · exfalso
      apply hz1
      have h2 := hyeq 1 (by rw [h1, map_one]; rfl)
      rw [map_one, Subgroup.coe_one] at h2
      have h3 : z = δ⁻¹ * (δ * z * δ⁻¹) * δ := by group
      rw [h3, h2]
      group
    · exact (hyeq s (by rw [hω])).trans rfl
    · exfalso
      apply hz1
      have h2 := hyeq (s * s) (by
        rw [Matrix.SpecialLinearGroup.coe_mul, hω2, hs, pow_two]
        exact (map_mul (Matrix.scalar (Fin 3)) ω ω).symm)
      rw [map_mul, Subgroup.coe_mul] at h2
      have hc1 : MulAut.conj δ z = z ^ 2 := by rw [MulAut.conj_apply, h2, pow_two]
      have hc : ∀ k : ℕ, MulAut.conj δ (z ^ k) = z ^ (2 * k) := by
        intro k
        rw [map_pow, hc1, ← pow_mul]
      have h3 : z ^ (2 * (2 * 2)) = z := by
        have e := congrArg (fun φ : MulAut (MulAut Q) => φ z)
          (show MulAut.conj δ ^ 3 = 1 by rw [← map_pow, hδ3, map_one])
        simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at e
        rw [hc1, hc, hc] at e
        exact e
      have h4 : z ^ (2 * (2 * 2)) = z ^ 2 := by
        rw [show 2 * (2 * 2) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hz3, one_pow, one_mul]
      rw [h4, pow_two] at h3
      exact mul_eq_left.mp h3
  have hδz' : δ * z = z * δ := by
    calc δ * z = δ * z * δ⁻¹ * δ := by group
      _ = z * δ := by rw [hδz]
  set φ := ψ ⟨δ, hδL⟩ with hφ
  have hψz : ∀ w, Multiplicative.toAdd (ψ ⟨z, hLNL z hzL⟩ w) =
      ω • Multiplicative.toAdd w := by
    intro w
    rw [hψΛ s w, hs]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hφz : φ * ψ ⟨z, hLNL z hzL⟩ = ψ ⟨z, hLNL z hzL⟩ * φ := by
    rw [hφ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hδz'
  have hφω : ∀ v, Multiplicative.toAdd (φ (Multiplicative.ofAdd (ω • v))) =
      ω • Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := by
    intro v
    have h1 : Multiplicative.ofAdd (ω • v) = ψ ⟨z, hLNL z hzL⟩ (Multiplicative.ofAdd v) := by
      apply Multiplicative.toAdd.injective
      rw [hψz]
      rfl
    rw [h1, ← MulAut.mul_apply, hφz, MulAut.mul_apply, hψz]
  have hφlin : ∀ (c : K) (v : Fin 3 → K), Multiplicative.toAdd (φ (Multiplicative.ofAdd (c • v))) =
      c • Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := by
    intro c v
    rcases hall c with rfl | rfl | rfl | rfl
    · rw [zero_smul, zero_smul, ofAdd_zero, map_one]
      rfl
    · rw [one_smul, one_smul]
    · exact hφω v
    · rw [pow_two, mul_smul, hφω, hφω, mul_smul]
  let fK : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
      map_add' := fun a b => by
        show Multiplicative.toAdd (φ (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) = _
        rw [map_mul, toAdd_mul]
      map_smul' := hφlin }
  set g := LinearMap.toMatrix' fK with hg
  have hgv : ∀ v, g.mulVec v = Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := fun v => by
    rw [hg, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hgw : ∀ w, Multiplicative.toAdd (φ w) = g.mulVec (Multiplicative.toAdd w) := fun w =>
    (hgv _).symm
  have hdet0 : g.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    apply hv0
    have h1 : φ (Multiplicative.ofAdd v) = φ 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      exact (hgv v).symm.trans hv
    exact Multiplicative.ofAdd.injective (φ.injective h1)
  set D₃ : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![g.det, 1, 1] with hD₃
  have hM₃ : (g⁻¹ * D₃).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hD₃, Matrix.det_diagonal,
      Fin.prod_univ_three]
    simp [hdet0]
  set A₃ : Matrix.SpecialLinearGroup (Fin 3) K := ⟨g⁻¹ * D₃, hM₃⟩ with hA₃
  set ℓ : MulAut Q := ((Λ A₃ : ↥L) : MulAut Q) with hℓ
  have hℓL : ℓ ∈ L := (Λ A₃).2
  have hgA₃ : g * (A₃ : Matrix (Fin 3) (Fin 3) K) = D₃ := by
    rw [hA₃]
    show g * (g⁻¹ * D₃) = D₃
    rw [← mul_assoc, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.mpr hdet0), one_mul]
  set P : ↥NL := ⟨δ * ℓ, NL.mul_mem hδL (hLNL ℓ hℓL)⟩ with hP
  have hψP : ∀ w, Multiplicative.toAdd (ψ P w) = D₃.mulVec (Multiplicative.toAdd w) := by
    intro w
    have e1 : P = ⟨δ, hδL⟩ * ⟨ℓ, hLNL ℓ hℓL⟩ := Subtype.ext rfl
    rw [e1, map_mul, MulAut.mul_apply, ← hφ, hgw, hψΛ A₃ w, Matrix.mulVec_mulVec, hgA₃]
  have hd₁ : (Matrix.diagonal ![ω, ω ^ 2, 1]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show ω * ω ^ 2 * 1 = 1
    linear_combination hω3
  have hd₂ : (Matrix.diagonal ![1, ω, ω ^ 2]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show 1 * ω * ω ^ 2 = 1
    linear_combination hω3
  set A₁ : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Matrix.diagonal ![ω, ω ^ 2, 1], hd₁⟩ with hA₁
  set A₂ : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Matrix.diagonal ![1, ω, ω ^ 2], hd₂⟩ with hA₂
  set t₁ : MulAut Q := ((Λ A₁ : ↥L) : MulAut Q) with ht₁
  set t₂ : MulAut Q := ((Λ A₂ : ↥L) : MulAut Q) with ht₂
  have ht₁L : t₁ ∈ L := (Λ A₁).2
  have ht₂L : t₂ ∈ L := (Λ A₂).2
  have hω6 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hA₁3 : A₁ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hA₁]
    show (Matrix.diagonal ![ω, ω ^ 2, 1]) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hω3, hω6]
  have hA₂3 : A₂ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hA₂]
    show (Matrix.diagonal ![1, ω, ω ^ 2]) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hω3, hω6]
  have ho₁ : orderOf t₁ = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [ht₁, ← Subgroup.coe_pow, ← map_pow, hA₁3, map_one, Subgroup.coe_one]
    · intro h1
      have h2 : Λ A₁ = 1 := Subtype.ext h1
      rw [MulEquiv.map_eq_one_iff] at h2
      have h3 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K =>
        (A : Matrix (Fin 3) (Fin 3) K) 0 0) h2
      simp [hA₁] at h3
      exact hω1 h3
  have ho₂ : orderOf t₂ = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [ht₂, ← Subgroup.coe_pow, ← map_pow, hA₂3, map_one, Subgroup.coe_one]
    · intro h1
      have h2 : Λ A₂ = 1 := Subtype.ext h1
      rw [MulEquiv.map_eq_one_iff] at h2
      have h3 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K =>
        (A : Matrix (Fin 3) (Fin 3) K) 1 1) h2
      simp [hA₂] at h3
      exact hω1 h3
  have hA₁₂ : A₁ * A₂ = A₂ * A₁ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hA₁, hA₂]
    show Matrix.diagonal ![ω, ω ^ 2, 1] * Matrix.diagonal ![1, ω, ω ^ 2] =
      Matrix.diagonal ![1, ω, ω ^ 2] * Matrix.diagonal ![ω, ω ^ 2, 1]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hc₁₂ : Commute t₁ t₂ := by
    show t₁ * t₂ = t₂ * t₁
    rw [ht₁, ht₂, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hA₁₂]
  set T₁ : ↥NL := ⟨t₁, hLNL t₁ ht₁L⟩ with hT₁
  set T₂ : ↥NL := ⟨t₂, hLNL t₂ ht₂L⟩ with hT₂
  have hψT₁ : ∀ w, Multiplicative.toAdd (ψ T₁ w) =
      (Matrix.diagonal ![ω, ω ^ 2, 1]).mulVec (Multiplicative.toAdd w) := fun w => hψΛ A₁ w
  have hψT₂ : ∀ w, Multiplicative.toAdd (ψ T₂ w) =
      (Matrix.diagonal ![1, ω, ω ^ 2]).mulVec (Multiplicative.toAdd w) := fun w => hψΛ A₂ w
  have hcomm : ∀ (d : Fin 3 → K) (T : ↥NL),
      (∀ w, Multiplicative.toAdd (ψ T w) = (Matrix.diagonal d).mulVec (Multiplicative.toAdd w)) →
        (T : MulAut Q) ∈ L → Commute (T : MulAut Q) (δ * ℓ) := by
    intro d T hT hTL
    have h1 : ψ T * ψ P = ψ P * ψ T := by
      refine MulEquiv.ext fun w => ?_
      apply Multiplicative.toAdd.injective
      rw [MulAut.mul_apply, MulAut.mul_apply, hT, hψP, hψP, hT, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hD₃, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 2
      funext i
      exact mul_comm _ _
    have hcL : ((T * P * T⁻¹ * P⁻¹ : ↥NL) : MulAut Q) ∈ L := by
      have hPt : (δ * ℓ) * (T : MulAut Q)⁻¹ * (δ * ℓ)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp P.2 _).mp (L.inv_mem hTL)
      have e : ((T * P * T⁻¹ * P⁻¹ : ↥NL) : MulAut Q) =
          (T : MulAut Q) * ((δ * ℓ) * (T : MulAut Q)⁻¹ * (δ * ℓ)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hP]
        group
      rw [e]
      exact L.mul_mem hTL hPt
    have h2 : ψ (T * P * T⁻¹ * P⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 := hfaith _ hcL h2
    have h4 : (T : MulAut Q) * (δ * ℓ) * (T : MulAut Q)⁻¹ * (δ * ℓ)⁻¹ = 1 := by
      rw [← h3]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hP]
    show (T : MulAut Q) * (δ * ℓ) = (δ * ℓ) * (T : MulAut Q)
    calc (T : MulAut Q) * (δ * ℓ)
        = (T : MulAut Q) * (δ * ℓ) * (T : MulAut Q)⁻¹ * (δ * ℓ)⁻¹ *
            ((δ * ℓ) * (T : MulAut Q)) := by group
      _ = (δ * ℓ) * (T : MulAut Q) := by rw [h4, one_mul]
  have hc₁ : Commute t₁ (δ * ℓ) := hcomm _ T₁ hψT₁ ht₁L
  have hc₂ : Commute t₂ (δ * ℓ) := hcomm _ T₂ hψT₂ ht₂L
  have hP3L : (δ * ℓ) ^ 3 ∈ L := by
    have e : (δ * ℓ) ^ 3 =
        (δ * ℓ * δ⁻¹) * ((δ * δ) * ℓ * (δ * δ)⁻¹) * ((δ * (δ * δ)) * ℓ) := by
      rw [pow_three]
      group
    rw [e, ← pow_three, hδ3, one_mul]
    refine L.mul_mem (L.mul_mem ?_ ?_) hℓL
    · exact (Subgroup.mem_normalizer_iff.mp hδL ℓ).mp hℓL
    · exact (Subgroup.mem_normalizer_iff.mp (NL.mul_mem hδL hδL) ℓ).mp hℓL
  have hD₃3 : D₃ * D₃ * D₃ = 1 := by
    rw [hD₃, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · show g.det * g.det * g.det = 1
      rw [← hcube _ hdet0]
      ring
    · show (1 : K) * 1 * 1 = 1
      ring
    · show (1 : K) * 1 * 1 = 1
      ring
  have hψP3 : ψ (P ^ 3) = 1 := by
    refine MulEquiv.ext fun w => ?_
    apply Multiplicative.toAdd.injective
    rw [map_pow, pow_three, MulAut.mul_apply, MulAut.mul_apply, hψP, hψP, hψP,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD₃3, Matrix.one_mulVec]
    rfl
  have hP3 : (δ * ℓ) ^ 3 = 1 := by
    have h1 := hfaith ((P ^ 3 : ↥NL) : MulAut Q) (by rw [Subgroup.coe_pow]; exact hP3L) hψP3
    rwa [Subgroup.coe_pow] at h1
  set w₁ : Multiplicative (Fin 3 → K) := Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : K))
    with hw₁
  set F₁ : Subgroup (MulAut Q) :=
    ((MulAction.stabilizer (MulAut (Multiplicative (Fin 3 → K))) w₁).comap ψ).map NL.subtype
    with hF₁
  have hmemF : ∀ T : ↥NL, ψ T w₁ = w₁ → (T : MulAut Q) ∈ F₁ := fun T hT =>
    ⟨T, MulAction.mem_stabilizer_iff.mpr hT, rfl⟩
  have hFmem : ∀ x ∈ F₁, ∃ T : ↥NL, (T : MulAut Q) = x ∧ ψ T w₁ = w₁ := by
    rintro _ ⟨T, hT, rfl⟩
    exact ⟨T, rfl, MulAction.mem_stabilizer_iff.mp hT⟩
  have ht₂F : t₂ ∈ F₁ := hmemF T₂ (by
    apply Multiplicative.toAdd.injective
    rw [hψT₂, hw₁, toAdd_ofAdd]
    funext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal])
  have ht₁F : t₁ ∉ F₁ := by
    intro h
    obtain ⟨T, hT, hTw⟩ := hFmem t₁ h
    have hTT : T = T₁ := Subtype.ext hT
    rw [hTT] at hTw
    have h1 := congrArg (fun w : Multiplicative (Fin 3 → K) => (Multiplicative.toAdd w) 0) hTw
    simp only [hψT₁, hw₁, toAdd_ofAdd] at h1
    simp [Matrix.mulVec_diagonal] at h1
    exact hω1 h1
  refine ⟨t₁, ht₁L, t₂, ht₂L, ℓ, hℓL, ho₁, ho₂, hc₁₂, hc₁, hc₂, hP3, fun a ha b hb hab => ?_⟩
  have hbF : b ∈ F₁ := (Subgroup.zpowers_le.mpr ht₂F) hb
  have haF : a ∈ F₁ := by
    rw [eq_inv_of_mul_eq_one_left hab]
    exact F₁.inv_mem hbF
  by_cases ha1 : a = 1
  · refine ⟨ha1, ?_⟩
    rw [ha1, one_mul] at hab
    exact hab
  · exact absurd ((Subgroup.zpowers_le.mpr haF) (mem_zpowers_of_ne_one624 ho₁ ha ha1)) ht₁F

end SL34

theorem false_of_E27_627 {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (hrank : ∀ E : Subgroup G, E ≤ Y → CFSG.Open.IsElemAbelian 3 E → ∀ r, Nat.card E = 3 ^ r →
      r ≤ 2)
    {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (θ : ↥Y →* Γ₁) (σ : ↥Y →* Γ₂)
    (hker : ∀ y : ↥Y, θ y = 1 → σ y = 1 → ∃ i : ℕ, y ^ 2 ^ i = 1)
    {e₁ e₂ x : ↥Y} (he₁ : σ e₁ = 1) (he₂ : σ e₂ = 1) (hσx : orderOf (σ x) = 3)
    (ho₁ : orderOf (θ e₁) = 3) (ho₂ : orderOf (θ e₂) = 3) (hc₁₂ : Commute (θ e₁) (θ e₂))
    (hc₁ : Commute (θ e₁) (θ x)) (hc₂ : Commute (θ e₂) (θ x)) (hx3 : θ x ^ 3 = 1)
    (hind : ∀ a ∈ Subgroup.zpowers (θ e₁), ∀ b ∈ Subgroup.zpowers (θ e₂), a * b = 1 →
      a = 1 ∧ b = 1) : False := by
  classical
  set φ : ↥Y →* Γ₁ × Γ₂ := θ.prod σ with hφ
  set f := φ.rangeRestrict with hf
  have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective φ
  have : Finite ↥φ.range := Finite.of_surjective f hfs
  have hfv : ∀ y : ↥Y, ((f y : ↥φ.range) : Γ₁ × Γ₂) = (θ y, σ y) := fun y => rfl
  have hfk : ∀ y : ↥Y, f y = 1 → ∃ i : ℕ, y ^ 2 ^ i = 1 := by
    intro y hy
    have h1 : ((f y : ↥φ.range) : Γ₁ × Γ₂) = 1 := by rw [hy]; rfl
    rw [hfv] at h1
    exact hker y (congrArg Prod.fst h1) (congrArg Prod.snd h1)
  have hord : ∀ y : ↥Y, orderOf (f y) = (orderOf (θ y)).lcm (orderOf (σ y)) := fun y => by
    rw [← Subgroup.orderOf_coe, hfv, Prod.orderOf_mk]
  have hcomm : ∀ a b : ↥Y, Commute (θ a) (θ b) → Commute (σ a) (σ b) → Commute (f a) (f b) :=
    fun a b h1 h2 => Subtype.ext (Prod.ext h1.eq h2.eq)
  have ho₁' : orderOf (f e₁) = 3 := by rw [hord, he₁, orderOf_one, ho₁, Nat.lcm_one_right]
  have ho₂' : orderOf (f e₂) = 3 := by rw [hord, he₂, orderOf_one, ho₂, Nat.lcm_one_right]
  have hox' : orderOf (f x) = 3 := by
    rw [hord, hσx]
    exact Nat.lcm_eq_right_iff_dvd.mpr (hσx ▸ orderOf_dvd_of_pow_eq_one hx3 |>.trans
      (by rw [hσx]))
  have hind' : ∀ a ∈ Subgroup.zpowers (f e₁), ∀ b ∈ Subgroup.zpowers (f e₂),
      ∀ c ∈ Subgroup.zpowers (f x), a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by
    intro a ha b hb c hc habc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h1 := congrArg (fun q : ↥φ.range => (q : Γ₁ × Γ₂)) habc
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one, hfv] at h1
    have h1₁ := congrArg Prod.fst h1
    have h1₂ := congrArg Prod.snd h1
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_one,
      Prod.snd_one, he₁, he₂, one_zpow, one_mul] at h1₁ h1₂
    have hk : ((orderOf (σ x) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr h1₂
    rw [hσx] at hk
    have hθk : θ x ^ k = 1 := by
      obtain ⟨m, rfl⟩ := hk
      rw [zpow_mul, show θ x ^ ((3 : ℕ) : ℤ) = 1 by rw [zpow_natCast]; exact hx3, one_zpow]
    have hc1 : f x ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, hfv, Subgroup.coe_one]
      exact Prod.ext (by simpa using hθk) (by simpa using h1₂)
    rw [hθk, mul_one] at h1₁
    obtain ⟨ha1, hb1⟩ := hind _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h1₁
    refine ⟨?_, ?_, hc1⟩
    · apply Subtype.ext
      rw [Subgroup.coe_zpow, hfv, Subgroup.coe_one]
      exact Prod.ext (by simpa using ha1) (by simp [he₁])
    · apply Subtype.ext
      rw [Subgroup.coe_zpow, hfv, Subgroup.coe_one]
      exact Prod.ext (by simpa using hb1) (by simp [he₂])
  obtain ⟨E, hE, hE27⟩ := exists_elemAbelian27_of_elements624 ho₁' ho₂' hox'
    (hcomm _ _ hc₁₂ (by rw [he₁]; exact Commute.one_left _))
    (hcomm _ _ hc₁ (by rw [he₁]; exact Commute.one_left _))
    (hcomm _ _ hc₂ (by rw [he₂]; exact Commute.one_left _)) hind'
  have := U3.le_two_of_elemAbelian_of_surjective f hfs hfk Nat.prime_three (by norm_num) hrank hE
    hE27
  omega

end CFSG.Quasithin.H13
