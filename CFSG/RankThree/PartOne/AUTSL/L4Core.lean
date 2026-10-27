module

public import CFSG.RankThree.PartOne.AUTSL.DiagCore
public import CFSG.RankThree.PartOne.AUTSL.SemilinearRel
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne.AUTSL

section Characters

open Matrix

variable {K' : Type*} [Field K'] [Finite K']

theorem exists_characters {n : ℕ} {ζ : K'} (hζ : IsPrimitiveRoot ζ 5) {G : Type*} [CommGroup G]
    (hG5 : ∀ x : G, x ^ 5 = 1) (ρ : G →* SpecialLinearGroup (Fin n) K') :
    ∃ (P : GL (Fin n) K') (f : Fin n → (G →* K'ˣ)), ∀ g : G,
      (P : Matrix (Fin n) (Fin n) K') * (ρ g : Matrix (Fin n) (Fin n) K') *
        ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') =
        Matrix.diagonal fun i => ((f i g : K'ˣ) : K') := by
  classical
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_commuting_pow_eq_one hζ ρ.range
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; rw [← map_mul, ← map_mul, mul_comm])
    (by rintro _ ⟨a, rfl⟩; rw [← map_pow, hG5, map_one])
  set Dm : G → Matrix (Fin n) (Fin n) K' := fun g =>
    (P : Matrix (Fin n) (Fin n) K') * (ρ g : Matrix (Fin n) (Fin n) K') *
      ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') with hDm
  have hdiag : ∀ g, (Dm g).IsDiag := fun g i j hij => hP (ρ g) ⟨g, rfl⟩ i j hij
  have hmul : ∀ g h, Dm (g * h) = Dm g * Dm h := fun g h => by
    simp only [hDm, map_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc (P : Matrix (Fin n) (Fin n) K') * ((ρ g : Matrix (Fin n) (Fin n) K') *
          (ρ h : Matrix (Fin n) (Fin n) K')) * ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K')
        = (P : Matrix (Fin n) (Fin n) K') * (ρ g : Matrix (Fin n) (Fin n) K') *
          (((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') *
            (P : Matrix (Fin n) (Fin n) K')) * (ρ h : Matrix (Fin n) (Fin n) K') *
            ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') := by
          rw [Units.inv_mul, mul_one]; noncomm_ring
      _ = _ := by noncomm_ring
  have hone : Dm 1 = 1 := by
    simp only [hDm, map_one, Matrix.SpecialLinearGroup.coe_one, mul_one]
    exact Units.mul_inv P
  let fm : Fin n → (G →* K') := fun i =>
    { toFun := fun g => Dm g i i
      map_one' := by rw [hone, Matrix.one_apply_eq]
      map_mul' := fun g h => by
        rw [hmul, Matrix.mul_apply, Finset.sum_eq_single i]
        · intro k _ hki
          rw [hdiag g (Ne.symm hki), zero_mul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi }
  refine ⟨P, fun i => (fm i).toHomUnits, fun g => ?_⟩
  have h1 : (Dm g) = Matrix.diagonal fun i => Dm g i i := ((hdiag g).diagonal_diag).symm
  show Dm g = Matrix.diagonal fun i => (((fm i).toHomUnits g : K'ˣ) : K')
  rw [h1]
  congr 1

end Characters

section Relation

open Matrix

variable {K K' : Type*} [Field K] [Finite K] [CharP K 2] [Field K'] [Finite K'] [CharP K' 2]
  [Algebra K K']

omit [Finite K'] in
theorem exists_E_relation {n : ℕ} (hn : 3 ≤ n) {E : Type*} [CommGroup E]
    (hE5 : ∀ x : E, x ^ 5 = 1) (ρ : E →* SpecialLinearGroup (Fin n) K) (P : GL (Fin n) K')
    (f : Fin n → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix (Fin n) (Fin n) K') *
        (ρ g : Matrix (Fin n) (Fin n) K).map (algebraMap K K') *
        ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') =
        Matrix.diagonal fun i => ((f i g : K'ˣ) : K'))
    (β : MulAut (SpecialLinearGroup (Fin n) K)) :
    ∃ (j e : ℕ) (A₃ : Matrix (Fin n) (Fin n) K'), IsUnit A₃ ∧ (e = 1 ∨ e = 4) ∧
      ∀ g : E, (P : Matrix (Fin n) (Fin n) K') *
        (β (ρ g) : Matrix (Fin n) (Fin n) K).map (algebraMap K K') *
        ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') * A₃ =
        A₃ * Matrix.diagonal (fun i => (((f i g : K'ˣ) : K') ^ e) ^ 2 ^ j) := by
  obtain ⟨j, A₃, hA₃, h | h⟩ := exists_semilinear_relation hn β P
  · refine ⟨j, 1, A₃, hA₃, Or.inl rfl, fun g => ?_⟩
    have := h (ρ g) (fun i => ((f i g : K'ˣ) : K')) (hD g)
    simpa only [pow_one] using this
  · refine ⟨j, 4, A₃, hA₃, Or.inr rfl, fun g => ?_⟩
    have := h (ρ g) (fun i => ((f i g : K'ˣ) : K')) (hD g)
    rw [this]
    have hinv : ∀ i, (((f i g : K'ˣ) : K'))⁻¹ = ((f i g : K'ˣ) : K') ^ 4 := fun i => by
      have h5 : ((f i g : K'ˣ) : K') ^ 5 = 1 := by
        have := congrArg (fun y : K'ˣ => (y : K'))
          (show (f i g) ^ 5 = 1 by rw [← map_pow, hE5 g, map_one])
        simpa using this
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h5)
    simp only [hinv]

end Relation

section Main

open Matrix

theorem l4_core {K : Type} [Field K] [Finite K] [CharP K 2]
    {S : Subgroup (SpecialLinearGroup (Fin 4) K)} (hS : IsPGroup 2 S)
    (𝒲 : Set (Submodule K (Fin 4 → K)))
    (hJ : ∀ y : SpecialLinearGroup (Fin 4) K,
      y ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)) ↔
        ∀ W ∈ 𝒲, ∀ w ∈ W, (y : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W)
    {E B : Subgroup (SpecialLinearGroup (Fin 4) K)} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hBE : B ≤ E)
    (hBJ : B ≤ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)))
    (hB : Nat.card B = 25) (α : MulAut (SpecialLinearGroup (Fin 4) K))
    (hαB : B.map α.toMonoidHom = B) (hα3 : ∀ b ∈ B, (α ^ 3) b = b) (hα1 : ∃ b ∈ B, α b ≠ b)
    (x : MulAut (SpecialLinearGroup (Fin 4) K)) (hxB : ∀ b ∈ B, b⁻¹ * x b ∈ S) :
    E ≤ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)) ∧ ∀ e ∈ E, e⁻¹ * x e ∈ S := by
  classical
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  let _ : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b => Subtype.ext (hEc a (hBE a.2) b (hBE b.2)) }
  have hE5' : ∀ e : E, e ^ 5 = 1 := fun e => Subtype.ext (by simpa using hE5 e e.2)
  have hB5' : ∀ b : B, b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hE5 b (hBE b.2))
  obtain ⟨K', hF', hAlg, hFin, hChar, ζ, hζ⟩ := exists_finite_extension_five K
  let ρ : E →* SpecialLinearGroup (Fin 4) K := E.subtype
  let ρ' : E →* SpecialLinearGroup (Fin 4) K' := (SpecialLinearGroup.map (algebraMap K K')).comp ρ
  obtain ⟨P, f, hD'⟩ := exists_characters hζ hE5' ρ'
  have hD : ∀ g : E, (P : Matrix (Fin 4) (Fin 4) K') *
      ((ρ g : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') *
      ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') =
      Matrix.diagonal fun i => ((f i g : K'ˣ) : K') := fun g => by
    have := hD' g
    simpa [ρ'] using this
  have hPPi : (P : Matrix (Fin 4) (Fin 4) K') *
      ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') = 1 := Units.mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
      (P : Matrix (Fin 4) (Fin 4) K') = 1 := Units.inv_mul P
  have hconjinj : ∀ X Y : Matrix (Fin 4) (Fin 4) K',
      (P : Matrix (Fin 4) (Fin 4) K') * X * ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') =
      (P : Matrix (Fin 4) (Fin 4) K') * Y *
        ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') → X = Y := fun X Y h => by
    calc X = (((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
          (P : Matrix (Fin 4) (Fin 4) K')) * X *
          (((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
            (P : Matrix (Fin 4) (Fin 4) K')) := by rw [hPiP, one_mul, mul_one]
      _ = ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') * ((P : Matrix (Fin 4) (Fin 4) K') *
          X * ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K')) *
          (P : Matrix (Fin 4) (Fin 4) K') := by noncomm_ring
      _ = ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') * ((P : Matrix (Fin 4) (Fin 4) K') *
          Y * ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K')) *
          (P : Matrix (Fin 4) (Fin 4) K') := by rw [h]
      _ = Y := by
        calc _ = (((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
              (P : Matrix (Fin 4) (Fin 4) K')) * Y *
              (((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
                (P : Matrix (Fin 4) (Fin 4) K')) := by noncomm_ring
          _ = Y := by rw [hPiP, one_mul, mul_one]
  have hfaithE : ∀ g : E, (∀ i, f i g = 1) → g = 1 := fun g hg => by
    have h1 := hD g
    have h2 : (Matrix.diagonal fun i => ((f i g : K'ˣ) : K')) = 1 := by
      have : (fun i => ((f i g : K'ˣ) : K')) = fun _ => 1 := funext fun i => by rw [hg i]; rfl
      rw [this]
      exact Matrix.diagonal_one
    rw [h2] at h1
    have h3 := hconjinj _ 1 (by rw [h1, mul_one, hPPi])
    have h5 : (ρ g : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') =
        (1 : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') := by
      rw [h3, Matrix.map_one _ (map_zero _) (map_one _)]
    have h4 : (ρ g : Matrix (Fin 4) (Fin 4) K) = 1 :=
      Matrix.map_injective (algebraMap K K').injective h5
    exact Subtype.ext (Subtype.ext h4)
  let ιB : B →* E := Subgroup.inclusion hBE
  have hfaithB : ∀ b : B, (∀ i, f i (ιB b) = 1) → b = 1 := fun b hb =>
    Subgroup.inclusion_injective hBE (by rw [hfaithE (ιB b) hb, map_one])
  have hαB' : ∀ b : B, α b ∈ B := fun b => by
    have : α b ∈ B.map α.toMonoidHom := ⟨b, b.2, rfl⟩
    rwa [hαB] at this
  have hαBinv : ∀ b : B, α⁻¹ b ∈ B := fun b => by
    have hb : (b : SpecialLinearGroup (Fin 4) K) ∈ B.map α.toMonoidHom := by
      rw [hαB]
      exact b.2
    obtain ⟨c, hc, hcb⟩ := hb
    have : α⁻¹ b = c := by
      rw [← hcb]
      simp
    rw [this]
    exact hc
  let θ : MulAut B :=
    { toFun := fun b => ⟨α b, hαB' b⟩
      invFun := fun b => ⟨α⁻¹ b, hαBinv b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hθval : ∀ b : B, ((θ b : B) : SpecialLinearGroup (Fin 4) K) = α b := fun b => rfl
  have hθ3 : θ ^ 3 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have h1 := hα3 b b.2
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1 ⊢
    simpa [hθval] using h1
  have hθ1 : θ ≠ 1 := by
    intro h
    obtain ⟨b, hb, hne⟩ := hα1
    apply hne
    have := congrArg (fun φ : MulAut B => ((φ ⟨b, hb⟩ : B) : SpecialLinearGroup (Fin 4) K)) h
    simpa [hθval] using this
  have hnorm : ∀ b, b * θ b * θ (θ b) = 1 := norm_eq_one_of_order_three hB θ hθ3 hθ1
  obtain ⟨j₀, e₀, A₀, hA₀, he₀, hrel₀⟩ := exists_E_relation (by norm_num : 3 ≤ 4) hE5' ρ P f hD α
  have hrelB : ∀ b : B, A₀ * Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K') ^ e₀) ^ 2 ^ j₀) =
      diagOf f (ιB (θ b)) * A₀ := fun b => by
    have h1 := hrel₀ (ιB b)
    have h2 : α (ρ (ιB b)) = ρ (ιB (θ b)) := rfl
    rw [h2, hD (ιB (θ b))] at h1
    exact h1.symm
  obtain ⟨hm₀, hinj, χ₀, hχ₀, h0, h1, h2⟩ := weights_of_relation f ιB hB hB5' hfaithB θ hθ3 hθ1
    j₀ e₀ he₀ A₀ hA₀ hrelB
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBp : IsPGroup 5 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  obtain ⟨s, hsS, hs⟩ := exists_conj_eq_of_sylow_trick (p := 5) (q := 2) Nat.prime_two
    (by norm_num) hS hBp hBJ x hxB
  let x' : MulAut (SpecialLinearGroup (Fin 4) K) := MulAut.conj s⁻¹ * x
  have hx'B : ∀ b ∈ B, x' b = b := fun b hb => by
    simp only [x', MulAut.mul_apply, MulAut.conj_apply, hs b hb]
    group
  obtain ⟨l, e', A₁, hA₁, he', hrel₁⟩ := exists_E_relation (by norm_num : 3 ≤ 4) hE5' ρ P f hD x'
  have hrelB' : ∀ b : B, A₁ * Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K') ^ e') ^ 2 ^ l) =
      diagOf f (ιB b) * A₁ := fun b => by
    have h1 := hrel₁ (ιB b)
    have h2 : x' (ρ (ιB b)) = ρ (ιB b) := hx'B _ b.2
    rw [h2, hD (ιB b)] at h1
    exact h1.symm
  have hm : ¬ 5 ∣ e₀ * 2 ^ j₀ := not_dvd_five_mul j₀ e₀ he₀
  have hall := fun e₁ : E => fixes_of_relation f ιB hB5' hE5' θ hnorm (e₀ * 2 ^ j₀) hm hinj hχ₀ h0
    h1 h2 l e' he' A₁ hA₁ hrelB' e₁
  have hmapinj : ∀ X Y : SpecialLinearGroup (Fin 4) K,
      (X : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') =
        (Y : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') → X = Y := fun X Y h =>
    Subtype.ext (Matrix.map_injective (algebraMap K K').injective h)
  have hfix : ∀ g : E, x' (g : SpecialLinearGroup (Fin 4) K) = g := fun g => by
    have h3 : (P : Matrix (Fin 4) (Fin 4) K') *
        (x' (ρ g) : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') *
        ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') * A₁ =
        ((P : Matrix (Fin 4) (Fin 4) K') * (ρ g : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') *
          ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K')) * A₁ := by
      rw [hrel₁ g, hall g, hD g]
      rfl
    exact hmapinj _ _ (hconjinj _ _ ((hA₁.mul_left_inj).1 h3))
  have hEJ : ∀ g : E, (g : SpecialLinearGroup (Fin 4) K) ∈
      Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K)) := fun g => by
    rw [hJ]
    intro W hW
    have hspan := diag_mem_span f ιB hinj g
    let Cj : Matrix (Fin 4) (Fin 4) K' →ₗ[K'] Matrix (Fin 4) (Fin 4) K' :=
      (LinearMap.mulLeft K' ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K')).comp
        (LinearMap.mulRight K' (P : Matrix (Fin 4) (Fin 4) K'))
    have hCj : ∀ z : E, Cj (diagOf f z) =
        (ρ z : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') := fun z => by
      have hz : diagOf f z = (P : Matrix (Fin 4) (Fin 4) K') *
          (ρ z : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') *
          ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') := (hD z).symm
      show ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') * (diagOf f z *
        (P : Matrix (Fin 4) (Fin 4) K')) = _
      rw [hz]
      calc ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') * ((P : Matrix (Fin 4) (Fin 4) K') *
            (ρ z : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') *
            ((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
              (P : Matrix (Fin 4) (Fin 4) K'))
          = (((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
              (P : Matrix (Fin 4) (Fin 4) K')) *
            (ρ z : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') *
            (((P⁻¹ : GL (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') *
              (P : Matrix (Fin 4) (Fin 4) K')) := by noncomm_ring
        _ = _ := by rw [hPiP, one_mul, mul_one]
    have hmem := Submodule.mem_map_of_mem (f := Cj) hspan
    rw [Submodule.map_span, ← Set.range_comp] at hmem
    have hmem2 : (g : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') ∈ Submodule.span K'
        ((fun a : Matrix (Fin 4) (Fin 4) K => a.map (algebraMap K K')) ''
          Set.range fun b : B =>
            ((b : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
      rw [← Set.range_comp]
      have hrange : (Cj ∘ fun b : B => diagOf f (ιB b)) =
          ((fun a : Matrix (Fin 4) (Fin 4) K => a.map (algebraMap K K')) ∘
            fun b : B => ((b : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
        funext b
        exact hCj (ιB b)
      rw [← hrange]
      have h4 : (g : Matrix (Fin 4) (Fin 4) K).map (algebraMap K K') =
          Cj (diagOf f g) := (hCj g).symm
      rw [h4]
      exact hmem
    have hdesc := mem_span_of_map_mem_span (K := K) (K' := K')
      (Set.range fun b : B => ((b : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      (g : Matrix (Fin 4) (Fin 4) K) hmem2
    let St : Submodule K (Matrix (Fin 4) (Fin 4) K) :=
      { carrier := {M | ∀ w ∈ W, M *ᵥ w ∈ W}
        add_mem' := fun {M N} hM hN w hw => by
          rw [Matrix.add_mulVec]
          exact W.add_mem (hM w hw) (hN w hw)
        zero_mem' := fun w hw => by simp
        smul_mem' := fun c M hM w hw => by
          rw [Matrix.smul_mulVec]
          exact W.smul_mem c (hM w hw) }
    have hle : Submodule.span K (Set.range fun b : B =>
        ((b : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ≤ St := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact (hJ _).1 (hBJ b.2) W hW
    exact hle hdesc
  refine ⟨fun g hg => hEJ ⟨g, hg⟩, fun e he => ?_⟩
  have hx'e : x' e = e := hfix ⟨e, he⟩
  have hxe : x e = s * e * s⁻¹ := by
    simp only [x', MulAut.mul_apply, MulAut.conj_apply] at hx'e
    calc x e = s * (s⁻¹ * x e * s⁻¹⁻¹) * s⁻¹ := by group
      _ = s * e * s⁻¹ := by rw [hx'e]
  rw [hxe]
  have hsconj : e⁻¹ * s * e ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 4) K))).inv_mem
        (hEJ ⟨e, he⟩)) s).1 hsS
    simpa using this
  have hrw : e⁻¹ * (s * e * s⁻¹) = (e⁻¹ * s * e) * s⁻¹ := by group
  rw [hrw]
  exact S.mul_mem hsconj (S.inv_mem hsS)

end Main

end CFSG.RankThree.PartOne.AUTSL
