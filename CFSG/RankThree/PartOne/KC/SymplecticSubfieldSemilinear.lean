module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
import CFSG.RankThree.PartOne.KC.SymplecticTorusWitness

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

variable {r : ℕ} {K : Type} [Field K]

theorem eq_of_spEnd_eq {g h : StatedSp r K} (hgh : ∀ y, spEnd g y = spEnd h y) : g = h :=
  spLin_injective (Units.ext (LinearMap.ext hgh))

theorem spEnd_fieldSp (τ : K ≃+* K) (g : StatedSp r K) (z : Fin r ⊕ Fin r → K) :
    spEnd (fieldSp r K τ g) (τ ∘ z) = τ ∘ spEnd g z := by
  rw [spEnd_apply, spEnd_apply, coe_fieldSp]
  ext i
  exact (RingHom.map_mulVec (τ : K →+* K) _ z i).symm

theorem fieldSp_spTransvection (τ : K ≃+* K) {u : Fin r ⊕ Fin r → K} (hu : ∀ i, τ (u i) = u i)
    (t : K) : fieldSp r K τ (spTransvection u t) = spTransvection u (τ t) := by
  refine eq_of_spEnd_eq fun y => ?_
  have hτu : τ ∘ u = u := funext hu
  obtain ⟨z, rfl⟩ : ∃ z, τ ∘ z = y := ⟨fun i => τ.symm (y i), by ext i; simp⟩
  rw [spEnd_fieldSp, spEnd_spTransvection, spEnd_spTransvection]
  have h1 := spForm_comp_ringEquiv (r := r) τ z u
  rw [hτu] at h1
  ext i
  simp only [Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, h1]
  rw [hu i]

theorem spEnd_conjSp_mulVec (A : gsp r K) (g : StatedSp r K) (w : Fin r ⊕ Fin r → K) :
    spEnd (conjSp r K A g) (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      *ᵥ w) = ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        spEnd g w := by
  rw [spEnd_apply, spEnd_apply, coe_conjSp, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]


theorem exists_smul_spEnd_of_proj_eq_one {g : StatedSp r K} (hg : proj r K g = 1) :
    ∃ c : K, ∀ v, spEnd g v = c • v :=
  CFSG.RankThree.PartOne.KCSymplectic.exists_smul_of_proj_eq_one hg

theorem exists_smul_spEnd_of_proj_eq {x y : StatedSp r K} (h : proj r K x = proj r K y) :
    ∃ c : K, ∀ v, spEnd x v = c • spEnd y v := by
  have h1 : proj r K (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := exists_smul_spEnd_of_proj_eq_one h1
  refine ⟨c, fun v => ?_⟩
  have h2 : x = y * (y⁻¹ * x) := by rw [mul_inv_cancel_left]
  rw [h2, spEnd_mul, Module.End.mul_apply, hc, map_smul]

theorem exists_spForm_eq_one {u : Fin r ⊕ Fin r → K} (hu : u ≠ 0) :
    ∃ v, spForm r K v u = 1 := by
  obtain ⟨y₁, hy₁⟩ : ∃ y, spForm r K y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (spForm_nondegenerate.2 u hcon)
  exact ⟨(spForm r K y₁ u)⁻¹ • y₁, by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy₁]⟩

theorem eq_of_proj_spTransvection_eq {u : Fin r ⊕ Fin r → K} (hu : u ≠ 0) {s t : K}
    (h : proj r K (spTransvection u s) = proj r K (spTransvection u t)) : s = t := by
  obtain ⟨z, hz⟩ := exists_smul_spEnd_of_proj_eq h
  have hBuu : spForm r K u u = 0 := spForm_isAlt.self_eq_zero u
  have hz1 : z = 1 := by
    have e := hz u
    rw [spEnd_spTransvection, spEnd_spTransvection, hBuu] at e
    simp only [mul_zero, zero_smul, add_zero] at e
    have e' : (1 - z) • u = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp e').resolve_right hu)).symm
  obtain ⟨v₀, hv₀⟩ := exists_spForm_eq_one hu
  have e := hz v₀
  rw [hz1, one_smul, spEnd_spTransvection, spEnd_spTransvection, hv₀, mul_one, mul_one] at e
  have e' : (s - t) • u = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel e)
  exact sub_eq_zero.mp ((smul_eq_zero.mp e').resolve_right hu)

theorem spForm_map {k : Type} [Field k] (f : k →+* K) (x w : Fin r ⊕ Fin r → k) :
    spForm r K (f ∘ x) (f ∘ w) = f (spForm r k x w) := by
  have hJ : (gram k r).map f = gram K r := UnitaryHigher.formJ_map_ringHom f
  have hv : ∀ i, f ((gram k r *ᵥ w) i) = (gram K r *ᵥ (f ∘ w)) i := by
    intro i
    have := RingHom.map_mulVec f (gram k r) w i
    rw [hJ] at this
    exact this
  rw [spForm_apply, spForm_apply, dotProduct, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hv i]
  rfl

theorem coe_matrix_apply {F : Type} [Field F] (g : StatedSp r F) (a b : Fin r ⊕ Fin r) :
    ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) a b =
      spEnd g (Pi.single b 1) a := by
  rw [spEnd_apply, Matrix.mulVec_single_one]
  rfl

theorem coe_single_one (k : Subfield K) (b : Fin r ⊕ Fin r) :
    (fun a => ((Pi.single b 1 : Fin r ⊕ Fin r → k) a : K)) = Pi.single b 1 := by
  ext a
  by_cases h : a = b <;> simp [h]

theorem subfieldSpHom_spTransvection (k : Subfield K) (u₀ : Fin r ⊕ Fin r → k) (t₀ : k) :
    subfieldSpHom r k (spTransvection u₀ t₀) =
      spTransvection (fun a => (u₀ a : K)) (t₀ : K) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  have hL : ((subfieldSpHom r k (spTransvection u₀ t₀) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a b =
        (((spTransvection u₀ t₀ : GL (Fin r ⊕ Fin r) k) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b : K) := rfl
  rw [hL, coe_matrix_apply, coe_matrix_apply, spEnd_spTransvection, spEnd_spTransvection]
  have hf : spForm r K (fun a => (Pi.single b 1 : Fin r ⊕ Fin r → k) a |> fun x => (x : K))
      (fun a => (u₀ a : K)) = ((spForm r k (Pi.single b 1) u₀ : k) : K) :=
    spForm_map (k.subtype : k →+* K) (Pi.single b 1) u₀
  simp only [coe_single_one] at hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf]
  push_cast
  have h1 : (((Pi.single b 1 : Fin r ⊕ Fin r → k) a : k) : K) =
      (Pi.single b 1 : Fin r ⊕ Fin r → K) a := congrFun (coe_single_one k b) a
  rw [h1]


theorem exists_smul_of_fixes_transvection (A : gsp r K) (τ : K ≃+* K) {u : Fin r ⊕ Fin r → K}
    (hu0 : u ≠ 0) (hu : ∀ i, τ (u i) = u i)
    (h : proj r K (semiConj A τ (spTransvection u 1)) = proj r K (spTransvection u 1)) :
    ∃ c : K, ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u =
      c • u := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = M := ⟨_, rfl⟩
  rw [hM]
  set g : StatedSp r K := spTransvection u (1 : K) with hg
  have hfg : fieldSp r K τ g = g := by rw [hg, fieldSp_spTransvection τ hu, map_one]
  have hsc : semiConj A τ g = conjSp r K A g := by rw [semiConj_apply, hfg]
  rw [hsc] at h
  obtain ⟨c, hc⟩ := exists_smul_spEnd_of_proj_eq h
  have hBuu : spForm r K u u = 0 := spForm_isAlt.self_eq_zero u
  have hgv : ∀ v, spEnd g v = v + spForm r K v u • u := fun v => by
    rw [hg, spEnd_spTransvection, one_mul]
  have key : ∀ w, M *ᵥ spEnd g w = c • spEnd g (M *ᵥ w) := fun w => by
    have := hc (M *ᵥ w)
    rw [← hM, spEnd_conjSp_mulVec] at this
    rwa [hM] at this
  have hinv : (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M = 1 := by
    rw [← hM]
    exact Units.inv_mul _
  have hMinj : ∀ w, M *ᵥ w = 0 → w = 0 := fun w hw => by
    calc w = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w := (Matrix.one_mulVec w).symm
      _ = ((((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M) *ᵥ w := by rw [hinv]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  by_cases hc1 : c = 1
  · subst hc1
    obtain ⟨v₀, hv₀⟩ := exists_spForm_eq_one hu0
    have h1 := key v₀
    rw [hgv v₀, hgv (M *ᵥ v₀), one_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hv₀,
      one_smul] at h1
    exact ⟨spForm r K (M *ᵥ v₀) u, add_left_cancel h1⟩
  · exfalso
    have h1 := key u
    rw [hgv u, hBuu, zero_smul, add_zero, hgv (M *ᵥ u)] at h1
    have hm0 : M *ᵥ u ≠ 0 := fun h0 => hu0 (hMinj u h0)
    generalize M *ᵥ u = m at h1 hm0
    obtain ⟨b, hb⟩ : ∃ b, b = spForm r K m u := ⟨_, rfl⟩
    rw [← hb] at h1
    have hc' : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
    have h2 : m = c • m + (c * b) • u := by
      conv_lhs => rw [h1]
      rw [smul_add, smul_smul]
    have h3 : (1 - c) • m = (c * b) • u := by
      rw [sub_smul, one_smul]
      exact sub_eq_of_eq_add' h2
    have hm : m = ((1 - c)⁻¹ * (c * b)) • u := by
      rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hc', one_smul]
    have hb0 : b = 0 := by
      rw [hb, hm, map_smul, LinearMap.smul_apply, smul_eq_mul, hBuu, mul_zero]
    rw [hb0, mul_zero, zero_smul] at h3
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact hc' h4
    · exact hm0 h4

theorem exists_scalar_of_lines {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι K) (h1 : ∀ i, ∃ c : K, M *ᵥ Pi.single i 1 = c • Pi.single i 1)
    (h2 : ∀ i j, i ≠ j → ∃ c : K,
      M *ᵥ (Pi.single i 1 + Pi.single j 1) = c • (Pi.single i 1 + Pi.single j 1)) :
    ∃ d : K, M = d • (1 : Matrix ι ι K) := by
  choose d hd using h1
  have hall : ∀ i j, d i = d j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨c, hc⟩ := h2 i j hij
      rw [Matrix.mulVec_add, hd i, hd j] at hc
      have hi := congrFun hc i
      have hj := congrFun hc j
      simp [hij, Ne.symm hij] at hi hj
      rw [hi, hj]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨d i₀, Matrix.ext fun a b => ?_⟩
  have h3 : M a b = d b * (Pi.single b 1 : ι → K) a := by
    have := congrFun (hd b) a
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  rw [h3, Matrix.smul_apply, Matrix.one_apply, hall b i₀]
  by_cases h : a = b <;> simp [h]

theorem conjSp_eq_of_scalar {A : gsp r K} {b : Kˣ}
    (hb : (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b)
    (g : StatedSp r K) : conjSp r K A g = g := by
  have hz : (A : GL (Fin r ⊕ Fin r) K) ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [hb, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨b, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp hz (g : GL (Fin r ⊕ Fin r) K)
  exact Subtype.ext (by rw [coe_conjSp, ← hcomm, mul_inv_cancel_right])

theorem conjAut_eq_one_of_scalar {A : gsp r K} {b : Kˣ}
    (hb : (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b) :
    conjAut r K A = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, conjSp_eq_of_scalar hb, MulAut.one_apply]

theorem semilinear_pointwise_centralizer [NeZero r] (k : Subfield K) (A : gsp r K)
    (τ : K ≃+* K)
    (h : ∀ g : StatedSp r k, (conjAut r K A * fieldAut r K τ) (proj r K (subfieldSpHom r k g)) =
      proj r K (subfieldSpHom r k g)) :
    (∃ b : Kˣ, (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b) ∧
      ∀ c ∈ k, τ c = c := by
  classical
  have hline : ∀ u : Fin r ⊕ Fin r → K, (∀ a, u a = 0 ∨ u a = 1) → u ≠ 0 →
      ∃ c : K, ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u =
        c • u := by
    intro u hu01 hu0
    let u₀ : Fin r ⊕ Fin r → k := fun a => if u a = 0 then 0 else 1
    have hu₀ : (fun a => (u₀ a : K)) = u := by
      ext a
      rcases hu01 a with h0 | h1
      · simp [u₀, h0]
      · simp [u₀, h1]
    have hτ : ∀ a, τ (u a) = u a := fun a => by
      rcases hu01 a with h0 | h1
      · simp [h0]
      · simp [h1]
    have h' := h (spTransvection u₀ 1)
    rw [subfieldSpHom_spTransvection, hu₀, alpha_apply_proj] at h'
    exact exists_smul_of_fixes_transvection A τ hu0 hτ h'
  have hsingle : ∀ i : Fin r ⊕ Fin r, ∃ c : K,
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        Pi.single i 1 = c • Pi.single i 1 := by
    intro i
    refine hline _ (fun a => ?_) ?_
    · by_cases ha : a = i <;> simp [ha]
    · intro h0
      have := congrFun h0 i
      simp at this
  have hpair : ∀ i j : Fin r ⊕ Fin r, i ≠ j → ∃ c : K,
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single i 1 + Pi.single j 1) = c • (Pi.single i 1 + Pi.single j 1) := by
    intro i j hij
    refine hline _ (fun a => ?_) ?_
    · by_cases ha : a = i
      · right
        subst ha
        simp [hij]
      · by_cases hb : a = j
        · right
          subst hb
          simp [ha]
        · left
          simp [ha, hb]
    · intro h0
      have := congrFun h0 i
      simp [hij.symm] at this
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl 0⟩
  obtain ⟨d, hd⟩ := exists_scalar_of_lines _ hsingle hpair
  have hd0 : d ≠ 0 := by
    intro hd0
    have hM0 : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      rw [hd, hd0, zero_smul]
    have h1 := Units.mul_inv (A : GL (Fin r ⊕ Fin r) K)
    rw [hM0, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simp at h2
  have hscalar : ∃ b : Kˣ, (A : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b := by
    refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hd,
      Matrix.smul_one_eq_diagonal]
    rfl
  refine ⟨hscalar, fun c hc => ?_⟩
  obtain ⟨b, hb⟩ := hscalar
  have h' := h (spTransvection (Pi.single (Sum.inl 0) 1) ⟨c, hc⟩)
  rw [subfieldSpHom_spTransvection, conjAut_eq_one_of_scalar hb, one_mul, coe_single_one,
    fieldAut_proj] at h'
  have hu0 : (Pi.single (Sum.inl 0) 1 : Fin r ⊕ Fin r → K) ≠ 0 := by
    intro h0
    have := congrFun h0 (Sum.inl 0)
    simp at this
  rw [fieldSp_spTransvection τ (fun a => by by_cases ha : a = Sum.inl 0 <;> simp [ha])] at h'
  exact eq_of_proj_spTransvection_eq hu0 h'

theorem conjAut_mul_fieldAut_eq_of_fixes_subfield [NeZero r] (k : Subfield K) (A : gsp r K)
    (τ : K ≃+* K)
    (h : ∀ g : StatedSp r k, (conjAut r K A * fieldAut r K τ) (proj r K (subfieldSpHom r k g)) =
      proj r K (subfieldSpHom r k g)) :
    conjAut r K A * fieldAut r K τ = fieldAut r K τ := by
  obtain ⟨b, hb⟩ := (semilinear_pointwise_centralizer k A τ h).1
  rw [conjAut_eq_one_of_scalar hb, one_mul]

theorem exists_fieldAut_of_fixes_subfield [NeZero r] (k : Subfield K)
    {α : MulAut (StatedProj (StatedSp r K))} (hα : α ∈ spSemilinearAutGroup r K)
    (h : ∀ g : StatedSp r k, α (proj r K (subfieldSpHom r k g)) =
      proj r K (subfieldSpHom r k g)) :
    ∃ τ : K ≃+* K, (∀ c ∈ k, τ c = c) ∧ α = fieldAut r K τ := by
  obtain ⟨A, τ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hα
  exact ⟨τ, (semilinear_pointwise_centralizer k A τ h).2,
    conjAut_mul_fieldAut_eq_of_fixes_subfield k A τ h⟩

end CFSG.RankThree.PartOne.KCSpComm
