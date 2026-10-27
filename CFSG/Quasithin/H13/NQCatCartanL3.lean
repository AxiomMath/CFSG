module

public import CFSG.Quasithin.H13.NQCatCartanBasic
public import CFSG.Quasithin.Vol2.KGFact4413L3
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBQPrimeLinearThreeSylowInner
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.Quasithin.H13.NQCat.CartanL3

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.H13.KG4413 CFSG.ComponentClassification
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem fst_eq_snd_of_dg3_mem_scalars {s : Fˣ × Fˣ} (h : dg3 s ∈ scalars 3 F) : s.1 = s.2 := by
  obtain ⟨c, -, hc⟩ := h
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  rw [coe_dg3] at h0 h1
  simp at h0 h1
  exact Units.ext (h0.trans h1.symm)

theorem inv_mul_eq_of_proj_dg3_eq {s s' : Fˣ × Fˣ} (h : proj 3 F (dg3 s) = proj 3 F (dg3 s')) :
    s.1⁻¹ * s'.1 = s.2⁻¹ * s'.2 := by
  rw [proj_eq_proj_iff, ← map_inv, ← map_mul] at h
  exact fst_eq_snd_of_dg3_mem_scalars h

theorem map_dg3 (σ : F ≃+* F) (s : Fˣ × Fˣ) :
    SpecialLinearGroup.map σ.toRingHom (dg3 s) =
      dg3 (Units.map σ.toRingHom.toMonoidHom s.1, Units.map σ.toRingHom.toMonoidHom s.2) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, coe_dg3, coe_dg3]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

theorem eq_one_of_fieldAut_fix {σ : F ≃+* F}
    (h : ∀ x : Fˣ, LinearFlag.fieldAut 3 F σ (proj 3 F (dg3 (x, 1))) = proj 3 F (dg3 (x, 1))) :
    σ = 1 := by
  ext a
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  have h1 := h (Units.mk0 a ha)
  rw [fieldAut_proj, map_dg3] at h1
  have h2 := inv_mul_eq_of_proj_dg3_eq h1
  rw [map_one, inv_one, one_mul, inv_mul_eq_one] at h2
  have h3 := congrArg Units.val h2
  show σ a = a
  simpa using h3

theorem slConjugation_of_mem_scalars (B : GL (Fin 3) F) {z : SpecialLinearGroup (Fin 3) F}
    (hz : z ∈ scalars 3 F) : CatalogueBHigherLinearAction.slConjugation 3 F B z = z := by
  obtain ⟨c, -, hc⟩ := hz
  have hBB : (B : Matrix (Fin 3) (Fin 3) F) * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  apply Subtype.ext
  rw [coe_slConjugation, hc,
    ← (Matrix.scalar_commute (c : F) (fun r => Commute.all _ r) (B : Matrix (Fin 3) (Fin 3) F)).eq,
    Matrix.mul_assoc, hBB, Matrix.mul_one]

theorem slGraphAut_of_mem_scalars {z : SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) :
    CatalogueBGraphForm.slGraphAut 3 F z = z⁻¹ := by
  obtain ⟨c, -, hc⟩ := inv_mem hz
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, hc, scalar_apply, diagonal_transpose]

theorem mem_of_pow_three_mem {G : Type*} [Group G] {H : Subgroup G} {x : G} {e : ℕ}
    (h3 : x ^ 3 ∈ H) (he : x ^ 2 ^ e = 1) : x ∈ H := by
  have hcop : Nat.Coprime 3 (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one he)
      (Nat.Coprime.pow_right e (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem h3 m

section Finite

variable [Finite F]

theorem fieldAut_mem_dL3 (σ : F ≃+* F) {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    LinearFlag.fieldAut 3 F σ d ∈ dL3 F := by
  obtain ⟨m, hm⟩ := exists_fieldAut_dL3 σ
  rw [hm d hd]
  exact zpow_mem hd m

theorem card_eq_four_of_pow_three {k : ℕ} (hk : 2 ≤ k) (hK : Nat.card F = 2 ^ k)
    (h3 : ∀ t : Fˣ, t ^ 3 = 1) : Nat.card F = 4 := by
  have h1 : Monoid.exponent Fˣ ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one h3
  rw [IsCyclic.exponent_eq_card, Nat.card_units] at h1
  have h2 := Nat.le_of_dvd (by norm_num) h1
  have h4 : 4 ≤ 2 ^ k :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

end Finite

section CharTwo

variable [CharP F 2]

theorem gammaZero_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) : gammaZero F d ∈ dL3 F := by
  rw [gammaZero_dL3 hd]
  exact w0L3_conj_mem_dL3 (inv_mem hd)

theorem gammaZero_proj_dg3 (x y : Fˣ) :
    gammaZero F (proj 3 F (dg3 (x, y))) = proj 3 F (dg3 ((x⁻¹ * y⁻¹)⁻¹, y⁻¹)) := by
  rw [gammaZero_dL3 ⟨_, ⟨(x, y), rfl⟩, rfl⟩, w0L3, ← map_inv (proj 3 F) (dg3 (x, y)),
    ← map_inv (proj 3 F) wJ, wJ_inv, ← map_inv dg3, Prod.inv_mk, ← map_mul, ← map_mul,
    wJ_mul_dg3_mul_wJ]

end CharTwo

variable [Finite F] [CharP F 2]

theorem eq_of_conjAut_mul_inv_mem {A : GL (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0)
    {d e : projectiveSL 3 F} (hd : d ∈ dL3 F) (he : e ∈ dL3 F)
    (h : LinearFlag.conjAut 3 F A e * d⁻¹ ∈ projUnitriangular 3 F) : e = d := by
  have h1 := conjAut_dL3_mem hA he
  have h2 : e * (e⁻¹ * LinearFlag.conjAut 3 F A e)⁻¹ * e⁻¹ ∈ projUnitriangular 3 F :=
    (Subgroup.mem_normalizer_iff.mp (dL3_le_normalizer he) _).mp (Subgroup.inv_mem _ h1)
  have h3 := mul_mem h2 h
  rw [show e * (e⁻¹ * LinearFlag.conjAut 3 F A e)⁻¹ * e⁻¹ * (LinearFlag.conjAut 3 F A e * d⁻¹) =
    e * d⁻¹ by group] at h3
  have h4 : e * d⁻¹ ∈ dL3 F ⊓ projUnitriangular 3 F :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ he (Subgroup.inv_mem _ hd), h3⟩
  rw [dL3_inf, mem_bot, mul_inv_eq_one] at h4
  exact h4

theorem inner_of_semilinear {β : MulAut (projectiveSL 3 F)} (hβs : β ∈ semilinearAutGroup 3 F)
    (hβ : ∃ e : ℕ, β ^ 2 ^ e = 1)
    (hβU : (projUnitriangular 3 F).map β.toMonoidHom = projUnitriangular 3 F)
    (hN : ∀ x ∈ normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)),
      β x * x⁻¹ ∈ projUnitriangular 3 F) :
    ∃ y : projectiveSL 3 F, β = MulAut.conj y := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hβs
  have hA := upperTriangular_of_semilinear_normalizes hβU
  have hfix : ∀ d ∈ dL3 F, LinearFlag.fieldAut 3 F σ d = d := fun d hd =>
    eq_of_conjAut_mul_inv_mem hA hd (fieldAut_mem_dL3 σ hd) (hN d (dL3_le_normalizer hd))
  obtain rfl : σ = 1 := eq_one_of_fieldAut_fix fun x => hfix _ ⟨_, ⟨(x, 1), rfl⟩, rfl⟩
  rw [map_one, mul_one] at hβ ⊢
  obtain ⟨e, he⟩ := hβ
  obtain ⟨y, hy⟩ := mem_of_pow_three_mem
    (CFSG.QuasithinUnique.SteinbergBQ.PrimeLinearThree.conjAut_pow_three_mem A) he
  exact ⟨y, hy.symm⟩

theorem graph_data {α : MulAut (projectiveSL 3 F)} (hαs : α ∉ semilinearAutGroup 3 F)
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hN : ∀ x ∈ normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)),
      α x * x⁻¹ ∈ projUnitriangular 3 F) :
    ∃ A : GL (Fin 3) F, (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) ∧
      α = LinearFlag.conjAut 3 F A * gammaZero F ∧ ∀ t : Fˣ, t ^ 3 = 1 := by
  obtain ⟨A, σ, hA, rfl⟩ := exists_eq_semilinear_mul_gammaZero hαU hαs
  have hfix : ∀ d ∈ dL3 F, LinearFlag.fieldAut 3 F σ (gammaZero F d) = d := fun d hd =>
    eq_of_conjAut_mul_inv_mem hA hd (fieldAut_mem_dL3 σ (gammaZero_mem_dL3 hd))
      (hN d (dL3_le_normalizer hd))
  obtain rfl : σ = 1 := eq_one_of_fieldAut_fix fun x => by
    have h1 := hfix _ ⟨_, ⟨(x, 1), rfl⟩, rfl⟩
    rwa [gammaZero_proj_dg3, inv_one, mul_one, inv_inv] at h1
  refine ⟨A, hA, by rw [map_one, mul_one], fun t => ?_⟩
  have h1 := hfix _ ⟨_, ⟨(t, t⁻¹), rfl⟩, rfl⟩
  rw [map_one, MulAut.one_apply, gammaZero_proj_dg3, inv_inv, inv_mul_cancel, inv_one] at h1
  have h2 := inv_mul_eq_of_proj_dg3_eq h1
  rw [inv_one, one_mul] at h2
  calc t ^ 3 = t ^ 2 * t := pow_succ t 2
    _ = t ^ 2 * (t⁻¹ * t⁻¹) := by rw [← h2]
    _ = 1 := by group

theorem map_ne_of_not_mem_semilinear {α : MulAut (projectiveSL 3 F)}
    (hαs : α ∉ semilinearAutGroup 3 F) {P : Subgroup (projectiveSL 3 F)}
    (hBP : projUpperTriangular 3 F ≤ P) (hP : P ⋖ ⊤) : P.map α.toMonoidHom ≠ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd1, hd3, rfl⟩ := eq_projStabilizer_of_isCoatom (covBy_top_iff.mp hP) hBP
  obtain ⟨D, σ, rfl⟩ := exists_formula_of_not_mem_semilinear hαs
  obtain ⟨hmap, hdim⟩ := map_projStabilizer_of_typeExchanging D σ (flagSpace 3 F d)
  rw [finrank_flagSpace (by omega)] at hdim
  rw [hmap]
  intro h
  have hne : ∀ V : Submodule F (Fin 3 → F), 1 ≤ Module.finrank F V →
      Module.finrank F V < 3 → ⊥ < V ∧ V < ⊤ := by
    intro V h1 h3
    refine ⟨bot_lt_iff_ne_bot.mpr fun hV => ?_, lt_top_iff_ne_top.mpr fun hV => ?_⟩
    · rw [hV, finrank_bot] at h1
      omega
    · rw [hV, finrank_top, Module.finrank_fin_fun] at h3
      omega
  have hW := (maximal_parabolics (K := F) (n := 3) 2 (by norm_num)).2.1
    (hne _ (by omega) (by omega))
    (hne _ (by rw [finrank_flagSpace (by omega)]; omega)
      (by rw [finrank_flagSpace (by omega)]; omega)) h
  have h1 := congrArg (fun V : Submodule F (Fin 3 → F) => Module.finrank F V) hW
  simp only [finrank_flagSpace (show d ≤ 3 by omega)] at h1
  omega

theorem cartanConcl_projectiveSL {k : ℕ} (hk : 2 ≤ k) (hK : Nat.card F = 2 ^ k) :
    CartanConcl (projectiveSL 3 F) (projUnitriangular 3 F) (Nat.card F = 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro α hα hαU hN
  by_cases hs : α ∈ semilinearAutGroup 3 F
  · exact Or.inl (inner_of_semilinear hs hα hαU hN)
  obtain ⟨-, -, -, h3⟩ := graph_data hs hαU hN
  have hαN : ∀ x ∈ normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)),
      α x ∈ normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) := by
    intro x hx
    have h1 : normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) =
        (normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F))).map α.toMonoidHom := by
      conv_lhs => rw [← hαU]
      exact (map_equiv_normalizer_eq _ α).symm
    rw [h1]
    exact mem_map_of_mem _ hx
  refine Or.inr ⟨card_eq_four_of_pow_three hk hK h3, ?_, fun P hNP hP =>
    map_ne_of_not_mem_semilinear hs (by rwa [← normalizer_projUnitriangular 2]) hP⟩
  obtain ⟨e, he⟩ := hα
  refine inner_of_semilinear (by
      rw [sq]
      exact UnbalancedCatalog.EvenLinearSL.mul_self_mem_semilinearAutGroup (by norm_num) α)
    ⟨e, by rw [← pow_mul, mul_comm, pow_mul, he, one_pow]⟩
    (by rw [sq, map_mul_toMonoidHom, hαU, hαU]) fun x hx => ?_
  rw [sq, MulAut.mul_apply,
    show α (α x) * x⁻¹ = α (α x) * (α x)⁻¹ * (α x * x⁻¹) by group]
  exact mul_mem (hN _ (hαN x hx)) (hN x hx)

theorem cartanConcl_specialLinear {k : ℕ} (hk : 2 ≤ k) (hK : Nat.card F = 2 ^ k) :
    CartanConcl (SpecialLinearGroup (Fin 3) F) (unitriangular 3 F) False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro α hα hαU hN
  left
  have hp : ∀ g, descendAut 3 F α (proj 3 F g) = proj 3 F (α g) := descendAut_proj 3 F α
  have hβU : (projUnitriangular 3 F).map (descendAut 3 F α).toMonoidHom =
      projUnitriangular 3 F := by
    have h : (descendAut 3 F α).toMonoidHom.comp (proj 3 F) = (proj 3 F).comp α.toMonoidHom :=
      MonoidHom.ext hp
    rw [projUnitriangular, Subgroup.map_map, h, ← Subgroup.map_map, hαU]
  have hβN : ∀ x ∈ normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)),
      descendAut 3 F α x * x⁻¹ ∈ projUnitriangular 3 F := by
    intro x hx
    rw [normalizer_projUnitriangular 2] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← normalizer_unitriangular] at hg
    rw [hp, ← map_inv, ← map_mul]
    exact mem_map_of_mem _ (hN g hg)
  have hβ : ∃ e : ℕ, descendAut 3 F α ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hα
    exact ⟨e, by rw [← map_pow, he, map_one]⟩
  by_cases hs : descendAut 3 F α ∈ semilinearAutGroup 3 F
  · obtain ⟨y, hy⟩ := inner_of_semilinear hs hβ hβU hβN
    obtain ⟨g, rfl⟩ := proj_surjective 3 F y
    have hdc : descendAut 3 F (MulAut.conj g) = MulAut.conj (proj 3 F g) := by
      ext x
      obtain ⟨z, rfl⟩ := proj_surjective 3 F x
      rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact ⟨g, RankThree.PartOne.AUTSL.descendAut_injective (by norm_num) (by rw [hy, hdc])⟩
  exfalso
  obtain ⟨A, -, hβeq, h3⟩ := graph_data hs hβU hβN
  have hlift : α = CatalogueBHigherLinearAction.slConjugation 3 F A *
      (CatalogueBHigherLinearAction.slConjugation 3 F (SpecialLinearGroup.toGL (wJ : SL(3, F))) *
        CatalogueBGraphForm.slGraphAut 3 F) :=
    RankThree.PartOne.AUTSL.descendAut_injective (by norm_num) (by
      rw [map_mul, map_mul]
      exact hβeq)
  obtain ⟨t, ht⟩ := exists_unit_ne_one (exists_finset_card_four_of_card hk hK)
  have htt : (t * t)⁻¹ = t := inv_eq_of_mul_eq_one_left (by
    rw [← mul_assoc, ← pow_three']
    exact h3 t)
  have hz : dg3 (t, t) ∈ scalars 3 F := ⟨t, h3 t, by
    rw [coe_dg3, scalar_apply]
    congr 1
    funext i
    fin_cases i <;> simp [htt]⟩
  have hαz : α (dg3 (t, t)) = (dg3 (t, t))⁻¹ := by
    rw [hlift, MulAut.mul_apply, MulAut.mul_apply, slGraphAut_of_mem_scalars hz,
      slConjugation_of_mem_scalars _ (inv_mem hz), slConjugation_of_mem_scalars _ (inv_mem hz)]
  have h1 := (hN (dg3 (t, t)) (by
    rw [normalizer_unitriangular]
    exact dg3_mem_upperTriangular _)).2 0
  rw [hαz, ← map_inv, ← map_mul, coe_dg3] at h1
  have h2 : t⁻¹ * t⁻¹ = 1 := Units.ext (by simpa using h1)
  apply ht
  have h4 : t = 1 :=
    calc t = t ^ 3 * (t⁻¹ * t⁻¹) := by group
      _ = 1 := by rw [h3 t, h2, one_mul]
  rw [h4, Units.val_one]

end CFSG.Quasithin.H13.NQCat.CartanL3
