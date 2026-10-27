module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12LinS
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Torus
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bA

public section

namespace CFSG.Quasithin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique

namespace QA12

variable {K : Type} [Field K] {X : Type} [Group X]

structure LinData (π : SpecialLinearGroup (Fin 3) K →* X) : Prop where
  surj : Function.Surjective π
  ker_le : π.ker ≤ scalars 3 K
  coatoms : ∀ A : Subgroup X, (unitriangular 3 K).map π ≤ A →
    (A ⋖ (⊤ : Subgroup X) ↔ ∃ j : Fin 2, A = (Q3 K j).map π)
  normalizer_le : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ≤
    (upperTriangular 3 K).map π

theorem LinData.exists_eq_Q {π : SpecialLinearGroup (Fin 3) K →* X} (h : LinData π)
    {P P' : Subgroup X} (hPar : IsTwoParabolicsOver ((unitriangular 3 K).map π) P P') :
    ∃ j j' : Fin 2, j ≠ j' ∧ P = (Q3 K j).map π ∧ P' = (Q3 K j').map π := by
  have hP : P ⋖ (⊤ : Subgroup X) := (hPar.2.2.2.2 P hPar.2.1).mpr (Or.inl rfl)
  have hP' : P' ⋖ (⊤ : Subgroup X) := (hPar.2.2.2.2 P' hPar.2.2.1).mpr (Or.inr rfl)
  obtain ⟨j, hj⟩ := (h.coatoms P hPar.2.1).mp hP
  obtain ⟨j', hj'⟩ := (h.coatoms P' hPar.2.2.1).mp hP'
  exact ⟨j, j', fun hjj => hPar.1 (by rw [hj, hj', hjj]), hj, hj'⟩

section Core

variable [Finite K] [Finite X]

theorem lin_core {π : SpecialLinearGroup (Fin 3) K →* X} (h : LinData π)
    (hK : ∃ s : Finset K, s.card = 4)
    (heq : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q3 K 0).map π) =
      Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q3 K 1).map π)) (u : Kˣ) :
    ∃ (c : Kˣ) (hc : c ^ 3 = 1), scalarElement c hc ∈ π.ker ∧ (u : K) = (c : K) ^ 2 := by
  have ht0 : tHom u ∈ perfectCore (Q3 K 0) := tHom_mem_perfectCore hK u
  have h1 : π (tHom u) ∈ perfectCore ((Q3 K 0).map π) := by
    rw [← map_perfectCore π (Q3 K 0)]
    exact Subgroup.mem_map_of_mem π ht0
  have hnorm : π (tHom u) ∈
      Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) := by
    refine Subgroup.le_normalizer_map π ⟨tHom u, ?_, rfl⟩
    rw [normalizer_unitriangular]
    exact tHom_mem_upperTriangular u
  have h2 : π (tHom u) ∈ perfectCore ((Q3 K 1).map π) := by
    have hm : π (tHom u) ∈ Subgroup.normalizer
        (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓ perfectCore ((Q3 K 0).map π) :=
      ⟨hnorm, h1⟩
    rw [heq] at hm
    exact hm.2
  rw [← map_perfectCore π (Q3 K 1)] at h2
  obtain ⟨m, hm, hmπ⟩ := Subgroup.mem_map.mp h2
  have hz : m⁻¹ * tHom u ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmπ, inv_mul_cancel]
  obtain ⟨c, hc, hzc⟩ := mem_scalars.mp (h.ker_le hz)
  have hsc : scalarElement c hc = m⁻¹ * tHom u :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [coe_scalarElement, ← hzc]
  refine ⟨c, hc, hsc ▸ hz, eq_sq_of_tHom_eq_mul hm hzc ?_⟩
  exact (mul_inv_cancel_left m (tHom u)).symm

theorem lin_false_of_ker_bot {π : SpecialLinearGroup (Fin 3) K →* X} (h : LinData π)
    (hker : π.ker = ⊥) (hK : 4 ≤ Nat.card K)
    (heq : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q3 K 0).map π) =
      Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q3 K 1).map π)) : False := by
  obtain ⟨u, hu⟩ := exists_unit_ne_one hK
  obtain ⟨c, hc, hker', hsq⟩ := lin_core h (exists_finset_card_four hK) heq u
  rw [hker, Subgroup.mem_bot] at hker'
  have h00 := congrFun (congrFun (congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
    (x : Matrix (Fin 3) (Fin 3) K)) hker') 0) 0
  simp only [coe_scalarElement, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h00
  apply hu
  apply Units.ext
  rw [hsq, h00]
  simp

theorem card_eq_four_of_cube (hK : 4 ≤ Nat.card K) (h : ∀ u : Kˣ, u ^ 3 = 1) :
    Nat.card K = 4 := by
  classical
  have := Fintype.ofFinite K
  have h1 := IsCyclic.card_pow_eq_one_le (α := Kˣ) (n := 3) (by norm_num)
  have h2 : (Finset.univ.filter fun a : Kˣ => a ^ 3 = 1) = Finset.univ := by
    ext a
    simp [h a]
  rw [h2, Finset.card_univ] at h1
  have h3 : Nat.card Kˣ = Fintype.card Kˣ := Nat.card_eq_fintype_card
  rw [Nat.card_units] at h3
  omega

theorem lin_four [CharP K 2] {π : SpecialLinearGroup (Fin 3) K →* X} (h : LinData π)
    (hker : π.ker = scalars 3 K) (hK : Nat.card K = 4) :
    Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ≤
        perfectCore ((Q3 K 0).map π) ∧
      Nat.card (Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X)) =
        3 * Nat.card ((unitriangular 3 K).map π) := by
  classical
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four (le_of_eq hK.symm)
  have hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1 := by
    intro a ha
    have := Fintype.ofFinite K
    have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [← Nat.card_eq_fintype_card, hK] at h1
    exact h1
  set U : Subgroup X := (unitriangular 3 K).map π with hU
  set N : Subgroup X := Subgroup.normalizer (U : Set X) with hN
  let τ : Kˣ →* X := π.comp tHom
  have hVN0 : unitriangular 3 K ≤ perfectCore (Q3 K 0) :=
    F146Field.Case2b.unitriangular_le_perfectCore_Q3 hK4 0
  have hscal : ∀ z : SpecialLinearGroup (Fin 3) K, z ∈ scalars 3 K →
      z ∈ perfectCore (Q3 K 0) → z = 1 :=
    fun z hz hz0 => congrArg Subtype.val (blk3_scalars 0 ⟨z, hz0⟩ hz)
  have htriv : ∀ u : Kˣ, tHom u = 1 → u = 1 := by
    intro u hu
    have e := congrFun (congrFun (congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K)) hu) 1) 1
    rw [coe_tHom] at e
    exact Units.ext (by simpa using e)
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : tHom u ∈ π.ker := hu
    rw [hker] at h1
    exact htriv u (hscal _ h1 (tHom_mem_perfectCore hK4 u))
  have hdisj : U ⊓ τ.range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, u, hxu⟩
    obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hxU
    have hzk : v⁻¹ * tHom u ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvx]
      have : π (tHom u) = x := hxu
      rw [this, inv_mul_cancel]
    rw [hker] at hzk
    have hz1 : v⁻¹ * tHom u = 1 :=
      hscal _ hzk ((perfectCore (Q3 K 0)).mul_mem
        ((perfectCore (Q3 K 0)).inv_mem (hVN0 hv)) (tHom_mem_perfectCore hK4 u))
    have htv : v = tHom u := inv_mul_eq_one.mp hz1
    have hu1 : u = 1 := by
      have e := hv.2 1
      rw [htv, coe_tHom] at e
      exact Units.ext (by simpa using e)
    rw [Subgroup.mem_bot, ← hxu, hu1, map_one]
  have hmul : ∀ n ∈ N, ∃ v ∈ U, ∃ r ∈ τ.range, n = v * r := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (h.normalizer_le hn)
    obtain ⟨v, hv, d, hdd, rfl⟩ := exists_unitriangular_mul_diagonal hx
    obtain ⟨c, hc, u, hdu⟩ := exists_scalar_mul_tHom (mem_diagSL.mpr hdd) hcube
    have hcker : scalarElement c hc ∈ π.ker := by
      rw [hker]
      exact scalarElement_mem_scalars c hc
    refine ⟨π v, Subgroup.mem_map_of_mem π hv, τ u, ⟨u, rfl⟩, ?_⟩
    rw [hdu, map_mul, map_mul, MonoidHom.mem_ker.mp hcker, one_mul]
    rfl
  have hRN : τ.range ≤ N := by
    rintro _ ⟨u, rfl⟩
    refine Subgroup.le_normalizer_map π ⟨tHom u, ?_, rfl⟩
    rw [normalizer_unitriangular]
    exact tHom_mem_upperTriangular u
  have hUN : U ≤ N := Subgroup.le_normalizer
  have hR : Nat.card τ.range = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hK]
  have hcard := card_mul_card_of_mul_eq hUN hRN hdisj hmul
  rw [hR] at hcard
  have hU0 : U ≤ perfectCore ((Q3 K 0).map π) := by
    rw [← map_perfectCore π (Q3 K 0)]
    exact Subgroup.map_mono hVN0
  have hR0 : τ.range ≤ perfectCore ((Q3 K 0).map π) := by
    rintro _ ⟨u, rfl⟩
    rw [← map_perfectCore π (Q3 K 0)]
    exact Subgroup.mem_map_of_mem π (tHom_mem_perfectCore hK4 u)
  refine ⟨fun n hn => ?_, by rw [← hcard, mul_comm]⟩
  obtain ⟨v, hv, r, hr, rfl⟩ := hmul n hn
  exact mul_mem (hU0 hv) (hR0 hr)

theorem lin_psl_01 [CharP K 2] {π : SpecialLinearGroup (Fin 3) K →* X} (h : LinData π)
    (hker : π.ker = scalars 3 K) (hK : 4 ≤ Nat.card K)
    (heq : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q3 K 0).map π) =
      Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q3 K 1).map π)) :
    Nat.card K = 4 ∧
      Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ≤
        perfectCore ((Q3 K 0).map π) ⊓ perfectCore ((Q3 K 1).map π) ∧
      Nat.card (Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X)) =
        3 * Nat.card ((unitriangular 3 K).map π) := by
  have hK4 := exists_finset_card_four hK
  have hcube : ∀ u : Kˣ, u ^ 3 = 1 := by
    intro u
    obtain ⟨c, hc, -, hsq⟩ := lin_core h hK4 heq u
    have hu : u = c ^ 2 := Units.ext (by simpa using hsq)
    rw [hu, ← pow_mul, mul_comm, pow_mul, hc, one_pow]
  have h4 := card_eq_four_of_cube hK hcube
  obtain ⟨hle, hcard⟩ := lin_four h hker h4
  refine ⟨h4, le_inf hle fun n hn => ?_, hcard⟩
  have hm : n ∈ Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ⊓
      perfectCore ((Q3 K 0).map π) := ⟨hn, hle hn⟩
  rw [heq] at hm
  exact hm.2

end Core

section Assemble

omit [Group X] in
theorem map_equiv_symm_map {A B' : Type*} [Group A] [Group B'] (e : A ≃* B') (H : Subgroup A) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem normalizer_map_equiv {A B' : Type*} [Group A] [Group B'] (σ : A ≃* B') (H : Subgroup A) :
    Subgroup.normalizer ((H.map σ.toMonoidHom : Subgroup B') : Set B') =
      (Subgroup.normalizer (H : Set A)).map σ.toMonoidHom := by
  have h := Subgroup.comap_normalizer_eq_of_surjective (H.map σ.toMonoidHom)
    (f := σ.toMonoidHom) σ.surjective
  rw [Subgroup.comap_map_eq_self_of_injective σ.injective] at h
  rw [← h, Subgroup.map_comap_eq_self_of_surjective σ.surjective]

variable [Finite K] [Finite X]

theorem residualOvergroupsAt_sl3 (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (SpecialLinearGroup (Fin 3) K) (unitriangular 3 K)
      (fun j => Q3 K j) := by
  have hB := isSolvable_upperTriangular (n := 3) (K := K) hK
  have h := residualOvergroupsAt_of_rank_two_data
    (π := MonoidHom.id (SpecialLinearGroup (Fin 3) K)) Function.surjective_id
    (V := unitriangular 3 K) (B := upperTriangular 3 K) (Q := Q3 K) (H := H3 K)
    (fun x hx => by
      rw [MonoidHom.mem_ker] at hx
      rw [show x = 1 from hx]
      exact one_mem _)
    (unitriangular_le_upperTriangular 3 K)
    (fun j => by
      rw [Q3_eq]
      exact upperTriangular_le_flagStabilizer _)
    Q3_ne covBy_Q3 (fun A hVA hAt => contained_in_Q3 hVA hAt) hB commutator_Q3_le
    (fun j A hVA hAQ hAns => H3_le_of_nonsolvable hB j hVA hAQ hAns)
  simpa [Subgroup.map_id] using h

theorem borel_isPSL {n : ℕ} (hn : 2 ≤ n) (hX : IsPSL 3 2 n X) {U P P' : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hPar : IsTwoParabolicsOver U P P')
    (heq : Subgroup.normalizer (U : Set X) ⊓ perfectCore P =
      Subgroup.normalizer (U : Set X) ⊓ perfectCore P') :
    n = 2 ∧ Subgroup.normalizer (U : Set X) ≤ perfectCore P ⊓ perfectCore P' ∧
      Nat.card (Subgroup.normalizer (U : Set X)) = 3 * Nat.card U := by
  obtain ⟨K, hF, hFin, hCh, φ, hcard, hφU, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hX hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : SpecialLinearGroup (Fin 3) K →* X := φ.symm.toMonoidHom.comp (proj 3 K) with hπ
  have hπU : (unitriangular 3 K).map π = (projUnitriangular 3 K).map φ.symm.toMonoidHom := by
    rw [hπ, ← Subgroup.map_map]
    rfl
  have hVπ : (unitriangular 3 K).map π = U := by
    rw [hπU, ← hφU]
    exact map_equiv_symm_map φ U
  have hQ : ∀ j : Fin 2, (Q3 K j).map π =
      (projStabilizer (flagSpace 3 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom := fun j => by
    rw [hπ, ← Subgroup.map_map]
    rfl
  have hker : π.ker = scalars 3 K := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ.symm (proj 3 K x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, proj_eq_one_iff]
  have hN : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ≤
      (upperTriangular 3 K).map π := by
    rw [hπU, normalizer_map_equiv φ.symm, normalizer_projUnitriangular 2]
    rw [hπ, ← Subgroup.map_map]
    exact le_rfl
  have hD : LinData π :=
    ⟨φ.symm.surjective.comp (proj_surjective 3 K), hker.le, fun A hA => by
      have hA' : U ≤ A := hVπ ▸ hA
      rw [hres.2.2.1 A hA']
      simp only [hQ], hN⟩
  have hK2 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  subst hVπ
  obtain ⟨j, j', hjj, rfl, rfl⟩ := hD.exists_eq_Q hPar
  have key : Nat.card K = 4 ∧
      Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ≤
        perfectCore ((Q3 K 0).map π) ⊓ perfectCore ((Q3 K 1).map π) ∧
      Nat.card (Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X)) =
        3 * Nat.card ((unitriangular 3 K).map π) := by
    fin_cases j <;> fin_cases j'
    · exact absurd rfl hjj
    · exact lin_psl_01 hD hker hK2 heq
    · obtain ⟨h4, hle, hc⟩ := lin_psl_01 hD hker hK2 heq.symm
      exact ⟨h4, hle, hc⟩
    · exact absurd rfl hjj
  have hn2 : n = 2 := by
    have h2 : 2 ^ n = 2 ^ 2 := by
      rw [← hcard, key.1]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  refine ⟨hn2, ?_, key.2.2⟩
  fin_cases j <;> fin_cases j'
  · exact absurd rfl hjj
  · exact key.2.1
  · rw [inf_comm]
    exact key.2.1
  · exact absurd rfl hjj

theorem false_of_isSL3 {n : ℕ} (hn : 2 ≤ n) (hX : IsSL3 (2 ^ n) X) {U P P' : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hPar : IsTwoParabolicsOver U P P')
    (heq : Subgroup.normalizer (U : Set X) ⊓ perfectCore P =
      Subgroup.normalizer (U : Set X) ⊓ perfectCore P') : False := by
  obtain ⟨K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hCh : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hK2 : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨n, hcard⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let e₁ : X ≃* SpecialLinearGroup (Fin 3) K :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  obtain ⟨S, hS⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ := by
    rw [← hS]
    exact isSylowTwoOf_top_of_sylow S
  obtain ⟨φ, hφU, hres⟩ := (residualOvergroupsAt_sl3 hK2).exists_iso_of_isSylow e₁ hU₀ hU
  set π : SpecialLinearGroup (Fin 3) K →* X := φ.symm.toMonoidHom with hπ
  have hVπ : (unitriangular 3 K).map π = U := by
    rw [← hφU]
    exact map_equiv_symm_map φ U
  have hker : π.ker = ⊥ := MonoidHom.ker_eq_bot_iff _ |>.mpr φ.symm.injective
  have hN : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup X) : Set X) ≤
      (upperTriangular 3 K).map π := by
    rw [hπ, normalizer_map_equiv φ.symm, normalizer_unitriangular]
  have hD : LinData π :=
    ⟨φ.symm.surjective, by rw [hker]; exact bot_le, fun A hA => by
      have hA' : U ≤ A := hVπ ▸ hA
      exact hres.2.2.1 A hA', hN⟩
  subst hVπ
  obtain ⟨j, j', hjj, rfl, rfl⟩ := hD.exists_eq_Q hPar
  fin_cases j <;> fin_cases j'
  · exact absurd rfl hjj
  · exact lin_false_of_ker_bot hD hker hK4 heq
  · exact lin_false_of_ker_bot hD hker hK4 heq.symm
  · exact absurd rfl hjj

end Assemble

end QA12

end CFSG.Quasithin
