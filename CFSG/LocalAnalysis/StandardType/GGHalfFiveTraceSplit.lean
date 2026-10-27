module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNoSmallRep
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix Polynomial

private theorem f4Omega_sq_ne_one : f4Omega ^ 2 ≠ 1 := by
  intro h
  have h3 : f4Omega ^ 3 = f4Omega := by rw [pow_succ, h, one_mul]
  rw [f4Omega_pow_three] at h3
  exact f4Omega_ne_one h3.symm

private theorem f4Omega_sq_ne_omega : f4Omega ^ 2 ≠ f4Omega := by
  intro h
  have h3 : f4Omega ^ 3 = f4Omega := by
    calc f4Omega ^ 3 = f4Omega ^ 2 * f4Omega := by rw [pow_succ]
      _ = f4Omega * f4Omega := by rw [h]
      _ = f4Omega ^ 2 := by rw [← pow_two]
      _ = f4Omega := h
  rw [f4Omega_pow_three] at h3
  exact f4Omega_ne_one h3.symm

private theorem f4Omega_isPrimitiveRoot : IsPrimitiveRoot f4Omega 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf f4Omega = 3 := orderOf_eq_prime f4Omega_pow_three f4Omega_ne_one
  rw [← hord]
  exact IsPrimitiveRoot.orderOf f4Omega

private theorem ker_aeval_prod_X_sub_C_eq_iSup {V : Type*} [AddCommGroup V] [Module F4 V]
    (f : Module.End F4 V) (s : Finset F4) :
    LinearMap.ker (Polynomial.aeval f (∏ a ∈ s, (Polynomial.X - Polynomial.C a) : Polynomial F4)) =
      ⨆ a ∈ s, f.eigenspace a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, map_one, Finset.notMem_empty, iSup_false, iSup_bot]
    rw [Module.End.one_eq_id]; exact LinearMap.ker_id
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.iSup_insert, ← ih]
    have hcop : IsCoprime (Polynomial.X - Polynomial.C a : Polynomial F4)
        (∏ b ∈ s, (Polynomial.X - Polynomial.C b)) :=
      IsCoprime.prod_right fun b hb =>
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub
          (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun h => ha (h ▸ hb)))
    rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop]
    congr 1
    ext v
    simp [LinearMap.mem_ker, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
      Module.End.mem_eigenspace_iff, Algebra.algebraMap_eq_smul_one, sub_eq_zero]

private theorem iSup_eigenspace_eq_top_of_pow_three {V : Type*} [AddCommGroup V] [Module F4 V]
    (Z : Module.End F4 V) (hZ : Z ^ 3 = 1) :
    ⨆ μ : F4, Z.eigenspace μ = ⊤ := by
  have h1 : Polynomial.aeval Z (Polynomial.X ^ 3 - 1 : Polynomial F4) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hZ, sub_self]
  rw [Polynomial.X_pow_sub_one_eq_prod (by norm_num) f4Omega_isPrimitiveRoot] at h1
  have h2 := ker_aeval_prod_X_sub_C_eq_iSup Z (Polynomial.nthRootsFinset 3 (1 : F4))
  rw [h1, LinearMap.ker_zero] at h2
  refine top_unique ?_
  rw [h2]
  exact iSup₂_le fun a _ => le_iSup (fun μ => Z.eigenspace μ) a

private theorem perfect_hom_eq_one {G M : Type*} [Group G] [CommMonoid M]
    (hG : Group.IsPerfect G) (f : G →* M) (g : G) : f g = 1 := by
  haveI := hG
  let f' : G →* Mˣ :=
    { toFun := fun x => ⟨f x, f x⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
        by rw [← map_mul, inv_mul_cancel, map_one]⟩,
      map_one' := Units.ext (map_one f),
      map_mul' := fun x y => Units.ext (map_mul f x y) }
  haveI : IsMulCommutative ↥f'.range :=
    ⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mul_comm (a : Mˣ) (b : Mˣ))⟩⟩
  haveI : Group.IsPerfect ↥f'.range := Group.IsPerfect.range (f := f')
  have h1 : (⟨f' g, ⟨g, rfl⟩⟩ : f'.range) = ⟨1, ⟨1, map_one f'⟩⟩ := Subsingleton.elim _ _
  have h2 : f' g = 1 := congrArg Subtype.val h1
  change (f' g : M) = 1
  rw [h2]
  rfl

private theorem fin3_sum_eq_of_f4 (t : Fin 3 → F4) (k : Fin 3) (hk : k ≠ 0)
    (h0 : t 0 = 1) (hj : ∀ j, j ≠ 0 → j ≠ k → t j = 0) :
    t 0 + t 1 + t 2 = 1 + t k := by
  have hk1 : k = 1 ∨ k = 2 := by fin_cases k <;> simp_all
  rcases hk1 with rfl | rfl
  · rw [h0, hj 2 (by decide) (by decide)]
    simp
  · rw [h0, hj 1 (by decide) (by decide)]
    simp

private theorem exists_natural_three_fixed_line_aux
    (R : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4)
    (hR : Function.Injective R) :
    ∃ (α : SpecialLinearGroup (Fin 3) F4 ≃* SpecialLinearGroup (Fin 3) F4)
      (E : (Fin 4 → F4) ≃ₗ[F4] (F4 × (Fin 3 → F4))),
      (∀ s v,
        E ((R s : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) =
          ((E v).1, (α s : Matrix (Fin 3) (Fin 3) F4) *ᵥ (E v).2)) ∧
      (∀ s, Matrix.trace (R s : Matrix (Fin 4) (Fin 4) F4) =
        1 + Matrix.trace (α s : Matrix (Fin 3) (Fin 3) F4)) := by
  classical
  let z : SpecialLinearGroup (Fin 3) F4 :=
    ⟨f4Omega • (1 : Matrix (Fin 3) (Fin 3) F4), by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
      exact f4Omega_pow_three⟩
  let ρ : SpecialLinearGroup (Fin 3) F4 →* Module.End F4 (Fin 4 → F4) :=
    { toFun := fun s => Matrix.toLin' (R s : Matrix (Fin 4) (Fin 4) F4),
      map_one' := by
        show Matrix.toLin' ((R 1 : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
          (1 : Module.End F4 (Fin 4 → F4))
        rw [map_one R]
        show Matrix.toLin' (1 : Matrix (Fin 4) (Fin 4) F4) = 1
        rw [Matrix.toLin'_one, Module.End.one_eq_id],
      map_mul' := by
        intro s t
        show Matrix.toLin' ((R (s * t) : SpecialLinearGroup (Fin 4) F4) :
            Matrix (Fin 4) (Fin 4) F4) =
          Matrix.toLin' (R s : Matrix (Fin 4) (Fin 4) F4) *
            Matrix.toLin' (R t : Matrix (Fin 4) (Fin 4) F4)
        rw [map_mul R s t]
        show Matrix.toLin' ((R s : Matrix (Fin 4) (Fin 4) F4) * (R t : Matrix (Fin 4) (Fin 4) F4)) =
          Matrix.toLin' (R s : Matrix (Fin 4) (Fin 4) F4) *
            Matrix.toLin' (R t : Matrix (Fin 4) (Fin 4) F4)
        rw [Matrix.toLin'_mul]
        rfl }
  let Z : Module.End F4 (Fin 4 → F4) := ρ z
  have hρ_inj : Function.Injective ρ := by
    intro s t hst
    apply hR
    exact Subtype.ext ((Matrix.toLinAlgEquiv' (R := F4)).injective hst)
  have hz_ne : z ≠ 1 := by
    intro h
    have hmat : (z : Matrix (Fin 3) (Fin 3) F4) = 1 := congrArg Subtype.val h
    have h00 := congrFun (congrFun hmat 0) 0
    simp [z] at h00
    exact f4Omega_ne_one h00
  have hZne : Z ≠ 1 := by
    intro hZ1
    apply hz_ne
    apply hρ_inj
    rw [show ρ z = (1 : Module.End F4 (Fin 4 → F4)) from hZ1, map_one]
  have hz3 : z ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change (f4Omega • (1 : Matrix (Fin 3) (Fin 3) F4)) ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F4)
    rw [← Algebra.algebraMap_eq_smul_one (A := Matrix (Fin 3) (Fin 3) F4)]
    rw [← map_pow, f4Omega_pow_three, map_one]
  have hZpow : Z ^ 3 = 1 := by
    change (ρ z) ^ 3 = 1
    rw [← map_pow, hz3, map_one]
  have hcommZ : ∀ s, Commute Z (ρ s) := by
    intro s
    have hzs : z * s = s * z := by
      apply Subtype.ext
      show (z : Matrix (Fin 3) (Fin 3) F4) * (s : Matrix (Fin 3) (Fin 3) F4) =
        (s : Matrix (Fin 3) (Fin 3) F4) * (z : Matrix (Fin 3) (Fin 3) F4)
      rw [show (z : Matrix (Fin 3) (Fin 3) F4) = f4Omega • 1 from rfl,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    change ρ z * ρ s = ρ s * ρ z
    rw [← map_mul, hzs, map_mul]
  have hN0bot : Z.eigenspace 0 = ⊥ := by
    rw [Module.End.eigenspace_def, zero_smul, sub_zero, LinearMap.ker_eq_bot']
    intro x hx
    have hunit : ρ (z⁻¹) * Z = 1 := by
      change ρ (z⁻¹) * ρ z = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    calc x = (1 : Module.End F4 (Fin 4 → F4)) x := (Module.End.one_apply x).symm
      _ = (ρ (z⁻¹) * Z) x := by rw [hunit]
      _ = ρ (z⁻¹) (Z x) := rfl
      _ = ρ (z⁻¹) 0 := by rw [hx]
      _ = 0 := map_zero _
  have htop : (⨆ μ : F4, Z.eigenspace μ) = ⊤ := iSup_eigenspace_eq_top_of_pow_three Z hZpow
  let e : Fin 3 → F4 := ![1, f4Omega, f4Omega ^ 2]
  have he_inj : Function.Injective e := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · exact absurd hij (by simpa [e] using f4Omega_ne_one.symm)
      · exact absurd hij (by simpa [e] using f4Omega_sq_ne_one.symm)
    · fin_cases j
      · exact absurd hij.symm (by simpa [e] using f4Omega_ne_one.symm)
      · rfl
      · exact absurd hij (by simpa [e] using f4Omega_sq_ne_omega.symm)
    · fin_cases j
      · exact absurd hij.symm (by simpa [e] using f4Omega_sq_ne_one.symm)
      · exact absurd hij.symm (by simpa [e] using f4Omega_sq_ne_omega.symm)
      · rfl
  let N : Fin 3 → Submodule F4 (Fin 4 → F4) := fun i => Z.eigenspace (e i)
  have hNind : iSupIndep N := by
    have h := (Module.End.eigenspaces_iSupIndep Z).comp he_inj
    simpa [N, Function.comp_def] using h
  have hNtop : (⨆ i : Fin 3, N i) = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = ⨆ μ : F4, Z.eigenspace μ := htop.symm
      _ ≤ ⨆ i : Fin 3, N i := by
          refine iSup_le fun μ => ?_
          rcases f4_cases μ with h | h | h | h
          · rw [h, hN0bot]; exact bot_le
          · rw [h]; exact le_iSup N 0
          · rw [h]; exact le_iSup N 1
          · rw [h]; exact le_iSup N 2
  have hInt3 : DirectSum.IsInternal N :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hNind hNtop
  have hmap : ∀ s i, Set.MapsTo (ρ s) (N i) (N i) := by
    intro s i x hx
    change x ∈ Z.eigenspace (e i) at hx
    change (ρ s) x ∈ Z.eigenspace (e i)
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    calc Z (ρ s x) = (Z * ρ s) x := rfl
      _ = (ρ s * Z) x := by rw [hcommZ s]
      _ = ρ s (Z x) := rfl
      _ = ρ s (e i • x) := by rw [hx]
      _ = e i • ρ s x := (ρ s).map_smul _ _
  let ρi : (i : Fin 3) → SpecialLinearGroup (Fin 3) F4 →* Module.End F4 (N i) := fun i =>
    { toFun := fun s => (ρ s).restrict (hmap s i),
      map_one' := by
        apply LinearMap.ext
        intro x
        simp [Module.End.one_apply, LinearMap.restrict_apply, map_one]
      map_mul' := by
        intro s t
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change ((ρ (s * t)) (x : Fin 4 → F4)) = (ρ s) ((ρ t) (x : Fin 4 → F4))
        rw [map_mul]
        rfl }
  have hfix : ∀ (i : Fin 3) (s : SpecialLinearGroup (Fin 3) F4) (x : Fin 4 → F4),
      x ∈ N i → ρi i s = 1 → ρ s x = x := by
    intro i s x hx hs
    have h2 : (ρi i s) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hs, Module.End.one_apply]
    exact congrArg Subtype.val h2
  let D : Fin 3 → ℕ := fun i => Module.finrank F4 (N i)
  have hsum : D 0 + D 1 + D 2 = 4 := by
    have h := TauCeti.finrank_eq_sum_finrank_of_isInternal hInt3
    rw [Module.finrank_fin_fun, Fin.sum_univ_three] at h
    show Module.finrank F4 (N 0) + Module.finrank F4 (N 1) + Module.finrank F4 (N 2) = 4
    omega
  have hDle : ∀ i, D i ≤ 4 := by
    intro i
    have h1 : Module.finrank F4 ↥(N i) ≤
        Module.finrank F4 ↥(⊤ : Submodule F4 (Fin 4 → F4)) :=
      Submodule.finrank_mono (le_top : N i ≤ ⊤)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  have hsmall : ∀ i : Fin 3, i ≠ 0 → D i ≤ 2 → D i = 0 := by
    intro i hi0 hle
    by_contra hne
    have hNne : N i ≠ ⊥ := by
      intro hbot
      apply hne
      show Module.finrank F4 ↥(N i) = 0
      rw [hbot, finrank_bot]
    obtain ⟨x, hxmem, hxne⟩ := (Submodule.ne_bot_iff (N i)).mp hNne
    have hres := sl3_hom_trivial_of_finrank_le_two (V := N i) hle (ρi i) z
    have hZx : Z x = e i • x := Module.End.mem_eigenspace_iff.mp hxmem
    have hval : Z x = x := hfix i z x hxmem hres
    have hsmul : e i • x = x := by rw [← hZx, hval]
    have hei : e i ≠ 1 := by
      fin_cases i
      · exact (hi0 rfl).elim
      · simpa [e] using f4Omega_ne_one
      · simpa [e] using f4Omega_sq_ne_one
    apply hei
    have h0 : (e i - 1) • x = 0 := by rw [sub_smul, sub_eq_zero]; simpa using hsmul
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hxne)
  have hD1 : D 1 = 0 ∨ D 1 = 3 ∨ D 1 = 4 := by
    by_cases h : D 1 ≤ 2
    · exact Or.inl (hsmall 1 (by decide) h)
    · right
      have hlt : 2 < D 1 := Nat.lt_of_not_le h
      have h4 : D 1 ≤ 4 := hDle 1
      omega
  have hD2 : D 2 = 0 ∨ D 2 = 3 ∨ D 2 = 4 := by
    by_cases h : D 2 ≤ 2
    · exact Or.inl (hsmall 2 (by decide) h)
    · right
      have hlt : 2 < D 2 := Nat.lt_of_not_le h
      have h4 : D 2 ≤ 4 := hDle 2
      omega
  have hDetZ : LinearMap.det Z = 1 := by
    change LinearMap.det (Matrix.toLin' (R z : Matrix (Fin 4) (Fin 4) F4)) = 1
    rw [LinearMap.det_toLin', Matrix.SpecialLinearGroup.det_coe]
  have hne40 : D 1 ≠ 4 := by
    intro h1
    have hNtop1 : N 1 = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      show Module.finrank F4 ↥(N 1) = Module.finrank F4 (Fin 4 → F4)
      rw [Module.finrank_fin_fun]
      exact h1
    have hZω : Z = f4Omega • (1 : Module.End F4 (Fin 4 → F4)) := by
      apply LinearMap.ext
      intro x
      have hx : x ∈ N 1 := by rw [hNtop1]; trivial
      have hx' : x ∈ Z.eigenspace f4Omega := by simpa [N, e] using hx
      have := Module.End.mem_eigenspace_iff.mp hx'
      simpa using this
    have hscalar : LinearMap.det (f4Omega • (1 : Module.End F4 (Fin 4 → F4))) = f4Omega := by
      rw [LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, mul_one, Module.finrank_fin_fun]
      calc f4Omega ^ 4 = f4Omega ^ 3 * f4Omega := by rw [pow_succ]
        _ = f4Omega := by rw [f4Omega_pow_three, one_mul]
    have : f4Omega = 1 := by rw [← hscalar, ← hZω, hDetZ]
    exact f4Omega_ne_one this
  have hne04 : D 2 ≠ 4 := by
    intro h2
    have hNtop2 : N 2 = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      show Module.finrank F4 ↥(N 2) = Module.finrank F4 (Fin 4 → F4)
      rw [Module.finrank_fin_fun]
      exact h2
    have hZω : Z = f4Omega ^ 2 • (1 : Module.End F4 (Fin 4 → F4)) := by
      apply LinearMap.ext
      intro x
      have hx : x ∈ N 2 := by rw [hNtop2]; trivial
      have hx' : x ∈ Z.eigenspace (f4Omega ^ 2) := by simpa [N, e] using hx
      have := Module.End.mem_eigenspace_iff.mp hx'
      simpa using this
    have hscalar : LinearMap.det (f4Omega ^ 2 • (1 : Module.End F4 (Fin 4 → F4))) = f4Omega ^ 2 := by
      rw [LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, mul_one, Module.finrank_fin_fun]
      calc (f4Omega ^ 2) ^ 4 = (f4Omega ^ 2) ^ 3 * f4Omega ^ 2 := by rw [pow_succ]
        _ = f4Omega ^ 2 := by
              rw [show (f4Omega ^ 2) ^ 3 = (f4Omega ^ 3) ^ 2 by rw [← pow_mul, ← pow_mul, mul_comm],
                f4Omega_pow_three, one_pow, one_mul]
    have : f4Omega ^ 2 = 1 := by rw [← hscalar, ← hZω, hDetZ]
    exact f4Omega_sq_ne_one this
  have hne00 : ¬ (D 1 = 0 ∧ D 2 = 0) := by
    rintro ⟨h1, h2⟩
    have hD0 : D 0 = 4 := by omega
    have hNtop0 : N 0 = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      show Module.finrank F4 ↥(N 0) = Module.finrank F4 (Fin 4 → F4)
      rw [Module.finrank_fin_fun]
      exact hD0
    have hZ1 : Z = 1 := by
      apply LinearMap.ext
      intro x
      have hx : x ∈ N 0 := by rw [hNtop0]; trivial
      have hx' : x ∈ Z.eigenspace 1 := by simpa [N, e] using hx
      have := Module.End.mem_eigenspace_iff.mp hx'
      simpa using this
    exact hZne hZ1
  have hcases : (D 1 = 3 ∧ D 2 = 0) ∨ (D 1 = 0 ∧ D 2 = 3) := by
    rcases hD1 with h1 | h1 | h1
    · rcases hD2 with h2 | h2 | h2
      · exact (hne00 ⟨h1, h2⟩).elim
      · exact Or.inr ⟨h1, h2⟩
      · exact (hne04 h2).elim
    · rcases hD2 with h2 | h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · omega
      · omega
    · exact (hne40 h1).elim
  have hD0 : D 0 = 1 := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  obtain ⟨k, hk0, hDk⟩ : ∃ k : Fin 3, k ≠ 0 ∧ D k = 3 := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
  have hDj : ∀ j : Fin 3, j ≠ 0 → j ≠ k → D j = 0 := by
    intro j hj0 hjk
    fin_cases j <;> fin_cases k <;> simp_all <;> omega
  have hres0 : ∀ s, ρi 0 s = 1 := fun s =>
    sl3_hom_trivial_of_finrank_le_two (V := N 0)
      (by change D 0 ≤ 2; rw [hD0]; norm_num) (ρi 0) s
  let W : Submodule F4 (Fin 4 → F4) := N k
  let b : Module.Basis (Fin 3) F4 W := Module.finBasisOfFinrankEq F4 W hDk
  let ρW : SpecialLinearGroup (Fin 3) F4 →* Module.End F4 W := ρi k
  let aMatHom : SpecialLinearGroup (Fin 3) F4 →* Matrix (Fin 3) (Fin 3) F4 :=
    { toFun := fun s => LinearMap.toMatrix b b (ρW s),
      map_one' := by rw [map_one, LinearMap.toMatrix_one],
      map_mul' := by intro s t; rw [map_mul, LinearMap.toMatrix_mul] }
  let dHom : SpecialLinearGroup (Fin 3) F4 →* F4 :=
    { toFun := fun s => LinearMap.det (ρW s),
      map_one' := by rw [map_one, Module.End.one_eq_id, LinearMap.det_id],
      map_mul' := by
        intro s t
        rw [map_mul]
        rw [show ρW s * ρW t = ρW s ∘ₗ ρW t from rfl]
        exact LinearMap.det_comp (ρW s) (ρW t) }
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) F4) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  have hdet : ∀ s, (aMatHom s).det = 1 := by
    intro s
    have h1 : dHom s = 1 := perfect_hom_eq_one hperf dHom s
    have h2 : (aMatHom s).det = dHom s := LinearMap.det_toMatrix b (ρW s)
    rw [h2, h1]
  let a : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 3) F4 :=
    { toFun := fun s => ⟨aMatHom s, hdet s⟩,
      map_one' := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_one]
        exact map_one aMatHom,
      map_mul' := by
        intro s t
        apply Subtype.ext
        show aMatHom (s * t) = aMatHom s * aMatHom t
        exact map_mul aMatHom s t }
  have ha : Function.Injective a := by
    intro s t hst
    have hmat : aMatHom s = aMatHom t := congrArg Subtype.val hst
    have hW : ρW s = ρW t := (LinearMap.toMatrix b b).injective hmat
    have hρ : ρ s = ρ t := by
      have hker : (ρ s - ρ t).ker = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = ⨆ i : Fin 3, N i := hNtop.symm
          _ ≤ (ρ s - ρ t).ker := by
              refine iSup_le fun i => ?_
              intro x hx
              rw [LinearMap.mem_ker]
              by_cases hi0 : i = 0
              · rw [hi0] at hx
                have hxs : ρ s x = x := hfix 0 s x hx (hres0 s)
                have hxt : ρ t x = x := hfix 0 t x hx (hres0 t)
                rw [LinearMap.sub_apply, hxs, hxt, sub_self]
              · by_cases hik : i = k
                · rw [hik] at hx
                  have hxeq : ρ s x = ρ t x := by
                    have h2 : (ρi k s) ⟨x, hx⟩ = (ρi k t) ⟨x, hx⟩ :=
                      congrArg (fun f : Module.End F4 (N k) => f ⟨x, hx⟩) hW
                    exact congrArg Subtype.val h2
                  rw [LinearMap.sub_apply, hxeq, sub_self]
                · have hNj : N i = ⊥ :=
                    (Submodule.finrank_eq_zero (S := N i)).mp (hDj i hi0 hik)
                  rw [hNj] at hx
                  have hx0 : x = 0 := (Submodule.mem_bot F4).mp hx
                  rw [hx0]; simp
      exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hker)
    apply hR
    exact Subtype.ext ((Matrix.toLinAlgEquiv' (R := F4)).injective hρ)
  let α : SpecialLinearGroup (Fin 3) F4 ≃* SpecialLinearGroup (Fin 3) F4 :=
    MulEquiv.ofBijective a ⟨ha, Finite.surjective_of_injective ha⟩
  let C : Submodule F4 (Fin 4 → F4) := N 0
  have hDsum : D 0 + D k = 4 := by
    have hk12 : k = 1 ∨ k = 2 := by
      fin_cases k
      · exact (hk0 rfl).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hk12 with rfl | rfl
    · have h2 : D 2 = 0 := hDj 2 (by decide) (by decide)
      omega
    · have h1 : D 1 = 0 := hDj 1 (by decide) (by decide)
      omega
  have hCW : IsCompl C W := by
    refine (Submodule.isCompl_iff_disjoint C W ?_).mpr ?_
    · rw [Module.finrank_fin_fun]
      have h : Module.finrank F4 C + Module.finrank F4 W = 4 := by
        simpa [C, W, D] using hDsum
      omega
    · have hp : Disjoint (N 0) (N k) :=
        hNind.pairwiseDisjoint (show (0 : Fin 3) ≠ k from fun h => hk0 h.symm)
      simpa [C, W] using hp
  let bC : Module.Basis (Fin 1) F4 C :=
    Module.finBasisOfFinrankEq F4 C (by simpa [C, D] using hD0)
  let eC : C ≃ₗ[F4] F4 :=
    bC.equivFun.trans (LinearEquiv.funUnique (Fin 1) F4 F4)
  let eW : W ≃ₗ[F4] (Fin 3 → F4) := b.equivFun
  let E : (Fin 4 → F4) ≃ₗ[F4] (F4 × (Fin 3 → F4)) :=
    (Submodule.prodEquivOfIsCompl C W hCW).symm.trans (eC.prodCongr eW)
  have hE_add : ∀ (c : C) (w : W),
      E ((c : Fin 4 → F4) + (w : Fin 4 → F4)) = (eC c, eW w) := by
    intro c w
    rw [show (c : Fin 4 → F4) + (w : Fin 4 → F4) =
      Submodule.prodEquivOfIsCompl C W hCW (c, w) from rfl]
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
  have hmat : ∀ (s : SpecialLinearGroup (Fin 3) F4) (w : W),
      eW (ρW s w) = aMatHom s *ᵥ eW w := by
    intro s w
    simpa [eW, aMatHom] using
      (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) (ρW s) w).symm
  have hE : ∀ s v,
      E ((R s : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) =
        ((E v).1, (α s : Matrix (Fin 3) (Fin 3) F4) *ᵥ (E v).2) := by
    intro s v
    let p : C × W := (Submodule.prodEquivOfIsCompl C W hCW).symm v
    let c : C := p.1
    let w : W := p.2
    have hv : v = (c : Fin 4 → F4) + (w : Fin 4 → F4) := by
      have h : Submodule.prodEquivOfIsCompl C W hCW (c, w) = v := by
        simpa [p, c, w] using
          (Submodule.prodEquivOfIsCompl C W hCW).apply_symm_apply v
      rw [Submodule.coe_prodEquivOfIsCompl'] at h
      exact h.symm
    have hc : (ρ s) (c : Fin 4 → F4) = (c : Fin 4 → F4) :=
      hfix 0 s (c : Fin 4 → F4) (by simpa [C] using c.2) (hres0 s)
    have hw : (ρ s) (w : Fin 4 → F4) = ((ρW s w : W) : Fin 4 → F4) := rfl
    have hEv : E v = (eC c, eW w) := by rw [hv, hE_add c w]
    calc
      E ((R s : Matrix (Fin 4) (Fin 4) F4) *ᵥ v)
          = E ((ρ s) v) := by
              change E (Matrix.toLin' (R s : Matrix (Fin 4) (Fin 4) F4) v) =
                E ((ρ s) v)
              rfl
      _ = E ((ρ s) ((c : Fin 4 → F4) + (w : Fin 4 → F4))) := by rw [hv]
      _ = E ((ρ s) (c : Fin 4 → F4) + (ρ s) (w : Fin 4 → F4)) := by rw [map_add]
      _ = E ((c : Fin 4 → F4) + ((ρW s w : W) : Fin 4 → F4)) := by rw [hc, hw]
      _ = (eC c, eW (ρW s w)) := hE_add c (ρW s w)
      _ = (eC c, aMatHom s *ᵥ eW w) := congrArg (fun x => (eC c, x)) (hmat s w)
      _ = ((E v).1, (α s : Matrix (Fin 3) (Fin 3) F4) *ᵥ (E v).2) := by
            rw [hEv]
            change (eC c, aMatHom s *ᵥ eW w) =
              (eC c, (α s : Matrix (Fin 3) (Fin 3) F4) *ᵥ eW w)
            rw [show (α s : Matrix (Fin 3) (Fin 3) F4) = aMatHom s from rfl]
  have htr : ∀ s, Matrix.trace (R s : Matrix (Fin 4) (Fin 4) F4) =
      1 + Matrix.trace (α s : Matrix (Fin 3) (Fin 3) F4) := by
    intro s
    let t : Fin 3 → F4 := fun i => (LinearMap.trace F4 ↥(N i)) ((ρ s).restrict (hmap s i))
    have htrace0 : (LinearMap.trace F4 (Fin 4 → F4)) (ρ s) = t 0 + t 1 + t 2 := by
      rw [LinearMap.trace_eq_sum_trace_restrict hInt3 (f := ρ s) (hmap s)]
      exact Fin.sum_univ_three t
    have htk : t k = (aMatHom s).trace := by
      show (LinearMap.trace F4 ↥(N k)) ((ρ s).restrict (hmap s k)) = (aMatHom s).trace
      rw [show (ρ s).restrict (hmap s k) = ρW s from rfl]
      rw [LinearMap.trace_eq_matrix_trace F4 b (ρW s)]
      rfl
    have ht0 : t 0 = 1 := by
      show (LinearMap.trace F4 ↥(N 0)) ((ρ s).restrict (hmap s 0)) = 1
      rw [show (ρ s).restrict (hmap s 0) = ρi 0 s from rfl, hres0 s, Module.End.one_eq_id,
        LinearMap.trace_id]
      change (D 0 : F4) = 1
      rw [hD0]
      norm_num
    have htj : ∀ j : Fin 3, j ≠ 0 → j ≠ k → t j = 0 := by
      intro j hj0 hjk
      have hNj : N j = ⊥ := (Submodule.finrank_eq_zero (S := N j)).mp (hDj j hj0 hjk)
      haveI : Subsingleton ↥(N j) := by
        rw [hNj]
        exact ⟨fun a b => Subtype.ext (by
          have ha : (a : Fin 4 → F4) = 0 := (Submodule.mem_bot F4).mp a.2
          have hb : (b : Fin 4 → F4) = 0 := (Submodule.mem_bot F4).mp b.2
          rw [ha, hb])⟩
      show (LinearMap.trace F4 ↥(N j)) ((ρ s).restrict (hmap s j)) = 0
      have h0 : (ρ s).restrict (hmap s j) = 0 := Subsingleton.elim _ _
      rw [h0, map_zero]
    have hsumt : t 0 + t 1 + t 2 = 1 + t k := fin3_sum_eq_of_f4 t k hk0 ht0 htj
    have hRtr : Matrix.trace (R s : Matrix (Fin 4) (Fin 4) F4) =
        (LinearMap.trace F4 (Fin 4 → F4)) (ρ s) := by
      rw [← Matrix.trace_toLin'_eq (R s : Matrix (Fin 4) (Fin 4) F4)]
      rfl
    calc Matrix.trace (R s : Matrix (Fin 4) (Fin 4) F4)
        = (LinearMap.trace F4 (Fin 4 → F4)) (ρ s) := hRtr
      _ = t 0 + t 1 + t 2 := htrace0
      _ = 1 + t k := hsumt
      _ = 1 + (aMatHom s).trace := by rw [htk]
      _ = 1 + Matrix.trace (a s : Matrix (Fin 3) (Fin 3) F4) := rfl
      _ = 1 + Matrix.trace (α s : Matrix (Fin 3) (Fin 3) F4) := rfl
  refine ⟨α, E, hE, htr⟩

theorem exists_natural_three_fixed_line
    (R : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4)
    (hR : Function.Injective R) :
    ∃ (α : SpecialLinearGroup (Fin 3) F4 ≃* SpecialLinearGroup (Fin 3) F4)
      (E : (Fin 4 → F4) ≃ₗ[F4] (F4 × (Fin 3 → F4))),
      ∀ s v,
        E ((R s : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) =
          ((E v).1, (α s : Matrix (Fin 3) (Fin 3) F4) *ᵥ (E v).2) := by
  obtain ⟨α, E, hE, _⟩ := exists_natural_three_fixed_line_aux R hR
  exact ⟨α, E, hE⟩

theorem exists_trace_split (R : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4)
    (hR : Function.Injective R) :
    ∃ a : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 3) F4,
      Function.Injective a ∧
        ∀ s, Matrix.trace (R s : Matrix (Fin 4) (Fin 4) F4) =
          1 + Matrix.trace (a s : Matrix (Fin 3) (Fin 3) F4) := by
  obtain ⟨α, _, _, htr⟩ := exists_natural_three_fixed_line_aux R hR
  refine ⟨α.toMonoidHom, ?_, ?_⟩
  · intro s t hst
    simpa using α.injective hst
  · intro s
    simpa using htr s

end CFSG.StandardType.GGHalf

end
