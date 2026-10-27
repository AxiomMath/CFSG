module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement

private theorem k328r1c_eigen_decomp {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {ω : F}
    (h3 : (3 : F) = 1) (hω3 : ω ^ 3 = 1) (hω : ω ^ 2 + ω + 1 = 0)
    (T : Module.End F V) (hT : T ^ 3 = 1) (v : V) :
    ∃ a ∈ T.eigenspace 1, ∃ b ∈ T.eigenspace ω, ∃ c ∈ T.eigenspace (ω ^ 2), v = a + b + c := by
  have hT3 : T (T (T v)) = v := by
    have := LinearMap.congr_fun hT v
    simpa [pow_succ] using this
  refine ⟨v + T v + T (T v), ?_, v + ω ^ 2 • T v + ω • T (T v), ?_,
    v + ω • T v + ω ^ 2 • T (T v), ?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    simp only [map_add, hT3, one_smul]
    abel
  · rw [Module.End.mem_eigenspace_iff]
    simp only [map_add, map_smul, hT3]
    linear_combination (norm := module) -((hω3) • T v)
  · rw [Module.End.mem_eigenspace_iff]
    simp only [map_add, map_smul, hT3]
    linear_combination (norm := module) -((hω3) • T v) - (ω * hω3) • T (T v)
  · linear_combination (norm := module) -((h3) • v) - (hω) • T v - (hω) • T (T v)

private theorem k328r1c_finrank_sum {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {ω : F} (h3 : (3 : F) = 1) (hω3 : ω ^ 3 = 1) (hω : ω ^ 2 + ω + 1 = 0)
    (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1) (hω12 : ω ^ 2 ≠ ω)
    (T : Module.End F V) (hT : T ^ 3 = 1) :
    Module.finrank F (T.eigenspace 1) + Module.finrank F (T.eigenspace ω) +
      Module.finrank F (T.eigenspace (ω ^ 2)) = Module.finrank F V := by
  let S : Fin 3 → Submodule F V := fun i => T.eigenspace (![1, ω, ω ^ 2] i)
  have hinj : Function.Injective (![1, ω, ω ^ 2] : Fin 3 → F) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] at h
         first
          | exact hω1 h.symm
          | exact hω1 h
          | exact hω2 h.symm
          | exact hω2 h
          | exact hω12 h.symm
          | exact hω12 h)
  have hInd : iSupIndep S := (Module.End.eigenspaces_iSupIndep T).comp hinj
  have htop : (⨆ i, S i) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := k328r1c_eigen_decomp h3 hω3 hω T hT v
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_iSup_of_mem 0 ha)
      (Submodule.mem_iSup_of_mem 1 hb)) (Submodule.mem_iSup_of_mem 2 hc)
  have := TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hInd
  rw [htop, finrank_top, Fin.sum_univ_three] at this
  exact this.symm

private theorem k328r1c_hom_trivial {G : Type*} [Group G] {X : Subgroup G} (hperf : ⁅X, X⁆ = X)
    {A : Type*} [CommGroup A] (f : ↥X →* A) (x : ↥X) : f x = 1 := by
  have hle : ⁅X, X⁆ ≤ f.ker.map X.subtype := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    refine Subgroup.mem_map.2 ⟨⁅(⟨a, ha⟩ : ↥X), (⟨b, hb⟩ : ↥X)⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hx : (x : G) ∈ f.ker.map X.subtype := hle (by rw [hperf]; exact x.2)
  obtain ⟨k, hk, hkx⟩ := hx
  have : k = x := Subtype.ext hkx
  rw [← this]
  exact hk

private theorem k328r1c_pow_finrank {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {G : Type*} [Group G] {X : Subgroup G} (hperf : ⁅X, X⁆ = X)
    (ρ : ↥X →* Module.End F V) (t : ↥X) (μ : F) (hcomm : ∀ x, ρ x * ρ t = ρ t * ρ x) :
    μ ^ Module.finrank F ((ρ t).eigenspace μ) = 1 := by
  have hmaps : ∀ x v, v ∈ (ρ t).eigenspace μ → ρ x v ∈ (ρ t).eigenspace μ := by
    intro x v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have := LinearMap.congr_fun (hcomm x) v
    simp only [Module.End.mul_apply] at this
    rw [← this, hv, map_smul]
  let δ : ↥X →* F :=
    { toFun := fun x => LinearMap.det ((ρ x).restrict (fun v hv => hmaps x v hv))
      map_one' := by
        have : (ρ 1).restrict (fun v hv => hmaps 1 v hv) = LinearMap.id := by
          ext v
          simp
        rw [this, LinearMap.det_id]
      map_mul' := fun x y => by
        have : (ρ (x * y)).restrict (fun v hv => hmaps (x * y) v hv) =
            (ρ x).restrict (fun v hv => hmaps x v hv) *
              (ρ y).restrict (fun v hv => hmaps y v hv) := by
          ext v
          simp
        rw [this, map_mul] }
  have hδ : δ t = 1 := by
    have := congrArg Units.val (k328r1c_hom_trivial hperf δ.toHomUnits t)
    simpa using this
  have hres : (ρ t).restrict (fun v hv => hmaps t v hv) = μ • LinearMap.id := by
    ext v
    have := Module.End.mem_eigenspace_iff.1 v.2
    simp [this]
  have : δ t = μ ^ Module.finrank F ((ρ t).eigenspace μ) := by
    show LinearMap.det ((ρ t).restrict (fun v hv => hmaps t v hv)) = _
    rw [hres, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [← this]
  exact hδ

private theorem k328r1c_exists_conj {F : Type} [Field F] {μ : F} (hμ1 : μ ≠ 1)
    (A : Matrix (Fin 4) (Fin 4) F)
    (h3 : Module.finrank F (Module.End.eigenspace (Matrix.toLinAlgEquiv' A) μ) = 3)
    (h1 : 0 < Module.finrank F (Module.End.eigenspace (Matrix.toLinAlgEquiv' A) 1)) :
    ∃ g : Matrix (Fin 4) (Fin 4) F, g.det = 1 ∧ A * g = g * Matrix.diagonal ![μ, μ, μ, 1] := by
  set T : Module.End F (Fin 4 → F) := Matrix.toLinAlgEquiv' A with hT
  let b := Module.finBasisOfFinrankEq F (T.eigenspace μ) h3
  obtain ⟨w', hw'⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h1
  have hw1 : T (w' : Fin 4 → F) = (w' : Fin 4 → F) := by
    simpa using Module.End.mem_eigenspace_iff.1 w'.2
  have hw0 : (w' : Fin 4 → F) ≠ 0 := fun h => hw' (Subtype.ext h)
  let c : Fin 4 → (Fin 4 → F) :=
    Fin.snoc (α := fun _ => Fin 4 → F) (fun i : Fin 3 => ((b i : ↥(T.eigenspace μ)) : Fin 4 → F))
      (w' : Fin 4 → F)
  have hind : LinearIndependent F c := by
    refine linearIndependent_fin_snoc.2 ⟨?_, ?_⟩
    · exact b.linearIndependent.map' (T.eigenspace μ).subtype (Submodule.ker_subtype _)
    · intro hmem
      have hmem' : (w' : Fin 4 → F) ∈ T.eigenspace μ :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (b i).2) hmem
      have h := Module.End.mem_eigenspace_iff.1 hmem'
      rw [hw1] at h
      have : (μ - 1) • (w' : Fin 4 → F) = 0 := by
        rw [sub_smul, ← h, one_smul, sub_self]
      exact hw0 ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hμ1))
  let B : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => c j i
  have hunit : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.1 hind
  have hdet : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).1 hunit).ne_zero
  have hd : ∀ j' : Fin 3, (![μ, μ, μ, 1] : Fin 4 → F) (Fin.castSucc j') = μ := fun j' => by
    fin_cases j' <;> rfl
  have hl : (![μ, μ, μ, 1] : Fin 4 → F) (Fin.last 3) = 1 := rfl
  have hc : ∀ j, T (c j) = (![μ, μ, μ, 1] : Fin 4 → F) j • c j := by
    intro j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [hl, one_smul]
      simpa only [c, Fin.snoc_last] using hw1
    · rw [hd j']
      have hmem := Module.End.mem_eigenspace_iff.1 (b j').2
      simpa only [c, Fin.snoc_castSucc] using hmem
  have hAB : A * B = B * Matrix.diagonal ![μ, μ, μ, 1] := by
    ext i j
    have := congrFun (hc j) i
    rw [hT, Matrix.toLinAlgEquiv'_apply] at this
    rw [Matrix.mul_diagonal]
    simpa [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  refine ⟨B * Matrix.diagonal ![1, 1, 1, (B.det)⁻¹], ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [hdet]
  · rw [← Matrix.mul_assoc, hAB, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _

private theorem k328r1c_field_facts {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (3 : F) = 1 ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ 1 ∧ ω ^ 2 ≠ ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hω1 : ω ≠ 1 := by
    rintro rfl
    exact one_ne_zero (by linear_combination hω - h2)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  refine ⟨by linear_combination h2, hω3, hω1, ?_, ?_⟩
  · intro h
    exact hω1 (by linear_combination hω3 - ω * h)
  · intro h
    exact one_ne_zero (by linear_combination hω - h - ω * h2)

private theorem k328r1c_exists_gl {F : Type} [Field F] (M : Matrix (Fin 4) (Fin 4) F)
    (h : M.det = 1) : ∃ g : GL (Fin 4) F, (g : Matrix (Fin 4) (Fin 4) F) = M :=
  ⟨((Matrix.isUnit_iff_isUnit_det M).2 (by rw [h]; exact isUnit_one)).unit, IsUnit.unit_spec _⟩

private theorem k328r1c_conj_of_comm {F : Type} [Field F] {z w : GL (Fin 4) F}
    {g : Matrix (Fin 4) (Fin 4) F} (hdet : g.det = 1)
    (h : (z : Matrix (Fin 4) (Fin 4) F) * g = g * (w : Matrix (Fin 4) (Fin 4) F)) :
    ∃ g' ∈ StatedSL 4 F, g' * z * g'⁻¹ = w := by
  obtain ⟨u, hu⟩ := k328r1c_exists_gl g hdet
  refine ⟨u⁻¹, Subgroup.inv_mem _
    (CFSG.Open.StatedAPI.mem_statedSL_of_det (by rw [hu]; exact hdet)), ?_⟩
  have h' : z * u = u * w := Units.ext (by simpa [hu] using h)
  rw [inv_inv, mul_assoc, h', ← mul_assoc, inv_mul_cancel, one_mul]

private theorem k328r1c_diag_inv {F : Type} [Field F] {ω : F} (hω3 : ω ^ 3 = 1)
    {z₀ : GL (Fin 4) F}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    ((z₀⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![ω ^ 2, ω ^ 2, ω ^ 2, 1] := by
  have h1 : (z₀ : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal ![ω ^ 2, ω ^ 2, ω ^ 2, 1] = 1 := by
    rw [hz, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
    all_goals linear_combination hω3
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_right_inv h1

theorem row1_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    ClassLeaf (StatedSL 4 F) z₀ := by
  have _ := ht
  intro z hzH hz3 X hXH hzX hXC hperf
  obtain ⟨h3, hω3, hω1, hω2, hω12⟩ := k328r1c_field_facts hF hω
  have hzcube : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
  set T : Module.End F (Fin 4 → F) := Matrix.toLinAlgEquiv' (z : Matrix (Fin 4) (Fin 4) F)
    with hT
  have hT3 : T ^ 3 = 1 := by
    rw [hT, ← map_pow, ← Units.val_pow_eq_pow_val, hzcube, Units.val_one, map_one]
  have hsum := k328r1c_finrank_sum h3 hω3 hω hω1 hω2 hω12 T hT3
  rw [Module.finrank_fin_fun] at hsum
  let ρ : ↥X →* Module.End F (Fin 4 → F) :=
    { toFun := fun x => Matrix.toLinAlgEquiv' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hcomm : ∀ x : ↥X, ρ x * ρ ⟨z, hzX⟩ = ρ ⟨z, hzX⟩ * ρ x := by
    intro x
    have h : (x : GL (Fin 4) F) * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 (hXC x.2)
    show Matrix.toLinAlgEquiv' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        Matrix.toLinAlgEquiv' (z : Matrix (Fin 4) (Fin 4) F) =
      Matrix.toLinAlgEquiv' (z : Matrix (Fin 4) (Fin 4) F) *
        Matrix.toLinAlgEquiv' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, h]
  have hρt : ρ ⟨z, hzX⟩ = T := rfl
  have hpω := k328r1c_pow_finrank hperf ρ ⟨z, hzX⟩ ω hcomm
  have hpω2 := k328r1c_pow_finrank hperf ρ ⟨z, hzX⟩ (ω ^ 2) hcomm
  rw [hρt] at hpω hpω2
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hord2 : orderOf (ω ^ 2) = 3 :=
    orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]) hω2
  have hd1 : 3 ∣ Module.finrank F (T.eigenspace ω) := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.2 hpω
  have hd2 : 3 ∣ Module.finrank F (T.eigenspace (ω ^ 2)) := by
    rw [← hord2]
    exact orderOf_dvd_iff_pow_eq_one.2 hpω2
  have hcases : (Module.finrank F (T.eigenspace ω) = 3 ∧ Module.finrank F (T.eigenspace 1) = 1) ∨
      (Module.finrank F (T.eigenspace (ω ^ 2)) = 3 ∧ Module.finrank F (T.eigenspace 1) = 1) ∨
      Module.finrank F (T.eigenspace 1) = 4 := by omega
  rcases hcases with ⟨h3', h1'⟩ | ⟨h3', h1'⟩ | h4
  · obtain ⟨g, hdet, hg⟩ := k328r1c_exists_conj hω1 (z : Matrix (Fin 4) (Fin 4) F) h3'
      (by rw [h1']; norm_num)
    obtain ⟨g', hg', hgz⟩ :=
      k328r1c_conj_of_comm (z := z) (w := z₀) hdet (by rw [hz]; exact hg)
    exact ⟨g', hg', Or.inl hgz⟩
  · obtain ⟨g, hdet, hg⟩ := k328r1c_exists_conj hω2 (z : Matrix (Fin 4) (Fin 4) F) h3'
      (by rw [h1']; norm_num)
    obtain ⟨g', hg', hgz⟩ := k328r1c_conj_of_comm (z := z) (w := z₀⁻¹) hdet
      (by rw [k328r1c_diag_inv hω3 hz]; exact hg)
    exact ⟨g', hg', Or.inr hgz⟩
  · exfalso
    have htop : T.eigenspace 1 = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h4, Module.finrank_fin_fun])
    have hT1 : T = 1 := LinearMap.ext fun v => by
      have := Module.End.mem_eigenspace_iff.1 (htop ▸ Submodule.mem_top : v ∈ T.eigenspace 1)
      simpa using this
    have hz1 : (z : Matrix (Fin 4) (Fin 4) F) = 1 :=
      Matrix.toLinAlgEquiv'.injective (by rw [← hT, hT1, map_one])
    have : z = 1 := Units.ext (by rw [hz1, Units.val_one])
    rw [this, orderOf_one] at hz3
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
