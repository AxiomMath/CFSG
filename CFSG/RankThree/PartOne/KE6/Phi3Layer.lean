module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenProduct
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix Pointwise

variable {Ω : Type} [Field Ω]

theorem thetaQ_conj_mem {θ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω} {S : Set (Fin Tag.E6.rank → ℤ)}
    {y u : ModGL Tag.E6 Ω}
    (hy : y ∈ Subgroup.normalizer (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)))
    (hyR : y ∈ θ.eqLocus (MonoidHom.id _))
    (hu : u ∈ rootSpan Tag.E6 Ω S ⊓ θ.eqLocus (MonoidHom.id _)) :
    y * u * y⁻¹ ∈ rootSpan Tag.E6 Ω S ⊓ θ.eqLocus (MonoidHom.id _) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hy u).1 hu.1, ?_⟩
  have hy' : θ y = y := hyR
  have hu' : θ u = u := hu.2
  change θ (y * u * y⁻¹) = y * u * y⁻¹
  rw [map_mul, map_mul, map_inv, hy', hu']

theorem torusGroup_sup_rootSpan_le_normalizer' {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) :
    torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) :=
  sup_le (torusGroup_le_normalizer_rootSpan hS) Subgroup.le_normalizer

theorem hPcent_of_std {w : WeylGroup Tag.E6} {S : Set (Fin Tag.E6.rank → ℤ)}
    {J : Set (Fin Tag.E6.rank)} (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J)
    {P : Subgroup (ModGL Tag.E6 Ω)}
    (hP : e6Commutant (P.map (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
        Set (ModGL Tag.E6 Ω)) = e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω))) :
    ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, (∀ u ∈ P, y * u = u * y) →
      y ∈ torusGroup Tag.E6 Ω ∧
        y ∈ Subgroup.centralizer (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) := by
  classical
  intro y hy hc
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hnN := canonicalRep_mem_normalizer (R := Ω) (τ := Tag.E6) w
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup Tag.E6 Ω)
    (rootSpan Tag.E6 Ω S) (torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
      (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) := by
    rw [← hmul]
    exact hy
  obtain ⟨h, hh, z, hz, rfl⟩ := hy'
  have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
  have hz' : n * z * n⁻¹ ∈ subsystemGroup Tag.E6 Ω J := by
    rw [← hQ]
    exact ⟨z, hz, rfl⟩
  have hc' : ∀ x ∈ P.map (MulAut.conj n).toMonoidHom,
      (n * h * n⁻¹) * (n * z * n⁻¹) * x = x * ((n * h * n⁻¹) * (n * z * n⁻¹)) := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hc u hu
    calc (n * h * n⁻¹) * (n * z * n⁻¹) * (MulAut.conj n).toMonoidHom u =
        n * (h * z * u) * n⁻¹ := by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
      _ = n * (u * (h * z)) * n⁻¹ := by rw [h1]
      _ = (MulAut.conj n).toMonoidHom u * ((n * h * n⁻¹) * (n * z * n⁻¹)) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have htor := CFSG.RankThree.Lattice.mem_torusGroup_of_commute_of_e6Commutant_eq hP hh' hz'
    (fun x hx => hc' x hx)
  have hX : (((n * h * n⁻¹) * (n * z * n⁻¹) : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) ∈ e6Commutant
        (P.map (MulAut.conj n).toMonoidHom : Set (ModGL Tag.E6 Ω)) :=
    fun x hx => (CFSG.RankThree.Lattice.commute_val_of_mul_eq (hc' x hx))
  rw [hP] at hX
  have hnorm : ∀ g : ModGL Tag.E6 Ω, g ∈ torusGroup Tag.E6 Ω →
      n⁻¹ * g * n ∈ torusGroup Tag.E6 Ω := fun g hg => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) g).1 hg
    simpa using this
  refine ⟨?_, ?_⟩
  · have := hnorm _ htor
    have e : n⁻¹ * ((n * h * n⁻¹) * (n * z * n⁻¹)) * n = h * z := by group
    rwa [e] at this
  · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    have hgJ : n * g * n⁻¹ ∈ subsystemGroup Tag.E6 Ω J := by
      rw [← hQ]
      exact ⟨g, hg, rfl⟩
    have h2 := CFSG.RankThree.Lattice.mul_eq_of_commute_val (hX _ hgJ)
    have e1 : g * (h * z) = n⁻¹ * ((n * g * n⁻¹) * ((n * h * n⁻¹) * (n * z * n⁻¹))) * n := by
      group
    have e2 : h * z * g = n⁻¹ * (((n * h * n⁻¹) * (n * z * n⁻¹)) * (n * g * n⁻¹)) * n := by
      group
    rw [e1, e2, h2]

theorem mem_normalizer_of_conj {n y : ModGL Tag.E6 Ω} {A B : Subgroup (ModGL Tag.E6 Ω)}
    (hAB : A.map (MulAut.conj n).toMonoidHom = B)
    (hy : n * y * n⁻¹ ∈ Subgroup.normalizer (B : Set (ModGL Tag.E6 Ω))) :
    y ∈ Subgroup.normalizer (A : Set (ModGL Tag.E6 Ω)) := by
  have hmem : ∀ x : ModGL Tag.E6 Ω, x ∈ A ↔ n * x * n⁻¹ ∈ B := fun x => by
    rw [← hAB]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx⟩
      have h : x' = x := by
        have h1 : n * x' * n⁻¹ = n * x * n⁻¹ := hxx
        exact mul_left_cancel (mul_right_cancel h1)
      rw [← h]
      exact hx'
  refine Subgroup.mem_normalizer_iff.2 fun h => ?_
  have e : n * (y * h * y⁻¹) * n⁻¹ = (n * y * n⁻¹) * (n * h * n⁻¹) * (n * y * n⁻¹)⁻¹ := by group
  rw [hmem h, hmem (y * h * y⁻¹), e]
  exact Subgroup.mem_normalizer_iff.1 hy (n * h * n⁻¹)

theorem smul_mem_parabolicRoots_of_lget {T : WeylGroup Tag.E6} {L : List (List ℤ)}
    (hLT : weylMatrix T = CFSG.RankThree.Lattice.toMat Tag.E6.rank L)
    {J J' : Set (Fin Tag.E6.rank)}
    (hcol : ∀ j ∈ J, ∀ i ∉ J', CFSG.RankThree.Lattice.lget L i j = 0) {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ parabolicRoots Tag.E6 J) : T • β ∈ parabolicRoots Tag.E6 J' := by
  refine ⟨IsRoot.smul hβ.1 T, fun i hi => ?_⟩
  rw [← weylMatrix_mulVec, hLT, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ J
  · have : CFSG.RankThree.Lattice.toMat Tag.E6.rank L i j = 0 := hcol j hj i hi
    rw [this, zero_mul]
  · rw [hβ.2 j hj, mul_zero]

theorem torus_sup_subsystemGroup_le_normalizer {J₁ J₂ : Set (Fin Tag.E6.rank)}
    (h₂₁ : CFSG.RankThree.Lattice.IsSeparated J₂ J₁) :
    torusGroup Tag.E6 Ω ⊔ subsystemGroup Tag.E6 Ω (J₁ ∪ J₂) ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 Ω J₁ : Set (ModGL Tag.E6 Ω)) := by
  refine sup_le ?_ ?_
  · rw [subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  · refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, hi, c, hg | hg⟩
    · by_cases hi₁ : i ∈ J₁
      · rw [hg]
        exact Subgroup.le_normalizer (xUnit_mem_subsystemGroup hi₁ c)
      · have hi₂ : i ∈ J₂ := hi.resolve_left hi₁
        have hcent : g ∈ Subgroup.centralizer (subsystemGroup Tag.E6 Ω J₁ : Set (ModGL Tag.E6 Ω)) :=
          Subgroup.mem_centralizer_iff.2 fun h hh => by
            rw [hg]
            exact (CFSG.RankThree.Lattice.commute_of_isSeparated h₂₁
              (xUnit_mem_subsystemGroup hi₂ c) hh).symm.eq
        exact Subgroup.centralizer_le_normalizer _ hcent
    · by_cases hi₁ : i ∈ J₁
      · rw [hg]
        exact Subgroup.le_normalizer (yUnit_mem_subsystemGroup hi₁ c)
      · have hi₂ : i ∈ J₂ := hi.resolve_left hi₁
        have hcent : g ∈ Subgroup.centralizer (subsystemGroup Tag.E6 Ω J₁ : Set (ModGL Tag.E6 Ω)) :=
          Subgroup.mem_centralizer_iff.2 fun h hh => by
            rw [hg]
            exact (CFSG.RankThree.Lattice.commute_of_isSeparated h₂₁
              (yUnit_mem_subsystemGroup hi₂ c) hh).symm.eq
        exact Subgroup.centralizer_le_normalizer _ hcent

theorem conj_mem_torus_sup {w : WeylGroup Tag.E6} {S : Set (Fin Tag.E6.rank → ℤ)}
    {J : Set (Fin Tag.E6.rank)} (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J) {y : ModGL Tag.E6 Ω}
    (hy : y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S) :
    canonicalRep (coxeterSystem Tag.E6) Ω w * y * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∈
      torusGroup Tag.E6 Ω ⊔ subsystemGroup Tag.E6 Ω J := by
  have hnN := canonicalRep_mem_normalizer (R := Ω) (τ := Tag.E6) w
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup Tag.E6 Ω)
    (rootSpan Tag.E6 Ω S) (torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
      (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) := by
    rw [← hmul]
    exact hy
  obtain ⟨h, hh, z, hz, rfl⟩ := hy'
  have hh' : canonicalRep (coxeterSystem Tag.E6) Ω w * h *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∈ torusGroup Tag.E6 Ω :=
    (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
  have hz' : canonicalRep (coxeterSystem Tag.E6) Ω w * z *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∈ subsystemGroup Tag.E6 Ω J := by
    rw [← hQ]
    exact ⟨z, hz, rfl⟩
  have e : canonicalRep (coxeterSystem Tag.E6) Ω w * (h * z) *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ =
      (canonicalRep (coxeterSystem Tag.E6) Ω w * h * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) Ω w * z *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right hz')

end CFSG.RankThree.PartOne.KE6
