module

public import CFSG.Monster.Existence.EbCase1
public import CFSG.Monster.Existence.ELevelOrder4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

theorem eb_conj_sq {G : Type*} [Group G] {E T : G} (h : E * E = 1) :
    T * E * T⁻¹ * (T * E * T⁻¹) = 1 := by
  calc T * E * T⁻¹ * (T * E * T⁻¹) = T * (E * E) * T⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem eb_conj_to_rep {G : Type*} [Group G] {E T u H K : G} (hK : T * E * T⁻¹ = K)
    (hu : K = u⁻¹ * H * u) : u * T * E * (u * T)⁻¹ = H := by
  calc u * T * E * (u * T)⁻¹ = u * (T * E * T⁻¹) * u⁻¹ := by group
    _ = H := by rw [hK, hu]; group

theorem eb_conj_prod_sq {G : Type*} [Group G] {E T R : G} (hEE : E * E = 1) (hRR : R * R = 1)
    (hER : E * R = R * E) : T * (E * R) * T⁻¹ * (T * (E * R) * T⁻¹) = 1 := by
  have hsq : E * R * (E * R) = 1 := by
    calc E * R * (E * R) = E * (R * E) * R := by simp only [mul_assoc]
      _ = E * (E * R) * R := by rw [← hER]
      _ = (E * E) * (R * R) := by simp only [mul_assoc]
      _ = 1 := by rw [hEE, hRR, mul_one]
  calc T * (E * R) * T⁻¹ * (T * (E * R) * T⁻¹) = T * (E * R * (E * R)) * T⁻¹ := by group
    _ = 1 := by rw [hsq]; group

@[expose] noncomputable def visGriess : Gvis →* MGriess := Subgroup.inclusion Gvis_le_AutO

@[simp] theorem coe_visGriess (f : Gvis) :
    ((visGriess f : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) = (f : SpaceB ≃ₗ[ℚ] SpaceB) := rfl

theorem visGriess_rhoGvis (r : Q) : visGriess (rhoGvis r) = rhoGriess r := rfl

theorem visGriess_injective : Function.Injective visGriess :=
  Subgroup.inclusion_injective Gvis_le_AutO

theorem isConj_xGriess_visGriess {f : Gvis}
    (h : ∃ g ∈ Gmat, g * xmat * g⁻¹ = (f : SpaceB ≃ₗ[ℚ] SpaceB)) :
    IsConj xGriess (visGriess f) := by
  obtain ⟨g, hg, hgf⟩ := h
  exact isConj_iff.2 ⟨⟨g, Gmat_le_AutO hg⟩, Subtype.ext hgf⟩

theorem isConj_xGriess_conj_iff (T X : Gvis) :
    IsConj xGriess (visGriess (T * X * T⁻¹)) ↔ IsConj xGriess (visGriess X) :=
  ⟨fun h => h.trans (visGriess.map_isConj (isConj_iff.2 ⟨T⁻¹, by group⟩)),
    fun h => h.trans (visGriess.map_isConj (isConj_iff.2 ⟨T, rfl⟩))⟩

structure CosetTwoBCensus : Prop where
  one : ∀ f ∈ cosetInv 1, f ∉ qmatClass (classRep 0) →
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = (f : SpaceB ≃ₗ[ℚ] SpaceB)
  two : ∀ f ∈ cosetInv 2, ∃ g ∈ Gmat, g * xmat * g⁻¹ = (f : SpaceB ≃ₗ[ℚ] SpaceB)

theorem eb_classRep_zero :
    classRep 0 = cosetRep 1 := by
  rw [classRep, cosetElt, classEnc_zero]
  have h : qOfEnc 0 = 1 := by
    rw [qOfEnc, show pauliDec 0 = (false, 0, 0) from rfl]
    exact pauliQ_false_zero
  rw [h, rhoGvis_one, mul_one]

theorem thetaVis_conj_rhoGvis (δ : Pvis) (c : Q) :
    thetaVis δ * rhoGvis c * (thetaVis δ)⁻¹ = rhoGvis (conjQ δ c) :=
  Subtype.ext (Visible.thetaEquiv_conj_rhoEquiv δ c)

theorem rhoGvis_mul_self {c : Q} (h : c * c = 1) : rhoGvis c * rhoGvis c = 1 := by
  rw [← rhoGvis_mul, h, rhoGvis_one]

theorem eb_key_class_zero
    (hcen : CosetTwoBCensus) {E : Gvis} (hEE : E * E = 1) {δ : Pvis}
    (hδ : thetaVis δ * E * (thetaVis δ)⁻¹ = cosetRep 1)
    (hEt : E * rhoGvis rStar = rhoGvis rStar * E) (hEu : E * rhoGvis rTwo = rhoGvis rTwo * E) :
    ∃ c : Q, (c = rStar ∨ c = rTwo ∨ c = rOneTwo) ∧
      IsConj xGriess (visGriess (E * rhoGvis c)) := by
  have hEo : E * rhoGvis rOneTwo = rhoGvis rOneTwo * E := by
    rw [← rStar_mul_rTwo, rhoGvis_mul]
    exact (Commute.mul_right (show Commute E (rhoGvis rTwo) from hEu)
      (show Commute E (rhoGvis rStar) from hEt)).eq
  have key : ∀ c : Q, c * c = 1 → E * rhoGvis c = rhoGvis c * E →
      thetaVis δ * (E * rhoGvis c) * (thetaVis δ)⁻¹ = cosetRep 1 * rhoGvis (conjQ δ c) ∧
      cosetRep 1 * rhoGvis (conjQ δ c) ∈ cosetInv 1 := by
    intro c hcc hEc
    have hZ : thetaVis δ * (E * rhoGvis c) * (thetaVis δ)⁻¹ =
        cosetRep 1 * rhoGvis (conjQ δ c) := by
      rw [← thetaVis_conj_rhoGvis, ← hδ]
      group
    refine ⟨hZ, (mem_cosetR_iff_exists 1 _).2 ⟨conjQ δ c, rfl⟩, ?_⟩
    rw [← hZ]
    exact eb_conj_prod_sq (G := Gvis) hEE (rhoGvis_mul_self hcc) hEc
  obtain ⟨hZt, hIt⟩ := key rStar eb_rStar_mul_self hEt
  obtain ⟨hZu, hIu⟩ := key rTwo eb_rTwo_mul_self hEu
  obtain ⟨hZo, hIo⟩ := key rOneTwo eb_rOneTwo_mul_self hEo
  have conj : ∀ c : Q, thetaVis δ * (E * rhoGvis c) * (thetaVis δ)⁻¹ =
      cosetRep 1 * rhoGvis (conjQ δ c) → cosetRep 1 * rhoGvis (conjQ δ c) ∈ cosetInv 1 →
      cosetRep 1 * rhoGvis (conjQ δ c) ∉ qmatClass (classRep 0) →
      IsConj xGriess (visGriess (E * rhoGvis c)) := by
    intro c hZ hI hcl
    rw [← isConj_xGriess_conj_iff (thetaVis δ), hZ]
    exact isConj_xGriess_visGriess (hcen.one _ hI hcl)
  by_cases h1 : cosetRep 1 * rhoGvis (conjQ δ rStar) ∈ qmatClass (classRep 0)
  · by_cases h2 : cosetRep 1 * rhoGvis (conjQ δ rTwo) ∈ qmatClass (classRep 0)
    · by_cases h3 : cosetRep 1 * rhoGvis (conjQ δ rOneTwo) ∈ qmatClass (classRep 0)
      · exfalso
        have hab : conjQ δ rOneTwo = conjQ δ rStar * conjQ δ rTwo := by
          rw [← rStar_mul_rTwo, map_mul]
        have hs3 : IsShortCoord (coordOf (conjQ δ rStar * conjQ δ rTwo)) := by
          rw [← hab]
          exact isShortCoord_conjQ δ isShortCoord_rOneTwo
        rw [hab] at h3
        exact class0_sound class0OK_eq_true (isShortCoord_conjQ δ isShortCoord_rStar)
          (isShortCoord_conjQ δ isShortCoord_rTwo) hs3 h1 h2 h3
      · exact ⟨rOneTwo, Or.inr (Or.inr rfl), conj _ hZo hIo h3⟩
    · exact ⟨rTwo, Or.inr (Or.inl rfl), conj _ hZu hIu h2⟩
  · exact ⟨rStar, Or.inl rfl, conj _ hZt hIt h1⟩

theorem cosetInv_six_eq_empty :
    cosetInv 6 = ∅ :=
  (Set.ncard_eq_zero (cosetInv_finite (Or.inr (Or.inr rfl)))).1 ncard_cosetInv_six

theorem eb_case_two
    (hcen : CosetTwoBCensus) {e : MGriess}
    (he : e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
      Subgroup.centralizer ({xGriess} : Set MGriess))
    (hee : e * e = 1)
    (hπ : piVis ⟨(e : SpaceB ≃ₗ[ℚ] SpaceB), mem_Gvis_of_mem_cent_xGriess he.2⟩ ≠ 1) :
    ∃ f ∈ FE, IsConj xGriess (e * f) := by
  have hKG := mem_Gvis_of_mem_cent_xGriess he.2
  set E : Gvis := ⟨(e : SpaceB ≃ₗ[ℚ] SpaceB), hKG⟩ with hE
  have hEe : visGriess E = e := rfl
  have hEE : E * E = 1 :=
    visGriess_injective (by rw [map_mul, hEe, map_one]; exact hee)
  have hKK : (E : SpaceB ≃ₗ[ℚ] SpaceB) * E = rhoEquiv 1 := by
    rw [Short.rhoEquiv_one]
    exact congrArg Subtype.val hEE
  obtain ⟨i, hi, δ, q, hK⟩ := exists_conj_mem_cosetR hKG hπ hKK
  have hKp : thetaVis δ * E * (thetaVis δ)⁻¹ = cosetRep i * rhoGvis q := Subtype.ext hK
  have hKinv : cosetRep i * rhoGvis q ∈ cosetInv i := by
    refine ⟨(mem_cosetR_iff_exists i _).2 ⟨q, rfl⟩, ?_⟩
    rw [← hKp]
    exact eb_conj_sq (G := Gvis) hEE
  have viaConj : (∃ g ∈ Gmat, g * xmat * g⁻¹ =
      ((cosetRep i * rhoGvis q : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) →
      ∃ f ∈ FE, IsConj xGriess (e * f) := by
    intro h
    refine ⟨1, FE.one_mem, ?_⟩
    rw [mul_one, ← hEe, ← isConj_xGriess_conj_iff (thetaVis δ), hKp]
    exact isConj_xGriess_visGriess h
  rcases hi with rfl | rfl | rfl
  · by_cases hcl : cosetRep 1 * rhoGvis q ∈ qmatClass (classRep 0)
    · obtain ⟨u, hu, hu'⟩ := hcl
      obtain ⟨w, rfl⟩ := (mem_rhoQ_subgroupOf_iff u).1 hu
      have hδ : thetaVis (δ * rhoPair w) * E * (thetaVis (δ * rhoPair w))⁻¹ = cosetRep 1 := by
        rw [thetaVis_mul]
        exact eb_conj_to_rep (G := Gvis) (u := rhoGvis w) hKp (hu'.trans (by rw [eb_classRep_zero]))
      have hEt : E * rhoGvis rStar = rhoGvis rStar * E := by
        have h := Subgroup.mem_centralizer_iff.1 he.1 tGriess (mem_FE.2 (Or.inr (Or.inl rfl)))
        exact visGriess_injective (by
          simp only [map_mul, hEe, visGriess_rhoGvis, rhoGriess_rStar]
          exact h.symm)
      have hEu : E * rhoGvis rTwo = rhoGvis rTwo * E := by
        have h := Subgroup.mem_centralizer_iff.1 he.1 uGriess
          (mem_FE.2 (Or.inr (Or.inr (Or.inl rfl))))
        exact visGriess_injective (by
          simp only [map_mul, hEe, visGriess_rhoGvis, rhoGriess_rTwo]
          exact h.symm)
      obtain ⟨c, hc, hconj⟩ := eb_key_class_zero hcen hEE hδ hEt hEu
      refine ⟨rhoGriess c, eb_rhoGriess_mem_FE_iff.2 (Or.inr hc), ?_⟩
      rwa [map_mul, hEe, visGriess_rhoGvis] at hconj
    · exact viaConj (hcen.one _ hKinv hcl)
  · exact viaConj (hcen.two _ hKinv)
  · rw [cosetInv_six_eq_empty] at hKinv
    exact absurd hKinv (Set.notMem_empty _)

end CFSG.Monster.Existence
