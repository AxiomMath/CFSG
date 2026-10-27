module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxModels
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210a

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G : Subgroup Γ}

theorem SemisimpleAction.conj_mem_mOf
    [Finite Γ] (h : SemisimpleAction p A G) {g : Γ}
    (hgG : g ∈ Subgroup.normalizer (G : Set Γ)) (hgA : g ∈ Subgroup.centralizer (A : Set Γ))
    {x : Γ} (hx : x ∈ mOf A G) : g * x * g⁻¹ ∈ mOf A G := by
  obtain ⟨⟨hMG, hDM, hMsol⟩, hgreat⟩ := thm210b h
  have hMG' : mOf A G ≤ G := hMG
  have hconj : ∀ y ∈ G, g * y * g⁻¹ ∈ G := fun y hy => (Subgroup.mem_normalizer_iff.mp hgG y).mp hy
  have hXG : (mOf A G).map (MulAut.conj g).toMonoidHom ≤ G := by
    rintro _ ⟨m, hm, rfl⟩
    exact hconj m (hMG' hm)
  have hcen : cenIn G A ≤ (mOf A G).map (MulAut.conj g).toMonoidHom := by
    intro y hy
    obtain ⟨hyG, hyC⟩ := Subgroup.mem_inf.mp hy
    have hg' : g⁻¹ * y * g ∈ G := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgG) y).mp hyG
      simpa using this
    refine ⟨g⁻¹ * y * g, hDM (Subgroup.mem_inf.mpr ⟨hg', Subgroup.mem_centralizer_iff.mpr
      fun a ha => ?_⟩), by simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 : Commute a g := Subgroup.mem_centralizer_iff.mp hgA a ha
    have h2 : Commute a y := Subgroup.mem_centralizer_iff.mp hyC a ha
    exact ((h1.inv_right.mul_right h2).mul_right h1).eq
  have : Group.IsSolvable ((mOf A G).map (MulAut.conj g).toMonoidHom) := by
    have := hMsol
    exact Group.isSolvable_of_surjective
      (f := ((mOf A G).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom) ((mOf A G).equivMapOfInjective
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).surjective
  exact hgreat ⟨hXG, hcen, this⟩ ⟨x, hx, rfl⟩

theorem index_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (H : ∀ i, Subgroup (β i)) : (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem coord_eq_equiv_symm [Finite Γ] {S : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) (x : ↥K) :
    hK.coord hJ x = hK.equiv.symm x ⟨J, hJ⟩ := by
  have := hK.coord_equiv hJ (hK.equiv.symm x)
  rwa [MulEquiv.apply_symm_apply] at this

theorem SemisimpleAction.relIndex_mOf
    [Finite Γ] (h : SemisimpleAction p A G) [Fintype ↥(lcal G)] :
    (mOf A G).relIndex G = ∏ J : ↥(lcal G), (kJ A (J : Subgroup Γ)).relIndex (J : Subgroup Γ) := by
  classical
  have hDP := h.isDirectProduct_lcal
  have hset : (mOf A G).subgroupOf G = (Subgroup.pi Set.univ
      (fun J : ↥(lcal G) => (kJ A (J : Subgroup Γ)).subgroupOf (J : Subgroup Γ))).map
        hDP.equiv.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_pi, Subgroup.mem_subgroupOf, h.mOf_eq_kProd,
      h.mem_kProd_iff]
    constructor
    · rintro ⟨hxG, hcoord⟩ J -
      have := hcoord J J.2
      rw [coord_eq_equiv_symm hDP J.2 ⟨x, hxG⟩] at this
      exact this
    · intro hx
      refine ⟨x.2, fun J hJ => ?_⟩
      have := hx ⟨J, hJ⟩ trivial
      rw [coord_eq_equiv_symm hDP hJ ⟨x, x.2⟩]
      exact this
  rw [Subgroup.relIndex, hset, Subgroup.index_map_of_bijective hDP.equiv.bijective,
    index_pi_dep]
  rfl

theorem SemisimpleAction.not_dvd_relIndex_mOf
    [Finite Γ] {r : ℕ} (h : SemisimpleAction p A G)
    (hr : r.Prime) (hcomp : ∀ J ∈ lcal G, ¬ r ∣ (kJ A J).relIndex J) :
    ¬ r ∣ (mOf A G).relIndex G := by
  classical
  have : Fintype ↥(lcal G) := Fintype.ofFinite _
  rw [h.relIndex_mOf]
  intro hdvd
  obtain ⟨J, -, hJ⟩ := ((Nat.Prime.prime hr).dvd_finsetProd_iff _).mp hdvd
  exact hcomp J J.2 hJ

theorem SemisimpleAction.not_dvd_relIndex_mOf_of_model
    [Finite Γ] {r : ℕ}
    (h : SemisimpleAction p A G) (hr : r.Prime)
    (hmodel : ∀ J ∈ lcal G,
      (r = 2 ∧ Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) ∨
      (r = 3 ∧ Nonempty (↥J ≃* PSU3 2 p))) :
    ¬ r ∣ (mOf A G).relIndex G := by
  refine h.not_dvd_relIndex_mOf hr fun J hJ => ?_
  obtain ⟨f, hf, -, -, hM, -⟩ := h.exists_frame_data hJ
  have hsub : (kJ A J).subgroupOf J = fixedNormalizer f := by
    rw [← hM]
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have := (h.nearSimple hJ).not_dvd_index_fixedNormalizer hf hr (hmodel J hJ)
  rwa [Subgroup.relIndex, hsub]

end CFSG.SignalizerFunctorTheorem.McBride.Near
