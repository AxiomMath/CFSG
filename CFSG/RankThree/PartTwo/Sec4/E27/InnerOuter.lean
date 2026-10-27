module

public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import CFSG.RankThree.PartTwo.Sec4.E27.HyperOuter

public section

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem centralizer_range_conj_eq_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Subgroup.centralizer (((MulAut.conj : X →* MulAut X).range : Subgroup (MulAut X)) :
      Set (MulAut X)) = ⊥ := by
  have hinj := conj_injective_of_center_bot hZ
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff] at hφ
  rw [Subgroup.mem_bot]
  ext x
  have h := hφ (MulAut.conj x) ⟨x, rfl⟩
  have h3 : (MulAut.conj x * φ) = MulAut.conj x * φ := rfl
  have h4 : φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]
  have h5 : MulAut.conj (φ x) = MulAut.conj x := by
    rw [← h4, ← h]
    group
  simpa using hinj h5

theorem seitz27_of_inner_outer {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hinner : ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 27 →
      HyperGen 3 (⊤ : Subgroup X) E)
    (hF : FieldAutData X 3) (hP : FixPlaneGen X 3) : Seitz27 X := by
  intro E hE hEc
  have hinj := conj_injective_of_center_bot hZ
  set K : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hK
  by_cases hin : E ≤ K
  ·
    set E' : Subgroup X := E.comap (MulAut.conj : X →* MulAut X) with hE'
    have hEmap : E'.map (MulAut.conj : X →* MulAut X) = E := by
      rw [hE', Subgroup.map_comap_eq]
      exact inf_eq_right.2 hin
    have hc' : Nat.card E' = 27 := by
      have := Subgroup.card_map_of_injective hinj (K := E')
      rw [hEmap] at this
      rw [← this, hEc]
    have hEa' : IsElemAbelian 3 E' := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · apply hinj
        have h1 := congrArg Subtype.val (hE.1.is_comm.comm
          (⟨MulAut.conj (a : X), a.2⟩ : E) ⟨MulAut.conj (b : X), b.2⟩)
        simpa using h1
      · apply hinj
        have h1 := hE.2 _ hx
        simpa using h1
    have h := hinner E' hEa' hc'
    rw [eq_top_iff]
    intro k _
    have hk := h (Subgroup.mem_top k)
    refine (Subgroup.closure_le (seitzHyperGamma 3 E)).2 ?_ hk
    rintro k ⟨-, F', hF'E', hrel, hcomm⟩
    have hFE : F'.map (MulAut.conj : X →* MulAut X) ≤ E := by
      rw [← hEmap]
      exact Subgroup.map_mono hF'E'
    have hrelE : (F'.map (MulAut.conj : X →* MulAut X)).relIndex E = 3 := by
      rw [← hEmap, Subgroup.relIndex_map_map_of_injective F' E' hinj]
      exact hrel
    have hfix : k ∈ fixedPoints (F'.map (MulAut.conj : X →* MulAut X)) := by
      rintro _ ⟨f, hf, rfl⟩
      have h2 := hcomm f hf
      simp only [MonoidHom.coe_coe, MulAut.conj_apply]
      rw [h2]
      group
    exact (le_iSup₂_of_le (F'.map (MulAut.conj : X →* MulAut X)) ⟨hFE, hrelE⟩ le_rfl :
      fixedPoints (F'.map (MulAut.conj : X →* MulAut X)) ≤ seitzHyperGamma 3 E) hfix
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI hKn : K.Normal := ⟨by
      rintro _ ⟨x, rfl⟩ g
      refine ⟨g x, ?_⟩
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]⟩
    have e : X ≃* K := MonoidHom.ofInjective hinj
    have hF' : FieldAutData K 3 := hF.of_mulEquiv e.symm Nat.prime_three
    have hP' : FixPlaneGen K 3 := hP.of_mulEquiv e.symm Nat.prime_three
    haveI : Finite (MulAut X) := inferInstance
    have h := hyperGen_of_fieldAutData_outer (centralizer_range_conj_eq_bot hZ) hF' hP' hE hEc hin
    exact seitzHyperGamma_eq_top_of_hyperGen hZ E h

end CFSG.RankThree.PartTwo.Sec4.E27
