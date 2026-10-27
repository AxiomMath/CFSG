module

public import CFSG.OddTranspositions.PartThree.Nine.Statements
public import CFSG.GH74.Uniqueness.Bender.FixedLinear
public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.GH74.Uniqueness.Bender.Outer
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Walter.Defs

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.BenderSuzuki CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_of_normal_not_isSolvable {F X : Type*} [Group F] [Group X]
    [IsSimpleGroup X] (eF : F ≃* X) {N : Subgroup F} [N.Normal] (hN : ¬ Group.IsSolvable N) :
    Nonempty (N ≃* X) := by
  have hNm : (N.map eF.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ eF.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map eF.toMonoidHom) with h | h
  · exfalso
    apply hN
    have hbot : N = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ eF.injective).mp h
    subst hbot
    infer_instance
  · have htop : N = ⊤ := by
      rw [← Subgroup.comap_map_eq_self_of_injective (f := eF.toMonoidHom) eF.injective N, h,
        Subgroup.comap_top]
    subst htop
    exact ⟨Subgroup.topEquiv.trans eF⟩

theorem outer_involution_fixed_cases {K : Subgroup G} [K.Normal] (hKB : IsBenderGroup K)
    (hKC : Subgroup.centralizer (K : Set G) = ⊥) {u : G} (hu2 : u * u = 1) (huK : u ∉ K)
    {L : Subgroup G} (hLK : L ≤ K) (hLu : ∀ l ∈ L, Commute u l)
    (hLn : ∀ c ∈ K, Commute u c → ∀ l ∈ L, c * l * c⁻¹ ∈ L) (hLns : ¬ Group.IsSolvable L) :
    (∃ m : ℕ, 2 ≤ m ∧ Nonempty (K ≃* PSL2Model (2 * m)) ∧ Nonempty (L ≃* PSL2Model m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) ∧ Nonempty (L ≃* PSL2Model n)) := by
  classical
  set α : MulAut K := MulAut.conjNormal u with hαdef
  have hα : ∀ k : K, ((α k : K) : G) = u * k * u⁻¹ := fun k => MulAut.conjNormal_apply u k
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have hα2 : α * α = 1 := by
    ext k
    change ((α (α k) : K) : G) = k
    rw [hα, hα, hui]
    calc u * (u * ↑k * u) * u = (u * u) * ↑k * (u * u) := by group
      _ = k := by rw [hu2, one_mul, mul_one]
  have hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹ := by
    rintro ⟨g, hg⟩
    apply huK
    have hc : (g : G)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := congrArg Subtype.val (hg ⟨k, hk⟩)
      rw [hα] at h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc k * ((g : G)⁻¹ * u) = (g : G)⁻¹ * (g * k * (g : G)⁻¹) * u := by group
        _ = (g : G)⁻¹ * (u * k * u⁻¹) * u := by rw [h]
        _ = (g : G)⁻¹ * u * k := by group
    rw [hKC, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    exact g.2
  set F := autFixed α with hF
  set L' : Subgroup K := L.subgroupOf K with hL'
  have hL'fix : L' ≤ F := by
    intro l hl
    change α l = l
    apply Subtype.ext
    rw [hα, (hLu l (Subgroup.mem_subgroupOf.mp hl)).eq, mul_inv_cancel_right]
  have hL'eq : L'.map K.subtype = L := by
    rw [hL', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLK]
  set L'' : Subgroup F := L'.subgroupOf F with hL''
  let e₀ : L'' ≃* L := ((Subgroup.subgroupOfEquivOfLe hL'fix).trans
    (L'.equivMapOfInjective K.subtype K.subtype_injective)).trans (MulEquiv.subgroupCongr hL'eq)
  have hL''ns : ¬ Group.IsSolvable L'' := fun h => hLns (by
    have := h
    exact solvable_of_surjective (f := e₀.toMonoidHom) e₀.surjective)
  have hL''n : L''.Normal := by
    refine ⟨fun l hl c => ?_⟩
    rw [hL'', Subgroup.mem_subgroupOf] at hl ⊢
    rw [hL', Subgroup.mem_subgroupOf] at hl ⊢
    have hcK : ((c : K) : G) ∈ K := (c : K).2
    have hcu : Commute u ((c : K) : G) := by
      have h := congrArg Subtype.val (show α c = c from c.2)
      rw [hα] at h
      change u * _ = _ * u
      calc u * ((c : K) : G) = u * ((c : K) : G) * u⁻¹ * u := by group
        _ = ((c : K) : G) * u := by rw [h]
    simpa using hLn _ hcK hcu _ hl
  obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.mp hKB
  cases hBT with
  | linear n hn eK =>
    obtain ⟨m, rfl, ⟨eF⟩, -⟩ := BenderType.fixed_linear (.linear n hn eK) α hα2 hout
    have hm : 2 ≤ m := by
      by_contra hm
      have hm1 : m = 1 := by omega
      subst hm1
      apply hL''ns
      have : Group.IsSolvable (PSL2Model 1) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_psl2_galoisField_two_one
      have : Group.IsSolvable F := solvable_of_surjective (f := eF.symm.toMonoidHom)
        eF.symm.surjective
      infer_instance
    have : IsSimpleGroup (PSL2Model m) :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup (.isPSL2 m hm (MulEquiv.refl _))
    obtain ⟨eN⟩ := nonempty_mulEquiv_of_normal_not_isSolvable eF hL''ns
    exact Or.inl ⟨m, hm, ⟨eK⟩, ⟨e₀.symm.trans eN⟩⟩
  | suzuki a ha eK =>
    exfalso
    obtain ⟨v, -, hv⟩ := BenderType.exists_inner_of_sq_eq_one_suzuki (.suzuki a ha eK) α hα2
    exact hout ⟨v, fun x => by rw [hv]⟩
  | unitary n hn eK =>
    obtain ⟨eF⟩ := BenderType.fixed_unitary (.unitary n hn eK) α hα2 hout
    have : IsSimpleGroup (PSL2Model n) :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup (.isPSL2 n hn (MulEquiv.refl _))
    obtain ⟨eN⟩ := nonempty_mulEquiv_of_normal_not_isSolvable eF hL''ns
    exact Or.inr ⟨n, hn, ⟨eK⟩, ⟨e₀.symm.trans eN⟩⟩

end CFSG.OddTranspositions.PartThree.Nine
