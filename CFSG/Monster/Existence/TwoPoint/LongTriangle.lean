module

public import CFSG.Monster.Existence.TwoPoint.PartFour
public import CFSG.Monster.Existence.TwoPoint.CoPairU62
public import CFSG.Monster.Existence.AssemblyHS
public import CFSG.Monster.Existence.TwoPoint.LeechPlug

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section General

variable {G : Type} [Group G]

theorem mem_pointStab_iff {s : Set G} {h : G} : h ∈ pointStab s ↔ ∀ x ∈ s, h ∈ cent x := by
  simp only [pointStab, Subgroup.mem_iInf]

theorem map_pointStab_conjSet (g : G) (s : Set G) :
    (pointStab s).map (MulAut.conj g).toMonoidHom = pointStab (conjSet g s) := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_pointStab_iff, mem_pointStab_iff]
  constructor
  · intro hh x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hh y hy)
    rw [MulAut.conj_symm_apply] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * (g * y * g⁻¹) = g * ((g⁻¹ * h * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * h := by group
  · intro hh y hy
    have := hh (g * y * g⁻¹) ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    simp only [MulAut.conj_symm_apply]
    calc g⁻¹ * h * g * y = g⁻¹ * (h * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * h) * g := by rw [this]
      _ = y * (g⁻¹ * h * g) := by group

noncomputable def pointStabConjEquiv (g : G) (s : Set G) :
    ↥(pointStab s) ≃* ↥(pointStab (conjSet g s)) :=
  ((pointStab s).equivMapOfInjective _ (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (map_pointStab_conjSet g s))

theorem HasLayeredTwoShape.conjSet {s : Set G} (g : G) {a b : ℕ}
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → P X → P Y)
    (h : HasLayeredTwoShape (pointStab s) a b P) :
    HasLayeredTwoShape (pointStab (conjSet g s)) a b P :=
  HasLayeredTwoShape.of_mulEquiv (pointStabConjEquiv g s) hP h

theorem pCore_eq_of_layered {H : Subgroup G} {a b : ℕ} {S : Type} [Group S]
    (hS : ∀ P : Subgroup S, P.Normal → IsPGroup 2 P → P = ⊥)
    (h : HasLayeredTwoShape H a b fun X _ => Nonempty (X ≃* S)) :
    Nonempty (↥H ⧸ pCore 2 ↥H ≃* S) := by
  obtain ⟨N, hN, -, -, -, -, -, -, hc, ⟨e⟩⟩ := h
  have hp := pCore_eq_of_quotient N (IsPGroup.of_card hc) e hS
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hp).trans e⟩

theorem exists_conjSet_eq_of_isLongTriangle
    [Finite G] {d₀ : B} {a z₀ : G}
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {s s' : Set G}
    (hs : IsLongTriangle a s) (hs' : IsLongTriangle a s') : ∃ g : G, conjSet g s = s' := by
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨s₁, s₂, -, -, -, hcov⟩ := two_triangle_orbits I hG
  obtain ⟨y, hy⟩ := table7_nonempty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG
    (IsConj.refl a) .two_A
  have hS := isShortTriangle_mul ha (IsConj.refl a) hy.1 hy.2
  have hlong : ∀ {t : Set G} (g : G), IsLongTriangle a t → IsLongTriangle a (conjSet g t) :=
    fun {t} g ht => ⟨ht.1.conjSet g, fun h => ht.2 (by
      have := h.conjSet g⁻¹
      rwa [conjSet_conjSet, inv_mul_cancel, show conjSet 1 t = t from by
        ext x; simp [conjSet]] at this)⟩
  obtain ⟨g, hg⟩ := hcov s hs.1
  obtain ⟨g', hg'⟩ := hcov s' hs'.1
  obtain ⟨h, hh⟩ := hcov _ hS.1
  have back : ∀ (t : Set G) (k : G), conjSet k⁻¹ (conjSet k t) = t := fun t k => by
    rw [conjSet_conjSet, inv_mul_cancel]
    ext x; simp [conjSet]
  rcases hg with hg | hg <;> rcases hg' with hg' | hg'
  · exact ⟨g'⁻¹ * g, by rw [← conjSet_conjSet, hg, ← hg', back]⟩
  · exfalso
    rcases hh with hh | hh
    · exact (hlong g hs).2 (hg ▸ hh ▸ hS.conjSet h)
    · exact (hlong g' hs').2 (hg' ▸ hh ▸ hS.conjSet h)
  · exfalso
    rcases hh with hh | hh
    · exact (hlong g' hs').2 (hg' ▸ hh ▸ hS.conjSet h)
    · exact (hlong g hs).2 (hg ▸ hh ▸ hS.conjSet h)
  · exact ⟨g'⁻¹ * g, by rw [← conjSet_conjSet, hg, ← hg', back]⟩

end General

section MGriess

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.B CFSG.Monster.B.Short

theorem four_c_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess) :
    ∀ s, IsLongTriangle tGriess s →
      CFSG.Blueprint.LieModel (pointStab s ⧸ pCore 2 (pointStab s)) .PSU 6 2 1 ∧
      HasLayeredTwoShape (pointStab s) 3 20 fun X _ => CFSG.Blueprint.LieModel X .PSU 6 2 1 := by
  obtain ⟨α, β, γ, hT, -, N, hN, N₀, hN₀, hle, hE, hc₀, hQ, hc, ⟨e⟩⟩ :=
    leech_longTriangle_shape_coW2
  have hQ₀ : HasLayeredTwoShape (pointStab ({α, β, γ} : Set MGriess)) 3 20
      fun X _ => Nonempty (X ≃* ↥(Kstab Co2.v0 ⊓ Kstab coW2)) :=
    ⟨N, hN, N₀, hN₀, hle, hE, hc₀, hQ, hc, ⟨e⟩⟩
  intro s hs
  obtain ⟨g, rfl⟩ := exists_conjSet_eq_of_isLongTriangle I gmsF1Type_MGriess_uncond hT hs
  have hQs := HasLayeredTwoShape.conjSet g
    (P := fun X _ => Nonempty (X ≃* ↥(Kstab Co2.v0 ⊓ Kstab coW2)))
    (fun _ _ _ _ f hX => hX.map fun k => f.symm.trans k) hQ₀
  obtain ⟨f⟩ := pCore_eq_of_layered coPair_u62_pCore hQs
  refine ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv f.symm coPair_u62, ?_⟩
  exact HasLayeredTwoShape.of_mulEquiv (MulEquiv.refl _)
    (P := fun X _ => CFSG.Blueprint.LieModel X .PSU 6 2 1)
    (fun _ _ _ _ k hX => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv k hX)
    (by
      obtain ⟨M, hM, M₀, hM₀, h1, h2, h3, h4, h5, ⟨k⟩⟩ := hQs
      exact ⟨M, hM, M₀, hM₀, h1, h2, h3, h4, h5,
        CFSG.LieType.CurtisTits.lieModel_of_mulEquiv k.symm coPair_u62⟩)

end MGriess

end CFSG.Monster.Existence
