module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C1

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

@[expose] def fixedSub {X : Type} [Group X] (f : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus f.toMonoidHom (MonoidHom.id X)

theorem mem_fixedSub {X : Type} [Group X] {f : MulAut X} {x : X} : x ∈ fixedSub f ↔ f x = x :=
  Iff.rfl

theorem exists_resHom {X : Type} [Group X] (F : Subgroup (MulAut X)) (hF : IsMulCommutative F)
    {f : MulAut X} (hf : f ∈ F) :
    ∃ r : F →* MulAut ↥(fixedSub f),
      ∀ (g : F) (x : ↥(fixedSub f)), ((r g x : ↥(fixedSub f)) : X) = (g : MulAut X) x := by
  have hstab : ∀ g : MulAut X, g ∈ F → ∀ x : X, x ∈ fixedSub f → g x ∈ fixedSub f := by
    intro g hg x hx
    rw [mem_fixedSub] at hx ⊢
    have hcomm : g * f = f * g := congrArg Subtype.val (hF.is_comm.comm ⟨g, hg⟩ ⟨f, hf⟩)
    have := congrArg (fun h : MulAut X => h x) hcomm
    simp only [MulAut.mul_apply] at this
    rw [hx] at this
    exact this.symm
  let aut : F → MulAut ↥(fixedSub f) := fun g =>
    { toFun := fun x => ⟨(g : MulAut X) x, hstab _ g.2 _ x.2⟩
      invFun := fun x => ⟨((g : MulAut X)⁻¹) x, hstab _ (F.inv_mem g.2) _ x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨{ toFun := aut, map_one' := ?_, map_mul' := ?_ }, fun g x => rfl⟩
  · ext x
    simp [aut]
  · intro g h
    ext x
    simp [aut]

theorem conc_of_fixedSub {X : Type} [Group X] [Finite X] (F : Subgroup (MulAut X))
    (hF : CFSG.Open.IsElemAbelian 3 F) {f : MulAut X} (hf : f ∈ F)
    (hQ : ∀ F₀ : Subgroup (MulAut ↥(fixedSub f)), CFSG.Open.IsElemAbelian 3 F₀ →
      Conc ↥(fixedSub f) F₀) : Conc X F := by
  haveI : Finite (MulAut X) := Finite.of_injective (fun g : MulAut X => (g : X → X))
    DFunLike.coe_injective
  obtain ⟨r, hr⟩ := exists_resHom F hF.1 hf
  have hcomm : IsMulCommutative r.range := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show r a * r b = r b * r a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val (hF.1.is_comm.comm a b))
  have hF0 : CFSG.Open.IsElemAbelian 3 r.range := by
    refine ⟨hcomm, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : (a : MulAut X) ^ 3 = 1 := hF.2 a a.2
    have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using this)
    rw [h3, map_one]
  obtain ⟨F0', hF0'le, hcard0, V, hVne, hVp, hVst⟩ := hQ r.range hF0
  set φ : F →* r.range := r.rangeRestrict with hφ
  have hφs : Function.Surjective φ := r.rangeRestrict_surjective
  set K0 : Subgroup r.range := F0'.subgroupOf r.range with hK0
  set F'' : Subgroup F := K0.comap φ with hF''
  refine ⟨F''.map F.subtype, Subgroup.map_subtype_le _, ?_, V.map (fixedSub f).subtype, ?_, ?_, ?_⟩
  · have e1 : Nat.card (F''.map F.subtype) = Nat.card F'' :=
      Subgroup.card_map_of_injective F.subtype_injective
    have e2 : F''.index = K0.index := Subgroup.index_comap_of_surjective _ hφs
    have e3 : Nat.card K0 = Nat.card F0' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF0'le).toEquiv
    have e4 : Nat.card F'' * F''.index = Nat.card F := Subgroup.card_mul_index F''
    have e5 : Nat.card K0 * K0.index = Nat.card r.range := Subgroup.card_mul_index K0
    have hpos : 0 < Nat.card F0' := Nat.card_pos
    have hidx : K0.index ≤ 3 := by
      have : Nat.card K0 * K0.index ≤ Nat.card K0 * 3 := by
        rw [e5, e3]; omega
      exact Nat.le_of_mul_le_mul_left this (by rw [e3]; exact hpos)
    rw [e1, ← e4, e2]
    exact Nat.mul_le_mul_left _ hidx |>.trans (by omega)
  · intro h
    apply hVne
    apply Subgroup.map_injective (f := (fixedSub f).subtype) (fixedSub f).subtype_injective
    rw [h, Subgroup.map_bot]
  · exact hVp.of_equiv (V.equivMapOfInjective (fixedSub f).subtype (fixedSub f).subtype_injective)
  · intro g hg v hv
    obtain ⟨g'', hg'', rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨v0, hv0, rfl⟩ := Subgroup.mem_map.mp hv
    have hmem : (r g'' : MulAut ↥(fixedSub f)) ∈ F0' := hg''
    refine Subgroup.mem_map.mpr ⟨r g'' v0, hVst _ hmem v0 hv0, ?_⟩
    exact (hr g'' v0)

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
