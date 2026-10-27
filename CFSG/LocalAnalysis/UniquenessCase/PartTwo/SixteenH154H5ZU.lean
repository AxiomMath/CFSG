module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZGroupB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZFixU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_L3World_map_mem_irrSet {U : Type} [CommGroup U]
    {N L : Subgroup (MulAut U)} (hN : N ≤ Subgroup.normalizer (L : Set (MulAut U)))
    {g : MulAut U} (hg : g ∈ N) {I : Subgroup U} (hI : I ∈ irrSet L) :
    I.map g.toMonoidHom ∈ irrSet L :=
  CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hN hg) x).1 hx)
    (fun x hx => by
      have := (Subgroup.mem_normalizer_iff.1 (hN (N.inv_mem hg)) x).1 hx
      simpa using this) hI

private noncomputable def s16h_L3World_irrSetActFun {U : Type} [CommGroup U]
    {N L : Subgroup (MulAut U)} (h : s16h_L3World N L) (a : ↥N) :
    Equiv.Perm ↥(irrSet L) :=
  Equiv.ofBijective
    (fun I : ↥(irrSet L) =>
      ⟨(I : Subgroup U).map (a : MulAut U).toMonoidHom,
        s16h_L3World_map_mem_irrSet h.normal a.2 I.2⟩)
    ⟨fun I I' hII' => Subtype.ext
        (Subgroup.map_injective (MulEquiv.injective (a : MulAut U))
          (Subtype.ext_iff.mp hII')),
     fun I' => ⟨⟨(I' : Subgroup U).map ((a : MulAut U)⁻¹).toMonoidHom,
        s16h_L3World_map_mem_irrSet h.normal (N.inv_mem a.2) I'.2⟩, by
       apply Subtype.ext
       show ((I' : Subgroup U).map ((a : MulAut U)⁻¹).toMonoidHom).map
           (a : MulAut U).toMonoidHom = (I' : Subgroup U)
       rw [Subgroup.map_map]
       have hcomp : (a : MulAut U).toMonoidHom.comp ((a : MulAut U)⁻¹).toMonoidHom =
           MonoidHom.id U := by ext w; simp
       rw [hcomp, Subgroup.map_id]⟩⟩

private lemma s16h_L3World_irrSetActFun_apply {U : Type} [CommGroup U]
    {N L : Subgroup (MulAut U)} (h : s16h_L3World N L) (a : ↥N) (I : ↥(irrSet L)) :
    ((s16h_L3World_irrSetActFun h a I : ↥(irrSet L)) : Subgroup U) =
      (I : Subgroup U).map (a : MulAut U).toMonoidHom :=
  rfl

private noncomputable def s16h_L3World_irrSetAct {U : Type} [CommGroup U]
    {N L : Subgroup (MulAut U)} (h : s16h_L3World N L) :
    ↥N →* Equiv.Perm ↥(irrSet L) where
  toFun := s16h_L3World_irrSetActFun h
  map_one' := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    change (I : Subgroup U).map (1 : MulAut U).toMonoidHom = (I : Subgroup U)
    rw [show (1 : MulAut U).toMonoidHom = MonoidHom.id U from rfl, Subgroup.map_id]
  map_mul' a b := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    change (I : Subgroup U).map ((a * b : ↥N) : MulAut U).toMonoidHom =
      ((I : Subgroup U).map (b : MulAut U).toMonoidHom).map (a : MulAut U).toMonoidHom
    rw [Subgroup.map_map]
    congr 1

theorem s16h_L3World_group {U : Type} [CommGroup U] [Finite U] {N L : Subgroup (MulAut U)}
    (h : s16h_L3World N L) :
    ∃ (P : Type) (_ : Group P) (ρ : ↥N →* P), (∀ a : ↥N, ρ a = 1 → (a : MulAut U) ∈ L) ∧
      s16h_ZCondGroup ↥ρ.range := by
  classical
  haveI : Finite ↥(irrSet L) := Finite.of_injective _ Subtype.coe_injective
  haveI : Fintype ↥(irrSet L) := Fintype.ofFinite _
  let rho : ↥N →* Equiv.Perm ↥(irrSet L) := s16h_L3World_irrSetAct h
  have hker : ∀ a : ↥N, rho a = 1 → (a : MulAut U) ∈ L := by
    intro a ha
    refine s16h_L3World_fix h a.2 ?_
    intro J hJ
    have h2 := congrArg (fun σ : Equiv.Perm ↥(irrSet L) =>
      ((σ ⟨J, hJ⟩ : ↥(irrSet L)) : Subgroup U)) ha
    change ((s16h_L3World_irrSetActFun h a ⟨J, hJ⟩ : ↥(irrSet L)) : Subgroup U) =
      (J : Subgroup U) at h2
    rw [s16h_L3World_irrSetActFun_apply] at h2
    simpa using h2
  by_cases hsmall : Nat.card ↥(irrSet L) ≤ 3
  · refine ⟨Equiv.Perm ↥(irrSet L), inferInstance, rho, hker, ?_⟩
    have hcard : Fintype.card ↥(irrSet L) ≤ 3 := by
      rwa [Nat.card_eq_fintype_card] at hsmall
    exact s16h_zcondGroup_of_embed_perm_fintype hcard (Subgroup.subtype rho.range)
      (Subgroup.subtype_injective rho.range)
  · obtain ⟨k, hk3, hsum⟩ := h.sum
    have hknot : ¬ k ≤ 2 := fun hk2 => hsmall (s16h_L3World_card_irr_le_three h hk2 hsum)
    have hk : k = 3 := by omega
    have hsum3 : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) 3 :=
      hk ▸ hsum
    rcases s16h_L3World_three h hsum3 with h3 | ⟨r, hrker, htrans⟩
    · exact absurd h3 (by omega)
    · refine ⟨Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), inferInstance, r, ?_, ?_⟩
      · intro a ha
        exact s16h_L3World_fix h a.2 ((hrker a).mp ha)
      · refine s16h_zcondGroup_of_transitive_gl3 r.range ?_
        intro u v hu hv
        obtain ⟨a, ha⟩ := htrans u v hu hv
        exact ⟨r a, MonoidHom.mem_range.mpr ⟨a, rfl⟩, ha⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
