module

public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch1Sec3Solvable

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin

variable {Γ : Type} [Group Γ]

theorem map_normal_of_characteristic {N : Subgroup Γ} [N.Normal] (C : Subgroup ↥N)
    [C.Characteristic] : (C.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hx
  have hchar : C.Characteristic := inferInstance
  have hmap := Subgroup.characteristic_iff_map_eq.mp hchar (MulAut.conjNormal g : MulAut ↥N)
  have hc' : (MulAut.conjNormal g : MulAut ↥N) c ∈ C := by
    rw [← hmap]
    exact ⟨c, hc, rfl⟩
  refine ⟨_, hc', ?_⟩
  rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]

variable [Finite Γ]

theorem map_fitting_le {N : Subgroup Γ} [N.Normal] :
    (CFSG.fittingSubgroup ↥N).map N.subtype ≤ CFSG.fittingSubgroup Γ := by
  have hn := map_normal_of_characteristic (N := N) (CFSG.fittingSubgroup ↥N)
  have : Group.IsNilpotent (CFSG.fittingSubgroup ↥N) := CFSG.fittingSubgroup_nilpotent
  have hnil : Group.IsNilpotent ((CFSG.fittingSubgroup ↥N).map N.subtype) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (CFSG.fittingSubgroup ↥N) N.subtype N.subtype_injective)
  exact le_sSup ⟨hn, hnil⟩

omit [Finite Γ] in
theorem map_pCore_le {N : Subgroup Γ} [N.Normal] (p : ℕ) :
    (CFSG.pCore p ↥N).map N.subtype ≤ CFSG.pCore p Γ := by
  have : (CFSG.pCore p ↥N).Characteristic := CFSG.BaerSuzuki.Helpers.pCore_characteristic p
  exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
    (map_normal_of_characteristic (CFSG.pCore p ↥N))
    ((CFSG.BaerSuzuki.Helpers.pCore_isPGroup p).map _)

theorem false_of_rank_le_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {N : Subgroup Γ}
    [N.Normal] (hrk : Open.pRank p (CFSG.pCore p Γ) ≤ 1) {Q : Subgroup ↥(CFSG.pCore p ↥N)}
    (hQ : IsElemAbelianOfRank p 2 ↥Q ∨ IsPOnePlusTwo p ↥Q) : False := by
  let f : ↥Q →* Γ := N.subtype.comp ((CFSG.pCore p ↥N).subtype.comp Q.subtype)
  have hfi : Function.Injective f :=
    N.subtype_injective.comp ((CFSG.pCore p ↥N).subtype_injective.comp Q.subtype_injective)
  have hmem : ∀ q : ↥Q, f q ∈ CFSG.pCore p Γ := fun q =>
    map_pCore_le p ⟨_, (q : ↥(CFSG.pCore p ↥N)).2, rfl⟩
  let f' : ↥Q →* ↥(CFSG.pCore p Γ) := f.codRestrict _ hmem
  have hf'i : Function.Injective f' := by
    intro a b h
    apply hfi
    have h' := congrArg (fun z : ↥(CFSG.pCore p Γ) => (z : Γ)) h
    exact h'
  have hrkQ : Open.pRank p (⊤ : Subgroup ↥Q) ≤ 1 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt f' hf'i).trans
      ((pRank_top_subtype (CFSG.pCore p Γ)).le.trans hrk)
  have hQp : IsPGroup p ↥Q :=
    (CFSG.BaerSuzuki.Helpers.pCore_isPGroup p).of_injective Q.subtype Q.subtype_injective
  have hcyc := Ch1Sec3.isCyclic_of_pRank_le_one hp2 hQp hrkQ
  rcases hQ with he | ⟨hex, hcard, -⟩
  · obtain ⟨e⟩ := he
    have hcard : Nat.card ↥Q = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hexp : Monoid.exponent ↥Q ∣ p := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => e.injective ?_
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      ext i
      simp
    rw [IsCyclic.exponent_eq_card, hcard] at hexp
    have := Nat.le_of_dvd hp.out.pos hexp
    have := hp.out.two_le
    nlinarith
  · have := hex
    have h1 := CFSG.IsExtraspecial.center_order_p p ↥Q
    have hcomm : IsMulCommutative ↥Q := IsCyclic.isMulCommutative
    have h2 : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hcomm.is_comm.comm y x
    rw [h2, Subgroup.card_top, hcard] at h1
    have := hp.out.two_le
    have h3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    rw [pow_one] at h3
    omega

end CFSG.Quasithin.Vol2.Ch11.OE6
