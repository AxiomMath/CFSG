module

public import CFSG.RankThree.PartTwo.Sec8.Groups
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.GH74.KGroups.U33
public import CFSG.LieType.Chevalley.G2SolvableNormalTrivial
public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem inner_of_pow_three_adjointGroup_two
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {α : MulAut (adjointGroup Tag.G2 k)} (hα3 : α ^ 3 = 1) :
    α ∈ (MulAut.conj : adjointGroup Tag.G2 k →* MulAut (adjointGroup Tag.G2 k)).range := by
  classical
  set Dc : Subgroup (adjointGroup Tag.G2 k) := commutator (adjointGroup Tag.G2 k) with hDc
  have hDcD : Dc.map (adjointGroup Tag.G2 k).subtype =
      ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := by
    rw [hDc, commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  have eDD : Dc ≃* ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ :=
    (Dc.equivMapOfInjective _ (adjointGroup Tag.G2 k).subtype_injective).trans
      (MulEquiv.subgroupCongr hDcD)
  obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hLie
  set eD : Dc ≃* CFSG.GH74.KGroups.U33.QP.originalSubgroup := eDD.trans eU with heD
  have hAutD : Nat.card (MulAut Dc) = 12096 := CFSG.GH74.KGroups.U33.card_mulAut eD
  have hcardD : Nat.card Dc = 6048 := by
    rw [Nat.card_congr eD.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  have hDsimple : IsSimpleGroup Dc := by
    have : IsSimpleGroup ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := by
      rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM).2
      all_goals exact absurd h0 (by norm_num)
    exact eDD.isSimpleGroup
  have : IsSimpleGroup Dc := hDsimple
  have hZD : Subgroup.center Dc = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Dc) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative Dc :=
        ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a⟩⟩
      have hp := (Group.is_simple_iff_prime_card (α := Dc)).mp hDsimple
      rw [hcardD] at hp
      norm_num at hp
  have hconjD : Function.Injective (MulAut.conj : Dc →* MulAut Dc) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcen : g ∈ Subgroup.center Dc := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 := congrArg (fun φ : MulAut Dc => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc h * g = g * h * g⁻¹ * g := by rw [h1]
        _ = g * h := by group
    rw [hZD, Subgroup.mem_bot] at hcen
    exact hcen
  set I := (MulAut.conj : Dc →* MulAut Dc).range with hI
  have hIcard : Nat.card I = 6048 := by
    rw [hI, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hconjD, Subgroup.card_top,
      hcardD]
  have hIidx : I.index = 2 := by
    have h := I.card_mul_index
    rw [hIcard, hAutD] at h
    omega
  have hmap : Dc.map α.toMonoidHom = Dc :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) α
  set α' : MulAut Dc := (α.subgroupMap Dc).trans (MulEquiv.subgroupCongr hmap) with hα'
  have hα'apply : ∀ x : Dc, ((α' x : Dc) : adjointGroup Tag.G2 k) = α x := fun x => rfl
  have hα'3 : α' ^ 3 = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have h := congrArg (fun f : MulAut (adjointGroup Tag.G2 k) => f x) hα3
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h ⊢
    rw [hα'apply, hα'apply, hα'apply]
    exact h
  have hα'I : α' ∈ I := by
    by_contra hnot
    apply hnot
    have h2 : α' * α' ∈ I := Subgroup.mul_self_mem_of_index_two hIidx α'
    have h3 : α' * (α' * α') ∈ I := by
      rw [← mul_assoc, ← pow_two, ← pow_succ, hα'3]
      exact one_mem I
    have := I.mul_mem h3 (I.inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨d, hd⟩ := hα'I
  set N : Subgroup (adjointGroup Tag.G2 k) := Subgroup.centralizer (Dc : Set _) with hN
  have hNDc : ∀ x ∈ N, x ∈ Dc → x = 1 := by
    intro x hxN hxD
    have hcen : (⟨x, hxD⟩ : Dc) ∈ Subgroup.center Dc := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxN y y.2)
    rw [hZD, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hNn : N.Normal := by
    rw [hN]
    infer_instance
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have hcomm : a * b * a⁻¹ * b⁻¹ = 1 := by
      refine hNDc _ ?_ ?_
      · exact N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)
      · have : ⁅a, b⁆ ∈ Dc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
          (Subgroup.mem_top b)
        simpa [commutatorElement_def] using this
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hcomm, one_mul]
  have hNsolv : Group.IsSolvable N := by
    have : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext (hNcomm _ a.2 _ b.2)⟩⟩
    infer_instance
  have hNbot : N = ⊥ := CFSG.LieType.Chevalley.G2_solvable_normal_subgroups_trivial k N hNsolv
  refine ⟨(d : adjointGroup Tag.G2 k), MulEquiv.ext fun y => ?_⟩
  have hαx : ∀ x ∈ Dc, α x = (d : adjointGroup Tag.G2 k) * x * (d : adjointGroup Tag.G2 k)⁻¹ := by
    intro x hx
    have h := congrArg (fun f : MulAut Dc => ((f ⟨x, hx⟩ : Dc) : adjointGroup Tag.G2 k)) hd
    simp only [MulAut.conj_apply] at h
    rw [← hα'apply ⟨x, hx⟩, ← h]
    rfl
  set v := y⁻¹ * (d : adjointGroup Tag.G2 k)⁻¹ * α y * d with hv
  have hvN : v ∈ N := by
    rw [hN, Subgroup.mem_centralizer_iff]
    intro x hx
    have hyx : y * x * y⁻¹ ∈ Dc := (inferInstance : Dc.Normal).conj_mem x hx y
    have h1 := hαx _ hyx
    rw [map_mul, map_mul, map_inv, hαx x hx] at h1
    have h2 : v * x * v⁻¹ = x := by
      rw [hv]
      calc y⁻¹ * (d : adjointGroup Tag.G2 k)⁻¹ * α y * d * x *
            (y⁻¹ * (d : adjointGroup Tag.G2 k)⁻¹ * α y * d)⁻¹ =
          y⁻¹ * (d : adjointGroup Tag.G2 k)⁻¹ *
            (α y * ((d : adjointGroup Tag.G2 k) * x * (d : adjointGroup Tag.G2 k)⁻¹) *
              (α y)⁻¹) * d * y := by group
        _ = y⁻¹ * (d : adjointGroup Tag.G2 k)⁻¹ *
            ((d : adjointGroup Tag.G2 k) * (y * x * y⁻¹) * (d : adjointGroup Tag.G2 k)⁻¹) *
              d * y := by rw [h1]
        _ = x := by group
    calc x * v = v * x * v⁻¹ * v := by rw [h2]
      _ = v * x := by group
  rw [hNbot, Subgroup.mem_bot] at hvN
  rw [MulAut.conj_apply]
  calc (d : adjointGroup Tag.G2 k) * y * (d : adjointGroup Tag.G2 k)⁻¹ =
      (d : adjointGroup Tag.G2 k) * y * (y⁻¹ * (d : adjointGroup Tag.G2 k)⁻¹ * α y * d) *
        (d : adjointGroup Tag.G2 k)⁻¹ := by rw [← hv, hvN, mul_one]
    _ = α y := by group

theorem inner_of_pow_three_of_g2Two
    {Y : Type} [Group Y] (hY : CFSG.RankThree.PartTwo.Sec8.IsoGTwoEven Y 1) {c : MulAut Y}
    (hc3 : c ^ 3 = 1) : c ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hY
  have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
  have hα3 : MulAut.congr e c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e c).mp
    (inner_of_pow_three_adjointGroup_two hk2 hα3)

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
