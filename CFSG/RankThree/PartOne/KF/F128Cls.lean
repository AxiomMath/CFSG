module

public import CFSG.RankThree.PartOne.KF.F122Glue
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.S11c.Sec66PSUFrame
public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL
public import CFSG.RankThree.PartOne.K128.TorusShape
public import CFSG.RankThree.PartOne.K1214.Omega
public import CFSG.LieType.Simplicity.Classical
public import CFSG.RankThree.PartOne.S11d.FixedFacts

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.PartOne.K1214 (SylowShape)

theorem false_of_three_le_localRank {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hLR2 : LocalRankLeTwo p T) (h3 : 3 ≤ localRank p T) : False := by
  obtain ⟨U, hU2, hU1, E, hEN, hE, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 3) h3
  exact hLR2 E hE hEc U hU1 hU2 hEN

theorem statedClassicalModel_congr {G H : Type} [Group G] [Group H] (ε : H ≃* G)
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel H t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ε.symm h

theorem localRank_le_three_of_cover {J T : Type} [Group J] [Finite J] [Group T] [Finite T]
    (π : J →* T) (hπ : Function.Surjective π) (he : evenRank J ≤ 3) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card π.ker) : localRank r T ≤ 3 := by
  calc localRank r T = localRank r (J ⧸ π.ker) :=
        (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
          (QuotientGroup.quotientKerEquivOfSurjective π hπ) hr).symm
    _ ≤ localRank r J := CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 π.ker hZ
    _ ≤ evenRank J := CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2
    _ ≤ 3 := he

theorem center_eq_bot_of_cover {J T : Type} [Group J] (hJ : Group.IsPerfect J) [Group T]
    (π : J →* T) (hπ : Function.Surjective π) {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel T t n p f) : Subgroup.center T = ⊥ := by
  have hsimple : IsSimpleGroup T :=
    (LieType.Simplicity.fam_classical_converse T
      ((Milestones.fam_classical_model_membership_alltags T).2 ⟨t, n, p, f, h⟩)).2.2
  have hperf : Group.IsPerfect T := by
    have := hJ
    exact Group.IsPerfect.ofSurjective (f := π) hπ
  apply center_eq_bot_of_simple'
  by_contra hc
  push Not at hc
  have h1 : (commutator T : Subgroup T) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := hc g h
    calc g * h * g⁻¹ * h⁻¹ = (h * g) * g⁻¹ * h⁻¹ := by rw [this]
      _ = 1 := by group
  obtain ⟨x, hx⟩ := exists_ne (1 : T)
  have h2 : x ∈ commutator T := by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top x
  rw [h1, Subgroup.mem_bot] at h2
  exact hx h2

open CFSG.GroupTheory.WeirSylow in
theorem isCyclic_sigmaModel_of_div_le_one {p e a N : ℕ} [hp : Fact p.Prime] (h : N / e ≤ 1) :
    IsCyclic (sigmaModel p e a N) := by
  rcases Nat.lt_or_ge (N / e) 1 with h0 | h1
  · have hd : Nat.digits p (N / e) = [] := by
      rw [Nat.lt_one_iff.mp h0]; exact Nat.digits_zero p
    have hlen : (Nat.digits p (N / e)).length = 0 := by rw [hd]; rfl
    have : IsEmpty (Fin (Nat.digits p (N / e)).length) := by rw [hlen]; infer_instance
    have : Subsingleton (sigmaModel p e a N) := by
      unfold sigmaModel
      infer_instance
    exact isCyclic_of_subsingleton
  · have h1' : N / e = 1 := le_antisymm h h1
    have hd : Nat.digits p (N / e) = [1] := by
      rw [h1']; exact Nat.digits_of_lt p 1 one_ne_zero hp.out.one_lt
    have hlen : (Nat.digits p (N / e)).length = 1 := by rw [hd]; rfl
    let i₀ : Fin (Nat.digits p (N / e)).length := ⟨0, by omega⟩
    have hi₀ : (Nat.digits p (N / e))[i₀] = 1 := by simp [i₀, hd]
    let j₀ : Fin ((Nat.digits p (N / e))[i₀]) := ⟨0, by rw [hi₀]; exact one_pos⟩
    let ev : sigmaModel p e a N →* Multiplicative (ZMod (p ^ a)) :=
      (Pi.evalMonoidHom (fun _ : Fin ((Nat.digits p (N / e))[i₀]) =>
        wreathTower p (Multiplicative (ZMod (p ^ a))) i₀) j₀).comp
        (Pi.evalMonoidHom (fun i : Fin (Nat.digits p (N / e)).length =>
          Fin ((Nat.digits p (N / e))[i]) →
            wreathTower p (Multiplicative (ZMod (p ^ a))) i) i₀)
    have hinj : Function.Injective ev := by
      intro f g hfg
      funext i j
      obtain rfl : i = i₀ := Fin.ext (by have := i.2; show (i : ℕ) = 0; omega)
      obtain rfl : j = j₀ := Fin.ext (by have := j.2; show (j : ℕ) = 0; omega)
      exact hfg
    exact isCyclic_of_injective ev hinj

theorem pRank_le_one_of_injective {H G : Type} [Group H] [Finite H] [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (ι : H →* G) (hι : Function.Injective ι) (h : ∀ P : Sylow p G, IsCyclic P) :
    CFSG.pRank p H ≤ 1 := by
  refine K128.pRank_le_one_of_cyclic_pSubgroups hp.out fun S hS => ?_
  have hS' : IsPGroup p ↥(S.map ι) := hS.map ι
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  have hQc : IsCyclic ↥(S.map ι) := by
    have : IsCyclic (Q : Subgroup G) := h Q
    exact Subgroup.isCyclic_of_le hQ
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective S ι hι)).2 hQc

open CFSG.GroupTheory.WeirSylow in
theorem sylow_cyclic_Sp {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (h : (if Even (orderOf (Nat.card K : ZMod p)) then 2 * n else n) /
      orderOf (Nat.card K : ZMod p) ≤ 1) : ∀ P : Sylow p (StatedSp n K), IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  intro P
  obtain ⟨e⟩ := sylow_Sp (hp.odd_of_ne_two hp2) K (by rwa [hcard]) n P
  rw [hcard] at e
  exact (MulEquiv.isCyclic e).2 (isCyclic_sigmaModel_of_div_le_one h)

theorem pRank_statedSp_le_one {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (h : (if Even (orderOf (Nat.card K : ZMod p)) then 2 * n else n) /
      orderOf (Nat.card K : ZMod p) ≤ 1) : CFSG.pRank p ↥(StatedSp n K) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact K128.pRank_le_one_of_cyclic_sylow (sylow_cyclic_Sp hp hp2 hpK h)

noncomputable def topQuotEquiv {T : Type} [Group T] (hZ : Subgroup.center T = ⊥) :
    ↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T) ≃* T :=
  (centerQuotientCongr Subgroup.topEquiv).trans (centerQuotientEquivSelf hZ)

theorem false_of_row {r : ℕ} (hrow : KF122Row r) {T : Type} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hZ : Subgroup.center T = ⊥)
    (hmodel : RowModel p (⊤ : Subgroup T) r) (hLR2 : LocalRankLeTwo p T) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hLRA : LocalRankAut p T α) : False := by
  have ε := topQuotEquiv hZ
  refine hrow T p ⊤ hp hp5 hmodel (localRankLeTwo_of_mulEquiv ε.symm hp hLR2)
    (MulAut.congr ε.symm α) ?_ ?_ (localRankAut_congr ε.symm hp hLRA)
  · rw [← map_pow, hαp, map_one]
  · exact fun h => hαinn ((mem_innerAut_congr ε.symm α).1 h)

theorem card_ker_dvd_multiplier_cls {J T : Type} [Group J] [Finite J] [Group T] [Finite T]
    (hq : CFSG.IsQuasisimple J) (π : J →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {t : StatedLieTag} {n f : ℕ} (hm : Models.LieModel T t n 2 f) :
    Nat.card π.ker ∣ Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hd := card_ker_dvd_card_hopfMultiplier hperf hq.1 π hπ hker
  rwa [hcard] at hd

theorem isPerfect_fixRes {T : Type} [Group T] [Finite T] (α : MulAut T) :
    Group.IsPerfect ↥(fixRes α) := by
  have hperfR : Group.IsPerfect (perfectResidual ↥(fixSub α)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.equivMapOfInjective (perfectResidual ↥(fixSub α)) (fixSub α).subtype
      (fixSub α).subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective (perfectResidual ↥(fixSub α)) (fixSub α).subtype
      (fixSub α).subtype_injective).surjective

theorem card_center_fixRes_dvd {T : Type} [Group T] [Finite T] (α : MulAut T)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {t : StatedLieTag} {n f : ℕ}
    (hm : Models.LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) t n 2 f) :
    Nat.card (Subgroup.center ↥(fixRes α)) ∣ Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have := isPerfect_fixRes α
  have hd := card_ker_dvd_card_hopfMultiplier hperf (isPerfect_fixRes α)
    (QuotientGroup.mk' (Subgroup.center ↥(fixRes α))) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk', hcard] at hd

theorem sylowShape_of_center_quotient {p r e : ℕ} (hp : p.Prime) {N : Type} [Group N] [Finite N]
    (hZ : ¬ p ∣ Nat.card (Subgroup.center N))
    (h : SylowShape p r e (N ⧸ Subgroup.center N)) : SylowShape p r e N :=
  fun _ hS hidx => K1214.SylowShape.exists_equiv hp (Subgroup.center N) hZ h hS hidx

theorem three_le_orderOf_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) (h1 : ¬ p ∣ q - 1)
    (h2 : ¬ p ∣ q + 1) (hq1 : 1 ≤ q) : 3 ≤ orderOf (q : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hne1 : (q : ZMod p) ≠ 1 := fun h => h1 (by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h]; simp)
  have hnem1 : (q : ZMod p) ≠ -1 := fun h => h2 (by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [h]; exact neg_add_cancel _)
  have hpos : 0 < orderOf (q : ZMod p) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, ZMod.pow_card_sub_one_eq_one hq0⟩)
  by_contra hlt
  push Not at hlt
  have hcase : orderOf (q : ZMod p) = 1 ∨ orderOf (q : ZMod p) = 2 := by omega
  rcases hcase with h | h
  · exact hne1 (orderOf_eq_one_iff.1 h)
  · have h2' : (q : ZMod p) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    have : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by ring_nf; rw [h2']; ring
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hne1 (sub_eq_zero.1 h3)
    · exact hnem1 (eq_neg_of_add_eq_zero_left h3)

theorem statedClassicalModel_of_lieModel_tags {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : Blueprint.LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h
    (by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

end CFSG.RankThree.PartOne
