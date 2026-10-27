module

public import CFSG.Monster.B.TwoA.Fischer.SliceOrder
public import CFSG.Monster.B.TwoA.Fischer.PrimitiveUnitary
public import CFSG.Monster.B.Generic.LocallyPrimitive
public import CFSG.GroupActions.PrimitiveNormal

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix MulAction
open scoped Pointwise

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem iterate_commutator_eq_map {G : Type*} [Group G] (R : Subgroup G) (n : ℕ) :
    (fun K : Subgroup G => ⁅K, K⁆)^[n] R = (derivedSeries R n).map R.subtype := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, derivedSeries_zero, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivedSeries_succ, Subgroup.map_commutator]

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem ediam_induce_le_two : ((sliceGraph lab Y).induce Y).ediam ≤ 2 := by
  rw [SimpleGraph.ediam_le_iff]
  intro y z
  by_contra h
  obtain ⟨hne, hnadj, hempty⟩ := SimpleGraph.two_lt_edist_iff.1 (not_le.1 h)
  have hc := hS.mu y y.2 z z.2 (fun e => hne (Subtype.ext e)) hnadj
  obtain ⟨w, hw⟩ : ((sliceGraph lab Y).commonNeighbors y z).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hc]; norm_num)
  have hw' := (sliceGraph lab Y).mem_commonNeighbors.1 hw
  have hmem : (⟨w, hw'.1.2.1⟩ : Y) ∈ ((sliceGraph lab Y).induce Y).commonNeighbors y z :=
    ((sliceGraph lab Y).induce Y).mem_commonNeighbors.2 ⟨hw'.1, hw'.2⟩
  rw [hempty] at hmem
  exact hmem

theorem exists_triangle (y z : Y) (h : ((sliceGraph lab Y).induce Y).Adj y z) :
    ∃ w, ((sliceGraph lab Y).induce Y).Adj y w ∧ ((sliceGraph lab Y).induce Y).Adj z w := by
  have hc := hS.lambda y z h
  obtain ⟨w, hw⟩ : ((sliceGraph lab Y).commonNeighbors y z).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hc]; norm_num)
  have hw' := (sliceGraph lab Y).mem_commonNeighbors.1 hw
  exact ⟨⟨w, hw'.1.2.1⟩, hw'.1, hw'.2⟩

theorem adj_smul_iff (a : sliceGroup lab Y) (y z : Y) :
    letI := hS.mulAction
    ((sliceGraph lab Y).induce Y).Adj (a • y) (a • z) ↔ ((sliceGraph lab Y).induce Y).Adj y z :=
  hS.adj_act_iff a.2 y z

theorem faithfulSMul :
    letI := hS.mulAction
    FaithfulSMul (sliceGroup lab Y) Y := by
  let _ := hS.mulAction
  exact ⟨fun h => hS.slicePerm_injective (Equiv.ext h)⟩

theorem isPreprimitive_local (x : Y) :
    letI := hS.mulAction
    IsPreprimitive (stabilizer (stabilizer (sliceGroup lab Y) x)
      (((sliceGraph lab Y).induce Y).neighborSet x))
      (((sliceGraph lab Y).induce Y).neighborSet x) := by
  let _ := hS.mulAction
  let _ := MulAction.compHom IsoPt projAct
  obtain ⟨L⟩ := hS.nonempty_localChart x.2
  let X := (sliceGraph lab Y).induce Y
  let N := stabilizer (stabilizer (sliceGroup lab Y) x) (X.neighborSet x)
  have hmem : ∀ n : N, (((n : stabilizer (sliceGroup lab Y) x) : sliceGroup lab Y) : S) ∈
      sliceStab act lab Y x := fun n =>
    ⟨((n : stabilizer (sliceGroup lab Y) x) : sliceGroup lab Y).2,
      congrArg Subtype.val (mem_stabilizer_iff.1 (n : stabilizer (sliceGroup lab Y) x).2)⟩
  let φ' : N → ProjSU := fun n => L.φ ⟨_, hmem n⟩
  have hφ' : Function.Surjective φ' := by
    intro m
    obtain ⟨a, rfl⟩ := L.surj m
    have ha1 : (⟨a, a.2.1⟩ : sliceGroup lab Y) ∈ stabilizer (sliceGroup lab Y) x :=
      Subtype.ext a.2.2
    have ha2 : (⟨_, ha1⟩ : stabilizer (sliceGroup lab Y) x) ∈ N := by
      rw [mem_stabilizer_iff]
      change (⟨a, a.2.1⟩ : sliceGroup lab Y) • X.neighborSet x = X.neighborSet x
      rw [← CFSG.Monster.B.Generic.neighborSet_smul_of_adj_smul_iff hS.adj_smul_iff,
        mem_stabilizer_iff.1 ha1]
    exact ⟨⟨_, ha2⟩, rfl⟩
  let f : X.neighborSet x →ₑ[φ'] IsoPt :=
    { toFun := fun z => L.τ ⟨z.1.1, z.2⟩
      map_smul' := fun n z => L.equivariant ⟨_, hmem n⟩ ⟨z.1.1, z.2⟩ _ rfl }
  have hf : Function.Bijective f := by
    let e : X.neighborSet x ≃ (sliceGraph lab Y).neighborSet x :=
      { toFun := fun z => ⟨z.1.1, z.2⟩
        invFun := fun z => ⟨⟨z.1, mem_of_mem_neighborSet z.2⟩, z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (e.trans L.τ).bijective
  exact (isPreprimitive_congr hφ' hf).2 isPreprimitive_projAct

theorem isPreprimitive :
    letI := hS.mulAction
    IsPreprimitive (sliceGroup lab Y) Y := by
  let _ := hS.mulAction
  have := hS.isPretransitive
  exact CFSG.Monster.B.Generic.locally_primitive_diameter_two_action
    ((sliceGraph lab Y).induce Y) hS.ediam_induce_le_two hS.exists_triangle hS.adj_smul_iff
    hS.isPreprimitive_local

theorem exists_mem_normal_act_eq {N : Subgroup (sliceGroup lab Y)} (hN : N.Normal)
    (hNbot : N ≠ ⊥) {y z : V} (hy : y ∈ Y) (hz : z ∈ Y) : ∃ n ∈ N, act (n : S) y = z := by
  let _ := hS.mulAction
  have := hS.faithfulSMul
  have := hS.isPreprimitive
  have : Nonempty Y := ⟨⟨y, hy⟩⟩
  have := CFSG.GroupActions.isPretransitive_of_normal_of_isPreprimitive
    (G := sliceGroup lab Y) (X := Y) hNbot
  obtain ⟨n, hn⟩ := exists_smul_eq N (⟨y, hy⟩ : Y) ⟨z, hz⟩
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

theorem dvd_card_of_normal {N : Subgroup (sliceGroup lab Y)} (hN : N.Normal) (hNbot : N ≠ ⊥) :
    3510 ∣ Nat.card N := by
  let _ := hS.mulAction
  obtain ⟨u, hu⟩ : Y.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hS.ncard]; norm_num)
  have horb : orbit N (⟨u, hu⟩ : Y) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨n, hn, hnz⟩ := hS.exists_mem_normal_act_eq hN hNbot hu z.2
    exact ⟨⟨n, hn⟩, Subtype.ext hnz⟩
  rw [← Nat.card_congr (orbitProdStabilizerEquivGroup N (⟨u, hu⟩ : Y)), Nat.card_prod, horb,
    Nat.card_congr (Equiv.Set.univ Y), Nat.card_coe_set_eq, hS.ncard]
  exact dvd_mul_right _ _

theorem eq_bot_of_isPGroup {p : ℕ} (hp : p.Prime) {N : Subgroup (sliceGroup lab Y)}
    (hN : N.Normal) (hP : IsPGroup p N) : N = ⊥ := by
  by_contra hNbot
  have := Fact.mk hp
  have := hS.finite_sliceGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hdvd := hS.dvd_card_of_normal hN hNbot
  rw [hk] at hdvd
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) hdvd))
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) hdvd))
  omega

theorem pCore_eq_bot {p : ℕ} (hp : p.Prime) : CFSG.pCore p (sliceGroup lab Y) = ⊥ :=
  sSup_eq_bot.2 fun _ hK => hS.eq_bot_of_isPGroup hp hK.1 hK.2

theorem eq_bot_of_normal_of_commute {A : Subgroup (sliceGroup lab Y)} (hA : A.Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  by_contra hAbot
  have := hS.finite_sliceGroup
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hAbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := A)).ne'
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpdvd
  let T : Subgroup (sliceGroup lab Y) :=
    { carrier := {g | g ∈ A ∧ g ^ p = 1}
      mul_mem' := fun {g h} hg hh => ⟨A.mul_mem hg.1 hh.1, by
        rw [Commute.mul_pow (hcomm g hg.1 h hh.1), hg.2, hh.2, one_mul]⟩
      one_mem' := ⟨A.one_mem, one_pow p⟩
      inv_mem' := fun {g} hg => ⟨A.inv_mem hg.1, by rw [inv_pow, hg.2, inv_one]⟩ }
  have hT : T.Normal := ⟨fun g hg h => ⟨hA.conj_mem g hg.1 h, by
    rw [conj_pow, hg.2, mul_one, mul_inv_cancel]⟩⟩
  have hTp : IsPGroup p T := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext g.2.2⟩
  have haT : (a : sliceGroup lab Y) ∈ T :=
    ⟨a.2, by rw [← Subgroup.coe_pow, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]⟩
  have hT1 := hS.eq_bot_of_isPGroup hp hT hTp
  rw [hT1, Subgroup.mem_bot] at haT
  have ha1 : a = 1 := Subtype.ext haT
  rw [ha1, orderOf_one] at ha
  exact hp.one_lt.ne ha

theorem eq_bot_of_normal_of_isSolvable {R : Subgroup (sliceGroup lab Y)} (hR : R.Normal)
    (hsol : Group.IsSolvable R) : R = ⊥ := by
  have key : ∀ n : ℕ, ∀ R : Subgroup (sliceGroup lab Y), R.Normal →
      (fun K : Subgroup (sliceGroup lab Y) => ⁅K, K⁆)^[n] R = ⊥ → R = ⊥ := by
    intro n
    induction n with
    | zero => exact fun R _ h => h
    | succ n ih =>
      intro R hR h
      rw [Function.iterate_succ_apply] at h
      have h1 := ih ⁅R, R⁆ (Subgroup.commutator_normal R R) h
      refine hS.eq_bot_of_normal_of_commute hR fun a ha b hb => ?_
      exact Subgroup.mem_centralizer_iff.1
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1) hb) a ha
  obtain ⟨n, hn⟩ := (Group.isSolvable_def R).1 hsol
  exact key n R hR (by rw [iterate_commutator_eq_map, hn, Subgroup.map_bot])

theorem primitive_and_radical_free :
    (letI := hS.mulAction; MulAction.IsPreprimitive (sliceGroup lab Y) Y) ∧
    (∀ N : Subgroup (sliceGroup lab Y), N.Normal → N ≠ ⊥ →
      ∀ y ∈ Y, ∀ z ∈ Y, ∃ n ∈ N, act (n : S) y = z) ∧
    (∀ N : Subgroup (sliceGroup lab Y), N.Normal → Group.IsSolvable N → N = ⊥) ∧
    ∀ p : ℕ, p.Prime → CFSG.pCore p (sliceGroup lab Y) = ⊥ :=
  ⟨hS.isPreprimitive, fun _ hN hNbot _ hy _ hz => hS.exists_mem_normal_act_eq hN hNbot hy hz,
    fun _ hN hsol => hS.eq_bot_of_normal_of_isSolvable hN hsol, fun _ hp => hS.pCore_eq_bot hp⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
