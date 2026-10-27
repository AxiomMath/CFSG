module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Permutation.FiveTransitive.Reduction
public import CFSG.Permutation.FiveTransitive.HallSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.Research.HallLargeDegreeReduced

open MulAction Subgroup
open scoped Pointwise
open Research.HallSylowNormalizer

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem normalizer_le_fixedSetStabilizer (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      MulAction.stabilizer G (MulAction.fixedPoints P X : Set X) := by
  classical
  intro n hn
  rw [MulAction.mem_stabilizer_set'
    (Set.toFinite (MulAction.fixedPoints P X : Set X))]
  intro x hx
  rw [MulAction.mem_fixedPoints] at hx ⊢
  intro r
  have hconj : n⁻¹ * (r : G) * n ∈ P :=
    (Subgroup.mem_normalizer_iff''.mp hn (r : G)).mp r.prop
  let r' : P := ⟨n⁻¹ * (r : G) * n, hconj⟩
  change (r : G) • (n • x) = n • x
  calc
    (r : G) • (n • x) = ((r : G) * n) • x :=
      (mul_smul (r : G) n x).symm
    _ = (n * (r' : G)) • x := by
      congr 1
      dsimp only [r']
      group
    _ = n • ((r' : G) • x) := mul_smul n (r' : G) x
    _ = n • x := congrArg (fun y : X => n • y) (hx r')

def normalizerToFixedSetStabilizer (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) →*
      MulAction.stabilizer G (MulAction.fixedPoints P X : Set X) :=
  Subgroup.inclusion (normalizer_le_fixedSetStabilizer (X := X) P)

noncomputable def normalizerFixedActionHom (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) →*
      Equiv.Perm (MulAction.fixedPoints P X) :=
  (MulAction.toPermHom
    (MulAction.stabilizer G (MulAction.fixedPoints P X : Set X))
    (MulAction.fixedPoints P X)).comp
      (normalizerToFixedSetStabilizer (X := X) P)

@[simp] theorem normalizerFixedActionHom_apply_val
    (P : Subgroup G) (n : Subgroup.normalizer (P : Set G))
    (x : MulAction.fixedPoints P X) :
    ((normalizerFixedActionHom (X := X) P n) x : X) =
      (n : G) • (x : X) := by
  change
    (((normalizerToFixedSetStabilizer (X := X) P n) • x :
      MulAction.fixedPoints P X) : X) = (n : G) • (x : X)
  rw [SMul.smul_stabilizer_def]
  rfl

private theorem normalizer_fixedAction_range_isMultiplyPretransitive
    {p k : ℕ} [Fact p.Prime]
    (htrans : MulAction.IsMultiplyPretransitive G X k)
    (e : Fin k ↪ X) (Q : Sylow p (MulAction.stabilizer G e)) :
    MulAction.IsMultiplyPretransitive
      (normalizerFixedActionHom (X := X) (ambientSylow e Q)).range
      (MulAction.fixedPoints (ambientSylow e Q) X) k := by
  classical
  let P : Subgroup G := ambientSylow e Q
  let rho := normalizerFixedActionHom (X := X) P
  rw [MulAction.isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨z, hzN, hz⟩ :=
    exists_mem_normalizer_ambientSylow_maps htrans e Q a b
  let n : Subgroup.normalizer (P : Set G) := ⟨z, hzN⟩
  refine ⟨⟨rho n, ⟨n, rfl⟩⟩, ?_⟩
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  simpa [P, rho, Function.Embedding.smul_apply, Subgroup.smul_def,
    Equiv.Perm.smul_def] using hz i

private theorem alternatingGroup_le_normalizer_fixedAction_of_card_six
    {p : ℕ} [Fact p.Prime]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) (Q : Sylow p (MulAction.stabilizer G e))
    [Fintype (MulAction.fixedPoints (ambientSylow e Q) X)]
    [DecidableEq (MulAction.fixedPoints (ambientSylow e Q) X)]
    (hfixed : Nat.card (MulAction.fixedPoints (ambientSylow e Q) X) = 6) :
    alternatingGroup (MulAction.fixedPoints (ambientSylow e Q) X) ≤
      (normalizerFixedActionHom (X := X) (ambientSylow e Q)).range := by
  classical
  let F := MulAction.fixedPoints (ambientSylow e Q) X
  have hfour :=
    normalizer_fixedAction_range_isMultiplyPretransitive h4 e Q
  have hfixed' : Nat.card F = 6 := by
    simpa only [F] using hfixed
  have hdegree : Nat.card F - 2 = 4 := by omega
  apply IsMultiplyPretransitive.alternatingGroup_le
  simpa only [F, hdegree] using hfour

private theorem alternatingGroup_le_of_index_lt_card
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (J : Subgroup (Equiv.Perm Y))
    (hfive : 5 ≤ Nat.card Y)
    (hindex : J.index < Nat.card Y) :
    alternatingGroup Y ≤ J := by
  classical
  by_cases hcore : J.normalCore = ⊥
  · have hdvd : J.normalCore.index ∣ J.index.factorial := by
      rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker,
        Subgroup.index_eq_card, ← Nat.card_perm]
      exact Subgroup.card_subgroup_dvd_card
        (MulAction.toPermHom
          (Equiv.Perm Y) ((Equiv.Perm Y) ⧸ J)).range
    have hfactorialDvd :
        (Nat.card Y).factorial ∣ J.index.factorial := by
      rw [hcore, Subgroup.index_bot, Nat.card_perm] at hdvd
      exact hdvd
    have hfactorialLe :
        (Nat.card Y).factorial ≤ J.index.factorial :=
      Nat.le_of_dvd (Nat.factorial_pos _) hfactorialDvd
    have hfactorialLt :
        J.index.factorial < (Nat.card Y).factorial :=
      Nat.factorial_lt_of_lt
        (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hindex
    omega
  · have hcoreNontrivial : Nontrivial J.normalCore :=
      J.normalCore.nontrivial_iff_ne_bot.mpr hcore
    exact
      (Equiv.Perm.alternatingGroup_le_of_normal hfive
        (N := J.normalCore) hcoreNontrivial).trans J.normalCore_le

private theorem alternatingGroup_le_of_four_transitive_card_seven
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (J : Subgroup (Equiv.Perm Y))
    (hcard : Nat.card Y = 7)
    (hfour : MulAction.IsMultiplyPretransitive J Y 4) :
    alternatingGroup Y ≤ J := by
  have hcard' : Fintype.card Y = 7 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hfourLe : 4 ≤ Fintype.card Y := by omega
  have hdvd : (Fintype.card Y).descFactorial 4 ∣ Nat.card J :=
    FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive
      J Y 4 hfourLe hfour
  have hJlower : 840 ≤ Nat.card J := by
    have hdiv : 840 ∣ Nat.card J := by
      simpa [hcard', Nat.descFactorial] using hdvd
    exact Nat.le_of_dvd Nat.card_pos hdiv
  have hproduct := J.index_mul_card
  have hpermCard : Nat.card (Equiv.Perm Y) = 5040 := by
    rw [Nat.card_perm, hcard]
    norm_num [Nat.factorial]
  rw [hpermCard] at hproduct
  have hindexLe : J.index ≤ 6 := by
    nlinarith
  apply alternatingGroup_le_of_index_lt_card Y J (by omega)
  omega

private theorem alternatingGroup_le_normalizer_fixedAction_of_card_seven
    {p : ℕ} [Fact p.Prime]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) (Q : Sylow p (MulAction.stabilizer G e))
    [Fintype (MulAction.fixedPoints (ambientSylow e Q) X)]
    [DecidableEq (MulAction.fixedPoints (ambientSylow e Q) X)]
    (hfixed : Nat.card (MulAction.fixedPoints (ambientSylow e Q) X) = 7) :
    alternatingGroup (MulAction.fixedPoints (ambientSylow e Q) X) ≤
      (normalizerFixedActionHom (X := X) (ambientSylow e Q)).range := by
  let F := MulAction.fixedPoints (ambientSylow e Q) X
  apply alternatingGroup_le_of_four_transitive_card_seven F
    (normalizerFixedActionHom (X := X) (ambientSylow e Q)).range
  · simpa only [F] using hfixed
  · exact normalizer_fixedAction_range_isMultiplyPretransitive h4 e Q

private theorem exists_normalizer_correction_to_swap
    (P : Subgroup G)
    [Fintype (MulAction.fixedPoints P X)]
    [DecidableEq (MulAction.fixedPoints P X)]
    (hAlt :
      alternatingGroup (MulAction.fixedPoints P X) ≤
        (normalizerFixedActionHom (X := X) P).range)
    (u : MulAction.stabilizer G (MulAction.fixedPoints P X : Set X))
    (huOdd : Equiv.Perm.sign
      (MulAction.toPermHom
        (MulAction.stabilizer G (MulAction.fixedPoints P X : Set X))
        (MulAction.fixedPoints P X) u) = -1)
    (x y : MulAction.fixedPoints P X) (hxy : x ≠ y) :
    ∃ n : Subgroup.normalizer (P : Set G),
      MulAction.toPermHom
          (MulAction.stabilizer G (MulAction.fixedPoints P X : Set X))
          (MulAction.fixedPoints P X)
          (normalizerToFixedSetStabilizer (X := X) P n * u) =
        Equiv.swap x y := by
  classical
  let K := MulAction.stabilizer G (MulAction.fixedPoints P X : Set X)
  let rhoK : K →* Equiv.Perm (MulAction.fixedPoints P X) :=
    MulAction.toPermHom K (MulAction.fixedPoints P X)
  let tau : Equiv.Perm (MulAction.fixedPoints P X) := Equiv.swap x y
  let c : Equiv.Perm (MulAction.fixedPoints P X) := tau * (rhoK u)⁻¹
  have htauOdd : Equiv.Perm.sign tau = -1 := by
    exact Equiv.Perm.sign_swap hxy
  have huOdd' : Equiv.Perm.sign (rhoK u) = -1 := by
    simpa only [rhoK, K] using huOdd
  have hcAlt : c ∈ alternatingGroup (MulAction.fixedPoints P X) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp only [c, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
      htauOdd, huOdd']
    simp
  obtain ⟨n, hn⟩ := hAlt hcAlt
  refine ⟨n, ?_⟩
  change rhoK (normalizerToFixedSetStabilizer (X := X) P n * u) = tau
  rw [map_mul]
  change normalizerFixedActionHom (X := X) P n * rhoK u = tau
  rw [hn]
  dsimp only [c]
  group

private theorem false_of_alternating_normalizer_and_odd_setwise_lift
    (e : Fin 4 ↪ X) (P : Subgroup G)
    [Fintype (MulAction.fixedPoints P X)]
    [DecidableEq (MulAction.fixedPoints P X)]
    (hPbase : P ≤ MulAction.stabilizer G e)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (hAlt :
      alternatingGroup (MulAction.fixedPoints P X) ≤
        (normalizerFixedActionHom (X := X) P).range)
    (u : MulAction.stabilizer G (MulAction.fixedPoints P X : Set X))
    (huOdd : Equiv.Perm.sign
      (MulAction.toPermHom
        (MulAction.stabilizer G (MulAction.fixedPoints P X : Set X))
        (MulAction.fixedPoints P X) u) = -1)
    (x y : MulAction.fixedPoints P X) (hxy : x ≠ y)
    (hxbase : ∀ i, e i ≠ (x : X))
    (hybase : ∀ i, e i ≠ (y : X)) : False := by
  classical
  let F := MulAction.fixedPoints P X
  let K := MulAction.stabilizer G (F : Set X)
  let rhoK : K →* Equiv.Perm F := MulAction.toPermHom K F
  obtain ⟨n, hn⟩ :=
    exists_normalizer_correction_to_swap (X := X) P hAlt u huOdd x y hxy
  let nK : K := normalizerToFixedSetStabilizer (X := X) P n
  let zK : K := nK * u
  have hzPerm : rhoK zK = Equiv.swap x y := by
    simpa only [F, K, rhoK, nK, zK] using hn
  have heFixed (i : Fin 4) : e i ∈ F := by
    rw [MulAction.mem_fixedPoints]
    intro r
    have hr := hPbase r.prop
    rw [MulAction.mem_stabilizer_iff] at hr
    have hi := congrArg (fun a : Fin 4 ↪ X => a i) hr
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def] using hi
  let eF : Fin 4 → F := fun i => ⟨e i, heFixed i⟩
  have hzFix (i : Fin 4) : (zK : G) • e i = e i := by
    have heFx : eF i ≠ x := by
      intro h
      exact hxbase i (congrArg Subtype.val h)
    have heFy : eF i ≠ y := by
      intro h
      exact hybase i (congrArg Subtype.val h)
    have hswap : Equiv.swap x y (eF i) = eF i :=
      Equiv.swap_apply_of_ne_of_ne heFx heFy
    have happ := congrArg
      (fun q : Equiv.Perm F => q (eF i)) hzPerm
    have hfixF : rhoK zK (eF i) = eF i := happ.trans hswap
    have hval := congrArg Subtype.val hfixF
    simpa [rhoK, F, K, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, SMul.smul_stabilizer_def] using hval
  have hzMem : (zK : G) ∈ MulAction.stabilizer G e := by
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    exact hzFix
  have hswapOrder : orderOf (Equiv.swap x y) = 2 :=
    (Equiv.Perm.swap_isSwap_iff.mpr hxy).orderOf
  have htwoOrderK : 2 ∣ orderOf zK := by
    rw [← hswapOrder, ← hzPerm]
    exact orderOf_map_dvd rhoK zK
  have htwoOrderG : 2 ∣ orderOf (zK : G) := by
    rw [Subgroup.orderOf_coe]
    exact htwoOrderK
  have htwoCard : 2 ∣ Nat.card (MulAction.stabilizer G e) :=
    htwoOrderG.trans
      ((MulAction.stabilizer G e).orderOf_dvd_natCard hzMem)
  exact hodd.not_two_dvd_nat htwoCard

theorem false_of_ambientSylow_fixed_card_six_and_odd_setwise_lift
    {p : ℕ} [Fact p.Prime]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) (Q : Sylow p (MulAction.stabilizer G e))
    [Fintype (MulAction.fixedPoints (ambientSylow e Q) X)]
    [DecidableEq (MulAction.fixedPoints (ambientSylow e Q) X)]
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (hfixed : Nat.card (MulAction.fixedPoints (ambientSylow e Q) X) = 6)
    (u : MulAction.stabilizer G
      (MulAction.fixedPoints (ambientSylow e Q) X : Set X))
    (huOdd : Equiv.Perm.sign
      (MulAction.toPermHom
        (MulAction.stabilizer G
          (MulAction.fixedPoints (ambientSylow e Q) X : Set X))
        (MulAction.fixedPoints (ambientSylow e Q) X) u) = -1)
    (x y : MulAction.fixedPoints (ambientSylow e Q) X) (hxy : x ≠ y)
    (hxbase : ∀ i, e i ≠ (x : X))
    (hybase : ∀ i, e i ≠ (y : X)) : False := by
  classical
  apply false_of_alternating_normalizer_and_odd_setwise_lift
    (X := X) e (ambientSylow e Q)
    (ambientSylow_le_stabilizer e Q) hodd
    (alternatingGroup_le_normalizer_fixedAction_of_card_six
      h4 e Q hfixed)
    u huOdd x y hxy hxbase hybase

theorem false_of_ambientSylow_fixed_card_seven_and_odd_setwise_lift
    {p : ℕ} [Fact p.Prime]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) (Q : Sylow p (MulAction.stabilizer G e))
    [Fintype (MulAction.fixedPoints (ambientSylow e Q) X)]
    [DecidableEq (MulAction.fixedPoints (ambientSylow e Q) X)]
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (hfixed : Nat.card (MulAction.fixedPoints (ambientSylow e Q) X) = 7)
    (u : MulAction.stabilizer G
      (MulAction.fixedPoints (ambientSylow e Q) X : Set X))
    (huOdd : Equiv.Perm.sign
      (MulAction.toPermHom
        (MulAction.stabilizer G
          (MulAction.fixedPoints (ambientSylow e Q) X : Set X))
        (MulAction.fixedPoints (ambientSylow e Q) X) u) = -1)
    (x y : MulAction.fixedPoints (ambientSylow e Q) X) (hxy : x ≠ y)
    (hxbase : ∀ i, e i ≠ (x : X))
    (hybase : ∀ i, e i ≠ (y : X)) : False := by
  classical
  apply false_of_alternating_normalizer_and_odd_setwise_lift
    (X := X) e (ambientSylow e Q)
    (ambientSylow_le_stabilizer e Q) hodd
    (alternatingGroup_le_normalizer_fixedAction_of_card_seven
      h4 e Q hfixed)
    u huOdd x y hxy hxbase hybase

end FiveTransitive.Research.HallLargeDegreeReduced

end CFSG
