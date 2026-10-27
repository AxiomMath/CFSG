module

public import CFSG.Permutation.FiveTransitive.Degree24DoubleEleven

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem order_eleven_centralizer_card_ne_forty_four
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 11) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) ≠ 44 := by
  classical
  let g : Equiv.Perm X := u
  have hgCycleType : g.cycleType = {11, 11} := by
    simpa only [g] using
      order_eleven_cycleType_eq_double
        X P hcard h5 hnotAlt u huorder
  have hgSupport : g.support.card = 22 := by
    rw [← Equiv.Perm.sum_cycleType, hgCycleType]
    norm_num
  have hgFixed :
      Fintype.card (Function.fixedPoints g) = 2 := by
    have hfixed := Equiv.Perm.card_fixedPoints g
    rw [Equiv.Perm.sum_cycleType, hcard, hgSupport] at hfixed
    omega
  let e : Function.fixedPoints g ≃ Fin 2 :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin]
      exact hgFixed)
  let x : X := (e.symm 0).1
  let y : X := (e.symm 1).1
  have hx : g x = x :=
    (e.symm 0).2
  have hy : g y = y :=
    (e.symm 1).2
  have hxy : x ≠ y := by
    intro h
    have heq : e.symm 0 = e.symm 1 :=
      Subtype.ext h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (e.symm.injective heq)
  let w₀Perm : Equiv.Perm X := Equiv.swap x y
  have hw₀Swap : w₀Perm.IsSwap :=
    ⟨x, y, hxy, rfl⟩
  have hw₀Commute : Commute w₀Perm g := by
    rw [Commute]
    apply Equiv.ext
    intro z
    by_cases hzx : z = x
    · subst z
      simp [w₀Perm, hx, hy]
    · by_cases hzy : z = y
      · subst z
        simp [w₀Perm, hx, hy]
      · have hgzx : g z ≠ x := by
          intro hz
          apply hzx
          exact g.injective (hz.trans hx.symm)
        have hgzy : g z ≠ y := by
          intro hz
          apply hzy
          exact g.injective (hz.trans hy.symm)
        change
          Equiv.swap x y (g z) =
            g (Equiv.swap x y z)
        rw [Equiv.swap_apply_of_ne_of_ne hgzx hgzy,
          Equiv.swap_apply_of_ne_of_ne hzx hzy]
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  let Cfull : Subgroup (Equiv.Perm X) :=
    Subgroup.centralizer ({g} : Set (Equiv.Perm X))
  have hCfullCard : Nat.card Cfull = 484 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgCycleType, hcard]
    norm_num
  intro hCcard
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let T : Sylow 2 C := Sylow.nonempty.some
  have hTcard : Nat.card T = 4 := by
    rw [T.card_eq_multiplicity, hCcard,
      show 44 = 2 ^ 2 * 11 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 2 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let inclusion : T →* Cfull := {
    toFun := fun t =>
      ⟨((t.1.1 : P) : Equiv.Perm X), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp t.1.prop)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact
      congrArg
        (fun z : Cfull => (z : Equiv.Perm X)) hab
  let R : Subgroup Cfull := inclusion.range
  have hRcard : Nat.card R = 4 := by
    calc
      Nat.card R = Nat.card T :=
        Nat.card_congr
          (MonoidHom.ofInjective hinclusion).toEquiv.symm
      _ = 4 := hTcard
  have hRmax :
      Nat.card R =
        2 ^ (Nat.card Cfull).factorization 2 := by
    rw [hRcard, hCfullCard,
      show 484 = 2 ^ 2 * 121 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 2 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let Q : Sylow 2 Cfull :=
    Sylow.ofCard R hRmax
  let w₀ : Cfull :=
    ⟨w₀Perm, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hw₀Commute⟩
  have hw₀order : orderOf w₀ = 2 := by
    calc
      orderOf w₀ =
          orderOf (w₀ : Equiv.Perm X) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf w₀Perm := rfl
      _ = 2 := hw₀Swap.orderOf
  let A : Subgroup Cfull :=
    Subgroup.zpowers w₀
  have hAcard : Nat.card A = 2 := by
    rw [Nat.card_zpowers, hw₀order]
  have hAisP : IsPGroup 2 A := by
    apply IsPGroup.of_card
    rw [hAcard, pow_one]
  obtain ⟨Q₀, hAQ₀⟩ :=
    hAisP.exists_le_sylow
  have hw₀Q₀ : w₀ ∈ (Q₀ : Subgroup Cfull) :=
    hAQ₀ (Subgroup.mem_zpowers w₀)
  obtain ⟨q, hq⟩ :=
    exists_smul_eq Cfull Q Q₀
  have hqInv : q⁻¹ • Q₀ = Q :=
    inv_smul_eq_iff.mpr hq.symm
  let w : Cfull :=
    MulAut.conj q⁻¹ w₀
  have hwConjugate :
      w ∈ (q⁻¹ • Q₀ : Sylow 2 Cfull) := by
    change ∃ z ∈ (Q₀ : Subgroup Cfull),
      MulAut.conj q⁻¹ z = w
    exact ⟨w₀, hw₀Q₀, rfl⟩
  have hwQ : w ∈ (Q : Subgroup Cfull) := by
    rwa [hqInv] at hwConjugate
  have hwRange : w ∈ R :=
    hwQ
  obtain ⟨t, ht⟩ := hwRange
  let wPerm : Equiv.Perm X := w
  have hwPermP : wPerm ∈ P := by
    have htPerm :=
      congrArg
        (fun z : Cfull => (z : Equiv.Perm X)) ht
    change (w : Equiv.Perm X) ∈ P
    rw [← htPerm]
    exact t.1.1.prop
  have hwPermSupport :
      wPerm.support.card = 2 := by
    calc
      wPerm.support.card = w₀Perm.support.card := by
        change
          (((q⁻¹ : Cfull) : Equiv.Perm X) *
            w₀Perm *
            (((q⁻¹ : Cfull) : Equiv.Perm X))⁻¹).support.card =
              w₀Perm.support.card
        rw [Equiv.Perm.card_support_conj]
      _ = 2 := Equiv.Perm.card_support_swap hxy
  have hwPermNe : wPerm ≠ 1 := by
    intro hw
    rw [hw] at hwPermSupport
    simp at hwPermSupport
  exact hnotAlt
    (alternatingGroup_le_of_nontrivial_support_le_seven
      X P hcard h5 hwPermP hwPermNe (by omega))

theorem five_point_stabilizer_card_ne_eleven_residue_five_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcases :
      Nat.card (fixingSubgroup P s) = 324 ∨
      Nat.card (fixingSubgroup P s) = 2304 ∨
      Nat.card (fixingSubgroup P s) = 27648) :
    False := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hh : h ≠ 0 := Nat.card_pos.ne'
  have hcases :
      h = 324 ∨ h = 2304 ∨ h = 27648 := by
    simpa only [H, h] using hHcases
  have hnotEleven : ¬11 ∣ h := by
    rcases hcases with hcase | hcase | hcase
    all_goals rw [hcase]
    all_goals norm_num
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 5100480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hPfactorization :
      (5100480 * h).factorization 11 = 1 := by
    rw [show 5100480 = 11 * 463680 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotEleven]
    norm_num
  let S : Sylow 11 P := Sylow.nonempty.some
  have hScard : Nat.card S = 11 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  have hnotElevenSqP : ¬11 ^ 2 ∣ Nat.card P := by
    intro hdvd
    have hge :
        2 ≤ (Nat.card P).factorization 11 :=
      (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
        (Nat.card_pos.ne') |>.mp hdvd
    rw [hPcard, hPfactorization] at hge
    omega
  let C : Subgroup P :=
    Subgroup.centralizer ((S : Subgroup P) : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer ((S : Subgroup P) : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  have hconstraints :
      c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
        N.index % 11 = 1 ∧
        c * r * N.index * 11 = Nat.card P := by
    simpa only [C, N, c, r] using
      sylow_eleven_normalizer_constraints
        X P hcard h5 hnotAlt hnotElevenSqP S hScard
  have hdivided :
      c * r * N.index = 463680 * h := by
    rw [hPcard] at hconstraints
    nlinarith [hconstraints.2.2.2.2.2]
  have hmod :
      (8 * h) % 11 = (c * r) % 11 := by
    calc
      (8 * h) % 11 = (463680 * h) % 11 := by
        simp [Nat.mul_mod]
      _ = (c * r * N.index) % 11 :=
        congrArg (fun n => n % 11) hdivided.symm
      _ = (c * r) % 11 := by
        rw [Nat.mul_mod, hconstraints.2.2.2.2.1]
        simp
  have hcLe : c ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hconstraints.1
  have hrLe : r ≤ 10 :=
    Nat.le_of_dvd (by norm_num) hconstraints.2.1
  have hcCases : c = 1 ∨ c = 2 ∨ c = 4 := by
    interval_cases c
    all_goals try norm_num at hconstraints
    all_goals omega
  have hrCases :
      r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 10 := by
    interval_cases r
    all_goals try norm_num at hconstraints
    all_goals omega
  have hc : c = 4 := by
    rcases hcCases with hc | hc | hc
    all_goals rcases hrCases with hr | hr | hr | hr
    all_goals rcases hcases with hhcase | hhcase | hhcase
    all_goals rw [hc, hr, hhcase] at hmod
    all_goals norm_num at hmod
    all_goals omega
  have hSleC : (S : Subgroup P) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hSsubCard :
      Nat.card ((S : Subgroup P).subgroupOf C) = 11 := by
    calc
      Nat.card ((S : Subgroup P).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 11 := hScard
  have hCcardRaw :=
    ((S : Subgroup P).subgroupOf C).index_mul_card
  have hCcard : Nat.card C = 44 := by
    have hcCard :
        c * 11 = Nat.card C := by
      dsimp only [c]
      change
        ((S : Subgroup P).subgroupOf C).index * 11 =
          Nat.card C
      calc
        ((S : Subgroup P).subgroupOf C).index * 11 =
            ((S : Subgroup P).subgroupOf C).index *
              Nat.card ((S : Subgroup P).subgroupOf C) :=
          congrArg
            (((S : Subgroup P).subgroupOf C).index * ·)
            hSsubCard.symm
        _ = Nat.card C := hCcardRaw
    rw [hc] at hcCard
    norm_num at hcCard
    simpa only [Nat.card_eq_fintype_card] using hcCard.symm
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorderS : orderOf u = 11 :=
    huRaw.trans hScard
  have huorderP : orderOf (u : P) = 11 := by
    calc
      orderOf (u : P) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 11 := huorderS
  let Cu : Subgroup P :=
    Subgroup.centralizer ({(u : P)} : Set P)
  have hCLeCu : C ≤ Cu := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz u u.prop).symm
  have hCdvdCu : Nat.card C ∣ Nat.card Cu :=
    Subgroup.card_dvd_of_le hCLeCu
  have hCudvdFourEightyFour : Nat.card Cu ∣ 484 := by
    simpa only [Cu] using
      order_eleven_centralizer_card_dvd_fourHundredEightyFour
        X P hcard h5 hnotAlt (u : P) huorderP
  have hCuP : Nat.card Cu ∣ Nat.card P :=
    Subgroup.card_subgroup_dvd_card Cu
  have hnotElevenSqCu : ¬121 ∣ Nat.card Cu := by
    intro hdvd
    exact hnotElevenSqP (hdvd.trans hCuP)
  have hCudvd : Nat.card Cu ∣ 44 :=
    dvd_fortyFour_of_dvd_fourHundredEightyFour
      hCudvdFourEightyFour hnotElevenSqCu
  have hCuCard : Nat.card Cu = 44 := by
    apply Nat.dvd_antisymm hCudvd
    rw [← hCcard]
    exact hCdvdCu
  exact
    order_eleven_centralizer_card_ne_forty_four
      X P hcard h5 hnotAlt (u : P) huorderP
      (by simpa only [Cu] using hCuCard)

end FiveTransitive.Degree24

end CFSG
