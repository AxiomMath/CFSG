module

public import CFSG.Permutation.FiveTransitive.Degree24FiveOrderIncidence

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction Subgroup

theorem card_order_five_elements_of_sylow_card_five
    (G : Type) [Group G] [Fintype G]
    (S : Sylow 5 G) (hScard : Nat.card S = 5) :
    Nat.card {u : G // orderOf u = 5} =
      Nat.card (Sylow 5 G) * 4 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A := Degree15.NonidentitySylowElements 5 G
  let B := {u : G // orderOf u = 5}
  let f : A → B :=
    fun a =>
      ⟨(a.2.1 : G), by
        calc
          orderOf (a.2.1 : G) =
              orderOf (a.2.1 : a.1) :=
            Subgroup.orderOf_coe _
          _ = 5 :=
            Degree15.orderOf_eq_prime_of_card_eq_prime
              (Degree15.sylow_card_eq_of_card_eq
                S hScard a.1) a.2.2⟩
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply
      Degree15.nonidentitySylowElementVal_injective
        S hScard
    simpa only [f,
      Degree15.nonidentitySylowElementVal] using
      congrArg Subtype.val hab
  have hfSurjective : Function.Surjective f := by
    intro u
    have huNe : u.1 ≠ 1 := by
      intro hu
      have huOrder := u.2
      rw [hu, orderOf_one] at huOrder
      norm_num at huOrder
    let R : Subgroup G := Subgroup.zpowers u.1
    have hRcard : Nat.card R = 5 := by
      rw [Nat.card_zpowers, u.2]
    have hRisP : IsPGroup 5 R := by
      apply IsPGroup.of_card (n := 1)
      rw [hRcard]
      norm_num
    obtain ⟨T, hRT⟩ := hRisP.exists_le_sylow
    let v : T :=
      ⟨u.1, hRT (Subgroup.mem_zpowers u.1)⟩
    have hvNe : v ≠ 1 := by
      intro hv
      apply huNe
      exact congrArg Subtype.val hv
    refine ⟨⟨T, ⟨v, hvNe⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hAcard :
      Nat.card A =
        Nat.card (Sylow 5 G) * 4 := by
    rw [Nat.card_eq_fintype_card]
    change
      Fintype.card
          (Degree15.NonidentitySylowElements 5 G) =
        Nat.card (Sylow 5 G) * 4
    rw [Degree15.card_nonidentitySylowElements
      S hScard, Nat.card_eq_fintype_card]
  calc
    Nat.card B = Nat.card A :=
      (Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)).symm
    _ = Nat.card (Sylow 5 G) * 4 := hAcard

private theorem four_dvd_card_orderFiveSupport_of_sylow_card_five
    (G X : Type) [Group G] [Fintype G]
    [Fintype X] [DecidableEq X]
    (ρ : G →* Equiv.Perm X)
    (S₀ : Sylow 5 G) (hS₀ : Nat.card S₀ = 5)
    (d : ℕ) :
    4 ∣
      Nat.card
        {u : G //
          orderOf u = 5 ∧
            (ρ u).support.card = d} := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A :=
    Σ S : Sylow 5 G,
      {u : S //
        u ≠ 1 ∧
          (ρ (u : G)).support.card = d}
  let B :=
    {u : G //
      orderOf u = 5 ∧
        (ρ u).support.card = d}
  let f : A → B :=
    fun a =>
      ⟨(a.2.1 : G),
        ⟨by
          calc
            orderOf (a.2.1 : G) =
                orderOf a.2.1 :=
              Subgroup.orderOf_coe _
            _ = 5 :=
              Degree15.orderOf_eq_prime_of_card_eq_prime
                (Degree15.sylow_card_eq_of_card_eq
                  S₀ hS₀ a.1) a.2.2.1,
        a.2.2.2⟩⟩
  have hfInjective : Function.Injective f := by
    rintro
      ⟨S, ⟨u, huNe, huSupport⟩⟩
      ⟨T, ⟨v, hvNe, hvSupport⟩⟩ hab
    have huvG : (u : G) = (v : G) := by
      simpa only [f] using congrArg Subtype.val hab
    have huG : (u : G) ≠ 1 := by
      intro hu
      apply huNe
      exact Subtype.ext hu
    have hST : S = T :=
      Degree15.sylow_eq_of_nonidentity_mem
        S T
        (Degree15.sylow_card_eq_of_card_eq
          S₀ hS₀ S)
        (Degree15.sylow_card_eq_of_card_eq
          S₀ hS₀ T)
        huG u.prop (by
          rw [huvG]
          exact v.prop)
    subst T
    have huv : u = v := Subtype.ext huvG
    subst v
    rfl
  have hfSurjective : Function.Surjective f := by
    intro u
    have huNe : u.1 ≠ 1 := by
      intro hu
      have huOrder := u.2.1
      rw [hu, orderOf_one] at huOrder
      norm_num at huOrder
    let R : Subgroup G := Subgroup.zpowers u.1
    have hRcard : Nat.card R = 5 := by
      rw [Nat.card_zpowers, u.2.1]
    have hRisP : IsPGroup 5 R := by
      apply IsPGroup.of_card (n := 1)
      rw [hRcard]
      norm_num
    obtain ⟨T, hRT⟩ := hRisP.exists_le_sylow
    let v : T :=
      ⟨u.1, hRT (Subgroup.mem_zpowers u.1)⟩
    have hvNe : v ≠ 1 := by
      intro hv
      apply huNe
      exact congrArg Subtype.val hv
    refine
      ⟨⟨T, ⟨v, ⟨hvNe, u.2.2⟩⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hFiber
      (S : Sylow 5 G) :
      4 ∣
        Nat.card
          {u : S //
            u ≠ 1 ∧
              (ρ (u : G)).support.card = d} := by
    have hScard : Nat.card S = 5 :=
      Degree15.sylow_card_eq_of_card_eq
        S₀ hS₀ S
    by_cases hex :
        ∃ u : S,
          u ≠ 1 ∧
            (ρ (u : G)).support.card = d
    · obtain ⟨u, huNe, huSupport⟩ := hex
      have hsupport
          (v : S) (hvNe : v ≠ 1) :
          (ρ (v : G)).support.card = d := by
        have hSupportEq :
            (ρ (v : G)).support =
              (ρ (u : G)).support := by
          apply le_antisymm
          · have hvGen :
                v ∈ Subgroup.zpowers u :=
              mem_zpowers_of_prime_card
                hScard huNe
            obtain ⟨z, hz⟩ :=
              Subgroup.mem_zpowers_iff.mp hvGen
            have hzρ :
                ρ (v : G) =
                  (ρ (u : G)) ^ z := by
              rw [← map_zpow]
              exact congrArg
                (fun w : S => ρ (w : G))
                hz.symm
            rw [hzρ]
            exact Equiv.Perm.support_zpow_le _ _
          · have huGen :
                u ∈ Subgroup.zpowers v :=
              mem_zpowers_of_prime_card
                hScard hvNe
            obtain ⟨z, hz⟩ :=
              Subgroup.mem_zpowers_iff.mp huGen
            have hzρ :
                ρ (u : G) =
                  (ρ (v : G)) ^ z := by
              rw [← map_zpow]
              exact congrArg
                (fun w : S => ρ (w : G))
                hz.symm
            rw [hzρ]
            exact Equiv.Perm.support_zpow_le _ _
        rw [hSupportEq, huSupport]
      let e :
          {v : S //
            v ≠ 1 ∧
              (ρ (v : G)).support.card = d} ≃
            {v : S // v ≠ 1} := {
        toFun v := ⟨v.1, v.2.1⟩
        invFun v :=
          ⟨v.1, ⟨v.2, hsupport v.1 v.2⟩⟩
        left_inv v := by
          apply Subtype.ext
          rfl
        right_inv v := by
          apply Subtype.ext
          rfl }
      rw [Nat.card_congr e,
        Nat.card_eq_fintype_card,
        Degree15.card_nonidentity_of_card_eq
          (p := 5)
          (by
            rw [← Nat.card_eq_fintype_card]
            exact
              Degree15.sylow_card_eq_of_card_eq
                S₀ hS₀ S)]
    · letI :
          IsEmpty
            {u : S //
              u ≠ 1 ∧
                (ρ (u : G)).support.card = d} :=
        ⟨fun u => hex ⟨u.1, u.2⟩⟩
      simp
  have hAdiv : 4 ∣ Nat.card A := by
    rw [Nat.card_sigma]
    exact Finset.dvd_sum
      (fun S _ => hFiber S)
  rw [← Nat.card_congr
    (Equiv.ofBijective f
      ⟨hfInjective, hfSurjective⟩)]
  exact hAdiv

theorem four_dvd_card_localOrderFiveSupportElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X) (d : ℕ)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 5) :
    4 ∣
      Nat.card
        (LocalOrderFiveSupportElements X P s d) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  letI : Fintype H := Fintype.ofFinite H
  let ρ : H →* Equiv.Perm X :=
    P.subtype.comp H.subtype
  change
    4 ∣
      Nat.card
        {u : H //
          orderOf u = 5 ∧
            (ρ u).support.card = d}
  exact
    four_dvd_card_orderFiveSupport_of_sylow_card_five
      H X ρ S hScard d

instance orderFiveSupportElementsSMul
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ) :
    SMul (ConjAct P) (OrderFiveSupportElements X P d) where
  smul g u :=
    ⟨g • u.1,
      ⟨by
        rw [ConjAct.smul_eq_mulAut_conj,
          (MulAut.conj _).orderOf_eq]
        exact u.2.1,
      by
        change
          (((((ConjAct.ofConjAct g : P) :
              Equiv.Perm X) *
            (u.1 : P) *
            ((ConjAct.ofConjAct g : P) :
              Equiv.Perm X)⁻¹).support.card) = d)
        rw [Equiv.Perm.card_support_conj]
        exact u.2.2⟩⟩

instance orderFiveSupportElementsMulAction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ) :
    MulAction (ConjAct P)
      (OrderFiveSupportElements X P d) :=
  Subtype.coe_injective.mulAction
    Subtype.val (fun _ _ => rfl)

private def orderFiveSupportStabilizerToCentralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ)
    (u : OrderFiveSupportElements X P d) :
    MulAction.stabilizer (ConjAct P) u →*
      Subgroup.centralizer
        ({(u.1 : Equiv.Perm X)} : Set (Equiv.Perm X)) where
  toFun k :=
    ⟨((ConjAct.ofConjAct k.1 : P) :
        Equiv.Perm X),
      by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hkP :
            ConjAct.ofConjAct k.1 * u.1 =
              u.1 * ConjAct.ofConjAct k.1 := by
          rw [← mul_inv_eq_iff_eq_mul]
          exact congrArg Subtype.val k.2
        exact congrArg Subtype.val hkP⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    rfl

theorem orderFiveSupport_stabilizer_card_dvd_centralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ)
    (u : OrderFiveSupportElements X P d) :
    Nat.card (MulAction.stabilizer (ConjAct P) u) ∣
      Nat.card
        (Subgroup.centralizer
          ({(u.1 : Equiv.Perm X)} :
            Set (Equiv.Perm X))) := by
  exact
    Subgroup.card_dvd_of_injective
      (orderFiveSupportStabilizerToCentralizer
        X P d u)
      (by
        intro a b hab
        apply Subtype.ext
        apply ConjAct.ofConjAct.injective
        apply Subtype.ext
        exact congrArg
          (fun z :
            Subgroup.centralizer
              ({(u.1 : Equiv.Perm X)} :
                Set (Equiv.Perm X)) =>
              (z : Equiv.Perm X))
          hab)

theorem orderFiveSupportFifteen_centralizer_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (u : OrderFiveSupportElements X P 15) :
    Nat.card
        (Subgroup.centralizer
          ({(u.1 : Equiv.Perm X)} :
            Set (Equiv.Perm X))) =
      272160000 := by
  classical
  let g : Equiv.Perm X := u.1
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 5 := u.2.1
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, u.2.2] at hsum
  have hkThree : k + 1 = 3 := by omega
  have hcycleType : g.cycleType = {5, 5, 5} := by
    rw [hk, hgorder, hkThree]
    norm_num
  change
    Nat.card
        (Subgroup.centralizer
          ({g} : Set (Equiv.Perm X))) =
      272160000
  rw [Equiv.Perm.nat_card_centralizer,
    hcycleType, hcard]
  norm_num

theorem divisor_dvd_card_of_stabilizer_card_dvd
    (G U : Type) [Group G] [Fintype G] [Fintype U]
    [MulAction G U]
    (m c : ℕ)
    (hGcard : Nat.card G = m * c)
    (hStabilizer :
      ∀ u : U,
        Nat.card (MulAction.stabilizer G u) ∣ c) :
    m ∣ Nat.card U := by
  classical
  let Ω := Quotient (MulAction.orbitRel G U)
  have hFiber (ω : Ω) :
      m ∣
        Nat.card
          (G ⧸ MulAction.stabilizer G ω.out) := by
    let K := MulAction.stabilizer G ω.out
    obtain ⟨a, ha⟩ := hStabilizer ω.out
    have hProduct := K.index_mul_card
    have hKpos : 0 < Nat.card K := Nat.card_pos
    rw [hGcard, ha] at hProduct
    rw [← K.index_eq_card]
    refine ⟨a, ?_⟩
    nlinarith
  have hCard :=
    Nat.card_congr
      (MulAction.selfEquivSigmaOrbitsQuotientStabilizer
        G U)
  rw [Nat.card_sigma] at hCard
  rw [hCard]
  exact Finset.dvd_sum fun ω _ => hFiber ω

end FiveTransitive.Degree24

end CFSG
