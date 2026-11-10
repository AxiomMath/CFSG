module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoDoubleCount

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

theorem sylow_card_eq_prime_of_card_eq_prime_mul
    (G : Type) [Group G] [Fintype G]
    (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : m ≠ 0) (hnotP : ¬p ∣ m)
    (hGcard : Nat.card G = p * m)
    (S : Sylow p G) :
    Nat.card S = p := by
  have hfactorization :
      (p * m).factorization p = 1 := by
    rw [Nat.factorization_mul
        (Fact.out : Nat.Prime p).ne_zero hm,
      Finsupp.add_apply,
      (Fact.out : Nat.Prime p).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hnotP]
  rw [S.card_eq_multiplicity, hGcard,
    hfactorization]
  simp

theorem card_order_prime_elements_of_sylow_card_prime
    (G : Type) [Group G] [Fintype G]
    (p : ℕ) [Fact p.Prime]
    (S : Sylow p G) (hScard : Nat.card S = p) :
    Nat.card {u : G // orderOf u = p} =
      Nat.card (Sylow p G) * (p - 1) := by
  classical
  let A := Degree15.NonidentitySylowElements p G
  let B := {u : G // orderOf u = p}
  let f : A → B :=
    fun a =>
      ⟨(a.2.1 : G), by
        calc
          orderOf (a.2.1 : G) =
              orderOf (a.2.1 : a.1) :=
            Subgroup.orderOf_coe _
          _ = p :=
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
      exact
        (Fact.out : Nat.Prime p).ne_one
          huOrder.symm
    let R : Subgroup G := Subgroup.zpowers u.1
    have hRcard : Nat.card R = p := by
      rw [Nat.card_zpowers, u.2]
    have hRisP : IsPGroup p R := by
      apply IsPGroup.of_card (n := 1)
      rw [hRcard]
      simp
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
        Nat.card (Sylow p G) * (p - 1) := by
    rw [Nat.card_eq_fintype_card]
    change
      Fintype.card
          (Degree15.NonidentitySylowElements p G) =
        Nat.card (Sylow p G) * (p - 1)
    rw [Degree15.card_nonidentitySylowElements
      S hScard, Nat.card_eq_fintype_card]
  calc
    Nat.card B = Nat.card A :=
      (Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)).symm
    _ =
        Nat.card (Sylow p G) * (p - 1) :=
      hAcard

abbrev OrderPrimeSupportElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ) :=
  {u : P //
    orderOf u = p ∧
      (u.1 : Equiv.Perm X).support.card = d}

abbrev OrderPrimeSupportFixesEmbedding
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ)
    (e : Fin 5 ↪ X) :=
  {u : OrderPrimeSupportElements X P p d //
    (u.1 : P) ∈ fixingSubgroup P (Set.range e)}

abbrev LocalOrderPrimeSupportElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    (p d : ℕ) :=
  {u : fixingSubgroup P s //
    orderOf u = p ∧
      ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = d)}

@[expose] noncomputable def localOrderPrimeSupportEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    (p d : ℕ) (e : Fin 5 ↪ X)
    (he : Set.range e = s) :
    LocalOrderPrimeSupportElements X P s p d ≃
      OrderPrimeSupportFixesEmbedding X P p d e where
  toFun u :=
    ⟨⟨(u.1 : fixingSubgroup P s),
        ⟨by
          calc
            orderOf
                ((u.1 : fixingSubgroup P s) : P) =
              orderOf u.1 :=
                Subgroup.orderOf_coe _
            _ = p := u.2.1,
        u.2.2⟩⟩,
      by
        rw [he]
        exact u.1.prop⟩
  invFun u := by
    have huFix :
        (u.1.1 : P) ∈ fixingSubgroup P s := by
      rw [← he]
      exact u.2
    let v : fixingSubgroup P s :=
      ⟨u.1.1, huFix⟩
    refine ⟨v, ⟨?_, ?_⟩⟩
    · calc
        orderOf v = orderOf (v : P) :=
          (Subgroup.orderOf_coe _).symm
        _ = orderOf u.1.1 := rfl
        _ = p := u.1.2.1
    · exact u.1.2.2
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def orderPrimeSupportFixesEmbeddingConjEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ)
    (g : P) (e : Fin 5 ↪ X) :
    OrderPrimeSupportFixesEmbedding X P p d e ≃
      OrderPrimeSupportFixesEmbedding X P p d (g • e) where
  toFun u :=
    ⟨⟨MulAut.conj g u.1.1,
        ⟨by
          rw [(MulAut.conj g).orderOf_eq]
          exact u.1.2.1,
        by
          change
            ((((g : P) : Equiv.Perm X) *
              (u.1.1 : P) *
              ((g : P) : Equiv.Perm X)⁻¹).support.card) = d
          rw [Equiv.Perm.card_support_conj]
          exact u.1.2.2⟩⟩,
      Set.conj_mem_fixingSubgroup
        (smul_range_fiveEmbedding g e) u.2⟩
  invFun u :=
    ⟨⟨MulAut.conj g⁻¹ u.1.1,
        ⟨by
          rw [(MulAut.conj g⁻¹).orderOf_eq]
          exact u.1.2.1,
        by
          change
            ((((g⁻¹ : P) : Equiv.Perm X) *
              (u.1.1 : P) *
              ((g⁻¹ : P) : Equiv.Perm X)⁻¹).support.card) = d
          rw [Equiv.Perm.card_support_conj]
          exact u.1.2.2⟩⟩,
      by
        apply Set.conj_mem_fixingSubgroup
          (M := P) (α := X)
        · rw [smul_range_fiveEmbedding]
          exact congrArg
            (fun f : Fin 5 ↪ X => Set.range f)
            (inv_smul_smul g e)
        · exact u.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change
      g⁻¹ * (g * u.1.val * g⁻¹) * g =
        u.1.val
    group
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change
      g * (g⁻¹ * u.1.val * g) * g⁻¹ =
        u.1.val
    group

private noncomputable def orderPrimeSupportEmbeddingIncidenceEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ) :
    (Σ e : Fin 5 ↪ X,
        OrderPrimeSupportFixesEmbedding X P p d e) ≃
      (Σ u : OrderPrimeSupportElements X P p d,
        MulAction.fixedBy (Fin 5 ↪ X) u.1) where
  toFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        apply Function.Embedding.ext
        intro i
        have hmem :
            z.1 i ∈ Set.range z.1 :=
          ⟨i, rfl⟩
        have hu :=
          (mem_fixingSubgroup_iff P).mp
            z.2.2 (z.1 i) hmem
        exact hu⟩⟩
  invFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact congrArg
          (fun e : Fin 5 ↪ X => e i) z.2.2⟩⟩
  left_inv z := by
    rcases z with ⟨e, u, hu⟩
    rfl
  right_inv z := by
    rcases z with ⟨u, e, he⟩
    rfl

theorem orderPrimeSupport_incidence_count
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hP5 : MulAction.IsMultiplyPretransitive P X 5)
    (p d fixedCount : ℕ)
    (hfixed :
      ∀ u : OrderPrimeSupportElements X P p d,
        Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
            fixedCount)
    (e₀ : Fin 5 ↪ X) :
    Nat.card (Fin 5 ↪ X) *
        Nat.card
          (OrderPrimeSupportFixesEmbedding
            X P p d e₀) =
      Nat.card
          (OrderPrimeSupportElements X P p d) *
        fixedCount := by
  classical
  let E := Fin 5 ↪ X
  let A :=
    Σ e : E,
      OrderPrimeSupportFixesEmbedding X P p d e
  let B :=
    Σ u : OrderPrimeSupportElements X P p d,
      MulAction.fixedBy E u.1
  let c :=
    Nat.card
      (OrderPrimeSupportFixesEmbedding X P p d e₀)
  have hFiberA (e : E) :
      Nat.card
          (OrderPrimeSupportFixesEmbedding X P p d e) =
        c := by
    obtain ⟨g, hg⟩ :=
      hP5.exists_smul_eq e e₀
    subst e₀
    exact Nat.card_congr
      (orderPrimeSupportFixesEmbeddingConjEquiv
        X P p d g e)
  have hAcard :
      Nat.card A = Nat.card E * c := by
    rw [Nat.card_sigma]
    simp_rw [hFiberA]
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  have hBcard :
      Nat.card B =
        Nat.card
          (OrderPrimeSupportElements X P p d) *
            fixedCount := by
    have hfixed'
        (u : OrderPrimeSupportElements X P p d) :
        Nat.card (MulAction.fixedBy E u.1) =
          fixedCount :=
      hfixed u
    rw [Nat.card_sigma]
    simp_rw [hfixed']
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  calc
    Nat.card E * c = Nat.card A := hAcard.symm
    _ = Nat.card B :=
      Nat.card_congr
        (orderPrimeSupportEmbeddingIncidenceEquiv
          X P p d)
    _ =
        Nat.card
          (OrderPrimeSupportElements X P p d) *
            fixedCount :=
      hBcard

instance orderPrimeSupportElementsSMul
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ) :
    SMul (ConjAct P)
      (OrderPrimeSupportElements X P p d) where
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

instance orderPrimeSupportElementsMulAction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ) :
    MulAction (ConjAct P)
      (OrderPrimeSupportElements X P p d) :=
  Subtype.coe_injective.mulAction
    Subtype.val (fun _ _ => rfl)

@[expose] def orderPrimeSupportStabilizerToCentralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ)
    (u : OrderPrimeSupportElements X P p d) :
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

theorem orderPrimeSupport_stabilizer_card_dvd_centralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p d : ℕ)
    (u : OrderPrimeSupportElements X P p d) :
    Nat.card (MulAction.stabilizer (ConjAct P) u) ∣
      Nat.card
        (Subgroup.centralizer
          ({(u.1 : Equiv.Perm X)} :
            Set (Equiv.Perm X))) := by
  exact
    Subgroup.card_dvd_of_injective
      (orderPrimeSupportStabilizerToCentralizer
        X P p d u)
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

end FiveTransitive.Degree24

end CFSG
