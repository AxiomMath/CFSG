module

public import CFSG.Permutation.FiveTransitive.Degree24Order96LocalConjugacy
public import CFSG.Permutation.FiveTransitive.Degree24Order96Orbit
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

namespace NormalizerFixedPoints

variable
    (X : Type) [Fintype X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P)

instance normalizerSMul :
    SMul
      (Subgroup.normalizer (R : Set P))
      (MulAction.fixedPoints R X) where
  smul n x :=
    ⟨(n : P) • x.1, by
      rw [MulAction.mem_fixedPoints]
      intro r
      have hconj :
          (n : P)⁻¹ * (r : P) * (n : P) ∈ R :=
        (Subgroup.mem_normalizer_iff''.mp n.prop
          (r : P)).mp r.prop
      let r' : R :=
        ⟨(n : P)⁻¹ * (r : P) * (n : P), hconj⟩
      have hcommute :
          (r : P) * (n : P) =
            (n : P) * (r' : P) := by
        change
          (r : P) * (n : P) =
            (n : P) *
              ((n : P)⁻¹ * (r : P) * (n : P))
        simp [mul_assoc]
      calc
        (r : P) • ((n : P) • x.1) =
            ((r : P) * (n : P)) • x.1 :=
          (mul_smul (r : P) (n : P) x.1).symm
        _ = ((n : P) * (r' : P)) • x.1 :=
          congrArg (fun q : P => q • x.1) hcommute
        _ = (n : P) • ((r' : P) • x.1) :=
          mul_smul (n : P) (r' : P) x.1
        _ = (n : P) • x.1 :=
          congrArg (fun y : X => (n : P) • y)
            (MulAction.mem_fixedPoints.mp x.2 r')⟩

instance normalizerMulAction :
    MulAction
      (Subgroup.normalizer (R : Set P))
      (MulAction.fixedPoints R X) :=
  Subtype.coe_injective.mulAction
    Subtype.val (fun _ _ => rfl)

end NormalizerFixedPoints

namespace OrderPrimeSupportElements

private theorem card_stabilizer_eq_card_centralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (p d : ℕ)
    (u : OrderPrimeSupportElements X P p d) :
    Nat.card (MulAction.stabilizer (ConjAct P) u) =
      Nat.card
        (Subgroup.centralizer
          ({(u.1 : P)} : Set P)) := by
  classical
  let K : Subgroup (ConjAct P) :=
    MulAction.stabilizer (ConjAct P) u
  let C : Subgroup P :=
    Subgroup.centralizer ({(u.1 : P)} : Set P)
  let e : K ≃ C := {
    toFun := fun k =>
      ⟨ConjAct.ofConjAct k.1, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hkP :
            ConjAct.ofConjAct k.1 * u.1 =
              u.1 * ConjAct.ofConjAct k.1 := by
          rw [← mul_inv_eq_iff_eq_mul]
          exact congrArg Subtype.val k.2
        exact hkP⟩
    invFun := fun c =>
      ⟨ConjAct.toConjAct c.1, by
        apply Subtype.ext
        change MulAut.conj c.1 u.1 = u.1
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
        exact
          Subgroup.mem_centralizer_singleton_iff.mp
            c.2⟩
    left_inv := by
      intro k
      apply Subtype.ext
      exact ConjAct.toConjAct_ofConjAct k.1
    right_inv := by
      intro c
      apply Subtype.ext
      rfl }
  exact Nat.card_congr e

end OrderPrimeSupportElements

theorem order96_cyclic_orderThree_normalizer_maps_fixed_five_tuples
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (u : P) (hu : orderOf u = 3)
    (a b : Fin 5 ↪ X)
    (ha : ∀ i, u • a i = a i)
    (hb : ∀ i, u • b i = b i) :
    ∃ c : P,
      c ∈ Subgroup.normalizer (Subgroup.zpowers u : Set P) ∧
        ∀ i, c • a i = b i := by
  classical
  obtain ⟨q, hq⟩ :=
    h5 a b a.injective b.injective
  let t : Set X := Set.range b
  have ht : t.ncard = 5 := by
    rw [Set.ncard_range_of_injective b.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let H : Subgroup P := fixingSubgroup P t
  have hHcardTarget : Nat.card H = 96 := by
    have heq :=
      five_point_stabilizers_have_equal_card
        X P h5 s t hs ht
    dsimp only [H]
    rw [← heq]
    exact hHcard
  have huH : u ∈ H := by
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i, rfl⟩
    exact hb i
  let uH : H := ⟨u, huH⟩
  have huHorder : orderOf uH = 3 := by
    calc
      orderOf uH = orderOf u :=
        (Subgroup.orderOf_coe uH).symm
      _ = 3 := hu
  let v : P := MulAut.conj q u
  have hvH : v ∈ H := by
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i, rfl⟩
    change (MulAut.conj q u : P) • b i = b i
    calc
      (MulAut.conj q u : P) • b i =
          q • (u • (q⁻¹ • b i)) := by
        simp only [MulAut.conj_apply, mul_smul]
      _ = q • (u • a i) := by
        rw [← hq i, inv_smul_smul]
      _ = q • a i :=
        congrArg (fun x : X => q • x) (ha i)
      _ = b i := hq i
  let vH : H := ⟨v, hvH⟩
  have hvHorder : orderOf vH = 3 := by
    calc
      orderOf vH = orderOf v :=
        (Subgroup.orderOf_coe vH).symm
      _ = orderOf u :=
        (MulAut.conj q).orderOf_eq u
      _ = 3 := hu
  rcases
      order96_orderThree_elements_conjugate_or_inverse
        X P t hHcardTarget uH vH huHorder hvHorder with
    hconj | hconj
  · obtain ⟨k, hk⟩ := hconj
    let kP : P := k
    have hkP : kP * u * kP⁻¹ = v := by
      exact congrArg Subtype.val hk
    let c : P := kP⁻¹ * q
    have hcConj : MulAut.conj c u = u := by
      change c * u * c⁻¹ = u
      calc
        c * u * c⁻¹ =
            kP⁻¹ * (q * u * q⁻¹) * kP := by
          dsimp only [c]
          group
        _ = kP⁻¹ * v * kP := by
          rfl
        _ = u := by
          rw [← hkP]
          group
    have hcMap :
        (Subgroup.zpowers u).map
            (MulAut.conj c).toMonoidHom =
          Subgroup.zpowers u := by
      rw [MonoidHom.map_zpowers]
      change
        Subgroup.zpowers (MulAut.conj c u) =
          Subgroup.zpowers u
      rw [hcConj]
    have hcNormalizer :
        c ∈ Subgroup.normalizer
          (Subgroup.zpowers u : Set P) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcMap
    refine ⟨c, hcNormalizer, ?_⟩
    intro i
    have hkFix :
        kP • b i = b i :=
      (mem_fixingSubgroup_iff P).mp
        k.prop (b i) ⟨i, rfl⟩
    calc
      c • a i = kP⁻¹ • (q • a i) := by
        simp only [c, mul_smul]
      _ = kP⁻¹ • b i := by rw [hq i]
      _ = kP⁻¹ • (kP • b i) :=
        congrArg (fun x : X => kP⁻¹ • x) hkFix.symm
      _ = b i := inv_smul_smul kP (b i)
  · obtain ⟨k, hk⟩ := hconj
    let kP : P := k
    have hkP : kP * u * kP⁻¹ = v⁻¹ := by
      exact congrArg Subtype.val hk
    let c : P := kP⁻¹ * q
    have hcConj : MulAut.conj c u = u⁻¹ := by
      change c * u * c⁻¹ = u⁻¹
      calc
        c * u * c⁻¹ =
            kP⁻¹ * (q * u * q⁻¹) * kP := by
          dsimp only [c]
          group
        _ = kP⁻¹ * v * kP := by
          rfl
        _ = kP⁻¹ * (kP * u * kP⁻¹)⁻¹ * kP := by
          rw [hkP]
          simp
        _ = u⁻¹ := by
          group
    have hcMap :
        (Subgroup.zpowers u).map
            (MulAut.conj c).toMonoidHom =
          Subgroup.zpowers u := by
      rw [MonoidHom.map_zpowers]
      change
        Subgroup.zpowers (MulAut.conj c u) =
          Subgroup.zpowers u
      rw [hcConj, Subgroup.zpowers_inv]
    have hcNormalizer :
        c ∈ Subgroup.normalizer
          (Subgroup.zpowers u : Set P) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcMap
    refine ⟨c, hcNormalizer, ?_⟩
    intro i
    have hkFix :
        kP • b i = b i :=
      (mem_fixingSubgroup_iff P).mp
        k.prop (b i) ⟨i, rfl⟩
    calc
      c • a i = kP⁻¹ • (q • a i) := by
        simp only [c, mul_smul]
      _ = kP⁻¹ • b i := by rw [hq i]
      _ = kP⁻¹ • (kP • b i) :=
        congrArg (fun x : X => kP⁻¹ • x) hkFix.symm
      _ = b i := inv_smul_smul kP (b i)

theorem order96_cyclic_orderThree_normalizer_fixed_action
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (u : OrderPrimeSupportElements X P 3 18) :
    let R : Subgroup P := Subgroup.zpowers (u.1 : P)
    let F : Set X := MulAction.fixedPoints R X
    let N : Subgroup P := Subgroup.normalizer (R : Set P)
    Nat.card F = 6 ∧
      MulAction.IsMultiplyPretransitive N F 5 := by
  classical
  dsimp
  let uP : P := u.1
  let g : Equiv.Perm X := uP
  let R : Subgroup P := Subgroup.zpowers uP
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P := Subgroup.normalizer (R : Set P)
  have huOrder : orderOf uP = 3 := by
    simpa only [uP] using u.2.1
  have hgSupport : g.support.card = 18 := by
    simpa only [g, uP] using u.2.2
  have hfixedEq :
      F = Function.fixedPoints g := by
    ext x
    rw [MulAction.mem_fixedPoints,
      Function.mem_fixedPoints_iff]
    constructor
    · intro hx
      exact hx
        ⟨uP, Subgroup.mem_zpowers uP⟩
    · intro hx z
      have huStab :
          uP ∈ MulAction.stabilizer P x := by
        rw [MulAction.mem_stabilizer_iff]
        exact hx
      have hzStab :
          (z : P) ∈ MulAction.stabilizer P x :=
        (Subgroup.zpowers_le.mpr huStab) z.prop
      exact MulAction.mem_stabilizer_iff.mp hzStab
  have hFcard : Nat.card F = 6 := by
    rw [hfixedEq, Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hgSupport]
  have hN5 :
      ∀ a b : Fin 5 → F,
        Function.Injective a →
        Function.Injective b →
        ∃ c : N, ∀ i, c • a i = b i := by
    intro a b ha hb
    let aX : Fin 5 ↪ X := {
      toFun := fun i => (a i).1
      inj' := fun i j hij =>
        ha (Subtype.ext hij) }
    let bX : Fin 5 ↪ X := {
      toFun := fun i => (b i).1
      inj' := fun i j hij =>
        hb (Subtype.ext hij) }
    have haFix (i : Fin 5) :
        uP • aX i = aX i :=
      MulAction.mem_fixedPoints.mp
        (a i).2 ⟨uP, Subgroup.mem_zpowers uP⟩
    have hbFix (i : Fin 5) :
        uP • bX i = bX i :=
      MulAction.mem_fixedPoints.mp
        (b i).2 ⟨uP, Subgroup.mem_zpowers uP⟩
    obtain ⟨c, hcNormalizer, hc⟩ :=
      order96_cyclic_orderThree_normalizer_maps_fixed_five_tuples
        X P h5 s hs hHcard uP huOrder
          aX bX haFix hbFix
    let cN : N := ⟨c, by
      simpa only [N, R] using hcNormalizer⟩
    refine ⟨cN, ?_⟩
    intro i
    apply Subtype.ext
    exact hc i
  refine ⟨hFcard, ?_⟩
  rw [MulAction.isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨c, hc⟩ :=
    hN5 a b a.injective b.injective
  refine ⟨c, ?_⟩
  ext i
  simpa [Function.Embedding.smul_apply] using
    congrArg Subtype.val (hc i)

private theorem order96_cyclic_orderThree_normalizer_fixed_action_range_eq_top
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (u : OrderPrimeSupportElements X P 3 18) :
    let R : Subgroup P := Subgroup.zpowers (u.1 : P)
    let F : Set X := MulAction.fixedPoints R X
    let N : Subgroup P := Subgroup.normalizer (R : Set P)
    (MulAction.toPermHom N F).range = ⊤ := by
  classical
  dsimp
  let uP : P := u.1
  let R : Subgroup P := Subgroup.zpowers uP
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P := Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let Q : Subgroup (Equiv.Perm F) := ρ.range
  obtain ⟨hFcard, hN5⟩ :=
    order96_cyclic_orderThree_normalizer_fixed_action
      X P hcard h5 s hs hHcard u
  have hQ5 :
      MulAction.IsMultiplyPretransitive Q F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨n, hn⟩ :=
      (MulAction.isMultiplyPretransitive_iff.mp hN5)
        a b
    let q : Q := ⟨ρ n, ⟨n, rfl⟩⟩
    refine ⟨q, ?_⟩
    exact hn
  obtain ⟨t, _, ht⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set F)) (n := 5) (by
        rw [Set.ncard_univ, hFcard]
        norm_num)
  let K : Subgroup Q := fixingSubgroup Q t
  have hKindexRaw :=
    hQ5.index_of_fixingSubgroup_mul ht
  rw [hFcard] at hKindexRaw
  norm_num at hKindexRaw
  have hKindex : K.index = 720 := by
    change (fixingSubgroup Q t).index = 720
    omega
  have hKproduct := K.index_mul_card
  have hQcardLower : 720 ≤ Nat.card Q := by
    rw [hKindex] at hKproduct
    have hKcardPos : 0 < Nat.card K :=
      Nat.card_pos
    omega
  have hQcardDvd :
      Nat.card Q ∣ Nat.card (Equiv.Perm F) :=
    Subgroup.card_subgroup_dvd_card Q
  have hPermCard :
      Nat.card (Equiv.Perm F) = 720 := by
    rw [Nat.card_perm, hFcard]
    norm_num
  rw [hPermCard] at hQcardDvd
  have hQcardUpper : Nat.card Q ≤ 720 :=
    Nat.le_of_dvd (by norm_num) hQcardDvd
  have hQcard : Nat.card Q = 720 := by
    omega
  change Q = ⊤
  apply Subgroup.eq_top_of_card_eq
  rw [hQcard, hPermCard]

theorem order96_cyclic_orderThree_normalizer_extremal_data
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96) :
    let U := OrderPrimeSupportElements X P 3 18
    ∃ u : U,
      Nat.card U = 226688 ∧
        Nat.card
            (Subgroup.normalizer
              (Subgroup.zpowers (u.1 : P) : Set P)) =
          4320 ∧
        let R : Subgroup P :=
          Subgroup.zpowers (u.1 : P)
        let F : Set X := MulAction.fixedPoints R X
        let N : Subgroup P :=
          Subgroup.normalizer (R : Set P)
        (MulAction.toPermHom N F).range = ⊤ := by
  classical
  dsimp
  obtain ⟨u, hUcard, hStabilizerCard⟩ :=
    order96_global_orderThree_extremal_data
      X P hcard h5 hnotAlt s hs hHcard
  let uP : P := u.1
  let R : Subgroup P := Subgroup.zpowers uP
  let C : Subgroup P :=
    Subgroup.centralizer (R : Set P)
  let C₁ : Subgroup P :=
    Subgroup.centralizer ({uP} : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  have huOrder : orderOf uP = 3 := by
    simpa only [uP] using u.2.1
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, huOrder]
  have hC₁card : Nat.card C₁ = 2160 := by
    have hcardEq :=
      OrderPrimeSupportElements.card_stabilizer_eq_card_centralizer
        X P 3 18 u
    change
      Nat.card
          (Subgroup.centralizer
            ({(u.1 : P)} : Set P)) =
        2160
    rw [← hcardEq, hStabilizerCard]
  have hCentEq : C = C₁ := by
    change
      Subgroup.centralizer
          (Subgroup.zpowers uP : Set P) =
        Subgroup.centralizer ({uP} : Set P)
    rw [Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hCcard : Nat.card C = 2160 := by
    rw [hCentEq]
    exact hC₁card
  letI : IsCyclic R := by
    dsimp only [R]
    infer_instance
  have hAutCard : Nat.card (MulAut R) = 2 := by
    rw [IsCyclic.card_mulAut R, hRcard,
      Nat.totient_prime (by norm_num : Nat.Prime 3)]
  have hrangeDvd :
      Nat.card R.normalizerMonoidHom.range ∣ 2 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card R.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (R : Set P)).relIndex
          (Subgroup.normalizer (R : Set P)) =
        Nat.card R.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      R.normalizerMonoidHom_ker]
  have hrDvd : C.relIndex N ∣ 2 := by
    rwa [hrEq]
  let uInv : OrderPrimeSupportElements X P 3 18 :=
    ⟨uP⁻¹, ⟨by
      simpa only [orderOf_inv] using huOrder,
      by
        change
          (((uP : Equiv.Perm X)⁻¹).support.card) =
            18
        rw [Equiv.Perm.support_inv]
        exact u.2.2⟩⟩
  have hpretrans :=
    order96_orderThree_support_conjugation_pretransitive
      X P hcard h5 hnotAlt s hs hHcard
  letI :
      MulAction.IsPretransitive
        (ConjAct P)
        (OrderPrimeSupportElements X P 3 18) :=
    hpretrans
  obtain ⟨q, hq⟩ :=
    exists_smul_eq
      (ConjAct P) u uInv
  let qP : P := ConjAct.ofConjAct q
  have hqP : MulAut.conj qP uP = uP⁻¹ := by
    exact congrArg Subtype.val hq
  have hqMap :
      R.map (MulAut.conj qP).toMonoidHom = R := by
    rw [MonoidHom.map_zpowers]
    change
      Subgroup.zpowers (MulAut.conj qP uP) =
        Subgroup.zpowers uP
    rw [hqP, Subgroup.zpowers_inv]
  have hqNormalizer : qP ∈ N := by
    exact
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        hqMap
  have huNeInv : uP ≠ uP⁻¹ := by
    intro huInv
    have huSquare : uP ^ 2 = 1 := by
      calc
        uP ^ 2 = uP * uP := pow_two uP
        _ = uP⁻¹ * uP :=
          congrArg (fun z => z * uP) huInv
        _ = 1 := inv_mul_cancel uP
    have hOrderDvd : orderOf uP ∣ 2 :=
      orderOf_dvd_of_pow_eq_one huSquare
    rw [huOrder] at hOrderDvd
    norm_num at hOrderDvd
  have hqNotCentralizer : qP ∉ C := by
    intro hqC
    have hqC₁ : qP ∈ C₁ := by
      rw [← hCentEq]
      exact hqC
    have hqSame :
        MulAut.conj qP uP = uP := by
      change qP * uP * qP⁻¹ = uP
      rw [mul_inv_eq_iff_eq_mul]
      exact
        Subgroup.mem_centralizer_singleton_iff.mp
          hqC₁
    exact huNeInv (hqSame.symm.trans hqP)
  have hrNeOne : C.relIndex N ≠ 1 := by
    intro hrOne
    have hNleC :
        N ≤ C :=
      Subgroup.relIndex_eq_one.mp hrOne
    exact hqNotCentralizer
      (hNleC hqNormalizer)
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrPos : 0 < C.relIndex N :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrTwo : C.relIndex N = 2 := by
    have hrLe : C.relIndex N ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    omega
  have hrel :
      C.relIndex N * N.index = C.index :=
    Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer
        (R : Set P))
  have hNcardEq :
      Nat.card N =
        C.relIndex N * Nat.card C := by
    have hprod :
        N.index *
              (C.relIndex N * Nat.card C) =
            N.index * Nat.card N := by
      calc
        N.index *
              (C.relIndex N * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card P := C.index_mul_card
        _ = N.index * Nat.card N :=
          N.index_mul_card.symm
    exact
      (Nat.mul_left_cancel
        (Nat.pos_of_ne_zero
          Subgroup.index_ne_zero_of_finite)
        hprod).symm
  have hNcard : Nat.card N = 4320 := by
    rw [hNcardEq, hrTwo, hCcard]
  have hRangeTop :=
    order96_cyclic_orderThree_normalizer_fixed_action_range_eq_top
      X P hcard h5 s hs hHcard u
  refine ⟨u, hUcard, ?_, ?_⟩
  · simpa only [N, R, uP] using hNcard
  · simpa only [N, R, uP] using hRangeTop

end FiveTransitive.Degree24

end CFSG
