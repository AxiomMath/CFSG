module

public import CFSG.Permutation.FiveTransitive.HallInvolutionConsequence

public section

namespace CFSG

namespace FiveTransitive.Research.HallVFourOrbits

open Research.OddFourStabilizerLifts
open Research.HallInvolutionConsequence
open Research.SharpFourDegreeCompletion

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_commuting_single_double_lifts
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    ∃ a b : G,
      a ^ 2 = 1 ∧ a ≠ 1 ∧ b ^ 2 = 1 ∧ b ≠ 1 ∧
      Commute a b ∧
      (∀ i, a • e i =
        e (Research.SharpFourBound.baseSingleSwap i)) ∧
      (∀ i, b • e i =
        e (Research.SharpFourBound.baseDoubleSwap i)) := by
  classical
  obtain ⟨u, v, huOrder, hvOrder, huvComm, huImage, hvImage⟩ :=
    exists_commuting_involution_lifts h4 e hodd
  have huData : u ^ 2 = 1 ∧ u ≠ 1 :=
    orderOf_eq_prime_iff.mp huOrder
  have hvData : v ^ 2 = 1 ∧ v ≠ 1 :=
    orderOf_eq_prime_iff.mp hvOrder
  let a : G := v
  let b : G := (u * v : baseSetwiseStabilizer (G := G) e)
  have haTwo : a ^ 2 = 1 := congrArg Subtype.val hvData.1
  have haNe : a ≠ 1 := by
    intro ha
    apply hvData.2
    apply Subtype.ext
    exact ha
  have hbTwoK : (u * v) ^ 2 = 1 := by
    rw [huvComm.mul_pow, huData.1, hvData.1, one_mul]
  have hbTwo : b ^ 2 = 1 := congrArg Subtype.val hbTwoK
  have haImage : baseSetwisePermHom (G := G) e v =
      (baseRangeEquiv e).permCongrHom
        Research.SharpFourBound.baseSingleSwap := by
    change baseSetwisePermHom (G := G) e v =
      (baseRangeEquiv e).permCongrHom baseRightSwap at hvImage
    exact hvImage
  have hbImage : baseSetwisePermHom (G := G) e (u * v) =
      (baseRangeEquiv e).permCongrHom
        Research.SharpFourBound.baseDoubleSwap := by
    rw [map_mul, huImage, hvImage]
    change
      (baseRangeEquiv e).permCongrHom baseLeftSwap *
          (baseRangeEquiv e).permCongrHom baseRightSwap =
        (baseRangeEquiv e).permCongrHom
          Research.SharpFourBound.baseDoubleSwap
    exact (map_mul (baseRangeEquiv e).permCongrHom
      baseLeftSwap baseRightSwap).symm
  have haBase := smul_base_of_setwisePermHom_eq e v
    Research.SharpFourBound.baseSingleSwap haImage
  have hbBase := smul_base_of_setwisePermHom_eq e (u * v)
    Research.SharpFourBound.baseDoubleSwap hbImage
  have hbNe : b ≠ 1 := by
    change (((u * v : baseSetwiseStabilizer (G := G) e) : G)) ≠ 1
    intro hb
    have hfix := hbBase (0 : Fin 4)
    rw [hb, one_smul] at hfix
    exact e.injective.ne (by decide) hfix
  have habComm : Commute a b := by
    rw [Commute]
    change (v : G) * ((u : G) * (v : G)) =
      ((u : G) * (v : G)) * (v : G)
    have huv : (u : G) * (v : G) = (v : G) * (u : G) :=
      congrArg Subtype.val huvComm.eq
    calc
      (v : G) * ((u : G) * (v : G)) =
          ((v : G) * (u : G)) * (v : G) := by rw [mul_assoc]
      _ = ((u : G) * (v : G)) * (v : G) := by rw [← huv]
  exact ⟨a, b, haTwo, haNe, hbTwo, hbNe, habComm, haBase, hbBase⟩

theorem product_involution_sq
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) :
    (a * b) ^ 2 = 1 := by
  rw [hab.mul_pow, haTwo, hbTwo, one_mul]

private theorem product_lift_smul_base
    (e : Fin 4 ↪ X) (a b : G)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i)) :
    ∀ i, (a * b) • e i = e (baseLeftSwap i) := by
  intro i
  rw [mul_smul, hbBase, haBase]
  congr 1
  fin_cases i <;> rfl

theorem product_lift_ne_one
    (e : Fin 4 ↪ X) (a b : G)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i)) :
    a * b ≠ 1 := by
  intro hc
  have hfix := product_lift_smul_base e a b haBase hbBase (0 : Fin 4)
  rw [hc, one_smul] at hfix
  exact e.injective.ne (by decide) hfix

theorem exists_double_fixed_single_moved
    (e : Fin 4 ↪ X) (a b : G)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (hcardEq : (MulAction.fixedBy X a).ncard =
      (MulAction.fixedBy X b).ncard) :
    ∃ p : X, b • p = p ∧ a • p ≠ p := by
  classical
  by_contra hnone
  push Not at hnone
  have hsub : MulAction.fixedBy X b ⊆ MulAction.fixedBy X a := by
    intro x hbx
    exact hnone x hbx
  have heq : MulAction.fixedBy X b = MulAction.fixedBy X a :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  have ha0 : e 0 ∈ MulAction.fixedBy X a := by
    change a • e 0 = e 0
    rw [haBase]
    rfl
  have hb0 : e 0 ∈ MulAction.fixedBy X b := by
    rw [heq]
    exact ha0
  change b • e 0 = e 0 at hb0
  rw [hbBase] at hb0
  exact e.injective.ne (by decide) hb0

theorem fixedBy_decomposition
    (e : Fin 4 ↪ X) (a b : G)
    (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (habComm : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (hcardAB : (MulAction.fixedBy X a).ncard =
      (MulAction.fixedBy X b).ncard)
    (hcardCB : (MulAction.fixedBy X (a * b)).ncard =
      (MulAction.fixedBy X b).ncard)
    (hFbUpper : (MulAction.fixedBy X b).ncard ≤ 3)
    (p : X) (hbp : b • p = p) (hap : a • p ≠ p) :
    let c := a * b
    let D := MulAction.fixedBy X a ∩ MulAction.fixedBy X b
    MulAction.fixedBy X b = {p, a • p} ∪ D ∧
    MulAction.fixedBy X a = {e 0, e 1} ∪ D ∧
    MulAction.fixedBy X c = {e 2, e 3} ∪ D := by
  classical
  dsimp only
  let c : G := a * b
  let D : Set X := MulAction.fixedBy X a ∩ MulAction.fixedBy X b
  have hab : a * b = c := rfl
  have hba : b * a = c := habComm.eq.symm.trans hab
  have haInv : ∀ z : X, a • (a • z) = z := by
    intro z
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have hbInv : ∀ z : X, b • (b • z) = z := by
    intro z
    rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  have habAct : ∀ z : X, a • (b • z) = c • z := by
    intro z
    rw [← mul_smul, hab]
  have hbaAct : ∀ z : X, b • (a • z) = c • z := by
    intro z
    rw [← mul_smul, hba]
  let q : X := a • p
  have hpq : p ≠ q := by simpa [q] using hap.symm
  have haq : a • q = p := by simp [q, haInv]
  have hbq : b • q = q := by
    calc
      b • q = b • (a • p) := rfl
      _ = c • p := hbaAct p
      _ = a • (b • p) := (habAct p).symm
      _ = q := by rw [hbp]
  have hFbEq : MulAction.fixedBy X b = {p, q} ∪ D := by
    ext z
    constructor
    · intro hbz
      by_cases hzp : z = p
      · simp [hzp]
      by_cases hzq : z = q
      · simp [hzq]
      have haz : a • z = z := by
        by_contra hmove
        have hbAz : b • (a • z) = a • z := by
          calc
            b • (a • z) = c • z := hbaAct z
            _ = a • (b • z) := (habAct z).symm
            _ = a • z := by rw [hbz]
        have hpaz : p ≠ a • z := by
          intro heq
          apply hzq
          have heq' := congrArg (fun w : X => a • w) heq
          have hqz : q = z := by
            change a • p = z
            exact heq'.trans (haInv z)
          exact hqz.symm
        have hqaz : q ≠ a • z := by
          intro heq
          apply hzp
          have heq' := congrArg (fun w : X => a • w) heq
          have hpz : p = z :=
            haq.symm.trans (heq'.trans (haInv z))
          exact hpz.symm
        have hfourCard :
            ({p, q, z, a • z} : Set X).ncard = 4 := by
          apply Set.ncard_eq_four.mpr
          exact ⟨p, q, z, a • z, hpq, Ne.symm hzp, hpaz,
            Ne.symm hzq, hqaz, Ne.symm hmove, rfl⟩
        have hfourSub : ({p, q, z, a • z} : Set X) ⊆
            MulAction.fixedBy X b := by
          intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact hbp
          · exact hbq
          · exact hbz
          · exact hbAz
        have hfourLe := Set.ncard_le_ncard hfourSub
        rw [hfourCard] at hfourLe
        omega
      right
      exact ⟨haz, hbz⟩
    · intro hz
      rcases hz with hz | hz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hbp
        · exact hbq
      · exact hz.2
  have hDfinite : D.Finite := Set.toFinite D
  have hpairPQ : ({p, q} : Set X).ncard = 2 := Set.ncard_pair hpq
  have hdisPQD : Disjoint ({p, q} : Set X) D := by
    rw [Set.disjoint_left]
    intro z hz hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hap hD.1
    · exact hpq (haq.symm.trans hD.1)
  have hFbCard :
      (MulAction.fixedBy X b).ncard = 2 + D.ncard := by
    rw [hFbEq, Set.ncard_union_eq hdisPQD, hpairPQ]
  have ha0 : a • e 0 = e 0 := by rw [haBase]; rfl
  have ha1 : a • e 1 = e 1 := by rw [haBase]; rfl
  have hb0 : b • e 0 ≠ e 0 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb1 : b • e 1 ≠ e 1 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hpair01 : ({e 0, e 1} : Set X).ncard = 2 :=
    Set.ncard_pair (e.injective.ne (by decide))
  have hdis01D : Disjoint ({e 0, e 1} : Set X) D := by
    rw [Set.disjoint_left]
    intro z hz hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hb0 hD.2
    · exact hb1 hD.2
  have h01DSub : ({e 0, e 1} : Set X) ∪ D ⊆
      MulAction.fixedBy X a := by
    intro z hz
    rcases hz with hz | hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ha0
      · exact ha1
    · exact hz.1
  have h01DCard : (({e 0, e 1} : Set X) ∪ D).ncard =
      (MulAction.fixedBy X a).ncard := by
    rw [Set.ncard_union_eq hdis01D, hpair01, hcardAB, hFbCard]
  have hFaEq : MulAction.fixedBy X a = {e 0, e 1} ∪ D := by
    symm
    apply Set.eq_of_subset_of_ncard_le h01DSub
    omega
  have hc2 : c ^ 2 = 1 := by
    simpa only [c] using product_involution_sq a b haTwo hbTwo habComm
  have hc2fix : c • e 2 = e 2 := by
    change (a * b) • e 2 = e 2
    rw [product_lift_smul_base e a b haBase hbBase]
    rfl
  have hc3fix : c • e 3 = e 3 := by
    change (a * b) • e 3 = e 3
    rw [product_lift_smul_base e a b haBase hbBase]
    rfl
  have ha2move : a • e 2 ≠ e 2 := by
    rw [haBase]
    exact e.injective.ne (by decide)
  have ha3move : a • e 3 ≠ e 3 := by
    rw [haBase]
    exact e.injective.ne (by decide)
  have hpair23 : ({e 2, e 3} : Set X).ncard = 2 :=
    Set.ncard_pair (e.injective.ne (by decide))
  have hdis23D : Disjoint ({e 2, e 3} : Set X) D := by
    rw [Set.disjoint_left]
    intro z hz hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha2move hD.1
    · exact ha3move hD.1
  have h23DSub : ({e 2, e 3} : Set X) ∪ D ⊆
      MulAction.fixedBy X c := by
    intro z hz
    rcases hz with hz | hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hc2fix
      · exact hc3fix
    · calc
        c • z = a • (b • z) := (habAct z).symm
        _ = a • z := by rw [hz.2]
        _ = z := hz.1
  have h23DCard : (({e 2, e 3} : Set X) ∪ D).ncard =
      (MulAction.fixedBy X c).ncard := by
    rw [Set.ncard_union_eq hdis23D, hpair23, hcardCB, hFbCard]
  have hFcEq : MulAction.fixedBy X c = {e 2, e 3} ∪ D := by
    symm
    apply Set.eq_of_subset_of_ncard_le h23DSub
    omega
  exact ⟨hFbEq, hFaEq, hFcEq⟩

theorem regular_four_set_ncard
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (habComm : Commute a b) (x : X)
    (hxa : a • x ≠ x) (hxb : b • x ≠ x)
    (hxc : (a * b) • x ≠ x) :
    ({x, a • x, b • x, (a * b) • x} : Set X).ncard = 4 := by
  have haInv : a • (a • x) = x := by
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have hbInv : b • (b • x) = x := by
    rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  have habAct : a • (b • x) = (a * b) • x := by
    rw [← mul_smul]
  have hbaAct : b • (a • x) = (a * b) • x := by
    rw [← mul_smul, habComm.eq.symm]
  have hac : a * (a * b) = b := by
    rw [← mul_assoc, ← pow_two, haTwo, one_mul]
  have hbc : b * (a * b) = a := by
    calc
      b * (a * b) = (b * a) * b := by rw [← mul_assoc]
      _ = (a * b) * b := by rw [← habComm.eq]
      _ = a * (b * b) := by rw [mul_assoc]
      _ = a := by rw [← pow_two, hbTwo, mul_one]
  have hxab : a • x ≠ b • x := by
    intro h
    apply hxc
    calc
      (a * b) • x = a • (b • x) := mul_smul _ _ _
      _ = a • (a • x) := congrArg (fun z : X => a • z) h.symm
      _ = x := haInv
  have hxac : a • x ≠ (a * b) • x := by
    intro h
    apply hxb
    calc
      b • x = (a * (a * b)) • x := by rw [hac]
      _ = a • ((a * b) • x) := mul_smul _ _ _
      _ = a • (a • x) := congrArg (fun z : X => a • z) h.symm
      _ = x := haInv
  have hxbc : b • x ≠ (a * b) • x := by
    intro h
    apply hxa
    calc
      a • x = (b * (a * b)) • x := by rw [hbc]
      _ = b • ((a * b) • x) := mul_smul _ _ _
      _ = b • (b • x) := congrArg (fun z : X => b • z) h.symm
      _ = x := hbInv
  apply Set.ncard_eq_four.mpr
  exact ⟨x, a • x, b • x, (a * b) • x,
    hxa.symm, hxb.symm, hxc.symm, hxab, hxac, hxbc, rfl⟩

theorem exceptional_fixed_union_ncard_eq_six_or_seven
    (e : Fin 4 ↪ X) (a b : G)
    (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (habComm : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (hcardAB : (MulAction.fixedBy X a).ncard =
      (MulAction.fixedBy X b).ncard)
    (hcardCB : (MulAction.fixedBy X (a * b)).ncard =
      (MulAction.fixedBy X b).ncard)
    (hFbUpper : (MulAction.fixedBy X b).ncard ≤ 3)
    (p : X) (hbp : b • p = p) (hap : a • p ≠ p) :
    ((MulAction.fixedBy X a ∪ MulAction.fixedBy X b) ∪
        MulAction.fixedBy X (a * b)).ncard = 6 ∨
      ((MulAction.fixedBy X a ∪ MulAction.fixedBy X b) ∪
        MulAction.fixedBy X (a * b)).ncard = 7 := by
  classical
  let q : X := a • p
  let D : Set X := MulAction.fixedBy X a ∩ MulAction.fixedBy X b
  obtain ⟨hFb, hFa, hFc⟩ :=
    fixedBy_decomposition e a b haTwo hbTwo habComm haBase hbBase
      hcardAB hcardCB hFbUpper p hbp hap
  have haInv : ∀ z : X, a • (a • z) = z := by
    intro z
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have haq : a • q = p := by
    simp only [q]
    exact haInv p
  have hbq : b • q = q := by
    calc
      b • q = b • (a • p) := rfl
      _ = a • (b • p) := by
        rw [← mul_smul, ← mul_smul, habComm.eq]
      _ = q := by rw [hbp]
  have hpq : p ≠ q := by
    simpa only [q] using hap.symm
  have ha0 : a • e 0 = e 0 := by rw [haBase]; rfl
  have ha1 : a • e 1 = e 1 := by rw [haBase]; rfl
  have ha2move : a • e 2 ≠ e 2 := by
    rw [haBase]
    exact e.injective.ne (by decide)
  have ha3move : a • e 3 ≠ e 3 := by
    rw [haBase]
    exact e.injective.ne (by decide)
  have hb0move : b • e 0 ≠ e 0 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb1move : b • e 1 ≠ e 1 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb2move : b • e 2 ≠ e 2 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb3move : b • e 3 ≠ e 3 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hpe0 : p ≠ e 0 := by
    intro h
    apply hap
    rw [h, ha0]
  have hpe1 : p ≠ e 1 := by
    intro h
    apply hap
    rw [h, ha1]
  have hpe2 : p ≠ e 2 := by
    intro h
    apply hb2move
    rw [← h, hbp]
  have hpe3 : p ≠ e 3 := by
    intro h
    apply hb3move
    rw [← h, hbp]
  have hqe0 : q ≠ e 0 := by
    intro h
    apply hpe0
    calc
      p = a • q := haq.symm
      _ = a • e 0 := congrArg (fun z : X => a • z) h
      _ = e 0 := ha0
  have hqe1 : q ≠ e 1 := by
    intro h
    apply hpe1
    calc
      p = a • q := haq.symm
      _ = a • e 1 := congrArg (fun z : X => a • z) h
      _ = e 1 := ha1
  have hqe2 : q ≠ e 2 := by
    intro h
    apply hb2move
    rw [← h, hbq]
  have hqe3 : q ≠ e 3 := by
    intro h
    apply hb3move
    rw [← h, hbq]
  have hqp : q ≠ p := hpq.symm
  have he0p : e 0 ≠ p := hpe0.symm
  have he1p : e 1 ≠ p := hpe1.symm
  have he2p : e 2 ≠ p := hpe2.symm
  have he3p : e 3 ≠ p := hpe3.symm
  have he0q : e 0 ≠ q := hqe0.symm
  have he1q : e 1 ≠ q := hqe1.symm
  have he2q : e 2 ≠ q := hqe2.symm
  have he3q : e 3 ≠ q := hqe3.symm
  let sixMap : Fin 6 → X := ![p, q, e 0, e 1, e 2, e 3]
  have hsixMap : Function.Injective sixMap := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [sixMap, e.injective.eq_iff, hpq, hpe0, hpe1, hpe2, hpe3,
        hqe0, hqe1, hqe2, hqe3, hqp, he0p, he1p, he2p, he3p,
        he0q, he1q, he2q, he3q] at hij ⊢
  let six : Set X := {p, q, e 0, e 1, e 2, e 3}
  have hrangeSix : Set.range sixMap = six := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [sixMap, six]
    · intro hz
      simp only [six, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
  have hsixCard : six.ncard = 6 := by
    rw [← hrangeSix, Set.ncard_range_of_injective hsixMap]
    norm_num
  have hsixD : Disjoint six D := by
    rw [Set.disjoint_left]
    intro z hz hD
    simp only [six, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hap hD.1
    · exact hpq (haq.symm.trans hD.1)
    · exact hb0move hD.2
    · exact hb1move hD.2
    · exact ha2move hD.1
    · exact ha3move hD.1
  have hpairD : Disjoint ({p, q} : Set X) D := by
    rw [Set.disjoint_left]
    intro z hz hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hap hD.1
    · exact hpq (haq.symm.trans hD.1)
  have hpairCard : ({p, q} : Set X).ncard = 2 :=
    Set.ncard_pair hpq
  have hFbCard : (MulAction.fixedBy X b).ncard = 2 + D.ncard := by
    rw [hFb, Set.ncard_union_eq hpairD, hpairCard]
  have hDle : D.ncard ≤ 1 := by
    rw [hFbCard] at hFbUpper
    omega
  have hFaMem (z : X) :
      z ∈ MulAction.fixedBy X a ↔ z = e 0 ∨ z = e 1 ∨ z ∈ D := by
    have hz := Set.ext_iff.mp hFa z
    simpa only [D, Set.mem_union, Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_assoc] using hz
  have hFbMem (z : X) :
      z ∈ MulAction.fixedBy X b ↔ z = p ∨ z = q ∨ z ∈ D := by
    have hz := Set.ext_iff.mp hFb z
    simpa only [q, D, Set.mem_union, Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_assoc] using hz
  have hFcMem (z : X) :
      z ∈ MulAction.fixedBy X (a * b) ↔ z = e 2 ∨ z = e 3 ∨ z ∈ D := by
    have hz := Set.ext_iff.mp hFc z
    simpa only [D, Set.mem_union, Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_assoc] using hz
  have hsixMem (z : X) :
      z ∈ six ↔ z = p ∨ z = q ∨ z = e 0 ∨ z = e 1 ∨ z = e 2 ∨ z = e 3 := by
    simp only [six, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hUnion :
      (MulAction.fixedBy X a ∪ MulAction.fixedBy X b) ∪
          MulAction.fixedBy X (a * b) = six ∪ D := by
    ext z
    simp only [Set.mem_union]
    constructor
    · rintro ((hza | hzb) | hzc)
      · rcases (hFaMem z).mp hza with h0 | h1 | hD
        · exact Or.inl ((hsixMem z).mpr (Or.inr (Or.inr (Or.inl h0))))
        · exact Or.inl ((hsixMem z).mpr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
        · exact Or.inr hD
      · rcases (hFbMem z).mp hzb with hp | hq | hD
        · exact Or.inl ((hsixMem z).mpr (Or.inl hp))
        · exact Or.inl ((hsixMem z).mpr (Or.inr (Or.inl hq)))
        · exact Or.inr hD
      · rcases (hFcMem z).mp hzc with h2 | h3 | hD
        · exact Or.inl ((hsixMem z).mpr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))))
        · exact Or.inl ((hsixMem z).mpr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3))))))
        · exact Or.inr hD
    · rintro (hz | hD)
      · rcases (hsixMem z).mp hz with hp | hq | h0 | h1 | h2 | h3
        · exact Or.inl (Or.inr ((hFbMem z).mpr (Or.inl hp)))
        · exact Or.inl (Or.inr ((hFbMem z).mpr (Or.inr (Or.inl hq))))
        · exact Or.inl (Or.inl ((hFaMem z).mpr (Or.inl h0)))
        · exact Or.inl (Or.inl ((hFaMem z).mpr (Or.inr (Or.inl h1))))
        · exact Or.inr ((hFcMem z).mpr (Or.inl h2))
        · exact Or.inr ((hFcMem z).mpr (Or.inr (Or.inl h3)))
      · exact Or.inl (Or.inl ((hFaMem z).mpr (Or.inr (Or.inr hD))))
  rw [hUnion, Set.ncard_union_eq hsixD, hsixCard]
  omega

end FiveTransitive.Research.HallVFourOrbits

end CFSG
