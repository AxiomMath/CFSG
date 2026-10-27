module

public import CFSG.RankThree.GF2n.Stroth78.Sec2FourLower
public import CFSG.RankThree.GF2n.Stroth78.Sec2Thirteen
public import CFSG.RankThree.GF2n.Stroth78.Reduction
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem QaOf_le_centralizer_centerIn_inf (S : Setting z E F) (a : G) :
    QaOf a ≤ Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨-, hyCent⟩ := Subgroup.mem_inf.mp hy
  have hyCent' : y ∈ Subgroup.centralizer (QaOf a : Set G) :=
    (Subgroup.mem_inf.mp hyCent).2
  exact (Subgroup.mem_centralizer_iff.mp hyCent' x hx).symm

theorem card_centerIn_QaOf_eq_card_ZQ (S : Setting z E F) {a : G}
    (hconj : IsConj z a) :
    Nat.card (centerIn (QaOf a)) = Nat.card (ZQ z) := by
  rw [card_centerIn_QaOf S hconj, ZQ_card S, Nat.mul_comm]

theorem centerIn_QaOf_le_sup_zpowers_of_le_Q_of_mem (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hza : z ∈ QaOf a)
    (hZQa : centerIn (QaOf a) ≤ Q z) :
    centerIn (QaOf a) ≤ Subgroup.zpowers a ⊔ ZQ z := by
  have hza_not : z ∉ centerIn (QaOf a) := z_not_mem_centerIn_Qa S haQ hconj haZ hza
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj
  let C : Subgroup G := Subgroup.centralizer ({a} : Set G) ⊓ Q z
  have hC_eq : Subgroup.centralizer (C : Set G) ⊓ Q z = Subgroup.zpowers a ⊔ ZQ z :=
    centralizer_centralizer_CQ_eq S haQ haZ ha2
  have hz2 : z ^ 2 = 1 := by
    simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  intro u huZ
  have huQa : u ∈ QaOf a := (Subgroup.mem_inf.mp huZ).1
  have huCent : u ∈ Subgroup.centralizer (QaOf a : Set G) := (Subgroup.mem_inf.mp huZ).2
  have huQ : u ∈ Q z := hZQa huZ
  have huCentral : u ∈ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨hcCent, hcQ⟩ := Subgroup.mem_inf.mp hc
    have hcuQa : c * u * c⁻¹ ∈ QaOf a :=
      fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hcCent huQa
    have hcuCent : c * u * c⁻¹ ∈ Subgroup.centralizer (QaOf a : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcinvCent : c⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.inv_mem (Subgroup.centralizer ({a} : Set G)) hcCent
      have hcxQa : c⁻¹ * x * c ∈ QaOf a := by
        change c⁻¹ * x * c ∈ fStar (Subgroup.centralizer ({a} : Set G))
        simpa using fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hcinvCent hx
      have hcomm := Subgroup.mem_centralizer_iff.mp huCent (c⁻¹ * x * c) hcxQa
      calc
        x * (c * u * c⁻¹) = c * ((c⁻¹ * x * c) * u) * c⁻¹ := by group
        _ = c * (u * (c⁻¹ * x * c)) * c⁻¹ := by rw [hcomm]
        _ = (c * u * c⁻¹) * x := by group
    have hcuZ : c * u * c⁻¹ ∈ centerIn (QaOf a) :=
      Subgroup.mem_inf.mpr ⟨hcuQa, hcuCent⟩
    have hwZ : (c * u * c⁻¹) * u⁻¹ ∈ centerIn (QaOf a) :=
      (centerIn (QaOf a)).mul_mem hcuZ ((centerIn (QaOf a)).inv_mem huZ)
    have hwQ : (c * u * c⁻¹) * u⁻¹ ∈ Q z :=
      (Q z).mul_mem ((Q z).mul_mem ((Q z).mul_mem hcQ huQ) ((Q z).inv_mem hcQ))
        ((Q z).inv_mem huQ)
    have hwz : (c * u * c⁻¹) * u⁻¹ ∈ Subgroup.zpowers z := by
      have hmem : ⁅c, u⁆ ∈ Subgroup.zpowers z := by
        rw [← Q_deriv_eq S]
        exact Subgroup.commutator_mem_commutator hcQ huQ
      have heq : ⁅c, u⁆ = (c * u * c⁻¹) * u⁻¹ := by
        rw [commutatorElement_def]
      rw [← heq]
      exact hmem
    have hw1 : (c * u * c⁻¹) * u⁻¹ = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · rw [← hk, zpow_mul]
        simp [hz2]
      · exfalso
        have heq : (c * u * c⁻¹) * u⁻¹ = z := by
          rw [← hk, zpow_add, zpow_mul]
          simp [hz2]
        exact hza_not (heq ▸ hwZ)
    calc
      c * u = ((c * u * c⁻¹) * u⁻¹) * (u * c) := by group
      _ = 1 * (u * c) := by rw [hw1]
      _ = u * c := by group
  rw [← hC_eq]
  exact Subgroup.mem_inf.mpr ⟨huCentral, huQ⟩

theorem card_zpowers_eq_two_of_isConj (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) :
    Nat.card (Subgroup.zpowers a) = 2 := by
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj
  have ha1 : a ≠ 1 := by
    intro h
    exact haZ (h.symm ▸ (ZQ z).one_mem)
  rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]

theorem zpowers_inf_ZQ_eq_bot (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) :
    Subgroup.zpowers a ⊓ ZQ z = ⊥ := by
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxa, hxW⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxa
  rw [Subgroup.mem_bot]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · rw [← hk, zpow_mul]
    simp [ha2]
  · exfalso
    apply haZ
    rw [← hk, zpow_add, zpow_mul] at hxW
    simpa [ha2] using hxW

theorem card_sup_zpowers_ZQ_eq_two_mul (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) :
    Nat.card ↥(Subgroup.zpowers a ⊔ ZQ z) = 2 * Nat.card (ZQ z) := by
  have hcomm : ∀ x ∈ ZQ z, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    have hxcent : x ∈ Subgroup.centralizer (Q z : Set G) := (Subgroup.mem_inf.mp hx).2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hax : Commute a x := Subgroup.mem_centralizer_iff.mp hxcent a haQ
    rw [← hk]
    exact (hax.symm.zpow_right k).eq
  have hinf : ZQ z ⊓ Subgroup.zpowers a = ⊥ := by
    rw [inf_comm]
    exact zpowers_inf_ZQ_eq_bot S hconj haZ
  have hcard := card_sup_of_comm (A := ZQ z) (B := Subgroup.zpowers a) hcomm hinf
  rw [sup_comm (Subgroup.zpowers a) (ZQ z), hcard,
    card_zpowers_eq_two_of_isConj S hconj haZ]
  ring

theorem card_ZQ_eq_two_mul_card_inf_of_le_sup (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hZQa : centerIn (QaOf a) ≤ Q z)
    (hsup : centerIn (QaOf a) ≤ Subgroup.zpowers a ⊔ ZQ z)
    (hza_not : z ∉ centerIn (QaOf a)) :
    Nat.card (ZQ z) = 2 * Nat.card ↥(ZQ z ⊓ centerIn (QaOf a)) := by
  set U : Subgroup G := centerIn (QaOf a) with hU
  set W : Subgroup G := ZQ z with hW
  have hWV : W ≤ Subgroup.zpowers a ⊔ W := le_sup_right
  have hUV : U ≤ Subgroup.zpowers a ⊔ W := hsup
  have haU : a ∈ U := mem_centerIn_QaOf_of_isConj S hconj
  have hjoin : U ⊔ W = Subgroup.zpowers a ⊔ W := by
    refine le_antisymm (sup_le hUV hWV) ?_
    exact sup_le ((Subgroup.zpowers_le.mpr haU).trans le_sup_left) le_sup_right
  have hcomm : ∀ x ∈ U, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hycent : y ∈ Subgroup.centralizer (Q z : Set G) := (Subgroup.mem_inf.mp hy).2
    exact Subgroup.mem_centralizer_iff.mp hycent x (hZQa hx)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U W hcomm).1
  have hVcard : Nat.card ↥(Subgroup.zpowers a ⊔ W) = 2 * Nat.card W := by
    rw [hW]
    exact card_sup_zpowers_ZQ_eq_two_mul S haQ hconj haZ
  have hUcard : Nat.card U = Nat.card W := by
    rw [hU, hW]
    exact card_centerIn_QaOf_eq_card_ZQ S hconj
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hEq : Nat.card W * (2 * Nat.card ↥(U ⊓ W)) = Nat.card W * Nat.card W := by
    calc
      Nat.card W * (2 * Nat.card ↥(U ⊓ W)) =
          (2 * Nat.card W) * Nat.card ↥(U ⊓ W) := by ring
      _ = Nat.card ↥(Subgroup.zpowers a ⊔ W) * Nat.card ↥(U ⊓ W) := by rw [hVcard]
      _ = Nat.card ↥(U ⊔ W) * Nat.card ↥(U ⊓ W) := by rw [hjoin]
      _ = Nat.card U * Nat.card W := hprod
      _ = Nat.card W * Nat.card W := by rw [hUcard]
  have h2 : 2 * Nat.card ↥(U ⊓ W) = Nat.card W := Nat.mul_left_cancel hWpos hEq
  have h2' : Nat.card W = 2 * Nat.card ↥(U ⊓ W) := h2.symm
  rw [inf_comm] at h2'
  simpa [hU, hW] using h2' 

theorem card_ZQ_eq_two_mul_card_inf_of_le (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hza : z ∈ QaOf a)
    (hZQa : centerIn (QaOf a) ≤ Q z) :
    Nat.card (ZQ z) = 2 * Nat.card ↥(ZQ z ⊓ centerIn (QaOf a)) := by
  have hza_not : z ∉ centerIn (QaOf a) := z_not_mem_centerIn_Qa S haQ hconj haZ hza
  have hsup := centerIn_QaOf_le_sup_zpowers_of_le_Q_of_mem S haQ hconj haZ hza hZQa
  exact card_ZQ_eq_two_mul_card_inf_of_le_sup S haQ hconj haZ hZQa hsup hza_not

theorem stroth78Hyperplane_of_centerIn_inf
    {a : G}
    (hcard : Nat.card (centerIn (Qa z)) =
      2 * Nat.card ↥(ZQ z ⊓ centerIn (QaOf a)))
    (hRnon : ¬ Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G) ≤
      (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G)) ⊔
        inSubgroup (pPrimeCore 2)
          (Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G))) :
    Stroth78Hyperplane z := by
  refine ⟨ZQ z ⊓ centerIn (QaOf a), inf_le_left, ?_, hRnon⟩
  simpa [ZQ] using hcard

theorem centerIn_Qa_not_le_Q_of_Qa_isPGroup_of_hyperplane
    (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hza : z ∈ QaOf a)
    (hRnon : ¬ Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G) ≤
      (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G)) ⊔
        inSubgroup (pPrimeCore 2)
          (Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G)))
    (h212 : Stroth78Assumption212 z) :
    ¬ centerIn (QaOf a) ≤ Q z := by
  intro hZQa
  have hcard := card_ZQ_eq_two_mul_card_inf_of_le S haQ hconj haZ hza hZQa
  exact h212 (stroth78Hyperplane_of_centerIn_inf hcard hRnon)

end CFSG.RankThree.GF2n.Stroth78
