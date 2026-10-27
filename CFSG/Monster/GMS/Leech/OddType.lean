module

public import CFSG.Monster.GMS.Leech.OddPhi
public import CFSG.Monster.GMS.Leech.OddFrattini

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem card_leechQ_inf_inf
    [Finite G] (hI : Co1InvolutionFacts) {t y : G}
    (h : IsLeechCentralLift z t) (h' : IsLeechCentralLift z y) :
    Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) =
      2 * (co1Fix (L.φ ⟨t, h.mem_centralizer⟩) ∩ co1Fix (L.φ ⟨y, h'.mem_centralizer⟩)).ncard := by
  have hset : ((leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) =
      {g : G | g ∈ leechQ z ∧ L.vec g ∈
        co1Fix (L.φ ⟨t, h.mem_centralizer⟩) ∩ co1Fix (L.φ ⟨y, h'.mem_centralizer⟩)} := by
    ext q
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hqQ, hqt⟩, hqy⟩
      exact ⟨hqQ, L.vec_mem_co1Fix_of_comm h.mem_centralizer hqQ hqt.symm,
        L.vec_mem_co1Fix_of_comm h'.mem_centralizer hqQ hqy.symm⟩
    · rintro ⟨hqQ, hr, hs⟩
      exact ⟨⟨hqQ, (L.commute_of_vec_mem_co1Fix hI h hqQ hr).symm⟩,
        (L.commute_of_vec_mem_co1Fix hI h' hqQ hs).symm⟩
  have h2 : Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) = ((leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  rw [h2, hset, L.ncard_preimage]

theorem image_triple
    [Finite G] (hI : Co1InvolutionFacts) {t y : G} (h : IsLeechCentralLift z t)
    (h' : IsLeechCentralLift z y) (hodd : Odd (orderOf (t * y))) :
    L.image (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) =
      Subgroup.centralizer ({L.φ ⟨t, h.mem_centralizer⟩} : Set Co1) ⊓
        Subgroup.centralizer ({L.φ ⟨y, h'.mem_centralizer⟩} : Set Co1) := by
  ext x
  rw [L.mem_image, Subgroup.mem_inf]
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, hcD, rfl⟩
    obtain ⟨hcD', hcy⟩ := Subgroup.mem_inf.1 hcD
    obtain ⟨-, hct⟩ := Subgroup.mem_inf.1 hcD'
    rw [Subgroup.mem_centralizer_singleton_iff] at hct hcy
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hct
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcy
  · rintro ⟨hr, hs⟩
    obtain ⟨c, rfl⟩ := L.φ_surj x
    have hg : (c : G) ∈ Subgroup.centralizer ({z} : Set G) := c.2
    have hconj : ∀ {a : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G)),
        L.φ ⟨a, ha⟩ * L.φ c = L.φ c * L.φ ⟨a, ha⟩ →
        (a⁻¹ * ((c : G) * a * (c : G)⁻¹) ∈ leechQ z) := by
      intro a ha hcomm
      refine L.inv_mul_conj_mem_of_phi_conj ha ha hg ?_
      rw [← hcomm]
      group
    obtain ⟨p, hp, hpt, hpy⟩ := L.exists_conj_of_odd_pair hI h h'.mem_centralizer
      h'.mem_centralizer h'.mul_self h'.mul_self hodd hodd hg (hconj h.mem_centralizer hr.symm)
      (hconj h'.mem_centralizer hs.symm)
    have hpC : p ∈ Subgroup.centralizer ({z} : Set G) := L.mem_centralizer hp
    have hpgC : p * (c : G) ∈ Subgroup.centralizer ({z} : Set G) := mul_mem hpC hg
    have hpy' : p * (c : G) ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hpy)
    refine ⟨⟨p * (c : G), hpgC⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hpgC, hpt⟩, hpy'⟩, ?_⟩
    rw [L.phi_mul hpC hg, (L.φ_ker ⟨p, hpC⟩).2 hp, one_mul]

theorem card_triple_eq
    [Finite G] (hI : Co1InvolutionFacts) {t y : G} (h : IsLeechCentralLift z t)
    (h' : IsLeechCentralLift z y) (hodd : Odd (orderOf (t * y))) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) =
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)) *
        Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, h.mem_centralizer⟩} : Set Co1) ⊓
          Subgroup.centralizer ({L.φ ⟨y, h'.mem_centralizer⟩} : Set Co1)) := by
  have hD : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    inf_le_left.trans inf_le_left
  rw [L.card_eq_card_image_mul _ hD, L.image_triple hI h h' hodd]
  have hQD : leechQ z ⊓ (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) =
      leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hg, ⟨-, ht⟩, hy⟩
      exact ⟨⟨hg, ht⟩, hy⟩
    · rintro ⟨⟨hg, ht⟩, hy⟩
      exact ⟨hg, ⟨L.mem_centralizer hg, ht⟩, hy⟩
  rw [hQD, mul_comm]

omit [Group G] L in
private theorem type_iff_aux {o a b : ℕ} {O A B : ℕ} (hA : 0 < A) :
    (o = O ∧ 2 * a = 2 * A ∧ 2 * a * b = 2 * A * B) ↔ (o = O ∧ a = A ∧ b = B) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have ha : a = A := by omega
    subst ha
    exact ⟨h0, rfl, Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * a) h2⟩
  · rintro ⟨h0, rfl, rfl⟩
    exact ⟨h0, rfl, rfl⟩

theorem leechOddType_iff
    [Finite G] (hI : Co1InvolutionFacts) {t y : G}
    (h : IsLeechCentralLift z t) (h' : IsLeechCentralLift z y) (hodd : Odd (orderOf (t * y)))
    (k : Fin 3) :
    LeechOddType z t y k ↔
      Co1OddType (L.φ ⟨t, h.mem_centralizer⟩) (L.φ ⟨y, h'.mem_centralizer⟩) k := by
  have ho := L.orderOf_phi_mul h.mem_centralizer h'.mem_centralizer hodd
  have hq := L.card_leechQ_inf_inf hI h h'
  have hd := L.card_triple_eq hI h h' hodd
  rw [hq] at hd
  set a := (co1Fix (L.φ ⟨t, h.mem_centralizer⟩) ∩ co1Fix (L.φ ⟨y, h'.mem_centralizer⟩)).ncard
  set b := Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, h.mem_centralizer⟩} : Set Co1) ⊓
    Subgroup.centralizer ({L.φ ⟨y, h'.mem_centralizer⟩} : Set Co1))
  fin_cases k
  · simp only [LeechOddType, Co1OddType, ho, hq, hd]
    exact type_iff_aux (o := orderOf (t * y)) (O := 3) (A := 2 ^ 10) (B := 2 ^ 7 * 3 ^ 5 * 5)
      (by norm_num)
  · simp only [LeechOddType, Co1OddType, ho, hq, hd]
    exact type_iff_aux (o := orderOf (t * y)) (O := 3) (A := 2 ^ 8) (B := 2 ^ 6 * 3 ^ 4 * 5 * 7)
      (by norm_num)
  · simp only [LeechOddType, Co1OddType, ho, hq, hd]
    exact type_iff_aux (o := orderOf (t * y)) (O := 5) (A := 2 ^ 8) (B := 2 ^ 5 * 3 ^ 2 * 5 ^ 2)
      (by norm_num)

theorem hasCommonLeechFour_iff
    [Finite G] (hI : Co1InvolutionFacts) {t y : G}
    (h : IsLeechCentralLift z t) (h' : IsLeechCentralLift z y) :
    HasCommonLeechFour z t y ↔
      Co1CommonFour (L.φ ⟨t, h.mem_centralizer⟩) (L.φ ⟨y, h'.mem_centralizer⟩) := by
  constructor
  · rintro ⟨w₀, hw₀, hwt, hwy⟩
    have hw₀4 := (L.isLeechFour_iff).1 hw₀
    exact ⟨L.vec w₀, hw₀4.2,
      L.vec_mem_co1Fix_of_comm h.mem_centralizer hw₀4.1
        (Subgroup.mem_centralizer_singleton_iff.1 hwt).symm,
      L.vec_mem_co1Fix_of_comm h'.mem_centralizer hw₀4.1
        (Subgroup.mem_centralizer_singleton_iff.1 hwy).symm⟩
  · rintro ⟨v, hv4, hvr, hvs⟩
    obtain ⟨w₀, hw₀Q, hw₀v⟩ := L.vec_surj v
    have hw₀4 : w₀ ∈ L.typeSet 2 := ⟨hw₀Q, by rw [hw₀v]; exact hv4⟩
    exact ⟨w₀, (L.isLeechFour_iff).2 hw₀4,
      Subgroup.mem_centralizer_singleton_iff.2
        (L.commute_of_vec_mem_co1Fix hI h hw₀Q (by rw [hw₀v]; exact hvr)).symm,
      Subgroup.mem_centralizer_singleton_iff.2
        (L.commute_of_vec_mem_co1Fix hI h' hw₀Q (by rw [hw₀v]; exact hvs)).symm⟩

theorem eq_of_phi_eq {t y : G} (h : IsLeechCentralLift z t) (h' : IsLeechCentralLift z y)
    (hodd : Odd (orderOf (t * y)))
    (hφ : L.φ ⟨y, h'.mem_centralizer⟩ = L.φ ⟨t, h.mem_centralizer⟩) : y = t := by
  have h1 : t⁻¹ * y ∈ leechQ z := (L.phi_eq_iff h.mem_centralizer h'.mem_centralizer).1 hφ.symm
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.mul_self
  rw [hti] at h1
  have h2 := L.eq_one_of_odd_orderOf h1 hodd
  calc y = t⁻¹ * (t * y) := by group
    _ = t⁻¹ := by rw [h2, mul_one]
    _ = t := hti

end LeechSystem

end CFSG.Monster.GMS
