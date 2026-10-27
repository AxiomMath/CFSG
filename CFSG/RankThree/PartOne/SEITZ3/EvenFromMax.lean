module

public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Arith

theorem not_dvd_and_not_modEq_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ q + 1) :
    ¬ p ∣ q ^ 4 * ((q ^ 2) ^ 2 + q ^ 2 + 1) ∧
      ¬ q ^ 4 * ((q ^ 2) ^ 2 + q ^ 2 + 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : (q : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    push_cast at this
    exact this
  have h3 : ((q ^ 4 * ((q ^ 2) ^ 2 + q ^ 2 + 1) : ℕ) : ZMod p) = ((3 : ℕ) : ZMod p) := by
    push_cast
    linear_combination ((q : ZMod p) ^ 7 - (q : ZMod p) ^ 6 + 2 * (q : ZMod p) ^ 5 -
      2 * (q : ZMod p) ^ 4 + 3 * (q : ZMod p) ^ 3 - 3 * (q : ZMod p) ^ 2 + 3 * (q : ZMod p) - 3) *
      h0
  constructor
  · intro h
    have h' : ((q ^ 4 * ((q ^ 2) ^ 2 + q ^ 2 + 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [h3] at h'
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 p).1 h')
    omega
  · intro h
    have h' := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    rw [h3] at h'
    have h'' : 3 ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff 3 1 p).1 h'
    have := Nat.le_of_dvd (by norm_num) ((Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 3)).1 h''.symm)
    omega

theorem ordG2_eq_index_mul {q : ℕ} (hq : 1 ≤ q) :
    ordG2 q = q ^ 4 * ((q ^ 2) ^ 2 + q ^ 2 + 1) * (q * (q ^ 2 - 1)) ^ 2 := by
  obtain ⟨z, hz⟩ : ∃ z, q ^ 2 = z + 1 := ⟨q ^ 2 - 1, by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    omega⟩
  have h6 : q ^ 6 = (z + 1) ^ 3 := by rw [← hz]; ring
  have h4 : q ^ 4 = (z + 1) ^ 2 := by rw [← hz]; ring
  have h6' : q ^ 6 - 1 = z * (z ^ 2 + 3 * z + 3) := by
    rw [h6]
    apply Nat.sub_eq_of_eq_add
    ring
  have hz' : q ^ 2 - 1 = z := by omega
  have hsq : (q * (q ^ 2 - 1)) ^ 2 = (z + 1) * z ^ 2 := by
    rw [mul_pow, hz', hz]
  unfold ordG2
  rw [hsq, h6', h6, h4, hz', hz]
  ring

end Arith

section Generation

theorem closure_cenGen_adjointG2_eq_top
    (hmax : MaxSL2SL2G2) (X : Type)
    [Field X] [Finite X]
    [CharP X 2] [IsSimpleGroup (adjointGroup .G2 X)] {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : Nat.card X = 2 ^ m) (hm : 1 ≤ m) (hpq : p ∣ Nat.card X + 1)
    (E₁ : Subgroup (adjointGroup .G2 X)) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL .G2 X) := finite_modGL
  have hq1 : 1 ≤ Nat.card X := Nat.card_pos
  have hq4 : 4 ≤ Nat.card X := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  have hpq2 : p ∣ Nat.card X ^ 2 - 1 := by
    rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ hq1]
    exact Dvd.dvd.mul_left hpq _
  have hΦ : Function.Injective (a1a1Hom X) := a1a1Hom_injective
  have hcardM : Nat.card (stdA1A1 X) = (Nat.card X * (Nat.card X ^ 2 - 1)) ^ 2 := card_stdA1A1
  have hcardG : Nat.card (adjointGroup .G2 X) = ordG2 (Nat.card X) := card_adjointGroup_G2
  have hidx : (stdA1A1 X).index =
      Nat.card X ^ 4 * ((Nat.card X ^ 2) ^ 2 + Nat.card X ^ 2 + 1) := by
    have h1 := Subgroup.index_mul_card (stdA1A1 X)
    rw [hcardM, hcardG, ordG2_eq_index_mul hq1] at h1
    have hpos : 0 < (Nat.card X * (Nat.card X ^ 2 - 1)) ^ 2 := by
      have : 0 < Nat.card X ^ 2 - 1 := by
        have : 4 ≤ Nat.card X ^ 2 := by nlinarith
        omega
      positivity
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  obtain ⟨hnd, hmod⟩ := not_dvd_and_not_modEq_one hp hp5 hpq
  rw [← hidx] at hnd hmod
  have hdvdSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) X) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hpq2 _
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' p hdvdSL
  have hep : e ^ p = 1 := by rw [← he]; exact pow_orderOf_eq_one e
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    exact hp.one_lt.ne he
  have hzp : ∀ a ∈ Subgroup.zpowers e, a ^ p = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep, one_zpow]
  let E'₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) X × Matrix.SpecialLinearGroup (Fin 2) X) :=
    (Subgroup.zpowers e).prod (Subgroup.zpowers e)
  let E' : Subgroup (adjointGroup .G2 X) := E'₀.map (a1a1Hom X)
  have hE'M : E' ≤ stdA1A1 X := Subgroup.map_le_range _ _
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have hab : (a, b) ^ p = (a ^ p, b ^ p) := rfl
    rw [← map_pow, hab, hzp a ha, hzp b hb]
    exact map_one _
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hΦ]
    have h1 : Nat.card E'₀ = Nat.card (Subgroup.zpowers e) * Nat.card (Subgroup.zpowers e) :=
      (Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers e) (Subgroup.zpowers e)).toEquiv).trans
        (Nat.card_prod _ _)
    rw [h1, Nat.card_zpowers, he, sq]
  let M : Subgroup (adjointGroup .G2 X) := stdA1A1 X
  have hEmp : IsPGroup p ↥(E'.subgroupOf M) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv, hE'c]
  obtain ⟨Q, hQ⟩ := hEmp.exists_le_sylow
  let S : Subgroup (adjointGroup .G2 X) := (Q : Subgroup ↥M).map M.subtype
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hE'S : E' ≤ S := by
    intro x hx
    exact ⟨⟨x, hE'M hx⟩, hQ hx, rfl⟩
  have hSp : IsPGroup p ↥S := Q.isPGroup'.map M.subtype
  have hSidx : ¬ p ∣ S.index := by
    have h1 : S.index = (Q : Subgroup ↥M).index * M.index := Subgroup.index_map_subtype _
    rw [h1]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact Q.not_dvd_index h
    · exact hnd h
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.K128.sylowShape_G2 X hp hp5 hX hm hpq2 S hSp hSidx
  have hmaxN : ∀ N : Subgroup (adjointGroup .G2 X), M ≤ N → N = M ∨ N = ⊤ := hmax X hq4
  have hgen : M ≤ Subgroup.closure (cenGen E') := by
    rintro _ ⟨⟨A, B⟩, rfl⟩
    have e1 : a1a1Hom X (A, B) = a1a1Hom X (A, 1) * a1a1Hom X (1, B) := by
      rw [← map_mul]; simp
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
    · refine ⟨a1a1Hom X (1, e), ⟨(1, e), ⟨one_mem _, Subgroup.mem_zpowers e⟩, rfl⟩, ?_, ?_⟩
      · intro h
        have := hΦ (h.trans (map_one _).symm)
        exact he1 (congrArg Prod.snd this)
      · rw [← map_mul, ← map_mul]
        simp
    · refine ⟨a1a1Hom X (e, 1), ⟨(e, 1), ⟨Subgroup.mem_zpowers e, one_mem _⟩, rfl⟩, ?_, ?_⟩
      · intro h
        have := hΦ (h.trans (map_one _).symm)
        exact he1 (congrArg Prod.fst this)
      · rw [← map_mul, ← map_mul]
        simp
  exact closure_cenGen_eq_top M S E' φ hSM hSp hSidx hE'S hE'p hE'c hmaxN hmod hgen E₁ hE₁p hE₁c

end Generation

section Assembly

theorem extSeitzAtInnerFor_G2_even
    (hmax : MaxSL2SL2G2) {q : TauCeti.PrimePower}
    (hq : q.p = 2) : CTP.ExtSeitzAtInnerFor (.G2 q) fun p => ¬ p ∣ q.card - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 _ hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := CTP.exists_adjointG2_model hiso
  have hXq : Nat.card X = q.card := by rw [hX, PrimePower.card_def]
  have : IsSimpleGroup (adjointGroup .G2 X) := MulEquiv.isSimpleGroup e.symm
  have : CharP X 2 := by
    have := finite_field_prime_power_characteristic q.prime_p q.exponent_pos hX
    rwa [hq] at this
  have hXm : Nat.card X = 2 ^ q.exponent := by rw [hX, hq]
  refine CTP.closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  by_cases hpq : p ∣ Nat.card X + 1
  · exact closure_cenGen_adjointG2_eq_top hmax X hp hp5 hXm q.exponent_pos hpq E₁ hE₁p hcard₁
  · exfalso
    have hq1 : 1 ≤ Nat.card X := Nat.card_pos
    have hnd : ¬ p ∣ Nat.card X ^ 2 - 1 := by
      rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ hq1]
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hP (by rwa [← hXq])
      · exact hpq h
    have : Finite (ModGL .G2 X) := finite_modGL
    have hdvd : p ∣ Nat.card (adjointGroup .G2 X) := by
      have h1 := Subgroup.card_subgroup_dvd_card E₁
      rw [hcard₁] at h1
      exact (dvd_pow_self p two_ne_zero).trans h1
    have h1 := CFSG.RankThree.PartOne.K128.pRank_le_one_G2 X hp hp5 hXm q.exponent_pos hdvd hnd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
    omega

end Assembly

end CFSG.RankThree.PartOne.SEITZ3
