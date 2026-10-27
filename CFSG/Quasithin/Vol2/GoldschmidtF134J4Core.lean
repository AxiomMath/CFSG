module

public import CFSG.Quasithin.Vol2.GoldschmidtF134J4Local
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4Nine
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4EOrbit

public section

namespace CFSG.Quasithin.F134.J4E9

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CFSG.QuasithinUnique.Setup.X1

theorem eq_one_of_pow_three_of_isPGroup_two {G : Type*} [Group G] {S : Subgroup G}
    (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  have h2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one h2))

theorem exists_normalized
    {Pt : Subgroup J} (hPt : Nat.card Pt = 9) (hPt3 : ∀ x ∈ Pt, x ^ 3 = 1)
    (hK : Nat.card ↥(Pt ⊔ P0) = 9 * 2 ^ 21) :
    ∃ U : Subgroup J, U ≤ Pt ∧ U ≠ ⊥ ∧ U ≠ Pt ∧
      ∀ l ∈ P0, l ∈ Subgroup.normalizer (Pt : Set J) → l ∈ Subgroup.normalizer (U : Set J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM := j4Facts.mat
  have hF := j4Facts
  have hEl := elem_uJ hM
  set K : Subgroup J := Pt ⊔ P0 with hKdef
  have hPtK : Pt ≤ K := le_sup_left
  have hP0K : P0 ≤ K := le_sup_right
  have hEP0 : Eg uJ 11 ≤ P0 := Eg_le_P0
  have hEK : Eg uJ 11 ≤ K := hEP0.trans hP0K
  have hP0H : P0 ≤ Hj := P0_le_Hj
  let Sk : Subgroup K := MulAction.stabilizer K basePt
  have hSkmem : ∀ x : K, x ∈ Sk ↔ (x : J) ∈ Hj := fun x => by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, smul_basePt_eq_self_iff]
  have hP0Sk : P0.subgroupOf K ≤ Sk := fun x hx =>
    (hSkmem x).mpr (hP0H (Subgroup.mem_subgroupOf.mp hx))
  have hP0card : Nat.card (P0.subgroupOf K) = 2 ^ 21 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0K).toEquiv, card_P0 hM hF]
  have hdvd : 2 ^ 21 ∣ Nat.card Sk := hP0card ▸ Subgroup.card_dvd_of_le hP0Sk
  have hcard := Sk.card_mul_index
  obtain ⟨c, hc⟩ := hdvd
  have hcidx : c * Sk.index = 9 := by
    rw [hc, hK, mul_assoc] at hcard
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hcard
  have hidx : Sk.index = 1 ∨ Sk.index = 3 ∨ Sk.index = 9 := by
    obtain ⟨i, hi, hiv⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show Sk.index ∣ 3 ^ 2 by simpa using Dvd.intro_left c hcidx)
    interval_cases i <;> simp_all
  rcases hidx with h1 | h3 | h9
  ·
    have hKH : K ≤ Hj := by
      intro x hx
      have : (⟨x, hx⟩ : K) ∈ Sk := by
        rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      exact (hSkmem ⟨x, hx⟩).mp this
    exact exists_normalized_of_le_Hj hKH hP0K hPtK hK hPt hPt3
  ·
    exfalso
    have hSkne : Sk ≠ ⊤ := by
      intro h
      rw [← Subgroup.index_eq_one] at h
      omega
    obtain ⟨x, hx⟩ : ∃ x : K, x ∉ Sk := by
      by_contra hcon
      push Not at hcon
      exact hSkne (eq_top_iff.mpr fun x _ => hcon x)
    have hxw : (x : J) • basePt ≠ basePt := fun h =>
      hx ((hSkmem x).mpr (smul_basePt_eq_self_iff.mp h))
    have h4 := four_le_ncard_orbit hxw
    have horb : (MulAction.orbit K basePt).ncard = 3 := by
      rw [← MulAction.index_stabilizer]
      exact h3
    have hsub : {w : J ⧸ Hj | ∃ e ∈ Eg uJ 11, e • ((x : J) • basePt) = w} ⊆
        MulAction.orbit K basePt \ {basePt} := by
      rintro _ ⟨e, he, rfl⟩
      refine ⟨⟨⟨(e : J) * x, K.mul_mem (hEK he) x.2⟩, ?_⟩, ?_⟩
      · show ((e : J) * x) • basePt = e • ((x : J) • basePt)
        rw [mul_smul]
      · intro h
        apply hxw
        have h' : (e : J)⁻¹ • (e • ((x : J) • basePt)) = (e : J)⁻¹ • basePt := by
          rw [Set.mem_singleton_iff.mp h]
        rwa [inv_smul_smul, smul_basePt_eq_self_iff.mpr (Eg_le_Hj (inv_mem he))] at h'
    have hfin : (MulAction.orbit K basePt).Finite := Set.finite_range _
    have h5 := Set.ncard_le_ncard hsub hfin.sdiff
    rw [Set.ncard_sdiff_singleton_of_mem (MulAction.mem_orbit_self basePt), horb] at h5
    omega
  ·
    have hSkcard : Nat.card Sk = 2 ^ 21 := by
      have : c = 1 := by
        rw [h9] at hcidx
        omega
      rw [hc, this, mul_one]
    have hSkp : IsPGroup 2 Sk := IsPGroup.of_card hSkcard
    by_cases hnor : ∃ M : Subgroup K, M.Normal ∧ Nat.card ↥(M ⊓ Pt.subgroupOf K) = 3
    · obtain ⟨M, hMn, hM3⟩ := hnor
      have hUcard : Nat.card ((M ⊓ Pt.subgroupOf K).map K.subtype) = 3 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hM3]
      refine ⟨(M ⊓ Pt.subgroupOf K).map K.subtype, ?_, ?_, ?_, ?_⟩
      · rintro _ ⟨m, hm, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hm.2
      · intro h
        rw [h] at hUcard
        simp at hUcard
      · intro h
        rw [h, hPt] at hUcard
        omega
      · refine mem_normalizer_of_conj P0 (Subgroup.normalizer (Pt : Set J)) _ ?_
        intro l hlA hlB u hu
        obtain ⟨m, hm, rfl⟩ := hu
        have hlK : l ∈ K := hP0K hlA
        have h1 : (⟨l, hlK⟩ : K) * m * (⟨l, hlK⟩ : K)⁻¹ ∈ M ⊓ Pt.subgroupOf K := by
          refine ⟨hMn.conj_mem m hm.1 ⟨l, hlK⟩, Subgroup.mem_subgroupOf.mpr ?_⟩
          show l * (m : J) * l⁻¹ ∈ Pt
          exact (Subgroup.mem_normalizer_iff.mp hlB _).mp (Subgroup.mem_subgroupOf.mp hm.2)
        exact ⟨_, h1, rfl⟩
    · exfalso
      refine no_nine (X := K) (Ω := J ⧸ Hj) basePt (Pt.subgroupOf K) ((Eg uJ 11).subgroupOf K)
        ?_ ?_ hSkp h9 ?_ ?_ ?_ ?_ ?_ fun M hMn h3 => hnor ⟨M, hMn, h3⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPtK).toEquiv, hPt]
      · intro x hx
        exact Subtype.ext (by simpa using hPt3 _ (Subgroup.mem_subgroupOf.mp hx))
      · intro x hx hxw
        have hxS : x ∈ Sk := hxw
        have := eq_one_of_pow_three_of_isPGroup_two hSkp hxS (Subtype.ext (by
          simpa using hPt3 _ (Subgroup.mem_subgroupOf.mp hx)))
        exact this
      · intro e he
        show (e : J) • basePt = basePt
        exact smul_basePt_eq_self_iff.mpr (Eg_le_Hj (Subgroup.mem_subgroupOf.mp he))
      · intro a ha b hb
        exact Subtype.ext (Eg_comm hEl (Subgroup.mem_subgroupOf.mp ha)
          (Subgroup.mem_subgroupOf.mp hb))
      · intro a ha
        exact Subtype.ext (Eg_sq hEl (Subgroup.mem_subgroupOf.mp ha))
      · intro x hx
        have h4 := four_le_ncard_orbit (g := (x : J)) hx
        have hset : {w : J ⧸ Hj | ∃ e ∈ (Eg uJ 11).subgroupOf K, e • (x • basePt) = w} =
            {w | ∃ e ∈ Eg uJ 11, e • ((x : J) • basePt) = w} := by
          ext w
          constructor
          · rintro ⟨e, he, rfl⟩
            exact ⟨e, Subgroup.mem_subgroupOf.mp he, rfl⟩
          · rintro ⟨e, he, rfl⟩
            exact ⟨⟨e, hEK he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
        rw [hset]
        exact h4

end CFSG.Quasithin.F134.J4E9
