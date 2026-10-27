module

public import CFSG.Quasithin.H13.NQCatL2LieParabolic
public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BAlt

public section

namespace CFSG.Quasithin.Lie2Parabolic

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13 CFSG.Quasithin.Ch1Four

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem two_part_of_type {f : ℕ} :
    ((IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y) → ∃ o, Odd o ∧ Nat.card Y = 2 ^ (3 * f) * o) ∧
      (IsPSp4 2 f Y → ∃ o, Odd o ∧ Nat.card Y = 2 ^ (4 * f) * o) := by
  refine ⟨fun h => ?_, fun h => (card_psp4_two_part (Or.inl ⟨by decide, h⟩)).2⟩
  rcases h with h | ⟨K, _, _, hK, ⟨e⟩⟩
  · exact (card_psl3_two_part (Or.inl ⟨by decide, h⟩)).2
  · rcases Nat.eq_zero_or_pos f with rfl | hf
    · exfalso
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    have hq : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    refine ⟨_, (odd_pow_sub_one_of_even (n := 2) hq hq1 (by norm_num)).mul
      (odd_pow_sub_one_of_even (n := 3) hq hq1 (by norm_num)), ?_⟩
    rw [Nat.card_congr e.toEquiv, card_sl3, hK, ← pow_mul, mul_comm f 3]

omit [Finite Y] in
theorem lie_of_type {f : ℕ} (h : (IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y) ∨ IsPSp4 2 f Y) :
    IsSL3Ch5 f Y ∨ LieModel Y .PSp 2 2 f := by
  rcases h with (h | ⟨K, _, _, hK, ⟨e⟩⟩) | h
  · exact Or.inl (Or.inl (Or.inl ⟨by decide, h⟩))
  · exact Or.inl (Or.inr ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩)
  · exact Or.inr (Or.inl ⟨by decide, h⟩)

theorem exists_sylow_le_perfectCore {f : ℕ} (hf : 2 ≤ f)
    (h : (IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y) ∨ IsPSp4 2 f Y) {P : Subgroup Y}
    (hP : IsMaxParabolic2 (⊤ : Subgroup Y) P) :
    ∃ S : Subgroup Y, IsSylowTwoOf S ⊤ ∧ S ≤ perfectCore P ∧
      IsPSL 2 2 f (ModO2 (perfectCore P)) := by
  obtain ⟨⟨-, S, hS, hSP⟩, hne, hmax⟩ := hP
  have hSP' : Subgroup.normalizer (S : Set Y) ≤ P := by simpa using hSP
  obtain ⟨Pj, -, hcov, hj, -⟩ :=
    CFSG.Quasithin.H13.NQCat.factL2LieParabolic_holds Y f hf (lie_of_type h) S hS
  have hPcov : P ⋖ ⊤ := by
    refine ⟨lt_top_iff_ne_top.mpr hne, fun Q hPQ hQ => ?_⟩
    have hQP : Q = P := hmax Q ⟨le_top, S, hS, by simpa using hSP'.trans hPQ.le⟩ hQ.ne hPQ.le
    exact hPQ.ne hQP.symm
  obtain ⟨j, rfl⟩ := (hcov P hSP').mp hPcov
  exact ⟨S, hS, (hj j).2.1, (hj j).2.2⟩

theorem card_perfectCore {f a : ℕ} (hf : 2 ≤ f)
    (h : (IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y) ∨ IsPSp4 2 f Y) {P : Subgroup Y}
    (hP : IsMaxParabolic2 (⊤ : Subgroup Y) P) {o : ℕ} (ho : Odd o)
    (hY : Nat.card Y = 2 ^ (a * f) * o) :
    Nat.card (CFSG.pCore 2 ↥(perfectCore P)) = 2 ^ ((a - 1) * f) ∧
      Nat.card ↥(perfectCore P) = 2 ^ (a * f) * (2 ^ (2 * f) - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSC, hL2⟩ := exists_sylow_le_perfectCore hf h hP
  set C := perfectCore P with hC
  obtain ⟨b, hb⟩ := hS.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ S.index := by
    have : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hY' : Nat.card Y = 2 ^ b * S.index := by rw [← hb, Subgroup.card_mul_index]
  have hba : b = a * f :=
    (two_pow_mul_odd_inj (Nat.odd_iff.mpr (by omega)) ho (hY'.symm.trans hY)).1
  have hrel : Nat.card ↥C = 2 ^ b * S.relIndex C := by
    rw [← hb, ← Subgroup.relIndex_mul_card (H := S) (K := C), inf_eq_left.mpr hSC, mul_comm]
  have hodd : Odd (S.relIndex C) := by
    refine Nat.odd_iff.mpr ?_
    have hdvd : S.relIndex C ∣ S.index := Subgroup.relIndex_dvd_index_of_le hSC
    by_contra hev
    exact hidx ((Nat.dvd_of_mod_eq_zero (by omega)).trans hdvd)
  obtain ⟨-, hcL⟩ := card_of_isPSL_two_two hL2
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).exists_card_eq
  have hsplit := (CFSG.pCore 2 ↥C).card_eq_card_quotient_mul_card_subgroup
  rw [show Nat.card (↥C ⧸ CFSG.pCore 2 ↥C) = Nat.card (ModO2 C) from rfl, hcL, hc] at hsplit
  have h4 : Odd (4 ^ f - 1) := by
    have : Even (4 ^ f) := (Nat.even_pow' (by omega)).mpr (by decide)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) this odd_one
  have e1 : 2 ^ (f + c) * (4 ^ f - 1) = 2 ^ (a * f) * S.relIndex C := by
    rw [← hba, ← hrel, hsplit]
    ring
  obtain ⟨hfc, -⟩ := two_pow_mul_odd_inj h4 hodd e1
  have hc' : c = (a - 1) * f := by
    rw [Nat.sub_one_mul]
    omega
  refine ⟨by rw [hc, hc'], ?_⟩
  rw [hsplit, show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num, mul_comm, ← mul_assoc,
    ← pow_add, show c + f = a * f by omega]

theorem kgRank2ParabolicOrder_holds : Vol2.Ch10.SecB.C10KH.KGRank2ParabolicOrder := by
  intro Y _ _ f hf P hP
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨o, ho, hY⟩ := (two_part_of_type (Y := Y)).1 h
    exact (card_perfectCore hf (Or.inl h) hP ho hY).2
  · obtain ⟨o, ho, hY⟩ := (two_part_of_type (Y := Y)).2 h
    exact (card_perfectCore hf (Or.inr h) hP ho hY).2

end CFSG.Quasithin.Lie2Parabolic
