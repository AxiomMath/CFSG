module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

private theorem w183_exceptionalOrders_psl_two {s f : ℕ} (hs2 : s ≠ 2) (hs3 : s ≠ 3) :
    exceptionalOrders .PSL 2 s f = (1, 1) := by
  unfold exceptionalOrders
  split <;> first | rfl | simp_all

private theorem w183_exceptionalOrders_psl_three {s f : ℕ} (hs2 : s ≠ 2) :
    exceptionalOrders .PSL 3 s f = (1, 1) := by
  unfold exceptionalOrders
  split <;> first | rfl | simp_all

private theorem w183_exceptionalOrders_psu_three {s f : ℕ} :
    exceptionalOrders .PSU 3 s f = (1, 1) := by
  unfold exceptionalOrders
  split <;> first | rfl | simp_all

private theorem w183_gcd_three_sub_one_eq_one {m : ℕ} (hm : m % 3 = 2) :
    Nat.gcd 3 (m - 1) = 1 := by
  have h1 : (m - 1) % 3 = 1 := by omega
  rw [← Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hd
  have h0 : (m - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  omega

private theorem w183_gcd_three_add_one_eq_one {m : ℕ} (hm : m % 3 = 1) :
    Nat.gcd 3 (m + 1) = 1 := by
  have h1 : (m + 1) % 3 = 2 := by omega
  rw [← Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hd
  have h0 : (m + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  omega

theorem Socle185Shape.exists_lieModel_table_dvd_two {S : Type} [Group S] (h : Socle185Shape S) :
    ∃ (t : StatedLieTag) (n p f : ℕ), CFSG.Models.LieModel S t n p f ∧
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) ∣ 2 := by
  rcases h with ⟨p, e, hp, hp5, he, hS⟩ | ⟨p, f, hp, hp5, h⟩ | hS
  ·
    refine ⟨.PSL, 2, p, e, ⟨hS.1, Or.inl hS⟩, ?_⟩
    have hgen : genericOrders .PSL 2 p e = (Nat.gcd 2 (p ^ e - 1), 1) := rfl
    have hexc : exceptionalOrders .PSL 2 p e = (1, 1) :=
      w183_exceptionalOrders_psl_two (by omega) (by omega)
    rw [hgen, hexc]
    simp only [Prod.fst, Prod.snd, mul_one, one_mul]
    exact Nat.gcd_dvd_left 2 (p ^ e - 1)
  · rcases h with ⟨h3, h4, hS⟩ | ⟨h3, h4, hS⟩
    ·
      refine ⟨.PSL, 3, p, f, ⟨CFSG.Blueprint.LieModel.admissible hS,
        Or.inl (CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide))⟩, ?_⟩
      have hgen : genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := rfl
      have hexc : exceptionalOrders .PSL 3 p f = (1, 1) :=
        w183_exceptionalOrders_psl_three (by omega)
      rw [hgen, hexc]
      simp only [Prod.fst, Prod.snd, mul_one, one_mul]
      rw [w183_gcd_three_sub_one_eq_one h3]
      norm_num
    ·
      refine ⟨.PSU, 3, p, f, ⟨CFSG.Blueprint.LieModel.admissible hS,
        Or.inl (CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide))⟩, ?_⟩
      have hgen : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := rfl
      have hexc : exceptionalOrders .PSU 3 p f = (1, 1) := w183_exceptionalOrders_psu_three
      rw [hgen, hexc]
      simp only [Prod.fst, Prod.snd, mul_one, one_mul]
      rw [w183_gcd_three_add_one_eq_one h3]
      norm_num
  ·
    refine ⟨.PSL, 2, 7, 1, ⟨hS.1, Or.inl hS⟩, ?_⟩
    have hgen : genericOrders .PSL 2 7 1 = (Nat.gcd 2 (7 ^ 1 - 1), 1) := rfl
    have hexc : exceptionalOrders .PSL 2 7 1 = (1, 1) :=
      w183_exceptionalOrders_psl_two (by norm_num) (by norm_num)
    rw [hgen, hexc]
    simp only [Prod.fst, Prod.snd, mul_one, one_mul]
    norm_num

theorem oddMultiplierSocle185_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    OddMultiplierSocle185 := by
  intro S _ hS X _ _ Z _ hZc hZodd hperf hiso
  obtain ⟨e⟩ := hiso
  haveI : Finite S := Finite.of_equiv (X ⧸ Z) e.toEquiv
  haveI hsimp : IsSimpleGroup S := hS.isSimpleGroup
  have hnab : ∃ a b : S, a * b ≠ b * a := hS.exists_not_commute
  have hcenterS : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hcenter_le_Z : Subgroup.center X ≤ Z := by
    intro c hc
    have hcS : e (c : X ⧸ Z) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨u, rfl⟩ := e.surjective s
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z u
      change e (a : X ⧸ Z) * e (c : X ⧸ Z) = e (c : X ⧸ Z) * e (a : X ⧸ Z)
      rw [← map_mul, ← map_mul]
      congr 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.mp hc a]
    rw [hcenterS, Subgroup.mem_bot] at hcS
    have h1 : (c : X ⧸ Z) = 1 := e.injective (by rw [hcS, map_one])
    exact (QuotientGroup.eq_one_iff c).mp h1
  have hZeq : Z = Subgroup.center X := le_antisymm hZc hcenter_le_Z
  have hperf' : Group.IsPerfect X := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    exact hperf
  obtain ⟨t, n, p, f, hm, hdvd⟩ := hS.exists_lieModel_table_dvd_two
  have hdvd' : Nat.card (Subgroup.center X) ∣ 2 :=
    (CFSG.RankThree.PartTwo.Sec21.Item221Proof.card_center_dvd_table hGA hperf'
      ((QuotientGroup.quotientMulEquivOfEq hZeq.symm).trans e) hm).trans hdvd
  have hZdvd : Nat.card ↥Z ∣ 2 := by rwa [hZeq]
  have hZ1 : Nat.card ↥Z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hZdvd with h | h
    · exact h
    · exfalso
      rw [h] at hZodd
      norm_num at hZodd
  exact Subgroup.eq_bot_of_card_eq Z hZ1

end CFSG.LocalAnalysis.WeakClosure81

end
