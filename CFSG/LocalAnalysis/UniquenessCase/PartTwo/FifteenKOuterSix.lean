module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.GH74.KGroups.PSL2
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix
import CFSG.Milestones.ASVolI.F431.BCoreU4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEngLift
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.GH74.Uniqueness.Section15HeringDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.ComponentClassification.OuterAutomorphisms

local instance fact_prime_seven_s15k : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem s15k_six_l3 {S : Type} [Group S] (h : UC22.IsL3 S 1) :
    Nat.card S = 168 ∧ Nat.card (MulAut S) ≤ 2 * Nat.card S := by
  have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by decide) h
  have h27 := CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hsc
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated (F := GaloisField 7 1)
    7 1 (by norm_num) (GaloisField.card 7 1 (by norm_num)) h27
  have hF : Nat.card (GaloisField 7 1) = 7 := by
    simpa using GaloisField.card 7 1 (by norm_num : (1 : ℕ) ≠ 0)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 7 1)) :=
    ⟨7, 1, by norm_num, by norm_num, by norm_num, hF⟩
  have hcard : Nat.card (CFSG.AGLEmbedding.PSL2GF 7 1) = 168 := by
    rw [show CFSG.AGLEmbedding.PSL2GF 7 1 = CFSG.GorensteinWalter.PSL2 (GaloisField 7 1) from rfl,
      CFSG.GorensteinWalter.psl2_card_formula (GaloisField 7 1) hodd, hF]
    norm_num
  have hS : Nat.card S = 168 := (Nat.card_congr e.toEquiv).trans hcard
  refine ⟨hS, ?_⟩
  have hAut : Nat.card (MulAut S) = Nat.card (MulAut (CFSG.AGLEmbedding.PSL2GF 7 1)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [hAut, CFSG.AGLEmbedding.card_mulAut_psl2GF 7 1 (by norm_num : 1 ≤ 1), hS]
  norm_num

theorem s15k_six_alt_card {S : Type} [Group S] {n : ℕ} (h : UC22.IsAlt S n) (hn : 2 ≤ n) :
    Nat.card S = n.factorial / 2 := by
  obtain ⟨e⟩ := h
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem s15k_six_alt {S : Type} [Group S] {n : ℕ} (h : UC22.IsAlt S n) (hn : n = 5 ∨ 7 ≤ n) :
    Nat.card S = n.factorial / 2 ∧ Nat.card (MulAut S) ≤ 2 * Nat.card S := by
  have hS : Nat.card S = n.factorial / 2 := s15k_six_alt_card h (by omega)
  obtain ⟨e⟩ := h
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  refine ⟨hS, ?_⟩
  have hsurj : Function.Surjective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n) → MulAut (alternatingGroup (Fin n))) := by
    intro f
    obtain ⟨σ, hσ⟩ :=
      CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le hn f
    refine ⟨σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply]
    exact (hσ g).symm
  have hAut : Nat.card (MulAut S) = Nat.card (MulAut (alternatingGroup (Fin n))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  calc Nat.card (MulAut S) = Nat.card (MulAut (alternatingGroup (Fin n))) := hAut
    _ ≤ Nat.card (Equiv.Perm (Fin n)) := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 * Nat.card (alternatingGroup (Fin n)) := (two_mul_nat_card_alternatingGroup).symm
    _ = 2 * Nat.card S := by rw [Nat.card_congr e.toEquiv]

theorem s15k_six_l4 {S : Type} [Group S] (h : IsLn S 4 1) :
    Nat.card S = 20160 ∧ Nat.card (MulAut S) ≤ 2 * Nat.card S := by
  have h8 : UC22.IsAlt S 8 :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel h
  obtain ⟨hS, hA⟩ := s15k_six_alt h8 (Or.inr (by norm_num))
  exact ⟨by rw [hS]; norm_num [Nat.factorial], hA⟩

theorem s15k_six_om6 {S : Type} [Group S] (h : IsOmegaMinus S 6 1) :
    Nat.card S = 25920 ∧ Nat.card (MulAut S) ≤ 2 * Nat.card S := by
  obtain ⟨F, _, hU, ⟨e⟩⟩ := s15k_om6_model h
  haveI := hU.finite
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := 2) (ε := 0) hU
  let e' : S ≃* CFSG.ClassicalGroups.UnitaryFlag.hypSU hU 2 0 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.hypTransport hU hR).symm
  have hcard : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypSU hU 2 0) = 25920 := by
    rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_hypSU_four hU]
    norm_num
  have hS : Nat.card S = 25920 := (Nat.card_congr e'.toEquiv).trans hcard
  refine ⟨hS, ?_⟩
  have hF4 : Nat.card F = 2 ^ 2 := by simpa using hU.card_eq_sq
  have hAutF : Nat.card (RingAut F) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hF4).1
  have hsurj : Function.Surjective
      (fun p : CFSG.ClassicalGroups.UnitaryFlag.hypSU hU 2 0 × RingAut F =>
        MulAut.conj p.1 * CFSG.ASVolI.burnsideF4m_U4_fieldAut hU p.2) := by
    intro θ
    obtain ⟨a, σ, hθ⟩ := CFSG.ASVolI.burnsideF4m_U4_normalForm hU θ
    exact ⟨(a, σ), hθ.symm⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, hAutF, hcard] at h1
  have hAut : Nat.card (MulAut S) =
      Nat.card (MulAut (CFSG.ClassicalGroups.UnitaryFlag.hypSU hU 2 0)) :=
    Nat.card_congr (MulAut.congr e').toEquiv
  rw [hAut, hS]
  omega

theorem s15k_six_alt6_outer :
    Nat.card (Outer (alternatingGroup (Fin 6))) = 2 ∨
      Nat.card (Outer (alternatingGroup (Fin 6))) = 4 := by
  have h4 : Nat.card (Outer (alternatingGroup (Fin 6))) ≤ 4 :=
    CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  let τ : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  let θ : MulAut (alternatingGroup (Fin 6)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 6)) τ
  let x : Outer (alternatingGroup (Fin 6)) := QuotientGroup.mk θ
  have hθ2 : θ ^ 2 = 1 := by
    change (MulAut.conjNormal (H := alternatingGroup (Fin 6)) τ) ^ 2 = 1
    rw [← map_pow, pow_two]
    have : τ * τ = 1 := Equiv.swap_mul_self 0 1
    rw [this, map_one]
  have hx2 : x ^ 2 = 1 := by
    change (QuotientGroup.mk' (inner (alternatingGroup (Fin 6))) θ) ^ 2 = 1
    rw [← map_pow, hθ2, map_one]
  have hkey : ∀ c : Equiv.Perm (Fin 6),
      c * List.formPerm [0, 1, 2] = List.formPerm [0, 1, 2] * c →
      c * List.formPerm [0, 1, 3] = List.formPerm [0, 1, 3] * c →
      c * List.formPerm [0, 1, 4] = List.formPerm [0, 1, 4] * c →
      c * List.formPerm [0, 1, 5] = List.formPerm [0, 1, 5] * c → c = 1 := by
    decide +kernel
  have hmem : ∀ l : List (Fin 6),
      (l = [0, 1, 2] ∨ l = [0, 1, 3] ∨ l = [0, 1, 4] ∨ l = [0, 1, 5]) →
      l.formPerm ∈ alternatingGroup (Fin 6) := by
    rintro l (rfl | rfl | rfl | rfl) <;> (rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel)
  have hx1 : x ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp h
    have hc : ∀ g : alternatingGroup (Fin 6),
        (a : Equiv.Perm (Fin 6)) * g * (a : Equiv.Perm (Fin 6))⁻¹ = τ * g * τ⁻¹ := by
      intro g
      have h1 := congrArg
        (fun φ : MulAut (alternatingGroup (Fin 6)) =>
          ((φ g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) ha
      simpa [MulAut.conj_apply, θ, MulAut.conjNormal_apply] using h1
    have key : ∀ g : alternatingGroup (Fin 6),
        ((a : Equiv.Perm (Fin 6))⁻¹ * τ) * g = g * ((a : Equiv.Perm (Fin 6))⁻¹ * τ) := by
      intro g
      have h1 := hc g
      calc ((a : Equiv.Perm (Fin 6))⁻¹ * τ) * g
          = (a : Equiv.Perm (Fin 6))⁻¹ * (τ * g * τ⁻¹) * τ := by group
        _ = (a : Equiv.Perm (Fin 6))⁻¹ * ((a : Equiv.Perm (Fin 6)) * g *
              (a : Equiv.Perm (Fin 6))⁻¹) * τ := by rw [h1]
        _ = g * ((a : Equiv.Perm (Fin 6))⁻¹ * τ) := by group
    have hc1 : (a : Equiv.Perm (Fin 6))⁻¹ * τ = 1 :=
      hkey _ (key ⟨_, hmem _ (Or.inl rfl)⟩) (key ⟨_, hmem _ (Or.inr (Or.inl rfl))⟩)
        (key ⟨_, hmem _ (Or.inr (Or.inr (Or.inl rfl)))⟩)
        (key ⟨_, hmem _ (Or.inr (Or.inr (Or.inr rfl)))⟩)
    have haτ : (a : Equiv.Perm (Fin 6)) = τ := inv_mul_eq_one.mp hc1
    have hs1 : Equiv.Perm.sign (a : Equiv.Perm (Fin 6)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp a.2
    rw [haτ] at hs1
    have hs2 : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap (by decide)
    rw [hs2] at hs1
    exact absurd hs1 (by decide)
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hdvd : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := hord ▸ orderOf_dvd_natCard x
  obtain ⟨m, hm⟩ := hdvd
  omega

theorem s15k_six_index_pow {S H : Type} [Group S] [Group H] [Finite S] [Finite H]
    (f : S →* H) (hf : Function.Injective f) (hn : f.range.Normal)
    (hc : ∀ h : H, (∀ s : S, h * f s = f s * h) → h = 1) (hS : s15ExcList S) :
    ∃ k : ℕ, f.range.index = 2 ^ k := by
  rcases hS with h | h | h | h | h | h
  · exact s15k_out_index_pow_of_aut_le f hf hn hc (s15k_six_l3 h).2
  · exact s15k_out_index_pow_of_aut_le f hf hn hc (s15k_six_l4 h).2
  · exact s15k_out_index_pow_of_aut_le f hf hn hc (s15k_six_alt h (Or.inl rfl)).2
  · have hd := s15k_out_index_dvd_outer f hf hn hc
    obtain ⟨e⟩ := h
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      at hd
    rcases s15k_six_alt6_outer with h2 | h4
    · rw [h2] at hd
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).mp (by simpa using hd)
      exact ⟨m, hm⟩
    · rw [h4] at hd
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp (by simpa using hd)
      exact ⟨m, hm⟩
  · exact s15k_out_index_pow_of_aut_le f hf hn hc (s15k_six_alt h (Or.inr (by norm_num))).2
  · exact s15k_out_index_pow_of_aut_le f hf hn hc (s15k_six_om6 h).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
