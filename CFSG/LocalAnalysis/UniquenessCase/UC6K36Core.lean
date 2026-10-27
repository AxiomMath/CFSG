module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Basic
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaxTwoLocal_ge_of_isTwoLocal {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, IsMaxTwoLocalSubgroup N ∧ H ≤ N := by
  obtain ⟨N, hHN, hN⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hH
  exact ⟨N, ⟨hN.1, fun K hK hNK => le_antisymm (hN.2 hK hNK) hNK⟩, hHN⟩

theorem mem_pCoreOf_top_of_mem_pCore {r : ℕ} {x : G} (hx : x ∈ CFSG.pCore r G) :
    x ∈ pCoreOf r (⊤ : Subgroup G) := by
  have h1 : (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup G)) ∈ CFSG.pCore r (⊤ : Subgroup G) := by
    rw [← CFSG.pCore_map_iso r (Subgroup.topEquiv (G := G)).symm]
    exact ⟨x, hx, rfl⟩
  exact (CFSG.mem_openPCoreOf_iff _).2 h1

theorem comm_pCoreOf_two_of_normal_odd {M K : Subgroup G} [K.Normal] (hKM : K ≤ M)
    (hK : ¬ 2 ∣ Nat.card K) {q x : G} (hq : q ∈ pCoreOf 2 M) (hx : x ∈ K) : q * x = x * q := by
  have hxM : x ∈ M := hKM hx
  have hQn : ((pCoreOf 2 M).subgroupOf M).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf 2 M]
    exact CFSG.pCore_normal
  have hQM : pCoreOf 2 M ≤ M := CFSG.openPCoreOf_le 2 M
  have h1 : x * q * x⁻¹ ∈ pCoreOf 2 M := hQn.conj_mem ⟨q, hQM hq⟩ hq ⟨x, hxM⟩
  have h2 : q * x * q⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem x hx q
  have hc : (x * q * x⁻¹) * q⁻¹ ∈ pCoreOf 2 M ⊓ K := by
    refine Subgroup.mem_inf.2 ⟨(pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hq), ?_⟩
    have h3 : x * (q * x⁻¹ * q⁻¹) ∈ K :=
      K.mul_mem hx (by
        have := K.inv_mem h2
        simpa [mul_assoc] using this)
    simpa [mul_assoc] using h3
  have hcoprime : (pCoreOf 2 M ⊓ K) = ⊥ := by
    have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
      rw [pCoreOf]
      exact CFSG.pCore_isPGroup.map _
    obtain ⟨a, ha⟩ := hQ2.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [ha]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hK)
  rw [hcoprime, Subgroup.mem_bot] at hc
  have h4 : x * q * x⁻¹ = q := by
    calc x * q * x⁻¹ = (x * q * x⁻¹ * q⁻¹) * q := by group
      _ = q := by rw [hc, one_mul]
  calc q * x = (x * q * x⁻¹) * x := by rw [h4]
    _ = x * q := by group

end General

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem pPrimeCore_le : relPPrimeCore p (⊤ : Subgroup G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.LocalAnalysis.AGL81TheoremC.relPPrimeCore_le_of_glbCore_le (k := 1) h.elem
    (by rw [h.card]) le_top h.gamma

theorem normal_pPrimeCore : (relPPrimeCore p (⊤ : Subgroup G)).Normal := by
  have hn := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
    h.prime (⊤ : Subgroup G)
  exact Subgroup.normalizer_eq_top_iff.1
    (eq_top_iff.2 ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hn))

theorem not_dvd_card_pPrimeCore : ¬ p ∣ Nat.card (relPPrimeCore p (⊤ : Subgroup G)) :=
  (Nat.Prime.coprime_iff_not_dvd h.prime).1
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      h.prime (⊤ : Subgroup G))

theorem exists_invariant_sylow_two :
    ∃ S : Subgroup G, fusionIsSylowIn 2 S (relPPrimeCore p (⊤ : Subgroup G)) ∧
      E ≤ normalizer (S : Set G) := by
  haveI := h.normal_pPrimeCore
  have hEX : E ≤ normalizer ((relPPrimeCore p (⊤ : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2
      (inferInstance : (relPPrimeCore p (⊤ : Subgroup G)).Normal)]
    exact le_top
  have hE1 : E ≤ normalizer (((⊥ : Subgroup G)) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  obtain ⟨S, hS, -, hES⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing h.prime
    Nat.prime_two (A := E) (M := relPPrimeCore p (⊤ : Subgroup G)) (Q := ⊥) h.isPGroup
    h.not_dvd_card_pPrimeCore hEX bot_le IsPGroup.of_bot hE1
  exact ⟨S, hS, hES⟩

theorem not_dvd_two_card_pPrimeCore : ¬ 2 ∣ Nat.card (relPPrimeCore p (⊤ : Subgroup G)) := by
  intro h2
  haveI := h.normal_pPrimeCore
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hES⟩ := h.exists_invariant_sylow_two
  obtain ⟨T, hT⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  have hfr : normalizer (S : Set G) ⊔ relPPrimeCore p (⊤ : Subgroup G) = ⊤ := by
    have := Sylow.normalizer_sup_eq_top T
    rwa [hT] at this
  have hne : S ≠ ⊥ := by
    intro hS1
    have hTd : 2 ∣ Nat.card (T : Subgroup (relPPrimeCore p (⊤ : Subgroup G))) :=
      T.dvd_card_of_dvd_card h2
    have hcard : Nat.card S = Nat.card (T : Subgroup (relPPrimeCore p (⊤ : Subgroup G))) := by
      rw [← hT]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [hS1, Subgroup.card_bot] at hcard
    rw [← hcard] at hTd
    exact absurd (Nat.le_of_dvd one_pos hTd) (by norm_num)
  have hloc : IsTwoLocal (normalizer (S : Set G)) := ⟨S, hne, hS.2.1, rfl⟩
  obtain ⟨N, hN, hSN⟩ := exists_isMaxTwoLocal_ge_of_isTwoLocal hloc
  have hNE : N ∈ calMOf E := ⟨hN, hES.trans hSN⟩
  rw [h.uniq] at hNE
  have hNM : N = M := hNE
  apply h.ne_top
  rw [eq_top_iff, ← hfr]
  exact sup_le (hNM ▸ hSN) h.pPrimeCore_le

theorem comm_pPrimeCore {q x : G} (hq : q ∈ pCoreOf 2 M)
    (hx : x ∈ relPPrimeCore p (⊤ : Subgroup G)) : q * x = x * q := by
  haveI := h.normal_pPrimeCore
  exact comm_pCoreOf_two_of_normal_odd h.pPrimeCore_le h.not_dvd_two_card_pPrimeCore hq hx

theorem comm_fittingSubgroup {q x : G} (hq : q ∈ pCoreOf 2 M) (hx : x ∈ CFSG.fittingSubgroup G) :
    q * x = x * q := by
  have hle : CFSG.fittingSubgroup G ≤ centralizer ({q} : Set G) := by
    rw [CFSG.fitting_eq_sup_pCore G]
    refine iSup_le fun r => ?_
    have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hrp : r.1.1 = p
    · have hy' : y ∈ CFSG.pCore p G := hrp ▸ hy
      exact (h.comm_pCoreOf_top hq (mem_pCoreOf_top_of_mem_pCore hy')).symm
    · haveI : Fact r.1.1.Prime := ⟨hr⟩
      have hyX : y ∈ relPPrimeCore p (⊤ : Subgroup G) := by
        refine (le_sSup (s := {N : Subgroup G | N ≤ ⊤ ∧ (N.subgroupOf ⊤).Normal ∧
            Nat.Coprime p (Nat.card N)}) ⟨le_top, ?_, ?_⟩ : CFSG.pCore r.1.1 G ≤ _) hy
        · exact Subgroup.normal_subgroupOf
        · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := r.1.1) (G := G)).exists_card_eq
          rw [hk]
          exact Nat.Coprime.pow_right _ ((Nat.coprime_primes h.prime hr).2 (Ne.symm hrp))
      exact (h.comm_pPrimeCore hq hyX).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
