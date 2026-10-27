module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Frame
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Cent
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Comp
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem dvd_card_component {L : Subgroup G} (hL : CFSG.IsComponent L) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) :
    p ∣ Nat.card L := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hdvd
  have hcop : Nat.Coprime p (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd h.prime).2 hdvd
  have hLX : L ≤ relPPrimeCore p (⊤ : Subgroup G) := by
    have h1 : CFSG.pPrimeCore p L = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hcop⟩)
    have h2 := map_pPrimeCore_le_of_isSubnormal_of_prime (s := p) hL.2
    rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    refine h2.trans ?_
    exact le_sSup (s := {N : Subgroup G | N ≤ ⊤ ∧ (N.subgroupOf ⊤).Normal ∧
      Nat.Coprime p (Nat.card N)}) ⟨le_top, Subgroup.normal_subgroupOf, CFSG.pPrimeCore_coprime_card⟩
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact h.comm_pPrimeCore hq (hLX hx)

theorem exists_noncentral_sylow_inf {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (P : Sylow p G) :
    ∃ x ∈ (P : Subgroup G) ⊓ L, ∃ y ∈ L, x * y ≠ y * x := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL.2
  have hRc : (R : Subgroup L) ≤ Subgroup.center L := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro g
    have hr' : (r : G) ∈ (P : Subgroup G) ⊓ L := by
      rw [← hR]
      exact ⟨r, hr, rfl⟩
    exact Subtype.ext (hcon r hr' g g.2).symm
  have hbot := eq_bot_of_sylow_le_center_of_isPerfect hL.1.1 R hRc
  have hdvd := R.dvd_card_of_dvd_card (h.dvd_card_component hL hne)
  rw [hbot, Subgroup.card_bot] at hdvd
  exact h.prime.one_lt.ne' (Nat.dvd_one.1 hdvd)

theorem pCoreOf_le_normalizer {L : Subgroup G} (hL : CFSG.IsComponent L) {P : Sylow p G}
    (hPM : (P : Subgroup G) ≤ M)
    (hS : ∃ x ∈ (P : Subgroup G) ⊓ L, ∃ y ∈ L, x * y ≠ y * x) :
    pCoreOf 2 M ≤ normalizer (L : Set G) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro q hq
  by_contra hqN
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := hS
  refine hxy0 ?_
  set L' : Subgroup G := L.map (MulAut.conj q).toMonoidHom with hL'
  have hcL' : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj q) hL
  have hne' : L ≠ L' := fun heq => hqN (mem_normalizer_of_map_conj_eq heq.symm)
  have hcomm : ⁅L, L'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hL hcL').resolve_left hne'
  have hLc : L ≤ centralizer (L' : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hQM : pCoreOf 2 M ≤ M := CFSG.openPCoreOf_le 2 M
  have hQn : ((pCoreOf 2 M).subgroupOf M).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf 2 M]
    exact CFSG.pCore_normal
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hcentral : ∀ x ∈ (P : Subgroup G) ⊓ L, ∀ y ∈ L, x * y = y * x := by
    intro x hx y hy
    have hxP : x ∈ (P : Subgroup G) := (Subgroup.mem_inf.1 hx).1
    have hxL : x ∈ L := (Subgroup.mem_inf.1 hx).2
    have hxM : x ∈ M := hPM hxP
    have hu : x⁻¹ * (q * x * q⁻¹) ∈ pCoreOf 2 M := by
      have h1 : x⁻¹ * q * x⁻¹⁻¹ ∈ pCoreOf 2 M := hQn.conj_mem ⟨q, hQM hq⟩ hq ⟨x⁻¹, M.inv_mem hxM⟩
      have h2 := (pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hq)
      simpa [mul_assoc] using h2
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hu⟩
    have hk' : (x⁻¹ * (q * x * q⁻¹)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hw : q * x * q⁻¹ ∈ L' := ⟨x, hxL, by simp [MulAut.conj_apply]⟩
    have hcx : Commute x⁻¹ (q * x * q⁻¹) := by
      have := Subgroup.mem_centralizer_iff.1 (hLc (L.inv_mem hxL)) _ hw
      exact this.symm
    rw [hcx.mul_pow, inv_pow] at hk'
    have hpow : x ^ (2 ^ k) = (q * x * q⁻¹) ^ (2 ^ k) := inv_mul_eq_one.1 hk'
    have hyc : y * x ^ (2 ^ k) = x ^ (2 ^ k) * y := by
      rw [hpow]
      exact (Subgroup.mem_centralizer_iff.1 (hLc hy) _ (L'.pow_mem hw _)).symm
    obtain ⟨b, hb⟩ := P.isPGroup' ⟨x, hxP⟩
    have hb' : x ^ (p ^ b) = 1 := congrArg Subtype.val hb
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hb')
        (Nat.Coprime.pow k b ((Nat.coprime_primes Nat.prime_two h.prime).2 (Ne.symm h.odd)))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hcm : Commute (x ^ (2 ^ k)) y := hyc.symm
    calc x * y = (x ^ (2 ^ k)) ^ m * y := by rw [hm]
      _ = y * (x ^ (2 ^ k)) ^ m := (hcm.pow_left m).eq
      _ = y * x := by rw [hm]
  exact hcentral x0 hx0 y0 hy0

theorem le_normalizer_of_component {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {P : Sylow p G} (hPM : (P : Subgroup G) ≤ M)
    (hS : ∃ x ∈ (P : Subgroup G) ⊓ L, ∃ y ∈ L, x * y ≠ y * x) :
    E ≤ normalizer (L : Set G) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro e he
  by_contra heN
  have he1 : e ≠ 1 := by
    rintro rfl
    exact heN (Subgroup.one_mem _)
  have hep : e ^ p = 1 := h.elem.2 e he
  have hord : orderOf e = p := orderOf_eq_prime hep he1
  have hcomm : ∀ i : ℕ, 0 < i → i < p → ∀ x ∈ L, ∀ y ∈ L,
      e ^ i * x * (e ^ i)⁻¹ * y = y * (e ^ i * x * (e ^ i)⁻¹) := by
    intro i hi0 hip x hx y hy
    set Li : Subgroup G := L.map (MulAut.conj (e ^ i)).toMonoidHom with hLi
    have hcLi : CFSG.IsComponent Li :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (e ^ i)) hL
    have hne' : L ≠ Li := by
      intro heq
      have hi : e ^ i ∈ normalizer (L : Set G) := mem_normalizer_of_map_conj_eq heq.symm
      have hcop : Nat.Coprime i (orderOf e) := by
        rw [hord]
        exact ((Nat.Prime.coprime_iff_not_dvd h.prime).2 (Nat.not_dvd_of_pos_of_lt hi0 hip)).symm
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      apply heN
      rw [← hm]
      exact (normalizer (L : Set G)).pow_mem hi m
    have hLc : L ≤ centralizer (Li : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1
      ((CFSG.LocalCores.distinct_components_commute hL hcLi).resolve_left hne')
    have hw : e ^ i * x * (e ^ i)⁻¹ ∈ Li := ⟨x, hx, MulAut.conj_apply (e ^ i) x⟩
    exact Subgroup.mem_centralizer_iff.1 (hLc hy) _ hw
  have hzy : ∀ z ∈ L, ∀ y ∈ (P : Subgroup G) ⊓ L, z * y * z⁻¹ ∈ M := by
    intro z hz y hy
    obtain ⟨d, hde, hd⟩ := exists_mem_centralizer_conj_eq h.prime.pos hep hcomm hz
    have hdM : d ∈ M :=
      h.centralizer_le_of_ne_one he he1 (Subgroup.mem_centralizer_singleton_iff.2 hde)
    rw [← hd y (Subgroup.mem_inf.1 hy).2]
    exact M.mul_mem (M.mul_mem hdM (hPM (Subgroup.mem_inf.1 hy).1)) (M.inv_mem hdM)
  have hcommM : ⁅L, (P : Subgroup G) ⊓ L⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro z hz y hy
    rw [commutatorElement_def]
    exact M.mul_mem (hzy z hz y hy) (M.inv_mem (hPM (Subgroup.mem_inf.1 hy).1))
  have hS' : ¬ ∀ x ∈ (P : Subgroup G) ⊓ L, ∀ y ∈ L, x * y = y * x := by
    intro hall
    obtain ⟨x, hx, y, hy, hxy⟩ := hS
    exact hxy (hall x hx y hy)
  have hLM : L ≤ M := by
    have := commutator_eq_self_of_not_central hL.1 (inf_le_right : (P : Subgroup G) ⊓ L ≤ L) hS'
    rw [← this]
    exact hcommM
  exact h.false_of_component_le hL hne hLM

theorem normalizes_component {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) :
    E ≤ normalizer (L : Set G) ∧ pCoreOf 2 M ≤ normalizer (L : Set G) := by
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  have hPM : (P : Subgroup G) ≤ M := h.le_of_isPGroup P.isPGroup' hEP
  have hS := h.exists_noncentral_sylow_inf hL hne P
  exact ⟨h.le_normalizer_of_component hL hne hPM hS, h.pCoreOf_le_normalizer hL hPM hS⟩

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
