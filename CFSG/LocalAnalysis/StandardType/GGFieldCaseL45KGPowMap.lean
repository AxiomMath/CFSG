module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.kg_inS_of_mem
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {h : G} (hU : h ∈ U) (hK : h ∈ K) :
    GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) ⟨h, hK⟩ := by
  refine ⟨(ggL45IsPElt_coe (p := p) (⟨h, hK⟩ : K)).mpr ?_, fun e he => ?_⟩
  · obtain ⟨k, hk⟩ := hcfg.isPGroup ⟨h, hU⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · obtain ⟨c, hc, hcN, rfl⟩ := mem_ggL45KgE.mp he
    exact (ggL45_rhoK_fix_iff hcN _).mpr
      (Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hU) c hc)

theorem GGL45Config.kg_rho_props
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) {g : G} (hg : g ∈ U) :
    GGL45IsPElt p (K.normalizerMonoidHom ⟨g, hcfg.le_normalizer hg⟩) ∧
      (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, K.normalizerMonoidHom ⟨g, hcfg.le_normalizer hg⟩ * e =
        e * K.normalizerMonoidHom ⟨g, hcfg.le_normalizer hg⟩) ∧
      (GGL45InducesIn θ I (K.normalizerMonoidHom ⟨g, hcfg.le_normalizer hg⟩) ↔ g ∈ U₁) := by
  refine ⟨?_, fun e he => ?_, (ggL45_inducesIn_rhoK_iff K θ I _).trans (hiff g hg _).symm⟩
  · obtain ⟨k, hk⟩ := hcfg.isPGroup ⟨g, hg⟩
    refine ⟨k, ?_⟩
    have : (⟨g, hcfg.le_normalizer hg⟩ : Subgroup.normalizer (K : Set G)) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, this, map_one]
  · obtain ⟨c, hc, hcN, rfl⟩ := mem_ggL45KgE.mp he
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hg) c hc).symm

theorem GGL45Config.kg_powmap
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) {s : ℕ}
    (hP4 : ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e = e * γ) →
      ¬ GGL45InducesIn θ I γ → GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
        γ h = h ^ (1 + p ^ (s - 1) * k'))
    {w : G} (hw : w ∈ U) (hwU₁ : w ∉ U₁) (hwp : w ^ p ∈ U₁) :
    ∃ k : ℕ, ¬ p ∣ k ∧ ∀ h ∈ U ⊓ K, w⁻¹ * h * w = h ^ (1 + p ^ (s - 1) * k) := by
  have hwi : w⁻¹ ∈ U := U.inv_mem hw
  obtain ⟨hpe, hcomm, hind⟩ := hcfg.kg_rho_props θ hiff hwi
  have hwpi : (w ^ p)⁻¹ ∈ U := U.inv_mem (U.pow_mem hw p)
  obtain ⟨-, -, hindp⟩ := hcfg.kg_rho_props θ hiff hwpi
  have hpow : K.normalizerMonoidHom ⟨w⁻¹, hcfg.le_normalizer hwi⟩ ^ p =
      K.normalizerMonoidHom ⟨(w ^ p)⁻¹, hcfg.le_normalizer hwpi⟩ := by
    rw [← map_pow]
    congr 1
    exact Subtype.ext (by simp [inv_pow])
  obtain ⟨k', hk', hact⟩ := hP4 _ hpe hcomm
    (fun h => hwU₁ (by simpa using hind.mp h))
    (by rw [hpow]; exact hindp.mpr (U₁.inv_mem hwp))
  refine ⟨k', hk', fun h hh => ?_⟩
  have := congrArg Subtype.val (hact ⟨h, hh.2⟩ (hcfg.kg_inS_of_mem hh.1 hh.2))
  rw [ggL45_rhoK_coe] at this
  simpa using this

theorem GGL45Config.kg_mem_part_of_cent
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) {s : ℕ}
    (hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t))
    (hP2e : ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → h ^ p ^ s = 1)
    (hP2n : ∃ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h ∧ h ^ p ^ (s - 1) ∉ Subgroup.center K)
    (hP4 : ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e = e * γ) →
      ¬ GGL45InducesIn θ I γ → GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
        γ h = h ^ (1 + p ^ (s - 1) * k'))
    {w : G} (hw : w ∈ U) (hc : ∀ h ∈ U ⊓ K, w * h = h * w) : w ∈ U₁ := by
  have hp : p.Prime := hcfg.prime
  by_contra hwU₁
  obtain ⟨N, hN⟩ := hcfg.isPGroup ⟨w, hw⟩
  have hex : ∃ j, w ^ p ^ j ∈ U₁ :=
    ⟨N, by rw [show w ^ p ^ N = 1 by simpa using congrArg Subtype.val hN]; exact U₁.one_mem⟩
  classical
  set j := Nat.find hex with hj
  have hj0 : j ≠ 0 := fun h0 => by
    have := Nat.find_spec hex
    rw [← hj, h0, pow_zero, pow_one] at this
    exact hwU₁ this
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hi1 : w ^ p ^ i ∉ U₁ := Nat.find_min hex (by omega)
  have hi2 : (w ^ p ^ i) ^ p ∈ U₁ := by
    have := Nat.find_spec hex
    rw [← hj, hi, pow_succ, pow_mul] at this
    exact this
  obtain ⟨k, hk, hact⟩ := hcfg.kg_powmap θ hiff hP4 (U.pow_mem hw _) hi1 hi2
  obtain ⟨h, hhS, hhZ⟩ := hP2n
  have hhU : (h : G) ∈ U ⊓ K := ⟨hcfg.part_le (hcfg.kg_S_mem θ hinn hiff hmul hhS), h.2⟩
  have hcomm : (w ^ p ^ i) * h = h * w ^ p ^ i :=
    ((Commute.pow_left (show Commute w (h : G) from hc h hhU) _)).eq
  have h1 := hact h hhU
  have h0 : (w ^ p ^ i)⁻¹ * h * w ^ p ^ i = h := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h0, pow_add, pow_one] at h1
  have h2 : (h : G) ^ (p ^ (s - 1) * k) = 1 :=
    mul_left_cancel ((h1.symm).trans (mul_one (h : G)).symm)
  apply hhZ
  have hoK : orderOf h ∣ p ^ s := orderOf_dvd_of_pow_eq_one (hP2e h hhS)
  have hoK2 : orderOf h ∣ p ^ (s - 1) * k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using h2)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hoK
  have hcop : Nat.Coprime (orderOf h) k := by
    rw [hm]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)
  have : orderOf h ∣ p ^ (s - 1) := hcop.dvd_of_dvd_mul_right hoK2
  rw [orderOf_dvd_iff_pow_eq_one.mp this]
  exact Subgroup.one_mem _

end Config

end CFSG.StandardType
