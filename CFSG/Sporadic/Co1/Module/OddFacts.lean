
module

public import CFSG.Sporadic.Co1.Module.OddFactsBase1

public import CFSG.Sporadic.Co1.Module.OddBuild

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint
open CFSG.Monster.GMS (IsCo1TwoA Co1CommonFour Co1OddType Co1OddPairFacts Co1InvolutionFacts co1Fix
  co1Orbit)

attribute [local instance] vecAct vecSMul

theorem co1Orbit_two :
    co1Orbit 2 = MulAction.orbit NativeSporadic.Co1 omega0 := by
  rw [orbit_omega0, ← range_co1Act v₄]
  rfl

theorem commonFour_conj
    (x r s : NativeSporadic.Co1) :
    Co1CommonFour (x * r * x⁻¹) (x * s * x⁻¹) ↔ Co1CommonFour r s := by
  unfold Co1CommonFour
  rw [co1Orbit_two]
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨x⁻¹ • v, (smul_mem_orbit_iff' x⁻¹ omega0 v).2 hv, ?_, ?_⟩
    · exact (mem_fix_conj_iff x r v).1 h1
    · exact (mem_fix_conj_iff x s v).1 h2
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨x • v, (smul_mem_orbit_iff' x omega0 v).2 hv, ?_, ?_⟩
    · show (x * r * x⁻¹) • x • v = x • v
      rw [mem_fix_conj_iff, inv_smul_smul]
      exact h1
    · show (x * s * x⁻¹) • x • v = x • v
      rw [mem_fix_conj_iff, inv_smul_smul]
      exact h2

theorem oddType_sRep
    (hN2 : ∀ k : Fin 3, Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer {sRep k}) = ![155520, 181440, 7200] k) (k : Fin 3) :
    Co1OddType rho3 (sRep k) k := by
  have h1 := pair_fix_ncard k
  have h2 := hN2 k
  have h3 := order_rho3_sRep
  fin_cases k
  · simp only [Co1OddType, co1Fix_eq]
    exact ⟨h3.1, by simpa using h1, by simpa using h2⟩
  · simp only [Co1OddType, co1Fix_eq]
    exact ⟨h3.2.1, by simpa using h1, by simpa using h2⟩
  · simp only [Co1OddType, co1Fix_eq]
    exact ⟨h3.2.2, by simpa using h1, by simpa using h2⟩

theorem rho3_facts
    (hC : Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) = 89181388800) :
    (∀ s : NativeSporadic.Co1, IsConj rho3 s → s ≠ rho3 → Odd (orderOf (rho3 * s)) →
      (∃ v ∈ MulAction.orbit NativeSporadic.Co1 omega0, rho3 • v = v ∧ s • v = v) →
      ∃ (k : Fin 3) (z : NativeSporadic.Co1),
        z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ∧ s = z * sRep k * z⁻¹) ∧
    (∀ k : Fin 3, Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer {sRep k}) = ![155520, 181440, 7200] k) ∧
    (∀ k : Fin 3, k ≠ 0 → ∀ z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1),
      ∀ g ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1),
      g ∈ Subgroup.centralizer ({z * sRep k * z⁻¹} : Set NativeSporadic.Co1) →
      (∀ v : Vec24, rho3 • v = v → (z * sRep k * z⁻¹) • v = v → g • v = v) → g = 1) := by
  have := finite_co1
  obtain ⟨C, hω, hρ, hs, hZn, ho, hd⟩ := exists_cert hC
  refine ⟨?_, ?_, ?_⟩
  · intro s hconj hne hodd ⟨v, hv, h1, h2⟩
    obtain ⟨k, z, hz, hsz⟩ := C.nf_vector (s := s) (by rw [hρ]; exact hconj)
      (by rw [hρ]; exact hne) (by rw [hρ]; exact hodd) (v := v) (by rw [hω]; exact hv)
      (by rw [hρ]; exact h1) h2
    refine ⟨k, z, by rw [hρ] at hz; exact hz, by rw [hsz, hs]⟩
  · intro k
    have hq : {ω ∈ MulAction.orbit NativeSporadic.Co1 C.ω₀ | C.ρ • ω = ω ∧ C.s k • ω = ω}.ncard =
        ![405, 135, 75] k := by
      rw [hω, hρ, hs k]
      exact pair_fix4_ncard k
    have h := C.card_centralizer_inf k hq
    rw [hρ, hs k, hZn] at h
    rw [h]
    fin_cases k <;> norm_num
  · intro k hk z hz g hg hgs hfix
    exact C.faithful_conj k (C.faith k hk) (z := z) (by rw [hρ]; exact hz) (g := g)
      (by rw [hρ]; exact hg) (by rw [hs k]; exact hgs) (by rw [hρ, hs k]; exact hfix)

theorem oddPf_rho3
    (hC : Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) = 89181388800) :
    OddPf rho3 := by
  obtain ⟨hN1, hN2, hN3⟩ := rho3_facts hC
  have htype := oddType_sRep hN2
  have hodd_of_type : ∀ {s : NativeSporadic.Co1} {k : Fin 3}, Co1OddType rho3 s k →
      Odd (orderOf (rho3 * s)) := by
    intro s k h
    fin_cases k <;> simp only [Co1OddType] at h <;> rw [h.1] <;> decide
  have hne_of_type : ∀ {s : NativeSporadic.Co1} {k : Fin 3}, Co1OddType rho3 s k → s ≠ rho3 := by
    intro s k h heq
    subst heq
    fin_cases k <;> simp only [Co1OddType] at h <;>
      (have h1 := h.1; rw [rho3_sq, orderOf_one] at h1; omega)
  have hcf_vec : ∀ {s : NativeSporadic.Co1}, Co1CommonFour rho3 s →
      ∃ v ∈ MulAction.orbit NativeSporadic.Co1 omega0, rho3 • v = v ∧ s • v = v := by
    rintro s ⟨v, hv, h1, h2⟩
    rw [co1Fix_eq] at h1 h2
    exact ⟨v, by rw [← co1Orbit_two]; exact hv, h1, h2⟩
  have hnf : ∀ {s : NativeSporadic.Co1} {k : Fin 3}, IsConj rho3 s → Co1CommonFour rho3 s →
      Co1OddType rho3 s k → ∃ z : NativeSporadic.Co1,
        z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ∧ s = z * sRep k * z⁻¹ := by
    intro s k hc hf ht
    obtain ⟨k₁, z, hz, hs⟩ := hN1 s hc (hne_of_type ht) (hodd_of_type ht) (hcf_vec hf)
    have hk₁ : Co1OddType rho3 s k₁ := by
      rw [hs]
      exact (oddType_cent hz k₁).2 (htype k₁)
    have e : k₁ = k := oddType_unique hk₁ ht
    subst e
    exact ⟨z, hz, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hconj hne hodd hcf
    obtain ⟨k, z, hz, hs⟩ := hN1 s hconj hne hodd (hcf_vec hcf)
    have hk : Co1OddType rho3 s k := by
      rw [hs]
      exact (oddType_cent hz k).2 (htype k)
    exact ⟨k, hk, fun j hj => oddType_unique hj hk⟩
  · intro k
    refine ⟨sRep k, sRep_conj k, hne_of_type (htype k), ?_, htype k⟩
    refine ⟨omega0, by rw [co1Orbit_two]; exact MulAction.mem_orbit_self omega0, ?_, ?_⟩
    · rw [co1Fix_eq]
      exact MulAction.mem_stabilizer_iff.1 rho3_mem
    · rw [co1Fix_eq]
      exact MulAction.mem_stabilizer_iff.1 (sRep_mem k)
  · intro k s s' hc hc' hf hf' ht ht'
    obtain ⟨z₁, hz₁, hs₁⟩ := hnf hc hf ht
    obtain ⟨z₂, hz₂, hs₂⟩ := hnf hc' hf' ht'
    refine ⟨z₂ * z₁⁻¹, Subgroup.mul_mem _ hz₂ (Subgroup.inv_mem _ hz₁), ?_⟩
    rw [hs₁, hs₂]
    group
  · intro k s hk hc hf ht
    obtain ⟨z, hz, hs⟩ := hnf hc hf ht
    refine ⟨nondeg_conj hk hz hs, fun g hg hfix => ?_⟩
    have hg1 := (Subgroup.mem_inf.1 hg).1
    have hg2 := (Subgroup.mem_inf.1 hg).2
    refine hN3 k hk z hz g hg1 (by rw [← hs]; exact hg2) (fun v h1 h2 => ?_)
    exact hfix v ⟨h1, by rw [hs]; exact h2⟩

theorem oddPf_of_conj
    (x r : NativeSporadic.Co1) (h : OddPf (x * r * x⁻¹)) : OddPf r := by
  obtain ⟨hA, hB, hC', hD⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hconj hne hodd hcf
    obtain ⟨k, hk, hu⟩ := hA (x * s * x⁻¹) ((isConj_conj_iff x r s).2 hconj)
      ((conj_ne_iff x r s).2 hne) (by rw [orderOf_conj_pair]; exact hodd)
      ((commonFour_conj x r s).2 hcf)
    exact ⟨k, (oddType_conj x r s k).1 hk, fun j hj => hu j ((oddType_conj x r s j).2 hj)⟩
  · intro k
    obtain ⟨s', hconj, hne, hcf, ht⟩ := hB k
    obtain ⟨s, rfl⟩ : ∃ s, x * s * x⁻¹ = s' := ⟨x⁻¹ * s' * x, by group⟩
    exact ⟨s, (isConj_conj_iff x r s).1 hconj, (conj_ne_iff x r s).1 hne,
      (commonFour_conj x r s).1 hcf, (oddType_conj x r s k).1 ht⟩
  · intro k s s' hc hc' hf hf' ht ht'
    obtain ⟨g, hg, hgs⟩ := hC' k (x * s * x⁻¹) (x * s' * x⁻¹) ((isConj_conj_iff x r s).2 hc)
      ((isConj_conj_iff x r s').2 hc') ((commonFour_conj x r s).2 hf)
      ((commonFour_conj x r s').2 hf') ((oddType_conj x r s k).2 ht)
      ((oddType_conj x r s' k).2 ht')
    refine ⟨x⁻¹ * g * x, (mem_centralizer_conj_iff x r g).1 hg, ?_⟩
    calc x⁻¹ * g * x * s * (x⁻¹ * g * x)⁻¹ = x⁻¹ * (g * (x * s * x⁻¹) * g⁻¹) * x := by group
      _ = x⁻¹ * (x * s' * x⁻¹) * x := by rw [hgs]
      _ = s' := by group
  · intro k s hk hc hf ht
    obtain ⟨hnd, hfaith⟩ := hD k (x * s * x⁻¹) hk ((isConj_conj_iff x r s).2 hc)
      ((commonFour_conj x r s).2 hf) ((oddType_conj x r s k).2 ht)
    refine ⟨fun u hu hperp => ?_, fun g hg hfix => ?_⟩
    · have h0 : x • u = 0 := by
        refine hnd (x • u) ((mem_W_conj_iff x r s u).2 hu) (fun v hv => ?_)
        have h1 := hperp (x⁻¹ • v) ((mem_W_conj_iff' x r s v).1 hv)
        have h2 := bil₀_co1Act' x u (x⁻¹ • v)
        have h3 : co1Act x (x⁻¹ • v) = v := smul_inv_smul x v
        rw [h3] at h2
        show bil₀ (co1Act x u) v = 0
        rw [h2]
        exact h1
      have hx0 : x⁻¹ • (0 : Vec24) = 0 := by
        rw [smul_eq_co1Act, co1Act_eq_mulVec, Matrix.mulVec_zero]
      calc u = x⁻¹ • x • u := (inv_smul_smul x u).symm
        _ = 0 := by rw [h0, hx0]
    · have hg1 := (Subgroup.mem_inf.1 hg).1
      have hg2 := (Subgroup.mem_inf.1 hg).2
      have hgx : x * g * x⁻¹ ∈ Subgroup.centralizer ({x * r * x⁻¹} : Set NativeSporadic.Co1) ⊓
          Subgroup.centralizer {x * s * x⁻¹} := by
        refine Subgroup.mem_inf.2 ⟨(mem_centralizer_conj_iff x r _).2 ?_,
          (mem_centralizer_conj_iff x s _).2 ?_⟩
        · rw [show x⁻¹ * (x * g * x⁻¹) * x = g by group]
          exact hg1
        · rw [show x⁻¹ * (x * g * x⁻¹) * x = g by group]
          exact hg2
      have e : x * g * x⁻¹ = 1 := by
        refine hfaith (x * g * x⁻¹) hgx (fun v hv => ?_)
        have hv' := (mem_W_conj_iff' x r s v).1 hv
        have h1 : g • x⁻¹ • v = x⁻¹ • v := (gmsAct_iff g _).1 (hfix _ hv')
        show (x * g * x⁻¹) • v = v
        rw [mul_smul, mul_smul, h1, smul_inv_smul]
      calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
        _ = 1 := by rw [e]; group

theorem co1OddPairFacts_of
    (hI : Co1InvolutionFacts) (hρ : IsCo1TwoA rho3) : Co1OddPairFacts := by
  rw [co1OddPairFacts_iff]
  intro r hr
  have hconj : IsConj r rho3 := hI.2.2 r rho3 hr.1 hρ.1 hr.2 hρ.2
  obtain ⟨x, hx⟩ := isConj_iff.1 hconj
  have hC : Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) =
      89181388800 := by
    have h := hρ.2
    rw [rho3_ncard_fix] at h
    norm_num at h
    omega
  apply oddPf_of_conj x r
  rw [hx]
  exact oddPf_rho3 hC

end CFSG.Sporadic.Co1.Module.Odd
