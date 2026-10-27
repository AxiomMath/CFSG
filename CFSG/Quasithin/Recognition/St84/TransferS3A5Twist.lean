module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5Cons
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Perm

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private lemma f112sa_exists_t {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hTP : S ⊓ f112saK L1 L2 S ≤ f112P1 L1 L2 S)
    {ρ₁ ρ₂ : ↥(f112P1 L1 L2 S) →* Equiv.Perm (Fin 3)}
    (hc : ∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ L1 → ρ₂ x = 1)
    (hd : ∀ x : ↥(f112P1 L1 L2 S), ρ₁ x = 1 → ρ₂ x = 1 → (x : H) ∈ pCoreOf 2 L1) :
    ∃ t : ↥(S ⊓ f112saK L1 L2 S), ρ₁ ⟨(t : H), hTP t.2⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hTQ : S ⊓ f112saK L1 L2 S ≤ pCoreOf 2 L1 := by
    intro t ht
    have htL1 : t ∈ L1 := by
      have ht' : t ∈ S ⊓ L1 := by rw [hB.S_inf_L1]; exact ht
      exact ht'.2
    exact hd ⟨t, hTP ht⟩ (hcon ⟨t, ht⟩) (hc ⟨t, hTP ht⟩ htL1)
  have hle : Nat.card ↥(S ⊓ f112saK L1 L2 S) ≤ Nat.card ↥(pCoreOf 2 L1) :=
    Subgroup.card_le_of_le hTQ
  rw [f112sa_card_T_eq_QS hF h1 h2, hB.QS_eq] at hle
  have hpos : 0 < Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := Nat.card_pos
  omega

private lemma f112sa_exists_diag {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hS : ¬ S ≤ L2) (hSP : S ≤ f112P1 L1 L2 S)
    (hTP : S ⊓ f112saK L1 L2 S ≤ f112P1 L1 L2 S)
    {ρ₁ ρ₂ : ↥(f112P1 L1 L2 S) →* Equiv.Perm (Fin 3)} {i₁ : Fin 3}
    (ha : ∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ bigB L1 L2 S → ρ₁ x i₁ = i₁)
    (hc : ∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ L1 → ρ₂ x = 1)
    (hd : ∀ x : ↥(f112P1 L1 L2 S), ρ₁ x = 1 → ρ₂ x = 1 → (x : H) ∈ pCoreOf 2 L1) :
    ∃ u : ↥(f112P1 L1 L2 S), (u : H) ∈ S ∧ (u : H) ∉ L2 ∧ ρ₁ u = 1 := by
  obtain ⟨t, htne⟩ := f112sa_exists_t hF h1 h2 hB hTP hc hd
  let tP : ↥(f112P1 L1 L2 S) := ⟨(t : H), hTP t.2⟩
  obtain ⟨s, hsS, hsL2⟩ := Set.not_subset.mp hS
  let sP : ↥(f112P1 L1 L2 S) := ⟨s, hSP hsS⟩
  have htS : (t : H) ∈ S := by
    have ht' : (t : H) ∈ S ⊓ L2 := by rw [hB.T_eq]; exact t.2
    exact ht'.1
  have htL2 : (t : H) ∈ L2 := by
    have ht' : (t : H) ∈ S ⊓ L2 := by rw [hB.T_eq]; exact t.2
    exact ht'.2
  have hfixs : ρ₁ sP i₁ = i₁ := ha sP ((le_sup_right : S ≤ bigB L1 L2 S) hsS)
  have hfixt : ρ₁ tP i₁ = i₁ := ha tP (f112sa_K_le_bigB L1 L2 S t.2.2)
  by_cases hs1 : ρ₁ sP = 1
  · exact ⟨sP, hsS, hsL2, hs1⟩
  · refine ⟨tP⁻¹ * sP, ?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact S.mul_mem (S.inv_mem htS) hsS
    · intro hmem
      apply hsL2
      have hcoe : ((tP⁻¹ * sP : ↥(f112P1 L1 L2 S)) : H) = (t : H)⁻¹ * s := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe] at hmem
      rw [show s = (t : H) * ((t : H)⁻¹ * s) by group]
      exact L2.mul_mem htL2 hmem
    · have hEq : ρ₁ tP = ρ₁ sP :=
        CFSG.GroupTheory.perm3_eq_of_fixed hfixt hfixs htne hs1
      rw [map_mul, map_inv, hEq]
      simp

theorem f112sa_twist {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hS : ¬ S ≤ L2) : S3A5TwistBasis L1 L2 S := by
  obtain ⟨ρ₁, ρ₂, i₁, i₂, ha, hb, hc, hd, _he, _hker, _hf⟩ :=
    f112sa_exists_rhoPair hF h1 h2 hB
  have hQn : f112P1 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set H) := by
    rw [hB.oTwo_left]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112P1 L1 L2 S)
  have hSP : S ≤ f112P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hKP : f112saK L1 L2 S ≤ f112P1 L1 L2 S :=
    (f112sa_K_le_bigB L1 L2 S).trans le_sup_right
  have hTP : S ⊓ f112saK L1 L2 S ≤ f112P1 L1 L2 S := inf_le_left.trans hSP
  have hL1P : L1 ≤ f112P1 L1 L2 S := le_sup_left
  have line_k : ∀ k ∈ f112saK L1 L2 S, k ^ 3 = 1 → f112P1 L1 L2 S ≤
      Subgroup.normalizer ((Subgroup.zpowers k ⊔ pCoreOf 2 L1 : Subgroup H) : Set H) := by
    intro k hk hk3
    let g : ↥(f112P1 L1 L2 S) := ⟨k, hKP hk⟩
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hk3
    have hg1 : ρ₁ g = 1 :=
      CFSG.GroupTheory.perm3_eq_one_of_pow_three (by rw [← map_pow, hg3, map_one])
        (ha g (f112sa_K_le_bigB L1 L2 S hk))
    exact CFSG.GroupTheory.le_normalizer_zpowers_sup_of_perm3 (G := H)
      (P := f112P1 L1 L2 S) (Q := pCoreOf 2 L1) (g := g) ρ₁ ρ₂ hd hQn hg1 hg3
  have line_d : ∀ d ∈ L1, d ^ 3 = 1 → f112P1 L1 L2 S ≤
      Subgroup.normalizer ((Subgroup.zpowers d ⊔ pCoreOf 2 L1 : Subgroup H) : Set H) := by
    intro d hdL1 hd3
    let g : ↥(f112P1 L1 L2 S) := ⟨d, hL1P hdL1⟩
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hd3
    have hg1 : ρ₂ g = 1 := hc g hdL1
    have hker' : ∀ x : ↥(f112P1 L1 L2 S), ρ₂ x = 1 → ρ₁ x = 1 → (x : H) ∈ pCoreOf 2 L1 :=
      fun x hx2 hx1 => hd x hx1 hx2
    exact CFSG.GroupTheory.le_normalizer_zpowers_sup_of_perm3 (G := H)
      (P := f112P1 L1 L2 S) (Q := pCoreOf 2 L1) (g := g) ρ₂ ρ₁ hker' hQn hg1 hg3
  obtain ⟨uP, huS, huL2, hu1⟩ := f112sa_exists_diag hF h1 h2 hB hS hSP hTP ha hc hd
  have hu2 : ρ₂ uP ≠ 1 := by
    intro hρu
    have hmemQ : (uP : H) ∈ pCoreOf 2 L1 := hd uP hu1 hρu
    have hmemQ' : (uP : H) ∈ pCoreOf 2 (f112saP1' L1 L2 S) := hB.QS_eq ▸ hmemQ
    have hmemT : (uP : H) ∈ S ⊓ f112saK L1 L2 S := f112sa_QS_le_T hF hmemQ'
    have hmemL2 : (uP : H) ∈ L2 := by
      have ht' : (uP : H) ∈ S ⊓ L2 := by rw [hB.T_eq]; exact hmemT
      exact ht'.2
    exact huL2 hmemL2
  have hfixu : ρ₂ uP i₂ = i₂ := hb uP ((le_sup_right : S ≤ L1 ⊔ S) huS)
  have husq : ρ₂ uP ^ 2 = 1 := CFSG.GroupTheory.perm3_sq_eq_one hfixu
  refine ⟨line_d, line_k, (uP : H), huS, huL2, ?_, ?_, ?_⟩
  · have h := hd (uP ^ 2) (by rw [map_pow, hu1, one_pow]) (by rw [map_pow, husq])
    simpa using h
  · intro d hdL1
    let dP : ↥(f112P1 L1 L2 S) := ⟨d, hL1P hdL1⟩
    have h := hd ⁅uP, dP⁆ (by rw [map_commutatorElement, hu1, commutatorElement_one_left])
      (by rw [map_commutatorElement, hc dP hdL1, commutatorElement_one_right])
    rw [show ((⁅uP, dP⁆ : ↥(f112P1 L1 L2 S)) : H) = ⁅(uP : H), d⁆ from
      map_commutatorElement (Subgroup.subtype (f112P1 L1 L2 S)) uP dP] at h
    exact h
  · intro k hkK hk3
    let kP : ↥(f112P1 L1 L2 S) := ⟨k, hKP hkK⟩
    have hkP3 : kP ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hk3
    have hk1 : ρ₁ kP = 1 :=
      CFSG.GroupTheory.perm3_eq_one_of_pow_three (by rw [← map_pow, hkP3, map_one])
        (ha kP (f112sa_K_le_bigB L1 L2 S hkK))
    have hk3' : ρ₂ kP ^ 3 = 1 := by rw [← map_pow, hkP3, map_one]
    have h := hd (uP * kP * uP⁻¹ * kP)
      (by rw [map_mul, map_mul, map_mul, map_inv, hu1, hk1]; group)
      (by rw [map_mul, map_mul, map_mul, map_inv]
          exact CFSG.GroupTheory.perm3_inv_conj husq hu2 hk3')
    simpa using h

theorem s3a5ParabolicId_of_moduleFacts {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    S3A5ParabolicId L1 L2 S := by
  have hB := s3a5VertexId_of_moduleFacts hF h1 h2 hC
  exact { toS3A5VertexId := hB
          ext := fun hS => ⟨f112sa_relIndex_T_eq_two hF h1 h2 hB hS,
            f112sa_perm5 hF h1 h2 hB hS, f112sa_s3s3 hF h1 h2 hB hS⟩
          twist := fun hS => f112sa_twist hF h1 h2 hB hS }

end CFSG.Quasithin.F112R.St84
