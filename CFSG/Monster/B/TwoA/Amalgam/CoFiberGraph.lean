module

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdj

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)

@[expose] def piDelta :

    Set CVert := {w | ∃ h : w ∈ cPi0, (cpsi ⟨w, h⟩ : Wv v0) ∈ Unitary.DeltaW}

@[expose] def piTau :
    Set CVert :=
  {w | ∃ h : w ∈ cPi0, (cpsi ⟨w, h⟩ : Wv v0) ∈ Unitary.usigOrbit Unitary.tauW}

abbrev piV
    (k : Jhat) : cPi0 := ⟨cvOf (jhatS k), jhatS_mem_cPi0 k⟩

theorem exists_piV
    (v : cPi0) : ∃ k : Jhat, v = piV k := by
  obtain ⟨k, hk⟩ := mem_cPi0.1 v.2
  exact ⟨k, Subtype.ext hk⟩

theorem cpsi_piV
    (k : Jhat) : cpsi (piV k) = piPt k := cpsi_cvOf k

theorem piV_eq_iff
    {k k' : Jhat} : piV k = piV k' ↔ cvOf (jhatS k) = cvOf (jhatS k') :=
  Subtype.ext_iff

theorem piPt_surjective :
    Function.Surjective piPt := by
  rintro ⟨x, g, rfl⟩
  obtain ⟨k, rfl⟩ := jhatToKv0_surjective g
  exact ⟨k, rfl⟩

theorem cpsi_preimage
    (k : Jhat) : cpsi ⁻¹' {piPt k} = {piV k, piV (a0J * k)} := by
  ext v
  obtain ⟨k', rfl⟩ := exists_piV v
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, cpsi_piV,
    Subtype.mk.injEq]
  exact ⟨fun h => piPt_eq_iff.1 h.symm, fun h => (piPt_eq_iff.2 h).symm⟩

theorem ncard_cpsi_preimage
    (x : Unitary.OmegaPt) : (cpsi ⁻¹' {x}).ncard = 2 := by
  obtain ⟨k, rfl⟩ := piPt_surjective x
  rw [cpsi_preimage]
  exact Set.ncard_pair fun h => cvOf_jhatS_ne_a0J k (piV_eq_iff.1 h)

theorem cvOf_a0S_mem_cPi0 :
    cvOf a0S ∈ cPi0 := jhatS_mem_cPi0 a0J

theorem mem_piDelta_iff
    (k : Jhat) :
    cvOf (jhatS k) ∈ piDelta ↔ (piPt k : Wv v0) ∈ Unitary.DeltaW :=
  ⟨fun ⟨_, h⟩ => by rwa [cpsi_cvOf] at h, fun h => ⟨jhatS_mem_cPi0 k, by rwa [cpsi_cvOf]⟩⟩

theorem mem_piTau_iff
    (k : Jhat) :
    cvOf (jhatS k) ∈ piTau ↔ (piPt k : Wv v0) ∈ Unitary.usigOrbit Unitary.tauW :=
  ⟨fun ⟨_, h⟩ => by rwa [cpsi_cvOf] at h, fun h => ⟨jhatS_mem_cPi0 k, by rwa [cpsi_cvOf]⟩⟩

theorem p1Orb_eq_of_mem
    {k : Jhat} {S : Set (Wv v0)} (hS : Unitary.usigOrbit (piPt k) = S)
    (hk : (piPt k : Wv v0) ≠ Unitary.sigmaW) :
    p1Orb (cvOf (jhatS k)) = {w | ∃ h : w ∈ cPi0, (cpsi ⟨w, h⟩ : Wv v0) ∈ S} := by
  rw [p1Orb_eq hk, hS]
  ext w
  constructor
  · rintro ⟨k', rfl, hk'⟩
    exact ⟨jhatS_mem_cPi0 k', by rwa [cpsi_cvOf]⟩
  · rintro ⟨hw, hS'⟩
    obtain ⟨k', hk'⟩ := mem_cPi0.1 hw
    subst hk'
    exact ⟨k', rfl, by rwa [cpsi_cvOf] at hS'⟩

theorem p1Orb_of_mem_piDelta
    {v : CVert} (hv : v ∈ piDelta) : p1Orb v = piDelta := by
  obtain ⟨hv0, hΔ⟩ := hv
  obtain ⟨k, rfl⟩ := mem_cPi0.1 hv0
  rw [cpsi_cvOf] at hΔ
  have hσ : (piPt k : Wv v0) ≠ Unitary.sigmaW := fun e =>
    Unitary.sigmaW_notMem_DeltaW (e ▸ hΔ)
  refine p1Orb_eq_of_mem ?_ hσ
  rw [← Unitary.usigOrbit_delta] at hΔ ⊢
  exact Unitary.usigOrbit_eq_of_mem hΔ

theorem p1Orb_of_mem_piTau
    {v : CVert} (hv : v ∈ piTau) : p1Orb v = piTau := by
  obtain ⟨hv0, hτ⟩ := hv
  obtain ⟨k, rfl⟩ := mem_cPi0.1 hv0
  rw [cpsi_cvOf] at hτ
  have hσ : (piPt k : Wv v0) ≠ Unitary.sigmaW := fun e =>
    Unitary.sigmaW_notMem_tauOrb (e ▸ hτ)
  exact p1Orb_eq_of_mem (Unitary.usigOrbit_eq_of_mem hτ) hσ

theorem mem_cPi0_cases
    (v : cPi0) :
    v.1 = cv0 ∨ v.1 = cvOf a0S ∨ v.1 ∈ piDelta ∨ v.1 ∈ piTau := by
  obtain ⟨k, rfl⟩ := exists_piV v
  have hΩ := (Set.ext_iff.1 Unitary.OmegaW_eq_union _).1 (piPt k).2
  rcases hΩ with (h | h) | h
  · have h1 : piPt 1 = piPt k := Subtype.ext (coe_piPt_one.trans (Set.mem_singleton_iff.1 h).symm)
    rcases piPt_eq_iff.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (h2.trans (by rw [mul_one, cvOf_jhatS_a0J])))
  · exact Or.inr (Or.inr (Or.inl ((mem_piDelta_iff k).2 h)))
  · exact Or.inr (Or.inr (Or.inr ((mem_piTau_iff k).2 h)))

theorem piDelta_eq_image :
    piDelta = Subtype.val '' (cpsi ⁻¹' {x | (x : Wv v0) ∈ Unitary.DeltaW}) := by
  ext w
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨⟨w, hw⟩, h, rfl⟩
  · rintro ⟨v, h, rfl⟩
    exact ⟨v.2, h⟩

theorem piTau_eq_image :
    piTau = Subtype.val '' (cpsi ⁻¹' {x | (x : Wv v0) ∈ Unitary.usigOrbit Unitary.tauW}) := by
  ext w
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨⟨w, hw⟩, h, rfl⟩
  · rintro ⟨v, h, rfl⟩
    exact ⟨v.2, h⟩

theorem ncard_OmegaPt_mem
    {S : Set (Wv v0)} (hS : S ⊆ Unitary.OmegaW) :
    {x : Unitary.OmegaPt | (x : Wv v0) ∈ S}.ncard = S.ncard :=
  Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
    (by rw [Subtype.range_coe]; exact hS)

theorem ncard_piDelta :
    piDelta.ncard = 1782 := by
  rw [piDelta_eq_image, Set.ncard_image_of_injective _ Subtype.val_injective,
    ncard_preimage_of_fiber ncard_cpsi_preimage, ncard_OmegaPt_mem Unitary.DeltaW_subset,
    Unitary.ncard_DeltaW]

theorem ncard_piTau :
    piTau.ncard = 2816 := by
  rw [piTau_eq_image, Set.ncard_image_of_injective _ Subtype.val_injective,
    ncard_preimage_of_fiber ncard_cpsi_preimage, ncard_OmegaPt_mem Unitary.tauOrb_subset,
    Unitary.ncard_usigOrbit_tau]

theorem image_piDelta :
    (fun v : cPi0 => (cpsi v : Wv v0)) '' {v | v.1 ∈ piDelta} = Unitary.DeltaW := by
  ext x
  constructor
  · rintro ⟨v, ⟨hv, h⟩, rfl⟩
    exact h
  · intro hx
    obtain ⟨k, hk⟩ := piPt_surjective ⟨x, Unitary.DeltaW_subset hx⟩
    refine ⟨piV k, (mem_piDelta_iff k).2 (by rw [hk]; exact hx), ?_⟩
    simp only [cpsi_piV, hk]

theorem image_piTau :
    (fun v : cPi0 => (cpsi v : Wv v0)) '' {v | v.1 ∈ piTau} =
      Unitary.usigOrbit Unitary.tauW := by
  ext x
  constructor
  · rintro ⟨v, ⟨hv, h⟩, rfl⟩
    exact h
  · intro hx
    obtain ⟨k, hk⟩ := piPt_surjective ⟨x, Unitary.tauOrb_subset hx⟩
    refine ⟨piV k, (mem_piTau_iff k).2 (by rw [hk]; exact hx), ?_⟩
    simp only [cpsi_piV, hk]

theorem cgraphPi_adj_iff
    {v w : cPi0} (hvw : v ≠ w) :
    cgraphPi.Adj v w ↔ cpsi v = cpsi w ∨ Unitary.omegaGraph.Adj (cpsi v) (cpsi w) := by
  obtain ⟨k, rfl⟩ := exists_piV v
  obtain ⟨k', rfl⟩ := exists_piV w
  rw [cpsi_piV, cpsi_piV]
  exact adj_jhatS_iff fun h => hvw (piV_eq_iff.2 h)

theorem omegaGraph_params :
    (∀ x : Unitary.OmegaPt, (Unitary.omegaGraph.neighborSet x).ncard = 891) ∧
      ∀ x y : Unitary.OmegaPt, x ≠ y → ¬ Unitary.omegaGraph.Adj x y →
        (Unitary.omegaGraph.commonNeighbors x y).ncard = 324 := by
  classical
  have h := (CFSG.Monster.B.Generic.rank_three_2300_graph_parameters (H := Kstab v0)
    (Ω := Unitary.OmegaPt) Unitary.card_OmegaPt Unitary.omega_suborbits).2.2.2.2
  refine ⟨fun x => ?_, fun x y hxy hn => ?_⟩
  · have h1 := h.regular x
    rw [← SimpleGraph.card_neighborSet_eq_degree] at h1
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    convert h1
    rfl
  · rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    convert h.of_not_adj hxy hn
    rfl

theorem native_Co2_two_clique_fiber_graph :
    cPi0.ncard = 4600 ∧ (∀ x : Unitary.OmegaPt, (cpsi ⁻¹' {x}).ncard = 2) ∧
    (∀ v w : cPi0, ∃ k : Shat, (k : Dfull) ∈ Jhat ∧ cvMul v k = w) ∧
    (∀ k : Shat, (k : Dfull) ∈ Jhat → (cvMul cv0 k = cv0 ↔ (k : Dfull) ∈ P1)) ∧
    p1Orb cv0 = {cv0} ∧
    (∀ (a : Dfull) (ha : a ∈ Ehat), a ∉ N1 →
      cvOf (elS ha) ∈ cPi0 ∧ p1Orb (cvOf (elS ha)) = {cvOf (elS ha)}) ∧
    (∀ v ∈ piDelta, p1Orb v = piDelta) ∧ (∀ v ∈ piTau, p1Orb v = piTau) ∧
    (∀ v : cPi0, v.1 = cv0 ∨ v.1 = cvOf a0S ∨ v.1 ∈ piDelta ∨ v.1 ∈ piTau) ∧
    piDelta.ncard = 1782 ∧ piTau.ncard = 2816 ∧
    (fun v : cPi0 => (cpsi v : Wv v0)) '' {v | v.1 ∈ piDelta} = Unitary.DeltaW ∧
    (fun v : cPi0 => (cpsi v : Wv v0)) '' {v | v.1 ∈ piTau} = Unitary.usigOrbit Unitary.tauW ∧
    (∀ v w : cPi0, v ≠ w →
      (cgraphPi.Adj v w ↔ cpsi v = cpsi w ∨ Unitary.omegaGraph.Adj (cpsi v) (cpsi w))) ∧
    cgraphPi.Connected ∧ (∀ v : cPi0, (cgraphPi.neighborSet v).ncard = 1783) ∧
    cgraphPi.diam = 2 ∧
    (∀ v w : cPi0, v ≠ w → ¬ cgraphPi.Adj v w → (cgraphPi.commonNeighbors v w).ncard = 648) ∧
    Set.InjOn clabel cPi0 ∧ clabel '' cPi0 = {y | ∃ g ∈ Jhat, g⁻¹ * cQ * g = y} := by
  obtain ⟨hk, hμ⟩ := omegaGraph_params
  obtain ⟨hdeg, hconn, hdiam, hcommon⟩ := twoClique_extension (G := cgraphPi)
    ncard_cpsi_preimage (fun v w hvw => cgraphPi_adj_iff hvw) hk hμ (by norm_num)
    Unitary.sigmaPt_ne_tauPt Unitary.not_adj_sigmaPt_tauPt
  refine ⟨?_, ncard_cpsi_preimage, ?_, ?_, p1Orb_cv0, fun a ha hn => ⟨?_, p1Orb_elS ha hn⟩,
    fun v hv => p1Orb_of_mem_piDelta hv, fun v hv => p1Orb_of_mem_piTau hv, mem_cPi0_cases,
    ncard_piDelta, ncard_piTau, image_piDelta, image_piTau, fun v w hvw => cgraphPi_adj_iff hvw,
    hconn, hdeg, hdiam, hcommon, ?_, ?_⟩
  ·
    have h := ncard_preimage_of_fiber ncard_cpsi_preimage (Set.univ : Set Unitary.OmegaPt)
    rw [Set.preimage_univ, Set.ncard_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card (α := Unitary.OmegaPt), Unitary.card_OmegaPt] at h
    rw [← Nat.card_coe_set_eq, h]
  ·
    intro v w
    obtain ⟨k, rfl⟩ := exists_piV v
    obtain ⟨k', rfl⟩ := exists_piV w
    refine ⟨jhatS (k⁻¹ * k'), (k⁻¹ * k').2, ?_⟩
    show cvMul (cvOf (jhatS k)) (jhatS (k⁻¹ * k')) = cvOf (jhatS k')
    rw [cvMul_jhatS, mul_inv_cancel_left]
  ·
    intro k hk
    rw [cvMul_cv0_iff, ← Eam_inf_Jhat]
    exact ⟨fun h => ⟨h, hk⟩, fun h => h.1⟩
  · exact jhatS_mem_cPi0 ⟨a, Ehat_le_Jhat ha⟩
  ·
    intro v hv w hw h
    obtain ⟨k, rfl⟩ := mem_cPi0.1 hv
    obtain ⟨k', rfl⟩ := mem_cPi0.1 hw
    rw [clabel_jhatS, clabel_jhatS] at h
    exact labE_eq_iff.1 (Subtype.ext h)
  ·
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨k, rfl⟩ := mem_cPi0.1 hv
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨cvOf (jhatS ⟨g, hg⟩), jhatS_mem_cPi0 _, rfl⟩

end CFSG.Monster.B.TwoA.Amalgam
