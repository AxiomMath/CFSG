module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmClass7Aux_pm (c : ZMod 3) (hc : c ≠ 0) : c = 1 ∨ c = -1 := by
  have h : c = 0 ∨ c = 1 ∨ c = -1 := by
    revert c
    decide
  rcases h with rfl | rfl | rfl
  · exact absurd rfl hc
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma hdRo7DSmClass7Aux_dE_zero_eq :
    (dE 7 0 : DV 7) = (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) := by
  decide

private lemma hdRo7DSmClass7Aux_mem_of_supp {ρ : ZMod 3} {Φ : Set (DV 7)}
    (hT : DSmTransLeaf) (hΦ : DRCl ρ Φ) {h g : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0)
    {k : ℕ} (hd : dSupp h = k) (g0 : g 0 ≠ 0) (gs : dSupp g = k) (hk : k ≠ 7) : g ∈ Φ := by
  refine dRCl_mem_of_ext hT hΦ hh h0 g0 ?_ ?_
  · rw [hd, gs]
  · intro h7
    exact absurd (hd.symm.trans h7) hk

private lemma hdRo7DSmClass7Aux_E1_mem {ρ : ZMod 3} {Φ : Set (DV 7)}
    (hT : DSmTransLeaf) (hΦ : DRCl ρ Φ) {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0)
    (hd : dSupp h = 1) : ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 1 → g ∈ Φ := by
  intro g g0 gs
  exact hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd g0 gs (by decide)

private lemma hdRo7DSmClass7Aux_E7_mem {ρ : ZMod 3} {Φ : Set (DV 7)}
    (hT : DSmTransLeaf) (hΦ : DRCl ρ Φ) {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0)
    (hd : dSupp h = 7) :
    ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 7 → dSgn g = dSgn h → g ∈ Φ := by
  intro g g0 gs gsg
  exact dRCl_mem_of_ext hT hΦ hh h0 g0 (by rw [hd, gs]) (fun _ => gsg.symm)

private lemma hdRo7DSmClass7Aux_excl3R1 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 1 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 3) : False := by
  have h1 : (![1, 0, 0, 0, 0, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 0, 0, 1, 0, 2, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_excl4R1 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 1 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 4) : False := by
  have h1 : (![1, 0, 0, 0, 1, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 0, 1, 0, 2, 2, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_excl6R1 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 1 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 6) : False := by
  have h1 : (![1, 0, 1, 1, 1, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 1, 1, 2, 2, 2, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_excl2R2 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 2 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 2) : False := by
  have h1 : (![1, 0, 0, 0, 0, 0, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 0, 0, 1, 1, 0, 0] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_excl3R2 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 2 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 3) : False := by
  have h1 : (![1, 0, 0, 0, 0, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 0, 1, 1, 0, 0, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_excl5R2 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 2 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 5) : False := by
  have h1 : (![1, 0, 0, 1, 1, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 0, 1, 2, 2, 2, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_excl6R2 {Φ : Set (DV 7)} (hT : DSmTransLeaf) (hΦ : DRCl 2 Φ)
    {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 6) : False := by
  have h1 : (![1, 0, 1, 1, 1, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  have h2 : (![1, 0, 1, 2, 2, 2, 2, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_mem_of_supp hT hΦ hh h0 hd (by decide) (by decide) (by decide)
  exact dRCl_false_of_bad hΦ h1 h2 (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_supp_cases_R1 {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) :
    dSupp h = 0 ∨ dSupp h = 1 ∨ dSupp h = 7 := by
  have hle : dSupp h ≤ 7 := dSupp_le h
  have hne := hΦ.1 h hh
  rw [dB_self_of_ne 1 h0] at hne
  interval_cases hk : dSupp h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exfalso
    exact hne (by decide)
  · exfalso
    exact hdRo7DSmClass7Aux_excl3R1 hT hΦ hh h0 hk
  · exfalso
    exact hdRo7DSmClass7Aux_excl4R1 hT hΦ hh h0 hk
  · exfalso
    exact hne (by decide)
  · exfalso
    exact hdRo7DSmClass7Aux_excl6R1 hT hΦ hh h0 hk
  · exact Or.inr (Or.inr rfl)

private lemma hdRo7DSmClass7Aux_E1_or_E7 {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) :
    (∃ h ∈ Φ, h 0 ≠ 0 ∧ dSupp h = 1) ∨ (∃ h ∈ Φ, h 0 ≠ 0 ∧ dSupp h = 7) := by
  obtain ⟨h, hh, h0, hsupp⟩ := hΦ.2.2.2.2.2.2
  rcases hdRo7DSmClass7Aux_supp_cases_R1 hT hΦ hh h0 with hk | hk | hk
  · exact absurd hk hsupp
  · exact Or.inl ⟨h, hh, h0, hk⟩
  · exact Or.inr ⟨h, hh, h0, hk⟩

private lemma hdRo7DSmClass7Aux_E7_forces_E1 {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 7) :
    ∃ g ∈ Φ, g 0 ≠ 0 ∧ dSupp g = 1 := by
  have hsgn := dSgn_of_full h0 hd
  rcases hsgn with hs | hs
  · have h1 : (![1, 1, 1, 1, 1, 1, 1, 1] : DV 7) ∈ Φ :=
      hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
    have h2 : (![1, 1, 2, 2, 2, 2, 2, 2] : DV 7) ∈ Φ :=
      hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
    refine ⟨dRef 1 (![1, 1, 1, 1, 1, 1, 1, 1] : DV 7) (![1, 1, 2, 2, 2, 2, 2, 2] : DV 7),
      hΦ.2.2.1 _ h1 _ h2, by decide, by decide⟩
  · have h1 : (![1, 1, 1, 1, 1, 1, 1, 2] : DV 7) ∈ Φ :=
      hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
    have h2 : (![1, 1, 2, 2, 2, 2, 2, 1] : DV 7) ∈ Φ :=
      hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
    refine ⟨dRef 1 (![1, 1, 1, 1, 1, 1, 1, 2] : DV 7) (![1, 1, 2, 2, 2, 2, 2, 1] : DV 7),
      hΦ.2.2.1 _ h1 _ h2, by decide, by decide⟩

private lemma hdRo7DSmClass7Aux_E7_signs_false {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) {h g : DV 7} (hh : h ∈ Φ) (hg : g ∈ Φ) (h0 : h 0 ≠ 0) (g0 : g 0 ≠ 0)
    (hd : dSupp h = 7) (gd : dSupp g = 7) (hs : dSgn h = 1) (gs : dSgn g = -1) : False := by
  have hp : (![1, 1, 1, 1, 1, 1, 1, 1] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
  have hm : (![1, 1, 1, 2, 2, 2, 2, 2] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_E7_mem hT hΦ hg g0 gd _ (by decide) (by decide) (by rw [gs]; decide)
  exact dRCl_false_of_bad hΦ hp hm (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_E7_sgn_eq {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) {h g : DV 7} (hh : h ∈ Φ) (hg : g ∈ Φ) (h0 : h 0 ≠ 0) (g0 : g 0 ≠ 0)
    (hd : dSupp h = 7) (gd : dSupp g = 7) : dSgn h = dSgn g := by
  rcases dSgn_of_full h0 hd with hs | hs <;> rcases dSgn_of_full g0 gd with gs | gs
  · rw [hs, gs]
  · exact (hdRo7DSmClass7Aux_E7_signs_false hT hΦ hh hg h0 g0 hd gd hs gs).elim
  · exact (hdRo7DSmClass7Aux_E7_signs_false hT hΦ hg hh g0 h0 gd hd gs hs).elim
  · rw [hs, gs]

private lemma hdRo7DSmClass7Aux_e0_E7_false {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) {h : DV 7} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hd : dSupp h = 7)
    (he0 : dE 7 0 ∈ Φ) : False := by
  have he0' : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ :=
    hdRo7DSmClass7Aux_dE_zero_eq ▸ he0
  rcases dSgn_of_full h0 hd with hs | hs
  · have hp : (![1, 1, 1, 1, 1, 1, 1, 1] : DV 7) ∈ Φ :=
      hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
    exact dRCl_false_of_bad hΦ hp he0' (by decide) (by decide)
  · have hp : (![1, 1, 1, 1, 1, 1, 1, 2] : DV 7) ∈ Φ :=
      hdRo7DSmClass7Aux_E7_mem hT hΦ hh h0 hd _ (by decide) (by decide) (by rw [hs]; decide)
    exact dRCl_false_of_bad hΦ hp he0' (by decide) (by decide)

private lemma hdRo7DSmClass7Aux_ref_e1 :
    dRef 1 (![1, 1, 0, 0, 0, 0, 0, 0] : DV 7) (![0, 1, 0, 0, 0, 0, 0, 0] : DV 7) =
      (![2, 0, 0, 0, 0, 0, 0, 0] : DV 7) := by
  decide

private lemma hdRo7DSmClass7Aux_neg_ref_e1 :
    -(![2, 0, 0, 0, 0, 0, 0, 0] : DV 7) = (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) := by
  decide

private lemma hdRo7DSmClass7Aux_ref_e0 :
    dRef 1 (![1, 1, 0, 0, 0, 0, 0, 0] : DV 7) (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) =
      (![0, 2, 0, 0, 0, 0, 0, 0] : DV 7) := by
  decide

private lemma hdRo7DSmClass7Aux_neg_ref_e0 :
    -(![0, 2, 0, 0, 0, 0, 0, 0] : DV 7) = (![0, 1, 0, 0, 0, 0, 0, 0] : DV 7) := by
  decide

private lemma hdRo7DSmClass7Aux_e0_of_OU {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) (hE1mem : ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 1 → g ∈ Φ)
    {g : DV 7} (hg : g ∈ Φ) (g0 : g 0 = 0) (gs : dSupp g = 1) :
    (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ := by
  have he1 : (![0, 1, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ :=
    dRCl_mem_of_int hT hΦ hg g0 (by decide) gs (by decide)
  have hsum : (![1, 1, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ :=
    hE1mem _ (by decide) (by decide)
  have href : (![2, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ := by
    have h := hΦ.2.2.1 _ hsum _ he1
    rwa [hdRo7DSmClass7Aux_ref_e1] at h
  have hneg : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ := by
    have h := hΦ.2.1 _ href
    rwa [hdRo7DSmClass7Aux_neg_ref_e1] at h
  exact hneg

private lemma hdRo7DSmClass7Aux_OU_of_e0 {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) (hE1mem : ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 1 → g ∈ Φ)
    (he0 : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ) {g : DV 7} (g0 : g 0 = 0)
    (gs : dSupp g = 1) : g ∈ Φ := by
  have hsum : (![1, 1, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ :=
    hE1mem _ (by decide) (by decide)
  have href : (![0, 2, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ := by
    have h := hΦ.2.2.1 _ hsum _ he0
    rwa [hdRo7DSmClass7Aux_ref_e0] at h
  have he1 : (![0, 1, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ := by
    have h := hΦ.2.1 _ href
    rwa [hdRo7DSmClass7Aux_neg_ref_e0] at h
  exact dRCl_mem_of_int hT hΦ he1 (by decide) g0 (by decide) gs

private lemma hdRo7DSmClass7Aux_smul_e0_mem {Φ : Set (DV 7)} (hΦ : DRCl 1 Φ) {c : ZMod 3}
    (hc : c = 1 ∨ c = -1) (he0 : dE 7 0 ∈ Φ) : c • dE 7 0 ∈ Φ := by
  rcases hc with rfl | rfl
  · simpa using he0
  · have h := hΦ.2.1 _ he0
    simpa using h

private lemma hdRo7DSmClass7Aux_eq_D {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) (hnoE7 : ¬ ∃ h ∈ Φ, h 0 ≠ 0 ∧ dSupp h = 7)
    (hE1mem : ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 1 → g ∈ Φ)
    (he0 : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∉ Φ) : Φ = dPhiD 7 := by
  ext g
  constructor
  · intro hg
    by_cases g0 : g 0 = 0
    · rcases hΦ.2.2.2.2.2.1 g hg g0 with hD | hO
      · exact hD
      · exfalso
        rcases (dIsO_iff g).mp hO with ⟨_, gs⟩ | ⟨hne, _⟩
        · exact he0 (hdRo7DSmClass7Aux_e0_of_OU hT hΦ hE1mem hg g0 gs)
        · exact hne g0
    · rcases hdRo7DSmClass7Aux_supp_cases_R1 hT hΦ hg g0 with hk | hk | hk
      · exfalso
        have hc := hdRo7DSmClass7Aux_pm (g 0) g0
        rw [eq_smul_dE_of_dSupp_zero hk] at hg
        rcases hc with hc | hc
        · rw [hc, one_smul] at hg
          exact he0 (hdRo7DSmClass7Aux_dE_zero_eq ▸ hg)
        · have hneg := hΦ.2.1 _ hg
          rw [hc] at hneg
          have hmem : dE 7 0 ∈ Φ := by simpa using hneg
          exact he0 (hdRo7DSmClass7Aux_dE_zero_eq ▸ hmem)
      · exact (dIsD_iff g).mpr (Or.inr ⟨g0, hk⟩)
      · exact absurd ⟨g, hg, g0, hk⟩ hnoE7
  · intro hg
    rcases (dIsD_iff g).mp hg with ⟨g0, gs⟩ | ⟨g0, gs⟩
    · exact hΦ.2.2.2.2.1 g g0 hg
    · exact hE1mem g g0 gs

private lemma hdRo7DSmClass7Aux_eq_B {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) (hnoE7 : ¬ ∃ h ∈ Φ, h 0 ≠ 0 ∧ dSupp h = 7)
    (hE1mem : ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 1 → g ∈ Φ)
    (he0 : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ) : Φ = dPhiB 7 := by
  ext g
  constructor
  · intro hg
    by_cases g0 : g 0 = 0
    · rcases hΦ.2.2.2.2.2.1 g hg g0 with hD | hO
      · exact Or.inl hD
      · exact Or.inr hO
    · rcases hdRo7DSmClass7Aux_supp_cases_R1 hT hΦ hg g0 with hk | hk | hk
      · exact Or.inr ((dIsO_iff g).mpr (Or.inr ⟨g0, hk⟩))
      · exact Or.inl ((dIsD_iff g).mpr (Or.inr ⟨g0, hk⟩))
      · exact absurd ⟨g, hg, g0, hk⟩ hnoE7
  · intro hg
    rcases hg with hD | hO
    · rcases (dIsD_iff g).mp hD with ⟨g0, gs⟩ | ⟨g0, gs⟩
      · exact hΦ.2.2.2.2.1 g g0 hD
      · exact hE1mem g g0 gs
    · rcases (dIsO_iff g).mp hO with ⟨g0, gs⟩ | ⟨g0, gs⟩
      · exact hdRo7DSmClass7Aux_OU_of_e0 hT hΦ hE1mem he0 g0 gs
      · have hc := hdRo7DSmClass7Aux_pm (g 0) g0
        have hge := eq_smul_dE_of_dSupp_zero gs
        rw [hge]
        exact hdRo7DSmClass7Aux_smul_e0_mem hΦ hc
          (hdRo7DSmClass7Aux_dE_zero_eq.symm ▸ he0)

private lemma hdRo7DSmClass7Aux_eq_E8 {Φ : Set (DV 7)} (hT : DSmTransLeaf)
    (hΦ : DRCl 1 Φ) (hE1mem : ∀ g : DV 7, g 0 ≠ 0 → dSupp g = 1 → g ∈ Φ)
    (he0 : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∉ Φ) {h₀ : DV 7} (hh₀ : h₀ ∈ Φ)
    (h0₀ : h₀ 0 ≠ 0) (hd₀ : dSupp h₀ = 7) (σ : ZMod 3) (hs₀ : dSgn h₀ = σ) :
    Φ = dPhiE8 σ := by
  ext g
  constructor
  · intro hg
    by_cases g0 : g 0 = 0
    · rcases hΦ.2.2.2.2.2.1 g hg g0 with hD | hO
      · exact Or.inl hD
      · exfalso
        rcases (dIsO_iff g).mp hO with ⟨_, gs⟩ | ⟨hne, _⟩
        · exact he0 (hdRo7DSmClass7Aux_e0_of_OU hT hΦ hE1mem hg g0 gs)
        · exact hne g0
    · rcases hdRo7DSmClass7Aux_supp_cases_R1 hT hΦ hg g0 with hk | hk | hk
      · exfalso
        have hc := hdRo7DSmClass7Aux_pm (g 0) g0
        rw [eq_smul_dE_of_dSupp_zero hk] at hg
        rcases hc with hc | hc
        · rw [hc, one_smul] at hg
          exact he0 (hdRo7DSmClass7Aux_dE_zero_eq ▸ hg)
        · have hneg := hΦ.2.1 _ hg
          rw [hc] at hneg
          have hmem : dE 7 0 ∈ Φ := by simpa using hneg
          exact he0 (hdRo7DSmClass7Aux_dE_zero_eq ▸ hmem)
      · exact Or.inl ((dIsD_iff g).mpr (Or.inr ⟨g0, hk⟩))
      · have hsg : dSgn g = σ := by
          rw [← hs₀]
          exact (hdRo7DSmClass7Aux_E7_sgn_eq hT hΦ hh₀ hg h0₀ g0 hd₀ hk).symm
        exact Or.inr ((dIsS_iff σ g).mpr ⟨g0, hk, hsg⟩)
  · intro hg
    rcases hg with hD | hS
    · rcases (dIsD_iff g).mp hD with ⟨g0, gs⟩ | ⟨g0, gs⟩
      · exact hΦ.2.2.2.2.1 g g0 hD
      · exact hE1mem g g0 gs
    · rcases (dIsS_iff σ g).mp hS with ⟨g0, gs, gsg⟩
      exact hdRo7DSmClass7Aux_E7_mem hT hΦ hh₀ h0₀ hd₀ g g0 gs (by rw [hs₀, gsg])

private lemma hdRo7DSmClass7Aux_no_R2 (hT : DSmTransLeaf) {Φ : Set (DV 7)}
    (hΦ : DRCl 2 Φ) : False := by
  obtain ⟨h, hh, h0, hsupp⟩ := hΦ.2.2.2.2.2.2
  have hle : dSupp h ≤ 7 := dSupp_le h
  have hne := hΦ.1 h hh
  rw [dB_self_of_ne 2 h0] at hne
  interval_cases hk : dSupp h
  · exact hsupp rfl
  · exfalso
    exact hne (by decide)
  · exfalso
    exact hdRo7DSmClass7Aux_excl2R2 hT hΦ hh h0 hk
  · exfalso
    exact hdRo7DSmClass7Aux_excl3R2 hT hΦ hh h0 hk
  · exfalso
    exact hne (by decide)
  · exfalso
    exact hdRo7DSmClass7Aux_excl5R2 hT hΦ hh h0 hk
  · exfalso
    exact hdRo7DSmClass7Aux_excl6R2 hT hΦ hh h0 hk
  · exfalso
    exact hne (by decide)

theorem dSmClass7 (hT : DSmTransLeaf) :
    (∀ Φ : Set (DV 7), DRCl 1 Φ →
      Φ = dPhiD 7 ∨ Φ = dPhiB 7 ∨ Φ = dPhiE8 1 ∨ Φ = dPhiE8 (-1)) ∧
    (∀ Φ : Set (DV 7), ¬ DRCl 2 Φ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro Φ hΦ
    by_cases hE7 : ∃ h ∈ Φ, h 0 ≠ 0 ∧ dSupp h = 7
    · obtain ⟨h₇, hh₇, h0₇, hd₇⟩ := hE7
      have hsgn₇ := dSgn_of_full h0₇ hd₇
      obtain ⟨m, hm, hm0, hmd⟩ := hdRo7DSmClass7Aux_E7_forces_E1 hT hΦ hh₇ h0₇ hd₇
      have hE1mem := hdRo7DSmClass7Aux_E1_mem hT hΦ hm hm0 hmd
      have he0 : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∉ Φ := by
        intro he
        exact hdRo7DSmClass7Aux_e0_E7_false hT hΦ hh₇ h0₇ hd₇
          (hdRo7DSmClass7Aux_dE_zero_eq.symm ▸ he)
      rcases hsgn₇ with hs | hs
      · have h := hdRo7DSmClass7Aux_eq_E8 hT hΦ hE1mem he0 hh₇ h0₇ hd₇ (dSgn h₇) rfl
        rw [hs] at h
        exact Or.inr (Or.inr (Or.inl h))
      · have h := hdRo7DSmClass7Aux_eq_E8 hT hΦ hE1mem he0 hh₇ h0₇ hd₇ (dSgn h₇) rfl
        rw [hs] at h
        exact Or.inr (Or.inr (Or.inr h))
    · rcases hdRo7DSmClass7Aux_E1_or_E7 hT hΦ with ⟨m, hm, hm0, hmd⟩ | ⟨m, hm, hm0, hmd⟩
      · have hE1mem := hdRo7DSmClass7Aux_E1_mem hT hΦ hm hm0 hmd
        by_cases he0 : dE 7 0 ∈ Φ
        · have he0' : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∈ Φ :=
            hdRo7DSmClass7Aux_dE_zero_eq ▸ he0
          exact Or.inr (Or.inl (hdRo7DSmClass7Aux_eq_B hT hΦ hE7 hE1mem he0'))
        · have he0' : (![1, 0, 0, 0, 0, 0, 0, 0] : DV 7) ∉ Φ :=
            fun he => he0 (hdRo7DSmClass7Aux_dE_zero_eq.symm ▸ he)
          exact Or.inl (hdRo7DSmClass7Aux_eq_D hT hΦ hE7 hE1mem he0')
      · exact absurd ⟨m, hm, hm0, hmd⟩ hE7
  · intro Φ hΦ
    exact hdRo7DSmClass7Aux_no_R2 hT hΦ

end CFSG.StandardType.HdRo7D.Small
