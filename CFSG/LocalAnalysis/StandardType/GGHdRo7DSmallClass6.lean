module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7DSmClass6Aux_norm_ne {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    {h : DV 6} (hh : h ∈ Φ) : dB ρ h h ≠ 0 := by
  rw [DRCl] at hΦ
  exact hΦ.1 h hh

private theorem hdRo7DSmClass6Aux_neg_mem {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    {h : DV 6} (hh : h ∈ Φ) : -h ∈ Φ := by
  rw [DRCl] at hΦ
  exact hΦ.2.1 h hh

private theorem hdRo7DSmClass6Aux_refl_mem {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    {h g : DV 6} (hh : h ∈ Φ) (hg : g ∈ Φ) : dRef ρ h g ∈ Φ := by
  rw [DRCl] at hΦ
  exact hΦ.2.2.1 h hh g hg

private theorem hdRo7DSmClass6Aux_D_mem {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    {h : DV 6} (h0 : h 0 = 0) (hD : dIsD h) : h ∈ Φ := by
  rw [DRCl] at hΦ
  exact hΦ.2.2.2.2.1 h h0 hD

private theorem hdRo7DSmClass6Aux_shape {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 = 0) : dIsD h ∨ dIsO h := by
  rw [DRCl] at hΦ
  exact hΦ.2.2.2.2.2.1 h hh h0

private theorem hdRo7DSmClass6Aux_exists_ext {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ) :
    ∃ h : DV 6, h ∈ Φ ∧ h 0 ≠ 0 ∧ dSupp h ≠ 0 := by
  rw [DRCl] at hΦ
  exact hΦ.2.2.2.2.2.2

private theorem hdRo7DSmClass6Aux_mem_of_class {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) {g : DV 6}
    (g0 : g 0 ≠ 0) (hs : dSupp g = dSupp h)
    (hsg : dSupp h = 6 → dSgn g = dSgn h) : g ∈ Φ :=
  dRCl_mem_of_ext hT hΦ hh h0 g0 hs.symm (fun h6 => (hsg h6).symm)

private theorem hdRo7DSmClass6Aux_int_mem {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 = 0) (hs : dSupp h = 1)
    {g : DV 6} (g0 : g 0 = 0) (hg : dSupp g = 1) : g ∈ Φ :=
  dRCl_mem_of_int hT hΦ hh h0 g0 hs hg

private theorem hdRo7DSmClass6Aux_rho1_not_supp3 {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 3) :
    False := by
  have ha : (![1,0,0,0,1,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  have hb : (![1,0,0,1,0,2,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho1_not_supp4 {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 4) :
    False := by
  have ha : (![1,0,0,1,1,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  have hb : (![1,0,1,0,2,2,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho1_not_supp6_pos {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 6)
    (hsgn : dSgn h = 1) : False := by
  have ha : (![1,1,1,1,1,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun _ => by rw [hsgn]; decide)
  have hb : (![1,1,1,2,2,2,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun _ => by rw [hsgn]; decide)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho1_not_supp6_neg {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 6)
    (hsgn : dSgn h = -1) : False := by
  have ha : (![1,1,1,1,1,1,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun _ => by rw [hsgn]; decide)
  have hb : (![1,1,1,2,2,2,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun _ => by rw [hsgn]; decide)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho2_not_supp2 {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 2) :
    False := by
  have ha : (![1,0,0,0,0,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  have hb : (![1,0,0,1,1,0,0] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho2_not_supp3 {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 3) :
    False := by
  have ha : (![1,0,0,0,1,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  have hb : (![1,0,1,1,0,0,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho2_not_supp5 {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hk : dSupp h = 5) :
    False := by
  have ha : (![1,0,1,1,1,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  have hb : (![1,0,1,2,2,2,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 (by decide) (by rw [hk]; decide)
      (fun h6 => by omega)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho1_ext_supp {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) :
    dSupp h = 0 ∨ dSupp h = 1 := by
  have hnorm : dB 1 h h ≠ 0 := hdRo7DSmClass6Aux_norm_ne hΦ hh
  rw [dB_self_of_ne 1 h0] at hnorm
  have hsle : dSupp h ≤ 6 := dSupp_le h
  interval_cases hk : dSupp h
  · left; rfl
  · right; rfl
  · exfalso; exact hnorm (by decide)
  · exact absurd (hdRo7DSmClass6Aux_rho1_not_supp3 hΦ hT hh h0 hk) id
  · exact absurd (hdRo7DSmClass6Aux_rho1_not_supp4 hΦ hT hh h0 hk) id
  · exfalso; exact hnorm (by decide)
  · rcases dSgn_of_full h0 hk with hsgn | hsgn
    · exact absurd (hdRo7DSmClass6Aux_rho1_not_supp6_pos hΦ hT hh h0 hk hsgn) id
    · exact absurd (hdRo7DSmClass6Aux_rho1_not_supp6_neg hΦ hT hh h0 hk hsgn) id

private theorem hdRo7DSmClass6Aux_rho2_ext_supp {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) :
    dSupp h = 0 ∨ dSupp h = 6 := by
  have hnorm : dB 2 h h ≠ 0 := hdRo7DSmClass6Aux_norm_ne hΦ hh
  rw [dB_self_of_ne 2 h0] at hnorm
  have hsle : dSupp h ≤ 6 := dSupp_le h
  interval_cases hk : dSupp h
  · left; rfl
  · exfalso; exact hnorm (by decide)
  · exact absurd (hdRo7DSmClass6Aux_rho2_not_supp2 hΦ hT hh h0 hk) id
  · exact absurd (hdRo7DSmClass6Aux_rho2_not_supp3 hΦ hT hh h0 hk) id
  · exfalso; exact hnorm (by decide)
  · exact absurd (hdRo7DSmClass6Aux_rho2_not_supp5 hΦ hT hh h0 hk) id
  · right; rfl

private theorem hdRo7DSmClass6Aux_mem_of_supp0 {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    (he0 : dE 6 0 ∈ Φ) {h : DV 6} (h0 : h 0 ≠ 0) (hs : dSupp h = 0) : h ∈ Φ := by
  have hpm : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  rw [eq_smul_dE_of_dSupp_zero hs]
  rcases hpm _ h0 with h1 | h1
  · rw [h1, one_smul]
    exact he0
  · rw [h1]
    simpa using hdRo7DSmClass6Aux_neg_mem hΦ he0

private theorem hdRo7DSmClass6Aux_e0_mem_of_supp0 {ρ : ZMod 3} {Φ : Set (DV 6)} (hΦ : DRCl ρ Φ)
    {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hs : dSupp h = 0) : dE 6 0 ∈ Φ := by
  have hpm : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  rcases hpm _ h0 with h1 | h1
  · have heq : h = dE 6 0 := by rw [eq_smul_dE_of_dSupp_zero hs, h1, one_smul]
    rwa [heq] at hh
  · have heq : h = -dE 6 0 := by rw [eq_smul_dE_of_dSupp_zero hs, h1]; simp
    have hneg := hdRo7DSmClass6Aux_neg_mem hΦ hh
    rwa [heq, neg_neg] at hneg

private theorem hdRo7DSmClass6Aux_rho1_E1_mem {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {g : DV 6} (g0 : g 0 ≠ 0) (hg : dSupp g = 1) : g ∈ Φ := by
  obtain ⟨h, hh, h0, hsupp⟩ := hdRo7DSmClass6Aux_exists_ext hΦ
  have hk := hdRo7DSmClass6Aux_rho1_ext_supp hΦ hT hh h0
  have hh1 : dSupp h = 1 := by
    rcases hk with hk | hk
    · exact absurd hk hsupp
    · exact hk
  exact hdRo7DSmClass6Aux_mem_of_class hΦ hT hh h0 g0 (by omega) (fun h6 => by omega)

private theorem hdRo7DSmClass6Aux_rho1_intO_mem_of_e0 {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) (he0 : dE 6 0 ∈ Φ) {g : DV 6} (g0 : g 0 = 0) (hg : dSupp g = 1) :
    g ∈ Φ := by
  have ha : dE 6 0 + dE 6 1 ∈ Φ :=
    hdRo7DSmClass6Aux_rho1_E1_mem hΦ hT (by decide) (by decide)
  have hneg1 : -dE 6 1 ∈ Φ := by
    have h := hdRo7DSmClass6Aux_refl_mem hΦ ha he0
    rwa [show dRef 1 (dE 6 0 + dE 6 1) (dE 6 0) = -dE 6 1 by decide] at h
  exact hdRo7DSmClass6Aux_int_mem hΦ hT hneg1 (by decide) (by decide) g0 hg

private theorem hdRo7DSmClass6Aux_rho1_e0_mem_of_intO {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) {g : DV 6} (hg : g ∈ Φ) (g0 : g 0 = 0) (hgs : dSupp g = 1) :
    dE 6 0 ∈ Φ := by
  have ha : dE 6 0 + dE 6 1 ∈ Φ :=
    hdRo7DSmClass6Aux_rho1_E1_mem hΦ hT (by decide) (by decide)
  have he1 : dE 6 1 ∈ Φ :=
    hdRo7DSmClass6Aux_int_mem hΦ hT hg g0 hgs (by decide) (by decide)
  have h := hdRo7DSmClass6Aux_refl_mem hΦ ha he1
  have hneg0 : -dE 6 0 ∈ Φ := by
    rwa [show dRef 1 (dE 6 0 + dE 6 1) (dE 6 1) = -dE 6 0 by decide] at h
  simpa using hdRo7DSmClass6Aux_neg_mem hΦ hneg0

private theorem hdRo7DSmClass6Aux_rho1_eq_B {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) (he0 : dE 6 0 ∈ Φ) : Φ = dPhiB 6 := by
  ext h
  constructor
  · intro hh
    simp only [dPhiB, Set.mem_setOf_eq]
    by_cases h0 : h 0 = 0
    · exact hdRo7DSmClass6Aux_shape hΦ hh h0
    · rcases hdRo7DSmClass6Aux_rho1_ext_supp hΦ hT hh h0 with hs | hs
      · exact Or.inr ((dIsO_iff h).mpr (Or.inr ⟨h0, hs⟩))
      · exact Or.inl ((dIsD_iff h).mpr (Or.inr ⟨h0, hs⟩))
  · intro hh
    simp only [dPhiB, Set.mem_setOf_eq] at hh
    rcases hh with hD | hO
    · rcases (dIsD_iff h).mp hD with ⟨h0, hs⟩ | ⟨h0, hs⟩
      · exact hdRo7DSmClass6Aux_D_mem hΦ h0 hD
      · exact hdRo7DSmClass6Aux_rho1_E1_mem hΦ hT h0 hs
    · rcases (dIsO_iff h).mp hO with ⟨h0, hs⟩ | ⟨h0, hs⟩
      · exact hdRo7DSmClass6Aux_rho1_intO_mem_of_e0 hΦ hT he0 h0 hs
      · exact hdRo7DSmClass6Aux_mem_of_supp0 hΦ he0 h0 hs

private theorem hdRo7DSmClass6Aux_rho1_eq_D {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ)
    (hT : DSmTransLeaf) (he0 : dE 6 0 ∉ Φ) : Φ = dPhiD 6 := by
  ext h
  constructor
  · intro hh
    simp only [dPhiD, Set.mem_setOf_eq]
    by_cases h0 : h 0 = 0
    · rcases hdRo7DSmClass6Aux_shape hΦ hh h0 with hD | hO
      · exact hD
      · exfalso
        have hsupp : dSupp h = 1 := by
          rcases (dIsO_iff h).mp hO with ⟨-, hs⟩ | ⟨hne, -⟩
          · exact hs
          · exact absurd h0 hne
        exact he0 (hdRo7DSmClass6Aux_rho1_e0_mem_of_intO hΦ hT hh h0 hsupp)
    · rcases hdRo7DSmClass6Aux_rho1_ext_supp hΦ hT hh h0 with hs | hs
      · exact absurd (hdRo7DSmClass6Aux_e0_mem_of_supp0 hΦ hh h0 hs) he0
      · exact (dIsD_iff h).mpr (Or.inr ⟨h0, hs⟩)
  · intro hh
    simp only [dPhiD, Set.mem_setOf_eq] at hh
    rcases (dIsD_iff h).mp hh with ⟨h0, hs⟩ | ⟨h0, hs⟩
    · exact hdRo7DSmClass6Aux_D_mem hΦ h0 hh
    · exact hdRo7DSmClass6Aux_rho1_E1_mem hΦ hT h0 hs

private theorem hdRo7DSmClass6Aux_rho2_exists_E6 {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) :
    ∃ h : DV 6, h ∈ Φ ∧ h 0 ≠ 0 ∧ dSupp h = 6 := by
  obtain ⟨h, hh, h0, hsupp⟩ := hdRo7DSmClass6Aux_exists_ext hΦ
  have hk := hdRo7DSmClass6Aux_rho2_ext_supp hΦ hT hh h0
  exact ⟨h, hh, h0, by rcases hk with hk | hk; exacts [absurd hk hsupp, hk]⟩

private theorem hdRo7DSmClass6Aux_rho2_E6_mem {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h₀ : DV 6} (hh₀ : h₀ ∈ Φ) (h0₀ : h₀ 0 ≠ 0)
    (hs₀ : dSupp h₀ = 6) {g : DV 6} (g0 : g 0 ≠ 0) (hg : dSupp g = 6)
    (hsg : dSgn g = dSgn h₀) : g ∈ Φ :=
  hdRo7DSmClass6Aux_mem_of_class hΦ hT hh₀ h0₀ g0 (by omega) (fun _ => hsg)

private theorem hdRo7DSmClass6Aux_rho2_e0_mem {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h₀ : DV 6} (hh₀ : h₀ ∈ Φ) (h0₀ : h₀ 0 ≠ 0)
    (hs₀ : dSupp h₀ = 6) : dE 6 0 ∈ Φ := by
  have hneg : -dE 6 0 ∈ Φ := by
    rcases dSgn_of_full h0₀ hs₀ with hsgn | hsgn
    · have ha : (![1,1,1,1,1,1,1] : DV 6) ∈ Φ :=
        hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ (by decide) (by decide)
          (by rw [hsgn]; decide)
      have hb : (![1,2,2,2,2,2,2] : DV 6) ∈ Φ :=
        hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ (by decide) (by decide)
          (by rw [hsgn]; decide)
      have h := hdRo7DSmClass6Aux_refl_mem hΦ ha hb
      rwa [show dRef 2 (![1,1,1,1,1,1,1] : DV 6) ![1,2,2,2,2,2,2] = -dE 6 0 by decide] at h
    · have ha : (![1,1,1,1,1,1,2] : DV 6) ∈ Φ :=
        hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ (by decide) (by decide)
          (by rw [hsgn]; decide)
      have hb : (![1,2,2,2,2,2,1] : DV 6) ∈ Φ :=
        hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ (by decide) (by decide)
          (by rw [hsgn]; decide)
      have h := hdRo7DSmClass6Aux_refl_mem hΦ ha hb
      rwa [show dRef 2 (![1,1,1,1,1,1,2] : DV 6) ![1,2,2,2,2,2,1] = -dE 6 0 by decide] at h
  simpa using hdRo7DSmClass6Aux_neg_mem hΦ hneg

private theorem hdRo7DSmClass6Aux_rho2_sign_bad {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h g : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hs : dSupp h = 6)
    (hsign : dSgn h = 1) (hg : g ∈ Φ) (g0 : g 0 ≠ 0) (gs : dSupp g = 6)
    (gsign : dSgn g = -1) : False := by
  have ha : (![1,1,1,1,1,1,1] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh h0 hs (by decide) (by decide)
      (by rw [hsign]; decide)
  have hb : (![1,1,2,2,2,2,2] : DV 6) ∈ Φ :=
    hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hg g0 gs (by decide) (by decide)
      (by rw [gsign]; decide)
  exact dRCl_false_of_bad hΦ ha hb (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho2_sgn_eq {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h₀ : DV 6} (hh₀ : h₀ ∈ Φ) (h0₀ : h₀ 0 ≠ 0)
    (hs₀ : dSupp h₀ = 6) {h : DV 6} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (hs : dSupp h = 6) :
    dSgn h = dSgn h₀ := by
  by_contra hne
  have hpm := dSgn_of_full h0 hs
  have hpm₀ := dSgn_of_full h0₀ hs₀
  have hanti : (dSgn h = 1 ∧ dSgn h₀ = -1) ∨ (dSgn h = -1 ∧ dSgn h₀ = 1) := by
    rcases hpm with h1 | h1 <;> rcases hpm₀ with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  rcases hanti with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hdRo7DSmClass6Aux_rho2_sign_bad hΦ hT hh h0 hs h1 hh₀ h0₀ hs₀ h2
  · exact hdRo7DSmClass6Aux_rho2_sign_bad hΦ hT hh₀ h0₀ hs₀ h2 hh h0 hs h1

private theorem hdRo7DSmClass6Aux_rho2_no_intO {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h₀ : DV 6} (hh₀ : h₀ ∈ Φ) (h0₀ : h₀ 0 ≠ 0)
    (hs₀ : dSupp h₀ = 6) {g : DV 6} (hg : g ∈ Φ) (g0 : g 0 = 0) (hgs : dSupp g = 1) :
    False := by
  have he1 : dE 6 1 ∈ Φ :=
    hdRo7DSmClass6Aux_int_mem hΦ hT hg g0 hgs (by decide) (by decide)
  rcases dSgn_of_full h0₀ hs₀ with hsgn | hsgn
  · have ha : (![1,1,1,1,1,1,1] : DV 6) ∈ Φ :=
      hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ (by decide) (by decide)
        (by rw [hsgn]; decide)
    have hb : (![1,2,1,1,1,1,1] : DV 6) ∈ Φ := by
      have h := hdRo7DSmClass6Aux_refl_mem hΦ he1 ha
      rwa [show dRef 2 (dE 6 1) (![1,1,1,1,1,1,1] : DV 6) = ![1,2,1,1,1,1,1] by decide] at h
    exact hdRo7DSmClass6Aux_rho2_sign_bad hΦ hT ha (by decide) (by decide) (by decide)
      hb (by decide) (by decide) (by decide)
  · have ha : (![1,1,1,1,1,1,2] : DV 6) ∈ Φ :=
      hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ (by decide) (by decide)
        (by rw [hsgn]; decide)
    have hb : (![1,2,1,1,1,1,2] : DV 6) ∈ Φ := by
      have h := hdRo7DSmClass6Aux_refl_mem hΦ he1 ha
      rwa [show dRef 2 (dE 6 1) (![1,1,1,1,1,1,2] : DV 6) = ![1,2,1,1,1,1,2] by decide] at h
    exact hdRo7DSmClass6Aux_rho2_sign_bad hΦ hT hb (by decide) (by decide) (by decide)
      ha (by decide) (by decide) (by decide)

private theorem hdRo7DSmClass6Aux_rho2_eq_of_rep {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) {h₀ : DV 6} (hh₀ : h₀ ∈ Φ) (h0₀ : h₀ 0 ≠ 0)
    (hs₀ : dSupp h₀ = 6) : Φ = dPhiE7 (dSgn h₀) := by
  have he0 := hdRo7DSmClass6Aux_rho2_e0_mem hΦ hT hh₀ h0₀ hs₀
  ext h
  constructor
  · intro hh
    simp only [dPhiE7, Set.mem_setOf_eq]
    by_cases h0 : h 0 = 0
    · rcases hdRo7DSmClass6Aux_shape hΦ hh h0 with hD | hO
      · exact Or.inl ⟨h0, hD⟩
      · exfalso
        have hsupp : dSupp h = 1 := by
          rcases (dIsO_iff h).mp hO with ⟨-, hs⟩ | ⟨hne, -⟩
          · exact hs
          · exact absurd h0 hne
        exact hdRo7DSmClass6Aux_rho2_no_intO hΦ hT hh₀ h0₀ hs₀ hh h0 hsupp
    · rcases hdRo7DSmClass6Aux_rho2_ext_supp hΦ hT hh h0 with hs | hs
      · exact Or.inr (Or.inl ⟨h0, (dIsO_iff h).mpr (Or.inr ⟨h0, hs⟩)⟩)
      · exact Or.inr (Or.inr ((dIsS_iff (dSgn h₀) h).mpr
          ⟨h0, hs, hdRo7DSmClass6Aux_rho2_sgn_eq hΦ hT hh₀ h0₀ hs₀ hh h0 hs⟩))
  · intro hh
    simp only [dPhiE7, Set.mem_setOf_eq] at hh
    rcases hh with ⟨h0, hD⟩ | ⟨h0, hO⟩ | hS
    · exact hdRo7DSmClass6Aux_D_mem hΦ h0 hD
    · rcases (dIsO_iff h).mp hO with ⟨hzero, -⟩ | ⟨-, hsupp⟩
      · exact absurd hzero h0
      · exact hdRo7DSmClass6Aux_mem_of_supp0 hΦ he0 h0 hsupp
    · have hsS := (dIsS_iff (dSgn h₀) h).mp hS
      exact hdRo7DSmClass6Aux_rho2_E6_mem hΦ hT hh₀ h0₀ hs₀ hsS.1 hsS.2.1 hsS.2.2

private theorem hdRo7DSmClass6Aux_rho2 {Φ : Set (DV 6)} (hΦ : DRCl 2 Φ)
    (hT : DSmTransLeaf) : Φ = dPhiE7 1 ∨ Φ = dPhiE7 (-1) := by
  obtain ⟨h₀, hh₀, h0₀, hs₀⟩ := hdRo7DSmClass6Aux_rho2_exists_E6 hΦ hT
  have heq := hdRo7DSmClass6Aux_rho2_eq_of_rep hΦ hT hh₀ h0₀ hs₀
  rcases dSgn_of_full h0₀ hs₀ with hsgn | hsgn
  · left; rw [heq, hsgn]
  · right; rw [heq, hsgn]

private theorem hdRo7DSmClass6Aux_rho1 {Φ : Set (DV 6)} (hΦ : DRCl 1 Φ) (hT : DSmTransLeaf) :
    Φ = dPhiD 6 ∨ Φ = dPhiB 6 := by
  by_cases he0 : dE 6 0 ∈ Φ
  · exact Or.inr (hdRo7DSmClass6Aux_rho1_eq_B hΦ hT he0)
  · exact Or.inl (hdRo7DSmClass6Aux_rho1_eq_D hΦ hT he0)

theorem dSmClass6 (hT : DSmTransLeaf) :
    (∀ Φ : Set (DV 6), DRCl 1 Φ → Φ = dPhiD 6 ∨ Φ = dPhiB 6) ∧
    (∀ Φ : Set (DV 6), DRCl 2 Φ → Φ = dPhiE7 1 ∨ Φ = dPhiE7 (-1)) :=
  ⟨fun _ hΦ => hdRo7DSmClass6Aux_rho1 hΦ hT,
   fun _ hΦ => hdRo7DSmClass6Aux_rho2 hΦ hT⟩

end CFSG.StandardType.HdRo7D.Small
