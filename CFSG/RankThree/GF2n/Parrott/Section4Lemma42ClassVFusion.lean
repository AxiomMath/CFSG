module

public import CFSG.RankThree.GF2n.Parrott.SpinFusionChecks
public import CFSG.RankThree.GF2n.Parrott.XAbelianCrux
public import CFSG.RankThree.GF2n.Parrott.XAbelianTools
public import CFSG.RankThree.GF2n.Parrott.SpinXFacts
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassV
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassVSpin
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

section Fusion

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

theorem bitmask_add_xabX_mulVec (m : V) :
    bitmask (m + ((rhoA xabX : GL8) : Mat8) *ᵥ m) = bitmask m ^^^ bapply bX (bitmask m) := by
  rw [bitmask_add, ← spinMat_apply xabX, ← bapply_colsOf, cols_xabX]

omit [Finite G]
  hN in
theorem conj_commutator_eq_inv_of_mul_self {x j : G} (hxx : x * x = 1) :
    x * (x * j * x⁻¹ * j⁻¹) * x⁻¹ = (x * j * x⁻¹ * j⁻¹)⁻¹ := by
  have hxx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hxx, inv_one]
  rw [eq_inv_iff_mul_eq_one]
  calc x * (x * j * x⁻¹ * j⁻¹) * x⁻¹ * (x * j * x⁻¹ * j⁻¹)
      = (x * x) * j * (x⁻¹ * x⁻¹) * j⁻¹ := by group
    _ = 1 := by rw [hxx, hxx']; group

omit [Finite G]
  hN in
theorem conj_involution_eq {x j : G} (hxx : x * x = 1) :
    j * x * j⁻¹ = x * (x * j * x⁻¹ * j⁻¹) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  calc j * x * j⁻¹ = j * x⁻¹ * j⁻¹ := by rw [hxi]
    _ = (x * x) * j * x⁻¹ * j⁻¹ := by rw [hxx, one_mul]
    _ = x * (x * j * x⁻¹ * j⁻¹) := by group

theorem mul_self_eq_one_iff_q_eq_zero (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {g : G} (hg : g ∈ J z) {w : V} (hw : spinVecToV h P w = QuotientV.pi z ⟨g, hg⟩) :
    g * g = 1 ↔ q w = 0 := by
  rw [← qVZMod_spinVecToV_eq_q D h P hP, hw, qVZMod_eq_zero_iff]
  constructor
  · intro hgg
    apply Subtype.ext
    rw [qV_pi_coe, Subgroup.coe_one]
    simpa [pow_two] using hgg
  · intro hq
    have h1 := congrArg Subtype.val hq
    rw [qV_pi_coe, Subgroup.coe_one] at h1
    simpa [pow_two] using h1

theorem exists_delta_of_spinFixes (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hρq : qH D ρ = xabRho)
    {x : G} (hxH : x ∈ H z) (hxq : qH D ⟨x, hxH⟩ = xabX) {m : V} (hm : SpinFixes xabRho m) :
    ∃ j : G, j ∈ J z ∧ (ρ : G) * j = j * (ρ : G) ∧
      ∃ hg : x * j * x⁻¹ * j⁻¹ ∈ J z, QuotientV.pi z ⟨x * j * x⁻¹ * j⁻¹, hg⟩ =
        spinVecToV h P (m + ((rhoA xabX : GL8) : Mat8) *ᵥ m) := by
  have hv : conjV h ρ (spinVecToV h P m) = spinVecToV h P m :=
    (conjV_fixed_iff_spinFixes D h P hP ρ m).2 (by rw [hρq]; exact hm)
  obtain ⟨j, hj, hρj, hπj⟩ := exists_mem_J_centralizer_of_fixed h hZ hρ3 hv
  refine ⟨j, hj, ?_, ?_⟩
  · calc (ρ : G) * j = ((ρ : G) * j * (ρ : G)⁻¹) * (ρ : G) := by group
      _ = j * (ρ : G) := by rw [hρj]
  · have hxjx : x * j * x⁻¹ ∈ J z := H_conj_mem_J (⟨x, hxH⟩ : ↥(H z)) hj
    have hg : x * j * x⁻¹ * j⁻¹ ∈ J z := (J z).mul_mem hxjx ((J z).inv_mem hj)
    refine ⟨hg, ?_⟩
    have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
      have := QuotientV.pow_two_eq_one_V h v
      rwa [pow_two] at this
    have hinv : ∀ v : QuotientV.V z, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
    have h1 : (⟨x * j * x⁻¹ * j⁻¹, hg⟩ : J z) = ⟨x * j * x⁻¹, hxjx⟩ * ⟨j, hj⟩⁻¹ := rfl
    have h2 : conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨x * j * x⁻¹, hxjx⟩ :=
      conjV_pi_conj h ⟨x, hxH⟩ hj
    rw [h1, map_mul, map_inv, ← h2, hπj, conjV_spinVecToV D h P hP, hxq, hinv,
      ← spinVecToV_add, add_comm]

theorem commute_of_fixed_classes (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {x : G} (hxH : x ∈ H z) (hxq : qH D ⟨x, hxH⟩ = xabX) {g a : G} (hg : g ∈ J z) (ha : a ∈ J z)
    (hgf : conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨g, hg⟩) = QuotientV.pi z ⟨g, hg⟩)
    (haf : conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨a, ha⟩) = QuotientV.pi z ⟨a, ha⟩) :
    g * a = a * g := by
  obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨g, hg⟩)
  obtain ⟨w', hw'⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨a, ha⟩)
  have hw1 : SpinFixes xabX w := by
    have := (conjV_fixed_iff_spinFixes D h P hP ⟨x, hxH⟩ w).1 (by rw [hw]; exact hgf)
    rwa [hxq] at this
  have hw2 : SpinFixes xabX w' := by
    have := (conjV_fixed_iff_spinFixes D h P hP ⟨x, hxH⟩ w').1 (by rw [hw']; exact haf)
    rwa [hxq] at this
  exact commute_of_b_eq_zero D h P hP hg ha hw hw' (xabX_isotropic w w' hw1 hw2)

omit
  hN in
theorem conjV_pi_fixed_of_inv (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z) {g : G}
    (hg : g ∈ J z) (hxg : x * g * x⁻¹ = g⁻¹) :
    conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨g, hg⟩) = QuotientV.pi z ⟨g, hg⟩ := by
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  have hinv : ∀ v : QuotientV.V z, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have h1 : conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨g, hg⟩) =
      QuotientV.pi z ⟨x * g * x⁻¹, H_conj_mem_J (⟨x, hxH⟩ : ↥(H z)) hg⟩ :=
    conjV_pi_conj h ⟨x, hxH⟩ hg
  rw [h1]
  have h2 : (⟨x * g * x⁻¹, H_conj_mem_J (⟨x, hxH⟩ : ↥(H z)) hg⟩ : J z) = ⟨g, hg⟩⁻¹ :=
    Subtype.ext hxg
  rw [h2, map_inv, hinv]

theorem exists_fusion_elements_of_class_v (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hρq : qH D ρ = xabRho)
    {x : G} (hxH : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxq : qH D ⟨x, hxH⟩ = xabX) :
    ∃ g₁ j₂ c : G, g₁ ∈ J z ∧ j₂ ∈ J z ∧ c ∈ J z ∧
      (ρ : G) * g₁ = g₁ * (ρ : G) ∧ (ρ : G) * j₂ = j₂ * (ρ : G) ∧ (ρ : G) * c = c * (ρ : G) ∧
      g₁ * g₁ = z ∧ c * c = 1 ∧ c ∉ centerIn (J z) ∧ x * g₁ * x⁻¹ = g₁⁻¹ ∧ x * c = c * x ∧
      g₁ * x * g₁⁻¹ = x * z ∧ j₂ * x * j₂⁻¹ = x * c := by
  have hz2 : orderOf z = 2 := h.1
  obtain ⟨mm₁, hmm₁, hq₁⟩ := exists_nonsingular_image
  obtain ⟨mm₂, hmm₂, hne₂, hq₂⟩ := exists_singular_image
  have hlt : ∀ mm ∈ wZero, mm < 256 := fun mm hmm => by
    simp only [wZero, List.mem_filter, List.mem_range] at hmm
    exact hmm.1
  have hb₁ : bitmask (vecOfNat mm₁) = mm₁ := bitmask_vecOfNat mm₁ (hlt mm₁ hmm₁)
  have hb₂ : bitmask (vecOfNat mm₂) = mm₂ := bitmask_vecOfNat mm₂ (hlt mm₂ hmm₂)
  have hfix₁ : SpinFixes xabRho (vecOfNat mm₁) :=
    (mem_wZero_iff _).1 (by rw [hb₁]; exact hmm₁)
  have hfix₂ : SpinFixes xabRho (vecOfNat mm₂) :=
    (mem_wZero_iff _).1 (by rw [hb₂]; exact hmm₂)
  have hq₁' : q (vecOfNat mm₁ + ((rhoA xabX : GL8) : Mat8) *ᵥ vecOfNat mm₁) ≠ 0 := by
    rw [Ne, q_eq_zero_iff, bitmask_add_xabX_mulVec, hb₁]
    exact hq₁
  have hq₂' : q (vecOfNat mm₂ + ((rhoA xabX : GL8) : Mat8) *ᵥ vecOfNat mm₂) = 0 := by
    rw [q_eq_zero_iff, bitmask_add_xabX_mulVec, hb₂]
    exact hq₂
  have hne₂' : vecOfNat mm₂ + ((rhoA xabX : GL8) : Mat8) *ᵥ vecOfNat mm₂ ≠ 0 := fun h0 => by
    have h1 := bitmask_add_xabX_mulVec (vecOfNat mm₂)
    rw [h0, bitmask_zero, hb₂] at h1
    exact hne₂ h1.symm
  obtain ⟨j₁, hj₁, hρj₁, hg₁, hπg₁⟩ := exists_delta_of_spinFixes D h hZ P hP hρ3 hρq hxH hxq hfix₁
  obtain ⟨j₂, hj₂, hρj₂, hc, hπc⟩ := exists_delta_of_spinFixes D h hZ P hP hρ3 hρq hxH hxq hfix₂
  have hρx : Commute (ρ : G) x := (mem_centralizer_singleton_iff.mp hxρ).symm
  have hρg : (ρ : G) * (x * j₁ * x⁻¹ * j₁⁻¹) = (x * j₁ * x⁻¹ * j₁⁻¹) * (ρ : G) :=
    (((hρx.mul_right (show Commute (ρ : G) j₁ from hρj₁)).mul_right hρx.inv_right).mul_right
      (show Commute (ρ : G) j₁ from hρj₁).inv_right).eq
  have hρc : (ρ : G) * (x * j₂ * x⁻¹ * j₂⁻¹) = (x * j₂ * x⁻¹ * j₂⁻¹) * (ρ : G) :=
    (((hρx.mul_right (show Commute (ρ : G) j₂ from hρj₂)).mul_right hρx.inv_right).mul_right
      (show Commute (ρ : G) j₂ from hρj₂).inv_right).eq
  have hgg : (x * j₁ * x⁻¹ * j₁⁻¹) * (x * j₁ * x⁻¹ * j₁⁻¹) = z := by
    have hne1 : ¬ (x * j₁ * x⁻¹ * j₁⁻¹) * (x * j₁ * x⁻¹ * j₁⁻¹) = 1 := fun hgg =>
      hq₁' ((mul_self_eq_one_iff_q_eq_zero D h P hP hg₁ hπg₁.symm).1 hgg)
    exact (CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2
      (sq_mem_zpowers_z h hg₁)).resolve_left hne1
  have hcc : (x * j₂ * x⁻¹ * j₂⁻¹) * (x * j₂ * x⁻¹ * j₂⁻¹) = 1 :=
    (mul_self_eq_one_iff_q_eq_zero D h P hP hc hπc.symm).2 hq₂'
  have hcZ : x * j₂ * x⁻¹ * j₂⁻¹ ∉ centerIn (J z) := fun hcZ =>
    hne₂' (spinVecToV_injective h P (by
      rw [← hπc, (pi_eq_one_iff_mem_centerIn hc).2 hcZ, ← spinVecToV_zero h P]))
  have hxg : x * (x * j₁ * x⁻¹ * j₁⁻¹) * x⁻¹ = (x * j₁ * x⁻¹ * j₁⁻¹)⁻¹ :=
    conj_commutator_eq_inv_of_mul_self hxx
  have hxc' : x * (x * j₂ * x⁻¹ * j₂⁻¹) * x⁻¹ = (x * j₂ * x⁻¹ * j₂⁻¹)⁻¹ :=
    conj_commutator_eq_inv_of_mul_self hxx
  have hcinv : (x * j₂ * x⁻¹ * j₂⁻¹)⁻¹ = x * j₂ * x⁻¹ * j₂⁻¹ := inv_eq_of_mul_eq_one_right hcc
  refine ⟨x * j₁ * x⁻¹ * j₁⁻¹, j₂, x * j₂ * x⁻¹ * j₂⁻¹, hg₁, hj₂, hc, hρg, hρj₂, hρc, hgg, hcc,
    hcZ, hxg, ?_, ?_, conj_involution_eq hxx⟩
  · calc x * (x * j₂ * x⁻¹ * j₂⁻¹) = (x * (x * j₂ * x⁻¹ * j₂⁻¹) * x⁻¹) * x := by group
      _ = (x * j₂ * x⁻¹ * j₂⁻¹) * x := by rw [hxc', hcinv]
  · rw [conj_involution_eq hxx, hxg]
    congr 1
    calc (x * j₁ * x⁻¹ * j₁⁻¹)⁻¹ * (x * j₁ * x⁻¹ * j₁⁻¹)⁻¹
        = ((x * j₁ * x⁻¹ * j₁⁻¹) * (x * j₁ * x⁻¹ * j₁⁻¹))⁻¹ := by group
      _ = z := by rw [hgg]; exact inv_eq_of_mul_eq_one_right (centerIn_J_sq h (z_mem_centerIn_J h))

theorem exists_spin_vector_of_commute (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρq : qH D ρ = xabRho) {x : G} (hxH : x ∈ H z) (hxq : qH D ⟨x, hxH⟩ = xabX)
    {a : G} (haJ : a ∈ J z) (haρ : (ρ : G) * a = a * (ρ : G)) (hax : x * a = a * x)
    (haa : a * a = 1) :
    ∃ w : V, spinVecToV h P w = QuotientV.pi z ⟨a, haJ⟩ ∧ SpinFixes xabRho w ∧
      SpinFixes xabX w ∧ q w = 0 := by
  obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨a, haJ⟩)
  refine ⟨w, hw, ?_, ?_, q_eq_zero_of_mul_self_eq_one D h P hP haJ haa hw⟩
  · have := (conjV_fixed_iff_spinFixes D h P hP ρ w).1
      (by rw [hw]; exact conjV_pi_eq_of_commute h haJ haρ)
    rwa [hρq] at this
  · have := (conjV_fixed_iff_spinFixes D h P hP ⟨x, hxH⟩ w).1
      (by rw [hw]; exact conjV_pi_eq_of_commute h haJ hax)
    rwa [hxq] at this

theorem mem_closure_or_mul_mem_closure (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρq : qH D ρ = xabRho) {x : G} (hxH : x ∈ H z) (hxq : qH D ⟨x, hxH⟩ = xabX)
    {c : G} (hcJ : c ∈ J z) (hcρ : (ρ : G) * c = c * (ρ : G)) (hcc : c * c = 1)
    (hcZ : c ∉ centerIn (J z)) (hxc : x * c = c * x) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) {a : G} (haJ : a ∈ J z)
    (haρ : (ρ : G) * a = a * (ρ : G)) (hax : x * a = a * x) (haa : a * a = 1) :
    a ∈ Subgroup.closure ({z, c} : Set G) ∨ z₁ * a ∈ Subgroup.closure ({z, c} : Set G) := by
  have hzB : z ∈ Subgroup.closure ({z, c} : Set G) := Subgroup.subset_closure (by simp)
  have hcB : c ∈ Subgroup.closure ({z, c} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm₁ : ∀ g ∈ J z, z₁ * g = g * z₁ := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hz₁.2 g hg).symm
  have hz₁z₁ : z₁ * z₁ = 1 := centerIn_J_sq h hz₁
  obtain ⟨wc, hwc, hcρ', hcx', hqc⟩ := exists_spin_vector_of_commute D h P hP hρq hxH hxq hcJ hcρ
    hxc hcc
  obtain ⟨wa, hwa, haρ', hax', hqa⟩ := exists_spin_vector_of_commute D h P hP hρq hxH hxq haJ haρ
    hax haa
  have hwc0 : wc ≠ 0 := fun h0 => by
    apply hcZ
    refine (pi_eq_one_iff_mem_centerIn hcJ).1 ?_
    rw [← hwc, h0, spinVecToV_zero]
  have hbit : ∀ w : V, w ≠ 0 → bitmask w ≠ 0 := fun w hw h0 =>
    hw (bitmask_injective (by rw [h0, bitmask_zero]))
  by_cases hwa0 : wa = 0
  · have haZ : a ∈ centerIn (J z) := by
      refine (pi_eq_one_iff_mem_centerIn haJ).1 ?_
      rw [← hwa, hwa0, spinVecToV_zero]
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).1 haZ with rfl | rfl | rfl | rfl
    · exact Or.inl (one_mem _)
    · exact Or.inl hzB
    · right
      rw [hz₁z₁]
      exact one_mem _
    · right
      have hzz₁ : z₁ * z = z * z₁ := hcomm₁ z (z_mem_J h)
      have e : z₁ * (z * z₁) = z := by
        calc z₁ * (z * z₁) = z * (z₁ * z₁) := by rw [← mul_assoc, hzz₁, mul_assoc]
          _ = z := by rw [hz₁z₁, mul_one]
      rw [e]
      exact hzB
  · have hwac : wa = wc := by
      apply bitmask_injective
      refine singular_unique _ ((mem_wZero_iff wa).2 haρ') ((mem_fixX_iff wa).2 hax') _
        ((mem_wZero_iff wc).2 hcρ') ((mem_fixX_iff wc).2 hcx')
        ((q_eq_zero_iff wa).1 hqa) ((q_eq_zero_iff wc).1 hqc) (hbit wa hwa0) (hbit wc hwc0)
    have hpi : QuotientV.pi z ⟨a, haJ⟩ = QuotientV.pi z ⟨c, hcJ⟩ := by
      rw [← hwa, ← hwc, hwac]
    have heJ : c⁻¹ * a ∈ J z := (J z).mul_mem ((J z).inv_mem hcJ) haJ
    have heZ : c⁻¹ * a ∈ centerIn (J z) := by
      refine (pi_eq_one_iff_mem_centerIn heJ).1 ?_
      have : (⟨c⁻¹ * a, heJ⟩ : J z) = ⟨c, hcJ⟩⁻¹ * ⟨a, haJ⟩ := rfl
      rw [this, map_mul, map_inv, hpi, inv_mul_cancel]
    have hca : a = c * (c⁻¹ * a) := by group
    have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.mp
      (z_centralizes_J h) c hcJ).symm
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).1 heZ with he | he | he | he
    · left
      rw [hca, he, mul_one]
      exact hcB
    · left
      rw [hca, he, ← hzc]
      exact Subgroup.mul_mem _ hzB hcB
    · right
      rw [hca, he]
      have e : z₁ * (c * z₁) = c := by
        calc z₁ * (c * z₁) = c * (z₁ * z₁) := by rw [← mul_assoc, hcomm₁ c hcJ, mul_assoc]
          _ = c := by rw [hz₁z₁, mul_one]
      rw [e]
      exact hcB
    · right
      rw [hca, he]
      have hzz₁ : z₁ * z = z * z₁ := hcomm₁ z (z_mem_J h)
      have e : z₁ * (c * (z * z₁)) = z * c := by
        calc z₁ * (c * (z * z₁)) = (z₁ * c) * (z * z₁) := by rw [mul_assoc]
          _ = (c * z₁) * (z * z₁) := by rw [hcomm₁ c hcJ]
          _ = c * (z₁ * z) * z₁ := by group
          _ = c * (z * z₁) * z₁ := by rw [hzz₁]
          _ = c * z * (z₁ * z₁) := by group
          _ = z * c := by rw [hz₁z₁, mul_one, hzc]
      rw [e]
      exact Subgroup.mul_mem _ hzB hcB

theorem exists_fusion_conj (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} {x : G} (hxH : x ∈ H z) (hxq : qH D ⟨x, hxH⟩ = xabX)
    {g₁ j₂ c : G} (hg₁J : g₁ ∈ J z) (hj₂J : j₂ ∈ J z) (hcJ : c ∈ J z)
    (hρg₁ : (ρ : G) * g₁ = g₁ * (ρ : G)) (hρj₂ : (ρ : G) * j₂ = j₂ * (ρ : G))
    (hxg₁ : x * g₁ * x⁻¹ = g₁⁻¹) (hxc : x * c = c * x)
    (hg₁x : g₁ * x * g₁⁻¹ = x * z) (hj₂x : j₂ * x * j₂⁻¹ = x * c)
    {a : G} (haJ : a ∈ J z) (hax : x * a = a * x) (hac : c * a = a * c) :
    (∃ y ∈ J z ⊓ centralizer ({(ρ : G)} : Set G), y * (x * a) * y⁻¹ = x * (a * z)) ∧
    (∃ y ∈ J z ⊓ centralizer ({(ρ : G)} : Set G), y * (x * a) * y⁻¹ = x * (a * c)) ∧
    (∃ y ∈ J z ⊓ centralizer ({(ρ : G)} : Set G), y * (x * a) * y⁻¹ = x * (a * (z * c))) := by
  have hz2 : orderOf z = 2 := h.1
  have hzz : z * z = 1 := centerIn_J_sq h (z_mem_centerIn_J h)
  have hzJ : ∀ g ∈ J z, z * g = g * z := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) g hg).symm
  have hg₁a : g₁ * a = a * g₁ := commute_of_fixed_classes D h P hP hxH hxq hg₁J haJ
    (conjV_pi_fixed_of_inv h hxH hg₁J hxg₁) (conjV_pi_eq_of_commute h haJ hax)
  have hg₁c : g₁ * c = c * g₁ := commute_of_fixed_classes D h P hP hxH hxq hg₁J hcJ
    (conjV_pi_fixed_of_inv h hxH hg₁J hxg₁) (conjV_pi_eq_of_commute h hcJ hxc)
  have hconj_a : g₁ * a * g₁⁻¹ = a := by rw [hg₁a]; group
  have hconj_c : g₁ * c * g₁⁻¹ = c := by rw [hg₁c]; group
  have hconj_z : g₁ * z * g₁⁻¹ = z := by rw [← hzJ g₁ hg₁J]; group
  have hρmem₁ : g₁ ∈ J z ⊓ centralizer ({(ρ : G)} : Set G) :=
    ⟨hg₁J, mem_centralizer_singleton_iff.mpr hρg₁.symm⟩
  have hρmem₂ : j₂ ∈ J z ⊓ centralizer ({(ρ : G)} : Set G) :=
    ⟨hj₂J, mem_centralizer_singleton_iff.mpr hρj₂.symm⟩
  have hρmem₃ : g₁ * j₂ ∈ J z ⊓ centralizer ({(ρ : G)} : Set G) :=
    (J z ⊓ centralizer ({(ρ : G)} : Set G)).mul_mem hρmem₁ hρmem₂
  have hu : j₂ * a * j₂⁻¹ * a⁻¹ ∈ Subgroup.zpowers z := by
    have := commutator_mem_zpowers_z h hj₂J haJ
    rwa [commutatorElement_def] at this
  have hE : ∀ u : G, u = j₂ * a * j₂⁻¹ * a⁻¹ → u * a = j₂ * a * j₂⁻¹ := fun u hu' => by
    rw [hu']; group
  have hy₂ : ∀ u : G, u = j₂ * a * j₂⁻¹ * a⁻¹ → u ∈ Subgroup.zpowers z →
      j₂ * (x * a) * j₂⁻¹ = x * (a * (c * u)) := by
    intro u hu' huz
    have huJ : ∀ g ∈ J z, u * g = g * u := fun g hg =>
      (Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_J h huz) g hg).symm
    calc j₂ * (x * a) * j₂⁻¹ = (j₂ * x * j₂⁻¹) * (j₂ * a * j₂⁻¹) := by group
      _ = (x * c) * (u * a) := by rw [hj₂x, hE u hu']
      _ = x * (c * (u * a)) := by rw [mul_assoc]
      _ = x * (c * (a * u)) := by rw [huJ a haJ]
      _ = x * ((c * a) * u) := by rw [← mul_assoc c a u]
      _ = x * ((a * c) * u) := by rw [hac]
      _ = x * (a * (c * u)) := by rw [mul_assoc a c u]
  have hy₁ : g₁ * (x * a) * g₁⁻¹ = x * (a * z) := by
    calc g₁ * (x * a) * g₁⁻¹ = (g₁ * x * g₁⁻¹) * (g₁ * a * g₁⁻¹) := by group
      _ = (x * z) * a := by rw [hg₁x, hconj_a]
      _ = x * (z * a) := by rw [mul_assoc]
      _ = x * (a * z) := by rw [hzJ a haJ]
  have hy₃ : ∀ b : G, g₁ * (x * (a * b)) * g₁⁻¹ = x * (a * (z * (g₁ * b * g₁⁻¹))) := by
    intro b
    calc g₁ * (x * (a * b)) * g₁⁻¹ = (g₁ * x * g₁⁻¹) * (g₁ * a * g₁⁻¹) * (g₁ * b * g₁⁻¹) := by
          group
      _ = (x * z) * a * (g₁ * b * g₁⁻¹) := by rw [hg₁x, hconj_a]
      _ = x * (a * (z * (g₁ * b * g₁⁻¹))) := by
          rw [mul_assoc x z a, hzJ a haJ]; group
  rcases (CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 hu) with hu1 | huz
  · have e2 := hy₂ _ rfl hu
    rw [hu1, mul_one] at e2
    refine ⟨⟨g₁, hρmem₁, hy₁⟩, ⟨j₂, hρmem₂, e2⟩, ⟨g₁ * j₂, hρmem₃, ?_⟩⟩
    have e3 := hy₃ c
    rw [hconj_c] at e3
    calc g₁ * j₂ * (x * a) * (g₁ * j₂)⁻¹ = g₁ * (j₂ * (x * a) * j₂⁻¹) * g₁⁻¹ := by group
      _ = x * (a * (z * c)) := by rw [e2]; exact e3
  · have e2 := hy₂ _ rfl (by rw [huz]; exact Subgroup.mem_zpowers z)
    rw [huz] at e2
    have hcz : c * z = z * c := (hzJ c hcJ).symm
    rw [hcz] at e2
    refine ⟨⟨g₁, hρmem₁, hy₁⟩, ⟨g₁ * j₂, hρmem₃, ?_⟩, ⟨j₂, hρmem₂, e2⟩⟩
    have e3 := hy₃ (z * c)
    have e4 : g₁ * (z * c) * g₁⁻¹ = z * c := by
      calc g₁ * (z * c) * g₁⁻¹ = (g₁ * z * g₁⁻¹) * (g₁ * c * g₁⁻¹) := by group
        _ = z * c := by rw [hconj_z, hconj_c]
    rw [e4] at e3
    calc g₁ * j₂ * (x * a) * (g₁ * j₂)⁻¹ = g₁ * (j₂ * (x * a) * j₂⁻¹) * g₁⁻¹ := by group
      _ = x * (a * (z * (z * c))) := by rw [e2]; exact e3
      _ = x * (a * c) := by
          rw [← mul_assoc z z c, hzz, one_mul]

omit
  hN in
theorem J_inf_centralizer_inf_le_isSylowOf (h : Tim79a.ParrottHyp z) {ρ x : G} {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    J z ⊓ centralizer ({ρ} : Set G) ⊓ centralizer ({x} : Set G) ≤ X := by
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine le_isSylowOf_of_isPGroup_of_le_normalizer hX
    (fun j hj => mem_inf.mpr ⟨mem_inf.mpr ⟨hj.1.2, J_le_H hj.1.1⟩, hj.2⟩) ?_
    (isPGroup_J h).to_inf_left.to_inf_left
  have key : ∀ c ∈ centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G),
      ∀ j ∈ J z ⊓ centralizer ({ρ} : Set G) ⊓ centralizer ({x} : Set G),
      c * j * c⁻¹ ∈ J z ⊓ centralizer ({ρ} : Set G) ⊓ centralizer ({x} : Set G) := by
    intro c hc j hj
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1.2) j).mp hj.1.1, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have hcσ : Commute c ρ := mem_centralizer_singleton_iff.mp hc.1.1
      have hjσ : Commute j ρ := mem_centralizer_singleton_iff.mp hj.1.2
      exact ((hcσ.mul_left hjσ).mul_left hcσ.inv_left).eq
    · rw [mem_centralizer_singleton_iff]
      have hcσ : Commute c x := mem_centralizer_singleton_iff.mp hc.2
      have hjσ : Commute j x := mem_centralizer_singleton_iff.mp hj.2
      exact ((hcσ.mul_left hjσ).mul_left hcσ.inv_left).eq
  intro c hc
  rw [mem_normalizer_iff]
  intro j
  refine ⟨key c hc j, fun hj => ?_⟩
  have h1 := key c⁻¹ (inv_mem hc) _ hj
  simpa [mul_assoc] using h1

theorem exists_fusion_subgroup_of_class_v (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hρq : qH D ρ = xabRho)
    {x : G} (hxH : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxq : qH D ⟨x, hxH⟩ = xabX) {X K : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G)))
    (hK : ∀ k : G, k ∈ K ↔ k ∈ X ∧ k * k = 1) :
    ∃ B : Subgroup G, B ≤ K ⊓ J z ∧ z ∈ B ∧ 2 < Nat.card B ∧
      (∀ a ∈ K ⊓ J z, a ∉ B → ∀ a' ∈ K ⊓ J z, a' ∉ B → a * a' ∈ B) ∧
      ∀ a ∈ K ⊓ J z, ∀ b ∈ B, ∃ y ∈ J z ⊓ centralizer ({(ρ : G)} : Set G),
        y * (x * a) * y⁻¹ = x * (a * b) := by
  have hz2 : orderOf z = 2 := h.1
  have hzz : z * z = 1 := centerIn_J_sq h (z_mem_centerIn_J h)
  obtain ⟨g₁, j₂, c, hg₁J, hj₂J, hcJ, hρg₁, hρj₂, hρc, hg₁g₁, hcc, hcZ, hxg₁, hxc, hg₁x, hj₂x⟩ :=
    exists_fusion_elements_of_class_v D h hZ P hP hρ3 hρq hxH hxρ hxx hxq
  obtain ⟨z₁, hZeq, hz₁z, hz₁2⟩ := exists_z1 h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hZeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  have hz₁z₁ : z₁ * z₁ = 1 := centerIn_J_sq h hz₁
  have hcomm₁ : ∀ g ∈ J z, z₁ * g = g * z₁ := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hz₁.2 g hg).symm
  have hV : fixDimV h ⟨x, hxH⟩ = 4 := xab_fixDimV D h P hP hxH hxq
  have hZleX := centerIn_J_le_of_isSylowOf_centralizer_inf h hZ ρ.2 hxH hX
  have hcX : c ∈ X := J_inf_centralizer_inf_le_isSylowOf h hX
    ⟨⟨hcJ, mem_centralizer_singleton_iff.mpr hρc.symm⟩, mem_centralizer_singleton_iff.mpr hxc.symm⟩
  have hzK : z ∈ K := (hK z).2 ⟨hZleX (z_mem_centerIn_J h), hzz⟩
  have hcK : c ∈ K := (hK c).2 ⟨hcX, hcc⟩
  have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) c hcJ).symm
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hc1 : c ≠ 1 := fun h1 => hcZ (by rw [h1]; exact (centerIn (J z)).one_mem)
  have hcz : c ≠ z := fun h1 => hcZ (by rw [h1]; exact z_mem_centerIn_J h)
  have hcard : Nat.card (Subgroup.closure ({z, c} : Set G)) = 4 :=
    CFSG.GroupTheory.card_closure_pair_of_involutions hzz hcc hzc hz1 hc1 hcz
  have hzB : z ∈ Subgroup.closure ({z, c} : Set G) := Subgroup.subset_closure (by simp)
  have hBle : Subgroup.closure ({z, c} : Set G) ≤ K ⊓ J z := by
    rw [Subgroup.closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact ⟨hzK, z_mem_J h⟩
    · exact ⟨hcK, hcJ⟩
  have hAfacts : ∀ a ∈ K ⊓ J z, (ρ : G) * a = a * (ρ : G) ∧ x * a = a * x ∧ a * a = 1 := by
    intro a ha
    obtain ⟨haX, haa⟩ := (hK a).1 ha.1
    have hamem := hX.le haX
    exact ⟨(mem_centralizer_singleton_iff.mp hamem.1.1).symm,
      (mem_centralizer_singleton_iff.mp hamem.2).symm, haa⟩
  have hA : ∀ a ∈ K ⊓ J z, a ∈ Subgroup.closure ({z, c} : Set G) ∨
      z₁ * a ∈ Subgroup.closure ({z, c} : Set G) := by
    intro a ha
    obtain ⟨haρ, hax, haa⟩ := hAfacts a ha
    exact mem_closure_or_mul_mem_closure D h P hP hρq hxH hxq hcJ hρc hcc hcZ hxc hz₁ hz₁z hz₁2
      ha.2 haρ hax haa
  refine ⟨Subgroup.closure ({z, c} : Set G), hBle, hzB, by rw [hcard]; norm_num, ?_, ?_⟩
  · intro a ha hanB a' ha' ha'nB
    have h1 := (hA a ha).resolve_left hanB
    have h2 := (hA a' ha').resolve_left ha'nB
    have e : a * a' = (z₁ * a) * (z₁ * a') := by
      calc a * a' = (z₁ * z₁) * a * a' := by rw [hz₁z₁, one_mul]
        _ = z₁ * (z₁ * a) * a' := by rw [mul_assoc z₁ z₁ a]
        _ = z₁ * (a * z₁) * a' := by rw [hcomm₁ a ha.2]
        _ = (z₁ * a) * (z₁ * a') := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  · intro a ha b hb
    obtain ⟨haρ, hax, haa⟩ := hAfacts a ha
    have hac : c * a = a * c :=
      commute_of_commute_of_fixDimV_eq_four h hZ hxH hxx hV hcJ ha.2 hxc.symm hax.symm
    obtain ⟨Sz, Sc, Szc⟩ := exists_fusion_conj D h P hP hxH hxq hg₁J hj₂J hcJ hρg₁ hρj₂ hxg₁ hxc
      hg₁x hj₂x ha.2 hax hac
    rcases mem_closure_pair_four hzz hcc hzc hb with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, by simp⟩
    · exact Sz
    · exact Sc
    · exact Szc

end Fusion

end CFSG.RankThree.GF2n.Parrott
