module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseATheta
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAIndex
import CFSG.Quasithin.Recognition.Stroth.Str83G4CP

import CFSG.Quasithin.Background.HZ82Base
import CFSG.Quasithin.Recognition.Stroth.Str83G4S1
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift
import CFSG.CGT.Foote81L6.OddQuot
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFact1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_Z_commute_Qy (v : f112Gamma L1 L2 S) {z y : (f112Amalgam L1 L2 S).Ghat}
    (hz : z ∈ caseAZ v) (hy : y ∈ CosetGeom.Qy v) : z * y = y * z := by
  have hz' : z ∈ omegaOneCenterOf (CosetGeom.Qy v) := hz
  have hcent : z ∈ Subgroup.centralizer (CosetGeom.Qy v : Set (f112Amalgam L1 L2 S).Ghat) :=
    (A4.centerOf_le_centralizer (CosetGeom.Qy v))
      ((A4.omegaOneCenterOf_le_centerOf (CosetGeom.Qy v)) hz')
  exact (Subgroup.mem_centralizer_iff.mp hcent y hy).symm

private theorem v1a_mem_pCoreOf_bigB_of_two_elem {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {t : G} (ht : t ∈ bigB L1 L2 S)
    (h2 : ∃ k, orderOf t = 2 ^ k) : t ∈ CFSG.Open.pCoreOf 2 (bigB L1 L2 S) := by
  obtain ⟨hF, hB, -, -, -, -⟩ := hfr
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S := le_sup_right
  have hSylB : CFSG.QuasithinUnique.IsSylowTwoOf S (bigB L1 L2 S) :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF) hSB hBP
  have hnB : (S.subgroupOf (bigB L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hB
  have htS : t ∈ S := by
    obtain ⟨k, hk⟩ := h2
    have hX : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    exact F7.le_of_normal_sylow hSylB hnB (Subgroup.zpowers_le.mpr ht) hX
      (Subgroup.mem_zpowers t)
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hSB hnB hF.1.h1.pgroup htS

private theorem v1a_mem_caseAS_of_two_elem_base {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {z : (f112Amalgam L1 L2 S).Ghat}
    (hz0 : z ∈ CosetGeom.stab (f112Gamma0 L1 L2 S))
    (hz1 : z ∈ CosetGeom.stab (f112Gamma1 L1 L2 S))
    (h2 : ∃ k, orderOf z = 2 ^ k) :
    z ∈ caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) := by
  have hzH : z ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓
      CosetGeom.stab (f112Gamma1 L1 L2 S) := ⟨hz0, hz1⟩
  have hφ : Set.InjOn (caseATheta L1 L2 S)
      (↑(CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓
        CosetGeom.stab (f112Gamma1 L1 L2 S)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    Set.InjOn.mono Set.inter_subset_left caseATheta_injOn_stab_γ₀
  have htB : caseATheta L1 L2 S z ∈ bigB L1 L2 S := by
    have h := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hzH
    rwa [caseATheta_map_stab_inf hfr] at h
  have ht2 : ∃ k, orderOf (caseATheta L1 L2 S z) = 2 ^ k := by
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, by rw [CFSG.CGT.Foote81L6.orderOf_map_of_injOn (caseATheta L1 L2 S)
      (fun a ha h => hφ ha (Subgroup.one_mem _) (by rw [h, map_one])) hzH, hk]⟩
  have htP : caseATheta L1 L2 S z ∈ CFSG.Open.pCoreOf 2 (bigB L1 L2 S) :=
    v1a_mem_pCoreOf_bigB_of_two_elem hfr htB ht2
  have hmap : (CFSG.Open.pCoreOf 2 (CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓
        CosetGeom.stab (f112Gamma1 L1 L2 S))).map (caseATheta L1 L2 S) =
      CFSG.Open.pCoreOf 2 (bigB L1 L2 S) := by
    let P : Subgroup (f112Amalgam L1 L2 S).Ghat :=
      CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓ CosetGeom.stab (f112Gamma1 L1 L2 S)
    have hP : P = CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓
        CosetGeom.stab (f112Gamma1 L1 L2 S) := rfl
    let ψ : ↥P →* G := (caseATheta L1 L2 S).comp P.subtype
    have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hφ a.2 b.2 h)
    have htop : (⊤ : Subgroup ↥P).map ψ = P.map (caseATheta L1 L2 S) := by
      rw [show ψ = (caseATheta L1 L2 S).comp P.subtype from rfl, ← Subgroup.map_map]
      congr 1
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hpc0 : CFSG.Open.pCoreOf 2 P =
        (CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype := by
      have h := CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 P.subtype
        P.subtype_injective (⊤ : Subgroup ↥P)
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    calc (CFSG.Open.pCoreOf 2 P).map (caseATheta L1 L2 S)
        = ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype).map
            (caseATheta L1 L2 S) := by rw [hpc0]
      _ = (CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥P)).map ψ := by rw [Subgroup.map_map]
      _ = CFSG.Open.pCoreOf 2 ((⊤ : Subgroup ↥P).map ψ) :=
          (CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 ψ hψ
            (⊤ : Subgroup ↥P)).symm
      _ = CFSG.Open.pCoreOf 2 (P.map (caseATheta L1 L2 S)) := by rw [htop]
      _ = CFSG.Open.pCoreOf 2 (bigB L1 L2 S) := by
          rw [hP, caseATheta_map_stab_inf hfr]
  have htMap : caseATheta L1 L2 S z ∈
      (CFSG.Open.pCoreOf 2 (CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓
        CosetGeom.stab (f112Gamma1 L1 L2 S))).map (caseATheta L1 L2 S) := by
    rwa [hmap]
  obtain ⟨x, hxP, hxθ⟩ := Subgroup.mem_map.mp htMap
  have hxH : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓
      CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hxP
  have hxz : x = z := hφ hxH hzH hxθ
  rw [hxz] at hxP
  simpa [caseAS] using hxP

theorem caseA_mem_caseAS_of_two_elem {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {v w : f112Gamma L1 L2 S} (hw : w ∈ CosetGeom.nbrs v)
    {g : (f112Amalgam L1 L2 S).Ghat} (hgv : g ∈ CosetGeom.stab v) (hgw : g ∈ CosetGeom.stab w)
    (h2 : ∃ k, orderOf g = 2 ^ k) : g ∈ caseAS v w := by
  obtain ⟨g₀, hg₀ | hg₀⟩ :=
    CosetGeom.exists_smul_edge (show (f112Amalgam L1 L2 S).graphHat.Adj v w from hw)
  · let z : (f112Amalgam L1 L2 S).Ghat :=
      (g₀ : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g * (g₀ : (f112Amalgam L1 L2 S).Ghat)
    have hz0 : z ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) := by
      have h : g ∈ CosetGeom.stab (g₀ • f112Gamma0 L1 L2 S) := by rw [hg₀.1]; exact hgv
      rw [CosetGeom.stab_smul] at h
      simpa [z] using mem_conjSub.mp h
    have hz1 : z ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := by
      have h : g ∈ CosetGeom.stab (g₀ • f112Gamma1 L1 L2 S) := by rw [hg₀.2]; exact hgw
      rw [CosetGeom.stab_smul] at h
      simpa [z] using mem_conjSub.mp h
    have hz2 : ∃ k, orderOf z = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have hzeq : z = MulAut.conj ((g₀ : (f112Amalgam L1 L2 S).Ghat)⁻¹) g := by
        simp [z, MulAut.conj_apply]
      rw [hzeq, MulEquiv.orderOf_eq (MulAut.conj ((g₀ : (f112Amalgam L1 L2 S).Ghat)⁻¹)) g, hk]
    have hmemz : z ∈ caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) :=
      v1a_mem_caseAS_of_two_elem_base hfr hz0 hz1 hz2
    have hconj : g ∈ conjSub (g₀ : (f112Amalgam L1 L2 S).Ghat)
        (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) :=
      mem_conjSub.mpr (by simpa [z] using hmemz)
    rwa [← caseA_S_smul g₀ (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S), hg₀.1, hg₀.2] at hconj
  · let z : (f112Amalgam L1 L2 S).Ghat :=
      (g₀ : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g * (g₀ : (f112Amalgam L1 L2 S).Ghat)
    have hz0 : z ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) := by
      have h : g ∈ CosetGeom.stab (g₀ • f112Gamma0 L1 L2 S) := by rw [hg₀.1]; exact hgw
      rw [CosetGeom.stab_smul] at h
      simpa [z] using mem_conjSub.mp h
    have hz1 : z ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := by
      have h : g ∈ CosetGeom.stab (g₀ • f112Gamma1 L1 L2 S) := by rw [hg₀.2]; exact hgv
      rw [CosetGeom.stab_smul] at h
      simpa [z] using mem_conjSub.mp h
    have hz2 : ∃ k, orderOf z = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have hzeq : z = MulAut.conj ((g₀ : (f112Amalgam L1 L2 S).Ghat)⁻¹) g := by
        simp [z, MulAut.conj_apply]
      rw [hzeq, MulEquiv.orderOf_eq (MulAut.conj ((g₀ : (f112Amalgam L1 L2 S).Ghat)⁻¹)) g, hk]
    have hmemz : z ∈ caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) :=
      v1a_mem_caseAS_of_two_elem_base hfr hz0 hz1 hz2
    have hconj : g ∈ conjSub (g₀ : (f112Amalgam L1 L2 S).Ghat)
        (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) :=
      mem_conjSub.mpr (by simpa [z] using hmemz)
    have hs : caseAS (g₀ • f112Gamma0 L1 L2 S) (g₀ • f112Gamma1 L1 L2 S) =
        conjSub (g₀ : (f112Amalgam L1 L2 S).Ghat)
          (caseAS (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) :=
      caseA_S_smul g₀ (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)
    rw [hg₀.1, hg₀.2] at hs
    have hwv : g ∈ caseAS w v := by rw [hs]; exact hconj
    rw [caseAS_comm v w]
    exact hwv

theorem caseA_Qy_le_caseAS {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {v w : f112Gamma L1 L2 S} (hw : w ∈ CosetGeom.nbrs v) :
    CosetGeom.Qy v ≤ caseAS v w := by
  have hdist : CosetGeom.dist v w ≤ 1 :=
    (CosetGeom.dist_eq_one_iff_adj.mpr
      (show (f112Amalgam L1 L2 S).graphHat.Adj v w from hw)).le
  have hQH : CosetGeom.Qy v ≤ CosetGeom.stab v ⊓ CosetGeom.stab w := fun y hy =>
    ⟨caseA_Qy_le_stab v hy, CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := v) (δ := w)
      hdist (caseA_Qy_le_ballStab_one hfr v hy)⟩
  haveI : ((CosetGeom.Qy v).subgroupOf (CosetGeom.stab v ⊓ CosetGeom.stab w)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQH]
    exact inf_le_left.trans (caseA_stab_le_normalizer_Qy v)
  have hp : IsPGroup 2 (CosetGeom.Qy v) := by
    unfold CosetGeom.Qy CFSG.Open.pCoreOf
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(CosetGeom.stab v))).map
      (CosetGeom.stab v).subtype
  intro x hx
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hQH inferInstance hp hx

theorem caseA_isElemAbelian_X
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) :
    IsElemAbelian 2 (caseAX α) := by
  obtain ⟨τ, hτadj⟩ := CosetGeom.exists_adj α
  have hτ : CosetGeom.vtype τ = true := by
    have hne := CosetGeom.vtype_ne_of_adj hτadj
    rw [hα] at hne
    cases h : CosetGeom.vtype τ <;> simp_all
  obtain ⟨φ, hinjα, -, -, -, -, -, -, -, -, hmapXα, -, -, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτadj
  have hX : caseAX α ≤ CosetGeom.stab α := caseA_X_le_stab hfr α
  have hS1 : IsElemAbelian 2 (str83X L1 L2 S) :=
    (str83G4S1_of_z2Comm str83G4Z2Comm_holds) G L1 L2 S a hfr
  refine CFSG.AGLEmbedding.isElemAbelian_of_map_injOn φ
    (fun a ha h => hinjα (hX ha) (Subgroup.one_mem _) (by rw [h, map_one])) ?_
  rw [hmapXα]
  exact hS1

theorem caseA_commutator_X_Qy_le_Z
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) :
    ⁅caseAX α, CosetGeom.Qy α⁆ ≤ caseAZ α := by
  obtain ⟨τ, hτadj⟩ := CosetGeom.exists_adj α
  have hτ : CosetGeom.vtype τ = true := by
    have hne := CosetGeom.vtype_ne_of_adj hτadj
    rw [hα] at hne
    cases h : CosetGeom.vtype τ <;> simp_all
  obtain ⟨φ, hinjα, -, -, -, -, hmapQα, -, hmapZα, -, hmapXα, -, -, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτadj
  have hcomm : ⁅caseAX α, CosetGeom.Qy α⁆ ≤ CosetGeom.stab α :=
    (Subgroup.commutator_le_sup _ _).trans
      (sup_le (caseA_X_le_stab hfr α) (caseA_Qy_le_stab α))
  have hZ : caseAZ α ≤ CosetGeom.stab α :=
    (caseA_Z_le_Qy α).trans (caseA_Qy_le_stab α)
  have hle : (⁅caseAX α, CosetGeom.Qy α⁆).map φ ≤ (caseAZ α).map φ := by
    rw [Subgroup.map_commutator, hmapXα, hmapQα, hmapZα]
    exact str83G4_commutator_x_q1_le hfr
  let ψ : ↥(CosetGeom.stab α) →* G := φ.comp (CosetGeom.stab α).subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hHψ : ((⁅caseAX α, CosetGeom.Qy α⁆).subgroupOf (CosetGeom.stab α)).map ψ =
      (⁅caseAX α, CosetGeom.Qy α⁆).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hcomm]
  have hKψ : ((caseAZ α).subgroupOf (CosetGeom.stab α)).map ψ = (caseAZ α).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hZ]
  rw [← hHψ, ← hKψ] at hle
  have hsub := (Subgroup.map_le_map_iff_of_injective hψ).mp hle
  have hmono : ((⁅caseAX α, CosetGeom.Qy α⁆).subgroupOf (CosetGeom.stab α)).map
        (CosetGeom.stab α).subtype ≤
      ((caseAZ α).subgroupOf (CosetGeom.stab α)).map (CosetGeom.stab α).subtype :=
    Subgroup.map_mono hsub
  rwa [Subgroup.map_subgroupOf_eq_of_le hcomm,
    Subgroup.map_subgroupOf_eq_of_le hZ] at hmono

theorem caseA_Z_le_X {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) : caseAZ α ≤ caseAX α := by
  obtain ⟨β, hβ⟩ := CosetGeom.exists_adj α
  exact (caseA_Z_le_Z_of_adj hfr hα hβ).trans
    (le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs α) => caseAZ w) β hβ)

theorem caseA_card_Z_type1
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) :
    Nat.card (caseAZ α) = 2 ^ (2 * a + 1) := by
  obtain ⟨τ, hτadj⟩ := CosetGeom.exists_adj α
  have hτ : CosetGeom.vtype τ = true := by
    have hne := CosetGeom.vtype_ne_of_adj hτadj
    rw [hα] at hne
    cases h : CosetGeom.vtype τ <;> simp_all
  obtain ⟨φ, hinjα, -, -, -, -, -, -, hmapZα, -, -, -, -, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτadj
  have hZ : caseAZ α ≤ CosetGeom.stab α := (caseA_Z_le_Qy α).trans (caseA_Qy_le_stab α)
  let ψ : ↥(CosetGeom.stab α) →* G := φ.comp (CosetGeom.stab α).subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hZψ : ((caseAZ α).subgroupOf (CosetGeom.stab α)).map ψ = (caseAZ α).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hZ]
  have hcard_sub : Nat.card ((caseAZ α).subgroupOf (CosetGeom.stab α)) =
      Nat.card (caseAZ α) := by
    rw [← Subgroup.card_map_of_injective (f := (CosetGeom.stab α).subtype)
      (K := (caseAZ α).subgroupOf (CosetGeom.stab α)) (CosetGeom.stab α).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hZ]
  have hcard : Nat.card ((caseAZ α).map φ) = Nat.card (caseAZ α) := by
    rw [← hZψ, Subgroup.card_map_of_injective hψ, hcard_sub]
  rw [hmapZα] at hcard
  rw [← hcard]
  exact str83G4Z1Card_holds G L1 L2 S a hfr

theorem caseA_relIndex_inf_Qy_le_type1
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false)
    (hτ : τ ∈ CosetGeom.nbrs α) {A : Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hA : A ≤ caseAS α τ) (hsq : ∀ x ∈ A, x * x ∈ CosetGeom.Qy α) :
    (A ⊓ CosetGeom.Qy α).relIndex A ≤ 2 ^ (2 * a + 1) := by
  obtain ⟨φ, hinjα, -, -, -, -, hQyα, -, -, -, -, -, hS, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτ
  have hAstab : A ≤ CosetGeom.stab α := hA.trans (caseAS_le_stab_left α τ)
  have hQstab : CosetGeom.Qy α ≤ CosetGeom.stab α := caseA_Qy_le_stab α
  let ψ : ↥(CosetGeom.stab α) →* G := φ.comp (CosetGeom.stab α).subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hA' : A ⊓ CosetGeom.Qy α ≤ CosetGeom.stab α :=
    (inf_le_left : A ⊓ CosetGeom.Qy α ≤ A).trans hAstab
  have hHψ : ((A ⊓ CosetGeom.Qy α).subgroupOf (CosetGeom.stab α)).map ψ =
      (A ⊓ CosetGeom.Qy α).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hA']
  have hKψ : (A.subgroupOf (CosetGeom.stab α)).map ψ = A.map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hAstab]
  have hrel : ((A ⊓ CosetGeom.Qy α).map φ).relIndex (A.map φ) =
      (A ⊓ CosetGeom.Qy α).relIndex A := by
    rw [← hHψ, ← hKψ,
      Subgroup.relIndex_map_map_of_injective
        ((A ⊓ CosetGeom.Qy α).subgroupOf (CosetGeom.stab α))
        (A.subgroupOf (CosetGeom.stab α)) hψ,
      Subgroup.relIndex_subgroupOf hAstab]
  rw [← hrel]
  have hmapinf : (A ⊓ CosetGeom.Qy α).map φ = A.map φ ⊓ (CosetGeom.Qy α).map φ := by
    refine le_antisymm (le_inf (Subgroup.map_mono inf_le_left)
      (Subgroup.map_mono inf_le_right)) ?_
    rintro y ⟨⟨a, haA, rfl⟩, ⟨q, hqQ, hqa⟩⟩
    have haP : a ∈ CosetGeom.stab α := hAstab haA
    have hqP : q ∈ CosetGeom.stab α := hQstab hqQ
    have haq : a = q := (hinjα hqP haP hqa).symm
    rw [haq] at haA ⊢
    exact Subgroup.mem_map_of_mem φ ⟨haA, hqQ⟩
  rw [hmapinf, hQyα]
  rw [← str83G4_pCoreOf_sup_left hfr]
  refine relIndex_inf_pCoreOf_le (L := L1 ⊔ S) (T := S) (A := A.map φ)
    (q := 2 ^ (2 * a + 1)) (str83G4_isSzU3Quot_sup_left hfr)
    (str83G4_isSylowTwoOf_sup_left hfr) ?_ ?_
  · exact (Subgroup.map_mono hA).trans (le_of_eq hS)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : φ (x * x) ∈ Q1 L1 L2 S := by
      have h1 := Subgroup.mem_map_of_mem φ (hsq x hx)
      rwa [hQyα] at h1
    rw [str83G4_pCoreOf_sup_left hfr]
    simpa [pow_two, map_mul] using hmem

theorem caseA_relIndex_inf_Qy_le_type1_of_involutions
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false)
    (hτ : τ ∈ CosetGeom.nbrs α) {A : Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hA : A ≤ Subgroup.closure {t | t ∈ caseAS α τ ∧ t * t = 1}) :
    (A ⊓ CosetGeom.Qy α).relIndex A ≤ 2 ^ (2 * a + 1) := by
  obtain ⟨φ, hinjα, -, -, -, -, hQyα, -, -, -, -, -, hS, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτ
  obtain ⟨X₀, hX₀mem, -, hX₀rel, hX₀inv⟩ :=
    exists_X0 (L := L1 ⊔ S) (T := S) (q := 2 ^ (2 * a + 1))
      (str83G4_isSzU3Quot_sup_left hfr) (str83G4_isSylowTwoOf_sup_left hfr)
  let X₀' : Subgroup (f112Amalgam L1 L2 S).Ghat := (X₀.comap φ) ⊓ CosetGeom.stab α
  have hX₀'stab : X₀' ≤ CosetGeom.stab α := inf_le_right
  have hmapX₀' : X₀'.map φ = X₀ := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp hx.1
    · intro y hy
      have hyS : y ∈ S := ((hX₀mem y).mp hy).1
      have hyS' : y ∈ (caseAS α τ).map φ := by rw [hS]; exact hyS
      obtain ⟨x, hxτ, hφx⟩ := Subgroup.mem_map.mp hyS'
      refine Subgroup.mem_map.mpr
        ⟨x, ⟨Subgroup.mem_comap.mpr ?_, caseAS_le_stab_left α τ hxτ⟩, hφx⟩
      rw [hφx]; exact hy
  have hgen : {t : (f112Amalgam L1 L2 S).Ghat | t ∈ caseAS α τ ∧ t * t = 1} ⊆
      (X₀' : Set (f112Amalgam L1 L2 S).Ghat) := by
    rintro t ⟨htτ, ht2⟩
    have htS : φ t ∈ S := by
      have h1 := Subgroup.mem_map_of_mem φ htτ
      rwa [hS] at h1
    have ht2' : φ t * φ t = 1 := by rw [← map_mul, ht2, map_one]
    exact ⟨Subgroup.mem_comap.mpr (hX₀inv (φ t) htS ht2'), caseAS_le_stab_left α τ htτ⟩
  have hA' : A ≤ X₀' := hA.trans ((Subgroup.closure_le _).mpr hgen)
  have hrelQ : (CosetGeom.Qy α).relIndex X₀' = 2 ^ (2 * a + 1) := by
    let ψ : ↥(CosetGeom.stab α) →* G := φ.comp (CosetGeom.stab α).subtype
    have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinjα a.2 b.2 h)
    have hQψ : ((CosetGeom.Qy α).subgroupOf (CosetGeom.stab α)).map ψ =
        (CosetGeom.Qy α).map φ := by
      rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
        Subgroup.map_subgroupOf_eq_of_le (caseA_Qy_le_stab α)]
    have hXψ : (X₀'.subgroupOf (CosetGeom.stab α)).map ψ = X₀'.map φ := by
      rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
        Subgroup.map_subgroupOf_eq_of_le hX₀'stab]
    have h1 : ((CosetGeom.Qy α).map φ).relIndex (X₀'.map φ) =
        (CosetGeom.Qy α).relIndex X₀' := by
      rw [← hQψ, ← hXψ,
        Subgroup.relIndex_map_map_of_injective
          ((CosetGeom.Qy α).subgroupOf (CosetGeom.stab α))
          (X₀'.subgroupOf (CosetGeom.stab α)) hψ,
        Subgroup.relIndex_subgroupOf hX₀'stab]
    rw [hQyα, hmapX₀'] at h1
    rw [← h1, ← str83G4_pCoreOf_sup_left hfr]
    exact hX₀rel
  have hne : (CosetGeom.Qy α).relIndex X₀' ≠ 0 := by
    rw [hrelQ]; exact pow_ne_zero _ (by norm_num)
  calc (A ⊓ CosetGeom.Qy α).relIndex A
      = (CosetGeom.Qy α).relIndex A := Subgroup.inf_relIndex_left A (CosetGeom.Qy α)
    _ ≤ (CosetGeom.Qy α).relIndex X₀' := Subgroup.relIndex_le_of_le_right hA' hne
    _ = 2 ^ (2 * a + 1) := hrelQ

theorem caseA_sq_le_relIndex_centralizerMod_X
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hτ : τ ∈ CosetGeom.nbrs α)
    {t : (f112Amalgam L1 L2 S).Ghat} (ht : t ∈ caseAS α τ) (ht2 : t * t = 1)
    (htQ : t ∉ CosetGeom.Qy α) :
    (2 ^ (2 * a + 1)) ^ 2 ≤
      (centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).relIndex (caseAX α) := by
  obtain ⟨φ, hinjα, -, -, -, -, hQyα, -, hZα, -, hXα, -, hS, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτ
  obtain ⟨L, N, hLN⟩ := str83G4_exists_chiefStep hfr
  obtain ⟨hstep, hZ1L, hnotle⟩ := hLN
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hnc : ¬ IsCentralStep (L1 ⊔ S) L N :=
    caseA_not_isCentralStep_of_not_le_centralizerMod hHL hnotle
  have htS : φ t ∈ S := by
    have h1 := Subgroup.mem_map_of_mem φ ht
    rwa [hS] at h1
  have htQ1 : φ t ∉ Q1 L1 L2 S := by
    intro hmem
    have hmem' : φ t ∈ (CosetGeom.Qy α).map φ := by rw [hQyα]; exact hmem
    obtain ⟨q, hq, hqφ⟩ := Subgroup.mem_map.mp hmem'
    have hqstab : q ∈ CosetGeom.stab α := caseA_Qy_le_stab α hq
    have htstab : t ∈ CosetGeom.stab α := caseAS_le_stab_left α τ ht
    have hqt : q = t := hinjα hqstab htstab hqφ
    exact htQ (hqt ▸ hq)
  have htH : φ t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) htS
  have ht2H : φ t * φ t ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [str83G4_pCoreOf_sup_left hfr]
    have h : φ t * φ t = 1 := by rw [← map_mul, ht2, map_one]
    rw [h]; exact (Q1 L1 L2 S).one_mem
  have htOH : φ t ∉ pCoreOf 2 (L1 ⊔ S) := by
    rwa [str83G4_pCoreOf_sup_left hfr]
  have hU : IsPGroup 2 (str83X L1 L2 S) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le (str83X_le_q1 hfr)
  have hUH : str83X L1 L2 S ≤ L1 ⊔ S :=
    (str83X_le_q1 hfr).trans ((str83G4_q1_le_s hfr).trans le_sup_right)
  have hM6 := sq_le_relIndex_centralizerMod (hX := str83G4_isSzU3Quot_sup_left hfr)
    (hU := hU) (hUH := hUH) (hstep := hstep) (hnc := hnc)
    (htH := htH) (ht := ht2H) (htO := htOH)
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans
      (CFSG.Quasithin.SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  have hNH : N ≤ L1 ⊔ S := hstep.1.1.trans hUH
  have hsec := caseA_relIndex_centralizerMod_section_le (Z := Z1 L1 L2 S) (L := L)
    (N := N) (X := str83X L1 L2 S) (u := φ t)
    hZ1L hstep.2.2.1.le hstep.1.1 (hNH.trans hHZ1) (hNH.trans hHL)
    (hHZ1 htH) (hHL htH)
  have hZα_stab : caseAZ α ≤ CosetGeom.stab α :=
    (caseA_Z_le_Qy α).trans (caseA_Qy_le_stab α)
  have hXα_stab : caseAX α ≤ CosetGeom.stab α := caseA_X_le_stab hfr α
  have ht_stab : t ∈ CosetGeom.stab α := caseAS_le_stab_left α τ ht
  have hU_stab : Subgroup.zpowers t ≤ CosetGeom.stab α := Subgroup.zpowers_le.mpr ht_stab
  let ψ : ↥(CosetGeom.stab α) →* G := φ.comp (CosetGeom.stab α).subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hZψ : ((caseAZ α).subgroupOf (CosetGeom.stab α)).map ψ = (caseAZ α).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hZα_stab]
  have hXψ : ((caseAX α).subgroupOf (CosetGeom.stab α)).map ψ = (caseAX α).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hXα_stab]
  have hUψ : ((Subgroup.zpowers t).subgroupOf (CosetGeom.stab α)).map ψ =
      (Subgroup.zpowers t).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hU_stab]
  have hmapCM : (centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).map φ =
      centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S) (Subgroup.zpowers (φ t)) := by
    have hP : (centralizerMod ((caseAZ α).subgroupOf (CosetGeom.stab α))
          ((caseAX α).subgroupOf (CosetGeom.stab α))
          ((Subgroup.zpowers t).subgroupOf (CosetGeom.stab α))).map
          (CosetGeom.stab α).subtype =
        centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t) := by
      rw [CFSG.Quasithin.centralizerMod_map_of_injective
          (CosetGeom.stab α).subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hZα_stab,
        Subgroup.map_subgroupOf_eq_of_le hXα_stab,
        Subgroup.map_subgroupOf_eq_of_le hU_stab]
    calc (centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).map φ
        = ((centralizerMod ((caseAZ α).subgroupOf (CosetGeom.stab α))
              ((caseAX α).subgroupOf (CosetGeom.stab α))
              ((Subgroup.zpowers t).subgroupOf (CosetGeom.stab α))).map
              (CosetGeom.stab α).subtype).map φ := by rw [hP]
      _ = (centralizerMod ((caseAZ α).subgroupOf (CosetGeom.stab α))
              ((caseAX α).subgroupOf (CosetGeom.stab α))
              ((Subgroup.zpowers t).subgroupOf (CosetGeom.stab α))).map ψ := by
          rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, Subgroup.map_map]
      _ = centralizerMod (((caseAZ α).subgroupOf (CosetGeom.stab α)).map ψ)
              (((caseAX α).subgroupOf (CosetGeom.stab α)).map ψ)
              (((Subgroup.zpowers t).subgroupOf (CosetGeom.stab α)).map ψ) :=
          CFSG.Quasithin.centralizerMod_map_of_injective hψ _ _ _
      _ = centralizerMod ((caseAZ α).map φ) ((caseAX α).map φ)
              ((Subgroup.zpowers t).map φ) := by rw [hZψ, hXψ, hUψ]
      _ = centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S) (Subgroup.zpowers (φ t)) := by
          rw [hZα, hXα, MonoidHom.map_zpowers]
  have hCM_stab : centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t) ≤
      CosetGeom.stab α := (centralizerMod_le_left _ _ _).trans hXα_stab
  have hCMψ : ((centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).subgroupOf
        (CosetGeom.stab α)).map ψ =
      (centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).map φ := by
    rw [show ψ = φ.comp (CosetGeom.stab α).subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hCM_stab]
  have hEq : ((centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).map φ).relIndex
        ((caseAX α).map φ) =
      (centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).relIndex (caseAX α) := by
    rw [← hCMψ, ← hXψ,
      Subgroup.relIndex_map_map_of_injective
        ((centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).subgroupOf
          (CosetGeom.stab α))
        ((caseAX α).subgroupOf (CosetGeom.stab α)) hψ,
      Subgroup.relIndex_subgroupOf hXα_stab]
  rw [hmapCM, hXα] at hEq
  calc (2 ^ (2 * a + 1)) ^ 2
      ≤ (centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S)
          (Subgroup.zpowers (φ t))).relIndex (str83X L1 L2 S) := hM6.trans hsec
    _ = (centralizerMod (caseAZ α) (caseAX α) (Subgroup.zpowers t)).relIndex (caseAX α) := hEq

end CFSG.Quasithin.Stroth

end
