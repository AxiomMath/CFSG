module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreAut
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreDelta
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreFix
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreFrame
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFourC
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeEightDpW0
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeTenIIg
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeElevenIWO2H

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_p_eq_three (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) : p = 3 := by
  obtain ⟨n, hn1, hn2⟩ := hc.core.card_nineOmegaIn
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  have hfr := nine3_oddFrame hc hI hρ
  rcases h35 with h3 | h5
  · have hpow : 2 ^ n = 2 := by omega
    rw [hn1, hpow] at hfr
    exact nine3OddFrame_two_p hc.core.hyp.base.prime hc.core.hyp.base.odd hfr
  · have hpow : 2 ^ n = 4 := by omega
    have h3' : 3 ≤ Nat.card ↥(nineDelta V S) := by omega
    have hi := nine3_fibreIndep hc hI h3' hρ
    rw [hn1, hpow] at hfr
    exact nine3OddFrame_four_p hc.core.hyp.base.prime hc.core.hyp.base.odd hfr hi

theorem nine3_exists_lift (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) {j : G}
    (hj : j ∈ conjSubgroup (nineI V K) g) :
    ∃ b ∈ nineZ V K S, (∀ h ∈ nineH V K, ⁅b⁻¹ * j, h⁆ ∈ nineI V K) ∧
      ∀ i ∈ nineI V K, ⁅b⁻¹ * j, i⁆ = 1 := by
  have hp : p = 3 := nine3_p_eq_three hc hI h35
  subst hp
  have hjS : j ∈ S := hc'.conj_nineI_le_S hI hj
  have hjK : j ∈ K := hc.core.S_le_K hjS
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  have hm : 0 < Nat.card ↥(nineOmegaIn V K S) := by
    haveI : Nonempty ↥(nineOmegaIn V K S) := ⟨⟨A, hc.core.A_mem_nineOmegaIn⟩⟩
    exact Nat.card_pos
  have hfr : Nine3OddFrame 3 (Nat.card ↥(nineOmegaIn V K S))
      (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) := nine3_oddFrame hc hI hρ
  obtain ⟨φ, hφinj, hφ_val, hφD⟩ := nine3_exists_hbar_aut hc (k := j) hjK
  have hHnorm : K ≤ Subgroup.normalizer (nineH V K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Nine3Choice.nineH_le_K (V := V) (K := K))).mp (nineH_subgroupOf_normal V K)
  have hfix : ∀ d ∈ nine3FibreSet (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) 0,
      φ d = d := by
    intro d hd
    obtain ⟨U, hU, hU0, u, huU, huR, hdu⟩ := nine3_dbar_over hc hρ hd.1 hd.2
    have hUS : U ≤ S := (nine3_fib_zero_iff hc hρ hU).mp hU0
    have hB : U ∈ nineOmegaIn V K S := ⟨hU.1, hUS⟩
    have hcommI : ⁅j, (u : G)⁻¹⁆ ∈ nineI V K :=
      nine3_comm_Ig_B hc hc' hI hB
        (Subgroup.commutator_mem_commutator hj (U.inv_mem huU))
    have hmemH : j * (u : G) * j⁻¹ ∈ nineH V K := by
      have hnorm : conjSubgroup (nineH V K) j⁻¹ = nineH V K :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (hHnorm (K.inv_mem hjK))
      have hmem' : j * (u : G) * j⁻¹ ∈ conjSubgroup (nineH V K) j⁻¹ :=
        mem_conjSubgroup_iff.mpr (by
          have h1 : (j⁻¹) * (j * (u : G) * j⁻¹) * (j⁻¹)⁻¹ = (u : G) := by group
          rw [h1]
          exact u.2)
      rwa [hnorm] at hmem'
    let h' : ↥(nineH V K) := ⟨j * (u : G) * j⁻¹, hmemH⟩
    have hphi := hφ_val u h' rfl
    rw [← hdu, hphi, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcoe : ((h' : G)⁻¹ * (u : G)) = ⁅j, (u : G)⁻¹⁆ := by
      simp only [h', Subgroup.coe_mk, commutatorElement_def]
      group
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hcoe] using hcommI
  obtain ⟨s, hs, hsconj⟩ := nine3OddFrame_aut_eq_conj hfr hm 0 hφinj hφD hfix
  have hZbar_le : Subgroup.closure
        (nine3FibreSet (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) 0) ≤
      Subgroup.map (QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K)))
        ((nineZ V K S).subgroupOf (nineH V K)) := by
    rw [Subgroup.closure_le]
    intro d hd
    obtain ⟨U, hU, hU0, u, huU, huR, hdu⟩ := nine3_dbar_over hc hρ hd.1 hd.2
    have hUS : U ≤ S := (nine3_fib_zero_iff hc hρ hU).mp hU0
    have huZ : (u : G) ∈ nineZ V K S :=
      (le_iSup₂_of_le U ⟨hU.1, hUS⟩ le_rfl : U ≤ nineZ V K S) huU
    refine Subgroup.mem_map.mpr ⟨u, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact huZ
    · rw [QuotientGroup.mk'_apply]
      exact hdu
  obtain ⟨z, hz, hz_eq⟩ := Subgroup.mem_map.mp (hZbar_le hs)
  have hbZ : (z : G) ∈ nineZ V K S := Subgroup.mem_subgroupOf.mp hz
  have hbK : (z : G) ∈ K := Nine3Choice.nineH_le_K z.2
  have hz_eq' : s = QuotientGroup.mk z := hz_eq.symm
  have hHpart : ∀ h ∈ nineH V K, ⁅(z : G)⁻¹ * j, h⁆ ∈ nineI V K := by
    intro h hh
    have hmemHb : (z : G) * h * (z : G)⁻¹ ∈ nineH V K :=
      (nineH V K).mul_mem ((nineH V K).mul_mem z.2 hh) ((nineH V K).inv_mem z.2)
    have hmemHj : j * h * j⁻¹ ∈ nineH V K := by
      have hnorm : conjSubgroup (nineH V K) j⁻¹ = nineH V K :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (hHnorm (K.inv_mem hjK))
      have hmem' : j * h * j⁻¹ ∈ conjSubgroup (nineH V K) j⁻¹ :=
        mem_conjSubgroup_iff.mpr (by
          have h1 : (j⁻¹) * (j * h * j⁻¹) * (j⁻¹)⁻¹ = h := by group
          rw [h1]
          exact hh)
      rwa [hnorm] at hmem'
    let hbar : ↥(nineH V K) := ⟨h, hh⟩
    let j1 : ↥(nineH V K) := ⟨j * h * j⁻¹, hmemHj⟩
    let b1 : ↥(nineH V K) := ⟨(z : G) * h * (z : G)⁻¹, hmemHb⟩
    have hqj1 : (QuotientGroup.mk j1 : Nine3Hbar V K) = QuotientGroup.mk b1 := by
      have h1 := hφ_val hbar j1 rfl
      have h2 := hsconj (QuotientGroup.mk hbar)
      rw [h1] at h2
      rw [h2, hz_eq']
      have hz1 : (z * hbar * z⁻¹ : ↥(nineH V K)) = b1 := by
        apply Subtype.ext
        simp only [b1, hbar, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      calc (QuotientGroup.mk z : Nine3Hbar V K) * QuotientGroup.mk hbar *
            (QuotientGroup.mk z)⁻¹
          = QuotientGroup.mk (z * hbar * z⁻¹) := by
            rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        _ = QuotientGroup.mk b1 := by rw [hz1]
    have hker : (j1 * b1⁻¹ : ↥(nineH V K)) ∈ (nineI V K).subgroupOf (nineH V K) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hqj1, mul_inv_cancel]
    have hmemI : ((j1 * b1⁻¹ : ↥(nineH V K)) : G) ∈ nineI V K :=
      Subgroup.mem_subgroupOf.mp hker
    have hconjI : (z : G)⁻¹ * ((j1 * b1⁻¹ : ↥(nineH V K)) : G) * (z : G) ∈
        nineI V K := by
      have hnorm := Nine3Core.conjSubgroup_nineI (V := V) (K := K) hbK
      rw [← hnorm]
      exact mem_conjSubgroup_iff.mpr (by
        have h1 : (z : G) * ((z : G)⁻¹ * ((j1 * b1⁻¹ : ↥(nineH V K)) : G) * (z : G)) *
            (z : G)⁻¹ = ((j1 * b1⁻¹ : ↥(nineH V K)) : G) := by group
        rw [h1]
        exact hmemI)
    rw [show ⁅(z : G)⁻¹ * j, h⁆ =
        (z : G)⁻¹ * ((j1 * b1⁻¹ : ↥(nineH V K)) : G) * (z : G) by
      simp only [j1, b1, hbar, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
        commutatorElement_def]
      group]
    exact hconjI
  let J : Subgroup G := ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K
  have hJ_le_Z : J ≤ nineZ V K S :=
    iSup₂_le fun B hB =>
      (inf_le_left : B ⊓ pCoreOf 2 K ≤ B).trans (le_iSup₂_of_le B hB le_rfl)
  have hJ_le_W : J ≤ nineW V S := by
    rw [hc.core.nineW_eq]
    exact hJ_le_Z.trans le_sup_right
  have hIZ : ⁅nineI V K, nineZ V K S⁆ ≤ J := by
    refine Subgroup.commutator_le.mpr fun a ha z hz => ?_
    have hZeq : nineZ V K S = ⨆ B : ↥(nineOmegaIn V K S), B.1 :=
      (iSup_subtype'' (nineOmegaIn V K S) (fun B : Subgroup G => B)).symm
    rw [hZeq] at hz
    refine (Subgroup.iSup_induction (fun B : ↥(nineOmegaIn V K S) => B.1)
      (C := fun z => z ∈ nineZ V K S ∧ ⁅a, z⁆ ∈ J) hz ?_ ?_ ?_).2
    · intro B z hzB
      refine ⟨(le_iSup₂_of_le B.1 B.2 le_rfl : B.1 ≤ nineZ V K S) hzB, ?_⟩
      have hmem : ⁅a, z⁆ ∈ ⁅nineI V K, B.1⁆ :=
        Subgroup.commutator_mem_commutator ha hzB
      rw [hI.comm B.1 B.2] at hmem
      exact (le_iSup₂_of_le B.1 B.2 le_rfl : B.1 ⊓ pCoreOf 2 K ≤ J) hmem
    · exact ⟨Subgroup.one_mem _, by simp⟩
    · intro x y hx hy
      refine ⟨(nineZ V K S).mul_mem hx.1 hy.1, ?_⟩
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hxy : x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ := by
        have hxW : x ∈ nineW V S := by
          rw [hc.core.nineW_eq]
          exact Subgroup.mem_sup_right hx.1
        have hyW : ⁅a, y⁆ ∈ nineW V S := hJ_le_W hy.2
        have hcomm := hc.core.nineW_mul_comm hxW hyW
        calc x * ⁅a, y⁆ * x⁻¹ = (⁅a, y⁆ * x) * x⁻¹ := by rw [hcomm]
          _ = ⁅a, y⁆ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [show ⁅a, x⁆ * x * ⁅a, y⁆ * x⁻¹ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) by group,
        hxy]
      exact J.mul_mem hx.2 hy.2
  have hJ_part : ∀ i ∈ nineI V K, ⁅i, (z : G)⁻¹ * j⁆ ∈ J := by
    intro i hi
    have hij : ⁅i, j⁆ ∈ nineI V K ⊓ conjSubgroup (nineI V K) g :=
      hc.commutator_nineI_conj_le hc' hI (Subgroup.commutator_mem_commutator hi hj)
    have hbij : ⁅i, j⁆ ∈ J := by
      change ⁅i, j⁆ ∈ (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K)
      rw [← nine3_nineI_inf_nineW0 hc hI]
      exact ⟨hij.1, (Nine3Choice.nineI_inf_conj_le_nineW0 hc hI) hij⟩
    have hxW : ⁅i, j⁆ ∈ nineW V S := hJ_le_W hbij
    have hzW : (z : G) ∈ nineW V S := by
      rw [hc.core.nineW_eq]
      exact Subgroup.mem_sup_right hbZ
    have hcomm := hc.core.nineW_mul_comm hzW hxW
    have hz_comm : (z : G)⁻¹ * ⁅i, j⁆ * (z : G) = ⁅i, j⁆ := by
      calc (z : G)⁻¹ * ⁅i, j⁆ * (z : G)
          = (z : G)⁻¹ * (⁅i, j⁆ * (z : G)) := by rw [mul_assoc]
        _ = (z : G)⁻¹ * ((z : G) * ⁅i, j⁆) := by rw [hcomm.symm]
        _ = ⁅i, j⁆ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅i, (z : G)⁻¹⁆ * (z : G)⁻¹ * ⁅i, j⁆ * ((z : G)⁻¹)⁻¹ =
        ⁅i, (z : G)⁻¹⁆ * ((z : G)⁻¹ * ⁅i, j⁆ * (z : G)) by group, hz_comm]
    exact J.mul_mem (hIZ (Subgroup.commutator_mem_commutator hi
      ((nineZ V K S).inv_mem hbZ))) hbij
  have hdelta := nine3_delta_zero hc hI
    (K.mul_mem (K.inv_mem hbK) hjK) hHpart hJ_part
  refine ⟨(z : G), hbZ, hHpart, ?_⟩
  intro i hi
  have hii := hdelta i hi
  rw [← commutatorElement_inv, hii, inv_one]

end CFSG.LocalAnalysis.WeakClosure81
