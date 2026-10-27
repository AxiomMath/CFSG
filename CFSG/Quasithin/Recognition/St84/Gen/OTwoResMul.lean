module

public import CFSG.Quasithin.Recognition.St84.Gen.OTwoResL2

import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
import CFSG.Quasithin.Recognition.St84.AppTreeL2

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.St84
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112_oTwoRes_le_of_le_mul {L1 L2 S : Subgroup H} {n : ℕ}
    (hR : Hyp111R L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {M₀ : Subgroup H} (hM : M₀ ≤ L2 ⊔ bigB L1 L2 S)
    (hnorm : oTwoRes L2 ≤ Subgroup.normalizer (M₀ : Set H))
    (hmul : ∀ x ∈ oTwoRes L2, ∃ m ∈ M₀, ∃ b ∈ bigB L1 L2 S, x = m * b) :
    oTwoRes L2 ≤ M₀ := by
  let M := oTwoRes L2
  let Q := pCoreOf 2 L2
  let B₂ := borelOf L2 S
  let N := M₀ ⊓ M
  have hML : M ≤ L2 := oTwoRes_le L2
  have hB₂L : B₂ ≤ L2 := F1.borelOf_le L2 S
  have hQleB₂ : Q ≤ B₂ :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hR.hyp.h2.sylow).trans
      (F1.sylow_le_borelOf L2 S)
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
    (F1.bigB_le_normalizer_left hR).2
  have hB_normM : bigB L1 L2 S ≤ Subgroup.normalizer (M : Set H) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub b (oTwoRes L2) = oTwoRes L2
    rw [conjSub_oTwoRes, F1.conjSub_eq_of_mem_normalizer (hBL2 hb)]
  have hP2_normM : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (M : Set H) :=
    sup_le (le_normalizer_oTwoRes L2) hB_normM
  have hB_normQ : bigB L1 L2 S ≤ Subgroup.normalizer (Q : Set H) :=
    hBL2.trans (normalizer_le_normalizer_pCoreOf 2 L2)
  have hP2_normQ : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (Q : Set H) :=
    sup_le (le_normalizer_pCoreOf 2 L2) hB_normQ
  have hNnorm : (N.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxM₀ : x ∈ Subgroup.normalizer (M₀ : Set H) := hnorm hx
    have hxMM : x ∈ Subgroup.normalizer (M : Set H) :=
      (hML.trans (le_normalizer_oTwoRes L2)) hx
    constructor
    · rintro ⟨hy₀, hyM⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxM₀ y).mp hy₀,
        (Subgroup.mem_normalizer_iff.mp hxMM y).mp hyM⟩
    · rintro ⟨hy₀, hyM⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxM₀ y).mpr hy₀,
        (Subgroup.mem_normalizer_iff.mp hxMM y).mpr hyM⟩
  haveI hNnormI : (N.subgroupOf M).Normal := hNnorm
  obtain ⟨eM⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf hML (le_normalizer_oTwoRes L2)
    (f112sl_oTwoRes_sup_pCoreOf hn h2)
  have hsimpleL : IsSimpleGroup (oTwoQuot ↥L2) := by
    obtain ⟨e⟩ := h2
    have hcard : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    haveI : IsSimpleGroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
    exact e.isSimpleGroup
  haveI hsimpleM : IsSimpleGroup (↥M ⧸ CFSG.pCore 2 ↥M) := eM.isSimpleGroup
  let π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' _
  have hmapN : ((N.subgroupOf M).map π).Normal :=
    hNnorm.map π (QuotientGroup.mk'_surjective _)
  haveI : ((N.subgroupOf M).map π).Normal := hmapN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf M).map π) with hbot | htop
  ·
    have hNleQ : N ≤ Q := by
      intro x hx
      have hxM : x ∈ M := hx.2
      have hxNsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
      have hxker : (⟨x, hxM⟩ : ↥M) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
        rw [MonoidHom.mem_ker]
        have hmem : π ⟨x, hxM⟩ ∈ (N.subgroupOf M).map π :=
          Subgroup.mem_map_of_mem π hxNsub
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      have hxpc : (⟨x, hxM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := by
        rwa [QuotientGroup.ker_mk'] at hxker
      have hxQ : x ∈ pCoreOf 2 M := (F1.mem_pCore_iff_coe _).mp hxpc
      have hxMQ : x ∈ M ⊓ Q := by
        rw [inf_pCoreOf_eq_pCoreOf hML (le_normalizer_oTwoRes L2)]
        exact hxQ
      exact hxMQ.2
    have hcommN : ⁅M₀, M⁆ ≤ N := by
      refine Subgroup.commutator_le.mpr ?_
      intro m hm x hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hxm : x * m * x⁻¹ ∈ M₀ :=
          (Subgroup.mem_normalizer_iff.mp (hnorm hx) m).mp hm
        have hEq : ⁅m, x⁆ = m * (x * m * x⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [hEq]
        exact M₀.mul_mem hm (M₀.inv_mem hxm)
      · have hxm : m * x * m⁻¹ ∈ M :=
          (Subgroup.mem_normalizer_iff.mp (hP2_normM (hM hm)) x).mp hx
        have hEq : ⁅m, x⁆ = (m * x * m⁻¹) * x⁻¹ := commutatorElement_def m x
        rw [hEq]
        exact M.mul_mem hxm (M.inv_mem hx)
    have htriv : ∀ m ∈ M₀, ∀ y ∈ L2, (m * y * m⁻¹) * y⁻¹ ∈ Q := by
      intro m hm y hy
      have hmP2 : m ∈ L2 ⊔ bigB L1 L2 S := hM hm
      have hyMQ : y ∈ M ⊔ Q := by
        rw [show M ⊔ Q = L2 from f112sl_oTwoRes_sup_pCoreOf hn h2]
        exact hy
      have hcoe : (↑(M ⊔ Q) : Set H) = (M : Set H) * (Q : Set H) :=
        Subgroup.coe_mul_of_left_le_normalizer_right M Q
          (hML.trans (le_normalizer_pCoreOf 2 L2))
      have hy' : y ∈ (M : Set H) * (Q : Set H) := by
        rw [← hcoe]; exact hyMQ
      obtain ⟨x, hxM, q, hqQ, hxy⟩ := hy'
      have hcommx : m * x * m⁻¹ * x⁻¹ ∈ Q := by
        have hmem : ⁅m, x⁆ ∈ N := hcommN (Subgroup.commutator_mem_commutator hm hxM)
        have hEq : ⁅m, x⁆ = m * x * m⁻¹ * x⁻¹ := commutatorElement_def m x
        rw [← hEq]
        exact hNleQ hmem
      have hmq : m * q * m⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hP2_normQ hmP2) q).mp hqQ
      have hxL : x ∈ L2 := hML hxM
      have hconjQ : x * (m * q * m⁻¹ * q⁻¹) * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L2 hxL)
          (m * q * m⁻¹ * q⁻¹)).mp (Q.mul_mem hmq (Q.inv_mem hqQ))
      have hEq : (m * y * m⁻¹) * y⁻¹ =
          (m * x * m⁻¹ * x⁻¹) * (x * (m * q * m⁻¹ * q⁻¹) * x⁻¹) := by
        rw [← hxy]; group
      rw [hEq]
      exact Q.mul_mem hcommx hconjQ
    have hconjB₂ : ∀ m ∈ M₀, ∀ y ∈ B₂, m * y * m⁻¹ ∈ B₂ := by
      intro m hm y hy
      have hmem := htriv m hm y (hB₂L hy)
      have hEq : m * y * m⁻¹ = ((m * y * m⁻¹) * y⁻¹) * y := by group
      rw [hEq]
      exact B₂.mul_mem (hQleB₂ hmem) hy
    have hM₀_normB₂ : M₀ ≤ Subgroup.normalizer (B₂ : Set H) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact hconjB₂ m hm y
      · intro hy
        have h := hconjB₂ m⁻¹ (M₀.inv_mem hm) (m * y * m⁻¹) hy
        simpa [mul_assoc] using h
    have hB_le_normB₂ : bigB L1 L2 S ≤ Subgroup.normalizer (B₂ : Set H) :=
      (F1.bigB_le_normalizer_borelOf hR).2
    have hM_le_normB₂ : M ≤ Subgroup.normalizer (B₂ : Set H) := by
      intro x hx
      obtain ⟨m, hm, b, hb, rfl⟩ := hmul x hx
      exact Subgroup.mul_mem _ (hM₀_normB₂ hm) (hB_le_normB₂ hb)
    have hself : L2 ⊓ Subgroup.normalizer (B₂ : Set H) = B₂ := by
      have hsub : (L2 ⊓ Subgroup.normalizer (B₂ : Set H)).subgroupOf L2 =
          B₂.subgroupOf L2 := by
        rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hB₂L]
        let P : Sylow 2 ↥L2 := CFSG.Quasithin.A4.toSylow hR.hyp.h2.sylow
        have hB₂sub : B₂.subgroupOf L2 =
            Subgroup.normalizer ((P : Subgroup ↥L2) : Set ↥L2) := by
          change (L2 ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup H) : Set H)).subgroupOf L2 = _
          rw [Subgroup.inf_subgroupOf_left,
            Subgroup.subgroupOf_normalizer_eq inf_le_right, CFSG.Quasithin.A4.toSylow_coe]
        rw [hB₂sub]
        exact Sylow.normalizer_normalizer P
      rw [Subgroup.subgroupOf_inj] at hsub
      rw [inf_eq_left.mpr hB₂L] at hsub
      simpa [inf_assoc, inf_comm, inf_left_comm] using hsub
    have hM_le_B₂ : M ≤ B₂ := by
      intro x hx
      have hxinf : x ∈ L2 ⊓ Subgroup.normalizer (B₂ : Set H) :=
        ⟨hML hx, hM_le_normB₂ hx⟩
      rwa [hself] at hxinf
    have hL2_le_B₂ : L2 ≤ B₂ := by
      rw [← f112sl_oTwoRes_sup_pCoreOf hn h2]
      exact sup_le hM_le_B₂ hQleB₂
    have hidx := index_borelOf_of_psl2 (by omega : n ≠ 0) hR.hyp.h2.sylow h2
    have htopB : B₂.subgroupOf L2 = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_subgroupOf.mpr (hL2_le_B₂ x.2)
    rw [htopB, Subgroup.index_top] at hidx
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  ·
    have hsupM : N.subgroupOf M ⊔ CFSG.pCore 2 ↥M = ⊤ := by
      have h := Subgroup.comap_map_eq π (N.subgroupOf M)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hquot2 : IsPGroup 2 (↥M ⧸ N.subgroupOf M) := by
      let f : ↥(CFSG.pCore 2 ↥M) →* ↥M ⧸ N.subgroupOf M :=
        (QuotientGroup.mk' (N.subgroupOf M)).comp (CFSG.pCore 2 ↥M).subtype
      have hf : Function.Surjective f := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) q
        have hx : x ∈ N.subgroupOf M ⊔ CFSG.pCore 2 ↥M := by
          rw [hsupM]; exact Subgroup.mem_top x
        obtain ⟨n, hn, p, hp, hnp⟩ :=
          (Subgroup.mem_sup_of_normal_left (s := N.subgroupOf M)
            (t := CFSG.pCore 2 ↥M)).mp hx
        refine ⟨⟨p, hp⟩, ?_⟩
        have hfval : f ⟨p, hp⟩ = (QuotientGroup.mk' (N.subgroupOf M)) p := rfl
        rw [hfval, ← hnp, map_mul]
        have hn1 : (QuotientGroup.mk' (N.subgroupOf M)) n = 1 :=
          (QuotientGroup.eq_one_iff n).mpr hn
        rw [hn1, one_mul]
      exact (CFSG.pCore_isPGroup (G := ↥M) (p := 2)).of_surjective f hf
    have hoddN : ∀ x : ↥M, Odd (orderOf x) → x ∈ N.subgroupOf M :=
      fun x hx => CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_isPGroup_quotient _
        hquot2 hx
    have hMN : M ≤ N := by
      change Subgroup.closure {x : H | x ∈ L2 ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1} ≤ N
      refine (Subgroup.closure_le N).mpr ?_
      rintro x ⟨hxL, m, hm, hxm⟩
      have hxM : x ∈ M := Subgroup.subset_closure ⟨hxL, m, hm, hxm⟩
      have hxodd : Odd (orderOf x) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxm)
      have hxN := hoddN ⟨x, hxM⟩ (by rwa [Subgroup.orderOf_mk])
      exact Subgroup.mem_subgroupOf.mp hxN
    exact hMN.trans inf_le_left

end CFSG.Quasithin.F112R.St84
