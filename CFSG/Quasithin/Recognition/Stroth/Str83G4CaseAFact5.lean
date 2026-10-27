module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFact4
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseARAbel
import CFSG.Quasithin.Recognition.Stroth.F112Moufang
import CFSG.Quasithin.Background.F7E1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_not_commute_base
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {z : (f112Amalgam L1 L2 S).Ghat}
    (hz0 : z ∈ CosetGeom.stab (f112Gamma0 L1 L2 S))
    (hz1 : z ∈ CosetGeom.stab (f112Gamma1 L1 L2 S))
    (h2 : ∃ k, orderOf z = 2 ^ k)
    (hzQ : z ∉ CosetGeom.Qy (f112Gamma1 L1 L2 S)) :
    ∃ y ∈ caseAZ (f112Gamma1 L1 L2 S), ¬ Commute z y := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨h1, hfix1⟩ := CosetGeom.mem_stab.mp hz1
  let hz : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨⟨z, h1⟩, hfix1⟩
  let t : G := ((f112StabEquiv1 L1 L2 S hz : ↥(P2 L1 L2 S)) : G)
  have hfix0 : (⟨z, h1⟩ : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S =
      f112Gamma0 L1 L2 S :=
    CosetGeom.smul_eq_of_mem_stab (γ := f112Gamma0 L1 L2 S)
      (g := (⟨z, h1⟩ : f112Acting L1 L2 S)) (by simpa using hz0)
  have htB : t ∈ bigB L1 L2 S := by
    have h := (f112_smul_γ₀_eq_iff hF (⟨z, h1⟩ : f112Acting L1 L2 S) hz.2).mp hfix0
    simpa [t, hz] using h
  have ht2 : ∃ k, orderOf t = 2 ^ k := by
    obtain ⟨k, hk⟩ := h2
    have hzord : orderOf hz = orderOf z := by
      rw [← Subgroup.orderOf_coe hz]
      exact Subgroup.orderOf_mk z h1
    refine ⟨k, ?_⟩
    calc orderOf t = orderOf (f112StabEquiv1 L1 L2 S hz : ↥(P2 L1 L2 S)) :=
          Subgroup.orderOf_coe _
      _ = orderOf hz := MulEquiv.orderOf_eq (f112StabEquiv1 L1 L2 S) hz
      _ = orderOf z := hzord
      _ = 2 ^ k := hk
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSylB := F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF) hSB hBP
  have hnB : (S.subgroupOf (bigB L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hB
  have htS : t ∈ S := by
    obtain ⟨k, hk⟩ := ht2
    have hX : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    exact F7.le_of_normal_sylow hSylB hnB (Subgroup.zpowers_le.mpr htB) hX
      (Subgroup.mem_zpowers t)
  have htQ : t ∉ Q2 L1 L2 S := by
    intro htQ
    apply hzQ
    have h := (caseA_mem_Qy_γ₁_iff hz).mpr (by simpa [t] using htQ)
    simpa [hz] using h
  obtain ⟨-, -, -, hCZ, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hnotle : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer ({t} : Set G) := by
    intro hle
    have htC : t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        ((Subgroup.mem_centralizer_iff.mp (hle hz)) t (Set.mem_singleton t)).symm
    apply htQ
    rw [← hCZ]
    exact Subgroup.mem_inf.mpr ⟨htS, htC⟩
  obtain ⟨y', hy'Z2, hy'notCent⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hnotcomm : ¬ Commute t y' := by
    intro hc
    apply hy'notCent
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hc.eq
  have hy'P2 : y' ∈ P2 L1 L2 S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.openPCoreOf_le 2 (P2 L1 L2 S)) hy'Z2
  let hyP : ↥(P2 L1 L2 S) := ⟨y', hy'P2⟩
  let hyStab : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    (f112StabEquiv1 L1 L2 S).symm hyP
  let y : (f112Amalgam L1 L2 S).Ghat := ((hyStab : f112Acting L1 L2 S) : _)
  have hyZ : y ∈ caseAZ (f112Gamma1 L1 L2 S) := by
    refine (caseA_mem_Z_γ₁_iff hyStab).mpr ?_
    show (f112StabEquiv1 L1 L2 S hyStab : G) ∈ Z2 L1 L2 S
    rw [show f112StabEquiv1 L1 L2 S hyStab = hyP from
      MulEquiv.apply_symm_apply (f112StabEquiv1 L1 L2 S) hyP]
    simpa [hyP] using hy'Z2
  have hnotzy : ¬ Commute z y := by
    intro hc
    apply hnotcomm
    have hsub : hz * hyStab = hyStab * hz := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hc.eq
    have himg := congrArg (fun x => (f112StabEquiv1 L1 L2 S x : ↥(P2 L1 L2 S))) hsub
    have himg' : (f112StabEquiv1 L1 L2 S hz : ↥(P2 L1 L2 S)) *
          (f112StabEquiv1 L1 L2 S hyStab : ↥(P2 L1 L2 S)) =
        (f112StabEquiv1 L1 L2 S hyStab : ↥(P2 L1 L2 S)) *
          (f112StabEquiv1 L1 L2 S hz : ↥(P2 L1 L2 S)) := by
      simpa using himg
    have hg : t * y' = y' * t := by
      have := congrArg (fun x : ↥(P2 L1 L2 S) => (x : G)) himg'
      simpa [t, hyP, hyStab] using this
    exact hg
  exact ⟨y, hyZ, hnotzy⟩

private theorem caseA_not_commute_of_adj
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {α β : f112Gamma L1 L2 S}
    (hadj : (f112Amalgam L1 L2 S).graphHat.Adj α β) (hβ : CosetGeom.vtype β = true)
    {z : (f112Amalgam L1 L2 S).Ghat} (hzα : z ∈ CosetGeom.stab α)
    (hzβ : z ∈ CosetGeom.stab β) (h2 : ∃ k, orderOf z = 2 ^ k)
    (hzQ : z ∉ CosetGeom.Qy β) :
    ∃ y ∈ caseAZ β, ¬ Commute z y := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge hadj
  · let gG : (f112Amalgam L1 L2 S).Ghat := (g : f112Acting L1 L2 S)
    let x : (f112Amalgam L1 L2 S).Ghat := gG⁻¹ * z * gG
    have hx0 : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) := by
      have h := hzα
      rw [← hg.1, CosetGeom.stab_smul] at h
      simpa [x, gG] using (mem_conjSub.mp h)
    have hx1 : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := by
      have h := hzβ
      rw [← hg.2, CosetGeom.stab_smul] at h
      simpa [x, gG] using (mem_conjSub.mp h)
    have hxord : orderOf x = orderOf z := by
      have hxeq : x = MulAut.conj gG⁻¹ z := by
        simp [x, gG, MulAut.conj_apply, mul_assoc]
      rw [hxeq]
      exact MulEquiv.orderOf_eq (MulAut.conj gG⁻¹) z
    have h2x : ∃ k, orderOf x = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, by rw [hxord, hk]⟩
    have hxQ : x ∉ CosetGeom.Qy (f112Gamma1 L1 L2 S) := by
      intro hx
      apply hzQ
      have hzconj : z ∈ CosetGeom.Qy (g • f112Gamma1 L1 L2 S) := by
        rw [caseA_Qy_smul]
        exact mem_conjSub.mpr (by simpa [x, gG] using hx)
      exact hg.2 ▸ hzconj
    obtain ⟨y', hy'Z, hy'not⟩ := caseA_not_commute_base hfr hx0 hx1 h2x hxQ
    let y : (f112Amalgam L1 L2 S).Ghat := gG * y' * gG⁻¹
    have hyZ : y ∈ caseAZ β := by
      have hyconj : y ∈ caseAZ (g • f112Gamma1 L1 L2 S) := by
        rw [caseA_Z_smul]
        exact mem_conjSub.mpr (by simpa [y, gG, mul_assoc] using hy'Z)
      exact hg.2 ▸ hyconj
    have hnot : ¬ Commute z y := by
      intro hc
      exact hy'not (by
        have := Commute.conj hc gG⁻¹
        simpa [x, y, gG, mul_assoc] using this)
    exact ⟨y, hyZ, hnot⟩
  · exfalso
    have hfalse : CosetGeom.vtype β = false := by
      rw [← hg.1, CosetGeom.vtype_smul]
      rfl
    rw [hfalse] at hβ
    exact Bool.false_ne_true hβ

theorem caseA_boundAt_four
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) :
    caseABoundAt L1 L2 S 4 := by
  have hb3 : caseABoundAt L1 L2 S 3 := (caseA_boundAt_three_iff hfr).mpr hA
  intro β δ hβ hd
  by_cases h3 : CosetGeom.dist β δ ≤ 3
  · exact hb3 β δ hβ h3
  · have hd4 : CosetGeom.dist β δ = 4 := by omega
    by_contra hnot
    obtain ⟨z, hzZ, hzQ⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨α₁, hadj₁, hd₁⟩ :=
      CosetGeom.exists_adj_dist_eq (α := β) (δ := δ) (d := 3) rfl (by omega)
    obtain ⟨β₂, hadj₂, hd₂⟩ :=
      CosetGeom.exists_adj_dist_eq (α := β) (δ := α₁) (d := 2) rfl (by omega)
    obtain ⟨α₃, hadj₃, hd₃⟩ :=
      CosetGeom.exists_adj_dist_eq (α := β) (δ := β₂) (d := 1) rfl (by omega)
    have hβ₂ : CosetGeom.vtype β₂ = true := by
      have h := (CosetGeom.vtype_eq_iff_even_dist rfl β β₂).mpr
        (by rw [hd₂]; exact even_two)
      rw [hβ] at h
      exact h.symm
    have hδ : CosetGeom.vtype δ = true := by
      have h := (CosetGeom.vtype_eq_iff_even_dist rfl β δ).mpr
        (by rw [hd4]; exact ⟨2, by norm_num⟩)
      rw [hβ] at h
      exact h.symm
    have hz2 : ∃ k, orderOf z = 2 ^ k := by
      have hsq : z ^ 2 = 1 :=
        (SmithC27.isElemAbelian_omegaOneCenterOf (CosetGeom.Qy β)).2 z hzZ
      have hne : z ≠ 1 := by
        intro h1
        apply hzQ
        rw [h1]
        exact (CosetGeom.Qy δ).one_mem
      exact ⟨1, by rw [orderOf_eq_prime hsq hne]; norm_num⟩
    have hzQα₁ : z ∈ CosetGeom.Qy α₁ := hb3 β α₁ hβ (by omega) hzZ
    have hzQα₃ : z ∈ CosetGeom.Qy α₃ := hb3 β α₃ hβ (by omega) hzZ
    have hzstab₁ : z ∈ CosetGeom.stab α₁ := caseA_Qy_le_stab α₁ hzQα₁
    have hzstabδ : z ∈ CosetGeom.stab δ := by
      have hzK : z ∈ CosetGeom.ballStab 1 α₁ :=
        caseA_Qy_le_ballStab_one hfr α₁ hzQα₁
      have hd₁δ : CosetGeom.dist α₁ δ ≤ 1 :=
        le_of_eq (CosetGeom.dist_eq_one_iff_adj.mpr hadj₁.symm)
      exact CosetGeom.ballStab_le_stab_of_dist_le hd₁δ hzK
    obtain ⟨y, hyZδ, hyNot⟩ :=
      caseA_not_commute_of_adj hfr hadj₁.symm hδ hzstab₁ hzstabδ hz2 hzQ
    have hβnbr₃ : β ∈ CosetGeom.nbrs α₃ := (CosetGeom.dist_eq_one_iff_adj.mp hd₃).symm
    have hzX₃ : z ∈ caseAX α₃ :=
      (le_iSup₂_of_le (f := fun w (_ : w ∈ CosetGeom.nbrs α₃) => caseAZ w) β hβnbr₃
        le_rfl) hzZ
    have hδnbr₁ : δ ∈ CosetGeom.nbrs α₁ := hadj₁.symm
    have hyX₁ : y ∈ caseAX α₁ :=
      (le_iSup₂_of_le (f := fun w (_ : w ∈ CosetGeom.nbrs α₁) => caseAZ w) δ hδnbr₁
        le_rfl) hyZδ
    have h₁ : α₁ ∈ CosetGeom.nbrs β₂ := hadj₂.symm
    have h₃ : α₃ ∈ CosetGeom.nbrs β₂ := hadj₃
    exact hyNot (caseA_commute_X hfr hA hβ₂ h₁ h₃ hyX₁ hzX₃).symm

end CFSG.Quasithin.Stroth

end
