module


import CFSG.Quasithin.Recognition.Stroth.Str83TwoArc
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABase
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAEquiv
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_mem_Qy_γ₀_of_fixes_two_nbrs {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {w₁ w₂ : f112Gamma L1 L2 S}
    (hw₁ : w₁ ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S))
    (hw₂ : w₂ ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S)) (hne : w₁ ≠ w₂)
    {g : (f112Amalgam L1 L2 S).Ghat}
    (hg : g ∈ CosetGeom.stab (f112Gamma0 L1 L2 S))
    (hg₁ : g ∈ CosetGeom.stab w₁) (hg₂ : g ∈ CosetGeom.stab w₂)
    (h2 : ∃ k, orderOf g = 2 ^ k) :
    g ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) := by
  obtain ⟨hF, -, ha, hSz, hL2, -⟩ := hfr
  obtain ⟨hgA, hgAγ⟩ := CosetGeom.mem_stab.mp hg
  let hW : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    ⟨⟨g, hgA⟩, hgAγ⟩
  obtain ⟨k, hkstab, hkγ⟩ := CosetGeom.stab_transitive_on_nbrs
    (γ := f112Gamma0 L1 L2 S) (δ := f112Gamma1 L1 L2 S) (δ' := w₁)
    CosetGeom.adj_γ₀_γ₁ hw₁
  obtain ⟨k', hk'stab, hk'γ⟩ := CosetGeom.stab_transitive_on_nbrs
    (γ := f112Gamma0 L1 L2 S) (δ := f112Gamma1 L1 L2 S) (δ' := w₂)
    CosetGeom.adj_γ₀_γ₁ hw₂
  have hkγ₀ : k • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
    CosetGeom.smul_eq_of_mem_stab hkstab
  have hk'γ₀ : k' • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
    CosetGeom.smul_eq_of_mem_stab hk'stab
  let hA : f112Acting L1 L2 S := k⁻¹ * (hW : f112Acting L1 L2 S) * k
  have hhAγ₀ : hA • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := by
    change (k⁻¹ * (hW : f112Acting L1 L2 S) * k) • f112Gamma0 L1 L2 S =
      f112Gamma0 L1 L2 S
    rw [mul_smul, mul_smul, hkγ₀, hgAγ]
    exact inv_smul_eq_iff.mpr hkγ₀.symm
  let hW' : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    ⟨hA, hhAγ₀⟩
  have hhAγ₁ : hA • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := by
    change (k⁻¹ * (hW : f112Acting L1 L2 S) * k) • f112Gamma1 L1 L2 S =
      f112Gamma1 L1 L2 S
    rw [mul_smul, mul_smul]
    rw [hkγ, CosetGeom.smul_eq_of_mem_stab (g := (hW : f112Acting L1 L2 S))
      (by simpa [hW] using hg₁)]
    rw [← hkγ, ← mul_smul, inv_mul_cancel, one_smul]
  let mA : f112Acting L1 L2 S := k⁻¹ * k'
  have hmAγ₀ : mA • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := by
    change (k⁻¹ * k') • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S
    rw [mul_smul, hk'γ₀]
    exact inv_smul_eq_iff.mpr hkγ₀.symm
  let mW : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    ⟨mA, hmAγ₀⟩
  have hmAγ₁ : mA • f112Gamma1 L1 L2 S = k⁻¹ • w₂ := by
    change (k⁻¹ * k') • f112Gamma1 L1 L2 S = k⁻¹ • w₂
    rw [mul_smul, hk'γ]
  have hmγ₁ : mA • f112Gamma1 L1 L2 S ≠ f112Gamma1 L1 L2 S := by
    intro hm
    have h1 : (k * mA) • f112Gamma1 L1 L2 S = w₂ := by
      have hkm : k * mA = k' := by simp [mA, mul_assoc]
      rw [hkm, hk'γ]
    have h2 : (k * mA) • f112Gamma1 L1 L2 S = w₁ := by
      rw [mul_smul, hm, hkγ]
    exact hne (h2.symm.trans h1)
  let hActc : f112Acting L1 L2 S := mA⁻¹ * hA * mA
  have hhActcγ₀ : hActc • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := by
    change (mA⁻¹ * hA * mA) • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S
    rw [mul_smul, mul_smul, hmAγ₀, hhAγ₀]
    exact inv_smul_eq_iff.mpr hmAγ₀.symm
  let hWctc : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    ⟨hActc, hhActcγ₀⟩
  have hfix_ctc : hActc • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := by
    change (mA⁻¹ * hA * mA) • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S
    rw [mul_smul, mul_smul, hmAγ₁]
    have h2 : hA • (k⁻¹ • w₂) = k⁻¹ • w₂ := by
      change (k⁻¹ * (hW : f112Acting L1 L2 S) * k) • (k⁻¹ • w₂) = k⁻¹ • w₂
      rw [mul_smul, mul_smul]
      have h3 : k • (k⁻¹ • w₂) = w₂ := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      rw [h3, CosetGeom.smul_eq_of_mem_stab (g := (hW : f112Acting L1 L2 S))
        (by simpa [hW] using hg₂)]
    rw [h2, ← hmAγ₁]
    rw [← mul_smul, inv_mul_cancel, one_smul]
  let t : G := (f112StabEquiv0 L1 L2 S hW' : G)
  let c : G := (f112StabEquiv0 L1 L2 S mW : G)
  have hctc_eq : c⁻¹ * t * c = (f112StabEquiv0 L1 L2 S hWctc : G) := by
    have hthis : (f112StabEquiv0 L1 L2 S hWctc : G) =
        (f112StabEquiv0 L1 L2 S (mW⁻¹ * hW' * mW) : G) := rfl
    rw [hthis]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, c, t]
  have hctcB : c⁻¹ * t * c ∈ bigB L1 L2 S := by
    rw [hctc_eq]
    exact (f112_smul_γ₁_eq_iff hF hActc hhActcγ₀).mp hfix_ctc
  have ht : t ∈ bigB L1 L2 S :=
    (f112_smul_γ₁_eq_iff hF hA hhAγ₀).mp hhAγ₁
  have hcP1 : c ∈ L1 ⊔ bigB L1 L2 S := (f112StabEquiv0 L1 L2 S mW).2
  have hcB : c ∉ bigB L1 L2 S := by
    intro hc
    exact hmγ₁ ((f112_smul_γ₁_eq_iff hF mA hmAγ₀).mpr hc)
  have hord_t : orderOf t = orderOf g := by
    have hhA_eq : hA = (MulAut.conj k⁻¹) (hW : f112Acting L1 L2 S) := by
      simp [hA, MulAut.conj_apply]
    calc orderOf t
        = orderOf (f112StabEquiv0 L1 L2 S hW' : ↥(L1 ⊔ bigB L1 L2 S)) := by
          rw [show t = ((f112StabEquiv0 L1 L2 S hW' :
            ↥(L1 ⊔ bigB L1 L2 S)) : G) from rfl, Subgroup.orderOf_coe]
      _ = orderOf hW' := (f112StabEquiv0 L1 L2 S).orderOf_eq hW'
      _ = orderOf ((hW' : MulAction.stabilizer (f112Acting L1 L2 S)
            (f112Gamma0 L1 L2 S)) : f112Acting L1 L2 S) :=
          (Subgroup.orderOf_coe (hW' : MulAction.stabilizer (f112Acting L1 L2 S)
            (f112Gamma0 L1 L2 S))).symm
      _ = orderOf hA := rfl
      _ = orderOf (hW : f112Acting L1 L2 S) := by
          rw [hhA_eq]
          exact (MulAut.conj k⁻¹).orderOf_eq (hW : f112Acting L1 L2 S)
      _ = orderOf g := by
          rw [show (hW : f112Acting L1 L2 S) = (⟨g, hgA⟩ : f112Acting L1 L2 S) from rfl]
          exact (Subgroup.orderOf_coe (⟨g, hgA⟩ : f112Acting L1 L2 S)).symm
  have h2t : ∃ j, orderOf t = 2 ^ j := by
    obtain ⟨j, hj⟩ := h2
    exact ⟨j, hord_t.trans hj⟩
  have htQ1 : t ∈ Q1 L1 L2 S :=
    str83_mem_pCoreOf_of_two_arc hF ha hSz hL2 hcP1 hcB ht hctcB h2t
  have hhA_Qy : ((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
      CosetGeom.Qy (f112Gamma0 L1 L2 S) :=
    (caseA_mem_Qy_γ₀_iff (L1 := L1) (L2 := L2) (S := S) hW').mpr (by simpa [t] using htQ1)
  have hhA_eq2 : ((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) =
      (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
        ((hW : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (k : (f112Amalgam L1 L2 S).Ghat) := by
    change (((k⁻¹ * (hW : f112Acting L1 L2 S) * k :
        f112Acting L1 L2 S)) : (f112Amalgam L1 L2 S).Ghat) =
      (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
        ((hW : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (k : (f112Amalgam L1 L2 S).Ghat)
    rfl
  have hk_norm : (k : (f112Amalgam L1 L2 S).Ghat) ∈
      Subgroup.normalizer (CosetGeom.Qy (f112Gamma0 L1 L2 S) :
        Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_stab_le_normalizer_Qy (f112Gamma0 L1 L2 S) hkstab
  have hgQy : g ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) := by
    have hthis := (Subgroup.mem_normalizer_iff.mp hk_norm
      (((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat))).mp hhA_Qy
    have hsimp : (k : (f112Amalgam L1 L2 S).Ghat) *
        ((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ =
        ((hW : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) := by
      rw [hhA_eq2]
      group
    rw [hsimp] at hthis
    simpa [hW] using hthis
  exact hgQy

private theorem caseA_mem_Qy_γ₁_of_fixes_two_nbrs {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {w₁ w₂ : f112Gamma L1 L2 S}
    (hw₁ : w₁ ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S))
    (hw₂ : w₂ ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S)) (hne : w₁ ≠ w₂)
    {g : (f112Amalgam L1 L2 S).Ghat}
    (hg : g ∈ CosetGeom.stab (f112Gamma1 L1 L2 S))
    (hg₁ : g ∈ CosetGeom.stab w₁) (hg₂ : g ∈ CosetGeom.stab w₂)
    (h2 : ∃ k, orderOf g = 2 ^ k) :
    g ∈ CosetGeom.Qy (f112Gamma1 L1 L2 S) := by
  obtain ⟨hF, -, ha, hSz, hL2, -⟩ := hfr
  obtain ⟨hgA, hgAγ⟩ := CosetGeom.mem_stab.mp hg
  let hW : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨⟨g, hgA⟩, hgAγ⟩
  obtain ⟨k, hkstab, hkγ⟩ := CosetGeom.stab_transitive_on_nbrs
    (γ := f112Gamma1 L1 L2 S) (δ := f112Gamma0 L1 L2 S) (δ' := w₁)
    CosetGeom.adj_γ₀_γ₁.symm hw₁
  obtain ⟨k', hk'stab, hk'γ⟩ := CosetGeom.stab_transitive_on_nbrs
    (γ := f112Gamma1 L1 L2 S) (δ := f112Gamma0 L1 L2 S) (δ' := w₂)
    CosetGeom.adj_γ₀_γ₁.symm hw₂
  have hkγ₁ : k • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
    CosetGeom.smul_eq_of_mem_stab hkstab
  have hk'γ₁ : k' • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
    CosetGeom.smul_eq_of_mem_stab hk'stab
  let hA : f112Acting L1 L2 S := k⁻¹ * (hW : f112Acting L1 L2 S) * k
  have hhAγ₁ : hA • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := by
    change (k⁻¹ * (hW : f112Acting L1 L2 S) * k) • f112Gamma1 L1 L2 S =
      f112Gamma1 L1 L2 S
    rw [mul_smul, mul_smul, hkγ₁, hgAγ]
    exact inv_smul_eq_iff.mpr hkγ₁.symm
  let hW' : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨hA, hhAγ₁⟩
  have hhAγ₀ : hA • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := by
    change (k⁻¹ * (hW : f112Acting L1 L2 S) * k) • f112Gamma0 L1 L2 S =
      f112Gamma0 L1 L2 S
    rw [mul_smul, mul_smul]
    rw [hkγ, CosetGeom.smul_eq_of_mem_stab (g := (hW : f112Acting L1 L2 S))
      (by simpa [hW] using hg₁)]
    rw [← hkγ, ← mul_smul, inv_mul_cancel, one_smul]
  let mA : f112Acting L1 L2 S := k⁻¹ * k'
  have hmAγ₁ : mA • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := by
    change (k⁻¹ * k') • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S
    rw [mul_smul, hk'γ₁]
    exact inv_smul_eq_iff.mpr hkγ₁.symm
  let mW : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨mA, hmAγ₁⟩
  have hmAγ₀ : mA • f112Gamma0 L1 L2 S = k⁻¹ • w₂ := by
    change (k⁻¹ * k') • f112Gamma0 L1 L2 S = k⁻¹ • w₂
    rw [mul_smul, hk'γ]
  have hmγ₀ : mA • f112Gamma0 L1 L2 S ≠ f112Gamma0 L1 L2 S := by
    intro hm
    have h1 : (k * mA) • f112Gamma0 L1 L2 S = w₂ := by
      have hkm : k * mA = k' := by simp [mA, mul_assoc]
      rw [hkm, hk'γ]
    have h2 : (k * mA) • f112Gamma0 L1 L2 S = w₁ := by
      rw [mul_smul, hm, hkγ]
    exact hne (h2.symm.trans h1)
  let hActc : f112Acting L1 L2 S := mA⁻¹ * hA * mA
  have hhActcγ₁ : hActc • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := by
    change (mA⁻¹ * hA * mA) • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S
    rw [mul_smul, mul_smul, hmAγ₁, hhAγ₁]
    exact inv_smul_eq_iff.mpr hmAγ₁.symm
  let hWctc : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨hActc, hhActcγ₁⟩
  have hfix_ctc : hActc • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := by
    change (mA⁻¹ * hA * mA) • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S
    rw [mul_smul, mul_smul, hmAγ₀]
    have h2 : hA • (k⁻¹ • w₂) = k⁻¹ • w₂ := by
      change (k⁻¹ * (hW : f112Acting L1 L2 S) * k) • (k⁻¹ • w₂) = k⁻¹ • w₂
      rw [mul_smul, mul_smul]
      have h3 : k • (k⁻¹ • w₂) = w₂ := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      rw [h3, CosetGeom.smul_eq_of_mem_stab (g := (hW : f112Acting L1 L2 S))
        (by simpa [hW] using hg₂)]
    rw [h2, ← hmAγ₀]
    rw [← mul_smul, inv_mul_cancel, one_smul]
  let t : G := (f112StabEquiv1 L1 L2 S hW' : G)
  let c : G := (f112StabEquiv1 L1 L2 S mW : G)
  have hctc_eq : c⁻¹ * t * c = (f112StabEquiv1 L1 L2 S hWctc : G) := by
    have hthis : (f112StabEquiv1 L1 L2 S hWctc : G) =
        (f112StabEquiv1 L1 L2 S (mW⁻¹ * hW' * mW) : G) := rfl
    rw [hthis]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, c, t]
  have hctcB : c⁻¹ * t * c ∈ bigB L1 L2 S := by
    rw [hctc_eq]
    exact (f112_smul_γ₀_eq_iff hF hActc hhActcγ₁).mp hfix_ctc
  have ht : t ∈ bigB L1 L2 S :=
    (f112_smul_γ₀_eq_iff hF hA hhAγ₁).mp hhAγ₀
  have hcP2 : c ∈ L2 ⊔ bigB L1 L2 S := (f112StabEquiv1 L1 L2 S mW).2
  have hcB : c ∉ bigB L1 L2 S := by
    intro hc
    exact hmγ₀ ((f112_smul_γ₀_eq_iff hF mA hmAγ₁).mpr hc)
  have hord_t : orderOf t = orderOf g := by
    have hhA_eq : hA = (MulAut.conj k⁻¹) (hW : f112Acting L1 L2 S) := by
      simp [hA, MulAut.conj_apply]
    calc orderOf t
        = orderOf (f112StabEquiv1 L1 L2 S hW' : ↥(L2 ⊔ bigB L1 L2 S)) := by
          rw [show t = ((f112StabEquiv1 L1 L2 S hW' :
            ↥(L2 ⊔ bigB L1 L2 S)) : G) from rfl, Subgroup.orderOf_coe]
      _ = orderOf hW' := (f112StabEquiv1 L1 L2 S).orderOf_eq hW'
      _ = orderOf ((hW' : MulAction.stabilizer (f112Acting L1 L2 S)
            (f112Gamma1 L1 L2 S)) : f112Acting L1 L2 S) :=
          (Subgroup.orderOf_coe (hW' : MulAction.stabilizer (f112Acting L1 L2 S)
            (f112Gamma1 L1 L2 S))).symm
      _ = orderOf hA := rfl
      _ = orderOf (hW : f112Acting L1 L2 S) := by
          rw [hhA_eq]
          exact (MulAut.conj k⁻¹).orderOf_eq (hW : f112Acting L1 L2 S)
      _ = orderOf g := by
          rw [show (hW : f112Acting L1 L2 S) = (⟨g, hgA⟩ : f112Acting L1 L2 S) from rfl]
          exact (Subgroup.orderOf_coe (⟨g, hgA⟩ : f112Acting L1 L2 S)).symm
  have h2t : ∃ j, orderOf t = 2 ^ j := by
    obtain ⟨j, hj⟩ := h2
    exact ⟨j, hord_t.trans hj⟩
  have htQ2 : t ∈ Q2 L1 L2 S :=
    str83_mem_pCoreOf_of_two_arc_right hF ha hSz hL2 hcP2 hcB ht hctcB h2t
  have hhA_Qy : ((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
      CosetGeom.Qy (f112Gamma1 L1 L2 S) :=
    (caseA_mem_Qy_γ₁_iff (L1 := L1) (L2 := L2) (S := S) hW').mpr (by simpa [t] using htQ2)
  have hhA_eq2 : ((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) =
      (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
        ((hW : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (k : (f112Amalgam L1 L2 S).Ghat) := by
    change (((k⁻¹ * (hW : f112Acting L1 L2 S) * k :
        f112Acting L1 L2 S)) : (f112Amalgam L1 L2 S).Ghat) =
      (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ *
        ((hW : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (k : (f112Amalgam L1 L2 S).Ghat)
    rfl
  have hk_norm : (k : (f112Amalgam L1 L2 S).Ghat) ∈
      Subgroup.normalizer (CosetGeom.Qy (f112Gamma1 L1 L2 S) :
        Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_stab_le_normalizer_Qy (f112Gamma1 L1 L2 S) hkstab
  have hgQy : g ∈ CosetGeom.Qy (f112Gamma1 L1 L2 S) := by
    have hthis := (Subgroup.mem_normalizer_iff.mp hk_norm
      (((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat))).mp hhA_Qy
    have hsimp : (k : (f112Amalgam L1 L2 S).Ghat) *
        ((hW' : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) *
        (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ =
        ((hW : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) := by
      rw [hhA_eq2]
      group
    rw [hsimp] at hthis
    simpa [hW] using hthis
  exact hgQy

theorem caseA_mem_Qy_of_fixes_two_nbrs {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {v w₁ w₂ : f112Gamma L1 L2 S}
    (hw₁ : w₁ ∈ CosetGeom.nbrs v) (hw₂ : w₂ ∈ CosetGeom.nbrs v) (hne : w₁ ≠ w₂)
    {g : (f112Amalgam L1 L2 S).Ghat} (hg : g ∈ CosetGeom.stab v)
    (hg₁ : g ∈ CosetGeom.stab w₁) (hg₂ : g ∈ CosetGeom.stab w₂)
    (h2 : ∃ k, orderOf g = 2 ^ k) : g ∈ CosetGeom.Qy v := by
  cases hv : CosetGeom.vtype v with
  | false =>
    obtain ⟨u, hu⟩ :=
      @CosetGeom.exists_smul_eq_γ₀ (f112Amalgam L1 L2 S).Ghat _
        ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        ((f112Amalgam L1 L2 S).Ghat1) ((f112Amalgam L1 L2 S).Ghat2) v hv
    have hg' : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab (f112Gamma0 L1 L2 S) := by
      have hgv : g ∈ CosetGeom.stab (u • f112Gamma0 L1 L2 S) := by rwa [← hu]
      rw [CosetGeom.stab_smul] at hgv
      exact mem_conjSub.mp hgv
    have hw₁' : (u⁻¹ : f112Acting L1 L2 S) • w₁ ∈
        CosetGeom.nbrs (f112Gamma0 L1 L2 S) := by
      have h : (f112Amalgam L1 L2 S).graphHat.Adj (u • f112Gamma0 L1 L2 S) w₁ := by
        rw [← hu]; exact hw₁
      have h2u : (u⁻¹ : f112Acting L1 L2 S) • (u • f112Gamma0 L1 L2 S) =
          f112Gamma0 L1 L2 S := by rw [← mul_smul, inv_mul_cancel, one_smul]
      have hmem := (CosetGeom.smul_adj (u⁻¹)).mpr h
      rwa [h2u] at hmem
    have hw₂' : (u⁻¹ : f112Acting L1 L2 S) • w₂ ∈
        CosetGeom.nbrs (f112Gamma0 L1 L2 S) := by
      have h : (f112Amalgam L1 L2 S).graphHat.Adj (u • f112Gamma0 L1 L2 S) w₂ := by
        rw [← hu]; exact hw₂
      have h2u : (u⁻¹ : f112Acting L1 L2 S) • (u • f112Gamma0 L1 L2 S) =
          f112Gamma0 L1 L2 S := by rw [← mul_smul, inv_mul_cancel, one_smul]
      have hmem := (CosetGeom.smul_adj (u⁻¹)).mpr h
      rwa [h2u] at hmem
    have hg₁' : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab ((u⁻¹ : f112Acting L1 L2 S) • w₁) := by
      rw [CosetGeom.stab_smul]
      refine mem_conjSub.mpr ?_
      simpa [mul_assoc] using hg₁
    have hg₂' : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab ((u⁻¹ : f112Acting L1 L2 S) • w₂) := by
      rw [CosetGeom.stab_smul]
      refine mem_conjSub.mpr ?_
      simpa [mul_assoc] using hg₂
    have hne' : (u⁻¹ : f112Acting L1 L2 S) • w₁ ≠
        (u⁻¹ : f112Acting L1 L2 S) • w₂ := by
      intro h
      apply hne
      have hc := congrArg (fun z => (u : f112Acting L1 L2 S) • z) h
      simpa [← mul_smul, mul_inv_cancel] using hc
    have h2' : ∃ k, orderOf ((u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat)) = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have hconj : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
          (u : (f112Amalgam L1 L2 S).Ghat) =
          (MulAut.conj (u : (f112Amalgam L1 L2 S).Ghat)⁻¹) g := by
        simp [MulAut.conj_apply]
      rw [hconj, (MulAut.conj (u : (f112Amalgam L1 L2 S).Ghat)⁻¹).orderOf_eq, hk]
    have hg'Q : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) :=
      caseA_mem_Qy_γ₀_of_fixes_two_nbrs hfr hw₁' hw₂' hne' hg' hg₁' hg₂' h2'
    have hmem : g ∈ conjSub (u : (f112Amalgam L1 L2 S).Ghat)
        (CosetGeom.Qy (f112Gamma0 L1 L2 S)) := mem_conjSub.mpr hg'Q
    rw [← caseA_Qy_smul u (f112Gamma0 L1 L2 S)] at hmem
    rwa [← hu] at hmem
  | true =>
    obtain ⟨u, hu⟩ :=
      @CosetGeom.exists_smul_eq_γ₁ (f112Amalgam L1 L2 S).Ghat _
        ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        ((f112Amalgam L1 L2 S).Ghat1) ((f112Amalgam L1 L2 S).Ghat2) v hv
    have hg' : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab (f112Gamma1 L1 L2 S) := by
      have hgv : g ∈ CosetGeom.stab (u • f112Gamma1 L1 L2 S) := by rwa [← hu]
      rw [CosetGeom.stab_smul] at hgv
      exact mem_conjSub.mp hgv
    have hw₁' : (u⁻¹ : f112Acting L1 L2 S) • w₁ ∈
        CosetGeom.nbrs (f112Gamma1 L1 L2 S) := by
      have h : (f112Amalgam L1 L2 S).graphHat.Adj (u • f112Gamma1 L1 L2 S) w₁ := by
        rw [← hu]; exact hw₁
      have h2u : (u⁻¹ : f112Acting L1 L2 S) • (u • f112Gamma1 L1 L2 S) =
          f112Gamma1 L1 L2 S := by rw [← mul_smul, inv_mul_cancel, one_smul]
      have hmem := (CosetGeom.smul_adj (u⁻¹)).mpr h
      rwa [h2u] at hmem
    have hw₂' : (u⁻¹ : f112Acting L1 L2 S) • w₂ ∈
        CosetGeom.nbrs (f112Gamma1 L1 L2 S) := by
      have h : (f112Amalgam L1 L2 S).graphHat.Adj (u • f112Gamma1 L1 L2 S) w₂ := by
        rw [← hu]; exact hw₂
      have h2u : (u⁻¹ : f112Acting L1 L2 S) • (u • f112Gamma1 L1 L2 S) =
          f112Gamma1 L1 L2 S := by rw [← mul_smul, inv_mul_cancel, one_smul]
      have hmem := (CosetGeom.smul_adj (u⁻¹)).mpr h
      rwa [h2u] at hmem
    have hg₁' : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab ((u⁻¹ : f112Acting L1 L2 S) • w₁) := by
      rw [CosetGeom.stab_smul]
      refine mem_conjSub.mpr ?_
      simpa [mul_assoc] using hg₁
    have hg₂' : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab ((u⁻¹ : f112Acting L1 L2 S) • w₂) := by
      rw [CosetGeom.stab_smul]
      refine mem_conjSub.mpr ?_
      simpa [mul_assoc] using hg₂
    have hne' : (u⁻¹ : f112Acting L1 L2 S) • w₁ ≠
        (u⁻¹ : f112Acting L1 L2 S) • w₂ := by
      intro h
      apply hne
      have hc := congrArg (fun z => (u : f112Acting L1 L2 S) • z) h
      simpa [← mul_smul, mul_inv_cancel] using hc
    have h2' : ∃ k, orderOf ((u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat)) = 2 ^ k := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have hconj : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
          (u : (f112Amalgam L1 L2 S).Ghat) =
          (MulAut.conj (u : (f112Amalgam L1 L2 S).Ghat)⁻¹) g := by
        simp [MulAut.conj_apply]
      rw [hconj, (MulAut.conj (u : (f112Amalgam L1 L2 S).Ghat)⁻¹).orderOf_eq, hk]
    have hg'Q : (u : (f112Amalgam L1 L2 S).Ghat)⁻¹ * g *
        (u : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy (f112Gamma1 L1 L2 S) :=
      caseA_mem_Qy_γ₁_of_fixes_two_nbrs hfr hw₁' hw₂' hne' hg' hg₁' hg₂' h2'
    have hmem : g ∈ conjSub (u : (f112Amalgam L1 L2 S).Ghat)
        (CosetGeom.Qy (f112Gamma1 L1 L2 S)) := mem_conjSub.mpr hg'Q
    rw [← caseA_Qy_smul u (f112Gamma1 L1 L2 S)] at hmem
    rwa [← hu] at hmem

end CFSG.Quasithin.Stroth

end
