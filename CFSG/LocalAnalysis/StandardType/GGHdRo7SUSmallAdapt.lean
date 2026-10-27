module

import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge
import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import Certificates.Data.SUSmallBase

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7SmAdaptAux_equivFun_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (i : Fin m) :
    b.equivFun (b i) = (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) := by
  ext j
  rw [Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun hj => h hj.symm)]

private lemma hdRo7SmAdaptAux_equivFun_ones {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) :
    b.equivFun (SUOnes 3 b) = smOnes m := by
  rw [SUOnes, map_sum]
  ext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [hdRo7SmAdaptAux_equivFun_basis, Pi.single_eq_same]; rfl
  · intro i _ hij
    rw [hdRo7SmAdaptAux_equivFun_basis, Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private lemma hdRo7SmAdaptAux_symm_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (g : SMGL m) (v : V) :
    (ggLinConj b.equivFun).symm g v = b.equivFun.symm (g (b.equivFun v)) := rfl

private lemma hdRo7SmAdaptAux_superm_symm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) {g : SMGL m}
    (hg : SMIsPerm g) : SUPerm 3 b ((ggLinConj b.equivFun).symm g) := by
  obtain ⟨σ, hσ⟩ := hg
  refine ⟨σ, fun i => ?_⟩
  rw [hdRo7SmAdaptAux_symm_apply]
  have hgi : g (Pi.single i (1 : ZMod 3)) = Pi.single (σ i) (1 : ZMod 3) := by
    ext j
    rw [hσ (Pi.single i 1) j, Pi.single_apply, Pi.single_apply]
    by_cases h : σ.symm j = i
    · have hj : j = σ i := by rw [← h, Equiv.apply_symm_apply]
      rw [if_pos h, if_pos hj]
    · have hj : j ≠ σ i := by
        intro hji; exact h (by rw [hji, Equiv.symm_apply_apply])
      rw [if_neg h, if_neg hj]
  rw [hdRo7SmAdaptAux_equivFun_basis b i, hgi, ← hdRo7SmAdaptAux_equivFun_basis b (σ i),
    LinearEquiv.symm_apply_apply]

private lemma hdRo7SmAdaptAux_smisperm_of_superm {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {u : V ≃ₗ[ZMod 3] V} (hu : SUPerm 3 b u) :
    SMIsPerm (ggLinConj b.equivFun u) := by
  obtain ⟨σ, hσ⟩ := hu
  refine ⟨σ, fun v i => ?_⟩
  rw [ggLinConj_apply, Module.Basis.equivFun_symm_apply]
  have hu_sum : u (∑ j, v j • b j) = ∑ j, v j • b (σ j) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hσ j]
  rw [hu_sum, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, hdRo7SmAdaptAux_equivFun_basis,
    Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (σ.symm i)]
  · rw [Equiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro j _ hji
    rw [if_neg (fun hji' => hji (by rw [← Equiv.symm_apply_apply σ j, hji'])), mul_zero]
  · intro hnot; exact absurd (Finset.mem_univ (σ.symm i)) hnot

private lemma hdRo7SmAdaptAux_smRefl_of_ggLinRefl {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {r : V ≃ₗ[ZMod 3] V} (hr : GGLinRefl r) :
    ∃ (u : SMV m) (φ : Module.Dual (ZMod 3) (SMV m)), SMRefl (ggLinConj b.equivFun r) u φ := by
  have his : IsReflLin r := (ggLinRefl_iff_isReflLin r).mp hr
  have his' : IsReflLin (ggLinConj b.equivFun r) := (ggLinConj_isReflLin b.equivFun r).mpr his
  obtain ⟨u, φ, hφu, heq⟩ := his'
  exact ⟨u, φ, hφu, fun v => by rw [heq, Module.reflection_apply]⟩

private lemma hdRo7SmAdaptAux_fix_ones {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) {g : SMGL m} {g₀ : V ≃ₗ[ZMod 3] V}
    (hg : ggLinConj b.equivFun g₀ = g) (hfix : g (smOnes m) = smOnes m) :
    g₀ (SUOnes 3 b) = SUOnes 3 b := by
  have h1 : ggLinConj b.equivFun g₀ (smOnes m) = smOnes m := by rw [hg]; exact hfix
  have hh := h1
  rw [ggLinConj_apply, ← hdRo7SmAdaptAux_equivFun_ones b, LinearEquiv.symm_apply_apply] at hh
  have h2 : b.equivFun (g₀ (SUOnes 3 b)) = b.equivFun (SUOnes 3 b) := by
    rw [hh, hdRo7SmAdaptAux_equivFun_ones b]
  exact b.equivFun.injective h2

private lemma hdRo7SmAdaptAux_transport_connected {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (S : Set (V ≃ₗ[ZMod 3] V)) {r s : V ≃ₗ[ZMod 3] V}
    (h : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ ¬ Commute a b) r s) :
    Relation.ReflTransGen
      (fun x y : SMGL m => x ∈ ((ggLinConj b.equivFun).toMonoidHom '' S) ∧
        y ∈ ((ggLinConj b.equivFun).toMonoidHom '' S) ∧ ¬ Commute x y)
      (ggLinConj b.equivFun r) (ggLinConj b.equivFun s) := by
  exact (Relation.ReflTransGen.lift (ggLinConj b.equivFun) (fun x y hxy =>
    ⟨⟨x, hxy.1, rfl⟩, ⟨y, hxy.2.1, rfl⟩,
      fun hc => hxy.2.2 (hc.of_map (ggLinConj b.equivFun).injective)⟩)) r s h

theorem su_linSmall_of_concrete : (∀ (m : ℕ), (m = 7 ∨ m = 8) → ∀ (H : Subgroup (SMGL m)), (∀ g,
    SMIsPerm g → g ∈ H) → QTwoLin.TransvectionFree H → (∀ g ∈ H, g (smOnes m) = smOnes m → ∀ s,
    SMIsPerm s → SMIsPerm (g * s * g⁻¹)) → (∃ S : Set (SMGL m), H = Subgroup.closure S ∧ (∀ r ∈ S, ∃
    (u : SMV m) (φ : Module.Dual (ZMod 3) (SMV m)), SMRefl r u φ) ∧ ∀ r ∈ S, ∀ t ∈ S,
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ ¬ Commute a b) r t) → ZS.LinWeyl 3
    H) → SULinSmallLeaf := by
  intro h p hpFact m V hAdd hMod b H A hdata hm
  have hp3 : p = 3 := hdata.hp
  subst p
  let τ : V ≃ₗ[ZMod 3] (SMV m) := b.equivFun
  let Hc : Subgroup (SMGL m) := H.map (ggLinConj τ).toMonoidHom
  have hTF : QTwoLin.TransvectionFree H := fun g hg hgt =>
    hdata.hNoT g (hdata.hHA hg) (c2Transv_of_isTransvectionLin g hgt)
  obtain ⟨S, hS, hHcl, hconn⟩ := hdata.hgen
  let S' : Set (SMGL m) := (ggLinConj τ).toMonoidHom '' S
  have hmapH : Hc = Subgroup.closure S' := by
    dsimp only [Hc, S']
    rw [hHcl]
    exact MonoidHom.map_closure (ggLinConj τ).toMonoidHom S
  have hperm_mem : ∀ g, SMIsPerm g → g ∈ Hc := by
    intro g hg
    refine Subgroup.mem_map.mpr ⟨(ggLinConj τ).symm g,
      hdata.hPH _ (hdRo7SmAdaptAux_superm_symm b hg), ?_⟩
    exact (ggLinConj τ).apply_symm_apply g
  have hTF' : QTwoLin.TransvectionFree Hc := (ggLinConj_transvectionFree τ H).mpr hTF
  have hstab' : ∀ g ∈ Hc, g (smOnes m) = smOnes m → ∀ s, SMIsPerm s →
      SMIsPerm (g * s * g⁻¹) := by
    intro g hg hfix s hs
    obtain ⟨g₀, hg₀H, hg₀eq⟩ := Subgroup.mem_map.mp hg
    have hg₀eq' : ggLinConj τ g₀ = g := hg₀eq
    have hfix₀ : g₀ (SUOnes 3 b) = SUOnes 3 b := hdRo7SmAdaptAux_fix_ones b hg₀eq' hfix
    have hsu₀ : SUPerm 3 b ((ggLinConj τ).symm s) := hdRo7SmAdaptAux_superm_symm b hs
    have hsu : SUPerm 3 b (g₀ * (ggLinConj τ).symm s * g₀⁻¹) :=
      hdata.hStab g₀ (hdata.hHA hg₀H) hfix₀ _ hsu₀
    have himg : ggLinConj τ (g₀ * (ggLinConj τ).symm s * g₀⁻¹) = g * s * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg₀eq', (ggLinConj τ).apply_symm_apply]
    rw [← himg]
    exact hdRo7SmAdaptAux_smisperm_of_superm b hsu
  have hrefl_S' : ∀ r ∈ S', ∃ u φ, SMRefl r u φ := by
    rintro r ⟨s, hsS, rfl⟩
    exact hdRo7SmAdaptAux_smRefl_of_ggLinRefl b (hS s hsS).2
  have hconn_S' : ∀ r ∈ S', ∀ t ∈ S',
      Relation.ReflTransGen (fun a b => a ∈ S' ∧ b ∈ S' ∧ ¬ Commute a b) r t := by
    rintro r ⟨r₀, hr₀S, rfl⟩ t ⟨t₀, ht₀S, rfl⟩
    exact hdRo7SmAdaptAux_transport_connected b S (hconn r₀ hr₀S t₀ ht₀S)
  have hgen' : ∃ S : Set (SMGL m), Hc = Subgroup.closure S ∧
      (∀ r ∈ S, ∃ (u : SMV m) (φ : Module.Dual (ZMod 3) (SMV m)), SMRefl r u φ) ∧
      ∀ r ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ ¬ Commute a b) r t :=
    ⟨S', hmapH, hrefl_S', hconn_S'⟩
  have hW : ZS.LinWeyl 3 Hc := h m hm Hc hperm_mem hTF' hstab' hgen'
  exact linWeyl_of_map_ggLinConj τ H hW

end CFSG.StandardType.HdRo7SU.Small
