module

public import CFSG.RankThree.PartOne.KE6.Phi6Frob
public import CFSG.RankThree.PartOne.KE.E6TwThreeShape
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open scoped Matrix Pointwise

variable {Ω : Type} [Field Ω]

theorem units_map_entrywise_rootDiagUnit (ς : Ω →+* Ω) (b : Fin Tag.E6.rank → Ωˣ) :
    Units.map (entrywiseHom ς) (rootDiagUnit Tag.E6 b) =
      rootDiagUnit Tag.E6 (fun i => Units.map ς.toMonoidHom (b i)) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_rootDiagUnit]

theorem rootChar_comp_perm (π : Equiv.Perm (Fin Tag.E6.rank)) (c : Fin Tag.E6.rank → Ωˣ)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => c (π i)) v = rootChar c (permLattice π v) := by
  simp only [rootChar, permLattice, Function.comp_apply]
  exact Fintype.prod_equiv π _ _ (fun i => by simp)

theorem rootAction_one {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (w : WeylGroup Tag.E6) {t₀ : ModGL Tag.E6 Ω} (ht₀ : t₀ ∈ torusGroup Tag.E6 Ω) :
    ∃ μ : Ωˣ, ∀ c : Ω, (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * 1) *
      pinnedX Tag.E6 Ω β c * (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * 1)⁻¹ =
        pinnedX Tag.E6 Ω (w • permLattice (1 : Equiv.Perm (Fin Tag.E6.rank)) β) ((μ : Ω) * c) := by
  classical
  set nw : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w with hnw
  have hnwm : nw ∈ monomialSubgroup Tag.E6 Ω := canonicalRep_mem_monomialSubgroup Ω w
  have hπ : weylQuotientHom Tag.E6 Ω ⟨nw, hnwm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  obtain ⟨b₀, hb₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀
  have hγ : IsRoot Tag.E6 (w • β) := IsRoot.smul hβ w
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnwm hβ
  rw [hπ] at hμ
  have hperm : permLattice (1 : Equiv.Perm (Fin Tag.E6.rank)) β = β := rfl
  rw [hperm]
  refine ⟨rootChar b₀ (w • β) * μ, fun c => ?_⟩
  have e1 : (t₀ * nw * 1) * pinnedX Tag.E6 Ω β c * (t₀ * nw * 1)⁻¹ =
      t₀ * (nw * pinnedX Tag.E6 Ω β c * nw⁻¹) * t₀⁻¹ := by group
  rw [e1, hμ c, hb₀, rootDiagUnit_conj_pinnedX b₀ hγ]
  congr 1
  simp only [Units.val_mul]
  ring

theorem rootAction_Q {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (w : WeylGroup Tag.E6) {t₀ : ModGL Tag.E6 Ω} (ht₀ : t₀ ∈ torusGroup Tag.E6 Ω) :
    ∃ μ : Ωˣ, ∀ c : Ω, (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * diagQ Ω) *
      pinnedX Tag.E6 Ω β c * (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * diagQ Ω)⁻¹ =
        pinnedX Tag.E6 Ω (w • permLattice e6Rho β) ((μ : Ω) * c) :=
  CFSG.RankThree.PartOne.KETw3.conj_t0nwP_pinnedX hβ w ht₀

theorem diagQ_conj_rootDiagUnit (c : Fin Tag.E6.rank → Ωˣ) :
    diagQ Ω * rootDiagUnit Tag.E6 c * (diagQ Ω)⁻¹ =
      rootDiagUnit Tag.E6 (fun i => c (e6Rho.symm i)) := by
  have h := E6_diagramMap_mul_rootDiagUnit (K := Ω) c
  rw [show diagQ Ω * rootDiagUnit Tag.E6 c = rootDiagUnit Tag.E6 (fun i => c (e6Rho.symm i)) *
    diagQ Ω from h, mul_inv_cancel_right]

theorem phi6_decomp [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpΩ : (p : Ω) ≠ 0) {y : ModGL Tag.E6 Ω} (hyH : y ∈ torusGroup Tag.E6 Ω) (hyp : y ^ p = 1)
    (Qε : ModGL Tag.E6 Ω) (πε : Equiv.Perm (Fin Tag.E6.rank))
    (hQd : ∀ c : Fin Tag.E6.rank → Ωˣ, Qε * rootDiagUnit Tag.E6 c * Qε⁻¹ =
      rootDiagUnit Tag.E6 (fun i => c (πε.symm i)))
    (ς : Ω →+* Ω) {G₃ : ModGL Tag.E6 Ω} (hG₃ : G₃ ∈ adjointGroup Tag.E6 Ω)
    (hfix : (G₃ * Qε) * Units.map (entrywiseHom ς) y * (G₃ * Qε)⁻¹ = y) :
    ∃ (w : WeylGroup Tag.E6) (t₀ q'' : ModGL Tag.E6 Ω), t₀ ∈ torusGroup Tag.E6 Ω ∧
      q'' ∈ rootSpan Tag.E6 Ω (torusRootKernel y) ∧
      G₃ * Qε = q'' * (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * Qε) ∧
      ∀ b : Fin Tag.E6.rank → Ωˣ, y = rootDiagUnit Tag.E6 b → ∀ v : Fin Tag.E6.rank → ℤ,
        rootChar b (w • permLattice πε v) = Units.map ς.toMonoidHom (rootChar b v) := by
  classical
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hyb : y = rootDiagUnit Tag.E6 b := hb
  set c : Fin Tag.E6.rank → Ωˣ := fun i => Units.map ς.toMonoidHom (b i) with hc
  set c' : Fin Tag.E6.rank → Ωˣ := fun i => c (πε.symm i) with hc'
  have hΦ : Units.map (entrywiseHom ς) y = rootDiagUnit Tag.E6 c := by
    rw [hyb, units_map_entrywise_rootDiagUnit]
  have h1 : G₃ * rootDiagUnit Tag.E6 c' * G₃⁻¹ = rootDiagUnit Tag.E6 b := by
    have e : G₃ * rootDiagUnit Tag.E6 c' * G₃⁻¹ =
        (G₃ * Qε) * rootDiagUnit Tag.E6 c * (G₃ * Qε)⁻¹ := by
      rw [hc', ← hQd c]
      group
    rw [e, ← hΦ, ← hyb]
    exact hfix
  have htr := exceptional_root_diagonal_conjugacy_Weyl_transporter Tag.E6 Ω b c'
  obtain ⟨w, hw⟩ := htr.1.1 ⟨G₃, hG₃, h1⟩
  have hwd : rootDiagUnit Tag.E6 b = canonicalRep (coxeterSystem Tag.E6) Ω w *
      rootDiagUnit Tag.E6 c' * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ :=
    (htr.2.2.1 w).2 hw
  set nw : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w with hnw
  have hnwA : nw ∈ adjointGroup Tag.E6 Ω := htr.2.2.2 w
  have hu : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹ = rootDiagUnit Tag.E6 b := by
    have e : nw⁻¹ * rootDiagUnit Tag.E6 b * nw = rootDiagUnit Tag.E6 c' := by
      rw [hwd]
      group
    calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹
        = G₃ * (nw⁻¹ * rootDiagUnit Tag.E6 b * nw) * G₃⁻¹ := by group
      _ = rootDiagUnit Tag.E6 b := by rw [e, h1]
  have hCG := centralizer_eq_sup_of_pow_eq_one hp5 hpΩ hyH hyp
  have hHN : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (torusRootKernel y) : Set (ModGL Tag.E6 Ω)) :=
    CFSG.RankThree.Classical2.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN
  have hu' : G₃ * nw⁻¹ ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel y) := by
    rw [← hCG]
    refine Subgroup.mem_inf.2 ⟨mul_mem hG₃ (inv_mem hnwA),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hyb]
    calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b =
        ((G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹) * (G₃ * nw⁻¹) := by group
      _ = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by rw [hu]
  have hu'' : G₃ * nw⁻¹ ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
      (rootSpan Tag.E6 Ω (torusRootKernel y) : Set (ModGL Tag.E6 Ω)) := by
    rw [← hmul]
    exact hu'
  obtain ⟨t₀, ht₀, q₀, hq₀, huq⟩ := hu''
  have huq' : t₀ * q₀ = G₃ * nw⁻¹ := huq
  refine ⟨w, t₀, t₀ * q₀ * t₀⁻¹, ht₀, (Subgroup.mem_normalizer_iff.1 (hHN ht₀) q₀).1 hq₀, ?_, ?_⟩
  · have : G₃ = t₀ * q₀ * nw := by
      rw [huq']
      group
    rw [this, ← hnw]
    group
  · intro b' hb' v
    have hbb : b' = b := rootDiagUnit_injective (hb'.symm.trans hyb)
    rw [hbb]
    have h2 := hw (permLattice πε v)
    rw [hc', rootChar_comp_perm, permLattice_symm_permLattice] at h2
    rw [h2, hc]
    exact (map_rootChar ς b v).symm

end CFSG.RankThree.PartOne.KE6
