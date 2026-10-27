module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProof
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofMain
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueVec
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueInj
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCfg
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

section FPL

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.mem_zpowers_of_perm_fixed (hC : GGFarCtx p Bs φ₁ φ₂ x y) {L : Subgroup G}
    (hL : φ₁.range = L)
    (hcl : ∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → g ∈ Subgroup.zpowers x) {b : G} (hb : b ∈ Bs)
    (hfix : ∀ π, hC.permAut₁ π ⟨b, hb⟩ = ⟨b, hb⟩) : b ∈ Subgroup.zpowers x := by
  apply hcl b hb
  obtain ⟨h, hv⟩ := hC.lifts.diag₁ b hb
  have hv' : GGActsVec φ₁ b h := hv
  have key : ∀ π : Equiv.Perm (Fin (n + 1)), GGVecEq h (h ∘ π.symm) := by
    intro π
    have hcomm : φ₁ (slPerm hC.two π) * b * (φ₁ (slPerm hC.two π))⁻¹ = b := by
      have := congrArg Subtype.val (hfix π)
      rw [GGFarCtx.permAut₁_apply] at this
      exact this
    have h2 := GGActsVec.conj_perm hC.two hv' π
    rw [hcomm] at h2
    exact GGActsVec.vecEq hC.lifts.ker₁ hv' h2
  have hconst : GGVecEq h 1 := by
    rw [ggVecEq_one_iff]
    intro k l
    by_cases hkl : k = l
    · rw [hkl]
    obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp (key (Equiv.swap k l))
    have hs : ({k, l} : Finset (Fin (n + 1))).card <
        (Finset.univ : Finset (Fin (n + 1))).card := by
      have hle : ({k, l} : Finset (Fin (n + 1))).card ≤ 2 := by
        have h' := Finset.card_insert_le k ({l} : Finset (Fin (n + 1)))
        simpa using h'
      have := hC.three_le
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hci : h i = c * h i := by
      have := hc i
      simpa [Function.comp, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2] using this
    have hc1 : c = 1 := by
      have : c * h i = 1 * h i := by rw [one_mul, ← hci]
      exact mul_right_cancel this
    have hk := hc k
    simpa [Function.comp, hc1] using hk
  intro l hl
  rw [← hL] at hl
  obtain ⟨s, rfl⟩ := hl
  exact hv'.commute_of_vecEq_one hconst s

end FPL

section Gate

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hnbr : GGNbr p B x D J y K) :
    y ∈ Bs ∧ y ∈ Subgroup.centralizer (K : Set G) ∧ y ∈ D ∧ y ∉ Subgroup.zpowers x ∧ x ≠ 1 := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDab : IsElemAbelian p D := hcfg.2.2.1.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  refine ⟨hcfg.2.1.1 hnbr.1.2.1, hyK, ?_, ?_, hS.2.2.1⟩
  · rw [hnbr.2.1]
    exact Subgroup.subset_closure (by simp)
  · intro hy
    have hD_le : D ≤ Subgroup.zpowers x := by
      rw [hnbr.2.1, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · exact hy
    have hzp_le : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
    have hD_eq : D = Subgroup.zpowers x := le_antisymm hD_le hzp_le
    have hxp : x ^ p = 1 := hDab.2 x hxD
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have horder : orderOf x = p ^ 2 := by
      rw [← Nat.card_zpowers, ← hD_eq, hDcard]
    have hp2dvd : p ^ 2 ∣ p := by
      rw [← horder]
      exact hdvd
    have hp2le : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2dvd
    nlinarith [hp.two_le]

theorem GGFarCtx.range_permAut₁_le {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {L : Subgroup G} (hL : φ₁.range = L) :
    hC.permAut₁.range ≤ ggAutomizer L Bs := by
  rintro _ ⟨π, rfl⟩
  refine Subgroup.subset_closure ⟨φ₁ (slPerm hC.two π), ?_, hC.perm_mem_normalizer₁ π, ?_⟩
  · rw [← hL]
    exact ⟨_, rfl⟩
  · intro b
    exact hC.permAut₁_apply π b

theorem GGFarCtx.card_range_permAut₁ {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) : Nat.card hC.permAut₁.range = (n + 1).factorial := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hC.permAut₁_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem GGFarCtx.not_automizer_le {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {n : ℕ} {F : Type} [Field F]
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x₀ y₀ : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x₀ y₀) (hL : φ₁.range = L)
    (hcl : ∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → g ∈ Subgroup.zpowers x₀) (hx : x₀ = x)
    {y' : G} {K' : Subgroup G} (hK' : GGNbr p B x D J y' K') :
    ¬ ggAutomizer L Bs ≤ ggAutomizer K' Bs := by
  intro hle
  obtain ⟨hy, hyK, -, hyx, -⟩ := ggNbr_facts hcfg hK'
  apply hyx
  rw [← hx]
  refine hC.mem_zpowers_of_perm_fixed hL hcl hy fun π => ?_
  refine ggAutomizer_fix_of_centralizes hy ?_ (hle (hC.range_permAut₁_le hL ⟨π, rfl⟩))
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp hyK k hk).symm

theorem ggTypeANbr_gate (hCD : GGTypeACompatDiagBInput) (hRO : GGTypeAReflOverInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (h : GGTypeANbrCfg p B Bs x L D J n f y K) {y' : G} {K' : Subgroup G}
    (hK' : GGNbr p B x D J y' K') :
    ∃ m, n ≤ m ∧ m ≤ n + 1 ∧
      GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) := by
  by_cases hle : ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs
  · obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, -, hc, hdiag⟩ := hCD G p B Bs x L D J n f y K h
    have hC := ggFarCtx_of_cfg h hL hk₁ hK hk₂ hc hdiag
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hWK, hAll⟩ := h
    obtain ⟨m, -, hW⟩ := (ggSecFiveAllAJoin_iff.mp hAll) y' K' hK'
    have h1 : (n + 1).factorial ≤ (m + 1).factorial := by
      rw [← ggWeylOfType_A_card hW, ← hC.card_range_permAut₁]
      exact Subgroup.card_le_of_le ((hC.range_permAut₁_le hL).trans le_sup_left)
    have h2 : (m + 1).factorial ≤ (n + 2).factorial := by
      rw [← ggWeylOfType_A_card hW, ← ggWeylOfType_A_card hWK]
      exact Subgroup.card_le_of_le (sup_le le_sup_left hle)
    refine ⟨m, ?_, ?_, hW⟩
    · by_contra hlt
      have : (m + 1).factorial < (n + 1).factorial :=
        (Nat.factorial_lt (Nat.succ_pos m)).mpr (by omega)
      omega
    · by_contra hgt
      have : (n + 2).factorial < (m + 1).factorial :=
        (Nat.factorial_lt (Nat.succ_pos (n + 1))).mpr (by omega)
      omega
  · exact ⟨n + 1, Nat.le_succ n, le_rfl, (hRO G p B Bs x L D J n f y K h y' K' hK' hle).2.1⟩

end Gate

end CFSG.StandardType

end
