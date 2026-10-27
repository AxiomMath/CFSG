module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus

public section

namespace CFSG.StandardType

namespace RCSTSp2

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot OTwoGen RootCentSp RCSTSp
open scoped commutatorElement

section Layer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {G : Type} [Group G] [Finite G]

theorem sThreeSetting_short_two_three (hK : Nat.card F = 2) (hn : 2 ≤ n)
    (ψ : StatedSp (n + 3) F →* G) (hψ : Function.Injective ψ) {r : G}
    (hr : ψ.range ⊓ Subgroup.centralizer {r} =
      ψ.range ⊓ Subgroup.centralizer {ψ (twoCentralElt (n + 3) 1 2 (0 : F) 1)}) :
    ∃ Q S T : Subgroup G, GGRCSSThreeSetting ψ.range r Q S T := by
  have h12 := one_ne_two_fin (n := n)
  obtain ⟨hC, hSQ, hTQ, hST⟩ := centralizer_a2_facts (F := F) (n := n)
  set QW := wRadical F (1 : Fin (n + 3)) 2 with hQW
  set S := (shortBlock F h12).range with hS
  set T := spCompl12 F n with hT
  set Q := QW.map ψ with hQdef
  set Sψ := S.map ψ with hSψ
  set Tψ := T.map ψ with hTψ
  have hXU : ggRCSX ψ.range r = (QW ⊔ (S ⊔ T)).map ψ := by
    change ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r}) = _
    rw [hr]
    change ggRCSX ψ.range (ψ (twoCentralElt (n + 3) 1 2 0 1)) = _
    rw [RCSTSp.ggRCSX_eq_map_centralizer ψ hψ
      (centralizer_twoCentralElt_le_ggOTwoPrime h12), hC]
  have hX : ggRCSX ψ.range r = Q ⊔ (Sψ ⊔ Tψ) := by
    rw [hXU, Subgroup.map_sup, Subgroup.map_sup]
  have hQ2 : IsPGroup 2 Q := (isPGroup_wRadical h12).map ψ
  have hSψQ : Sψ ≤ normalizer (Q : Set G) := ggRCST_map_le_normalizer ψ hSQ
  have hTψQ : Tψ ≤ normalizer (Q : Set G) := ggRCST_map_le_normalizer ψ hTQ
  have hSψT : Sψ ≤ centralizer (Tψ : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hST hs)) t ht]
  have hdQL : Disjoint Q (Sψ ⊔ Tψ) := by
    rw [hSψ, hTψ, ← Subgroup.map_sup]
    exact disjoint_map_of_injective hψ disjoint_wRadical_levi
  have hdST : Disjoint Sψ Tψ := disjoint_map_of_injective hψ disjoint_shortBlock_spCompl12
  have hD : ggRCSXd ψ.range r = Q ⊔ Tψ := by
    change CFSG.Quasithin.perfectCore (ggRCSX ψ.range r) = Q ⊔ Tψ
    rw [hXU, ← CFSG.Quasithin.map_perfectCore, ← hC,
      perfectCore_centralizer_twoCentralElt_two hK hn (Or.inl rfl), Subgroup.map_sup]
  have hTq : CFSG.IsQuasisimple Tψ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((spCompl12Equiv F n).trans (T.equivMapOfInjective ψ hψ))
      (CFSG.LieType.Universal.Symplectic.isQuasisimple (n + 1) F (by omega)
        (Or.inr (Or.inr ⟨hK, by omega⟩)))
  have hTcen : ∀ t ∈ Tψ, (∀ t' ∈ Tψ, t * t' = t' * t) → t = 1 := by
    rintro _ ⟨t, ht, rfl⟩ h
    rw [eq_one_of_commute_spCompl12 ht fun t' ht' => hψ (by
      rw [map_mul, map_mul]
      exact h _ ⟨t', ht', rfl⟩), map_one]
  have hTZ : Subgroup.center ↥Tψ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hTcen z z.2 fun t' ht' =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t', ht'⟩)).symm)
  have h3T : 3 ∣ Nat.card Tψ := by
    have h6 : Nat.card (longRootSp2 F (n + 3) 0) = 6 := by
      rw [longRootSp2,
        Nat.card_congr (MonoidHom.ofInjective (longBlock_injective 0)).symm.toEquiv,
        CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK]
      norm_num
    have h1 : Nat.card (longRootSp2 F (n + 3) 0) ∣ Nat.card T :=
      Subgroup.card_dvd_of_le (longRootSp2_le_spCompl12 n)
    rw [h6] at h1
    rw [hTψ, Nat.card_congr (T.equivMapOfInjective ψ hψ).symm.toEquiv]
    exact dvd_trans (by norm_num) h1
  have hS3 : Nonempty (↥Sψ ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := F) hK
    exact ⟨(S.equivMapOfInjective ψ hψ).symm.trans
      ((MonoidHom.ofInjective (shortBlock_injective h12)).symm.trans e3)⟩
  have hXgen : ggRCSX ψ.range r =
      (Subgroup.centralizer {twoCentralElt (n + 3) 1 2 (0 : F) 1}).map ψ := by
    rw [hXU, ← hC]
  have h1 : ψ.range ⊓ Subgroup.centralizer {r} ≤ ggRCSX ψ.range r := by
    rw [hr, RCSTSp.range_inf_centralizer_of_injective hψ, hXgen]
  exact ⟨Q, Sψ, Tψ, h1, hX, hQ2, hSψQ, hTψQ, hSψT, hdQL, hdST, hD, hS3, hTq, hTZ, h3T⟩

theorem sThreeSetting_short_two_three_gen (hK : Nat.card F = 2) (hn : 2 ≤ n)
    (ψ : StatedSp (n + 3) F →* G) (hψ : Function.Injective ψ) {r : G}
    {h : StatedSp (n + 3) F} {i j : Fin (n + 3)} (hij : i ≠ j)
    (hr : ψ.range ⊓ Subgroup.centralizer {r} =
      ψ.range ⊓ Subgroup.centralizer {ψ (h * twoCentralElt (n + 3) i j (0 : F) 1 * h⁻¹)}) :
    ∃ Q S T : Subgroup G, GGRCSSThreeSetting ψ.range r Q S T := by
  obtain ⟨g, hg⟩ := exists_conj_one_two (F := F) hij
  have hrange : (ψ.comp (MulAut.conj (h * g)).toMonoidHom).range = ψ.range :=
    range_comp_conj ψ (h * g)
  have h1 : ψ (h * twoCentralElt (n + 3) i j (0 : F) 1 * h⁻¹) =
      (ψ.comp (MulAut.conj (h * g)).toMonoidHom) (twoCentralElt (n + 3) 1 2 0 1) := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    congr 1
    group
  have key := sThreeSetting_short_two_three hK hn (ψ.comp (MulAut.conj (h * g)).toMonoidHom)
    (comp_conj_injective hψ _) (r := r) (by rw [hrange, ← h1]; exact hr)
  rwa [hrange] at key

end Layer

end RCSTSp2

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal.Spin (HypFrame)

section Frame

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {P₁ P₂ P₃ : HypPair Q}

open scoped MatrixGroups in
theorem sThreeSetting_frame (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {y₀ : V} (hy₀ : y₀ ≠ 0) (hy₀W : InW P₁ P₂ y₀)
    (hy₀3 : polar Q P₃.e y₀ = 0 ∧ polar Q P₃.f y₀ = 0)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) (nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hWq : CFSG.IsQuasisimple (orthDerived (Q.restrict (wSub P₁ P₂))))
    (hWZ : center (orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥)
    (h3 : 3 ∣ Nat.card (omFix Q P₁ P₂))
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) (u : U) :
    ∃ QG SG TG : Subgroup G, GGRCSSThreeSetting ψ.range (ψ (u * x * u⁻¹)) QG SG TG := by
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr]
  have h1 : φ.range ⊓ centralizer {φ x} ≤ ggRCSX φ.range (φ x) := by
    rw [RCSTSp.range_inf_centralizer_of_injective hφ,
      RCSTSp.ggRCSX_eq_map_centralizer φ hφ hxC]
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q P₁ P₂) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) P₁ P₂) with hAGdef
  set BG := Φ σ φ (omFix Q P₁ P₂) with hBGdef
  have hX : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ BG := by
    rw [RCSTSp.ggRCSX_eq_map_centralizer φ hφ hxC, centralizer_eq_comap hσ hσE x, hx,
      centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv P₁ P₂ h₁₂ hE)
  have eB : ↥BG ≃* ↥(orthDerived (Q.restrict (wSub P₁ P₂))) :=
    (Φ_equiv hσ φ hφ hL₂E).trans
      (omFixEquiv h₁₂ hQ hEΩ hOE (nondegenerate_restrict_wSub hQ h₁₂) hΩ)
  have hBq : CFSG.IsQuasisimple BG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hWq
  have hBZ : center BG = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eB.symm, hWZ,
      Subgroup.map_bot]
  obtain ⟨x', hx'W, hx'3, hy₀x'⟩ := exists_polar_eq_one_perp hQ h₁₂ h₁₃ h₂₃ hy₀ hy₀W hy₀3
  have hQB : QG ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := by
    have h := Φ_mono (σ := σ) φ
      (rootRadical_le_commutator_omFix h₁₂ h₁₃ h₂₃ hy₀W hx'W hy₀3 hx'3 hy₀x')
    rwa [Φ_commutator hσ φ (sup_le hRE hL₂E) (sup_le hRE hL₂E), Φ_sup hσ φ hRE hL₂E] at h
  obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
  have eS : ↥AG ≃* Equiv.Perm (Fin 3) := eA.trans e3
  have hdQL : Disjoint QG (AG ⊔ BG) := by
    have h := Φ_disjoint hσ φ hφ (disjoint_rootRadical_sup h₁₂)
    rwa [Φ_sup hσ φ hL₁E hL₂E] at h
  have hdST : Disjoint AG BG := Φ_disjoint hσ φ hφ (disjoint_leviFix_omFix h₁₂)
  have hBperf : ⁅BG, BG⁆ = BG := Subgroup.isPerfect_iff.mp hBq.1
  have hperf : ⁅QG ⊔ BG, QG ⊔ BG⁆ = QG ⊔ BG := by
    refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQB ?_)
    calc BG = ⁅BG, BG⁆ := hBperf.symm
      _ ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have hSs : Group.IsSolvable ↥AG :=
    Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
  have hD : CFSG.Quasithin.perfectCore (ggRCSX φ.range (φ x)) = QG ⊔ BG :=
    perfectCore_eq_of_solvable (by rw [hX, sup_assoc]) (le_normalizer_sup_of_centralizer h1Q h12)
      hSs hperf
  have h3B : 3 ∣ Nat.card BG := by
    rw [Nat.card_congr (Φ_equiv hσ φ hφ hL₂E).toEquiv]
    exact h3
  exact ⟨QG, AG, BG, h1, by rw [hX, sup_assoc], hQ2, h1Q, h2Q, h12, hdQL, hdST, hD, ⟨eS⟩,
    hBq, hBZ, h3B⟩

end Frame

end RCSTOm

end CFSG.StandardType
