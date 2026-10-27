module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeAut
public import CFSG.LocalAnalysis.StandardType.GGSL7CentralCover
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBFrame

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem linear_two_data_of_innerDiagOnLabel {G : Type} [Group G]
    {S : ℕ → LargeEvenLabel → Prop} {Bs K : Subgroup G}
    (hS : ∀ lab, S 3 lab → lab.tag = .A ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) :
    ∃ (d : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (θ : K ⧸ Subgroup.center K ≃* projectiveSL d F),
      3 ≤ d ∧ Nat.card F = 2 ∧ commutator K = ⊤ ∧
        ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
          Set.range (conjAut d F) := by
  obtain ⟨hperf, lab, hLambda, hraw⟩ := hK
  obtain ⟨R, _, I, _, -, -, θ₀, hs, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hA, hn⟩ := hS lab hs
  have hd : 3 ≤ lab.rank + 1 := by
    simp only [LargeEvenInLambda2, hA] at hLambda
    omega
  dsimp only [CFSG.StandardType.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [hA] at hraw
  dsimp only [LargeEvenRecipeLinear] at hraw
  obtain ⟨F, hfield, hfin, hF, -, -, θ, -, hNs, h3I⟩ := hraw
  letI : Field F := hfield
  letI : Finite F := hfin
  have hF2 : Nat.card F = 2 := by simpa only [hn, pow_one] using hF
  letI : CharP F 2 := charP_two_of_card (m := 1) (by simpa using hF2)
  let e := TypeA.recipeEquiv (lab.rank + 1) F
  refine ⟨lab.rank + 1, F, hfield, hfin, inferInstance, hNs, θ.trans e,
    hd, hF2, hperf, fun b hb => ?_⟩
  have hi := TypeA.congr_recipeEquiv_mem (ggLAut_mem_of_induces K θ hNs h3I hb)
  have he : θ.symm.trans (θ.trans e) = e := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [ggLAut_congr K θ (θ.trans e) ⟨b, hNs hb⟩, he]
  exact hi

theorem card_actor_le_half_of_linear_two_cover
    {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (hd : 0 < d) (hF : Nat.card F = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* projectiveSL d F) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ β ∈ Set.range (conjAut d F),
      ∀ l, β (ψ l) = ψ (α l)) : Nat.card A ≤ 3 ^ (d / 2) := by
  have hAI' : ∀ α ∈ A, ∃ β : MulAut (projectiveSL d F),
      ∀ l, β (ψ l) = ψ (α l) := by
    intro α hα
    obtain ⟨β, -, hβ⟩ := hAI α hα
    exact ⟨β, hβ⟩
  have hE := TypeA.isElemAbelian_inducedSub hψ hA
  have hEI : (TypeA.inducedSub ψ A : Set (MulAut (projectiveSL d F))) ⊆
      Set.range (conjAut d F) := by
    intro β hβ
    obtain ⟨α, hα, hβα⟩ := hβ
    obtain ⟨β', hβ', hβ'α⟩ := hAI α hα
    have heq : β = β' := TypeA.induced_unique ψ hψ hβα hβ'α
    rwa [heq]
  have hb := TwoThree.card_le_pow_half hE
    (TwoThree.card_sq_le_of_subset_conjAut hF hd hE hEI)
  rwa [TypeA.card_inducedSub hψ hker hperf hAI'] at hb

theorem twelve_le_dim_of_tableB_linear_two
    {F : Type} [Field F] [Finite F] [CharP F 2] {d r : ℕ}
    (hd : 0 < d) (hF : Nat.card F = 2) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL d F} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 r (projectiveSL d F) (Set.range (conjAut d F)) L' ψ A)
    (hcard : 3 ^ 6 ≤ Nat.card A) : 12 ≤ d := by
  have hb := card_actor_le_half_of_linear_two_cover hd hF ψ
    hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 hTB.2.2.2.2.1
  have hr : 6 ≤ d / 2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp (hcard.trans hb)
  omega

theorem native_linear_equiv_of_innerDiagOnLabel
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8)
    (hz : z ∈ Bs) (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → lab.tag = .A ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) :
    ∃ (d : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (θ : K ⧸ Subgroup.center K ≃* projectiveSL d F) (e : K ≃* projectiveSL d F),
      12 ≤ d ∧ Nat.card F = 2 ∧ (∀ k, e k = ggQuotHom θ k) ∧
        ∀ α ∈ (ggGamma K hN).range, MulAut.congr e α ∈ Set.range (conjAut d F) := by
  obtain ⟨d, F, hfield, hfin, hchar, hNs, θ, hd, hF, hperf, hinner⟩ :=
    linear_two_data_of_innerDiagOnLabel hS hK
  letI : Field F := hfield
  letI : Finite F := hfin
  letI : CharP F 2 := hchar
  have hAr := P9_Wa_card_range hBs hcard hz hz1 hN hker
  have hTB : GGTorusTBGroup 3 (n - 1) (projectiveSL d F) (Set.range (conjAut d F)) K
      (ggQuotHom θ) (ggGamma K hN).range := by
    refine ggTorusTBGroup_of_marking Nat.prime_three hBs hBstar hperf θ hN
      (fun b hb => ?_) (by rw [hAr]) ?_
    · simpa only using hinner b hb
    · rw [hAr]
      exact Nat.pow_le_pow_right (by norm_num) (by rcases hn with rfl | rfl <;> norm_num)
  have hA6 : 3 ^ 6 ≤ Nat.card (ggGamma K hN).range := by
    rw [hAr]
    exact Nat.pow_le_pow_right (by norm_num) (by rcases hn with rfl | rfl <;> norm_num)
  have hd12 := twelve_le_dim_of_tableB_linear_two (by omega) hF hTB hA6
  let e := MulEquiv.ofBijective (ggQuotHom θ)
    (bijective_of_surjective_projectiveSL_of_card_two (by omega : 5 ≤ d) hF
      (ggQuotHom θ) hTB.1 hTB.2.1 hTB.2.2.1)
  have he : ∀ k, e k = ggQuotHom θ k := fun _ => rfl
  refine ⟨d, F, hfield, hfin, hchar, θ, e, hd12, hF, he, fun α hα => ?_⟩
  obtain ⟨β, hβ, hβα⟩ := hTB.2.2.2.2.1 α hα
  have heq : MulAut.congr e α = β := by
    ext x
    obtain ⟨k, rfl⟩ := e.surjective x
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [he, he, hβα]
  rwa [heq]

end CFSG.StandardType.FrameRoute

end
