module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem w6X_rootDiagUnit_mem_graphFixed
    {K : Type} [Field K] {σ : K →+* K}
    {t : Fin 6 → Kˣ} (ht : t ∈ TableB.TwE6.torus₀ σ) :
    rootDiagUnit TwistTag.E6.tag t ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨s, hs, rfl⟩ := ht
  exact TableB.TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs

private theorem w6X_rootDiagUnit_mem_sup
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {bd : Fin 6 → Kˣ} (hbd : bd ∈ TableB.TwE6.compat σ)
    (hbdT : bd ∉ TableB.TwE6.torus₀ σ) {d : ModGL TwistTag.E6.tag K}
    (hroot : rootDiagUnit TwistTag.E6.tag bd ∈
      graphFixedRootGroup TwistTag.E6 K σ ⊔ Subgroup.zpowers d)
    {b : Fin 6 → Kˣ} (hb : b ∈ TableB.TwE6.compat σ) :
    rootDiagUnit TwistTag.E6.tag b ∈
      graphFixedRootGroup TwistTag.E6 K σ ⊔ Subgroup.zpowers d := by
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ := TableB.TwE6.exists_mul_inv_pow_mem hq hK hσ hb hbd hbdT
  have hsplit : b = (b * (bd ^ k)⁻¹) * bd ^ k := by group
  have hdecomp : rootDiagUnit TwistTag.E6.tag b =
      rootDiagUnit TwistTag.E6.tag (b * (bd ^ k)⁻¹) *
        (rootDiagUnit TwistTag.E6.tag bd) ^ k := by
    calc rootDiagUnit TwistTag.E6.tag b
        = rootDiagUnit TwistTag.E6.tag ((b * (bd ^ k)⁻¹) * bd ^ k) :=
          congrArg (fun w => rootDiagUnit TwistTag.E6.tag w) hsplit
      _ = rootDiagUnit TwistTag.E6.tag (b * (bd ^ k)⁻¹) *
            rootDiagUnit TwistTag.E6.tag (bd ^ k) := rootDiagUnit_mul _ _
      _ = rootDiagUnit TwistTag.E6.tag (b * (bd ^ k)⁻¹) *
            (rootDiagUnit TwistTag.E6.tag bd) ^ k :=
          congrArg (fun z => rootDiagUnit TwistTag.E6.tag (b * (bd ^ k)⁻¹) * z)
            (rootDiagUnit_pow (τ := TwistTag.E6.tag) bd k).symm
  rw [hdecomp]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (w6X_rootDiagUnit_mem_graphFixed hk))
    (Subgroup.pow_mem _ hroot k)

section Index

theorem twInndiag_eq_sup_zpowers
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {d : ModGL TwistTag.E6.tag K} (hd : d ∈ RecipeExcLang.twInndiagGroup K σ)
    (hd0 : d ∉ graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    RecipeExcLang.twInndiagGroup K σ =
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom ⊔ Subgroup.zpowers d := by
  classical
  set C0 := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC0
  set H := C0 ⊔ Subgroup.zpowers d with hH
  have hC0Γ : C0 ≤ RecipeExcLang.twInndiagGroup K σ := by
    rw [hC0]
    exact RecipeExcLang.graphFixedRootGroup_le_twInndiag σ
  have hHle : H ≤ RecipeExcLang.twInndiagGroup K σ := by
    rw [hH]
    exact sup_le hC0Γ (Subgroup.zpowers_le.2 hd)
  refine le_antisymm ?_ hHle
  set L := AlgebraicClosure K
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK2
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨bd, hbd, cd, hcd, hdec⟩ := RecipeExcLang.exists_decomp_of_mem_twInndiag hn hK
    (σ := σ) hσ (L := L) (Fr := iterateFrobenius L 2 n)
    (fun c => by rw [iterateFrobenius_def]) hd
  have hbd' : bd ∈ TableB.TwE6.compat σ.toRingHom :=
    (TableB.TwE6.mem_compat σ.toRingHom).2 hbd
  have hbdT : bd ∉ TableB.TwE6.torus₀ σ.toRingHom := by
    intro hmem
    apply hd0
    rw [hdec]
    exact Subgroup.mul_mem _ (w6X_rootDiagUnit_mem_graphFixed hmem) hcd
  have hroot : rootDiagUnit TwistTag.E6.tag bd ∈ H := by
    have hdH : d ∈ H := by
      rw [hH]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    have hcdH : cd ∈ H := by
      rw [hH]
      exact Subgroup.mem_sup_left hcd
    have hbdeq : rootDiagUnit TwistTag.E6.tag bd = d * cd⁻¹ := by rw [hdec]; group
    rw [hbdeq]
    exact Subgroup.mul_mem _ hdH (Subgroup.inv_mem _ hcdH)
  refine (Subgroup.closure_le H).2 ?_
  rintro w (hw | ⟨b, hb, rfl⟩)
  · rw [hH]
    exact Subgroup.mem_sup_left hw
  · rw [hH] at hroot ⊢
    exact w6X_rootDiagUnit_mem_sup hn hK (σ := σ.toRingHom) hσ hbd' hbdT hroot
      ((TableB.TwE6.mem_compat σ.toRingHom).2 hb)

end Index

end CFSG.StandardType.TableCRes

end
