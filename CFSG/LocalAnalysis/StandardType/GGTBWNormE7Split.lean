module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Split
public import CFSG.LocalAnalysis.StandardType.GGTorusE7Split
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.GroupTheory.SelfCentralizingMap

public noncomputable section

namespace CFSG.StandardType.E7WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.StandardType.TableBExc
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem eq_torusPow_of_le_of_selfCent {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hle : E ≤ torusPow τ K p)
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) : E = torusPow τ K p :=
  le_antisymm hle fun e he => hsc e (fun x hx => Subtype.ext
    (CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm he.1 (hle hx).1)) he.2


theorem exists_conj_eq_torusPow_of_selfCent {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) {E : Subgroup (adjointGroup .E7 K)}
    (hE : IsElemAbelian p E) (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ g : adjointGroup .E7 K, E.map (MulAut.conj g).toMonoidHom = torusPow .E7 K p := by
  obtain ⟨g, hg⟩ := ExcElemToral.exists_conj_le_torusPow_of_nonTorsion hp (by omega)
    (fun _ => by omega) (by intro h; cases h) hpq E hE
  refine ⟨g, eq_torusPow_of_le_of_selfCent ?_
    (CFSG.GroupTheory.selfCentralizing_map_mulEquiv (MulAut.conj g) hsc)⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hg x hx

theorem ggTorusWNormSC_recipe_E7_split {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusWNormSC p (RecipeGroup .E7 K) (RecipeID .E7 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, -, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E7 K)
      (fun _ hφ _ => idImage_subset_inn_E7 K hφ) (ExcSplitL.ggCenterPrime_recipe_E7 hf hK hp hp2)
      ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E7 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E :=
    CFSG.GroupTheory.selfCentralizing_map_mulEquiv ε hEsc
  obtain ⟨g, hg⟩ := exists_conj_eq_torusPow_of_selfCent hp hp5 hpq hEg hEgs
  obtain ⟨ζ, -, ι, hζo, hι, hιr, hsimple, hnorm⟩ := E7SplitTorus.exists_frame hp hp2 hpq
  let ψ1 : L →* adjointGroup .E7 K := (MulAut.conj g).toMonoidHom.comp (ε.toMonoidHom.comp ψ)
  let Λ1 : adjointGroup .E7 K →* MulAut L :=
    Λ₀.comp (ε.symm.toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom)
  have hψ1 : Function.Surjective ψ1 := (MulAut.conj g).surjective.comp (ε.surjective.comp hψ)
  have hker1 : ψ1.ker ≤ Subgroup.center L := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : ε (ψ l) = 1 := (MulAut.conj g).injective (by
      simpa only [ψ1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_one] using hl)
    exact ε.injective (by rw [h1, map_one])
  have hΛ1 : Function.Injective Λ1 :=
    hΛinj.comp (ε.symm.injective.comp (MulAut.conj g⁻¹).injective)
  have hcomp : Λ1.comp ((MulAut.conj g).toMonoidHom.comp ε.toMonoidHom) = Λ₀ := by
    refine MonoidHom.ext fun x => ?_
    simp only [Λ1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    congr 1
    rw [show g⁻¹ * (g * ε x * g⁻¹) * g⁻¹⁻¹ = ε x by group, MulEquiv.symm_apply_apply]
  have hΛψ1 : ∀ l, Λ1 (ψ1 l) = MulAut.conj l := by
    intro l
    have h1 := congrArg (fun F : RecipeGroup .E7 K →* MulAut L => F (ψ l)) hcomp
    simp only [MonoidHom.comp_apply] at h1
    exact h1.trans (hΛeq rfl)
  have hEA : (torusPow .E7 K p).map Λ1 = A := by
    rw [← hg, Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc, hcomp,
      Subgroup.map_comap_eq, inf_eq_right]
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    exact ⟨e, he⟩
  have hn : ∀ i, E7SplitTorus.simpleRep i ∈
      Subgroup.normalizer (torusPow .E7 K p : Set (adjointGroup .E7 K)) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hιr] at hx ⊢
      obtain ⟨s, rfl⟩ := hx
      rw [← ofAdd_toAdd s, hsimple]
      exact ⟨_, rfl⟩
    · intro hx
      rw [← hιr] at hx ⊢
      obtain ⟨s, hs⟩ := hx
      have hss : simple .E7 i * simple .E7 i = 1 := (coxeterSystem .E7).simple_mul_simple_self i
      have h1 := hsimple i (TableBExc.torusAct .E7 p (simple .E7 i) (Multiplicative.toAdd s))
      rw [← torusAct_mul, hss, torusAct_one, ofAdd_toAdd, hs] at h1
      exact ⟨_, mul_left_cancel (mul_right_cancel h1)⟩
  have hAut : ∀ β : MulAut (adjointGroup .E7 K),
      (∀ x, β x ∈ torusPow .E7 K p ↔ x ∈ torusPow .E7 K p) →
      ∃ (c : (ZMod p)ˣ) (u : WeylGroup .E7), ∀ v,
        β (ι (Multiplicative.ofAdd v)) =
          ι (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct .E7 p u v)) :=
    fun β hβ => ExcFrames.exists_scalar_weyl_of_mulAut_torusPow_E7E8 (Or.inl rfl) hp hζo ι hιr
      hnorm β hβ
  intro _ Γ _ _ M C V _ _ ι' φ h α _ _ _ _ hgen s hs
  exact ggWNormConcl_of_centralCover_weylFrame ψ1 hψ1 hker1 center_adjointGroup_eq_bot Λ1 hΛ1
    hΛψ1 (torusPow .E7 K p) A hEA ι hι hιr (fun i => E7SplitTorus.simpleRep i) hn hsimple hnorm
    hAut (by decide) (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inl rfl)) hp2)
    ι' φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E7_split {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E7)
    (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  have hf : 1 ≤ f := hlab.1
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E7_split hf hK hp hp5 (by rw [hK]; exact hpq)

end CFSG.StandardType.E7WNorm
