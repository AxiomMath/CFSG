module

public import CFSG.LocalAnalysis.StandardType.GGTorusFieldTransferSh
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldShInputs
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.ToralCentralizerBruhat
import CFSG.LieType.Chevalley.BorelStructure
import CFSG.LocalAnalysis.StandardType.GGNbrKGF4ThreeAddHolds
import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldE6TwE6
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial

open TableB NbrInnerRest

@[expose] def ggF4Sh_set
    (K : Type) [Field K] [Finite K] : Set (MulAut (TableBF4.RecipeGroup K)) :=
  {φ | ∃ e : TableBF4.RecipeGroup K, ggF4Sh_A2A2 (TableBF4.recipeEquiv K e) ∧
    φ = (MulAut.conj e : MulAut (TableBF4.RecipeGroup K))}

theorem ggF4Sh_A2A2_baseChange
    {k K : Type} [Field k] [Field K] (ι : k →+* K) {y : adjointGroup Tag.F4 k}
    {z : adjointGroup Tag.F4 K}
    (hz : (z : ModGL Tag.F4 K) = baseChangeGL ι (y : ModGL Tag.F4 k))
    (hy : ggF4Sh_A2A2 y) : ggF4Sh_A2A2 z := by
  classical
  obtain ⟨g, hg, a, ha3, h12, hga⟩ := hy
  letI : Algebra k (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp ι).toAlgebra
  let ῑ : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  have hcomp : (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).comp
      (algebraMap k (AlgebraicClosure k)) = (algebraMap K (AlgebraicClosure K)).comp ι := by
    ext x
    exact ῑ.commutes x
  refine ⟨baseChangeGL (ῑ : AlgebraicClosure k →+* AlgebraicClosure K) g,
    TableBExcTwo.baseChangeGL_mem_adjointGroup _ hg,
    fun i => Units.map (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).toMonoidHom (a i),
    fun i => ?_, ?_, ?_⟩
  · rw [← map_pow, ha3 i, map_one]
  · have hker : rootCharKernel (τ := Tag.F4)
        (fun i => Units.map (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).toMonoidHom (a i)) =
        rootCharKernel (τ := Tag.F4) a := by
      ext v
      simp only [rootCharKernel, Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      have hv : rootChar (fun i => Units.map (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).toMonoidHom
          (a i)) v = Units.map (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).toMonoidHom
            (rootChar a v) := by
        simp [rootChar, map_prod, map_zpow]
      rw [hv]
      constructor
      · intro h
        exact Units.map_injective (f := (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).toMonoidHom)
          (ῑ : AlgebraicClosure k →+* AlgebraicClosure K).injective (by rw [h, map_one])
      · intro h
        rw [h, map_one]
    rw [hker]
    exact h12
  · rw [hz, CFSG.SeitzReduction.F4Pilot.baseChangeGL_baseChangeGL, ← hcomp,
      ← CFSG.SeitzReduction.F4Pilot.baseChangeGL_baseChangeGL, hga, map_mul, map_mul, map_inv,
      baseChangeGL_rootDiagUnit]

theorem ggF4Sh_weylIrred_of_notA2A2
    (K : Type) [Field K] [Finite K] [CharP K 2] (hpq : 3 ∣ Nat.card K + 1)
    (E : Subgroup (TableBF4.RecipeGroup K)) (hE : IsElemAbelian 3 E) (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ g : TableBF4.RecipeGroup K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    (hline : ∃ e ∈ E, e ≠ 1 ∧ ¬ ggF4Sh_A2A2 (TableBF4.recipeEquiv K e)) :
    GGWeylIrred E := by
  classical
  let f : TableBF4.RecipeGroup K ≃* adjointGroup Tag.F4 K := TableBF4.recipeEquiv K
  let E' : Subgroup (adjointGroup Tag.F4 K) := E.map f.toMonoidHom
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE f.toMonoidHom
  have hcard' : 3 ^ 3 ≤ Nat.card E' := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hcard
  have hSC' : ∀ x ∈ Subgroup.centralizer (E' : Set (adjointGroup Tag.F4 K)),
      x ^ 3 = 1 → x ∈ E' := by
    intro x hx hx3
    have hx' : f.symm x ∈ E := by
      refine hSC (f.symm x) ?_ ?_
      · intro e he
        have h := (Subgroup.mem_centralizer_iff.1 hx) (f e)
          (Subgroup.mem_map_of_mem f.toMonoidHom he)
        apply f.injective
        rw [map_mul, map_mul, f.apply_symm_apply]
        exact h.symm
      · have hmap : (f.symm x) ^ 3 = f.symm (x ^ 3) := (map_pow f.symm x 3).symm
        rw [hmap, hx3, map_one]
    exact Subgroup.mem_map.mpr ⟨f.symm x, hx', f.apply_symm_apply x⟩
  obtain ⟨e, he, he1, hne⟩ := hline
  have he' : f e ∈ E' := Subgroup.mem_map_of_mem f.toMonoidHom he
  have he1' : f e ≠ 1 := fun h => he1 (f.injective (by rw [h, map_one]))
  have htor := ggF4Sh_toral_of_notA2A2 K hpq E' hE' (f e) he' he1' hne
  have hwirr := Irred937.f4_weylIrred_of_toral K hpq E' hE' htor hcard' hSC'
  have hthis := ggWeylIrred_map f.symm hwirr
  have hEE : (E.map f.toMonoidHom).map f.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  rwa [hEE] at hthis

private theorem ggF4ShAux_conj_mem_zpowers {G : Type} [Group G] {a c x : G}
    (hca : c * a * c⁻¹ ∈ Subgroup.zpowers a) (hx : x ∈ Subgroup.zpowers a) :
    c * x * c⁻¹ ∈ Subgroup.zpowers a := by
  have hmap : (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom ≤ Subgroup.zpowers a := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
    change (MulAut.conj c) a ∈ Subgroup.zpowers a
    rw [MulAut.conj_apply]
    exact hca
  have h1 : (MulAut.conj c).toMonoidHom x ∈ Subgroup.zpowers a :=
    hmap (Subgroup.mem_map_of_mem _ hx)
  change (MulAut.conj c) x ∈ Subgroup.zpowers a at h1
  rw [MulAut.conj_apply] at h1
  exact h1

theorem ggF4Sh_noLineSh
    (K : Type) [Field K] [Finite K] [CharP K 2] (hpq : 3 ∣ Nat.card K + 1) :
    GGTorusNoLineSh 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) (ggF4Sh_set K) := by
  classical
  haveI : Finite (adjointGroup Tag.F4 K) := Subtype.finite
  haveI : Finite (TableBF4.RecipeGroup K) :=
    Finite.of_equiv (adjointGroup Tag.F4 K) (TableBF4.recipeEquiv K).toEquiv.symm
  have hZ : Subgroup.center (TableBF4.RecipeGroup K) = ⊥ := TableBF4.center_recipeGroup_eq_bot K
  have hIp : ∀ φ ∈ TableBF4.RecipeID K, φ ^ 3 = 1 →
      φ ∈ Set.range (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)) :=
    fun φ hφ _ => TableBF4.idImage_subset_inn K hφ
  have hcp : GGCenterPrime 3 (TableBF4.RecipeGroup K) :=
    ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num)
  have hp : Nat.Prime 3 := Nat.prime_three
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : (TableBF4.RecipeGroup K) →* MulAut L',
      (∀ {e : (TableBF4.RecipeGroup K)} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ 3 = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup (TableBF4.RecipeGroup K) := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : (TableBF4.RecipeGroup K), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set (TableBF4.RecipeGroup K)) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set (TableBF4.RecipeGroup K)) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2 : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_⟩
  ·
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  · intro hN a₀ ha₀ ha₀ne
    by_contra hcon0
    rw [not_or] at hcon0
    obtain ⟨hnotSh, hcon⟩ := hcon0
    have hcon' : ∀ n ∈ {n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))},
        MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∈ Subgroup.zpowers a₀ := by
      intro n hn
      by_contra hnot
      exact hcon ⟨n, hn, hnot⟩
    obtain ⟨e₀, he₀⟩ := hAΛ a₀ ha₀
    have he₀E : e₀ ∈ E := by
      rw [hE, Subgroup.mem_comap, he₀]
      exact ha₀
    have he₀ne : e₀ ≠ 1 := fun h1 => ha₀ne (by rw [← he₀, h1, map_one])
    have hlineE : ∃ e ∈ E, e ≠ 1 ∧ ¬ ggF4Sh_A2A2 (TableBF4.recipeEquiv K e) := by
      refine ⟨e₀, he₀E, he₀ne, fun hA => hnotSh ⟨MulAut.conj e₀, ⟨e₀, hA, rfl⟩, fun l => ?_⟩⟩
      rw [MulAut.conj_apply, ← he₀, hΛmap]
    have hirr : GGWeylIrred E :=
      ggF4Sh_weylIrred_of_notA2A2 K hpq E hEab (by rw [hcardE]; exact hr) hscE hlineE
    set E' : Subgroup (TableBF4.RecipeGroup K) := (Subgroup.zpowers a₀).comap Λ with hE'
    have hE'E : E' ≤ E := fun e he => (Subgroup.zpowers_le.mpr ha₀) he
    have hinvE : ∀ g ∈ Subgroup.normalizer (E : Set (TableBF4.RecipeGroup K)), ∀ e ∈ E', g * e * g⁻¹ ∈ E' := by
      intro g hg e he
      obtain ⟨n, rfl⟩ := hψ g
      have h1 := ggF4ShAux_conj_mem_zpowers (hcon' n (hnorm_to n hg)) he
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
      exact h1
    rcases hirr E' hE'E hinvE with hbot | htop
    · have he₀E' : e₀ ∈ E' := by
        rw [hE', Subgroup.mem_comap, he₀]
        exact Subgroup.mem_zpowers a₀
      rw [hbot, Subgroup.mem_bot] at he₀E'
      exact he₀ne he₀E'
    · have hcardE' : Nat.card E' ≤ 3 := by
        have hcard_zp : Nat.card (Subgroup.zpowers a₀) ≤ 3 := by
          rw [Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.2 a₀ ha₀))
        have hle : Nat.card E' ≤ Nat.card (Subgroup.zpowers a₀) :=
          Nat.card_le_card_of_injective (fun e : E' => (⟨Λ e, e.2⟩ : Subgroup.zpowers a₀))
            (fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)))
        exact le_trans hle hcard_zp
      have h27 : 27 ≤ Nat.card E' := by
        have h : 3 ^ 3 ≤ Nat.card E' := by rw [htop, hcardE]; exact h3
        norm_num at h
        exact h
      omega

private def ggF4Sh_FixOn
    (K : Type) [Field K] [Finite K] (S : (Fin Tag.F4.rank → ℤ) → Prop) (n p : ℕ) : Prop :=
  ∀ f ∈ RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH Tag.F4.cartan S K false),
    orderOf f = p →
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* K)
        (Φ : LargeEvenCenterQuot (MarkChev.chevH Tag.F4.cartan S K false) ≃* adjointGroup Tag.F4 K),
        Nat.card k = 2 ^ (n / p) ∧
        (ggFixSub f).map Φ.toMonoidHom = (TableBExcTwo.adjointMap Tag.F4 ι).range

private theorem ggF4Sh_FixOn_isRoot
    (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : 0 < p) : ggF4Sh_FixOn K (IsRoot Tag.F4) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.F4) K), H = adjointGroup Tag.F4 K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot Tag.F4) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* K)
          (Φ : LargeEvenCenterQuot H ≃* adjointGroup Tag.F4 K),
          Nat.card k = 2 ^ (n / p) ∧
          (ggFixSub f).map Φ.toMonoidHom = (TableBExcTwo.adjointMap Tag.F4 ι).range from
    h _ (chevH_false_eq_adjointGroup K Tag.F4)
  intro H hH f hf hford
  subst hH
  have hr : 0 < Tag.F4.rank := by decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  haveI : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK σ
  rw [hσp] at hdvd hcard
  have hτ' : Tag.F4 = .G2 ∨ Tag.F4 = .F4 ∨ Tag.F4 = .D4 ∨ Tag.F4 = .E7 ∨ Tag.F4 = .E8 :=
    Or.inr (Or.inl rfl)
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut Tag.F4 σ) =
      (fixedFieldImage Tag.F4 σ).subgroupOf (adjointGroup Tag.F4 K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup Tag.F4 σ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two hτ' hchar σ]
  let m : LargeEvenCenterQuot (adjointGroup Tag.F4 K) ≃* adjointGroup Tag.F4 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup Tag.F4 K)) * entrywiseAdjointAut Tag.F4 σ * 1⁻¹)
      (m x) = m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  refine ⟨↥(fixSubfield σ), inferInstance, inferInstance, (fixSubfield σ).subtype, m, ?_, ?_⟩
  · rw [hcard]
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have h1 : entrywiseAdjointAut Tag.F4 σ (m g) = m g := by
        have := key g
        simp only [one_mul, inv_one, mul_one] at this
        rw [this, show f g = g from hg]
      have h2 : m g ∈ ggAutFixedSubgroup (entrywiseAdjointAut Tag.F4 σ) := h1
      rw [hfix] at h2
      obtain ⟨y, hy, hyx⟩ := h2
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨y, rfl⟩
      have hx : entrywiseAdjointAut Tag.F4 σ
          (TableBExcTwo.adjointMap Tag.F4 (fixSubfield σ).subtype y) =
          TableBExcTwo.adjointMap Tag.F4 (fixSubfield σ).subtype y := by
        have h2 : TableBExcTwo.adjointMap Tag.F4 (fixSubfield σ).subtype y ∈
            ggAutFixedSubgroup (entrywiseAdjointAut Tag.F4 σ) := by
          rw [hfix]
          exact ⟨y, y.2, rfl⟩
        exact h2
      refine ⟨m.symm (TableBExcTwo.adjointMap Tag.F4 (fixSubfield σ).subtype y), ?_, by simp⟩
      change f _ = _
      apply m.injective
      rw [← key, MulEquiv.apply_symm_apply]
      simpa using hx

private theorem ggF4Sh_FixOn_recipe
    (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : 0 < p) {f : MulAut (TableBF4.RecipeGroup K)}
    (hf : f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false))
    (hord : orderOf f = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* K)
      (Φ : TableBF4.RecipeGroup K ≃* adjointGroup Tag.F4 K),
      Nat.card k = 2 ^ (n / p) ∧
      (ggFixSub f).map Φ.toMonoidHom = (TableBExcTwo.adjointMap Tag.F4 ι).range := by
  have h : ggF4Sh_FixOn K (LargeEvenIsRoot Tag.F4.cartan) n p := by
    have h0 := ggF4Sh_FixOn_isRoot K hn hK hp
    rwa [← largeEvenIsRoot_eq_isRoot Tag.F4] at h0
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.F4.cartan K),
      H = MarkChev.chevH Tag.F4.cartan (LargeEvenIsRoot Tag.F4.cartan) K false →
      ∀ f ∈ LargeEvenChevFieldImage Tag.F4.cartan K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* K)
          (Φ : LargeEvenCenterQuot H ≃* adjointGroup Tag.F4 K),
          Nat.card k = 2 ^ (n / p) ∧
          (ggFixSub f).map Φ.toMonoidHom = (TableBExcTwo.adjointMap Tag.F4 ι).range from
    key _ (largeEvenChevH_eq Tag.F4.cartan K false) f hf hord
  intro H hH
  subst hH
  exact h

theorem ggF4Sh_fixStd_explicit
    (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {f : MulAut (TableBF4.RecipeGroup K)}
    (hf : f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false))
    (hord : orderOf f = 3) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* K)
      (Φ : TableBF4.RecipeGroup K ≃* adjointGroup Tag.F4 K)
      (θ₀ : ggFixDer f ≃* TableBF4.RecipeGroup k),
      Nat.card k = 2 ^ (n / 3) ∧ ggFixDer f = ggFixSub f ∧
      ∀ g : ggFixDer f, (Φ (g : TableBF4.RecipeGroup K) : ModGL Tag.F4 K) =
        baseChangeGL ι ((TableBF4.recipeEquiv k (θ₀ g) : adjointGroup Tag.F4 k) : ModGL Tag.F4 k) := by
  classical
  obtain ⟨k, _, _, ι, Φ, hcard, himg⟩ := ggF4Sh_FixOn_recipe K hn hK (by norm_num : 0 < 3) hf hord
  have hq := chev_isQuasisimple (τ := .F4) (Or.inl rfl) k
  obtain ⟨eR⟩ := centerQuot_chevGroup_equiv k .F4
  have hsimple : IsSimpleGroup (TableBF4.RecipeGroup k) := by
    haveI : IsSimpleGroup (AdjointQuotient Tag.F4 k) := hq.2.1
    exact eR.isSimpleGroup
  have hnab : ∃ a b : TableBF4.RecipeGroup k, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨eR.symm a, eR.symm b, fun h' => hab (eR.symm.injective (by rw [map_mul, map_mul]; exact h'))⟩
  let e1 : ↥(ggFixSub f) ≃* ↥((ggFixSub f).map Φ.toMonoidHom) :=
    (ggFixSub f).equivMapOfInjective Φ.toMonoidHom Φ.injective
  let e2 : ↥((ggFixSub f).map Φ.toMonoidHom) ≃* ↥(TableBExcTwo.adjointMap Tag.F4 ι).range :=
    MulEquiv.subgroupCongr himg
  let e3 : ↥(TableBExcTwo.adjointMap Tag.F4 ι).range ≃* adjointGroup Tag.F4 k :=
    (MonoidHom.ofInjective (TableBExcTwo.adjointMap_injective ι)).symm
  let E' : TableBF4.RecipeGroup k ≃* ↥(ggFixSub f) :=
    (TableBF4.recipeEquiv k).trans (e3.symm.trans (e2.symm.trans e1.symm))
  have hder : ggFixDer f = ggFixSub f := ggFixDer_eq_ggFixSub hnab f E'
  refine ⟨k, inferInstance, inferInstance, ι, Φ, (MulEquiv.subgroupCongr hder).trans E'.symm,
    hcard, hder, ?_⟩
  intro g
  have hmem : (g : TableBF4.RecipeGroup K) ∈ ggFixSub f := by
    rw [← hder]
    exact g.2
  have hθ : TableBF4.recipeEquiv k ((MulEquiv.subgroupCongr hder).trans E'.symm g) =
      e3 (e2 (e1 ⟨g, hmem⟩)) := by
    simp [E']
    rfl
  rw [hθ]
  have h4 : TableBExcTwo.adjointMap Tag.F4 ι (e3 (e2 (e1 ⟨g, hmem⟩))) = e2 (e1 ⟨g, hmem⟩) :=
    MonoidHom.apply_ofInjective_symm _ _
  have h5 := congrArg (fun z : adjointGroup Tag.F4 K => (z : ModGL Tag.F4 K)) h4
  exact h5.symm

theorem ggF4Sh_fixGeom {R R₀ : Type} [Group R] [Group R₀] {I : Set (MulAut R)}
    {I₀ : Set (MulAut R₀)} {f : MulAut R} (hZ : Subgroup.center R = ⊥)
    (hZ₀ : Subgroup.center R₀ = ⊥) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hI₀ : Set.range (MulAut.conj : R₀ →* MulAut R₀) ⊆ I₀) (hder : ggFixDer f = ggFixSub f)
    (θ₀ : ggFixDer f ≃* R₀) : GGFixGeom I f I₀ θ₀ := by
  have key : ∀ g : R, MulAut.conj g * f = f * MulAut.conj g → f g = g := by
    intro g hg
    have h1 : ∀ y : R, g * f y * g⁻¹ = f g * f y * (f g)⁻¹ := by
      intro y
      have h := congrArg (fun α : MulAut R => α y) hg
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h
    have hcomm : ∀ y : R, ((f g)⁻¹ * g) * f y = f y * ((f g)⁻¹ * g) := by
      intro y
      calc (f g)⁻¹ * g * f y
          = (f g)⁻¹ * (g * f y * g⁻¹) * g := by group
        _ = (f g)⁻¹ * (f g * f y * (f g)⁻¹) * g := by rw [h1 y]
        _ = f y * ((f g)⁻¹ * g) := by group
    have hz : (f g)⁻¹ * g = 1 := by
      have hmem : (f g)⁻¹ * g ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro u
        obtain ⟨y, rfl⟩ := f.surjective u
        exact (hcomm y).symm
      rwa [hZ, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hz
  refine ⟨?_, ?_⟩
  · intro φ hφI hφ
    obtain ⟨g, rfl⟩ := hI hφI
    have hg : g ∈ ggFixDer f := by
      rw [hder, mem_ggFixSub]
      exact key g hφ
    refine ⟨MulAut.conj (θ₀ ⟨g, hg⟩), hI₀ ⟨θ₀ ⟨g, hg⟩, rfl⟩, fun x hx => ?_⟩
    have h1 : (⟨MulAut.conj g x, ggFixDer_map_mem hφ hx⟩ : ggFixDer f) =
        ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  · intro φ hφI hφ htriv
    obtain ⟨g, rfl⟩ := hI hφI
    have hg : g ∈ ggFixDer f := by
      rw [hder, mem_ggFixSub]
      exact key g hφ
    have hcomm : ∀ v : R₀, v * θ₀ ⟨g, hg⟩ = θ₀ ⟨g, hg⟩ * v := by
      intro v
      obtain ⟨x, rfl⟩ := MulEquiv.surjective θ₀ v
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have he : g * x.val * g⁻¹ = x.val := htriv x.val x.2
      have hxg : x.val * g = g * x.val := by
        simpa [mul_assoc] using (congrArg (fun t => t * g) he).symm
      exact hxg
    have h1 : θ₀ ⟨g, hg⟩ = 1 := by
      have hmem : θ₀ ⟨g, hg⟩ ∈ Subgroup.center R₀ := by
        rw [Subgroup.mem_center_iff]
        exact hcomm
      rwa [hZ₀, Subgroup.mem_bot] at hmem
    have h2 : (⟨g, hg⟩ : ggFixDer f) = 1 :=
      θ₀.injective (by rw [h1, map_one])
    have hg1 : g = 1 := congrArg Subtype.val h2
    simpa [hg1]

theorem ggF4Sh_notCyc
    {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k] [Finite k] (ι : k →+* K)
    (hq : 3 ∣ Nat.card K + 1) (hq2 : 2 < Nat.card K)
    (Φ : TableBF4.RecipeGroup K ≃* adjointGroup Tag.F4 K) {f : MulAut (TableBF4.RecipeGroup K)}
    (hder : ggFixDer f = ggFixSub f) (θ₀ : ggFixDer f ≃* TableBF4.RecipeGroup k)
    (hθ : ∀ g : ggFixDer f, (Φ (g : TableBF4.RecipeGroup K) : ModGL Tag.F4 K) =
      baseChangeGL ι ((TableBF4.recipeEquiv k (θ₀ g) : adjointGroup Tag.F4 k) : ModGL Tag.F4 k)) :
    GGFixNotCycOn 3 (TableBF4.RecipeID K) f θ₀ (ggF4Sh_set k) := by
  intro φ hφI hφ φ₀ hφ₀ hres
  obtain ⟨g₁, rfl⟩ := TableBF4.idImage_subset_inn K hφI
  have hZ := TableBF4.center_recipeGroup_eq_bot K
  have hZk := TableBF4.center_recipeGroup_eq_bot k
  have key : f g₁ = g₁ := by
    have h1 : ∀ y : TableBF4.RecipeGroup K, g₁ * f y * g₁⁻¹ = f g₁ * f y * (f g₁)⁻¹ := by
      intro y
      have h := congrArg (fun α : MulAut (TableBF4.RecipeGroup K) => α y) hφ
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h
    have hcomm : ∀ y : TableBF4.RecipeGroup K, ((f g₁)⁻¹ * g₁) * f y = f y * ((f g₁)⁻¹ * g₁) := by
      intro y
      calc (f g₁)⁻¹ * g₁ * f y
          = (f g₁)⁻¹ * (g₁ * f y * g₁⁻¹) * g₁ := by group
        _ = (f g₁)⁻¹ * (f g₁ * f y * (f g₁)⁻¹) * g₁ := by rw [h1 y]
        _ = f y * ((f g₁)⁻¹ * g₁) := by group
    have hz : (f g₁)⁻¹ * g₁ = 1 := by
      have hmem : (f g₁)⁻¹ * g₁ ∈ Subgroup.center (TableBF4.RecipeGroup K) := by
        rw [Subgroup.mem_center_iff]
        intro u
        obtain ⟨y, rfl⟩ := f.surjective u
        exact (hcomm y).symm
      rwa [hZ, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hz
  have hg : g₁ ∈ ggFixDer f := by
    rw [hder, mem_ggFixSub]
    exact key
  obtain ⟨e₀, he₀, rfl⟩ := hφ₀
  have hθe : θ₀ ⟨g₁, hg⟩ = e₀ := by
    have hconj : ∀ v : TableBF4.RecipeGroup k, θ₀ ⟨g₁, hg⟩ * v * (θ₀ ⟨g₁, hg⟩)⁻¹ = e₀ * v * e₀⁻¹ := by
      intro v
      obtain ⟨x, rfl⟩ := MulEquiv.surjective θ₀ v
      have h := hres x.1 x.2
      have h1 : (⟨MulAut.conj g₁ x.1, ggFixDer_map_mem hφ x.2⟩ : ggFixDer f) =
          ⟨g₁, hg⟩ * x * ⟨g₁, hg⟩⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv] at h
      exact h
    have hmem : e₀⁻¹ * θ₀ ⟨g₁, hg⟩ ∈ Subgroup.center (TableBF4.RecipeGroup k) := by
      rw [Subgroup.mem_center_iff]
      intro v
      have h := hconj v
      have h2 : θ₀ ⟨g₁, hg⟩ * v = e₀ * v * e₀⁻¹ * θ₀ ⟨g₁, hg⟩ := by
        rw [← h]; group
      calc v * (e₀⁻¹ * θ₀ ⟨g₁, hg⟩) = e₀⁻¹ * (e₀ * v * e₀⁻¹ * θ₀ ⟨g₁, hg⟩) := by group
        _ = e₀⁻¹ * (θ₀ ⟨g₁, hg⟩ * v) := by rw [h2]
        _ = e₀⁻¹ * θ₀ ⟨g₁, hg⟩ * v := by group
    rw [hZk, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  have hA : ggF4Sh_A2A2 (Φ g₁) := by
    refine ggF4Sh_A2A2_baseChange ι (y := TableBF4.recipeEquiv k e₀) ?_ he₀
    rw [← hθe]
    exact hθ ⟨g₁, hg⟩
  obtain ⟨g', hg', a, ha, h12, hga⟩ := hA
  have hB := Irred937.not_fixCompCyclic_of_a2a2 Irred937.f4ThreeA2A2TwoComponents_holds K hq hq2
    (Φ g₁) g' hg' a ha h12 hga
  exact fun h => hB ((Irred937.ggFixCompCyclic_conj_of_mulEquiv Φ g₁).mp h)

theorem ggF4Sh_rawFieldFixSh
    (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (h3n : 3 ∣ n)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGRawFieldFixSh 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false)) := by
  intro hs hna f hf hord
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ n := Nat.le_of_dvd (by omega) h3n
  have hKchar : CharP K 2 := charP_two_of_card hK
  have hK3 : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3
  have hKbig : 2 < Nat.card K := by
    rw [hK]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, _, _, ι, Φ, θ₀, hkcard, hder, hθ⟩ := ggF4Sh_fixStd_explicit K hn hK hf hord
  have hkchar : CharP k 2 := charP_two_of_card hkcard
  have hk3 : 3 ∣ Nat.card k + 1 := by
    rw [hkcard]
    have hmul : n = 3 * (n / 3) := (Nat.mul_div_cancel' h3n).symm
    rw [hmul] at h3
    exact CFSG.RankThree.PartOne.dvd_two_pow_add_one_of_mul Nat.prime_three h3
  have hq := chev_isQuasisimple (τ := .F4) (Or.inl rfl) k
  obtain ⟨eR⟩ := centerQuot_chevGroup_equiv k .F4
  have hsimple : IsSimpleGroup (TableBF4.RecipeGroup k) := by
    haveI : IsSimpleGroup (AdjointQuotient Tag.F4 k) := hq.2.1
    exact eR.isSimpleGroup
  have hnab : ∃ a b : TableBF4.RecipeGroup k, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨eR.symm a, eR.symm b, fun h' => hab (eR.symm.injective (by rw [map_mul, map_mul]; exact h'))⟩
  refine ⟨TableBF4.RecipeGroup k, inferInstance, TableBF4.RecipeID k, ggF4Sh_set k, θ₀, hsimple,
    hnab, ?_, ?_, ?_, ?_⟩
  · refine ggF4Sh_fixGeom (TableBF4.center_recipeGroup_eq_bot K)
      (TableBF4.center_recipeGroup_eq_bot k) (TableBF4.idImage_subset_inn K) ?_ hder θ₀
    rintro _ ⟨x, rfl⟩
    exact conj_mem_chevIDImage (LargeEvenChevH LargeEvenCartanF4 k false) x
  · exact ggTorusLift_F4Plus Nat.prime_three (by norm_num) hk3
  · exact ggF4Sh_noLineSh k hk3
  · exact ggF4Sh_notCyc ι hK3 hKbig Φ hder θ₀ hθ

theorem ggF4FieldShInput_holds
    (hpc : GGRawPCyclicOn GGNotD4Three) : GGF4FieldShInput := by
  intro lab hlab ht hd hdvd
  have hp : Nat.Prime 3 := Nat.prime_three
  have hnot : GGNotD4Three 3 lab := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hno : ¬ (lab.tag = .triD4 ∧ 3 = 3) := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    (hpc 3 hp (by norm_num) lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have h8 : LargeEvenLabelAll lab (GGRawFieldFixSh 3 3) := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨hn, -⟩ := hlab
    dsimp only at ht hd hdvd hn
    subst ht
    intro Q hQ
    exact recipeChevalley_and (fun K _ _ hK => ggF4Sh_rawFieldFixSh K hn hK hdvd hd) hQ
  exact (largeEvenLabelAll_and hcyc
    (largeEvenLabelAll_and (ggRawFieldConjInputExc_holds 3 hp (by norm_num) lab hlab hno)
      (largeEvenLabelAll_and (ggRawFieldCentralInput_of_triality plusFourTrialityInput_holds lab hlab)
        (largeEvenLabelAll_and (ggRawInnFieldInput_holds 3 hp (by norm_num) lab hlab) h8)))).mono
    fun _ _ _ _ ⟨hcy, hc, hce, hi, h8'⟩ hs hna =>
      ggRawFieldFixSh_all hc (ggRawFieldNorm_of_central hce hi hs hna) hcy h8' hs hna

end CFSG.StandardType
