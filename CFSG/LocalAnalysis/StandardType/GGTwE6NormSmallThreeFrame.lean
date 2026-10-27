module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlaneEnnola
public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeLang
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeTorus
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeCoord

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups


theorem exists_endNode_frame {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {X : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hX4 : 3 ^ 4 ≤ Nat.card X)
    (hXU : ∃ U : Subgroup (TwE6Delta.RecipeR K n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U)
    {x : MulAut (TwE6Delta.RecipeR K n)} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf (CFSG.Assembly.LargeEvenLayer (ggFix x)) (ggFix x))
    (hend : ∀ y ∈ X, (∀ j ∈ CFSG.Assembly.LargeEvenLayer (ggFix x), y j = j) →
      y ∈ Subgroup.zpowers x) :
    ∃ (emb : TwE6Delta.RecipeR K n →* ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (ζ : (AlgebraicClosure K)ˣ) (α : Fin TwistTag.E6.tag.rank → ℤ)
      (Ψ : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      Function.Injective emb ∧ IsPrimitiveRoot ζ 3 ∧ IsRoot TwistTag.E6.tag α ∧
      (∀ γ ∈ Ψ, IsRoot TwistTag.E6.tag γ) ∧
      (∀ γ, IsRoot TwistTag.E6.tag γ →
        ∃ r, emb r = rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL) ∧
      (∀ γ ∈ Ψ, ∃ s ∈ CFSG.Assembly.LargeEvenLayer (ggFix x),
        emb s = rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)) ∧
      (∀ φ ∈ X, ∃ c : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        (∀ k, c k ^ 3 = 1) ∧ rootChar c α = 1 ∧
        ∀ r, emb (φ r) = rootDiagUnit TwistTag.E6.tag c * emb r *
          (rootDiagUnit TwistTag.E6.tag c)⁻¹) ∧
      ∀ (H : Subgroup (TwE6Delta.RecipeR K n)) (u : TwE6Delta.RecipeR K n),
        (∀ γ ∈ Ψ, ∃ h ∈ H,
          rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) = emb h) →
        (∀ h ∈ H, ∀ c, rootDiagUnit TwistTag.E6.tag c = emb h → rootChar c α = 1 →
          u * h = h * u) →
        3 ^ 3 ≤ Nat.card ↥(H ⊓ Subgroup.centralizer {u}) := by
  classical
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : NeZero ((3 : ℕ) : AlgebraicClosure K) := ⟨fun h => absurd
    ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 3).1 h) (by norm_num)⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ 3 :=
    ⟨_, IsPrimitiveRoot.isUnit_unit (by norm_num) hζ0⟩
  obtain ⟨U, hU, hU2, hUX⟩ := hXU
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj hn hK
  haveI : Finite (TwE6Delta.RecipeR K n) := Finite.of_equiv _ ε.toEquiv
  have hXr : X ≤ (TwE6Transport.recipeConj σ ε).range := fun φ hφ => (hε φ).2 (hXI hφ)
  have hAI := TwE6Transport.recipeMat_le σ ε X
  have hA := TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hX
  have hA4 : 3 ^ 4 ≤ Nat.card (TwE6Transport.recipeMat σ ε X) := by
    rw [TwE6Transport.card_recipeMat σ ε hn hK hσ hXr]; exact hX4
  have hAU := TwE6Transport.twNormTwo_recipeMat σ ε hU hU2 hUX
  obtain ⟨D, hc, hv⟩ := TwE6FieldCore.exists_twLangData_ennola hK hσ h3 hAI hA hA4 hAU
  obtain ⟨α, hα, hαD⟩ := TwE6RootKill.rootKill_of_ennolaKill_weylKill
      (TwE6RootKill.ennolaKill_of_steps TwE6RootKill.leviSplitStep_holds
          TwE6RootKill.ennolaSplitStep_holds) TwE6RootKill.weylKill_holds K σ (2 ^ n) hK hσ (ringChar.eq K 2) 3
    Nat.prime_three h3 _ hAI hA (by rw [if_pos rfl]; exact hA4) hAU D
  obtain ⟨f, hf, hfi⟩ : ∃ f : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K),
      (∀ y, f y = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) y * D.g0) ∧
        Function.Injective f :=
    ⟨(MulAut.conj D.g0⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      fun y => by simp [MulAut.conj_apply],
      (MulAut.conj D.g0⁻¹).injective.comp (baseChangeGL_injective _)⟩
  have hkill : ∀ y ∈ TwE6Transport.recipeMat σ ε X, ∃ a, rootDiagUnit TwistTag.E6.tag a = f y ∧
      rootChar a α = 1 := fun y hy => by
    obtain ⟨a, ha, haα⟩ := hαD y hy
    exact ⟨a, by rw [ha, hc, hf, one_mul, inv_one, mul_one], haα⟩
  obtain ⟨w, rfl⟩ := hXr hx
  have htA : (w : ModGL TwistTag.E6.tag K) ∈ TwE6Transport.recipeMat σ ε X :=
    (TwE6Transport.mem_recipeMat σ ε).2 ⟨w.2, hx⟩
  have ht1 : (w : ModGL TwistTag.E6.tag K) ≠ 1 := fun h => hx1 (by
    rw [show w = 1 from Subtype.ext h, map_one])
  have hfix : ggFix (TwE6Transport.recipeConj σ ε w) =
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (RecipeExcLang.twConj K σ w)).map ε.toMonoidHom := by
    rw [Subgroup.map_equiv_eq_comap_symm']
    ext r
    rw [mem_ggFix, Subgroup.mem_comap, CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
      TwE6Transport.recipeConj_apply, MulEquiv.apply_eq_iff_symm_apply]
    rfl
  set J := CFSG.Assembly.LargeEvenLayer (ggFix (TwE6Transport.recipeConj σ ε w)) with hJ
  have hcomp' : CFSG.Assembly.IsComponentOf J ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (RecipeExcLang.twConj K σ w)).map ε.toMonoidHom) := by
    rw [← hfix]; exact hcomp
  obtain ⟨hQ, -⟩ := isComponentOf_comap_of_injective ε.toMonoidHom ε.injective hcomp'
  obtain ⟨S, ι, aT, i, hSD, hι, hrange, hιx, haT, hρ, hQi⟩ := exists_endNode_lang hK hσ D hc hv
    htA (hAI htA) (hA.2 _ htA) ht1 (β := RecipeExcLang.twConj K σ w)
    (fun c => RecipeExcLang.coe_twConj σ w c) (CFSG.Assembly.isComponentOf_iff_open.1 hQ)
  obtain ⟨emb, hemb, hembi⟩ : ∃ emb : TwE6Delta.RecipeR K n →*
      ModGL TwistTag.E6.tag (AlgebraicClosure K), (∀ r, emb r = ι (ε.symm r)) ∧
        Function.Injective emb :=
    ⟨ι.comp ε.symm.toMonoidHom, fun _ => rfl, hι.comp ε.symm.injective⟩
  have hconj : ∀ (w' : RecipeExcLang.twInndiagGroup K σ) (c : Fin TwistTag.E6.tag.rank →
      (AlgebraicClosure K)ˣ), rootDiagUnit TwistTag.E6.tag c = f w' → ∀ r,
      emb (TwE6Transport.recipeConj σ ε w' r) = rootDiagUnit TwistTag.E6.tag c * emb r *
        (rootDiagUnit TwistTag.E6.tag c)⁻¹ := fun w' c hcw r => by
    rw [hcw, hemb, hemb, TwE6Transport.recipeConj_apply, MulEquiv.symm_apply_apply, hιx, hιx,
      RecipeExcLang.coe_twConj, hf, map_mul, map_mul, map_inv]
    group
  have hJR : ∀ j ∈ J, emb j ∈ rationalComponent S.ρ S.Γ (rootCharHom aT) i := fun j hj => by
    have hj' : ε.symm j ∈ J.comap ε.toMonoidHom := by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hj
    rw [← hQi, hemb]
    exact Subgroup.mem_map_of_mem ι hj'
  refine ⟨emb, ζ, α, componentRoots (rootCharHom aT) i, hembi, hζ, hα,
    (isRootComponent_componentRoots i).isRoot, fun γ hγ => ?_, fun γ hγ => ?_, fun φ hφ => ?_,
    fun H u hH hu => ?_⟩
  ·
    have hW : rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL ∈ ι.range := by
      rw [hrange]; exact TwE6EltSmall.ennola_rootSL2_WSL_mem_Γ D hv S hSD hn hK hσ hγ
    obtain ⟨c, hc'⟩ := hW
    exact ⟨ε c, by rw [hemb, MulEquiv.symm_apply_apply, hc']⟩
  ·
    have hT := rootDiagUnit_corootTuple_mem_rationalComponent D hv S hSD hn hK hσ h3 hζ i hγ
    rw [← hQi] at hT
    obtain ⟨c, hcJ, hc'⟩ := hT
    exact ⟨ε c, hcJ, by rw [hemb, MulEquiv.symm_apply_apply, hc']⟩
  ·
    obtain ⟨w', rfl⟩ := hXr hφ
    have hw'A : (w' : ModGL TwistTag.E6.tag K) ∈ TwE6Transport.recipeMat σ ε X :=
      (TwE6Transport.mem_recipeMat σ ε).2 ⟨w'.2, hφ⟩
    obtain ⟨c, hcf, hcα⟩ := hkill _ hw'A
    refine ⟨c, fun k => ?_, hcα, hconj w' c hcf⟩
    have h3c : rootDiagUnit TwistTag.E6.tag (c ^ 3) = rootDiagUnit TwistTag.E6.tag 1 := by
      rw [← rootDiagUnit_pow, rootDiagUnit_one, hcf, ← map_pow, hA.2 _ hw'A, map_one]
    exact congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h3c) k
  ·
    refine three_pow_three_le_card_inf_centralizer hζ hfi hA hA4
      (fun y hy => (hkill y hy).imp fun _ h => h.1) hα (fun y hy c hcy => ?_) htA
      (haT.trans (hf _).symm) i (fun y hy hyΨ => ?_) hH hu
    · obtain ⟨a, ha, haα⟩ := hkill y hy
      rwa [CFSG.LieType.Chevalley.rootDiagUnit_injective (hcy.trans ha.symm)]
    · obtain ⟨hyΓ, hyX⟩ := (TwE6Transport.mem_recipeMat σ ε).1 hy
      obtain ⟨c, hcy, -⟩ := hkill y hy
      have hfixJ : ∀ j ∈ J, TwE6Transport.recipeConj σ ε ⟨y, hyΓ⟩ j = j := fun j hj => by
        apply hembi
        rw [hconj ⟨y, hyΓ⟩ c hcy j]
        have hle := LangRat.rationalComponent_le_centralizer S i (b := c)
          (by rw [LangRat.rationalRoots_eq_of_rho_neg S hρ i]; exact hyΨ c hcy)
        rw [Subgroup.mem_centralizer_iff.1 (hle (hJR j hj)) _ (Set.mem_singleton _),
          mul_inv_cancel_right]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hend _ hyX hfixJ)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have hwk : w ^ k = ⟨y, hyΓ⟩ :=
        TwE6Transport.recipeConj_injective σ ε hn hK hσ (by rw [map_zpow, hk])
      rw [← Subgroup.coe_zpow, hwk]

end CFSG.StandardType.TwE6NormThree

end
