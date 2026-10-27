module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeFinite
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import Certificates.Certificate10050
import Certificates.Certificate8117

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.TwE6EndNode3
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (components_of_langSetup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (langSetup_hTame_of_prime)


theorem exists_killer_of_component {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p₀ : ℕ}
    (S : LangSetup Tag.E6 Ω p₀) (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ) (h3 : (3 : Ω) ≠ 0)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {v : Fin 6 → ZMod 3} (hv : v ≠ 0)
    (hT : rootDiagUnit Tag.E6 (zetaVec ζ hζ v) ∈ S.D.torus)
    {C : Type} [Group C] [Finite C] (ι : C →* ModGL Tag.E6 Ω) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) {β : MulAut C}
    (hβ : ∀ c, ι (β c) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * ι c * (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹)
    {J : Subgroup C} (hJ : CFSG.Assembly.IsComponentOf J (CFSG.StandardType.ggFix β))
    (hexcl : CubeExcl v) :
    ∃ u : Fin 6 → ZMod 3, u ≠ 0 ∧ u ≠ v ∧ u ≠ -v ∧
      ∀ c ∈ J, ι c * rootDiagUnit Tag.E6 (zetaVec ζ hζ u) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ u) * ι c := by
  classical
  obtain ⟨v, rfl⟩ : ∃ w : Fin Tag.E6.rank → ZMod 3, w = v := ⟨v, rfl⟩
  have hv' : v ≠ 0 := hv
  have hprim : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hζ hζ1)
  have hker : ∀ (w : Fin Tag.E6.rank → ZMod 3) (α : Fin Tag.E6.rank → ℤ),
      rootChar (zetaVec ζ hζ w) α = 1 ↔ KerP w α := fun w α => by
    have e : zetaVec ζ hζ w = fun k => ζ ^ ((w k).val : ℤ) :=
      funext fun k => by rw [zetaVec_apply, zpow_natCast]
    rw [e, TwE6RootKill.rootChar_val_eq_one_iff_wk hprim]
    rfl
  set a := zetaVec (τ := Tag.E6) ζ hζ v with ha
  have hkv : ∀ α : Fin Tag.E6.rank → ℤ, rootChar a α = 1 ↔ KerP v α := hker v
  have hap : ∀ k, a k ^ 3 = 1 := fun k => by
    rw [ha, zetaVec_apply, pow_right_comm, hζ, one_pow]
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro h
    refine hv' (funext fun k => (ZMod.val_eq_zero (v k)).1 ?_)
    have hk := congrFun (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)) k
    rw [ha, zetaVec_apply, Pi.one_apply, hprim.pow_eq_one_iff_dvd] at hk
    have hlt := ZMod.val_lt (v k)
    omega
  have hTame := langSetup_hTame_of_prime S Nat.prime_three (by exact_mod_cast h3)
    (fun h => absurd h (by decide)) hT hap h1
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup β) := by
    have e : CFSG.StandardType.ggFix β = fixSubgroup β :=
      Subgroup.ext fun _ => mem_ggFix.trans mem_fixSubgroup.symm
    rw [← e]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hJ
  obtain ⟨i, -, hi⟩ := components_of_langSetup S Nat.prime_three ι hι hrange β hβ hT hap h1
    hTame hJ'
  set Ψ := componentRoots (rootCharHom a) i
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hΨker : ∀ α ∈ Ψ, IsRoot Tag.E6 α ∧ KerP v α := fun α ⟨hα, _⟩ =>
    ⟨hα.1, (hkv α).1 hα.2⟩
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [hρ γ (hΨ.isRoot γ hγ)]
    exact hΨ.neg_mem γ hγ
  have hle : J.map ι ≤ rootSpan Tag.E6 Ω Ψ := by
    have hsub : rationalRoots S.ρ (rootCharHom a) i ⊆ Ψ := by
      rintro γ ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => exact hδ
      | succ k ih => rw [Function.iterate_succ_apply']; exact hρΨ _ ih
    rw [hi]
    calc rationalComponent S.ρ S.Γ (rootCharHom a) i
        ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
          Subgroup.commutator_le.2 fun x hx y hy => by
            rw [commutatorElement_def]
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
              (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
      _ ≤ rootSpan Tag.E6 Ω (rationalRoots S.ρ (rootCharHom a) i) := inf_le_left
      _ ≤ rootSpan Tag.E6 Ω Ψ := biSup_mono fun γ hγ => hsub hγ
  have hcent : ∀ u : Fin Tag.E6.rank → ZMod 3, (∀ α ∈ Ψ, rootChar (zetaVec ζ hζ u) α = 1) →
      ∀ c ∈ J, ι c * rootDiagUnit Tag.E6 (zetaVec ζ hζ u) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ u) * ι c := by
    intro u hu c hc
    have hspan : rootSpan Tag.E6 Ω Ψ ≤
        Subgroup.centralizer {rootDiagUnit Tag.E6 (zetaVec ζ hζ u)} := by
      refine iSup₂_le fun α hα => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h := rootDiagUnit_conj_pinnedX (zetaVec ζ hζ u) (hΨ.isRoot α hα) x
      rw [hu α hα, Units.val_one, one_mul] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hspan (hle (Subgroup.mem_map_of_mem ι hc)))
  rcases hexcl with ⟨g, b, hg, hgv, hb, hbv, hgb, hsplit⟩ | ⟨u, hu0, hu1, hu2, hu⟩
  · obtain ⟨g, rfl⟩ : ∃ g' : Fin Tag.E6.rank → ℤ, g' = g := ⟨g, rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b' : Fin Tag.E6.rank → ℤ, b' = b := ⟨b, rfl⟩
    have hcor : ∀ γ α : Fin Tag.E6.rank → ℤ,
        rootChar (zetaVec ζ hζ (corootVec γ)) α = ζ ^ iform (τ := Tag.E6) α γ := fun γ α => by
      rw [← corootTuple_eq_zetaVec]
      exact TwE6RootKill.rootChar_corootTuple γ α ζ
    by_cases hgΨ : g ∈ Ψ
    ·
      have hN : ∀ α ∈ Ψ, iform (τ := Tag.E6) g α ≠ 0 := by
        rcases hΨ.irreducible {α | α ∈ Ψ ∧ iform (τ := Tag.E6) g α ≠ 0} (fun _ h => h.1)
            (fun α ⟨hα, hgα⟩ δ hδ hδS => by
              rw [iform_comm]
              exact hsplit δ α (hΨker δ hδ).1 (hΨker δ hδ).2 (hΨker α hα).1 (hΨker α hα).2
                (not_not.1 fun h => hδS ⟨hδ, h⟩) hgα) with h | h
        · have hgS : g ∈ {α | α ∈ Ψ ∧ iform (τ := Tag.E6) g α ≠ 0} :=
            ⟨hgΨ, (iform_self_pos_of_isRoot hg).ne'⟩
          rw [h] at hgS
          exact ((Set.mem_empty_iff_false g).1 hgS).elim
        · exact fun α hα => (h.symm.subset hα).2
      obtain ⟨h0, hb1, hb2⟩ := corootVec_ne_of_ker hb hbv
      refine ⟨corootVec b, h0, hb1, hb2, hcent (corootVec b) fun α hα => ?_⟩
      rw [hcor, iform_comm, hsplit b α hb hbv (hΨker α hα).1 (hΨker α hα).2 hgb (hN α hα),
        zpow_zero]
    ·
      have hgk : g ∈ kernelRoots (rootCharHom a) := ⟨hg, (hkv g).2 hgv⟩
      have hO : ∀ α ∈ Ψ, iform (τ := Tag.E6) α g = 0 := by
        rintro α ⟨hαk, hαi⟩
        by_contra hne
        exact hgΨ ⟨hgk, (mk_eq_of_iform_ne_zero (α := ⟨g, hgk⟩) (β := ⟨α, hαk⟩)
          (by rw [iform_comm]; exact hne)).trans hαi⟩
      obtain ⟨h0, hg1, hg2⟩ := corootVec_ne_of_ker hg hgv
      exact ⟨corootVec g, h0, hg1, hg2, hcent (corootVec g) fun α hα => by
        rw [hcor, hO α hα, zpow_zero]⟩
  · exact ⟨u, hu0, hu1, hu2, hcent u fun α hα =>
      (hker u α).2 (hu α (hΨker α hα).1 (hΨker α hα).2)⟩

end CFSG.StandardType.TwE6Cube

end
