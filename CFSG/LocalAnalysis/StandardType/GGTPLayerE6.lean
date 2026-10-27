module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE
public import CFSG.LocalAnalysis.StandardType.GGKGLayersE6
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGKGLayersTheta
public import CFSG.RankThree.PartOne.KE.ConjRootSpan
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.KGL
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.RankThree.PartOne.KE

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def ggTP_comapEquiv {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (L : Subgroup H) (hL : L ≤ f.range) :
    L.comap f ≃* L :=
  (Subgroup.equivMapOfInjective (L.comap f) f hf).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL))

private noncomputable def ggTP_perpRootSpan_equiv {K : Type} [Field K]
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    rootSpan Tag.E6 K {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ iform γ β = 0} ≃*
      ↥(E6Pilot.a5Levi K) := by
  classical
  let u := Classical.choose (exists_weyl_smul_a5 hβ)
  have hu : (fun γ => u • γ) '' {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ γ 1 = 0} =
      {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ iform γ β = 0} :=
    Classical.choose_spec (exists_weyl_smul_a5 hβ)
  have hset : {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ γ 1 = 0} =
      E6Pilot.a5LeviRoots := by
    rw [E6Pilot.a5LeviRoots_eq_perpRoots]
    rfl
  have hmap := map_conj_rootSpan (τ := Tag.E6) (L := K) u
    (S := {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ γ 1 = 0}) (fun γ hγ => hγ.1)
  rw [hu, hset] at hmap
  exact ((MulEquiv.subgroupCongr hmap).symm.trans
    ((Subgroup.equivMapOfInjective (rootSpan Tag.E6 K E6Pilot.a5LeviRoots)
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) K u)).toMonoidHom
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) K u)).injective).symm)).trans
    ((MulEquiv.subgroupCongr (E6Pilot.map_subtype_a5Levi (K := K)).symm).trans
      (Subgroup.equivMapOfInjective (E6Pilot.a5Levi K) (adjointGroup Tag.E6 K).subtype
        (adjointGroup Tag.E6 K).subtype_injective).symm)

theorem ggTPLayerModel_E6
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (hTB : GGTorusTBGroup 3 5 (RecipeGroup Tag.E6 K) (RecipeID Tag.E6 K) L' ψ A)
    (hA : Nat.card A = 3 ^ 5) {c : ↥A} (hc : GGCorootPt 3 (ggTorusAut A) c) :
    ∃ (ER : Subgroup (RecipeGroup Tag.E6 K)) (X : Type) (_ : Group X),
      GGLayerOf (ggRFix ψ {(c : MulAut L')}) ER ∧ Nonempty (ER ≃* X) ∧
        Subgroup.center X = ⊥ ∧ CFSG.Open.StatedClassicalModel X .PSL 6 2 n := by
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
    have hcard : Fintype.card K = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]; exact hK
    rw [hcard] at hm
    have hdvd : ringChar K ∣ 2 ^ n := by
      rw [hm]
      exact dvd_pow_self _ m.pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardu : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have h3u : 3 ∣ Nat.card Kˣ := by rw [hcardu]; exact h3
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' 3 h3u
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  obtain ⟨g, κ, hg, hκinj, hκrange, hconj, hweyl, hsimple⟩ :=
    kgFrameE6_holds K n hn hK h3 ζ hζ hζo L' ψ A hTB hA
  have hF : KGAutFrame A κ := ⟨hA, hκinj, hκrange, hweyl, hsimple⟩
  have hconjΘ : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹ :=
    kgThetaHom_conj g ψ
      (fun a => rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)))) hconj
  obtain ⟨β, hβroot, hβ⟩ := hF.corootPt hc
  let ER : Subgroup (RecipeGroup Tag.E6 K) :=
    (rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))})).comap
      (kgThetaHom g)
  have hER : GGLayerOf (ggRFix ψ {(c : MulAut L')}) ER := by
    have h1' := kgAdjL1 K hchar ζ hζ hζo β hβroot
    rw [← hβ] at h1'
    refine layer_of_famCentralizer ψ hTB.1 (kgThetaHom g) (kgThetaHom_injective g)
      (kgThetaHom_range g hg) {(c : MulAut L')} {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))}
      ?_ ?_ h1'
    · rintro f hf
      have hf_eq := Set.mem_singleton_iff.mp hf
      subst hf_eq
      exact ⟨kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c)), rfl, fun l => hconjΘ c l⟩
    · rintro a ha
      have ha_eq := Set.mem_singleton_iff.mp ha
      subst ha_eq
      exact ⟨(c : MulAut L'), rfl, fun l => hconjΘ c l⟩
  have hz : ({kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))} : Set (Fin Tag.E6.rank → Kˣ)) =
      {kgZetaE6 ζ hζ (kgExpVec β)} :=
    congrArg (fun x : Fin Tag.E6.rank → ZMod 3 =>
      ({kgZetaE6 ζ hζ x} : Set (Fin Tag.E6.rank → Kˣ))) hβ
  have hker_eq : kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))} =
      {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ iform γ β = 0} :=
    (congrArg (fun F => kgKernelE6 F) hz).trans
      (famKernel_kgExpVec_single (K := K) hζo hζ hβroot)
  have hLle : rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))})
      ≤ (kgThetaHom g).range := by
    rw [kgThetaHom_range g hg]
    exact E6Pilot.rootSpan_le_adjointGroup_E6 (K := K) _
  have e1 : ER ≃* rootSpan Tag.E6 K
      {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ iform γ β = 0} :=
    (ggTP_comapEquiv (kgThetaHom g) (kgThetaHom_injective g)
      (rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))}))
      hLle).trans (MulEquiv.subgroupCongr (congrArg (rootSpan Tag.E6 K) hker_eq))
  haveI : CharP K 2 := ringChar.of_eq hchar
  refine ⟨ER, ↥(E6Pilot.a5Levi K), inferInstance, hER,
    ⟨e1.trans (ggTP_perpRootSpan_equiv hβroot)⟩, ?_, ?_⟩
  · exact E6Pilot.center_a5Levi_eq_bot (K := K)
  · exact (CFSG.Blueprint.LieModel.classical_iff (by decide)).mp
      (E6Pilot.lieModel_a5Levi (K := K) (f := n) hK)

end CFSG.StandardType

end
