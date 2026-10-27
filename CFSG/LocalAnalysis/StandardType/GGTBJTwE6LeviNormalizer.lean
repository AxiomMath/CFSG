module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Model
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ParabolicMod
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenGen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

theorem sectionFrameAut_le_adMulAutHom_range_twE6
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hTinj : Function.Injective T)
    (hT : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd x)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x))
    {X : Type} [Group X] (ψ : X →* twistedE6RootGroup K σ)
    (s : (Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p)) →* X)
    (hs : ∀ f, ψ (s f) = T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j)))) :
    FrameBs.sectionFrameAut s (⊤ : Subgroup X) ≤ (adMulAutHom TwistTag.E6.tag p).range := by
  classical
  rintro τ ⟨a, -, ha⟩
  let g := ggKGTwY F (ψ a)
  let V : Set (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
    Set.range fun f : Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p) => ggKGTwY F (ψ (s f))
  have hVD : ∀ z ∈ V, ∃ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      z = rootDiagUnit TwistTag.E6.tag b := by
    rintro z ⟨f, rfl⟩
    refine ⟨TableBExc.E6Three.zetaVec ζ hζ (fun j => Multiplicative.toAdd (f j)), ?_⟩
    change ggKGTwY F (ψ (s f)) = _
    rw [hs, hT]
  have hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    TwE6PlusRootGen.ggKGTwY_mem_adjointGroup F (ψ a)
  have hconj : ∀ f, g * ggKGTwY F (ψ (s f)) * g⁻¹ = ggKGTwY F (ψ (s (τ f))) := by
    intro f
    have h := congrArg (fun x : X => ggKGTwY F (ψ x)) (ha f)
    simpa only [map_mul, map_inv] using h
  have hgV : ∀ z ∈ V, g * z * g⁻¹ ∈ V := by
    rintro z ⟨f, rfl⟩
    exact ⟨τ f, (hconj f).symm⟩
  obtain ⟨w, hw⟩ := NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
    hVD hg hgV
  refine MonoidHom.mem_range.mpr ⟨w, ?_⟩
  apply MulEquiv.ext
  intro f
  have hc := (hconj f).symm.trans (hw _ ⟨f, rfl⟩)
  simp only [hs, hT] at hc
  rw [TwE6PlusRootGen.ggKGTw_conj_rootDiagUnit hζ] at hc
  have hpoints : T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (τ f j))) =
      T (Multiplicative.ofAdd (adAct TwistTag.E6.tag p w (fun j => Multiplicative.toAdd (f j)))) := by
    apply ggKGTl_conj_injective F
    change ggKGTwY F (T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (τ f j)))) =
      ggKGTwY F (T (Multiplicative.ofAdd (adAct TwistTag.E6.tag p w
        (fun j => Multiplicative.toAdd (f j)))))
    rw [hT, hT]
    exact hc
  have he := congrArg Multiplicative.toAdd (hTinj hpoints)
  funext i
  rw [adMulAutHom_apply]
  apply Multiplicative.toAdd.injective
  exact (congrFun he i).symm

theorem adMulAutHom_mem_sectionFrameAut_of_weyl_point
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hT : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd x)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x))
    {X : Type} [Group X] [Finite X] (ψ : X →* twistedE6RootGroup K σ)
    (hker : ψ.ker ≤ Subgroup.center X) (hcp : ¬p ∣ Nat.card (Subgroup.center X))
    (s : (Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p)) →* X)
    (hs : ∀ f, ψ (s f) = T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j))))
    {H : Subgroup X} {a : X} (ha : a ∈ H) {w : WeylGroup TwistTag.E6.tag}
    (hw : ggKGTwY F (ψ a) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) :
    adMulAutHom TwistTag.E6.tag p w ∈ FrameBs.sectionFrameAut s H := by
  have hp : p.Prime := Fact.out
  have hsp : ∀ f, (s f) ^ p = 1 := fun f => by
    rw [← map_pow, ReflInner.pow_eq_one_of_zmod f, map_one]
  refine ⟨a, ha, fun f => ?_⟩
  apply eq_of_lift_pow_eq_one hp hker hcp
  · simp only [map_mul, map_inv, hs]
    let c : Fin TwistTag.E6.tag.rank → ZMod p := fun j => Multiplicative.toAdd (f j)
    have hc : (fun j => Multiplicative.toAdd (adMulAutHom TwistTag.E6.tag p w f j)) =
        adAct TwistTag.E6.tag p w c := by
      funext j
      rw [adMulAutHom_apply]
      rfl
    rw [hc]
    let T' : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ := T
    let c' : Fin Tag.E6.rank → ZMod p := c
    let w' : WeylGroup Tag.E6 := w
    have hT' : ∀ x : Fin Tag.E6.rank → ZMod p, ggKGTwY F (T' (Multiplicative.ofAdd x)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) := hT
    have hw' : ggKGTwY F (ψ a) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w' := hw
    exact TwE6PlusRootGen.conj_twE6PlusTorus F hζ hT' hw' c'
  · rw [conj_pow, hsp, mul_one, mul_inv_cancel]
  · exact hsp _

theorem adMulAutHom_range_le_sectionFrameAut_twE6
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hT : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd x)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x))
    {X : Type} [Group X] [Finite X] (ψ : X →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center X)
    (hcp : ¬p ∣ Nat.card (Subgroup.center X))
    (s : (Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p)) →* X)
    (hs : ∀ f, ψ (s f) = T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j)))) :
    (adMulAutHom TwistTag.E6.tag p).range ≤ FrameBs.sectionFrameAut s (⊤ : Subgroup X) := by
  classical
  have hsimple : ∀ i, adMulAutHom TwistTag.E6.tag p (simple TwistTag.E6.tag i) ∈
      FrameBs.sectionFrameAut s (⊤ : Subgroup X) := by
    intro i
    let i' : Fin Tag.E6.rank := i
    obtain ⟨r, -, hr⟩ := ggKGTwJ_weyl hK hσ F hv (isRoot_single Tag.E6 i')
    have hrTw : ggKGTwY F r = canonicalRep (coxeterSystem TwistTag.E6.tag)
        (AlgebraicClosure K) (rootReflection (τ := TwistTag.E6.tag)
          (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) := hr
    have href : rootReflection (τ := TwistTag.E6.tag)
        (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        simple TwistTag.E6.tag i := by
      simpa using (rootReflection_eq_conj (τ := TwistTag.E6.tag) (w := 1) (j := i) (by simp))
    rw [href] at hrTw
    obtain ⟨a, ha⟩ := hψ r
    exact adMulAutHom_mem_sectionFrameAut_of_weyl_point F hζ T hT ψ hker hcp s hs
      (Subgroup.mem_top a) (by rw [ha]; exact hrTw)
  rintro τ ⟨w, rfl⟩
  obtain ⟨ω, rfl⟩ := (coxeterSystem TwistTag.E6.tag).wordProd_surjective w
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, map_one]; exact Subgroup.one_mem _
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul]
    exact Subgroup.mul_mem _ (hsimple i) ih

theorem sectionFrameAut_eq_adMulAutHom_range_twE6
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hTinj : Function.Injective T)
    (hT : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd x)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x))
    {X : Type} [Group X] [Finite X] (ψ : X →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center X)
    (hcp : ¬p ∣ Nat.card (Subgroup.center X))
    (s : (Fin TwistTag.E6.tag.rank → Multiplicative (ZMod p)) →* X)
    (hs : ∀ f, ψ (s f) = T (Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j)))) :
    FrameBs.sectionFrameAut s (⊤ : Subgroup X) = (adMulAutHom TwistTag.E6.tag p).range :=
  le_antisymm (sectionFrameAut_le_adMulAutHom_range_twE6 F hζ T hTinj hT ψ s hs)
    (adMulAutHom_range_le_sectionFrameAut_twE6 hK hσ F hv hζ T hT ψ hψ hker hcp s hs)

end CFSG.StandardType

end
