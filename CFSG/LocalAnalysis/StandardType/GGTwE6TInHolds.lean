module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TInDescent
public import CFSG.LocalAnalysis.StandardType.GGTwE6TInTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwoLocalToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TwE6RootKill CFSG.Open

theorem ggTwE6ThreeTwoLocalInnToralInput_holds : GGTwE6ThreeTwoLocalInnToralInput := by
  intro f hf h3 Ω _ _ _ Fr hFr X V hXR hVR hXel hXc hV1 hV2 hXV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  obtain ⟨A, hAI, hAX, hAU⟩ :=
    exists_twNormTwo_descent hf h3 Ω Fr hFr hXR hVR hV1 hV2 hXV
  let b : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag Ω :=
    baseChangeGL (algebraMap K Ω)
  have hinj : Function.Injective b := CFSG.LieType.Chevalley.baseChangeGL_injective _
  have hAeq : A = X.comap b := by
    rw [← hAX]
    exact (Subgroup.comap_map_eq_self_of_injective hinj A).symm
  have hAel : IsElemAbelian 3 A := by
    rw [hAeq]
    exact hXel.comap hinj
  have hcard : 3 ^ 4 ≤ Nat.card A := by
    have h1 : Nat.card A = Nat.card (A.map b) :=
      (Subgroup.card_map_of_injective (K := A) (f := b) hinj).symm
    have h2 : Nat.card (A.map b) = Nat.card ↥X :=
      congrArg (fun H : Subgroup (ModGL TwistTag.E6.tag Ω) => Nat.card ↥H) hAX
    exact (h1.trans (h2.trans hXc)).ge
  have hK : Nat.card K = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : K, frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  obtain ⟨g, hg, hgt⟩ :=
    exists_conj_torus_of_twNormTwo (K₀ := K) (K := K) (n := f)
      ExcFramesHalf.bigElemAbelianToralBar_E6_three hK hσ h3
      (algebraMap K (AlgebraicClosure K)) hAI hAel hcard hAU
  rw [← hAX]
  exact isToralE6_map_baseChange_of_algebraicClosure Ω A ⟨g, hg, hgt⟩

end CFSG.StandardType.NoOffTwE6Three
