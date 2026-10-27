module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootTorus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

private theorem weylElt_conj_coroot
    {Ω : Type} [Field Ω] (i : Fin Tag.E6.rank) (δ : Fin Tag.E6.rank → ℤ) (s : Ωˣ) :
    weylElt Tag.E6 Ω i 1 * TwE6Coroot.coroot δ s * (weylElt Tag.E6 Ω i 1)⁻¹ =
      TwE6Coroot.coroot ((coxeterSystem Tag.E6).simple i • δ) s := by
  simp only [TwE6Coroot.coroot, simple_smul]
  exact CFSG.SeitzReduction.E6Pilot.weylElt_one_conj_corootTuple δ s i

private theorem conj_mul_conj {G : Type*} [Group G] (g n c : G) :
    (g * n * g⁻¹) * (g * c * g⁻¹) * (g * n * g⁻¹)⁻¹ = g * (n * c * n⁻¹) * g⁻¹ := by
  group

theorem tspec_conj_coroot
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D)
    (i : Fin 6) (δ : Fin Tag.E6.rank → ℤ) (s : Ωˣ)
    {u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hu : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (u : ModGL TwistTag.E6.tag K) =
      g * TwE6Coroot.coroot δ s * g⁻¹) :
    baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        ((D.nb i * u * (D.nb i)⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      g * TwE6Coroot.coroot ((coxeterSystem Tag.E6).simple i • δ) s * g⁻¹ := by
  let i' : Fin Tag.E6.rank := i
  let n : ModGL Tag.E6 K := (D.nb i' : ModGL TwistTag.E6.tag K)
  let uK : ModGL Tag.E6 K := (u : ModGL TwistTag.E6.tag K)
  have hcoe : ((D.nb i' * u * (D.nb i')⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      n * uK * n⁻¹ := rfl
  have hbc : baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        ((D.nb i' * u * (D.nb i')⁻¹ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) n *
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) uK *
        (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) n)⁻¹ := by
    rw [hcoe, map_mul, map_mul, map_inv]
  have hnb : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) n =
      g * weylElt Tag.E6 Ω i' 1 * g⁻¹ :=
    hD.nb_eq i'
  have hu' : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) uK =
      g * TwE6Coroot.coroot δ s * g⁻¹ := hu
  rw [hbc, hnb, hu']
  rw [conj_mul_conj, weylElt_conj_coroot i' δ s]

end CFSG.StandardType.E6ThreeModel
