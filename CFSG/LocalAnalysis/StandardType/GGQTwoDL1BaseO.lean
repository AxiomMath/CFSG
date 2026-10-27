module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Lift
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseOOdd
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1OCent
public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixO
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthNormIso
import CFSG.LieType.ChevTwo.OrthogonalAutLarge
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9OrthAmbient
import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

private theorem p9uBO_permAut_swap_ne {p k : ℕ} [Fact p.Prime] {i j l : Fin k}
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    SpCoord.permAut (p := p) (Equiv.swap i j) *
        SpCoord.permAut (p := p) (Equiv.swap j l) ≠
      SpCoord.permAut (p := p) (Equiv.swap j l) *
        SpCoord.permAut (p := p) (Equiv.swap i j) := by
  intro h
  have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod p)) =>
      u (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)))) h
  simp only [MulAut.mul_apply, SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hij hil,
    Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
  have h2 := congrFun h1 j
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hjl] at h2
  exact one_ne_zero (Multiplicative.ofAdd.injective h2)

private theorem p9uBO_swap_pair {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} (Φ : OrthTorus.OrthFrameCore p Bs L) (hr : 3 ≤ Φ.r) :
    ∃ (i j k : Fin Φ.r), i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      ∃ (w₀ w₁ : ↥(CFSG.RankThree.Classical2.orthDerived Φ.Q)),
        (∀ f : Fin Φ.r → Multiplicative (ZMod p),
          (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
            Φ.Δ.τ (SpCoord.permAut (Equiv.swap i j) f)) ∧
        (∀ f : Fin Φ.r → Multiplicative (ZMod p),
          (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
            Φ.Δ.τ (SpCoord.permAut (Equiv.swap j k) f)) ∧
        ∃ r₀ ∈ ggAutomizer L Bs, GGIsReflection p r₀ ∧ ∃ r₀' ∈ ggAutomizer L Bs,
          GGIsReflection p r₀' ∧ r₀ * r₀' ≠ r₀' * r₀ ∧
          (∀ s : ↥Bs, ((r₀ s : ↥Bs) : G) = Φ.ψ w₀ * (s : G) * (Φ.ψ w₀)⁻¹) ∧
          (∀ s : ↥Bs, ((r₀' s : ↥Bs) : G) = Φ.ψ w₁ * (s : G) * (Φ.ψ w₁)⁻¹) := by
  haveI := Φ.finite_linearEquiv
  let i : Fin Φ.r := ⟨0, by omega⟩
  let j : Fin Φ.r := ⟨1, by omega⟩
  let k : Fin Φ.r := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hjk : j ≠ k := by simp [j, k]
  have hik : i ≠ k := by simp [i, k]
  obtain ⟨w₀, hw₀, hn₀⟩ := Φ.swapReal i j hij
  obtain ⟨w₁, hw₁, hn₁⟩ := Φ.swapReal j k hjk
  have hgL₀ : Φ.ψ w₀ ∈ L := by
    have h : Φ.ψ w₀ ∈ Φ.ψ.range := ⟨w₀, rfl⟩
    rwa [Φ.hrange] at h
  have hgL₁ : Φ.ψ w₁ ∈ L := by
    have h : Φ.ψ w₁ ∈ Φ.ψ.range := ⟨w₁, rfl⟩
    rwa [Φ.hrange] at h
  refine ⟨i, j, k, hij, hjk, hik, w₀, w₁, hw₀, hw₁, ggConjAut Bs hn₀,
    ggConjAut_mem_ggAutomizer hgL₀ hn₀, ?_, ggConjAut Bs hn₁, ggConjAut_mem_ggAutomizer hgL₁ hn₁,
    ?_, ?_, fun s => ggConjAut_apply Bs hn₀ s, fun s => ggConjAut_apply Bs hn₁ s⟩
  · exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj
      (Fact.out : p.Prime).one_lt (fun b => ggConjAut_apply Bs hn₀ b)
      (fun t ht => Φ.Δ.swap_sq_comm hw₀ t ht)
      (fun t => Φ.Δ.mem_reflFixed_iff hw₀ t) (Φ.Δ.card_reflFixed hij)
  · exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj
      (Fact.out : p.Prime).one_lt (fun b => ggConjAut_apply Bs hn₁ b)
      (fun t ht => Φ.Δ.swap_sq_comm hw₁ t ht)
      (fun t => Φ.Δ.mem_reflFixed_iff hw₁ t) (Φ.Δ.card_reflFixed hjk)
  · intro hcomm
    exact p9uBO_permAut_swap_ne hij hjk hik
      ((Φ.aut_commute_iff_torus_action w₀ w₁ (ggConjAut Bs hn₀) (ggConjAut Bs hn₁)
        (SpCoord.permAut (Equiv.swap i j)) (SpCoord.permAut (Equiv.swap j k))
        (fun b => ggConjAut_apply Bs hn₀ b) (fun b => ggConjAut_apply Bs hn₁ b)
        hw₀ hw₁).mp hcomm)

theorem qtwoDL1_base_orth (ha₀ : GGLNoncyclicInput) {G : Type}
    [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥L = ⊥) :
    ∃ r₀ ∈ ggAutomizer L Bs, GGIsReflection p r₀ ∧ ∃ r₀' ∈ ggAutomizer L Bs,
      GGIsReflection p r₀' ∧ r₀ * r₀' ≠ r₀' * r₀ ∧ Nat.card ↥(ggRankTwo Bs r₀ r₀') ≤ 216 := by
  have : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg).1⟩
  have hr := Φ.hr
  obtain ⟨i, j, k, hij, hjk, hik, w₀, w₁, hw₀, hw₁, r₀, hr₀, hrefl₀, r₀', hr₀', hrefl₀', hne,
    hr₀act, hr₀'act⟩ := p9uBO_swap_pair Φ (by omega)
  refine ⟨r₀, hr₀, hrefl₀, r₀', hr₀', hrefl₀', hne, ?_⟩
  obtain ⟨alg, E, χ, ζ, hζ, hζp, hχQ, hχτ⟩ := Φ.exists_normIso hF
  letI := alg
  let C : QTwoDL1ONormChart Φ := ⟨E, χ, ζ, hζ, hζp, hχQ, hχτ⟩
  obtain ⟨hcard, hin⟩ := qtwoDL1_baseO_centChart ha₀ hcfg Φ hF hZ C hij hjk hik hw₀ hw₁
    hr₀act hr₀'act
  change Nat.card ↥(ggOTwoPrime (Subgroup.centralizer
    ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G))) ≤ 216
  rw [qtwoDL1_ggOTwoPrime_eq_of_inner
    (qtwoDL1_baseO_odd ha₀ hcfg hodd Φ hF hZ hr₀ hrefl₀ hr₀' hrefl₀' hne) hin]
  exact hcard

end CFSG.StandardType.QTwo

end
