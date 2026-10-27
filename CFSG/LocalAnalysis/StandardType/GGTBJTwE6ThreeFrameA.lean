module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator

theorem ggTwE6Three_frameA
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1)
    {A : Subgroup (MulAut L')} (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) :
    GGE6ThreeFrameA A Fm.κ := by
  classical
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ Fm.κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ Fm.κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    coordSet_eq_univ_or_hypE6_twE6Three Fm.hκrange
  have htmul : ∀ x y, Fm.t (x + y) = Fm.t x * Fm.t y :=
    t_add_twE6Three (algebraMap K (AlgebraicClosure K)) Fm.hζ Fm.htF
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (σ := σ.toRingHom) σ.surjective
  have hodd : ∀ z ∈ ψ₀.ker, Odd (orderOf z) := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 (hker3 z hz)
    rcases (Nat.dvd_prime Nat.prime_three).1 hz3 with h | h
    · rw [h]
      exact ⟨0, rfl⟩
    · rw [h]
      exact ⟨1, rfl⟩
  choose r hrJ hr using fun γ : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ} =>
    TwE6ThreeRootGen.exists_mem_ggKGTwJ_conj hK hσ Fm.F Fm.hv Fm.hζ Fm.htF γ.2
  obtain ⟨-, m, hmN, -, -, -, -, hW, hR, hΦ, -, -⟩ :=
    exists_lift_of_coverTorus (p := 3) (k := Tag.E6.rank) (L' := L')
      (R := ↥(twistedE6RootGroup K σ)) (G := ModGL TwistTag.E6.tag K)
      (ψ := ψ₀) (A := A) (Φ := Fm.κ) (τ := Fm.t) (T := Fm.T)
      (ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ})
      (s := fun i => ExcSplitRootGen.excRefl (p := 3) i.1) (r := r)
      (S := fun i => ggKGTwJ Fm.F i.1) (ι₀ := (twistedE6RootGroup K σ).subtype)
      hψ₀ hker hZ hker3 (Subgroup.subtype_injective _) Fm.hκinj htmul Fm.hconj Fm.hTfix
      (fun z hz => Fm.hTodd z hz (hodd z hz)) hr
      (fun i a => ExcSplitRootGen.excRefl_excRefl (τ := Tag.E6) (p := 3) i.2 _)
      (fun i => card_fix_excRefl_mul_three_twE6Three (κ := Fm.κ) Fm.hκinj hVmem hV i.2)
      (fun i a => exists_t_pow_three_twE6Three (κ := Fm.κ) Fm.hHyp a) hrJ
      (fun i => isComponentOf_image_fix_twE6Three (κ := Fm.κ) hn hK hσ Fm.F Fm.hv Fm.hζ Fm.hζo
        Fm.htF hVmem hV i)
      (fun i => ggKGTwJ_dvd_card hK hσ Fm.F Fm.hv i.2 h3)
  unfold GGE6ThreeFrameA
  refine ⟨Fm.hκinj, Fm.hκrange, fun γ hγ => ?_, Fm.hnorm⟩
  exact ⟨m ⟨γ, hγ⟩, hmN ⟨γ, hγ⟩, hW _, hR _, hΦ ⟨γ, hγ⟩⟩

end CFSG.StandardType

end
