module

public import CFSG.LocalAnalysis.StandardType.GGResidualWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthModelInputs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanUnitaryAnyA
import CFSG.LocalAnalysis.StandardType.GGOrthFrameConcl
import CFSG.LocalAnalysis.StandardType.GGOrthModelInputsHold
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

@[expose] def ggRowP_Rk1Rest (nb tA tD ltB : Prop) (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (¬ tA ∧ ¬ tD ∧ ggRowP_ETwE6 p lab ∧ lab.n = 1 ∧ nb) ∨
    (lab.n = 1 ∧ ggRowP_EOmP p lab ∧ lab.rank = 4 ∧ nb ∧ ¬ tA ∧ ¬ ltB)

section Defs

@[expose] def GGResidualRk1Frame (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) : Prop :=
  ∃ Φ : OrthTorus.OrthWeakFrame p Bs X, Φ.Recognized

@[expose] def GGRk1ResidualFrameInputExOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ¬ (GGIsWeylMatrixA M ∧
          ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨
            (X ∈ 𝒦 ∧ ¬ (NSJoin.NSTypeD M ∧
              ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) ∨
            (T M ∧ (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
              GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)) →
          ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          GGInnerDiagOnLabel (fun p lab => ggRowP_Rk1Rest (X ≠ L) (GGIsWeylMatrixA M) (NSJoin.NSTypeD M)
            (B < Bs) p lab ∧
            (X ≠ L → ¬ NSJoin.NSTypeD M →
              (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) → lab.n ≠ 1)) p Bs X →
          (NSJoin.NSTypeD M → X = L → GGInnerDiagOnLabel (fun _ lab => lab.n = 1) p Bs X) →
          GGResidualRk1Frame p Bs X ∨ ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r

end Defs

section Proofs

theorem ggRk1ConclEx_conj {p : ℕ} {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {r a : MulAut ↥Bs} (hr : GGRk1ConclEx p Bs X r) (ha : a ∈ ggAutomizer X Bs) :
    GGRk1ConclEx p Bs X (a * r * a⁻¹) := by
  obtain ⟨F, hF, hFin, θ, hchar, hinj, hrange, ⟨n, hnS, hnN, hnact⟩, hsplit, hnsplit, hlab, hex⟩ := hr
  obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  have hX : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
  have hconj : (ggRankOneIn X Bs r).map (MulAut.conj g).toMonoidHom =
      ggRankOneIn X Bs (a * r * a⁻¹) := by
    have h := ggRankOneIn_map_conj (X := X) hg r
    rwa [hX] at h
  refine ⟨F, hF, hFin, (MulAut.conj g).toMonoidHom.comp θ, hchar, ?_, ?_,
    ⟨g * n * g⁻¹, ?_, ?_, ?_⟩, hsplit, hnsplit, hlab, hex⟩
  · exact (MulAut.conj g).injective.comp hinj
  · rw [MonoidHom.range_comp, hrange, hconj]
  · rw [← hconj]
    exact Subgroup.mem_map.mpr ⟨n, hnS, by simp [MulAut.conj_apply]⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hnN) (Subgroup.inv_mem _ hgN)
  · intro b
    have h1 := hg (r (a⁻¹ b))
    have h2 := hnact (a⁻¹ b)
    have h3 := inv_apply_of_forall hg b
    show ((a (r (a⁻¹ b)) : ↥Bs) : G) = g * n * g⁻¹ * b * (g * n * g⁻¹)⁻¹
    rw [h1, h2, h3]
    group

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

theorem OrthWeakFrame.rk1Ex_of_swapElt (hRig : GGLabelRigidInput) (hM2 : OrthRankOneModelInput) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthWeakFrame p Bs X) (hΦ : Φ.Recognized) (hXns : ¬ GGSplitLie p X) {i j : Fin Φ.r}
    (hij : i ≠ j) {w : ↥(orthDerived Φ.Q)}
    (hw : ∀ f : Fin Φ.r → Multiplicative (ZMod p), (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (SpCoord.permAut (Equiv.swap i j) f))
    {a : MulAut ↥Bs} (haA : a ∈ ggAutomizer X Bs) (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) :
    GGIsReflection p a ∧ GGRk1ConclEx p Bs X a := by
  haveI := Φ.finite_linearEquiv
  have haR : GGIsReflection p a :=
    isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj (Fact.out : p.Prime).one_lt ha
      (fun t ht => Φ.Δ.swap_sq_comm hw t ht) (fun t => Φ.Δ.mem_reflFixed_iff hw t) (Φ.Δ.card_reflFixed hij)
  have haS : ggRankOneIn X Bs a = ((Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
    have h := ggRankOneIn_eq_map_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj ha
      (fun t => Φ.Δ.mem_reflFixed_iff hw t)
    rw [Φ.hrange] at h
    exact h
  have hr3 : 3 ≤ Φ.r := by have := Φ.hr; omega
  have hq : 4 ≤ Nat.card Φ.F := by
    rw [Φ.hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Φ.f := Nat.pow_le_pow_right (by norm_num) Φ.hf
  obtain ⟨⟨θm, hθinj, hθrange, -⟩, -⟩ :=
    hM2 Φ.F Φ.V Φ.Q p hp2 Φ.A Φ.hA Φ.r Φ.Δ hr3 hq Φ.hfix i j hij
  have hθΩ : ∀ x, θm x ∈ orthDerived Φ.Q := by
    intro x
    have hx : θm x ∈ θm.range := ⟨x, rfl⟩
    rw [hθrange] at hx
    exact (ggOTwoPrime_le _ hx).2
  let θΩ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* ↥(orthDerived Φ.Q) :=
    θm.codRestrict (orthDerived Φ.Q) hθΩ
  let θ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* G := Φ.ψ.comp θΩ
  have hθΩinj : Function.Injective θΩ := fun x y h => hθinj (congrArg Subtype.val h)
  have hΩrange : θΩ.range = (Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q) := by
    ext y
    rw [Subgroup.mem_subgroupOf, ← hθrange]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hrange : θ.range = ggRankOneIn X Bs a := by
    rw [haS]
    change (Φ.ψ.comp θΩ).range = _
    rw [MonoidHom.range_comp, hΩrange]
  refine ⟨haR, Φ.F, inferInstance, inferInstance, θ, inferInstance, ?_, hrange, ?_, ?_, ?_, ?_, ?_⟩
  · exact Φ.hinj.comp hθΩinj
  · have hr2 : a * a = 1 := by simpa [pow_two] using haR.1
    exact ggExists_weylElt_of_mem_ggAutomizer haA hr2
  · intro hs
    exact absurd hs hXns
  · intro _
    exact Φ.hpq
  · intro lab' hlam' hl'
    have hf1 : 1 ≤ Φ.f := by have := Φ.hf; omega
    have hnn : lab'.n = Φ.f := by
      rcases hΦ.2.2 with ⟨_, hl⟩ | ⟨_, hl⟩
      · exact ggLabel_n_eq_of_D hRig Φ.hr hf1 hl hlam' hl'
      · exact ggLabel_n_eq_of_twD hRig Φ.hr hf1 hl hlam' hl'
    rw [hnn, Φ.hcard]
  · have hf1 : 1 ≤ Φ.f := by have := Φ.hf; omega
    rcases hΦ.2.2 with ⟨_, hl⟩ | ⟨_, hl⟩
    · exact ⟨⟨.D, Φ.r, Φ.f⟩, ⟨hf1, show 3 ≤ Φ.r by have := Φ.hr; omega⟩, hl, Φ.hcard⟩
    · exact ⟨⟨.twD, Φ.r, Φ.f⟩, ⟨hf1, show 2 ≤ Φ.r by have := Φ.hr; omega⟩, hl, Φ.hcard⟩

end OrthTorus

end Proofs

end CFSG.StandardType

end
