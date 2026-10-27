module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcWeylE8
import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
import CFSG.LieType.Chevalley.LangActualInvolutionReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_weyl_of_mem_normalizer_of_frame
    {τ : Tag} {p : ℕ} [NeZero p]
    {K : Type} [Field K] {g0 : ModGL τ (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    {hζ : ζ ^ p = 1} {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    {E : Subgroup (adjointGroup τ K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hι₀ : Function.Injective ι₀) (hrange : ι₀.range = E)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    {g : adjointGroup τ K} (hg : g ∈ Subgroup.normalizer (E : Set (adjointGroup τ K))) :
    ∃ u : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
      g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p u s)) := by
  classical
  set bc := baseChangeGL (τ := τ) (algebraMap K (AlgebraicClosure K)) with hbc
  have hσex : ∀ s : Fin τ.rank → ZMod p, ∃ t : Fin τ.rank → ZMod p,
      ι₀ (Multiplicative.ofAdd t) = g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ := by
    intro s
    have hmem : g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp (hrange ▸ ⟨_, rfl⟩)
    rw [← hrange] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨Multiplicative.toAdd x, hx⟩
  choose σ hσ using hσex
  set h : ModGL τ (AlgebraicClosure K) := g0⁻¹ * bc (g : ModGL τ K) * g0 with hh
  have hgC : bc (g : ModGL τ K) ∈ adjointGroup τ (AlgebraicClosure K) :=
    map_baseChangeGL_adjointGroup_le (algebraMap K (AlgebraicClosure K)) ⟨_, g.2, rfl⟩
  have hhC : h ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (mul_mem (inv_mem hg0C) hgC) hg0C
  have hconj : ∀ s : Fin τ.rank → ZMod p,
      h * ExcFrames.frameDiag ζ hζ s * h⁻¹ = ExcFrames.frameDiag ζ hζ (σ s) := by
    intro s
    have h1 : bc ((ι₀ (Multiplicative.ofAdd (σ s)) : adjointGroup τ K) : ModGL τ K) =
        bc (g : ModGL τ K) * bc ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) *
          (bc (g : ModGL τ K))⁻¹ := by
      rw [hσ s, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    rw [hbase, hbase] at h1
    have h2 : ExcFrames.frameDiag ζ hζ (σ s) =
        g0⁻¹ * (bc (g : ModGL τ K) * (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) *
          (bc (g : ModGL τ K))⁻¹) * g0 := by
      rw [← h1]
      group
    rw [h2, hh]
    group
  obtain ⟨u, hu⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.exists_weyl_of_conj_family τ
    (AlgebraicClosure K)
    (fun s => TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p (σ s)))
    (fun s => TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p s)) hhC hconj
  have hinj : Function.Injective (ExcFrames.frameDiag (τ := τ) ζ hζ) := by
    intro x y hxy
    have h1 : bc ((ι₀ (Multiplicative.ofAdd x) : adjointGroup τ K) : ModGL τ K) =
        bc ((ι₀ (Multiplicative.ofAdd y) : adjointGroup τ K) : ModGL τ K) := by
      rw [hbase, hbase, hxy]
    have h2 := baseChangeGL_injective (τ := τ) (algebraMap K (AlgebraicClosure K)) h1
    exact Multiplicative.ofAdd.injective (hι₀ (Subtype.ext h2))
  refine ⟨u, fun s => ?_⟩
  have h3 : ExcFrames.frameDiag ζ hζ (σ s) =
      ExcFrames.frameDiag ζ hζ (TableBExc.torusAct τ p u s) := by
    rw [← ExcFrames.canonicalRep_conj_frameDiag]
    exact hu s
  rw [← hσ s, hinj h3]

theorem exists_simpleRealization_of_frame_with_baseChange
    {τ : Tag} {p : ℕ} [NeZero p] {K : Type} [Field K] [Finite K] [CharP K 2] {w : WeylGroup τ}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g0 : ModGL τ (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hcent : ∀ v : WeylGroup τ, v * w = w * v)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) :
    ∃ m : Fin τ.rank → adjointGroup τ K,
      (∀ i, baseChangeGL (algebraMap K (AlgebraicClosure K)) (m i : ModGL τ K) =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (simple τ i) * g0⁻¹) ∧
      ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p),
        m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s)) := by
  classical
  have hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr_bij : Function.Bijective Fr :=
    frobenius_bijective (k := K) (L := AlgebraicClosure K) Fr hFr
  set σ : AlgebraicClosure K ≃+* AlgebraicClosure K := RingEquiv.ofBijective Fr hFr_bij with hσdef
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hmul : ∀ a b : WeylGroup τ,
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (a * b) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) a *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) b :=
    fun a b => RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (τ := τ)
      (R := AlgebraicClosure K) a b
  have hFr_canon : ∀ v : WeylGroup τ,
      Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v :=
    fun v => by
      simpa only [hσ] using entrywise_canonicalRep (τ := τ) σ v
  have hinv : ∀ a : WeylGroup τ,
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) a⁻¹ =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, inv_mul_cancel, canonicalRep_one]
  have hconj_fixed : ∀ v : WeylGroup τ,
      Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹) =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹ := by
    intro v
    have hwv : (w * v) * w⁻¹ = v := by
      rw [← hcent v]; group
    have hkey : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v := by
      rw [← hinv, ← hmul, ← hmul, hwv]
    calc Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹)
        = (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg0, hFr_canon v]
      _ = g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹ := by
          rw [show (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) *
                canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
                (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
              g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
                canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
                (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ by group,
            hkey]
  have hex : ∀ i : Fin τ.rank,
      ∃ c : adjointGroup τ K,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) =
          g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (simple τ i) *
            g0⁻¹ := by
    intro i
    set v : WeylGroup τ := simple τ i with hv
    have hvv : v * v = 1 := by
      rw [hv]; exact (coxeterSystem τ).simple_mul_simple_self i
    have hn2 : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v ^ 2 = 1 := by
      rw [sq, ← hmul, hvv, canonicalRep_one]
    have hx2 :
        (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹) ^ 2 = 1 := by
      rw [sq, show (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹) *
            (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹) =
          g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) * g0⁻¹ by group,
        ← sq, hn2, mul_one, mul_inv_cancel]
    have : Finite (Subgroup.zpowers
        (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹)) :=
      finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, hx2⟩)
    have hxC : g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹ ∈
        adjointGroup τ (AlgebraicClosure K) :=
      mul_mem (mul_mem hg0C
        (canonicalRep_mem_adjointGroup (coxeterSystem τ) (AlgebraicClosure K) v))
        (inv_mem hg0C)
    have hXC : Subgroup.zpowers
        (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹) ≤
        adjointGroup τ (AlgebraicClosure K) := (Subgroup.zpowers_le).2 hxC
    have hXF : ∀ y ∈ Subgroup.zpowers
          (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹),
        Units.map (entrywiseHom Fr) y = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [map_zpow, hconj_fixed v]
    obtain ⟨c, hc, hcx⟩ := hrat _ inferInstance hXC hXF
      (Subgroup.mem_zpowers (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹))
    exact ⟨⟨c, hc⟩, by simpa [hv] using hcx⟩
  choose m hm using hex
  refine ⟨m, hm, ?_⟩
  intro i s
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have hcomp : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ :
            adjointGroup τ K) : ModGL τ K) =
      g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (simple τ i) *
        ExcFrames.frameDiag (τ := τ) ζ hζ s *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (simple τ i))⁻¹) * g0⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hm i, hbase s]
    group
  rw [hcomp, ExcFrames.canonicalRep_conj_frameDiag]
  exact (hbase (TableBExc.torusAct τ p (simple τ i) s)).symm

theorem exists_simpleRealization_of_frame
    {τ : Tag} {p : ℕ} [NeZero p] {K : Type} [Field K] [Finite K] [CharP K 2] {w : WeylGroup τ}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g0 : ModGL τ (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hcent : ∀ v : WeylGroup τ, v * w = w * v)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) :
    ∃ m : Fin τ.rank → adjointGroup τ K,
      ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p),
        m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s)) := by
  obtain ⟨m, -, hact⟩ := exists_simpleRealization_of_frame_with_baseChange hFr hrat
    hg0C hg0 hcent hbase
  exact ⟨m, hact⟩


theorem excPlusFrameModel_E8_threeFive
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) : GGExcPlusFrameModel .E8 p K := by
  intro E hE hcard hsc
  have : Fact p.Prime := ⟨by rcases hp35 with rfl | rfl <;> norm_num⟩
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcent, -, hι₀, hrange, hbase⟩ :=
    Irred937.exists_langFrame_of_sc (Or.inr rfl) hp35 K hpq E hE hcard hsc
  have hrat : ∀ X : Subgroup (ModGL .E8 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E8 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .E8 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X _ hXC hXF => Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
      (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
        (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)
  obtain ⟨m, hm⟩ := exists_simpleRealization_of_frame hFr hrat hg0C hg0 hcent hbase
  exact ⟨ι₀, m, hι₀, hrange, hm,
    fun g hg => exists_weyl_of_mem_normalizer_of_frame hg0C hι₀ hrange hbase hg⟩

theorem ggTorusReflGenW_E8Plus_threeFive
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusReflGenW p (Tag.E8.rank - 1) (TableBExc.RecipeGroup .E8 K)
      (TableBExc.RecipeID .E8 K) := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  exact ggTorusReflGenW_of_excPlusModel hp hp2
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inr rfl) hp hp2 K
      (excPlusFrameModel_E8_threeFive hp35 K hpq))

end CFSG.StandardType

end
