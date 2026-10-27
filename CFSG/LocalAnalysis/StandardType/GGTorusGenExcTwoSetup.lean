module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoBase
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.LieType.Chevalley.SingleEdgePerfect
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace ExcTwoGen

private theorem frameDiag_mem_twistedTorus_two
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod 3) →* adjointGroup τ K}
    (hbase : ∀ s : Fin τ.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (s : Fin τ.rank → ZMod 3) :
    ExcFrames.frameDiag ζ hζ s ∈ twistedTorusOf
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr)) := by
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  refine mem_twistedTorusOf.2 ⟨?_, ?_⟩
  · rcases hτ with rfl | rfl
    · exact rootDiagUnit_mem_torusGroup_E7 _
    · exact rootDiagUnit_mem_torusGroup_E8 _
  · have hds : ExcFrames.frameDiag ζ hζ s =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) * g0 := by
      rw [hbase s]
      group
    rw [hds]
    exact frob_conj_baseChange_two hFr hg0 _

theorem exists_langSetup_data_two
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {w : WeylGroup τ}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5),
      S.D.Φ = Units.map (entrywiseHom Fr) ∧ S.D.q = Nat.card K ∧
      S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧ S.D.g0 = g0 ∧
      LangDescent S.D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype) := by
  classical
  let L := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with rfl | rfl | rfl <;> simp)
  let D : LangDatum τ L :=
    { Φ := Units.map (entrywiseHom Fr)
      q := Nat.card K
      n := canonicalRep (coxeterSystem τ) L w
      g0 := g0
      steinberg := ⟨Fr, hFr, ⟨1, Or.inl rfl, fun g => by simp⟩⟩
      n_weyl := ⟨w, rfl⟩
      g0_mem := hg0C
      lang := hg0 }
  have hd : LangDescent D 7 ((baseChangeGL (algebraMap K L)).comp
      (adjointGroup τ K).subtype) := by
    rcases hτ with h | h | h
    · exact langDescent_untw 3 (Or.inl ⟨h, rfl⟩) hFr D rfl Nat.prime_seven (by norm_num) hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven
        (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven
        (by norm_num) hperf
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    refine ⟨?_, ?_⟩
    · show IsPrimePow (Nat.card K)
      rw [hK]
      exact Nat.prime_two.isPrimePow
    · show ((Nat.card K : ℕ) : L) = 0
      rw [hK]
      exact (CharP.cast_eq_zero_iff L 2 2).2 (dvd_refl 2)
  have hpq : ¬ 5 ∣ D.q := by
    show ¬ 5 ∣ Nat.card K
    rw [hK]
    norm_num
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let S : LangSetup τ L 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hd.finite_model
  exact ⟨S, rfl, rfl, rfl, rfl, hd⟩

theorem exists_langSetup_of_langFrame_two
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {w : WeylGroup τ} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g0 : ModGL τ (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod 3) →* adjointGroup τ K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hζo : orderOf ζ = 3)
    (hbase : ∀ s : Fin τ.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (hinj : Function.Injective ι₀) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D.Φ = Units.map (entrywiseHom Fr) ∧ S.D.q = Nat.card K ∧
      S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s : Fin τ.rank → ZMod 3,
        ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s) ∧
      ∀ s : Fin τ.rank → ZMod 3, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus := by
  classical
  obtain ⟨S, hΦ, hq, hn, hg0S, hd⟩ := exists_langSetup_data_two (Or.inr hτ) hK hFr hg0C hg0
  let bc : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype
  let ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp bc
  have hι : ∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL τ K) * g0 := by
    intro c
    change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL τ K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hrange : ι.range = S.Γ := by
    have hcomp : ι = (MulAut.conj g0⁻¹).toMonoidHom.comp bc := rfl
    rw [hcomp, MonoidHom.range_comp, show S.Γ = S.D.Γ from rfl, hd.Γ_eq, hg0S]
  have hinjι : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp
      (Subgroup.subtype_injective _))
  refine ⟨S, ι, hΦ, hq, hn, hinjι, hrange, ?_, ?_⟩
  · intro s
    rw [hι, hbase s]
    group
  · intro s
    have hmem := frameDiag_mem_twistedTorus_two hτ hFr hg0 hζ hbase s
    rw [show S.D.torus = twistedTorusOf (canonicalRep (coxeterSystem τ)
      (AlgebraicClosure K) w) (Units.map (entrywiseHom Fr)) from by
        rw [LangDatum.torus, hΦ, hn]]
    exact hmem

end ExcTwoGen

end CFSG.StandardType
