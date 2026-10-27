module

public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A5
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi1
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
  {E : Subgroup (twistedE6RootGroup K σ)}

@[expose] noncomputable def ggTBJTwE6FrameDatum (F : TwE6Frame K σ n p E) :
    LangDatum Tag.E6 (AlgebraicClosure K) where
  Φ := twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
  q := 2 ^ n
  n := canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v
  g0 := F.g0
  steinberg := ⟨F.Fr, F.fr_eq, diagramMap TwistTag.E6 _, Or.inr ⟨TwistTag.E6, rfl, rfl⟩,
    fun _ => rfl⟩
  n_weyl := ⟨F.v, rfl⟩
  g0_mem := F.g0_mem
  lang := F.lang

theorem ggTBJTwE6_frame_v_eq (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v) :
    F.v = twE6W0 := by
  have h1 : F.v = ggKGEp_w0 .E6 := ggKGEp_eq_w0_of_longest hv
  have h2 : twE6W0 = ggKGEp_w0 .E6 := ggKGEp_eq_w0_of_longest TwE6ThreeRootGen.excIsLongest_twE6W0
  rw [h1, h2]

theorem exists_ggTBJTwE6FrameSetup (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (hp : p.Prime) (hq : 5 ≤ p ∨ 2 ≤ n)
    (hpq : ¬ p ∣ 2 ^ n) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p) (e : twistedE6RootGroup K σ ≃* S.Γ),
      (∀ x, (e x : ModGL Tag.E6 (AlgebraicClosure K)) = ggKGTwY F x) ∧
      (∀ α, S.ρ α = -α) ∧ S.D.q = 2 ^ n ∧
      ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit Tag.E6 a ∈ S.D.torus ↔ ∀ i, a i ^ (2 ^ n + 1) = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let D := ggTBJTwE6FrameDatum F
  let D' := CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum (ℓ := 2)
    (Ω := AlgebraicClosure K) (K := K) Nat.prime_two hn hK F.fr_eq
  have hv' : F.v = twE6W0 := ggTBJTwE6_frame_v_eq F hv
  have hn' : D.n = D'.n := by
    show canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v =
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0
    rw [hv']
    rfl
  have hstep : D.step = D'.step := by
    show (MulAut.conj D.n).toMonoidHom.comp D.Φ = (MulAut.conj D'.n).toMonoidHom.comp D'.Φ
    rw [hn']
    rfl
  have htorus : D.torus = D'.torus := by
    show CFSG.RankThree.PartOne.KE.twistedTorusOf D.n D.Φ =
      CFSG.RankThree.PartOne.KE.twistedTorusOf D'.n D'.Φ
    rw [hn']
    rfl
  have hqD : D.q = D'.q := rfl
  have hρ : FrobRootMap D (Equiv.neg (Fin Tag.E6.rank → ℤ)) := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum_frob
      (ℓ := 2) (Ω := AlgebraicClosure K) (K := K) Nat.prime_two hn hK F.fr_eq
    exact ⟨h1, h2, h3, fun γ hγ => by rw [hstep]; exact h4 γ hγ,
      fun a ha γ hγ => by rw [hqD]; exact h5 a (htorus ▸ ha) γ hγ⟩
  have hfin : Finite D.model :=
    finite_model_twistedE6 (ℓ := 2) Nat.prime_two hn hK hσ F.fr_eq D rfl
  have hn0 : n ≠ 0 := by omega
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 := by
    constructor
    · change IsPrimePow (2 ^ n)
      exact Nat.prime_two.isPrimePow.pow hn0
    · change (((2 ^ n : ℕ)) : AlgebraicClosure K) = 0
      exact (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (2 ^ n)).2 (dvd_pow_self 2 hn0)
  let S : LangSetup Tag.E6 (AlgebraicClosure K) p :=
    D.toSetup p (Equiv.neg (Fin Tag.E6.rank → ℤ)) hρ hp
      (hq.imp_right fun h => show 4 ≤ 2 ^ n from calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h) hqpow hpq hfin
  let e : twistedE6RootGroup K σ ≃* S.Γ :=
    twistedE6EquivΓ (ℓ := 2) Nat.prime_two hn hK hσ F.fr_eq D rfl
  refine ⟨S, e, fun x => ?_, fun α => rfl, rfl, fun a => ?_⟩
  · exact (coe_twistedE6EquivΓ (ℓ := 2) Nat.prime_two hn hK hσ F.fr_eq D rfl x).trans
      (ggKGTwY_apply F x).symm
  · change rootDiagUnit Tag.E6 a ∈ D.torus ↔ _
    rw [htorus]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum_torus (ℓ := 2)
      (Ω := AlgebraicClosure K) (K := K) Nat.prime_two hn hK F.fr_eq

end CFSG.StandardType

end
