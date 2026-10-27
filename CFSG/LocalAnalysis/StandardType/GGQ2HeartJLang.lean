module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Lang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}

@[expose] noncomputable def ggQ2HeartJDatum (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0) :
    LangDatum Tag.E6 (AlgebraicClosure K) where
  Φ := twistHom TwistTag.E6 (AlgebraicClosure K) Fr
  q := 2 ^ n
  n := canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0
  g0 := g
  steinberg := ⟨Fr, hFr, diagramMap TwistTag.E6 _, Or.inr ⟨TwistTag.E6, rfl, rfl⟩,
    fun _ => rfl⟩
  n_weyl := ⟨twE6W0, rfl⟩
  g0_mem := hg
  lang := hlang

theorem ggQ2HeartJ_langSetup (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5) (e : twistedE6RootGroup K σ ≃* S.Γ),
      (∀ x, (e x : ModGL Tag.E6 (AlgebraicClosure K)) =
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g) ∧
      (∀ α, S.ρ α = -α) ∧ S.D.q = 2 ^ n ∧ S.IsAlgebraic ∧
      ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit Tag.E6 a ∈ S.D.torus ↔ ∀ i, a i ^ (2 ^ n + 1) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let D := ggQ2HeartJDatum Fr hFr g hg hlang
  let D' := CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum (ℓ := 2)
    (Ω := AlgebraicClosure K) (K := K) Nat.prime_two hn hK hFr
  have hn' : D.n = D'.n := rfl
  have hstep : D.step = D'.step := by
    show (MulAut.conj D.n).toMonoidHom.comp D.Φ = (MulAut.conj D'.n).toMonoidHom.comp D'.Φ
    rw [hn']
    rfl
  have htorus : D.torus = D'.torus := by
    show CFSG.RankThree.PartOne.KE.twistedTorusOf D.n D.Φ =
      CFSG.RankThree.PartOne.KE.twistedTorusOf D'.n D'.Φ
    rw [hn']
    rfl
  have hq : D.q = D'.q := rfl
  have hρ : FrobRootMap D (Equiv.neg (Fin Tag.E6.rank → ℤ)) := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum_frob
      (ℓ := 2) (Ω := AlgebraicClosure K) (K := K) Nat.prime_two hn hK hFr
    exact ⟨h1, h2, h3, fun γ hγ => by rw [hstep]; exact h4 γ hγ,
      fun a ha γ hγ => by rw [hq]; exact h5 a (htorus ▸ ha) γ hγ⟩
  have hfin : Finite D.model :=
    finite_model_twistedE6 (ℓ := 2) Nat.prime_two hn hK hσ hFr D rfl
  have hn0 : n ≠ 0 := by omega
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 := by
    constructor
    · change IsPrimePow (2 ^ n)
      exact Nat.prime_two.isPrimePow.pow hn0
    · change (((2 ^ n : ℕ)) : AlgebraicClosure K) = 0
      exact (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (2 ^ n)).2 (dvd_pow_self 2 hn0)
  have h5q : ¬ 5 ∣ D.q := by
    change ¬ 5 ∣ 2 ^ n
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_two).1
      ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h)
    omega
  let S : LangSetup Tag.E6 (AlgebraicClosure K) 5 :=
    D.toSetup 5 (Equiv.neg (Fin Tag.E6.rank → ℤ)) hρ (by norm_num) (Or.inl le_rfl) hqpow h5q hfin
  let e : twistedE6RootGroup K σ ≃* S.Γ :=
    twistedE6EquivΓ (ℓ := 2) Nat.prime_two hn hK hσ hFr D rfl
  have hAlg : S.IsAlgebraic :=
    LangSetup.isAlgebraic_of_isAlgClosure S K 2 (by
      change Nat.card K = (2 ^ n) ^ 2
      exact hK)
  refine ⟨S, e, fun x => ?_, fun α => rfl, rfl, hAlg, fun a => ?_⟩
  · exact coe_twistedE6EquivΓ (ℓ := 2) Nat.prime_two hn hK hσ hFr D rfl x
  · change rootDiagUnit Tag.E6 a ∈ D.torus ↔ _
    rw [htorus]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.twE6EnnolaDatum_torus (ℓ := 2)
      (Ω := AlgebraicClosure K) (K := K) Nat.prime_two hn hK hFr

end CFSG.StandardType

end
