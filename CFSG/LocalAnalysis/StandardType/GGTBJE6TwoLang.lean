module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.RankThree.PartOne.K133H.G2Plane

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.StandardType.ExcFrames.E6QPlusThree CFSG.RankThree.PartOne.KE6


theorem e6Two_langSetup {K : Type} [Field K] [Finite K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g0 : ModGL .E6 (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} (D : E6QPlusThreeFrame K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hg0C : g0 ∈ adjointGroup .E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * eqpN (AlgebraicClosure K))
    (hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ 2)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.frame s : ModGL .E6 K) =
      g0 * e6ThreeDiag ζ hζ s * g0⁻¹) :
    ∃ (S : LangSetup .E6 (AlgebraicClosure K) 5)
      (ι : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s, ι (D.frame s) = e6ThreeDiag ζ hζ s) ∧
      (∀ s, e6ThreeDiag ζ hζ s ∈ S.D.torus) ∧
      (∀ β, IsRoot .E6 β → S.ρ β = e6W0 • β) := by
  classical
  let L := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let D0 : LangDatum .E6 L := LangDatum.ofFrobenius Fr (Nat.card K) hFr e6W0 hg0C hg0
  have hd : LangDescent D0 7 ((baseChangeGL (algebraMap K L)).comp
      (adjointGroup .E6 K).subtype) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.langDescent_ofFrobenius (Or.inr (Or.inl rfl)) e6W0 K hFr
      hg0C hg0
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hqpow : IsPrimePow D0.q ∧ ((D0.q : ℕ) : L) = 0 := by
    refine ⟨?_, ?_⟩
    · show IsPrimePow (Nat.card K)
      rw [hK]
      exact Nat.prime_two.isPrimePow.pow f.ne_zero
    · show ((Nat.card K : ℕ) : L) = 0
      rw [hK]
      exact (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 f.ne_zero)
  have hpq : ¬ 5 ∣ D0.q := by
    show ¬ 5 ∣ Nat.card K
    rw [hK]
    intro h5
    have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h5
    norm_num at h52
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved .E6 L D0
  let S : LangSetup .E6 L 5 :=
    D0.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hd.finite_model
  have hSD : S.D = D0 := rfl
  let bc : adjointGroup .E6 K →* ModGL .E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype
  let ι : adjointGroup .E6 K →* ModGL .E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp bc
  have hι : ∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0 := by
    intro c
    change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) (c : ModGL .E6 K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hrange : ι.range = S.Γ := by
    have hcomp : ι = (MulAut.conj g0⁻¹).toMonoidHom.comp bc := rfl
    rw [hcomp, MonoidHom.range_comp, show S.Γ = S.D.Γ from rfl, hSD, hd.Γ_eq]
    rfl
  have hinjι : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp
      (Subgroup.subtype_injective _))
  have hιframe : ∀ s, ι (D.frame s) = e6ThreeDiag ζ hζ s := by
    intro s
    rw [hι, hcoord s]
    group
  refine ⟨S, ι, rfl, hinjι, hrange, hιframe, ?_, ?_⟩
  · intro s
    show e6ThreeDiag ζ hζ s ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf (eqpN L)
      (Units.map (entrywiseHom Fr))
    rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mem_twistedTorusOf_iff_negPhi]
    exact ⟨rootDiagUnit_mem_torusGroup _, negPhi_eqpN_e6ThreeDiag Fr hζ hFrζ s⟩
  · intro β hβ
    exact S.rho_eq_smul_of_frob (fun c => hFr c) rfl rfl hβ

end CFSG.StandardType

end
