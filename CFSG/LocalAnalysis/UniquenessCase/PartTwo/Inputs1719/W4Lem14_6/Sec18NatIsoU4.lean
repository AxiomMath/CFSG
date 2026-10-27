module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusNatIsoModHolds
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

private theorem exists_statedSU_natTransport {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁]
    [Finite K₂] (hcard : Nat.card K₁ = Nat.card K₂) (n q : ℕ) :
    ∃ (χ : ↥(StatedSU n q K₁) ≃* ↥(StatedSU n q K₂))
      (B : Multiplicative (Fin n → K₁) ≃* Multiplicative (Fin n → K₂)),
      ∀ (γ : ↥(StatedSU n q K₁)) (x : Multiplicative (Fin n → K₁)),
        B (natAct (StatedSU n q K₁) γ x) =
          natAct (StatedSU n q K₂) (χ γ) (B x) := by
  classical
  letI : Fintype K₁ := Fintype.ofFinite K₁
  letI : Fintype K₂ := Fintype.ofFinite K₂
  obtain ⟨σ, -⟩ : ∃ σ : K₁ ≃+* K₂, True :=
    ⟨CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hcard, trivial⟩
  have hmap : (StatedSU n q K₁).map
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n) σ).toMonoidHom =
        StatedSU n q K₂ :=
    CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU σ n q
  let χ : ↥(StatedSU n q K₁) ≃* ↥(StatedSU n q K₂) :=
    ((CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n) σ).subgroupMap
      (StatedSU n q K₁)).trans (MulEquiv.subgroupCongr hmap)
  let B : Multiplicative (Fin n → K₁) ≃* Multiplicative (Fin n → K₂) :=
    (AddEquiv.piCongrRight fun _ => σ.toAddEquiv).toMultiplicative
  have hB : ∀ w : Fin n → K₁, B (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd (fun i => σ (w i)) := fun _ => rfl
  have hχ : ∀ (γ : ↥(StatedSU n q K₁)),
      ((χ γ : StatedSU n q K₂) : GL (Fin n) K₂) =
        (((γ : StatedSU n q K₁) : GL (Fin n) K₁)).map σ := fun γ => rfl
  refine ⟨χ, B, fun γ x => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from (ofAdd_toAdd x).symm]
  simp only [natAct, hB, toAdd_ofAdd, hχ]
  funext i
  exact RingHom.map_mulVec (σ : K₁ →+* K₂) ((γ : StatedSU n q K₁) : GL (Fin n) K₁)
    (Multiplicative.toAdd x) i

private theorem exists_natAct_intertwine_statedSU {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (α : MulAut ↥(StatedSU 4 (2 ^ n) K)) :
    ∃ A : Multiplicative (Fin 4 → K) ≃* Multiplicative (Fin 4 → K),
      ∀ (γ : ↥(StatedSU 4 (2 ^ n) K)) (x : Multiplicative (Fin 4 → K)),
        A (natAct (StatedSU 4 (2 ^ n) K) γ x) =
          natAct (StatedSU 4 (2 ^ n) K) (α γ) (A x) := by
  classical
  have hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, pow_two, ← pow_add]; congr 1; omega⟩
  haveI : CharP K 2 := hfield.charP
  have hbot : (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ n) K) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot (K := K) (2 ^ n)
  let eP : StatedProj (StatedSU 4 (2 ^ n) K) ≃* ↥(StatedSU 4 (2 ^ n) K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have heP : ∀ x : ↥(StatedSU 4 (2 ^ n) K), eP (QuotientGroup.mk x) = x := fun _ => rfl
  obtain ⟨σ, B, -, hγ⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.AutSU.exists_isometry_of_mulAut_statedProj
      (m := 2) (ε := 0) hfield (by norm_num) (by norm_num) (MulAut.congr eP.symm α)
  have hαg : ∀ g : ↥(StatedSU 4 (2 ^ n) K),
      ((α g : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ (g : GL (Fin 4) K) *
          B⁻¹ := by
    intro g
    obtain ⟨hg, h1⟩ := hγ g
    have h4 : eP (MulAut.congr eP.symm α (QuotientGroup.mk g)) = α g := by
      show eP (eP.symm (α (eP (QuotientGroup.mk g)))) = α g
      rw [heP, MulEquiv.apply_symm_apply]
    have h2 : α g = ⟨B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ
        (g : GL (Fin 4) K) * B⁻¹, hg⟩ := by
      have h3 := congrArg eP h1
      rw [h4] at h3
      simpa [heP] using h3
    exact congrArg Subtype.val h2
  have hmat : ∀ g : ↥(StatedSU 4 (2 ^ n) K),
      (((α g : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (B : Matrix (Fin 4) (Fin 4) K) *
          (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map σ *
            (B⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    intro g
    have h := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) (hαg g)
    simpa [Units.val_mul, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut] using h
  let Av : (Fin 4 → K) ≃+ (Fin 4 → K) :=
    (AddEquiv.piCongrRight fun _ => σ.toAddEquiv).trans
      (Matrix.toLinearEquiv' B (Units.invertible B)).toAddEquiv
  have hAv : ∀ w : Fin 4 → K, Av w = B *ᵥ (fun i => σ (w i)) := fun _ => rfl
  refine ⟨Av.toMultiplicative, fun γ x => ?_⟩
  let M : Matrix (Fin 4) (Fin 4) K :=
    (((γ : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hmv : ∀ (w : Fin 4 → K),
      (fun i => σ (Matrix.mulVec M w i)) = M.map σ *ᵥ (fun i => σ (w i)) := by
    intro w
    exact funext fun i => RingHom.map_mulVec (σ : K →+* K) M w i
  have hBB : (B⁻¹ : Matrix (Fin 4) (Fin 4) K) * (B : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simpa [Units.val_mul] using
      congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) (inv_mul_cancel B)
  have hkey : (((α γ : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *
      (B : Matrix (Fin 4) (Fin 4) K) =
        (B : Matrix (Fin 4) (Fin 4) K) * M.map σ := by
    rw [hmat γ, Matrix.mul_assoc, hBB, Matrix.mul_one]
  apply Multiplicative.toAdd.injective
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from (ofAdd_toAdd x).symm]
  change Av (Matrix.mulVec M (Multiplicative.toAdd x)) =
    Matrix.mulVec (((α γ : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K))
      (Av (Multiplicative.toAdd x))
  rw [hAv, hAv, hmv]
  calc (B : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (M.map σ *ᵥ fun i => σ (Multiplicative.toAdd x i))
      = ((B : Matrix (Fin 4) (Fin 4) K) * M.map σ) *ᵥ
          (fun i => σ (Multiplicative.toAdd x i)) := by rw [Matrix.mulVec_mulVec]
    _ = ((((α γ : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (B : Matrix (Fin 4) (Fin 4) K)) *ᵥ
            (fun i => σ (Multiplicative.toAdd x i)) := by rw [hkey]
    _ = (((α γ : StatedSU 4 (2 ^ n) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          ((B : Matrix (Fin 4) (Fin 4) K) *ᵥ
            (fun i => σ (Multiplicative.toAdd x i))) := by rw [Matrix.mulVec_mulVec]

theorem k146NatIsoU4_holds : K146NatIsoU4 := by
  intro W _ _ hW L n I J hU4 hn hdisj
  rcases hdisj with ⟨hI, hJ⟩ | ⟨hI, hJ⟩
  · obtain ⟨K₁, hKf₁, hKfin₁, hcard₁, hreal₁⟩ := hI
    obtain ⟨K₂, hKf₂, hKfin₂, hcard₂, hreal₂⟩ := hJ
    letI := hKf₁
    letI := hKfin₁
    letI := hKf₂
    letI := hKfin₂
    obtain ⟨π₁, hπ₁⟩ := hreal₁
    obtain ⟨π₂, hπ₂⟩ := hreal₂
    have hinj₁ := FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful _) hπ₁
    have hinj₂ := FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful _) hπ₂
    let e₁ := MulEquiv.ofBijective π₁ ⟨hinj₁, hπ₁.1⟩
    let e₂ := MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂.1⟩
    let φ : ↥(StatedSU 4 (2 ^ n) K₁) ≃* ↥(StatedSU 4 (2 ^ n) K₂) := e₁.trans e₂.symm
    obtain ⟨χ, B, hB⟩ :=
      exists_statedSU_natTransport (n := 4) (q := 2 ^ n) (hcard₁.trans hcard₂.symm)
    obtain ⟨A₁, hA₁⟩ :=
      exists_natAct_intertwine_statedSU (n := n) (by omega) hcard₁ (φ.trans χ.symm)
    have hiso : CFSG.Quasithin.H.Pair.IsoMod L I J :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isoMod_of_realizesVia_nat_intertwine
        hπ₁ hπ₂ φ.toMonoidHom φ.surjective
        (MonoidHom.ext fun γ => e₂.apply_symm_apply (e₁ γ)) (A₁.trans B) (by
          intro γ x
          rw [MulEquiv.trans_apply, hA₁, hB]
          exact congrArg (fun g => natAct _ g (B (A₁ x))) (χ.apply_symm_apply (φ γ)))
    have hsI : StableUnder L I := fun x hx => hπ₁.2.2.2.1 ⟨x, hx⟩
    have hsJ : StableUnder L J := fun x hx => hπ₂.2.2.2.1 ⟨x, hx⟩
    obtain ⟨e, he⟩ := hiso
    exact CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_SecIsoOn_of_mulEquiv
      hsI hsJ e (fun g hg x => he g hg x (hsI g hg (x : W) x.2))
  · have hiso :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.k_Omega6Minus_natIsoMod_holds L I J n hI hJ
    obtain ⟨-, K₁, hKf₁, hKfin₁, b₁, c₁, hcard₁, hirr₁, hreal₁⟩ := hI
    obtain ⟨-, K₂, hKf₂, hKfin₂, b₂, c₂, hcard₂, hirr₂, hreal₂⟩ := hJ
    letI := hKf₁
    letI := hKfin₁
    letI := hKf₂
    letI := hKfin₂
    obtain ⟨π₁, hπ₁⟩ := hreal₁
    obtain ⟨π₂, hπ₂⟩ := hreal₂
    have hsI : StableUnder L I := fun x hx => hπ₁.2.2.2.1 ⟨x, hx⟩
    have hsJ : StableUnder L J := fun x hx => hπ₂.2.2.2.1 ⟨x, hx⟩
    obtain ⟨e, he⟩ := hiso
    exact CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_ta_SecIsoOn_of_mulEquiv
      hsI hsJ e (fun g hg x => he g hg x (hsI g hg (x : W) x.2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
