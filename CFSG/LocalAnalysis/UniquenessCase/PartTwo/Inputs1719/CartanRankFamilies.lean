module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcFields
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.UniquenessCase.Lie.CoprimeLift
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.RankThree.PartOne.S10.TransitiveSemisimpleOddKernel
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
public import CFSG.Quasithin.SteinbergBICommonNormalizerTools
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus
public import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcE6
import CFSG.Quasithin.Vol2.Ch12Sec6P31LieG
import CFSG.LieType.Chevalley.PosUnipotentSylow
import CFSG.GroupTheory.PermSylowTwo.Alt
import CFSG.ClassicalGroups.Orthogonal.DiagTorusFlagStabilizer
import CFSG.LieType.Chevalley.TorusNormalizesPosUnipotent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open Matrix
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_CartanRankFamily (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f →
    LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f - 1 →
        (t = .PSL → ¬ r ∣ m) → (t = .E6 → r ≠ 3) →
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤
            CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S))

@[expose] def K_CartanRank_PSL : Prop := K_CartanRankFamily .PSL

@[expose] def K_CartanRank_PSU : Prop := K_CartanRankFamily .PSU

@[expose] def K_CartanRank_PSp : Prop := K_CartanRankFamily .PSp

@[expose] def K_CartanRank_POmegaOdd : Prop := K_CartanRankFamily .POmegaOdd

@[expose] def K_CartanRank_POmegaPlus : Prop := K_CartanRankFamily .POmegaPlus

@[expose] def K_CartanRank_POmegaMinus : Prop := K_CartanRankFamily .POmegaMinus

@[expose] def K_CartanRank_G2 : Prop := K_CartanRankFamily .G2

@[expose] def K_CartanRank_F4 : Prop := K_CartanRankFamily .F4

@[expose] def K_CartanRank_E6 : Prop := K_CartanRankFamily .E6

@[expose] def K_CartanRank_E7 : Prop := K_CartanRankFamily .E7

@[expose] def K_CartanRank_E8 : Prop := K_CartanRankFamily .E8

@[expose] def K_CartanRank_twistedE6 : Prop := K_CartanRankFamily .twistedE6

@[expose] def K_CartanRank_trialityD4 : Prop := K_CartanRankFamily .trialityD4

@[expose] def K_CartanRank_twistedB2 : Prop := K_CartanRankFamily .twistedB2

@[expose] def K_CartanRank_twistedG2 : Prop := K_CartanRankFamily .twistedG2

@[expose] def K_CartanRank_twistedF4 : Prop := K_CartanRankFamily .twistedF4

@[expose] def K_CartanRank_Tits : Prop := K_CartanRankFamily .Tits

theorem k_CartanRank_of_families
    (hPSL : K_CartanRank_PSL) (hPSU : K_CartanRank_PSU) (hPSp : K_CartanRank_PSp)
    (hPOdd : K_CartanRank_POmegaOdd) (hPOPlus : K_CartanRank_POmegaPlus)
    (hPOMinus : K_CartanRank_POmegaMinus) (hG2 : K_CartanRank_G2) (hF4 : K_CartanRank_F4)
    (hE6 : K_CartanRank_E6) (hE7 : K_CartanRank_E7) (hE8 : K_CartanRank_E8)
    (htwE6 : K_CartanRank_twistedE6) (hD4 : K_CartanRank_trialityD4)
    (hB2 : K_CartanRank_twistedB2) (hG2Tw : K_CartanRank_twistedG2)
    (hF4Tw : K_CartanRank_twistedF4) (hTits : K_CartanRank_Tits) :
    K_CartanRank := by
  intro K _ _ t m f hadm hmodel hq hodd S hS r hr hr2 hrdvd hPSLside hE6side
  change K_CartanRankFamily .PSL at hPSL
  change K_CartanRankFamily .PSU at hPSU
  change K_CartanRankFamily .PSp at hPSp
  change K_CartanRankFamily .POmegaOdd at hPOdd
  change K_CartanRankFamily .POmegaPlus at hPOPlus
  change K_CartanRankFamily .POmegaMinus at hPOMinus
  change K_CartanRankFamily .G2 at hG2
  change K_CartanRankFamily .F4 at hF4
  change K_CartanRankFamily .E6 at hE6
  change K_CartanRankFamily .E7 at hE7
  change K_CartanRankFamily .E8 at hE8
  change K_CartanRankFamily .twistedE6 at htwE6
  change K_CartanRankFamily .trialityD4 at hD4
  change K_CartanRankFamily .twistedB2 at hB2
  change K_CartanRankFamily .twistedG2 at hG2Tw
  change K_CartanRankFamily .twistedF4 at hF4Tw
  change K_CartanRankFamily .Tits at hTits
  cases t
  · exact hPSL K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun _ => hPSLside rfl)
      (fun h => absurd h (by decide))
  · exact hPSU K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hPSp K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hPOdd K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hPOPlus K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hPOMinus K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hG2 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hF4 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hE6 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun _ => hE6side rfl)
  · exact hE7 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hE8 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact htwE6 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hD4 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hB2 K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hG2Tw K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hF4Tw K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
  · exact hTits K m f hadm hmodel hq hodd S hS r hr hr2 hrdvd (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))

theorem cartanRank_le_of_borelWit {K : Type} [Group K] [Finite K] {t : CFSG.Open.StatedLieTag}
    {m l r : ℕ} (hrank : CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m = l)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K r l)
    (hr : r.Prime) (hr2 : r ≠ 2) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤
      CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  rw [hrank]
  exact (le_pRank_normalizerQuotient_of_borelWit hr hr2 h S hS).1

theorem uc22p20oBorelWit_map_equiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) {r k : ℕ}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit Y r k) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit X r k := by
  intro P
  let P' : Sylow 2 Y := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨F, hFN, hFE, hFc⟩ := h P'
  refine ⟨F.map e.symm.toMonoidHom, ?_,
    CFSG.SectionRank.isElemAbelian_map hFE e.symm.toMonoidHom, ?_⟩
  · have hP' : (P' : Subgroup Y) = (P : Subgroup X).map e.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
    have hback : (P' : Subgroup Y).map e.symm.toMonoidHom = P := by
      rw [hP', Subgroup.map_map]
      simp
    have hle := Subgroup.le_normalizer_map (H := (P' : Subgroup Y)) e.symm.toMonoidHom
    rw [hback] at hle
    exact (Subgroup.map_mono hFN).trans hle
  · rw [Subgroup.card_map_of_injective e.symm.injective, hFc]

section ChevalleyTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Matrix

theorem torusCoordHom_injective_on_pow_eq_one {τ : Tag} {K : Type} [Field K]
    {r : ℕ} (hr : r.Prime) (hdet : ¬ (r : ℤ) ∣ τ.cartan.det)
    {t : Fin τ.rank → Kˣ} (hpow : ∀ i, t i ^ r = 1)
    (ht : torusCoordHom τ K t = 1) : t = 1 := by
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_eq_one_of_prod_zpow_eq_one
    (A := τ.cartan) (B := τ.cartan.det.sign • τ.cartan.adjugate) (m := τ.cartan.det.natAbs)
    (by rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, Int.sign_mul_self, natCast_zsmul])
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2
      fun h => hdet (Int.natCast_dvd.2 h))) hpow fun j => Units.ext ?_
  have h := torusCoordHom_apply_rootVec_single (R := K) t j
  rw [ht, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
    rootVec_eq_single_of_isRoot (isRoot_single τ j)] at h
  have h' := congrArg (fun v : RootModule τ K =>
    v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) h
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
  rw [Units.val_one, ← h']

end ChevalleyTorus

section ChevalleyBorel

open CFSG.Blueprint.Chevalley CFSG.Blueprint.Multiplier CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.UniquenessCase.UC22


theorem exists_torus_elemAbelian_adjointChevalley {τ : Tag} {K : Type} [Field K] [Finite K]
    [CharP K 2] {r : ℕ} (hr : r.Prime) (hdet : ¬ (r : ℤ) ∣ τ.cartan.det)
    (hdvd : r ∣ Nat.card K - 1) :
    ∃ F : Subgroup (adjointGroup τ K),
      F ≤ Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K)) ∧
      IsElemAbelian r F ∧ Nat.card F = r ^ τ.rank := by
  have : Fact r.Prime := ⟨hr⟩
  have hdvd' : r ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hdvd'
  let μ : Subgroup Kˣ := Subgroup.zpowers u
  have hcardμ : Nat.card μ = r := by rw [Nat.card_zpowers, hu]
  let φ : (Fin τ.rank → μ) →* (Fin τ.rank → Kˣ) :=
    { toFun := fun x i => ((x i : μ) : Kˣ)
      map_one' := rfl
      map_mul' := fun x y => rfl }
  have hTle : torusGroup τ K ≤ adjointGroup τ K :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨⟨i, t⟩, rfl⟩
      exact torusElt_mem_adjointGroup i t)
  let δ : (Fin τ.rank → μ) →* adjointGroup τ K :=
    (Subgroup.inclusion hTle).comp ((torusCoordHom τ K).comp φ)
  have hpow : ∀ x : Fin τ.rank → μ, ∀ i, ((x i : μ) : Kˣ) ^ r = 1 := by
    intro x i
    have h : (x i) ^ r = 1 := by
      have h1 : (x i) ^ Nat.card μ = 1 := pow_card_eq_one'
      rwa [hcardμ] at h1
    simpa using congrArg (fun a : μ => ((a : Kˣ))) h
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : torusCoordHom τ K (fun i => ((x i : μ) : Kˣ)) = 1 := by
      have h1 := congrArg (fun y : adjointGroup τ K => (y : ModGL τ K)) hx
      simpa [δ, φ] using h1
    have hx1 : (fun i => ((x i : μ) : Kˣ)) = 1 :=
      torusCoordHom_injective_on_pow_eq_one hr hdet (hpow x) hx'
    funext i
    exact Subtype.ext (congrFun hx1 i)
  have hpowP : ∀ x : Fin τ.rank → μ, x ^ r = 1 := by
    intro x
    funext i
    have h : (x i) ^ r = 1 := by
      have h1 : (x i) ^ Nat.card μ = 1 := pow_card_eq_one'
      rwa [hcardμ] at h1
    exact h
  have hE : IsElemAbelian r δ.range := uc22pwlie_range_isElemAbelian δ hpowP
  have hcard : Nat.card δ.range = r ^ τ.rank := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_pi, hcardμ]
  have hN : δ.range ≤ Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K)) := by
    rintro _ ⟨x, rfl⟩
    have hxT : δ x ∈ torusSub τ K := by
      change ((δ x : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K
      exact (torusCoordHom τ K (fun i => ((x i : μ) : Kˣ))).2
    exact torusSub_le_normalizer_posUnipotentSub hxT
  exact ⟨δ.range, hN, hE, hcard⟩

theorem exists_borelWit_adjointGroup_chevalley {τ : Tag} {K : Type} [Field K] [Finite K]
    [CharP K 2] {r : ℕ} (hr : r.Prime) (hdet : ¬ (r : ℤ) ∣ τ.cartan.det)
    (hdvd : r ∣ Nat.card K - 1) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit (adjointGroup τ K) r τ.rank := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hN, hE, hcard⟩ :=
    exists_torus_elemAbelian_adjointChevalley (τ := τ) (K := K) hr hdet hdvd
  obtain ⟨-, hP2, hPi⟩ := CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_subgroupOf_top
    (isSylowTwoOf_posUnipotent (K := K) τ)
  have hidx : ¬ 2 ∣ (posUnipotentSub τ K).index := by
    rw [← Subgroup.relIndex_top_right (H := posUnipotentSub τ K)]
    exact hPi
  let P0 : Sylow 2 (adjointGroup τ K) := hP2.toSylow hidx
  have hP0coe : (P0 : Subgroup (adjointGroup τ K)) = posUnipotentSub τ K := by
    ext x
    exact IsPGroup.mem_toSylow hP2 hidx
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_sylow P0 F ?_ hE hcard
  change F ≤ Subgroup.normalizer
    ((P0 : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K))
  rw [hP0coe]
  exact hN

end ChevalleyBorel

section OrthogonalMinusProjective

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open QuadraticMap CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.UniquenessCase.UC22
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem statedScalars_subgroupOf_statedOmega_quadMinus_projective_eq_bot :
    (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus m F b c)) = ⊥ := by
  exact CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (σ := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (K := F)
    (Q := quadMinus m F b c) (Q₀ := StatedQuadMinus m F b c)
    (coe_quadMinus m F b c)
    ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, by
      rw [quadMinus_single_u]
      exact one_ne_zero⟩

theorem exists_borelWit_statedProj_quadMinus (hm : 4 ≤ m) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card F - 1)
    (S : Sylow 2 (StatedProj (StatedOmega (StatedQuadMinus m F b c))))
    (hS : statedProjectiveFlagStabilizer (StatedQuadMinus m F b c)
        (tailModelFlag (m - 1) F (Fin 2)) =
      Subgroup.normalizer ((S : Subgroup (StatedProj (StatedOmega
        (StatedQuadMinus m F b c)))) :
        Set (StatedProj (StatedOmega (StatedQuadMinus m F b c))))) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (StatedProj (StatedOmega (StatedQuadMinus m F b c))) r (m - 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hdvd' : r ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r hdvd'
  let μ : Subgroup Fˣ := Subgroup.zpowers u
  have hcardμ : Nat.card μ = r := by rw [Nat.card_zpowers, hu]
  have hmem_each : ∀ (x : Fin (m - 1) → μ) (j : Fin (m - 1)),
      diagGLMinusHom m F (Pi.mulSingle j ((x j : μ) : Fˣ)) ∈
        StatedOmega (StatedQuadMinus m F b c) := by
    intro x j
    have hdiv : orderOf (((x j : μ) : Fˣ)) ∣ r := by
      rw [Subgroup.orderOf_coe, ← hcardμ]
      exact orderOf_dvd_natCard (x j)
    have hodd : Odd (orderOf (((x j : μ) : Fˣ))) :=
      Odd.of_dvd_nat (hr.odd_of_ne_two hr2) hdiv
    exact minusDiagGen_mem_statedOmega_fin (b := b) (c := c)
      (t := ((x j : μ) : Fˣ)) j hodd rfl
  have hmem : ∀ x : Fin (m - 1) → μ,
      diagGLMinusHom m F (fun j => ((x j : μ) : Fˣ)) ∈
        StatedOmega (StatedQuadMinus m F b c) := by
    intro x
    have hprod : (∏ j : Fin (m - 1), Pi.mulSingle j ((x j : μ) : Fˣ)) =
        fun j => ((x j : μ) : Fˣ) :=
      Finset.univ_prod_mulSingle _
    rw [← hprod, ← Fin.prod_ofFn, map_list_prod]
    refine List.prod_induction _ (fun a b ha hb => Subgroup.mul_mem _ ha hb)
      (Subgroup.one_mem _) ?_
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [List.mem_ofFn] at ha
    obtain ⟨j, rfl⟩ := ha
    exact hmem_each x j
  let f : (Fin (m - 1) → μ) →* StatedOmega (StatedQuadMinus m F b c) :=
    { toFun := fun x => ⟨diagGLMinusHom m F (fun j => ((x j : μ) : Fˣ)), hmem x⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (diagGLMinusHom m F)
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul (diagGLMinusHom m F)
          (fun j => ((x j : μ) : Fˣ)) (fun j => ((y j : μ) : Fˣ)) }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : diagGLMinusHom m F (fun j => ((x j : μ) : Fˣ)) = 1 := by
      exact congrArg (fun y : StatedOmega (StatedQuadMinus m F b c) =>
        (y : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F)) hx
    have hx'' : (fun j => ((x j : μ) : Fˣ)) = 1 := by
      apply diagGLMinusHom_injective m F
      simpa using hx'
    funext j
    exact Subtype.ext (congrFun hx'' j)
  have hpow : ∀ x : Fin (m - 1) → μ, x ^ r = 1 := by
    intro x
    funext j
    have h1 : (x j) ^ Nat.card μ = 1 := pow_card_eq_one'
    rwa [hcardμ] at h1
  have hcardA : Nat.card (Fin (m - 1) → μ) = r ^ (m - 1) := by
    simp [Nat.card_pi, hcardμ]
  have hker : (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus m F b c)) = ⊥ :=
    statedScalars_subgroupOf_statedOmega_quadMinus_projective_eq_bot (F := F) (b := b) (c := c)
  have hπinj : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
        (StatedOmega (StatedQuadMinus m F b c)))) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : y ∈ (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
        (StatedOmega (StatedQuadMinus m F b c)) :=
      (QuotientGroup.eq_one_iff _).1 hy
    rw [hker] at hy'
    exact Subgroup.mem_bot.mp hy'
  let fproj : (Fin (m - 1) → μ) →* StatedProj (StatedOmega (StatedQuadMinus m F b c)) :=
    (QuotientGroup.mk' ((StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus m F b c)))).comp f
  have hfproj : Function.Injective fproj := hπinj.comp hf
  have hE : IsElemAbelian r fproj.range :=
    uc22pwlie_range_isElemAbelian fproj hpow
  have hcard : Nat.card fproj.range = r ^ (m - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfproj).toEquiv, hcardA]
  have hN : fproj.range ≤ Subgroup.normalizer
      ((S : Subgroup (StatedProj (StatedOmega (StatedQuadMinus m F b c)))) :
        Set (StatedProj (StatedOmega (StatedQuadMinus m F b c)))) := by
    rintro _ ⟨x, rfl⟩
    have hxT : f x ∈ (diagTorusMinus m F).subgroupOf
        (StatedOmega (StatedQuadMinus m F b c)) := by
      change ((f x : StatedOmega (StatedQuadMinus m F b c)) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) ∈ diagTorusMinus m F
      exact ⟨fun j => ((x j : μ) : Fˣ), rfl⟩
    have hxD := diagTorusMinus_subgroupOf_le_statedDerivedFlagStabilizer
      (F := F) (b := b) (c := c) hm hxT
    have hxP : QuotientGroup.mk' ((StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
        (StatedOmega (StatedQuadMinus m F b c))) (f x) ∈
        statedProjectiveFlagStabilizer (StatedQuadMinus m F b c)
          (tailModelFlag (m - 1) F (Fin 2)) := by
      have := (statedDerivedFlagStabilizer_map (StatedQuadMinus m F b c)
        (tailModelFlag (m - 1) F (Fin 2))).le ⟨f x, hxD, rfl⟩
      simpa using this
    rw [hS] at hxP
    exact hxP
  exact uc22pwlie_borelWit_of_sylow S fproj.range hN hE hcard

end OrthogonalMinusProjective

section OrthogonalPlusProjective

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open QuadraticMap CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.UniquenessCase.UC22
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_borelWit_statedProj_quadPlus (hm : 4 ≤ m) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card F - 1) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (StatedProj (StatedOmega (StatedQuadPlus m F))) r m := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd' : r ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r hdvd'
  let μ : Subgroup Fˣ := Subgroup.zpowers u
  have hcardμ : Nat.card μ = r := by rw [Nat.card_zpowers, hu]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hmem_each : ∀ (x : Fin m → μ) (j : Fin m),
      diagGLPlusHom m F (Pi.mulSingle j ((x j : μ) : Fˣ)) ∈
        StatedOmega (StatedQuadPlus m F) := by
    intro x j
    have hdiv : orderOf (((x j : μ) : Fˣ)) ∣ r := by
      rw [Subgroup.orderOf_coe, ← hcardμ]
      exact orderOf_dvd_natCard (x j)
    have hodd : Odd (orderOf (((x j : μ) : Fˣ))) :=
      Odd.of_dvd_nat (hr.odd_of_ne_two hr2) hdiv
    exact diagGen_mem_statedOmega_fin (F := F) hm h2 ((x j : μ) : Fˣ) j hodd rfl
  have hmem : ∀ x : Fin m → μ,
      diagGLPlusHom m F (fun j => ((x j : μ) : Fˣ)) ∈
        StatedOmega (StatedQuadPlus m F) := by
    intro x
    have hprod : (∏ j : Fin m, Pi.mulSingle j ((x j : μ) : Fˣ)) =
        fun j => ((x j : μ) : Fˣ) :=
      Finset.univ_prod_mulSingle _
    rw [← hprod, ← Fin.prod_ofFn, map_list_prod]
    refine List.prod_induction _ (fun a b ha hb => Subgroup.mul_mem _ ha hb)
      (Subgroup.one_mem _) ?_
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [List.mem_ofFn] at ha
    obtain ⟨j, rfl⟩ := ha
    exact hmem_each x j
  let f : (Fin m → μ) →* StatedOmega (StatedQuadPlus m F) :=
    { toFun := fun x => ⟨diagGLPlusHom m F (fun j => ((x j : μ) : Fˣ)), hmem x⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (diagGLPlusHom m F)
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul (diagGLPlusHom m F)
          (fun j => ((x j : μ) : Fˣ)) (fun j => ((y j : μ) : Fˣ)) }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : diagGLPlusHom m F (fun j => ((x j : μ) : Fˣ)) = 1 := by
      exact congrArg (fun y : StatedOmega (StatedQuadPlus m F) =>
        (y : GL (Fin m ⊕ Fin m) F)) hx
    have hx'' : (fun j => ((x j : μ) : Fˣ)) = 1 := by
      apply diagGLPlusHom_injective m F
      simpa using hx'
    funext j
    exact Subtype.ext (congrFun hx'' j)
  have hpow : ∀ x : Fin m → μ, x ^ r = 1 := by
    intro x
    funext j
    have h1 : (x j) ^ Nat.card μ = 1 := pow_card_eq_one'
    rwa [hcardμ] at h1
  have hcardA : Nat.card (Fin m → μ) = r ^ m := by
    simp [Nat.card_pi, hcardμ]
  have hker : (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
      (StatedOmega (StatedQuadPlus m F)) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (n := m) (by omega)
  have hπinj : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
        (StatedOmega (StatedQuadPlus m F)))) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : y ∈ (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
        (StatedOmega (StatedQuadPlus m F)) :=
      (QuotientGroup.eq_one_iff _).1 hy
    rw [hker] at hy'
    exact Subgroup.mem_bot.mp hy'
  let fproj : (Fin m → μ) →* StatedProj (StatedOmega (StatedQuadPlus m F)) :=
    (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
      (StatedOmega (StatedQuadPlus m F)))).comp f
  have hfproj : Function.Injective fproj := hπinj.comp hf
  have hE : IsElemAbelian r fproj.range :=
    uc22pwlie_range_isElemAbelian fproj hpow
  have hcard : Nat.card fproj.range = r ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfproj).toEquiv, hcardA]
  obtain ⟨S, hS⟩ := plusProjectiveUnipotent_isSylow (n := m) (K := F) 2 (by omega)
  have hnorm : Subgroup.normalizer (S : Set (StatedProj (StatedOmega
        (StatedQuadPlus m F)))) = plusProjectiveBorel m F := by
    change Subgroup.normalizer ((S : Subgroup (StatedProj (StatedOmega
      (StatedQuadPlus m F)))) : Set (StatedProj (StatedOmega (StatedQuadPlus m F)))) =
        plusProjectiveBorel m F
    rw [hS]
    exact plusProjectiveUnipotent_normalizer (n := m) (K := F) (by omega)
  have hN : fproj.range ≤ Subgroup.normalizer (S : Set (StatedProj (StatedOmega
        (StatedQuadPlus m F)))) := by
    rw [hnorm]
    rintro _ ⟨x, rfl⟩
    have hxT : f x ∈ diagTorusOrth m F := by
      change ((f x : StatedOmega (StatedQuadPlus m F)) :
        GL (Fin m ⊕ Fin m) F) ∈ diagTorusPlus m F
      exact ⟨fun j => ((x j : μ) : Fˣ), rfl⟩
    have hxD := diagTorusOrth_le_statedDerivedFlagStabilizer (F := F) hm hxT
    have hxP : QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
        (StatedOmega (StatedQuadPlus m F))) (f x) ∈
        statedProjectiveFlagStabilizer (StatedQuadPlus m F) (stdFlag m F) := by
      have := (statedDerivedFlagStabilizer_map (StatedQuadPlus m F) (stdFlag m F)).le
        ⟨f x, hxD, rfl⟩
      simpa using this
    simpa [fproj, plusProjectiveBorel] using hxP
  exact uc22pwlie_borelWit_of_sylow S fproj.range hN hE hcard

end OrthogonalPlusProjective

theorem uc22p20oBorelWit_one_of_central_quotient {K : Type} [Group K] [Finite K]
    (Z : Subgroup K) [Z.Normal] (hZ : Z ≤ Subgroup.center K) (hZodd : Odd (Nat.card Z))
    {r : ℕ} (hr : r.Prime)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit (K ⧸ Z) r 1) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K r 1 := by
  have : Fact r.Prime := ⟨hr⟩
  intro P
  let Psub : Subgroup K := P
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  let P' : Sylow 2 (K ⧸ Z) := P.mapSurjective (f := QuotientGroup.mk' Z) hπ
  obtain ⟨F', hF'N, hF'E, hF'c⟩ := h P'
  have hP : IsPGroup 2 Psub := P.isPGroup'
  let F : Subgroup K := F'.comap (QuotientGroup.mk' Z)
  have hFle : F ≤ Subgroup.normalizer (P : Set K) := by
    change F ≤ Subgroup.normalizer (Psub : Set K)
    rw [CFSG.Quasithin.H13.S126P31.normalizer_eq_comap_of_central_odd Z hZ
      hZodd.not_two_dvd_nat hP]
    exact Subgroup.comap_mono hF'N
  have hFcard : Nat.card F = Nat.card Z * r := by
    have h := CFSG.Quasithin.SteinbergBI.card_comap_of_surjective hπ F'
    rw [QuotientGroup.ker_mk'] at h
    change Nat.card (F'.comap (QuotientGroup.mk' Z)) = Nat.card Z * r
    have hF'r : Nat.card F' = r := by simpa using hF'c
    rw [h, hF'r]
  have hdvd : r ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_mul_left r _
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := F) r hdvd
  let y : K := (x : F)
  have hyN : y ∈ Subgroup.normalizer (P : Set K) := hFle x.2
  have hyr : orderOf y = r := by
    rw [show y = ((x : F) : K) from rfl, Subgroup.orderOf_coe, hxord]
  refine ⟨Subgroup.zpowers y, Subgroup.zpowers_le.mpr hyN, ?_, ?_⟩
  · exact CFSG.Open.isElemAbelian_zpowers (by simpa [hyr] using pow_orderOf_eq_one y)
  · rw [Nat.card_zpowers, hyr]
    simp

open CFSG.Blueprint
open CFSG.LieType.Ree

theorem exists_borelWit_suzuki {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ 2 ^ (2 * a + 1) - 1) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit (suzukiGroup a K) r 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have hdvd : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrdvd
  obtain ⟨lam, hlam⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hdvd
  let D : Kˣ →* suzukiGroup a K :=
    { toFun := suzukiDElt a K
      map_one' := suzukiDElt_one
      map_mul' := fun l m => (suzukiDElt_mul l m).symm }
  have hDinj : Function.Injective D := by
    intro l m h
    exact (suzukiDElt_inj hK).1 (by simpa [D] using h)
  have hxord : orderOf (suzukiDElt a K lam) = r := by
    rw [show suzukiDElt a K lam = D lam from rfl, orderOf_injective D hDinj lam, hlam]
  have hTle : suzukiT a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    (suzuki_borel_structure (a := a) (K := K) hK).2.2.2.1
  have hxN : suzukiDElt a K lam ∈
      Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    hTle (suzukiDElt_mem_suzukiT a K lam)
  obtain ⟨P0, hP0⟩ : ∃ P0 : Sylow 2 (suzukiGroup a K),
      (P0 : Subgroup (suzukiGroup a K)) = suzukiU a K :=
    ⟨CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwr1_sz_sylow hK,
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwr1_sz_sylow_coe hK⟩
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_sylow P0
    (Subgroup.zpowers (suzukiDElt a K lam)) ?_ ?_ ?_
  · have hP0set : (P0 : Set (suzukiGroup a K)) =
        (suzukiU a K : Set (suzukiGroup a K)) :=
      congrArg (fun H : Subgroup (suzukiGroup a K) => (H : Set (suzukiGroup a K))) hP0
    rw [hP0set]
    exact Subgroup.zpowers_le.mpr hxN
  · exact CFSG.Open.isElemAbelian_zpowers
      (by simpa [hxord] using pow_orderOf_eq_one (suzukiDElt a K lam))
  · rw [Nat.card_zpowers, hxord]
    simp

theorem k_CartanRank_twistedB2_holds : K_CartanRank_twistedB2 := by
  change K_CartanRankFamily .twistedB2
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨rfl, -, -, -⟩ := hadm.2.2
  obtain ⟨-, a, ha, Kf, hfield, hfin, hf, hKcard, ⟨e⟩⟩ :=
    (LieModel.suzukiModel hmodel).2
  let := hfield
  let := hfin
  have hK' : Nat.card Kf = 2 ^ (2 * a + 1) := by rw [hKcard, hf]
  have hrdvd' : r ∣ 2 ^ (2 * a + 1) - 1 := by rw [← hf]; exact hrdvd
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r 1 :=
    uc22p20oBorelWit_map_equiv e (exists_borelWit_suzuki ha hK' hr hrdvd')
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K r 1 :=
    uc22p20oBorelWit_one_of_central_quotient (Subgroup.center K) le_rfl hodd hr hWY
  exact cartanRank_le_of_borelWit rfl hWK hr hr2 S hS

theorem exists_borelWit_statedSp (m f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f) (hm : 2 ≤ m) {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ 2 ^ f - 1) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit (StatedSp m F) r m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : r ∣ Nat.card F - 1 := by rw [hF]; exact hrdvd
  obtain ⟨ζ, hζ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_zeta hr hdvd
  let μ : Subgroup Fˣ := Subgroup.zpowers ζ
  have hcardμ : Nat.card μ = r := by rw [Nat.card_zpowers, hζ]
  have hexp : ∀ a : μ, a ^ r = 1 := by
    intro a
    have h : orderOf a ∣ Nat.card μ := orderOf_dvd_natCard a
    rw [hcardμ] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  let A : Subgroup (Fin m → Fˣ) := Subgroup.pi Set.univ (fun _ => μ)
  let ψ : A →* StatedSp m F :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom (r := m)
      (k := F)).comp A.subtype
  have hinj : Function.Injective ψ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom_injective.comp
      A.subtype_injective
  have hpow : ∀ a : A, a ^ r = 1 := by
    intro a
    refine Subtype.ext (funext fun i => ?_)
    exact congrArg Subtype.val (hexp ⟨a.1 i, a.2 i (Set.mem_univ i)⟩)
  have hE : IsElemAbelian r ψ.range :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_range_isElemAbelian ψ hpow
  have hcard : Nat.card ψ.range = r ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    rw [CFSG.RankThree.PartOne.TransitiveSemisimple.natCard_pi_univ_subgroup]
    simp [A, hcardμ]
  have hrange : ψ.range ≤ CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torus m F := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have hnorm : Subgroup.normalizer
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent m F :
        Set (StatedSp m F)) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup m F :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.sylow_normalizers
      (r := m) (K := F) (p := 2) (hr := by omega)).1
  have hle : ψ.range ≤ Subgroup.normalizer
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent m F :
        Set (StatedSp m F)) := by
    rw [hnorm]
    exact hrange.trans
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.torus_le_borelSubgroup
        (r := m) (K := F))
  obtain ⟨P0, hP0⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := F) 2 m
  have hN : ψ.range ≤ Subgroup.normalizer (P0 : Set (StatedSp m F)) := by
    have hP0set : (P0 : Set (StatedSp m F)) =
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent m F :
          Set (StatedSp m F)) :=
      congrArg (fun H : Subgroup (StatedSp m F) => (H : Set (StatedSp m F))) hP0
    rw [hP0set]
    exact hle
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_sylow
    P0 ψ.range hN hE hcard

theorem k_CartanRank_PSp_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_PSp := by
  change K_CartanRankFamily .PSp
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm : 2 ≤ m := hadm.2.2.1
  have hoddq : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hoddq)
  have hZ : Subgroup.center K = ⊥ := by
    refine CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_center_eq_bot hN hq hodd hmodel ?_
    show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
    rw [hgcd]
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hZ
  have hmodelK : LieModel K .PSp m 2 f := LieModel.of_mulEquiv e.symm hmodel
  obtain ⟨F, hFld, hFin, hChar, hFcard, ⟨eSp⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel
      hmodelK
  let := hFld
  let := hFin
  let := hChar
  have hW := exists_borelWit_statedSp m f F hFcard hm hr hrdvd
  have hW' := uc22p20oBorelWit_map_equiv eSp hW
  exact cartanRank_le_of_borelWit rfl hW' hr hr2 S hS

section PSU

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22

section SplitUnitary

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  (h : UnitaryFieldData 2 f K) {μ : Subgroup Kˣ}

noncomputable def uc22pwliu_splitA {d : ℕ} (x : Fin d → μ) : Fin d → Kˣ := fun i => (x i : Kˣ)

noncomputable def uc22pwliu_splitD (ε : ℕ) : Fin ε → Kˣ := fun _ => 1

theorem uc22pwliu_splitHd (d ε : ℕ) (x : Fin d → μ) :
    ∀ k, h.norm (uc22pwliu_splitD (K := K) ε k) = 1 := by
  intro k; simp [uc22pwliu_splitD, UnitaryFieldData.norm]

theorem uc22pwliu_splitHp (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) (x : Fin d → μ) :
    torusRatio h (uc22pwliu_splitA (K := K) x) (uc22pwliu_splitD (K := K) ε) = 1 := by
  rw [torusRatio]
  have h1 : ∏ i, (uc22pwliu_splitA (K := K) x i : K) /
      h.bar (uc22pwliu_splitA (K := K) x i) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    have hxi : h.bar ((uc22pwliu_splitA (K := K) x i : K)) =
        (uc22pwliu_splitA (K := K) x i : K) := hinv (x i)
    rw [hxi]
    exact div_self (Units.ne_zero _)
  have h2 : ∏ k, (uc22pwliu_splitD (K := K) ε k : K) = 1 := by simp [uc22pwliu_splitD]
  rw [h1, h2, mul_one]

noncomputable def uc22pwliu_splitElt (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) (x : Fin d → μ) :
    hypSU h d ε :=
  (torusMat_mem_hypSU h (uc22pwliu_splitA (K := K) x)
    (uc22pwliu_splitHd h d ε x) (uc22pwliu_splitHp h d ε hinv x)).choose

theorem uc22pwliu_splitElt_spec (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) (x : Fin d → μ) :
    uc22pwliu_splitElt h d ε hinv x ∈ hypTorus h d ε ∧
      (((uc22pwliu_splitElt h d ε hinv x : GL (HypIndex d ε) K)) :
        Matrix (HypIndex d ε) (HypIndex d ε) K) =
        Matrix.diagonal (torusEntries h (uc22pwliu_splitA (K := K) x)
          (uc22pwliu_splitD (K := K) ε)) :=
  (torusMat_mem_hypSU h (uc22pwliu_splitA (K := K) x)
    (uc22pwliu_splitHd h d ε x) (uc22pwliu_splitHp h d ε hinv x)).choose_spec

noncomputable def uc22pwliu_splitT (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) :
    (Fin d → μ) →* hypSU h d ε where
  toFun := uc22pwliu_splitElt h d ε hinv
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [(uc22pwliu_splitElt_spec h d ε hinv 1).2]
    change _ = (1 : Matrix (HypIndex d ε) (HypIndex d ε) K)
    rw [← Matrix.diagonal_one]
    congr 1
    funext y
    rcases y with i | k | i <;> simp [torusEntries, uc22pwliu_splitA, uc22pwliu_splitD]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (uc22pwliu_splitElt_spec h d ε hinv x).2,
      (uc22pwliu_splitElt_spec h d ε hinv y).2, (uc22pwliu_splitElt_spec h d ε hinv (x * y)).2,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext z
    rcases z with i | k | i <;>
      simp [torusEntries, uc22pwliu_splitA, uc22pwliu_splitD, mul_inv] <;> ring

theorem uc22pwliu_splitT_coe (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) (x : Fin d → μ) :
    (((uc22pwliu_splitT h d ε hinv x : hypSU h d ε) : GL (HypIndex d ε) K) :
        Matrix (HypIndex d ε) (HypIndex d ε) K) =
      Matrix.diagonal (torusEntries h (uc22pwliu_splitA (K := K) x)
        (uc22pwliu_splitD (K := K) ε)) :=
  (uc22pwliu_splitElt_spec h d ε hinv x).2

theorem uc22pwliu_splitT_mem_borel (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) (x : Fin d → μ) :
    uc22pwliu_splitT h d ε hinv x ∈ hypBorel h d ε :=
  hypTorus_le_hypBorel h (uc22pwliu_splitElt_spec h d ε hinv x).1

theorem uc22pwliu_splitT_meet_scalars (d ε : ℕ)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K)) {x : Fin d → μ}
    (hx : uc22pwliu_splitT h d ε hinv x ∈ hypScalars h d ε) : x = 1 := by
  obtain ⟨c, -, hcm, hc⟩ := mem_normOneScalars.1 hx
  have hmat : (((uc22pwliu_splitT h d ε hinv x : hypSU h d ε) : GL (HypIndex d ε) K) :
      Matrix (HypIndex d ε) (HypIndex d ε) K) =
      Matrix.diagonal (torusEntries h (uc22pwliu_splitA (K := K) x)
        (uc22pwliu_splitD (K := K) ε)) := uc22pwliu_splitT_coe h d ε hinv x
  have hc' : (((uc22pwliu_splitT h d ε hinv x : hypSU h d ε) : GL (HypIndex d ε) K) :
      Matrix (HypIndex d ε) (HypIndex d ε) K) = Matrix.scalar (HypIndex d ε) (c : K) := by
    rw [hc]
    rfl
  have hdiag : ∀ y : HypIndex d ε,
      torusEntries h (uc22pwliu_splitA (K := K) x) (uc22pwliu_splitD (K := K) ε) y = (c : K) := by
    intro y
    have := congr_fun (congr_fun (hmat.symm.trans hc') y) y
    simpa [Matrix.scalar_apply] using this
  funext i
  have hai : (uc22pwliu_splitA (K := K) x i : K) = (c : K) := by
    simpa [uc22pwliu_splitA, torusEntries] using hdiag (Sum.inl i)
  have hci : (((uc22pwliu_splitA (K := K) x i)⁻¹ : Kˣ) : K) = (c : K) := by
    rw [Units.val_inv_eq_inv_val]
    have hd := hdiag (Sum.inr (Sum.inr i))
    rw [show torusEntries h (uc22pwliu_splitA (K := K) x) (uc22pwliu_splitD (K := K) ε)
        (Sum.inr (Sum.inr i)) =
        (h.bar ((uc22pwliu_splitA (K := K) x i : K)))⁻¹ from rfl] at hd
    have hbar : h.bar ((uc22pwliu_splitA (K := K) x i : K)) =
        (uc22pwliu_splitA (K := K) x i : K) := by
      simpa [uc22pwliu_splitA] using hinv (x i)
    rw [hbar] at hd
    exact hd
  have hsq : (uc22pwliu_splitA (K := K) x i) * (uc22pwliu_splitA (K := K) x i) = 1 := by
    apply Units.ext
    have hEq : ((uc22pwliu_splitA (K := K) x i : K)) =
        (((uc22pwliu_splitA (K := K) x i)⁻¹ : Kˣ) : K) := hai.trans hci.symm
    calc (↑(uc22pwliu_splitA (K := K) x i) * ↑(uc22pwliu_splitA (K := K) x i) : K)
        = ↑(uc22pwliu_splitA (K := K) x i) * ↑((uc22pwliu_splitA (K := K) x i)⁻¹) := by
          rw [hEq]
      _ = 1 := by
          rw [Units.val_inv_eq_inv_val]
          exact mul_inv_cancel₀ (Units.ne_zero _)
  have ha1 : uc22pwliu_splitA (K := K) x i = 1 := by
    have hsq' : (uc22pwliu_splitA (K := K) x i) ^ 2 = 1 := by
      rw [pow_two]; exact hsq
    have hsqK : ((uc22pwliu_splitA (K := K) x i : K)) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq', Units.val_one]
    have hval : ((uc22pwliu_splitA (K := K) x i : K)) = 1 := by
      rcases sq_eq_one_iff.mp hsqK with h1 | h1
      · exact h1
      · rwa [h1, CharTwo.neg_eq]
    exact Units.ext hval
  apply Subtype.ext
  apply Units.ext
  simpa [uc22pwliu_splitA] using congrArg (fun u : Kˣ => (u : K)) ha1

theorem uc22pwliu_split_core (d ε : ℕ) (hd : 1 ≤ d) (hε : ε ≤ 1)
    (hinv : ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hcard : Nat.card μ = ℓ) (hexp : ∀ a : μ, a ^ ℓ = 1)
    {X : Type} [Group X] [Finite X]
    (α : hypSU h d ε →* X) (hα : Function.Surjective α)
    (hinj : ∀ x : Fin d → μ, α (uc22pwliu_splitT h d ε hinv x) = 1 → x = 1) :
    uc22p20oBorelWit X ℓ d := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : (Fin d → μ) →* X := α.comp (uc22pwliu_splitT h d ε hinv)
  have hφ : Function.Injective ψ :=
    (injective_iff_map_eq_one ψ).2 fun x hx => hinj x hx
  have hpow : ∀ x : Fin d → μ, x ^ ℓ = 1 := by
    intro x
    refine funext fun i => ?_
    simpa using hexp (x i)
  have hE : IsElemAbelian ℓ ψ.range := uc22pwlie_range_isElemAbelian ψ hpow
  have hcardψ : Nat.card ψ.range = ℓ ^ d := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    simp [Nat.card_pi, hcard]
  obtain ⟨-, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow h hd hε
  obtain ⟨P0, hP0⟩ : ∃ P0 : Sylow 2 X,
      (P0 : Subgroup X) = (hypUnitriangular h d ε).map α :=
    ⟨Q.mapSurjective (f := α) hα, by
      rw [Sylow.coe_mapSurjective (f := α) hα Q, hQ]⟩
  have hN : ψ.range ≤ Subgroup.normalizer (P0 : Set X) := by
    have h2 : Subgroup.normalizer (P0 : Set X) =
        Subgroup.normalizer (((hypUnitriangular h d ε).map α : Subgroup X) : Set X) := by
      rw [← hP0]
      rfl
    rw [h2]
    rintro _ ⟨x, rfl⟩
    have hB : uc22pwliu_splitT h d ε hinv x ∈
        Subgroup.normalizer (hypUnitriangular h d ε : Set (hypSU h d ε)) := by
      rw [(CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_Sylow_normalizers h hd hε).1]
      exact uc22pwliu_splitT_mem_borel h d ε hinv x
    exact Subgroup.le_normalizer_map α ⟨_, hB, rfl⟩
  exact uc22pwlie_borelWit_of_sylow P0 ψ.range hN hE hcardψ

theorem uc22pwliu_exists_splitMu {n : ℕ} (h : UnitaryFieldData 2 n K) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓq : ℓ ∣ 2 ^ n - 1) :
    ∃ μ : Subgroup Kˣ, Nat.card μ = ℓ ∧ (∀ a : μ, a ^ ℓ = 1) ∧
      ∀ a : μ, h.bar (((a : Kˣ) : K)) = ((a : Kˣ) : K) := by
  have hcard := UnitaryFieldData.card_eq_sq h
  have hdvdK : ℓ ∣ Nat.card K - 1 := by
    rw [hcard]
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_left hℓq _
  obtain ⟨ζ, hζ⟩ := uc22pwlie_exists_zeta hℓ hdvdK
  let μ : Subgroup Kˣ := Subgroup.zpowers ζ
  have hcardμ : Nat.card μ = ℓ := by rw [Nat.card_zpowers, hζ]
  have hexp : ∀ a : μ, a ^ ℓ = 1 := by
    intro a
    have h : orderOf a ∣ Nat.card μ := orderOf_dvd_natCard a
    rw [hcardμ] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  refine ⟨μ, hcardμ, hexp, fun a => ?_⟩
  have hq1 : ((a : Kˣ) : K) ^ (2 ^ n - 1) = 1 := by
    have h1 : (a : Kˣ) ^ (2 ^ n - 1) = 1 := by
      have horder : orderOf ((a : μ) : Kˣ) ∣ ℓ := by
        rw [Subgroup.orderOf_coe, ← hcardμ]
        exact orderOf_dvd_natCard a
      exact orderOf_dvd_iff_pow_eq_one.1 (horder.trans hℓq)
    simpa using congrArg (fun u : Kˣ => (u : K)) h1
  have hqeq : 2 ^ n = (2 ^ n - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm
  rw [UnitaryFieldData.bar_apply, hqeq, pow_succ, hq1, one_mul]

end SplitUnitary

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_CartanRank_PSU_holds :
    K_CartanRank_PSU := by
  change K_CartanRankFamily .PSU
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, hm3, -⟩ := hadm
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · have hf1' : f = 1 := by omega
    rw [hf1'] at hrdvd
    exact absurd (by simpa using hrdvd) hr.not_dvd_one
  · let d := m / 2
    let ε := m % 2
    have hε : ε ≤ 1 := by
      have := Nat.mod_lt m (by norm_num : 0 < 2)
      omega
    have hm_eq : 2 * d + ε = m := by
      have := Nat.div_add_mod m 2
      simp only [d, ε]
      omega
    have hd : 1 ≤ d := by omega
    have hm3' : 3 ≤ 2 * d + ε := by omega
    have hmodel' : LieModel (K ⧸ Subgroup.center K) .PSU (2 * d + ε) 2 f := by
      rw [hm_eq]; exact hmodel
    obtain ⟨Kf, hFld, hFin, h, ⟨e⟩⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU
        (Y := K ⧸ Subgroup.center K) (n := f) (r := d) (ε := ε) hf (by omega) hmodel'
    let := hFld
    let := hFin
    have : CharP Kf 2 := h.charP
    obtain ⟨μ, hcardμ, hexp, hinv⟩ := uc22pwliu_exists_splitMu h hr hrdvd
    obtain ⟨α, hα, hker, -⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_cover h hε hm3' hf2 hq e
    have hinj : ∀ x : Fin d → μ, α (uc22pwliu_splitT h d ε hinv x) = 1 → x = 1 := by
      intro x hx
      exact uc22pwliu_splitT_meet_scalars h d ε hinv (hker _ hx)
    have hW := uc22pwliu_split_core h d ε hd hε hinv hr hcardμ hexp α hα hinj
    exact cartanRank_le_of_borelWit (by rfl) hW hr hr2 S hS

end PSU

theorem uc22pwlie_borelWit_of_cover_split {m : ℕ} (hm : 2 ≤ m) {k : Type} [Field k] [Finite k]
    [CharP k 2] {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ Nat.card k - 1) (hnd : ¬ r ∣ m)
    {X : Type} [Group X] [Finite X]
    (α : SpecialLinearGroup (Fin m) k →* X) (hα : Function.Surjective α)
    (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) k)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit X r (m - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_zeta hr hrdvd
  let μ : Subgroup kˣ := Subgroup.zpowers ζ
  have hcardμ : Nat.card μ = r := by rw [Nat.card_zpowers, hζ]
  have hexp : ∀ a : μ, a ^ r = 1 := by
    intro a
    have h : orderOf a ∣ Nat.card μ := orderOf_dvd_natCard a
    rw [hcardμ] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  let φ : (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom μ m).ker →* X :=
    α.comp (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_diagHom μ m)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxker :
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_diagHom μ m x ∈ α.ker :=
      MonoidHom.mem_ker.2 hx
    have hxcen : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_diagHom μ m x ∈
        Subgroup.center (SpecialLinearGroup (Fin m) k) := hαc hxker
    have hxscal :
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_diagHom μ m x ∈
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars m k := by
      rwa [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    let i0 : Fin m := ⟨0, by omega⟩
    have hconst : ∀ i : Fin m, x.1 i = x.1 i0 := fun i =>
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_diag_const hxscal i i0
    have hprod : ∏ i : Fin m, x.1 i = 1 := x.2
    have hcm : (x.1 i0) ^ m = 1 := by
      rw [Finset.prod_congr rfl (fun i _ => hconst i)] at hprod
      simpa using hprod
    have hcr : (x.1 i0) ^ r = 1 := hexp (x.1 i0)
    have hcop : Nat.Coprime r m := (hr.coprime_iff_not_dvd).2 hnd
    have hdvd : orderOf (x.1 i0) ∣ Nat.gcd r m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcr) (orderOf_dvd_of_pow_eq_one hcm)
    rw [hcop.gcd_eq_one] at hdvd
    have hc1 : x.1 i0 = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    refine Subtype.ext (funext fun i => ?_)
    rw [hconst i, hc1]
    rfl
  have hE : IsElemAbelian r φ.range :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_range_isElemAbelian φ
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_ker_pow hexp m)
  have hker : Nat.card
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom μ m).ker = r ^ (m - 1) := by
    have h1 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_card_ker_prod_mul μ
      (by omega : 1 ≤ m)
    rw [hcardμ] at h1
    have h2 : r ^ m = r ^ (m - 1) * r := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hr.pos h1
  have hcard : Nat.card φ.range = r ^ (m - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hker]
  obtain ⟨Q, hQ⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := k) 2 (n := m) (by omega)
  obtain ⟨P0, hP0⟩ : ∃ P0 : Sylow 2 X,
      (P0 : Subgroup X) = (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular m k).map
        α :=
    ⟨Q.mapSurjective (f := α) hα, by
      rw [Sylow.coe_mapSurjective (f := α) hα Q, hQ]⟩
  have hN : φ.range ≤ Subgroup.normalizer (P0 : Set X) := by
    have h2 : Subgroup.normalizer (P0 : Set X) =
        Subgroup.normalizer
          (((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular m k).map α :
            Subgroup X) : Set X) := by
      rw [← hP0]
      rfl
    rw [h2]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_range_le_normalizer μ m α
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_sylow
    P0 φ.range hN hE hcard

theorem k_CartanRank_PSL_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_PSL := by
  change K_CartanRankFamily .PSL
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd hPSL _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, hm, -, -⟩ := hadm
  have hnd : ¬ r ∣ m := hPSL rfl
  have hcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hdvd
    have hdiv :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodel
    change Nat.card (Subgroup.center K) ∣ Nat.gcd m (2 ^ f - 1) * 1 at hdiv
    rw [mul_one] at hdiv
    exact hnd (hdvd.trans (hdiv.trans (Nat.gcd_dvd_left _ _)))
  obtain ⟨k, hFld, hFin, hkcard, ⟨eY⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Q := K ⧸ Subgroup.center K) hmodel
  let := hFld
  let := hFin
  let : Fintype k := Fintype.ofFinite k
  have : CharP k 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card, hkcard])
  have hdvd : r ∣ Nat.card k - 1 := by rw [hkcard]; exact hrdvd
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r (m - 1) := by
    have hProj : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m k) r (m - 1) :=
      uc22pwlie_borelWit_of_cover_split hm hr hdvd hnd
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m k)
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective m k)
        (fun x hx =>
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center m k
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff.1
              (MonoidHom.mem_ker.1 hx)))
    exact uc22p20oBorelWit_map_equiv eY hProj
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K r (m - 1) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_central_quotient
      (Z := Subgroup.center K) le_rfl hr hcop hWY
  exact cartanRank_le_of_borelWit rfl hWK hr hr2 S hS

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem k_CartanRank_POmegaMinus_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_POmegaMinus := by
  change K_CartanRankFamily .POmegaMinus
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, hm4⟩ := hadm
  have hSC : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaMinus m 2 f :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .POmegaMinus) (by decide)).1 hmodel
  simp only [CFSG.Open.StatedClassicalModel] at hSC
  obtain ⟨Kf, hfield, hfin, hKcard, b, c, hbc, ⟨eY⟩⟩ := hSC.2
  let := hfield
  let := hfin
  have hchar : CharP Kf 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  let : CharP Kf 2 := hchar
  have hdvd : r ∣ Nat.card Kf - 1 := by rw [hKcard]; exact hrdvd
  have hBI :=
    orthogonal_geometry_tail_model_Borel_overgroup_interface
      (K ⧸ Subgroup.center K) .POmegaMinus (Or.inr rfl) m 2 f hSC
  simp only [CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.TailModelBorelInterface] at hBI
  have hBI' : CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.BorelInterface 2
      (StatedQuadMinus m Kf b c) (tailModelFlag (m - 1) Kf (Fin 2)) :=
    hBI Kf hKcard b c hbc
  obtain ⟨Sproj, hSproj⟩ := hBI'.2.1
  have hW := exists_borelWit_statedProj_quadMinus (F := Kf) (b := b) (c := c)
    hm4 hr hr2 hdvd Sproj hSproj
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r (m - 1) :=
    uc22p20oBorelWit_map_equiv eY hW
  have hoddq : Odd (((2 : ℕ) ^ f) ^ m + 1) := by
    have h : Odd (2 ^ (f * m) + 1) := by
      have h2 : 2 ∣ 2 ^ (f * m) := dvd_pow_self 2 (Nat.mul_pos (by omega) (by omega)).ne'
      rw [Nat.odd_iff]
      omega
    have h' : ((2 : ℕ) ^ f) ^ m + 1 = 2 ^ (f * m) + 1 := by rw [pow_mul]
    rwa [h']
  have hg : Nat.gcd 4 (((2 : ℕ) ^ f) ^ m + 1) = 1 := by
    have hcop := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hoddq)
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hcop
    exact Nat.Coprime.gcd_eq_one hcop
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus m 2 f = (1, 1) := by
    change (Nat.gcd 4 (((2 : ℕ) ^ f) ^ m + 1), 1) = (1, 1)
    rw [hg]
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_center_eq_bot
      hN hq hodd hmodel hgen
  obtain ⟨eK⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hZ
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K r (m - 1) :=
    uc22p20oBorelWit_map_equiv eK hWY
  exact cartanRank_le_of_borelWit (t := .POmegaMinus) (m := m) (l := m - 1) (by rfl)
    hWK hr hr2 S hS

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem k_CartanRank_POmegaPlus_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_POmegaPlus := by
  change K_CartanRankFamily .POmegaPlus
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, hm4⟩ := hadm
  have hSC : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus m 2 f :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .POmegaPlus) (by decide)).1 hmodel
  simp only [CFSG.Open.StatedClassicalModel] at hSC
  obtain ⟨Kf, hfield, hfin, hKcard, ⟨eY⟩⟩ := hSC.2
  let := hfield
  let := hfin
  have hchar : CharP Kf 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  let : CharP Kf 2 := hchar
  have hdvd : r ∣ Nat.card Kf - 1 := by rw [hKcard]; exact hrdvd
  have hW := exists_borelWit_statedProj_quadPlus (F := Kf) hm4 hr hr2 hdvd
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r m :=
    uc22p20oBorelWit_map_equiv eY hW
  have heven : Even ((2 : ℕ) ^ f) :=
    Nat.even_pow.2 ⟨even_two, by omega⟩
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus m 2 f = (1, 1) := by
    change (if Even ((2 : ℕ) ^ f) then (1, 1) else
      if Even m then (2, 2) else (Nat.gcd 4 (((2 : ℕ) ^ f) ^ m - 1), 1)) = (1, 1)
    rw [if_pos heven]
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_center_eq_bot
      hN hq hodd hmodel hgen
  obtain ⟨eK⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hZ
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K r m :=
    uc22p20oBorelWit_map_equiv eK hWY
  exact cartanRank_le_of_borelWit (t := .POmegaPlus) (m := m) (l := m) (by rfl)
    hWK hr hr2 S hS

section ExceptionalRankTwo


theorem k_CartanRank_trialityD4_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_trialityD4 := by
  change K_CartanRankFamily .trialityD4
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2
  rw [hm0] at hmodel ⊢
  have hW := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_d4_holds hN
    K hq hodd f hmodel r hr hrdvd
  exact cartanRank_le_of_borelWit rfl hW hr hr2 S hS

theorem k_CartanRank_twistedF4_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_twistedF4 := by
  change K_CartanRankFamily .twistedF4
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2.1
  rw [hm0] at hmodel ⊢
  have hW := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_f4_holds hN
    K hq hodd f hmodel r hr hrdvd
  exact cartanRank_le_of_borelWit rfl hW hr hr2 S hS

theorem k_CartanRank_G2_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_G2 := by
  change K_CartanRankFamily .G2
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2.1
  have hq3 : 3 ≤ 2 ^ f := hadm.2.2.2
  rw [hm0] at hmodel ⊢
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_center_eq_bot hN hq hodd hmodel (by rfl)
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hZ
  have hmodelK : LieModel K .G2 0 2 f := LieModel.of_mulEquiv e.symm hmodel
  have hq2 : 2 < 2 ^ f := by omega
  have h := (k_G2CartanRank_holds K f hmodelK hq2 S hS r hr hr2 hrdvd).1
  have h' : CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 :=
    (CFSG.SectionRank.pRank_coe_eq_openPRank r
      (⊤ : Subgroup (normalizerQuotient S))).symm.trans h
  rw [h']
  rfl

open CFSG.Blueprint.Chevalley CFSG.Blueprint.Multiplier CFSG.LieType.Chevalley

theorem k_CartanRank_F4_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_F4 := by
  change K_CartanRankFamily .F4
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2
  rw [hm0] at hmodel ⊢
  obtain ⟨-, hch⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (t := .F4) (by decide)).1 hmodel
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hch
  obtain ⟨Kf, hfield, hfin, hKcard, ⟨eY⟩⟩ := hch.2
  let := hfield
  let := hfin
  have hf1 : 1 ≤ f := hadm.2.1
  have hchar : CharP Kf 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  let : CharP Kf 2 := hchar
  have hdvd : r ∣ Nat.card Kf - 1 := by rw [hKcard]; exact hrdvd
  have hdet : ¬ (r : ℤ) ∣ Tag.F4.cartan.det := by
    rw [det_cartan_F4]
    intro h
    have hnat : r ∣ 1 := by exact_mod_cast h
    exact hr.not_dvd_one hnat
  have hW : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (adjointGroup .F4 Kf) r Tag.F4.rank :=
    exists_borelWit_adjointGroup_chevalley (τ := .F4) (K := Kf) hr hdet hdvd
  have hZadj : Subgroup.center (adjointGroup .F4 Kf) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : Finite (ModGL .F4 Kf) := CFSG.LieType.Chevalley.finite_modGL
  have : Finite (adjointGroup .F4 Kf) := Subtype.finite
  let eY' : (K ⧸ Subgroup.center K) ≃* adjointGroup .F4 Kf :=
    eY.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans
      QuotientGroup.quotientBot)
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r Tag.F4.rank :=
    uc22p20oBorelWit_map_equiv eY' hW
  have hdiv :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodel
  have hgen1 : (genericOrders .F4 0 2 f).1 = 1 := rfl
  have hgen2 : (genericOrders .F4 0 2 f).2 = 1 := rfl
  rw [hgen1, hgen2, mul_one] at hdiv
  have hcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hd
    exact hr.not_dvd_one (hd.trans hdiv)
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      K r Tag.F4.rank :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_central_quotient
      (Z := Subgroup.center K) le_rfl hr hcop hWY
  exact cartanRank_le_of_borelWit (t := .F4) (m := 0) (l := Tag.F4.rank) (by rfl)
    hWK hr hr2 S hS

theorem k_CartanRank_E7_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_E7 := by
  change K_CartanRankFamily .E7
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2
  rw [hm0] at hmodel ⊢
  obtain ⟨-, hch⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (t := .E7) (by decide)).1 hmodel
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hch
  obtain ⟨Kf, hfield, hfin, hKcard, ⟨eY⟩⟩ := hch.2
  let := hfield
  let := hfin
  have hchar : CharP Kf 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  let : CharP Kf 2 := hchar
  have hdvd : r ∣ Nat.card Kf - 1 := by rw [hKcard]; exact hrdvd
  have hdet : ¬ (r : ℤ) ∣ Tag.E7.cartan.det := by
    rw [det_cartan_E7]
    intro h
    have hnat : r ∣ 2 := by exact_mod_cast h
    rcases (Nat.dvd_prime Nat.prime_two).mp hnat with h1 | h1
    · exact hr.ne_one h1
    · exact hr2 h1
  have hW : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (adjointGroup .E7 Kf) r Tag.E7.rank :=
    exists_borelWit_adjointGroup_chevalley (τ := .E7) (K := Kf) hr hdet hdvd
  have hZadj : Subgroup.center (adjointGroup .E7 Kf) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : Finite (ModGL .E7 Kf) := CFSG.LieType.Chevalley.finite_modGL
  have : Finite (adjointGroup .E7 Kf) := Subtype.finite
  let eY' : (K ⧸ Subgroup.center K) ≃* adjointGroup .E7 Kf :=
    eY.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans
      QuotientGroup.quotientBot)
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r Tag.E7.rank :=
    uc22p20oBorelWit_map_equiv eY' hW
  have hdiv :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodel
  have hoddq : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hoddq)
  have hgen1 : (genericOrders .E7 0 2 f).1 = 1 := by
    simp [CFSG.Blueprint.Multiplier.genericOrders, hgcd]
  have hgen2 : (genericOrders .E7 0 2 f).2 = 1 := rfl
  rw [hgen1, hgen2, mul_one] at hdiv
  have hcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hd
    exact hr.not_dvd_one (hd.trans hdiv)
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      K r Tag.E7.rank :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_central_quotient
      (Z := Subgroup.center K) le_rfl hr hcop hWY
  exact cartanRank_le_of_borelWit (t := .E7) (m := 0) (l := Tag.E7.rank) (by rfl)
    hWK hr hr2 S hS

theorem k_CartanRank_E8_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_E8 := by
  change K_CartanRankFamily .E8
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2
  rw [hm0] at hmodel ⊢
  obtain ⟨-, hch⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (t := .E8) (by decide)).1 hmodel
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hch
  obtain ⟨Kf, hfield, hfin, hKcard, ⟨eY⟩⟩ := hch.2
  let := hfield
  let := hfin
  have hchar : CharP Kf 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  let : CharP Kf 2 := hchar
  have hdvd : r ∣ Nat.card Kf - 1 := by rw [hKcard]; exact hrdvd
  have hdet : ¬ (r : ℤ) ∣ Tag.E8.cartan.det := by
    rw [det_cartan_E8]
    intro h
    have hnat : r ∣ 1 := by exact_mod_cast h
    exact hr.not_dvd_one hnat
  have hW : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (adjointGroup .E8 Kf) r Tag.E8.rank :=
    exists_borelWit_adjointGroup_chevalley (τ := .E8) (K := Kf) hr hdet hdvd
  have hZadj : Subgroup.center (adjointGroup .E8 Kf) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : Finite (ModGL .E8 Kf) := CFSG.LieType.Chevalley.finite_modGL
  have : Finite (adjointGroup .E8 Kf) := Subtype.finite
  let eY' : (K ⧸ Subgroup.center K) ≃* adjointGroup .E8 Kf :=
    eY.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans
      QuotientGroup.quotientBot)
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r Tag.E8.rank :=
    uc22p20oBorelWit_map_equiv eY' hW
  have hdiv :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodel
  have hgen1 : (genericOrders .E8 0 2 f).1 = 1 := rfl
  have hgen2 : (genericOrders .E8 0 2 f).2 = 1 := rfl
  rw [hgen1, hgen2, mul_one] at hdiv
  have hcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hd
    exact hr.not_dvd_one (hd.trans hdiv)
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      K r Tag.E8.rank :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_central_quotient
      (Z := Subgroup.center K) le_rfl hr hcop hWY
  exact cartanRank_le_of_borelWit (t := .E8) (m := 0) (l := Tag.E8.rank) (by rfl)
    hWK hr hr2 S hS

theorem k_CartanRank_E6_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_E6 := by
  change K_CartanRankFamily .E6
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ hE6side
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2
  rw [hm0] at hmodel ⊢
  obtain ⟨-, hch⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (t := .E6) (by decide)).1 hmodel
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hch
  obtain ⟨Kf, hfield, hfin, hKcard, ⟨eY⟩⟩ := hch.2
  let := hfield
  let := hfin
  have hchar : CharP Kf 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  let : CharP Kf 2 := hchar
  have hdvd : r ∣ Nat.card Kf - 1 := by rw [hKcard]; exact hrdvd
  have hdet : ¬ (r : ℤ) ∣ Tag.E6.cartan.det := by
    rw [det_cartan_E6]
    intro h
    have hnat : r ∣ 3 := by exact_mod_cast h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hnat with h1 | h1
    · exact hr.ne_one h1
    · exact hE6side rfl h1
  have hW : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (adjointGroup .E6 Kf) r Tag.E6.rank :=
    exists_borelWit_adjointGroup_chevalley (τ := .E6) (K := Kf) hr hdet hdvd
  have hZadj : Subgroup.center (adjointGroup .E6 Kf) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : Finite (ModGL .E6 Kf) := CFSG.LieType.Chevalley.finite_modGL
  have : Finite (adjointGroup .E6 Kf) := Subtype.finite
  let eY' : (K ⧸ Subgroup.center K) ≃* adjointGroup .E6 Kf :=
    eY.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans
      QuotientGroup.quotientBot)
  have hWY : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      (K ⧸ Subgroup.center K) r Tag.E6.rank :=
    uc22p20oBorelWit_map_equiv eY' hW
  have hdiv :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodel
  have hgen1 : (genericOrders .E6 0 2 f).1 = Nat.gcd 3 (2 ^ f - 1) := rfl
  have hgen2 : (genericOrders .E6 0 2 f).2 = 1 := rfl
  rw [hgen1, hgen2, mul_one] at hdiv
  have hcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hd
    have hrg : r ∣ Nat.gcd 3 (2 ^ f - 1) := hd.trans hdiv
    have hr3 : r ∣ 3 := hrg.trans (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hr3 with h1 | h1
    · exact hr.ne_one h1
    · exact hE6side rfl h1
  have hWK : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
      K r Tag.E6.rank :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_central_quotient
      (Z := Subgroup.center K) le_rfl hr hcop hWY
  exact cartanRank_le_of_borelWit (t := .E6) (m := 0) (l := Tag.E6.rank) (by rfl)
    hWK hr hr2 S hS
end ExceptionalRankTwo

theorem k_CartanRank_POmegaOdd_holds : K_CartanRank_POmegaOdd := by
  change K_CartanRankFamily .POmegaOdd
  intro K _ _ m f hadm _ _ _ _ _ r _ _ _
  exact absurd hadm.2.2.2 (by decide)

theorem k_CartanRank_twistedG2_holds : K_CartanRank_twistedG2 := by
  change K_CartanRankFamily .twistedG2
  intro K _ _ m f hadm _ _ _ _ _ r _ _ _
  exact absurd hadm.2.2.2.1 (by decide)

theorem k_CartanRank_Tits_holds : K_CartanRank_Tits := by
  change K_CartanRankFamily .Tits
  intro K _ _ m f hadm _ _ _ _ _ r hr _ hrdvd _ _
  obtain ⟨-, -, -, -, hf1⟩ := hadm
  rw [hf1] at hrdvd
  exact absurd (by simpa using hrdvd) hr.not_dvd_one

section Assembly


theorem k_CartanRank_of_griess_of_twistedE6
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    (htwE6 : K_CartanRank_twistedE6) : K_CartanRank :=
  k_CartanRank_of_families
    (k_CartanRank_PSL_of_griess hN) k_CartanRank_PSU_holds
    (k_CartanRank_PSp_of_griess hN) k_CartanRank_POmegaOdd_holds
    (k_CartanRank_POmegaPlus_of_griess hN)
    (k_CartanRank_POmegaMinus_of_griess hN) (k_CartanRank_G2_of_griess hN)
    (k_CartanRank_F4_of_griess hN) (k_CartanRank_E6_of_griess hN)
    (k_CartanRank_E7_of_griess hN) (k_CartanRank_E8_of_griess hN) htwE6
    (k_CartanRank_trialityD4_of_griess hN) k_CartanRank_twistedB2_holds
    k_CartanRank_twistedG2_holds (k_CartanRank_twistedF4_of_griess hN)
    k_CartanRank_Tits_holds

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
