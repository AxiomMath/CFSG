module

public import CFSG.Quasithin.Recognition.Stroth.LemmaSDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.Quasithin.Vol2.Ch3E215MC
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open scoped LinearAlgebra.Projectivization MatrixGroups

theorem rankOneData_psu3 {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (k : ℕ) (hk : 2 ≤ k)
    (hcard : Nat.card K = (2 ^ k) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ k)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    RankOneData ↥(ProjectiveSpecialUnitaryMatrixGroup J)
        ((hermitianUnipotentPSU J hJ).range)
        (unitaryCoordinateStabilizer J 0) ∧
      Nat.card ((hermitianUnipotentPSU J hJ).range) = (2 ^ k) ^ 3 := by
  let q := 2 ^ k
  let G := ↥(ProjectiveSpecialUnitaryMatrixGroup J)
  let Ω := unitaryIsotropicPoints J
  let α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  let β := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  let U := (hermitianUnipotentPSU J hJ).range
  let T := (torusPSU J hJ).range
  let B := unitaryCoordinateStabilizer J 0
  change RankOneData G U B ∧ Nat.card U = q ^ 3
  have hUdef : U = (hermitianUnipotentPSU J hJ).range := rfl
  have hBdef : B = unitaryCoordinateStabilizer J 0 := rfl
  have hTdef : T = (torusPSU J hJ).range := rfl
  have hαeq : α = unitaryOuterIsotropicPoint J hJ 0
      unitary_three_point_structure._proof_1 := by
    apply Subtype.ext
    rfl
  obtain ⟨-, -, -, -, -, rho, hrho, hnative, hcardΩ, h2tr, hstab, -, hnormal, -, hsup,
    hTeq, hTcyc, hTcard, ⟨S, hS⟩, hUcard, hreg, hSE, htwoRank, htwoRank', -,
    ⟨w, hw2, hwα, hwβ⟩, hswap⟩ :=
      unitary_three_point_structure J k hk hcard hfixed hJ
  have hUcard' : Nat.card U = (2 ^ k) ^ 3 := by simpa [hUdef] using hUcard
  have hTcard' : Nat.card T =
      ((2 ^ k) ^ 2 - 1) / Nat.gcd 3 (2 ^ k + 1) := by simpa [hTdef] using hTcard
  letI : MulAction G Ω := MulAction.compHom Ω rho
  have hBstab : B = MulAction.stabilizer G α := hstab.symm
  have h2trΩ : MulAction.IsMultiplyPretransitive G Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact h2tr a b c d hab hcd
  haveI : MulAction.IsMultiplyPretransitive G Ω 2 := h2trΩ
  haveI : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hidx : B.index = q ^ 3 + 1 := by
    rw [hBstab, MulAction.index_stabilizer_of_transitive G α, hcardΩ]
  have hUB : U ≤ B := by
    change (hermitianUnipotentPSU J hJ).range ≤ unitaryCoordinateStabilizer J 0
    rw [← hsup]
    exact le_sup_left
  have hTleB : T ≤ B := by
    change (torusPSU J hJ).range ≤ unitaryCoordinateStabilizer J 0
    rw [← hsup]
    exact le_sup_right
  have hTnorm : T ≤ Subgroup.normalizer (U : Set G) :=
    hTleB.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hnormal)
  have hαβ : α ≠ β := by
    intro h
    have h' : unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint (K := K) 2 := by
      rw [← show (α : ℙ K (Fin 3 → K)) = unitaryCoordinatePoint 0 from rfl, h,
        show (β : ℙ K (Fin 3 → K)) = unitaryCoordinatePoint 2 from rfl]
    exact unitaryCoordinatePoint_two_ne_zero h'.symm
  have hnsq : w * w = 1 := by
    simpa [pow_two, hw2] using pow_orderOf_eq_one w
  have hnT : ∀ t ∈ T, w⁻¹ * t * w ∈ T := by
    intro t ht
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp ht
    rw [(hswap w hwα hwβ).1 c]
    exact ⟨(c ^ q)⁻¹, rfl⟩
  have hwB : w ∉ B := by
    intro hw
    have hfix : w • α = α := by
      rwa [hBstab] at hw
    change rho w α = α at hfix
    rw [hwα] at hfix
    exact hαβ hfix.symm
  have hreg' : ∀ a b : Ω, a ≠ α → b ≠ α → ∃! u : U, u • a = b := by
    intro a b ha hb
    rw [hαeq] at ha hb
    rw [hUdef]
    change ∃! u : ↥(hermitianUnipotentPSU J hJ).range, (rho (u : G)) a = b
    exact hreg a b ha hb
  have hinj : Set.InjOn (fun s : G => ((s * w : G) : G ⧸ B)) (U : Set G) :=
    injOn_mul_quotient_of_regular B U α hBstab hUB hreg' hwB
  have hbound : B.index ≤ (U : Set G).ncard + 1 := by
    rw [hidx]
    have hnc : (U : Set G).ncard = Nat.card U :=
      (Nat.card_coe_set_eq (U : Set G)).symm
    rw [hnc, hUcard']
  have hsup' : B = U ⊔ T := by
    rw [hUdef, hTdef, hBdef]
    exact hsup.symm
  have hTnorm' : T ≤ Subgroup.normalizer (U : Set G) := by
    rwa [hUdef, hTdef] at hTnorm ⊢
  have hbruhat : ∀ x : G, x ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, x = b₁ * w * b₂ :=
    fun x => CFSG.Quasithin.Ch3E215M.bruhat_of_injOn hwB (S := (U : Set G))
      (fun u hu => hUB hu) hinj hbound x
  have hq2 : 2 < q := by
    dsimp [q]
    calc
      2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  haveI : IsSimpleGroup G := huppert_II_10_13 J q hq2 hcard hfixed
  have hUbot : U ≠ ⊥ := by
    intro h
    have h1 : Nat.card U = 1 := by rw [h, Subgroup.card_bot]
    rw [hUcard'] at h1
    have hq : 2 ≤ q := by
      dsimp [q]
      exact Nat.one_lt_two_pow (by omega)
    have hq1 : 1 < q := by omega
    have hq3 : 1 < q ^ 3 := by
      have hq2 : 1 ≤ q ^ 2 := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
          _ = q ^ 2 := by ring
      calc
        1 < q := hq1
        _ = q * 1 := by ring
        _ ≤ q * q ^ 2 := Nat.mul_le_mul_left q hq2
        _ = q ^ 3 := by ring
    have hq3' : 1 < (2 ^ k) ^ 3 := by simpa [q] using hq3
    omega
  have hdata : RankOneData G U B := by
    refine ⟨?_, hUbot, ⟨S, hS⟩, hUB, ?_, ?_, ?_⟩
    · change IsPGroup 2 ↥((hermitianUnipotentPSU J hJ).range)
      rw [← hS]
      exact S.isPGroup'
    · intro M hUM hM
      rcases le_B_or_eq_top_of_bruhat hsup' hTnorm' hnT hnsq hUbot hbruhat M hUM with h | h
      · exact h
      · exact absurd h hM.ne
    · rw [hidx, hUcard']
      dsimp [q]
      omega
    · have hle : U.relIndex B ≤ Nat.card T :=
        relIndex_le_card_right_of_sup_eq hsup' hTnorm' 
      calc
        U.relIndex B ≤ Nat.card T := hle
        _ ≤ q ^ 2 - 1 := by
          rw [hTcard']
          exact Nat.div_le_self _ _
        _ < q ^ 3 := by
          have hq : 2 ≤ q := by
            dsimp [q]
            exact Nat.one_lt_two_pow (by omega)
          have h1 : q ^ 2 - 1 < q ^ 2 := by
            exact Nat.sub_one_lt (by nlinarith)
          have h2 : q ^ 2 ≤ q ^ 3 := by
            calc
              q ^ 2 = q ^ 2 * 1 := by ring
              _ ≤ q ^ 2 * q := Nat.mul_le_mul_left _ (by omega)
              _ = q ^ 3 := by ring
          exact lt_of_lt_of_le h1 h2
        _ = Nat.card U := hUcard'.symm
  exact ⟨hdata, hUcard'⟩

theorem card_eq_of_hasNormalCopy_psu3 :
    ∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (k : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ k →
      Nat.card F = (2 ^ k) ^ 2 →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y (StatedProj (StatedSU 3 (2 ^ k) F)) →
      Fintype.card Ω = 2 ^ (3 * k) + 1 := by
  intro Y _ _ Ω _ _ _ k F _ _ hk hFcard h2 hdeg hcopy
  obtain ⟨J, hJ, -, hfixed⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := F) 2 k hFcard
  obtain ⟨hdata, hUcard⟩ := rankOneData_psu3 J k hk hFcard hfixed hJ
  obtain ⟨ePsu⟩ :=
    CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj J (2 ^ k) hFcard hfixed
  obtain ⟨M, hMnormal, hMequiv⟩ := hcopy
  obtain ⟨φ⟩ := hMequiv
  let ψ : ↥M ≃* ↥(ProjectiveSpecialUnitaryMatrixGroup J) := φ.trans ePsu.symm
  letI : M.Normal := hMnormal
  let U' : Subgroup M :=
    ((hermitianUnipotentPSU J hJ).range).map ψ.symm.toMonoidHom
  let B' : Subgroup M :=
    (unitaryCoordinateStabilizer J 0).map ψ.symm.toMonoidHom
  have hdata' : RankOneData M U' B' := hdata.map ψ.symm
  have hU'card : Nat.card U' = (2 ^ k) ^ 3 := by
    rw [Subgroup.card_map_of_injective ψ.symm.injective, hUcard]
  have hMbot : M ≠ ⊥ := by
    intro hbot
    apply hdata'.ne_bot
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp (by simpa [hbot] using x.2))
  have hdeg' := card_eq_one_add_of_rankOneData M hMbot h2 hdeg
    ⟨U', B', hdata', hU'card⟩
  rw [hdeg']
  rw [show (2 ^ k) ^ 3 = 2 ^ (3 * k) by rw [← pow_mul, mul_comm]]
  omega

end CFSG.Quasithin.Stroth
