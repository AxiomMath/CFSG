module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4KernelB
import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4A2A2
import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
import CFSG.Quasithin.Background.A3Structure314Defs
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
import CFSG.Quasithin.EmptyFaithful.S14610Q1
import CFSG.Quasithin.EmptyFaithful.S14610Top
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch10SecB4
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecAVi2
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.LangRat

open CFSG CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem langF4_comp_cases
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    (∃ j : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j) ∧
          rationalComponent S.ρ S.Γ (rootCharHom a) j ≠ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = S.D.q ∧
        Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
          LargeEvenProj (LargeEvenSpGroup F 3)) := by
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_omega_param (L := L) hap
  have hk0 : ∃ j, k j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [show a = 1 from funext fun j => by rw [hak j, hcon j, pow_zero]; rfl,
      rootDiagUnit_one]
  rcases CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Std.classify_kernel2 k hk3 hk0 with
    hB | hA2
  · exact Or.inr (langF4_comp_kernelB S hT hap hω3 hω1 hak hB i)
  · by_cases hq2 : S.D.q = 2
    · exfalso
      exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.not_isSolvable_of_isQuasisimple'
        hqs (CFSG.HardMathSupport.Dickson.Bal207.FamF42.isSolvable_rationalComponent_of_a2a2
          S hT hap hω3 hω1 hk3 hk0 hak hA2 hq2 i)
    · refine Or.inl (langF4_a2a2_two_comp S hT hap h1 hω3 hω1 hak hA2 ?_ i)
      have h2dvd : 2 ∣ S.D.q := (CharP.cast_eq_zero_iff L 2 S.D.q).1 S.hqpow.2
      obtain ⟨r, e, hr, hre⟩ := (isPrimePow_iff_pow_succ S.D.q).1 S.hqpow.1
      have h2r : 2 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (hre ▸ h2dvd)
      have hr2 : r = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_iff.2 hr)).1 h2r).symm
      have hq2pow : S.D.q = 2 ^ (e + 1) := by rw [← hre, hr2]
      have hepos : 0 < e := by
        rcases Nat.eq_zero_or_pos e with he | he
        · exact absurd (by rw [hq2pow, he]; norm_num) hq2
        · exact he
      rw [hq2pow]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (e + 1) := pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2) (by omega)

end CFSG.StandardType.LangRat

end
