module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofGen
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofTwentySeven
import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofSeitzU
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS

open CFSG.Assembly.RankThreeEven (projSL)

namespace Proof1612PGL

variable {G : Type} [Group G] [Finite G]

theorem le_sSup_of_autThetaQuot {A L : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hgen : sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤) :
    L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set F := {X : Subgroup (↥L ⧸ θ) | ¬ 3 ∣ Nat.card X ∧
    ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} with hF
  set N := sSup (invariantPiSubgroups L A (piCompl 3)) with hN
  have hpre : ∀ X ∈ F, (X.comap (QuotientGroup.mk' θ)).map L.subtype ∈
      invariantPiSubgroups L A (piCompl 3) := by
    rintro X ⟨hX3, hXinv⟩
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [isPiSubgroup_piCompl_iff Nat.prime_three,
        Subgroup.card_map_of_injective L.subtype_injective]
      exact not_three_dvd_card_comap _ hX3 (by rw [QuotientGroup.ker_mk']; exact hθ3)
    · refine Item148PtRes2.le_normalizer_of_conj_mem' fun a ha m hm => ?_
      obtain ⟨l, hl, rfl⟩ := hm
      have haN := hAN ha
      have hl' : a * (l : G) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haN l).mp l.2
      refine ⟨⟨_, hl'⟩, ?_, rfl⟩
      have hσ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, haN⟩) ∈
          Sec4.autThetaQuot A L :=
        Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, ha, rfl⟩
      exact hXinv _ hσ ⟨QuotientGroup.mk' θ l, hl, rfl⟩
  have hbot : (⊥ : Subgroup (↥L ⧸ θ)) ∈ F :=
    ⟨by rw [Subgroup.card_bot]; norm_num, fun σ _ => by rw [Subgroup.map_bot]⟩
  set T : Subgroup ↥L := N.subgroupOf L with hT
  have hθT : θ ≤ T := by
    intro l hl
    refine Subgroup.mem_subgroupOf.mpr (le_sSup (hpre ⊥ hbot) ⟨l, ?_, rfl⟩)
    change QuotientGroup.mk' θ l ∈ (⊥ : Subgroup (↥L ⧸ θ))
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hl
  have hFT : ∀ X ∈ F, X ≤ T.map (QuotientGroup.mk' θ) := by
    intro X hX x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ x
    exact ⟨l, Subgroup.mem_subgroupOf.mpr (le_sSup (hpre X hX) ⟨l, hx, rfl⟩), rfl⟩
  have htop : T.map (QuotientGroup.mk' θ) = ⊤ := top_unique (hgen ▸ sSup_le hFT)
  intro g hg
  have hgT : (⟨g, hg⟩ : ↥L) ∈ T := by
    obtain ⟨t, ht, hteq⟩ : QuotientGroup.mk' θ ⟨g, hg⟩ ∈ T.map (QuotientGroup.mk' θ) :=
      htop ▸ Subgroup.mem_top _
    have h1 : t⁻¹ * ⟨g, hg⟩ ∈ θ := by
      rw [← QuotientGroup.ker_mk' θ, MonoidHom.mem_ker, map_mul, map_inv, hteq, inv_mul_cancel]
    have h2 := mul_mem ht (hθT h1)
    rwa [mul_inv_cancel_left] at h2
  exact Subgroup.mem_subgroupOf.mp hgT

end Proof1612PGL

open Proof1612PGL

theorem ks1612GenPGL_of
    (h131 : Item131) : KS1612GenPGL := by
  intro G _ _ A c L h hPGL hx
  have hD := h.toSec15R.toSec14Std.toSec13Data
  have hfacts := facts_of_isZ3PGLThreePi hD hPGL
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hfacts.1
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := hfacts.2.1
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  have h3 : Nat.card (A ⊓ L : Subgroup G) = 3 :=
    Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL
  have h34 : ¬ Nonempty (lBarA c L A ≃*
      Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) := by
    rintro ⟨φ⟩
    obtain ⟨hS, hZc⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
    obtain ⟨-, h9, -, -⟩ := facts_of_prod hD hS hZc φ
    exact absurd h3 (by omega)
  have hstar : Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with
        ⟨-, h9, -, -⟩ | ⟨-, h9, -, -⟩ | ⟨-, -, hstar, -⟩ | ⟨hcL', -⟩
    · exact absurd h3 (by omega)
    · exact absurd h3 (by omega)
    · exact hstar
    · exact absurd hcL' hcL
  have hgen : sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤ :=
    step142LowerGenL3PGL_proof G A c L h.toSec15R.toSec14Std hL3 h34 hPGL hstar hx
  exact le_sSup_of_autThetaQuot hD.le_normalizer hgen

theorem step1612Gen_of_item131
    (h131 : Item131) : Step1612Gen :=
  step1612Gen_of h131 (ks1517Gen_of (ks1517CentGen_of ks1517SeitzU)) (ks1612GenPGL_of h131)

end CFSG.RankThree.PartTwo.Sec16
