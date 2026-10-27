module

import Lean
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeLinCover
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
public import CFSG.LieType.Steinberg.CentralExt.GriessAllModels
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

section CoverLemma

variable {S L K : Type} [Group S] [Group L] [Group K]

private theorem ggNSLiePI3_card_ker_dpFst_dvd {β : S →* K} {η : L →* K} :
    Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker ∣ Nat.card η.ker := by
  refine Subgroup.card_dvd_of_injective
    (((CFSG.AGLEmbedding.FixedThree.dpSnd β η).comp
      (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker.subtype).codRestrict η.ker
      fun x => CFSG.AGLEmbedding.FixedThree.dpFst_mem_ker x.2) ?_
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have h1 : ((x : CFSG.AGLEmbedding.FixedThree.derivedPullback β η) : S × L).1 = 1 := x.2
  have h2 : ((y : CFSG.AGLEmbedding.FixedThree.derivedPullback β η) : S × L).1 = 1 := y.2
  have h3 : CFSG.AGLEmbedding.FixedThree.dpSnd β η
        (x : CFSG.AGLEmbedding.FixedThree.derivedPullback β η) =
      CFSG.AGLEmbedding.FixedThree.dpSnd β η
        (y : CFSG.AGLEmbedding.FixedThree.derivedPullback β η) :=
    congrArg Subtype.val hxy
  exact Prod.ext (h1.trans h2.symm) h3

theorem ggExists_cover_of_hopfMultiplier_coprime [Finite S] [Finite L] {β : S →* K} {η : L →* K}
    (hβ : Function.Surjective β) (hη : Function.Surjective η) (hS : Group.IsPerfect S)
    (hL : Group.IsPerfect L) (hβc : β.ker ≤ Subgroup.center S) (hηc : η.ker ≤ Subgroup.center L)
    (hKz : Subgroup.center K = ⊥) {d e : ℕ} (hd : Nat.card β.ker = d)
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier K) = d * e) (hcop : Nat.Coprime (Nat.card η.ker) e) :
    ∃ ψ : S →* L, Function.Surjective ψ ∧ ∀ s, η (ψ s) = β s := by
  have : Finite (CFSG.AGLEmbedding.FixedThree.derivedPullback β η) := by
    have : Finite (S × L) := inferInstance
    exact Subtype.finite
  have hp₁ := CFSG.AGLEmbedding.FixedThree.dpFst_surjective (β := β) hη hS
  have hp₂ := CFSG.AGLEmbedding.FixedThree.dpSnd_surjective (η := η) hβ hL
  have hq := CFSG.AGLEmbedding.FixedThree.dpQ_surjective hβ hη hS
  have hQp := CFSG.AGLEmbedding.FixedThree.isPerfect_derivedPullback (β := β) hη hS hηc
  have hker : (CFSG.AGLEmbedding.FixedThree.dpQ β η).ker =
      Subgroup.center (CFSG.AGLEmbedding.FixedThree.derivedPullback β η) :=
    le_antisymm (CFSG.AGLEmbedding.FixedThree.ker_dpQ_le_center hβc hηc)
      (CFSG.AGLEmbedding.FixedThree.center_le_ker_dpQ hq hKz)
  let e' : CFSG.AGLEmbedding.FixedThree.derivedPullback β η ⧸
      Subgroup.center (CFSG.AGLEmbedding.FixedThree.derivedPullback β η) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (CFSG.AGLEmbedding.FixedThree.dpQ β η) hq)
  have hdiv := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hQp e'
  rw [← hker, hM] at hdiv
  have c1 := Subgroup.card_ker_mul_card_of_surjective hp₁
  have c2 := Subgroup.card_ker_mul_card_of_surjective hβ
  have c3 := Subgroup.card_ker_mul_card_of_surjective hq
  have : Finite K := Finite.of_surjective β hβ
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hdpos : 0 < d := hd ▸ Nat.card_pos
  have hkq : Nat.card (CFSG.AGLEmbedding.FixedThree.dpQ β η).ker =
      Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker * d := by
    have : Nat.card (CFSG.AGLEmbedding.FixedThree.dpQ β η).ker * Nat.card K =
        Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker * d * Nat.card K := by
      rw [c3, ← c1, ← c2, hd]; ring
    exact Nat.eq_of_mul_eq_mul_right hKpos this
  rw [hkq] at hdiv
  have hdvd : Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker ∣ e := by
    have : Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker * d ∣ e * d := by
      rwa [mul_comm e d]
    exact Nat.dvd_of_mul_dvd_mul_right hdpos this
  have hker1 : (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker = ⊥ := by
    have hdvdη : Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker ∣ Nat.card η.ker :=
      ggNSLiePI3_card_ker_dpFst_dvd
    have hgcd : Nat.gcd (Nat.card η.ker) e = 1 := hcop
    have hone : Nat.card (CFSG.AGLEmbedding.FixedThree.dpFst β η).ker ∣ 1 :=
      hgcd ▸ Nat.dvd_gcd hdvdη hdvd
    exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hone)
  have hinj : Function.Injective (CFSG.AGLEmbedding.FixedThree.dpFst β η) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker1
  let g : CFSG.AGLEmbedding.FixedThree.derivedPullback β η ≃* S :=
    MulEquiv.ofBijective (CFSG.AGLEmbedding.FixedThree.dpFst β η) ⟨hinj, hp₁⟩
  refine ⟨(CFSG.AGLEmbedding.FixedThree.dpSnd β η).comp g.symm.toMonoidHom, ?_, fun s => ?_⟩
  · exact hp₂.comp g.symm.surjective
  · have hx := CFSG.LieType.Steinberg.mem_pullback.1
      (CFSG.AGLEmbedding.FixedThree.derivedPullback_le β η (g.symm s).2)
    have h5 : CFSG.AGLEmbedding.FixedThree.dpFst β η (g.symm s) = s := g.apply_symm_apply s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    change η ((g.symm s : CFSG.AGLEmbedding.FixedThree.derivedPullback β η) : S × L).2 = β s
    rw [← hx]
    exact congrArg β h5

end CoverLemma

section HSplit

variable (K : Type) [Field K] [Finite K] [CharP K 2] (f n : ℕ)

theorem ggSU_central_extension_splits
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) (hn4 : ¬ (n = 4 ∧ f = 1))
    (hn6 : ¬ (n = 6 ∧ f = 1)) (E : Type) [Group E] [Finite E] (π : E →* Su K 2 f n) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) : ∃ s : Su K 2 f n →* E, π.comp s = MonoidHom.id (Su K 2 f n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero, one_pow] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    exact absurd h1 (lt_irrefl 1)
  let e : Su K 2 f n ≃* StatedSU n (2 ^ f) K :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (F := K) (p := 2) (f := f) hK n)
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e.toMonoidHom e.injective
  have hπ' : Function.Surjective (e.toMonoidHom.comp π) := e.surjective.comp hπ
  have hc' : (e.toMonoidHom.comp π).ker ≤ Subgroup.center E := hker ▸ hc
  obtain ⟨t, ht⟩ : ∃ t : StatedSU n (2 ^ f) K →* E,
      ∀ g, (e.toMonoidHom.comp π) (t g) = g := by
    by_cases hn5 : 5 ≤ n
    · exact LineU.statedSU_exists_section_unitary (n := f) (d := n) hK hf hn5
        (fun h => hn6 (by simpa using h)) hπ' hc'
    · have hn4' : n = 4 := by omega
      subst hn4'
      have hf2 : 2 ≤ f := by
        by_contra h
        have hf1 : f = 1 := by omega
        exact hn4 ⟨rfl, hf1⟩
      have hq : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
        (F := K) (p := 2) (f := f) hK ⟨2, by norm_num⟩ (by omega) hq hπ' hc'
  refine ⟨t.comp e.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  have h := ht (e x)
  simp only [MonoidHom.comp_apply] at h
  exact e.injective h

end HSplit

end CFSG.StandardType

end
