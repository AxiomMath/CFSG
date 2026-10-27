module

public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
import CFSG.RankThree.PartTwo.Sec16.Item16Tail24Tools
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofKb
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem le_normalizer_of_subset_sectionCentralizer {E : Subgroup G}
    (hEp : Group.IsPerfect E)
    (hEC : (E : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀))
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ≤ Subgroup.normalizer (E : Set G)) :
    Y₀ ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y₀) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  intro y hy
  have hmap : E.map (MulAut.conj y).toMonoidHom ≤ E ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hq : e⁻¹ * y * e * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
      simpa using (hEC (E.inv_mem he)).2 y hy
    rw [show y * e * y⁻¹ = e * (e⁻¹ * y * e * y⁻¹) by group]
    exact Subgroup.mul_mem_sup he hq
  have hJperf : Group.IsPerfect (E.map (MulAut.conj y).toMonoidHom) := by
    letI : Group.IsPerfect E := hEp
    exact Group.IsPerfect.map (MulAut.conj y).toMonoidHom
  have hJE : E.map (MulAut.conj y).toMonoidHom ≤ E :=
    Proof1624.le_of_isPerfect_of_le_sup hQ hQ2 hJperf hmap
  have hcard : Nat.card E ≤ Nat.card (E.map (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hEq : E.map (MulAut.conj y).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hJE hcard
  simpa using (Subgroup.mem_normalizer_iff_map_conj_eq (H := E) (g := y)).mpr hEq

private theorem inf_pCore_le_of_isSylowOf {E Q U : Subgroup G}
    (hENQ : E ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U E) : E ⊓ Q ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : ((E ⊓ Q).subgroupOf E).Normal := by
    have h : (Q.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hENQ
    simpa only [Subgroup.inf_subgroupOf_left] using h
  letI : ((E ⊓ Q).subgroupOf E).Normal := hnormal
  have hp : IsPGroup 2 ((E ⊓ Q).subgroupOf E) := hQ2.to_inf_right.comap_subtype
  obtain ⟨P, hP⟩ := hU
  have hle : ((E ⊓ Q).subgroupOf E) ≤ (P : Subgroup E) := hp.le_sylow_of_normal P
  have hmap := Subgroup.map_mono (f := E.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left, hP] at hmap

private theorem le_normalizer_of_isSylowOf {E U : Subgroup G}
    (hEp : Group.IsPerfect E)
    (hEC : (E : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀))
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ≤ Subgroup.normalizer (E : Set G))
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U E)
    (hEinfQU : E ⊓ CFSG.Open.pCoreOf 2 Y₀ ≤ U) :
    Y₀ ≤ Subgroup.normalizer (U : Set G) := by
  have hY : Y₀ ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_of_subset_sectionCentralizer hEp hEC hQ
  have hconjU : ∀ y ∈ Y₀, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro y hy u hu
    have huE : u ∈ E := hU.le hu
    have hcommE : u⁻¹ * y * u * y⁻¹ ∈ E := by
      have hyu : y * u * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hY hy) u).mp huE
      rw [show u⁻¹ * y * u * y⁻¹ = u⁻¹ * (y * u * y⁻¹) by group]
      exact E.mul_mem (E.inv_mem huE) hyu
    have hcommQ : u⁻¹ * y * u * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
      simpa using (hEC (E.inv_mem huE)).2 y hy
    have hcommU : u⁻¹ * y * u * y⁻¹ ∈ U := hEinfQU ⟨hcommE, hcommQ⟩
    rw [show y * u * y⁻¹ = u * (u⁻¹ * y * u * y⁻¹) by group]
    exact U.mul_mem hu hcommU
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hconjU y hy u
  · intro hu
    have h := hconjU y⁻¹ (Y₀.inv_mem hy) (y * u * y⁻¹) hu
    rwa [show y⁻¹ * (y * u * y⁻¹) * (y⁻¹)⁻¹ = u by group] at h

theorem le_M_of_le_normalizer (h : Sec17Std G A c L Y₀) {Z E : Subgroup G} (hEZ : E ≤ Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G)) (hAE : A ≤ Subgroup.normalizer (E : Set G))
    (hE3 : ¬ 3 ∣ Nat.card E) (hE2 : 2 ∣ Nat.card E) (hEp : Group.IsPerfect E)
    (hEC : (E : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀))
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ≤ Subgroup.normalizer (E : Set G)) :
    Z ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcop : Nat.Coprime 3 (Nat.card E) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hE3
  obtain ⟨P, hAP, hPne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two A E hA.isPGroup hAE hcop hE2
  let U : Subgroup G := (P : Subgroup E).map E.subtype
  have hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 U E := ⟨P, rfl⟩
  have hEM : E ≤ Subgroup.normalizer (Y₀ : Set G) := fun e he => (hEC he).1
  have hENQ : E ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y₀)
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y₀) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hEinfQU : E ⊓ CFSG.Open.pCoreOf 2 Y₀ ≤ U :=
    inf_pCore_le_of_isSylowOf hENQ hQ2 hUsyl
  have hYU : Y₀ ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_isSylowOf hEp hEC hQ hUsyl hEinfQU
  have hYAU : Y₀ ⊔ A ≤ Subgroup.normalizer (U : Set G) := sup_le hYU hAP
  have hNUM : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
    Proof165.normalizer_le_M h hPne hUsyl.isPGroup hYAU
  have hfr : Z ≤ E ⊔ (Z ⊓ Subgroup.normalizer (U : Set G)) :=
    Proof17Res12.le_sup_inf_normalizer (H := Z) hEZ hZE hUsyl
  exact hfr.trans (sup_le hEM fun z hz => hNUM hz.2)

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
