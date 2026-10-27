module

public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable def perpOf (Z E : Subgroup G) : Subgroup G :=
  Sec11.sectionCentralizerSubgroup (Z ⊓ Subgroup.normalizer (E : Set G)) E
    (CFSG.Open.pCoreOf 2 E) inf_le_right
    (inf_le_right.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E))

theorem mem_perpOf_iff {Z E : Subgroup G} {z : G} :
    z ∈ perpOf Z E ↔ z ∈ Z ∧ z ∈ Subgroup.normalizer (E : Set G) ∧
      ∀ e ∈ E, z * e * z⁻¹ * e⁻¹ ∈ CFSG.Open.pCoreOf 2 E := by
  rw [perpOf, Sec11.mem_sectionCentralizerSubgroup]
  simp only [Late.sectionCentralizer, Set.mem_setOf_eq, Subgroup.mem_inf, and_assoc]

theorem perpOf_le (Z E : Subgroup G) : perpOf Z E ≤ Z := fun _ hz =>
  (mem_perpOf_iff.mp hz).1

theorem commutator_mem_pCoreOf {Z E : Subgroup G} {z e : G} (hz : z ∈ perpOf Z E) (he : e ∈ E) :
    e * z * e⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 E := by
  have h := (mem_perpOf_iff.mp hz).2.2 e he
  have hinv : (z * e * z⁻¹ * e⁻¹)⁻¹ = e * z * e⁻¹ * z⁻¹ := by group
  rw [← hinv]
  exact (CFSG.Open.pCoreOf 2 E).inv_mem h

private theorem conj_mem_perpOf {Z E : Subgroup G} {g z : G}
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hz : z ∈ perpOf Z E) : g * z * g⁻¹ ∈ perpOf Z E := by
  have hgO : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 E : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E hgE
  obtain ⟨hzZ, hzE, hzc⟩ := mem_perpOf_iff.mp hz
  refine mem_perpOf_iff.mpr ⟨?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgZ z).mp hzZ
  · exact (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem hgE hzE)
      ((Subgroup.normalizer (E : Set G)).inv_mem hgE)
  · intro e he
    have hge : g⁻¹ * e * g ∈ E := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (E : Set G)).inv_mem hgE) e).mp he
    have h1 : z * (g⁻¹ * e * g) * z⁻¹ * (g⁻¹ * e * g)⁻¹ ∈ CFSG.Open.pCoreOf 2 E :=
      hzc _ hge
    have h2 : g * (z * (g⁻¹ * e * g) * z⁻¹ * (g⁻¹ * e * g)⁻¹) * g⁻¹ ∈
        CFSG.Open.pCoreOf 2 E := (Subgroup.mem_normalizer_iff.mp hgO _).mp h1
    have heq : g * z * g⁻¹ * e * (g * z * g⁻¹)⁻¹ * e⁻¹ =
        g * (z * (g⁻¹ * e * g) * z⁻¹ * (g⁻¹ * e * g)⁻¹) * g⁻¹ := by group
    rw [heq]
    exact h2

theorem mem_normalizer_perpOf {Z E : Subgroup G} {g : G}
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgE : g ∈ Subgroup.normalizer (E : Set G)) :
    g ∈ Subgroup.normalizer (perpOf Z E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact conj_mem_perpOf hgZ hgE
  · intro hz
    have h := conj_mem_perpOf (Z := Z) (E := E) (g := g⁻¹) (z := g * z * g⁻¹)
      ((Subgroup.normalizer (Z : Set G)).inv_mem hgZ)
      ((Subgroup.normalizer (E : Set G)).inv_mem hgE) hz
    have heq : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
    rwa [heq] at h

theorem le_normalizer_perpOf {Z E : Subgroup G}
    (hZE : Z ≤ Subgroup.normalizer (E : Set G)) :
    Z ≤ Subgroup.normalizer (perpOf Z E : Set G) := fun _ hz =>
  mem_normalizer_perpOf (Subgroup.le_normalizer hz) (hZE hz)

theorem pCoreOf_le_perpOf {Z E : Subgroup G} (hEZ : E ≤ Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G)) :
    CFSG.Open.pCoreOf 2 E ≤ perpOf Z E := by
  intro z hz
  have hzE : z ∈ E := (CFSG.LieType.BorelTits.pCoreOf_le 2 E) hz
  refine mem_perpOf_iff.mpr ⟨hEZ hzE, Subgroup.le_normalizer hzE, ?_⟩
  intro e he
  have hzN : e * z⁻¹ * e⁻¹ ∈ CFSG.Open.pCoreOf 2 E :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E he) z⁻¹).mp
      ((CFSG.Open.pCoreOf 2 E).inv_mem hz)
  have hmul : z * (e * z⁻¹ * e⁻¹) ∈ CFSG.Open.pCoreOf 2 E :=
    (CFSG.Open.pCoreOf 2 E).mul_mem hz hzN
  have heq : z * (e * z⁻¹ * e⁻¹) = z * e * z⁻¹ * e⁻¹ := by group
  rwa [← heq]

theorem pCoreOf_two_le_perpOf {Z E : Subgroup G} (hEZ : E ≤ Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G)) :
    CFSG.Open.pCoreOf 2 Z ≤ perpOf Z E := by
  have hEZ' : E ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Z : Set G) :=
    hEZ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Z)
  have hnorm : E ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Z ⊓ E : Subgroup G) : Set G) :=
    (le_inf hEZ' Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hN2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Z ⊓ E) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Z).to_inf_left
  have hcore : CFSG.Open.pCoreOf 2 Z ⊓ E ≤ CFSG.Open.pCoreOf 2 E :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hN2
  intro z hz
  have hzZ : z ∈ Z := (CFSG.LieType.BorelTits.pCoreOf_le 2 Z) hz
  refine mem_perpOf_iff.mpr ⟨hzZ, hZE hzZ, ?_⟩
  intro e he
  have hcommZ : z * e * z⁻¹ * e⁻¹ ∈ CFSG.Open.pCoreOf 2 Z := by
    have h1 : e * z⁻¹ * e⁻¹ ∈ CFSG.Open.pCoreOf 2 Z :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Z (hEZ he)) z⁻¹).mp
        ((CFSG.Open.pCoreOf 2 Z).inv_mem hz)
    have hmul : z * (e * z⁻¹ * e⁻¹) ∈ CFSG.Open.pCoreOf 2 Z :=
      (CFSG.Open.pCoreOf 2 Z).mul_mem hz h1
    have heq : z * (e * z⁻¹ * e⁻¹) = z * e * z⁻¹ * e⁻¹ := by group
    rwa [← heq]
  have hcommE : z * e * z⁻¹ * e⁻¹ ∈ E := by
    have hconj : z * e * z⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hZE hzZ) e).mp he
    have hmul : (z * e * z⁻¹) * e⁻¹ ∈ E := E.mul_mem hconj (E.inv_mem he)
    have heq : (z * e * z⁻¹) * e⁻¹ = z * e * z⁻¹ * e⁻¹ := by group
    rwa [heq] at hmul
  exact hcore ⟨hcommZ, hcommE⟩

theorem isSolvable_perpOf {Z E : Subgroup G} (h3 : ¬ 3 ∣ Nat.card Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G))
    (hE : ∀ J ∈ thetaComponentsIn Z, J ≤ E) : Group.IsSolvable ↥(perpOf Z E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  let H : Subgroup G := perpOf Z E
  have h3H : ¬ 3 ∣ Nat.card ↥H := by
    intro h
    apply h3
    have hcard : Nat.card ↥H = Nat.card ↥(H.subgroupOf Z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (perpOf_le Z E)).toEquiv.symm
    rw [hcard] at h
    exact h.trans (Subgroup.card_subgroup_dvd_card (H.subgroupOf Z))
  obtain ⟨J, hJ⟩ := Sec15.Proof1423.exists_mem_thetaComponents_of_not_isSolvable
    (H := ↥H) h3H hns
  let K : Subgroup G := J.map H.subtype
  have hKH : K ∈ thetaComponentsIn H := by
    refine mem_thetaComponentsIn_iff.mpr ⟨Subgroup.map_subtype_le J, ?_⟩
    show (J.map H.subtype).subgroupOf H ∈ thetaComponents 3 H
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hJ
  have hHnormal : (H.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perpOf_le Z E)).mpr
      (le_normalizer_perpOf hZE)
  have hKZ : K ∈ thetaComponentsIn Z :=
    Sec15.Proof1423.mem_thetaComponentsIn_of_isSubnormal hKH (perpOf_le Z E) hHnormal.isSubnormal
  have hKle : K ≤ E := hE K hKZ
  haveI : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hKZ
  have hKcore : K ≤ CFSG.Open.pCoreOf 2 E := by
    have hcomm : ⁅K, K⁆ ≤ CFSG.Open.pCoreOf 2 E := by
      calc ⁅K, K⁆ ≤ ⁅H, E⁆ := Subgroup.commutator_mono (le_of_mem_thetaComponentsIn hKH) hKle
        _ ≤ CFSG.Open.pCoreOf 2 E := by
            rw [Subgroup.commutator_le]
            intro z hz e he
            exact (mem_perpOf_iff.mp hz).2.2 e he
    calc K = ⁅K, K⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ CFSG.Open.pCoreOf 2 E := hcomm
  have hK2 : IsPGroup 2 K :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E).to_le hKcore
  have hKq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 hKZ
  haveI : Nontrivial ↥K := by
    haveI : Nontrivial (K ⧸ aschbacherSolvableCore 3 K) :=
      LocalCores.isQuasisimple_nontrivial hKq
    exact (QuotientGroup.mk'_surjective (N := aschbacherSolvableCore 3 K)).nontrivial
  haveI : Group.IsNilpotent ↥K := hK2.isNilpotent
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance

theorem pCoreOf_le_of_sylow {Z E S : Subgroup G} (hEZ : E ≤ Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G))
    (hSle : S ≤ perpOf Z E) (hS : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex (perpOf Z E)) :
    CFSG.Open.pCoreOf 2 E ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := perpOf Z E
  have hSH : S ≤ H := hSle
  have hNH : CFSG.Open.pCoreOf 2 E ≤ H := pCoreOf_le_perpOf hEZ hZE
  have hHnorm : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 E : Set G) :=
    (perpOf_le Z E).trans
      (hZE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E))
  haveI hNnormal : ((CFSG.Open.pCoreOf 2 E).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHnorm
  have hNp : IsPGroup 2 ((CFSG.Open.pCoreOf 2 E).subgroupOf H) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E).comap_subtype
  have hSp : IsPGroup 2 (S.subgroupOf H) := hS.comap_subtype
  have hle : ((CFSG.Open.pCoreOf 2 E).subgroupOf H) ≤ S.subgroupOf H :=
    hNp.le_sylow_of_normal (hSp.toSylow hSyl)
  calc CFSG.Open.pCoreOf 2 E
      = ((CFSG.Open.pCoreOf 2 E).subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ (S.subgroupOf H).map H.subtype := Subgroup.map_mono hle
    _ = S := Subgroup.map_subgroupOf_eq_of_le hSH

theorem pCoreOf_two_le_of_sylow {Z E S : Subgroup G} (hEZ : E ≤ Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G))
    (hSle : S ≤ perpOf Z E) (hS : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex (perpOf Z E)) :
    CFSG.Open.pCoreOf 2 Z ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := perpOf Z E
  have hSH : S ≤ H := hSle
  have hNH : CFSG.Open.pCoreOf 2 Z ≤ H := pCoreOf_two_le_perpOf hEZ hZE
  have hHnorm : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Z : Set G) :=
    (perpOf_le Z E).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Z)
  haveI hNnormal : ((CFSG.Open.pCoreOf 2 Z).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHnorm
  have hNp : IsPGroup 2 ((CFSG.Open.pCoreOf 2 Z).subgroupOf H) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Z).comap_subtype
  have hSp : IsPGroup 2 (S.subgroupOf H) := hS.comap_subtype
  have hle : ((CFSG.Open.pCoreOf 2 Z).subgroupOf H) ≤ S.subgroupOf H :=
    hNp.le_sylow_of_normal (hSp.toSylow hSyl)
  calc CFSG.Open.pCoreOf 2 Z
      = ((CFSG.Open.pCoreOf 2 Z).subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ (S.subgroupOf H).map H.subtype := Subgroup.map_mono hle
    _ = S := Subgroup.map_subgroupOf_eq_of_le hSH

theorem le_normalizer_of_sylow {Z E S : Subgroup G} (hEZ : E ≤ Z)
    (hZE : Z ≤ Subgroup.normalizer (E : Set G))
    (hSle : S ≤ perpOf Z E) (hS : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex (perpOf Z E)) :
    E ≤ Subgroup.normalizer (S : Set G) := by
  have hOS : CFSG.Open.pCoreOf 2 E ≤ S := pCoreOf_le_of_sylow hEZ hZE hSle hS hSyl
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have hcomm : e * s * e⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 E :=
      commutator_mem_pCoreOf (hSle hs) he
    have hmul : (e * s * e⁻¹ * s⁻¹) * s ∈ S := S.mul_mem (hOS hcomm) hs
    have heq : (e * s * e⁻¹ * s⁻¹) * s = e * s * e⁻¹ := by group
    rwa [heq] at hmul
  · intro hs
    have hcomm : e⁻¹ * (e * s * e⁻¹) * (e⁻¹)⁻¹ * (e * s * e⁻¹)⁻¹ ∈
        CFSG.Open.pCoreOf 2 E := commutator_mem_pCoreOf (hSle hs) (E.inv_mem he)
    have hmul : (e⁻¹ * (e * s * e⁻¹) * (e⁻¹)⁻¹ * (e * s * e⁻¹)⁻¹) * (e * s * e⁻¹) ∈ S :=
      S.mul_mem (hOS hcomm) hs
    have heq : (e⁻¹ * (e * s * e⁻¹) * (e⁻¹)⁻¹ * (e * s * e⁻¹)⁻¹) * (e * s * e⁻¹) = s := by
      group
    rwa [heq] at hmul

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
