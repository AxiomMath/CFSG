module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearRootNormalizer
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI
open scoped Pointwise MatrixGroups

universe u

theorem normalizer_card_map_equiv {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (e : G ≃* H) :
    Nat.card (Subgroup.normalizer (P.map e.toMonoidHom : Set H)) =
      Nat.card (Subgroup.normalizer (P : Set G)) := by
  rw [← Subgroup.map_normalizer_eq_of_bijective P e.bijective,
    Subgroup.card_map_of_injective e.injective]

theorem psl2_even_sylow_normalizer_card
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (P : Sylow 2 (PSL2MatrixGroup K)) :
    Nat.card (Subgroup.normalizer (P : Set (PSL2MatrixGroup K))) =
      (Nat.card K - 1) * Nat.card K := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* PSL2MatrixGroup K :=
    linearCover_pslEquivSL.symm
  let P0 := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective
    (linearCoverRootSylow f hcard)
  have hP0 : (P0 : Subgroup (PSL2MatrixGroup K)) =
      (linearCoverRootSubgroup K).map e.toMonoidHom := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup K) P0 P
  have hP : (P : Subgroup (PSL2MatrixGroup K)) =
      (P0 : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  change Nat.card (Subgroup.normalizer
    ((P : Subgroup (PSL2MatrixGroup K)) : Set (PSL2MatrixGroup K))) = _
  rw [hP, normalizer_card_map_equiv, hP0, normalizer_card_map_equiv,
    linear_root_normalizer_card]

theorem psl2_even_sylow_elementary_card
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (P : Sylow 2 (PSL2MatrixGroup K)) :
    IsElementaryAbelian 2 P ∧ Nat.card P = Nat.card K := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨e⟩ := huppert_II_8_2_a_sylow_equiv_additive hcard P
  have hcomm : IsMulCommutative P := ⟨⟨fun x y => e.symm.injective
    (by rw [map_mul, map_mul]; exact mul_comm _ _)⟩⟩
  have hpow : ∀ x : P, x ^ 2 = 1 := by
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    change Multiplicative.ofAdd (2 • (e.symm x).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (by
      simp only [two_nsmul, CharTwo.add_self_eq_zero])
  refine ⟨?_, ?_⟩
  · exact
      { toIsMulCommutative := hcomm
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  · exact (Nat.card_congr e.symm.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)

theorem psl2_nonidentity_unique_sylow
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (P Q : Sylow 2 (PSL2MatrixGroup K))
    (x : PSL2MatrixGroup K) (hx : x ≠ 1) (hxP : x ∈ P) (hxQ : x ∈ Q) :
    (P : Subgroup (PSL2MatrixGroup K)) = (Q : Subgroup (PSL2MatrixGroup K)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, S, _, _, _, _, hpart⟩ := huppert_II_8_5_a_psl2_cover hcard P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup K) P Q
  have hQ : (Q : Subgroup (PSL2MatrixGroup K)) =
      (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  obtain ⟨T, _, huniq⟩ := hpart x hx
  have hPeq : (P : Subgroup (PSL2MatrixGroup K)) = T := huniq _
    ⟨hxP, Or.inl ⟨1, by
      rw [map_one]
      exact (Subgroup.map_id _).symm⟩⟩
  have hQeq : (Q : Subgroup (PSL2MatrixGroup K)) = T := huniq _
    ⟨hxQ, Or.inl ⟨g, hQ⟩⟩
  exact hPeq.trans hQeq.symm

theorem psl2_no_split_primes_normalizer_intersection_two
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K - 1))
    (P : Sylow 2 (PSL2MatrixGroup K)) :
    IsPGroup 2 ((Subgroup.normalizer (P : Set (PSL2MatrixGroup K))).subgroupOf A) := by
  let N := (Subgroup.normalizer (P : Set (PSL2MatrixGroup K))).subgroupOf A
  have hNcop : Nat.Coprime (Nat.card N) (Nat.card K - 1) :=
    hcop.of_dvd_left N.card_subgroup_dvd_card
  have hNdiv : Nat.card N ∣ (Nat.card K - 1) * Nat.card K := by
    have h := Subgroup.card_comap_dvd_of_injective
      (Subgroup.normalizer (P : Set (PSL2MatrixGroup K))) A.subtype A.subtype_injective
    exact psl2_even_sylow_normalizer_card f hcard P ▸ h
  have hrootdiv : Nat.card N ∣ Nat.card K := hNcop.dvd_of_dvd_mul_left hNdiv
  exact IsPGroup.of_card_dvd_pow (hcard ▸ hrootdiv)

theorem psl2_no_split_primes_subgroup_sylow_normalizer_intersection
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K - 1))
    (R : Sylow 2 A) (P : Sylow 2 (PSL2MatrixGroup K))
    (hR : (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype =
      (R : Subgroup A)) :
    (Subgroup.normalizer (P : Set (PSL2MatrixGroup K))).subgroupOf A =
      (R : Subgroup A) := by
  apply R.is_maximal' (psl2_no_split_primes_normalizer_intersection_two f hcard A hcop P)
  intro x hx
  have hxP : x ∈ (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype := by
    rw [hR]
    exact hx
  exact Subgroup.le_normalizer hxP

theorem psl2_no_split_primes_subgroup_sylow_TI
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K - 1)) (R : Sylow 2 A) :
    ∀ g : A, g ∉ (R : Subgroup A) →
      Disjoint (R : Subgroup A) ((R : Subgroup A).conjBy g) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := R.exists_comap_subtype_eq
  have hN := psl2_no_split_primes_subgroup_sylow_normalizer_intersection
    f hcard A hcop R P hP
  intro g hg
  apply Subgroup.disjoint_def.mpr
  intro x hxR hxconj
  by_contra hxne
  have hxGne : (x : PSL2MatrixGroup K) ≠ 1 := fun h => hxne (Subtype.ext h)
  have hxP : (x : PSL2MatrixGroup K) ∈ P := by
    change x ∈ (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype
    rw [hP]
    exact hxR
  obtain ⟨y, hyR, hyx⟩ := Subgroup.mem_map.mp hxconj
  have hyP : (y : PSL2MatrixGroup K) ∈ P := by
    change y ∈ (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype
    rw [hP]
    exact hyR
  have hxPg : (x : PSL2MatrixGroup K) ∈
      (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj (g : PSL2MatrixGroup K)).toMonoidHom := by
    exact Subgroup.mem_map.mpr ⟨y, hyP, congrArg Subtype.val hyx⟩
  have hPg : (((g : PSL2MatrixGroup K) • P : Sylow 2 (PSL2MatrixGroup K)) :
      Subgroup (PSL2MatrixGroup K)) =
      (P : Subgroup (PSL2MatrixGroup K)).map
        (MulAut.conj (g : PSL2MatrixGroup K)).toMonoidHom := rfl
  have hxPg' : (x : PSL2MatrixGroup K) ∈ ((g : PSL2MatrixGroup K) • P) := by
    change (x : PSL2MatrixGroup K) ∈
      (((g : PSL2MatrixGroup K) • P : Sylow 2 (PSL2MatrixGroup K)) :
        Subgroup (PSL2MatrixGroup K))
    rw [hPg]
    exact hxPg
  have heq := psl2_nonidentity_unique_sylow f hcard P
    ((g : PSL2MatrixGroup K) • P) x hxGne hxP hxPg'
  have hgN : (g : PSL2MatrixGroup K) ∈
      Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (P : Subgroup (PSL2MatrixGroup K)).map
      (MulAut.conj (g : PSL2MatrixGroup K)).toMonoidHom =
        (P : Subgroup (PSL2MatrixGroup K))
    exact hPg.symm.trans heq.symm
  have hgR : g ∈ (R : Subgroup A) := hN ▸ hgN
  exact hg hgR

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
