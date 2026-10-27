module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5U3T
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

section U3Coord

variable {K : Type*} [Field K] [CharP K 2] {n : ℕ} (J : HermitianForm n K)

private theorem coord_mul_self_eq_one_iff_cs5 (z : hermitianUnipotentCoord J) :
    z * z = 1 ↔ z.1.1 = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : hermitianUnipotentCoord J => w.1.2) h
    change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0 at h1
    have h2 : z.1.1 * J.conj z.1.1 = 0 := by
      have : z.1.2 + z.1.2 = 0 := CharTwo.add_self_eq_zero _
      rw [this, zero_sub, neg_eq_zero] at h1
      exact h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact (map_eq_zero J.conj).mp h3
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · show z.1.1 + z.1.1 = 0
      exact CharTwo.add_self_eq_zero _
    · show z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0
      rw [h, zero_mul, sub_zero]
      exact CharTwo.add_self_eq_zero _

end U3Coord

theorem ti_of_stronglyEmbedded_cs5 {G : Type} [Group G] {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (S : Set G))) :
    ∀ g ∈ (⊤ : Subgroup G), g ∉ Subgroup.normalizer (S : Set G) →
      S ⊓ B6.conjSub g S = ⊥ := by
  intro g _ hgN
  have hodd := hSE.2.2 g⁻¹ (fun h => hgN (by simpa using Subgroup.inv_mem _ h))
  rw [inv_inv] at hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxg⟩ := hx
  have hxM : x ∈ Subgroup.normalizer (S : Set G) ⊓
      (Subgroup.normalizer (S : Set G)).map (MulAut.conj g).toMonoidHom :=
    ⟨Subgroup.le_normalizer hxS, ⟨g⁻¹ * x * g, Subgroup.le_normalizer (B6.mem_conjSub.mp hxg),
      by simp [mul_assoc]⟩⟩
  have hd := Subgroup.orderOf_dvd_natCard _ hxM
  obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_mem_cs5 hS hxS
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hodd' : Odd (orderOf x) := hodd.of_dvd_nat hd
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ hodd'.coprime_two_right
  have := Nat.Coprime.eq_one_of_dvd hcop h2
  exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp this)

theorem RankOneSyl.of_one_sylow_cs5 {G : Type} [Group G] [Finite G] {q : ℕ} {S₀ : Subgroup G}
    (h₀ : RankOneSyl (⊤ : Subgroup G) S₀ q) :
    ∀ S : Subgroup G, IsSylowTwoOf S ⊤ → RankOneSyl (⊤ : Subgroup G) S q := by
  intro S hS
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top_cs5 h₀.sylow hS
  rw [hg]
  exact RankOneSyl.map_mulEquiv_cs5 (MulAut.conj g) h₀

section Model

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut

theorem rankOneSyl_root_psu3_cs5 {K : Type} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    RankOneSyl (⊤ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (unitaryCoverRoot J hJ)
      (2 ^ f) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsimple : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  obtain ⟨-, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, hZ2, hZcard, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hcen : centerSub (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    map_center_eq_sylowCenter _
  rw [← hS]
  refine ⟨isSylowTwoOf_top_of_sylow S, ti_of_stronglyEmbedded_cs5 S.isPGroup' hSE,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [top_inf_eq, Subgroup.relIndex_top_right]
    refine (Sylow.card_eq_index_normalizer S).symm.trans ?_
    rw [hcard, hS]
  ·
    intro N hN hnorm
    haveI : N.Normal := ⟨fun n hn g => hnorm g (Subgroup.mem_top g) n hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      apply hSE.1
      rw [eq_top_iff]
      intro x _
      exact (hN (h ▸ Subgroup.mem_top x)).2
  ·
    rw [hcen]
    exact hZcard
  ·
    intro z hz
    rw [hcen] at hz
    have := hZ2 z hz
    rwa [pow_two] at this
  ·
    intro z hz hz1 z' hz' hz'1
    rw [hcen] at hz hz'
    obtain ⟨b, hb, hbz⟩ := normalizer_transitive_center hSE hZ2 hz hz' hz1 hz'1
    refine ⟨b⁻¹, ⟨Subgroup.mem_top _, Subgroup.inv_mem _ hb⟩, ?_⟩
    rw [inv_inv]
    exact hbz
  ·
    intro x hx hx2
    rw [hcen]
    rw [hS] at hx ⊢
    obtain ⟨z, rfl⟩ := hx
    have hzz : z * z = 1 :=
      CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
        (by rw [map_mul, hx2, map_one])
    exact (mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ z).mpr
      ((coord_mul_self_eq_one_iff_cs5 J z).mp hzz)
  · omega

end Model

theorem rankOneSyl_top_of_isPSU_three_cs5 {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hG : IsPSU 3 2 n G) {S : Subgroup G} (hS : IsSylowTwoOf S ⊤) :
    RankOneSyl (⊤ : Subgroup G) S (2 ^ n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := exists_mulEquiv_psu3_proj_cs5 hn hG
  let K := FiniteField.Extension (GaloisField 2 n) 2 2
  let J := binaryQuadraticHermitian n (by omega)
  haveI : CharP K 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (GaloisField 2 n) K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  haveI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv G e.toEquiv
  exact RankOneSyl.of_mulEquiv_cs5 e.symm
    (RankOneSyl.of_one_sylow_cs5 (rankOneSyl_root_psu3_cs5 J n hn hKcard hfixed hJ)) S hS

theorem rankOneSyl_of_isPSU_three_cs5 {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y} {n : ℕ}
    (hn : 2 ≤ n) (hX : IsPSU 3 2 n ↥X) (hS : IsSylowTwoOf S X) :
    RankOneSyl X S (2 ^ n) :=
  RankOneSyl.of_subgroup_cs5 hS.1
    (rankOneSyl_top_of_isPSU_three_cs5 hn hX ((isSylowTwoOf_top_iff_cs5 hS.1).mpr hS))

end CFSG.Quasithin.H13
