module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

theorem closure_threeElements_opp (Y : Subgroup G) :
    closure {x : ↥(Opp 3 Y) | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤ := by
  have h : closure (((↑) : ↥(Opp 3 Y) → G) ⁻¹'
      {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  refine eq_top_iff.mpr (h.symm.le.trans (Subgroup.closure_mono ?_))
  rintro x ⟨-, k, hk⟩
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩

theorem closure_threeElements_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (h : closure {x : A | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) :
    closure {x : B | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤ := by
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective f hf, ← h, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hk ▸ orderOf_map_dvd f x)
  exact Subgroup.subset_closure ⟨j, hj⟩

theorem closure_threeElements_barO3 (Y : Subgroup G) :
    closure {x : BarO3 (Opp 3 Y) | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤ :=
  closure_threeElements_of_surjective _ (QuotientGroup.mk'_surjective _)
    (closure_threeElements_opp Y)

theorem pPrimeCore_barO3 (X : Subgroup G) : CFSG.pPrimeCore 3 (BarO3 X) = ⊥ :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3

theorem not_hasE9_barO3 {X : Subgroup G} (hE9 : ¬ HasE9 ↥X) : ¬ HasE9 (BarO3 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact fun h => hE9 (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient
    (CFSG.pPrimeCore 3 ↥X)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card) h)

theorem eq_top_of_map_barO3_eq_top {X : Subgroup G}
    (hgen : closure {x : ↥X | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) {N : Subgroup ↥X} [N.Normal]
    (hN : N.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) = ⊤) : N = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  have hxN : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X) x ∈
      N.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) := hN ▸ Subgroup.mem_top _
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxN
  have hp : n⁻¹ * x ∈ CFSG.pPrimeCore 3 ↥X := QuotientGroup.eq.mp hnx
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 3 ^ k := hk ▸ orderOf_map_dvd _ x
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  have hx' : QuotientGroup.mk' N x = QuotientGroup.mk' N (n⁻¹ * x) := by
    rw [map_mul, map_inv, hn1, inv_one, one_mul]
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ Nat.card (CFSG.pPrimeCore 3 ↥X) := by
    rw [hx']
    exact (orderOf_map_dvd _ _).trans (Subgroup.orderOf_dvd_natCard _ hp)
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card) h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

theorem isSimpleGroup_barO3 (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {Y : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥(Opp 3 Y)) (hE9 : ¬ HasE9 ↥(Opp 3 Y))
    (hX : ¬ IsPGroup 3 (BarO3 (Opp 3 Y))) :
    IsSimpleGroup (BarO3 (Opp 3 Y)) ∧ ∃ a b : BarO3 (Opp 3 Y), a * b ≠ b * a :=
  isSimpleGroup_of_not_hasE9 hSch (hK.quotient _) (not_hasE9_barO3 hE9) (pPrimeCore_barO3 _)
    (closure_threeElements_barO3 Y) hX

theorem isPerfect_opp {Y : Subgroup G} (hE9 : ¬ HasE9 ↥(Opp 3 Y))
    (hX : ¬ IsPGroup 3 (BarO3 (Opp 3 Y))) : Group.IsPerfect ↥(Opp 3 Y) := by
  haveI : Group.IsPerfect (BarO3 (Opp 3 Y)) := isPerfect_of_not_hasE9 (not_hasE9_barO3 hE9)
    (pPrimeCore_barO3 _) (closure_threeElements_barO3 Y) hX
  refine ⟨eq_top_of_map_barO3_eq_top (closure_threeElements_opp Y) ?_⟩
  rw [← derivedSeries_one, map_derivedSeries_eq (QuotientGroup.mk'_surjective _),
    derivedSeries_one]
  exact Group.IsPerfect.commutator_eq_top

theorem eq_opp_of_normal (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {Y : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥(Opp 3 Y)) (hE9 : ¬ HasE9 ↥(Opp 3 Y))
    (hX : ¬ IsPGroup 3 (BarO3 (Opp 3 Y))) {D₃ : Subgroup G} (hDX : D₃ ≤ Opp 3 Y)
    (hD3 : Nat.card D₃ = 3) {B : Subgroup G} (hBX : B ≤ Opp 3 Y)
    (hBn : Opp 3 Y ≤ normalizer (B : Set G)) (hDB : D₃ ≤ B) : B = Opp 3 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := (isSimpleGroup_barO3 hSch hK hE9 hX).1
  haveI hBnorm : (B.subgroupOf (Opp 3 Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).mpr hBn
  haveI : ((B.subgroupOf (Opp 3 Y)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y)))).Normal :=
    hBnorm.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 (hD3 ▸ dvd_rfl : 3 ∣ Nat.card D₃)
  have hdX : (d : G) ∈ Opp 3 Y := hDX d.2
  have hdmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y)) ⟨d, hdX⟩ ∈
      (B.subgroupOf (Opp 3 Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hDB d.2))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((B.subgroupOf (Opp 3 Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y))))
    with hbot | htop
  · exfalso
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hdmem
    have hdvd := Subgroup.orderOf_dvd_natCard _ hdmem
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hd] at hdvd
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, dvd_rfl, hdvd⟩
      CFSG.pPrimeCore_coprime_card
  · exact le_antisymm hBX (Subgroup.subgroupOf_eq_top.mp
      (eq_top_of_map_barO3_eq_top (closure_threeElements_opp Y) htop))

theorem not_hasE9_opp {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    ¬ HasE9 ↥(Opp 3 Y) := by
  intro h
  have hle : Opp 3 Y ≤ L9 Y H := fun x hx =>
    Subgroup.mem_iSup_of_mem (1 : ↥H) ⟨x, hx, by simp⟩
  have h2 := CFSG.GroupTheory.ThreeTranspositions.two_le_pRank_of_hasE9_subgroup (L9 Y H)
    (h.map_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  have h1 : CFSG.Open.pRank 3 (L9 Y H) = 1 := hyp.2.1.2.2
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
