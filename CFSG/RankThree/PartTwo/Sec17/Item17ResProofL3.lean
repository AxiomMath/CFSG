module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofComm
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
import CFSG.Quasithin.Background.A318PC7
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofClaim164
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def KS1721AutThreeL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X → ¬ 27 ∣ Nat.card X →
    ∀ (σ : MulAut X) (k : ℕ), σ ^ 3 ^ k = 1 → σ ^ 3 = 1

namespace Proof17Res

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_of_cube_mem {L T : Subgroup G} {c : G} (hT3 : IsPGroup 3 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hcT : c ∈ T) (hcL : c ∉ L) (hc3 : c ^ 3 = 1)
    (hcube : ∀ u ∈ T, u ^ 3 ∈ L → ∃ k : ℤ, (c ^ k)⁻¹ * u ∈ L) :
    ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup T := L.subgroupOf T with hN
  have hNn : N.Normal := ⟨fun n hn t => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hTL t.2) n).mp hn⟩
  set π := QuotientGroup.mk' N with hπ
  have hmem : ∀ x : T, π x = 1 ↔ (x : G) ∈ L := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
  have hQ3 : IsPGroup 3 (T ⧸ N) := hT3.to_quotient N
  set cT : T := ⟨c, hcT⟩ with hcT'
  have hcq3 : π cT ^ 3 = 1 := by
    rw [← map_pow, hmem]
    simp [hcT', hc3]
  have hcq1 : π cT ≠ 1 := fun h1 => hcL ((hmem cT).mp h1)
  have hZ : Nat.card (Subgroup.zpowers (π cT)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hcq3 hcq1]
  have hcyc : IsCyclic (⊤ : Subgroup (T ⧸ N)) := by
    refine CFSG.Quasithin.A318P.isCyclic_of_unique_three (hQ3.to_subgroup ⊤) hZ ?_
    intro r _ hr
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N r
    have hu3 : (u : G) ^ 3 ∈ L := by
      have h1 : π (u ^ 3) = 1 := by
        rw [map_pow]
        change (QuotientGroup.mk' N u) ^ 3 = 1
        rw [← hr]
        exact pow_orderOf_eq_one _
      have := (hmem (u ^ 3)).mp h1
      simpa using this
    obtain ⟨k, hk⟩ := hcube u u.2 hu3
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    change QuotientGroup.mk' N (cT ^ k) = QuotientGroup.mk' N u
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    simpa [hcT'] using hk
  have hcomm : ∀ a b : T ⧸ N, a * b = b * a := by
    intro a b
    have := (@IsCyclic.isMulCommutative ↥(⊤ : Subgroup (T ⧸ N)) _ hcyc).is_comm.comm
      ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩
    exact congrArg Subtype.val this
  intro x hx y hy
  have h1 : π (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : T)⁻¹ * (⟨y, hy⟩ : T)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm (π ⟨x, hx⟩) (π ⟨y, hy⟩)]
    group
  have := (hmem _).mp h1
  simpa using this

theorem pow_three_eq_one_of_aut {L : Subgroup G}
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hK : ∀ (σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (k : ℕ), σ ^ 3 ^ k = 1 → σ ^ 3 = 1)
    {u : G} (huN : u ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (huk : u ^ 3 ^ k = 1)
    (hu3 : u ^ 3 ∈ L) : u ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set u' : Subgroup.normalizer (L : Set G) := ⟨u, huN⟩ with hu'
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom u') with hσ
  have hσk : σ ^ 3 ^ k = 1 := by
    have h1 : u' ^ 3 ^ k = 1 := Subtype.ext (by simpa [hu'] using huk)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσ3 : σ ^ 3 = 1 := hK σ k hσk
  set v : ↥L := ⟨u ^ 3, hu3⟩ with hv
  have hconj : ∀ x : ↥L, π v * π x * (π v)⁻¹ = π x := by
    intro x
    have h1 := congrArg (fun φ : MulAut _ => φ (π x)) hσ3
    simp only [MulAut.one_apply] at h1
    have h2 : (σ ^ 3) (π x) = π (L.normalizerMonoidHom (u' ^ 3) x) := by
      rw [hσ, ← map_pow, ← map_pow]
      rfl
    have h3 : L.normalizerMonoidHom (u' ^ 3) x = v * x * v⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp [hv, hu']
    rw [h2, h3, map_mul, map_mul, map_inv] at h1
    exact h1
  have hcen : π v ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      have := hconj x
      change π x * π v = π v * π x
      calc π x * π v = π v * π x * (π v)⁻¹ * π v := by rw [this]
        _ = π v * π x := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  have hvk : v ^ 3 ^ k = 1 := Subtype.ext (by
    simp only [hv, SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, huk, one_pow])
  have hv3 : IsPGroup 3 (Subgroup.zpowers v) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hvk)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hv1 : v = 1 := injOn_mk_of_isPGroup Nat.prime_three hv3 (Subgroup.mem_zpowers v)
    (one_mem _) (by rw [hcen, map_one])
  exact congrArg Subtype.val hv1

theorem mem_of_pow_three_of_item1511 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀) (h1511 : Item1511 A (lB A) c L)
    (hL : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (hMeets : MeetsY4 A (lB A) L Y₀)
    {T : Subgroup G} (hT3 : IsPGroup 3 T)
    (hTH : T ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) (hAT : A ≤ T) :
    ∀ u ∈ T, u ^ 3 = 1 → u ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y₀ : Set G)
    with hK
  have hTK : T ≤ K := le_inf hTH (hTH.trans hs.normalizer_c_le)
  have hT' : IsPGroup 3 (T.subgroupOf K) := hT3.comap_subtype
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  set P := (Q : Subgroup K).map K.subtype with hP
  have hPsyl : IsSylowOf 3 P K := ⟨Q, rfl⟩
  have hTP : T ≤ P := fun x hx => ⟨⟨x, hTK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨p, e, hp, he, hiso⟩ := hL
  have hY₀ : Y₀ ∈ scriptY0 A (lB A) := scriptY0Star_subset A (lB A) hs.mem_y0Star
  obtain ⟨-, -, -, -, hAeq⟩ := @h1511 p e hp he hiso Y₀ hY₀ hMeets P (hAT.trans hTP) hPsyl
  intro u hu hu3
  rw [hAeq]
  exact Subgroup.subset_closure ⟨hTP hu, hu3⟩

end Proof17Res

open Proof17Res in
theorem claim1721SCommL3_of
    (h1511 : Item1511S17) (hMeets : Claim1715Meets)
    (hSyl : Claim1721SylL3) (h9 : CardInfNineS17) (hK : KS1721AutThreeL3) :
    Claim1721SCommL3 := by
  intro G _ _ A c L Y₀ Y₁ S p P h hL hΩ T hT hAT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  have h9' : Nat.card (A ⊓ L : Subgroup G) = 9 := h9 G A c L Y₀ hs
  have hcL : c ∉ L := hs.toSec15R.hypS.2.2 c hs.zpowers_mem_omegaA L hs.mem_lA
  have hcA : c ∈ A := hs.c_mem
  have h3L : 3 ∣ Nat.card L := by
    have := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9'] at this
    exact (by norm_num : 3 ∣ 9).trans this
  have hCL := Sec15R.centralizer_le_normalizer_L hs.toSec15R h3L
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hT.le.trans hCL
  have hT3 : IsPGroup 3 T := hT.isPGroup
  have hTH : T ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hT.le.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hΩ1 := mem_of_pow_three_of_item1511 hs (h1511 G A c L Y₀ hs) hL (hMeets G A c L Y₀ hs)
    hT3 hTH hAT
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_eq_bot_of_types hs.mem_lA.1 (Or.inr (Or.inl hL))
  have h27 : ¬ 27 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := fun h27 =>
    hSyl G A c L Y₀ Y₁ S p P h hL (h27.trans (Subgroup.card_quotient_dvd_card _))
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Steps165.eq_zpowers_sup_inf hs.toSec15R hcL h9'
  have hcAL : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hs.le_centralizer_c he.2))
  refine commutator_mem_of_cube_mem hT3 hTL (hAT hcA) hcL hs.c_pow_three ?_
  intro u hu hu3
  obtain ⟨k, hk⟩ := hT3 ⟨u, hu⟩
  have huk : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hu1 := pow_three_eq_one_of_aut hZ (hK _ hL h27) (hTL hu) huk hu3
  have huA := hΩ1 u hu hu1
  rw [hAeq] at huA
  obtain ⟨j, a, ha, rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcAL huA
  exact ⟨j, by simpa using ha.2⟩

end CFSG.RankThree.PartTwo.Sec17
