module

public import CFSG.RankThree.PartTwo.Sec15.Item1510Proof
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Steps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_inSubgroup_theta (L : Subgroup G) :
    Nat.card (inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card (aschbacherSolvableCore 3 ↥L) :=
  Subgroup.card_map_of_injective L.subtype_injective

theorem not_three_dvd_card_theta (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
  rw [card_inSubgroup_theta]
  exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1

theorem isSolvable_theta (L : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) L) := by
  have hs := (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  exact Group.isSolvable_of_surjective
    (f := (L.subtype.subgroupMap (aschbacherSolvableCore 3 ↥L)))
    (MonoidHom.subgroupMap_surjective _ _)

theorem inf_eq_bot_of_coprime {X Y : Subgroup G} (hX : IsPGroup 3 X) (hY : ¬ 3 ∣ Nat.card Y) :
    X ⊓ Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hX.to_le (inf_le_left : X ⊓ Y ≤ X))
  have h2 : Nat.card (X ⊓ Y : Subgroup G) ∣ Nat.card Y := Subgroup.card_dvd_of_le inf_le_right
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  · exfalso
    apply hY
    rw [hn] at h2
    exact (dvd_pow_self 3 (Nat.succ_ne_zero n)).trans h2

omit [Finite G] in
theorem isPGroup_of_card_nine {S : Subgroup G} (hS9 : Nat.card S = 9) : IsPGroup 3 S :=
  IsPGroup.of_card (n := 2) (by rw [hS9]; norm_num)

section Image

variable {L S : Subgroup G}

theorem card_map_mk_of_card_nine (hSL : S ≤ L) (hS9 : Nat.card S = 9) :
    Nat.card ((S.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 := by
  have h := Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) (S.subgroupOf L)
  have hSc : Nat.card (S.subgroupOf L) = 9 := by
    rw [← hS9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hk : Nat.card ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).ker.subgroupOf
      (S.subgroupOf L)) = 1 := by
    rw [QuotientGroup.ker_mk']
    set K := (aschbacherSolvableCore 3 ↥L).subgroupOf (S.subgroupOf L) with hK
    have h1 : Nat.card K ∣ 9 := hSc ▸ Subgroup.card_subgroup_dvd_card K
    have h2 : ¬ 3 ∣ Nat.card K := by
      intro h3
      apply (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
      have hKc : Nat.card K =
          Nat.card (aschbacherSolvableCore 3 ↥L ⊓ S.subgroupOf L : Subgroup ↥L) := by
        rw [hK, ← Subgroup.subgroupOf_map_subtype,
          Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      rw [hKc] at h3
      exact h3.trans (Subgroup.card_dvd_of_le inf_le_left)
    have hcop : Nat.Coprime (Nat.card K) 9 :=
      (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h2)).symm
    exact Nat.Coprime.eq_one_of_dvd hcop h1
  rw [hk, mul_one, hSc] at h
  exact h

theorem mk_ne_one_of_mem (hSL : S ≤ L) (hS9 : Nat.card S = 9) {b : G} (hbS : b ∈ S)
    (hb1 : b ≠ 1) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (⟨b, hSL hbS⟩ : ↥L) ≠ 1 := by
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hb : b ∈ S ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨hbS, ⟨⟨b, hSL hbS⟩, h, rfl⟩⟩
  rw [inf_eq_bot_of_coprime (isPGroup_of_card_nine hS9) (not_three_dvd_card_theta L)] at hb
  exact hb1 hb

end Image

theorem inf_centralizer_le_sup_theta {L S : Subgroup G} (hSL : S ≤ L) (hS9 : Nat.card S = 9)
    (χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) {b : G} (hbS : b ∈ S)
    (hb1 : b ≠ 1) :
    L ⊓ Subgroup.centralizer ({b} : Set G) ≤ S ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set ψ := χ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hψ
  set S' := (S.subgroupOf L).map π with hS'
  have hS'9 : Nat.card S' = 9 := card_map_mk_of_card_nine hSL hS9
  set E := S'.map ψ.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective, hS'9]
  set b' : ↥L := ⟨b, hSL hbS⟩ with hb'
  have hb'S : π b' ∈ S' := ⟨b', Subgroup.mem_subgroupOf.mpr hbS, rfl⟩
  have hb'1 : ψ (π b') ≠ 1 := by
    rw [ne_eq, MulEquiv.map_eq_one_iff]
    exact mk_ne_one_of_mem hSL hS9 hbS hb1
  have hC := KFacts.L34.centralizer_eq_of_card_eq_nine KFacts.L34.card_galoisField_two_two hE9
    (⟨π b', hb'S, rfl⟩ : ψ (π b') ∈ E) hb'1
  rintro g ⟨hgL, hgb⟩
  set g' : ↥L := ⟨g, hgL⟩ with hg'
  have hcomm : ψ (π g') ∈ Subgroup.centralizer ({ψ (π b')} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp hgb)
  rw [hC] at hcomm
  obtain ⟨y, ⟨s, hsS, hsy⟩, hy⟩ := hcomm
  have hyg : π s = π g' := by
    rw [hsy]
    exact ψ.injective hy
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyg
  have hgs : g = (s : G) * ((s⁻¹ * g' : ↥L) : G) := by
    simp [hg']
  rw [hgs]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hsS) ⟨s⁻¹ * g', hyg, rfl⟩

theorem le_theta_of_le_normalizer {L S Y : Subgroup G} (hSL : S ≤ L) (hS9 : Nat.card S = 9)
    (χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) (hYL : Y ≤ L)
    (hY3 : ¬ 3 ∣ Nat.card Y) (hSY : S ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set ψ := χ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hψ
  set S' := (S.subgroupOf L).map π with hS'
  set Y' := (Y.subgroupOf L).map π with hY'
  have hS'9 : Nat.card S' = 9 := card_map_mk_of_card_nine hSL hS9
  have hSY' : S' ≤ Subgroup.normalizer (Y' : Set _) := by
    refine le_trans ?_ (Subgroup.le_normalizer_map π)
    refine Subgroup.map_mono fun s hs => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h := Subgroup.mem_normalizer_iff.mp (hSY (Subgroup.mem_subgroupOf.mp hs)) (z : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h
  have hY'3 : ¬ 3 ∣ Nat.card Y' := by
    intro h3
    apply hY3
    have h1 := Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf π (Y.subgroupOf L)
    have h2 : Nat.card (Y.subgroupOf L) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
    rw [← h2, ← h1]
    exact h3.mul_right _
  have hE9 : Nat.card (S'.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hS'9]
  have hEY : S'.map ψ.toMonoidHom ≤ Subgroup.normalizer ((Y'.map ψ.toMonoidHom : Subgroup _) :
      Set _) :=
    (Subgroup.map_mono hSY').trans (Subgroup.le_normalizer_map _)
  have hY''3 : ¬ 3 ∣ Nat.card (Y'.map ψ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective ψ.injective]
  have hbot := KFacts.L34.eq_bot_of_le_normalizer KFacts.L34.card_galoisField_two_two hE9 hY''3
    hEY
  rw [Subgroup.map_eq_bot_iff_of_injective _ ψ.injective, hY', Subgroup.map_eq_bot_iff,
    hπ, QuotientGroup.ker_mk'] at hbot
  intro y hy
  exact ⟨⟨y, hYL hy⟩, hbot (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem theta_eq_pCoreOf_of_quot {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hq : letI := kerAO2_normal hD.le_normalizer
      Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃*
        Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))) :
    inSubgroup (aschbacherSolvableCore 3) L = CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨χ⟩, h9⟩ := Proof1510.facts_l34_of_quot hD hq
  let _ := kerAO2_normal hD.le_normalizer
  obtain ⟨φ⟩ := hq
  have hP2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥L) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hP3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥L) := hP2.isNilpotent
  have hle : CFSG.Open.pCore 2 ↥L ≤ aschbacherSolvableCore 3 ↥L :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.2.1 _
      (CFSG.LieType.BorelTits.pCore_normal 2) inferInstance hP3
  have hL : Nat.card L = 20160 * Nat.card (aschbacherSolvableCore 3 ↥L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L),
      Nat.card_congr χ.toEquiv, KFacts.KS14.card_projSL_three_four]
  have hN : Nat.card (A ⊔ L : Subgroup G) = 3 * 20160 * Nat.card (CFSG.Open.pCore 2 ↥L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (kerAO2 A L),
      Nat.card_congr φ.toEquiv, Nat.card_prod, KFacts.KS14.card_projSL_three_four,
      Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]
    congr 1
    have hle' : CFSG.Open.pCoreOf 2 L ≤ A ⊔ L :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_right
    rw [kerAO2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv]
    exact Subgroup.card_map_of_injective L.subtype_injective
  have hsup := Sec6.card_sup_mul_card_inf hD.le_normalizer
  rw [h9, hD.card_eq, hN, hL] at hsup
  have hcard : Nat.card (aschbacherSolvableCore 3 ↥L) ≤ Nat.card (CFSG.Open.pCore 2 ↥L) := by
    omega
  have heq : CFSG.Open.pCore 2 ↥L = aschbacherSolvableCore 3 ↥L :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [CFSG.Open.pCoreOf, heq]
  rfl

theorem inf_eq_of_isPGroup {L S P : Subgroup G} (hSL : S ≤ L) (hS9 : Nat.card S = 9)
    (χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) {b : G} (hbS : b ∈ S)
    (hb1 : b ≠ 1) (hP : IsPGroup 3 P) (hSP : S ≤ P)
    (hPb : P ≤ Subgroup.centralizer ({b} : Set G)) : P ⊓ L = S := by
  refine le_antisymm (fun z hz => ?_) (le_inf hSP hSL)
  have hz' := inf_centralizer_le_sup_theta hSL hS9 χ hbS hb1 ⟨hz.2, hPb hz.1⟩
  have hθN : S ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    hSL.trans (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S _ hθN] at hz'
  obtain ⟨s, hs, t, ht, rfl⟩ := hz'
  have htP : t ∈ P := by
    have := P.mul_mem (P.inv_mem (hSP hs)) hz.1
    simpa using this
  have ht1 : t ∈ P ⊓ inSubgroup (aschbacherSolvableCore 3) L := ⟨htP, ht⟩
  rw [inf_eq_bot_of_coprime hP (not_three_dvd_card_theta L), Subgroup.mem_bot] at ht1
  rw [ht1]
  simpa using hs

end CFSG.RankThree.PartTwo.Sec15.Proof1510Steps
