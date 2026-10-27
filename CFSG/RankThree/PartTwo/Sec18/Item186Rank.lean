module

public import CFSG.RankThree.PartTwo.Notation
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item186Proof

variable {G : Type} [Group G] [Finite G]

theorem four_le_localRank_of_pair {M K J F F' : Subgroup G}
    (hQ : CFSG.Open.pCoreOf 2 M ≠ ⊥)
    (hK : K ∈ oTwoComponentsIn M) (hJ : J ∈ oTwoComponentsIn M) (hJK : J ≠ K)
    (hFK : F ≤ K) (hFe : ∀ f ∈ F, f ^ 3 = 1) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f)
    (hF9 : 9 ≤ Nat.card F)
    (hF'J : F' ≤ J) (hF'e : ∀ f ∈ F', f ^ 3 = 1) (hF'c : ∀ f ∈ F', ∀ f' ∈ F', f * f' = f' * f)
    (hF'9 : 9 ≤ Nat.card F')
    (hF'f : ∀ f ∈ F', (∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → f = 1) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM := le_of_mem_oTwoComponentsIn hK
  have hJM := le_of_mem_oTwoComponentsIn hJ
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set N := CFSG.pCore 2 M with hN
  set π := QuotientGroup.mk' N with hπ
  have hmemN : ∀ m : M, m ∈ N ↔ (m : G) ∈ Q := fun m => (CFSG.mem_openPCoreOf_iff m).symm
  have hπ1 : ∀ m : M, π m = 1 ↔ (m : G) ∈ Q := fun m => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemN]
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  set Fs := (F.subgroupOf M).map π with hFs
  set F's := (F'.subgroupOf M).map π with hF's
  set Js := (J.subgroupOf M).map π with hJs
  have hcommKJ : ∀ y ∈ Fs, ∀ z ∈ Js, y * z = z * y := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨j, hj, rfl⟩
    exact (Sec19.Step1910Proof.mk_mul_comm_of_ne hJ hK hJK (Subgroup.mem_subgroupOf.mp hj)
      (hFK (Subgroup.mem_subgroupOf.mp hf))).symm
  have hF'sJ : F's ≤ Js := Subgroup.map_mono fun f hf =>
    Subgroup.mem_subgroupOf.mpr (hF'J (Subgroup.mem_subgroupOf.mp hf))
  have hcomm : ∀ y ∈ Fs, ∀ z ∈ F's, y * z = z * y := fun y hy z hz =>
    hcommKJ y hy z (hF'sJ hz)
  have hinf : Fs ⊓ F's = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hvF, f, hf, rfl⟩
    rw [Subgroup.mem_bot]
    have hf1 : (f : G) = 1 := by
      refine hF'f _ (Subgroup.mem_subgroupOf.mp hf) fun j hj => ?_
      have hjM : j ∈ M := hJM hj
      have h2 : π (f * ⟨j, hjM⟩ * f⁻¹ * (⟨j, hjM⟩ : M)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          hcommKJ _ hvF (π ⟨j, hjM⟩) ⟨⟨j, hjM⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩]
        group
      exact (hπ1 _).mp h2
    rw [show f = 1 from Subtype.ext hf1, map_one]
  have hFM : F ≤ M := hFK.trans hKM
  have hF'M : F' ≤ M := hF'J.trans hJM
  have hF3 : IsPGroup 3 (F.subgroupOf M) := by
    refine IsPGroup.comap_subtype ?_
    exact fun f => ⟨1, Subtype.ext (by simpa using hFe f f.2)⟩
  have hF'3 : IsPGroup 3 (F'.subgroupOf M) := by
    refine IsPGroup.comap_subtype ?_
    exact fun f => ⟨1, Subtype.ext (by simpa using hF'e f f.2)⟩
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  have hcardmap : ∀ S : Subgroup M, IsPGroup 3 S → Nat.card (S.map π) = Nat.card S :=
    fun S hS => by
      obtain ⟨e⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image 3
        Nat.prime_three π hker S hS
      exact (Nat.card_congr e.toEquiv).symm
  have hFscard : Nat.card Fs = Nat.card F := by
    rw [hFs, hcardmap _ hF3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv]
  have hF'scard : Nat.card F's = Nat.card F' := by
    rw [hF's, hcardmap _ hF'3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'M).toEquiv]
  set V := Fs ⊔ F's with hV
  have hVcard : Nat.card V = Nat.card F * Nat.card F' := by
    have h1 := Sec3.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, hFscard, hF'scard] at h1
    exact h1
  have hFF : ∀ a ∈ Fs, ∀ b ∈ Fs, a * b = b * a := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hFc _ (Subgroup.mem_subgroupOf.mp hf) _ (Subgroup.mem_subgroupOf.mp hf'))
  have hF'F' : ∀ a ∈ F's, ∀ b ∈ F's, a * b = b * a := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hF'c _ (Subgroup.mem_subgroupOf.mp hf) _ (Subgroup.mem_subgroupOf.mp hf'))
  have hVcl : V = Subgroup.closure ((Fs : Set (M ⧸ N)) ∪ (F's : Set (M ⧸ N))) := by
    rw [hV, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    have hT : ∀ a ∈ ((Fs : Set (M ⧸ N)) ∪ (F's : Set (M ⧸ N))),
        ∀ b ∈ ((Fs : Set (M ⧸ N)) ∪ (F's : Set (M ⧸ N))), a * b = b * a := by
      intro a ha b hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hFF a ha b hb
      · exact hcomm a ha b hb
      · exact (hcomm b hb a ha).symm
      · exact hF'F' a ha b hb
    intro a ha b hb
    rw [hVcl] at ha hb
    exact KFacts.KS14.commute_of_mem_closure hT ha hb
  have hVe : ∀ v ∈ V, v ^ 3 = 1 := by
    intro v hv
    have hv' := hv
    rw [hVcl] at hv'
    induction hv' using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
      · rw [← map_pow]
        exact (hπ1 _).mpr (by
          have := hFe _ (Subgroup.mem_subgroupOf.mp hf)
          rw [show ((f ^ 3 : M) : G) = (f : G) ^ 3 from rfl, this]
          exact Q.one_mem)
      · rw [← map_pow]
        exact (hπ1 _).mpr (by
          have := hF'e _ (Subgroup.mem_subgroupOf.mp hf)
          rw [show ((f ^ 3 : M) : G) = (f : G) ^ 3 from rfl, this]
          exact Q.one_mem)
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hVcomm a (hVcl ▸ ha) b (hVcl ▸ hb)) 3), iha (hVcl ▸ ha),
        ihb (hVcl ▸ hb), one_mul]
    | inv a ha iha => rw [inv_pow, iha (hVcl ▸ ha), inv_one]
  have hV3 : IsPGroup 3 V := fun v => ⟨1, Subtype.ext (by simpa using hVe v v.2)⟩
  obtain ⟨R, hR3, ⟨eR⟩⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three π (QuotientGroup.mk'_surjective N) hker V hV3
  have hRcomm : ∀ a b : R, a * b = b * a := fun a b => eR.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (hVcomm _ (eR a).2 _ (eR b).2))
  have hRe : ∀ a : R, a ^ 3 = 1 := fun a => eR.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hVe _ (eR a).2))
  obtain ⟨r, hr⟩ := hR3.exists_card_eq
  have hr4 : 4 ≤ r := by
    have h81 : 81 ≤ 3 ^ r := by
      rw [← hr, Nat.card_congr eR.toEquiv, hVcard]
      exact le_trans (by norm_num) (Nat.mul_le_mul hF9 hF'9)
    by_contra h
    push Not at h
    interval_cases r <;> norm_num at h81
  obtain ⟨R₄, hR₄⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 4) (G := R)
    (by rw [hr]; exact pow_dvd_pow 3 hr4)
  set X₄ := (R₄.map R.subtype).map M.subtype with hX₄
  have hX₄card : Nat.card X₄ = 3 ^ 4 := by
    rw [hX₄, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective R.subtype_injective, hR₄]
  have hX₄mem : ∀ a ∈ X₄, ∃ a' : R, (((a' : M) : G)) = a := by
    rintro _ ⟨_, ⟨a', -, rfl⟩, rfl⟩
    exact ⟨a', rfl⟩
  have hX₄c : IsMulCommutative X₄ := ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨a', ha'⟩ := hX₄mem a a.2
    obtain ⟨b', hb'⟩ := hX₄mem b b.2
    change (a : G) * b = b * a
    rw [← ha', ← hb']
    exact congrArg (fun z : R => ((z : M) : G)) (hRcomm a' b'))⟩⟩
  have hX₄e : ∀ a ∈ X₄, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨a', ha'⟩ := hX₄mem a ha
    rw [← ha']
    exact congrArg (fun z : R => ((z : M) : G)) (hRe a')
  have hX₄N : X₄ ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.map_subtype_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact Theta.le_localRank_of_le_normalizer (by norm_num) hQ
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hX₄c hX₄e hX₄card hX₄N

end Item186Proof

end CFSG.RankThree.PartTwo.Sec18
