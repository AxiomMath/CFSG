module

import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof15Res7

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem le_delta_of_map_eq_centralizer
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L)
    (hdc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)})
    {Z : Subgroup G} (hZL : Z ≤ L) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZ : (Z.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    Z ≤ delta A (lB A) Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hθ2 : IsPGroup 2 θ := Proof152Gen.isPGroup_theta_of_j2 h hJ
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hθ2
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  obtain ⟨-, hAL9, hAc⟩ := j2_point_facts hD hJ
  have hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G) := by
    intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))
  set H := delta A (lB A) Z with hHdef
  have hHZ : H ≤ Z := delta_le Z
  have hLN : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hLc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hmem : ∀ R : Subgroup G, R ≤ Z → IsPGroup 2 R → A ≤ Subgroup.normalizer (R : Set G) →
      R ≤ H := by
    intro R hRZ hR2 hAR
    have hR3 : ¬ 3 ∣ Nat.card R := by
      intro h3
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
      rw [hn] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    exact le_delta (mem_scriptQ_of_hj_point h hJ ⟨(hRZ.trans hZL).trans hLN,
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩).1 hRZ
  have hθH : Z ⊓ inSubgroup (aschbacherSolvableCore 3) L ≤ H :=
    hmem _ inf_le_left ((hθ2.map L.subtype).to_le inf_le_right)
      (Late.le_normalizer_inf hAZ (hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L)))
  set H₀ := (H.subgroupOf L).map π with hH₀
  set z : ↥L ⧸ θ := π ⟨d, hdL⟩ with hz
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem' : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem'⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem'⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    obtain ⟨S3, hdS3, hS3d⟩ := hdc
    refine ⟨S3.mapSurjective hπs, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  set C := Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) with hC
  have hlift : ∀ W : Subgroup (↥L ⧸ θ), IsPGroup 2 W → W ≤ C →
      (A.subgroupOf L).map π ≤ Subgroup.normalizer (W : Set (↥L ⧸ θ)) → W ≤ H₀ := by
    intro W hW2 hWC hWA
    set R := Z ⊓ (W.comap π).map L.subtype with hR
    have hR2 : IsPGroup 2 R := (isPGroup_map_comap π hW2 hker).to_le inf_le_right
    have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
      Late.le_normalizer_inf hAZ
        (hAinv _ (Subgroup.map_subtype_le _) (inf_le_normalizer_map_comap π hWA))
    have hRH := hmem R inf_le_left hR2 hAR
    intro w hw
    have hwZ : w ∈ (Z.subgroupOf L).map π := by
      rw [hZ]
      exact hWC hw
    obtain ⟨y, hy, rfl⟩ := hwZ
    exact ⟨y, Subgroup.mem_subgroupOf.mpr
      (hRH ⟨Subgroup.mem_subgroupOf.mp hy, ⟨y, hw, rfl⟩⟩), rfl⟩
  obtain ⟨hZc, hZ3, hZn, ⟨eA⟩⟩ := KFacts.KS14.Native.j2_centralizer_quotient hJ hz1 hzc
  have hZC := KFacts.KS14.Native.j2_center_centralizer hJ hz1 hzc
  have hCp := KFacts.KS14.Native.j2_centralizer_isPerfect hJ hz1 hzc
  set Zc := (Subgroup.zpowers z).subgroupOf C with hZcdef
  set Abar := (A.subgroupOf L).map π with hAbar
  have hAbarC : Abar ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, hz, ← map_mul, ← map_mul]
    have hcomm : (a : G) * d = d * (a : G) := congrArg Subtype.val
      (hA.1.1.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ ⟨d, hdA⟩)
    have hcomm' : a * ⟨d, hdL⟩ = ⟨d, hdL⟩ * a := Subtype.ext hcomm
    rw [hcomm']
  set B := Abar.subgroupOf C with hB
  have hzAbar : z ∈ Abar := ⟨⟨d, hdL⟩, Subgroup.mem_subgroupOf.mpr hdA, rfl⟩
  have hZB : Zc ≤ B := by
    intro x hx
    rw [hB, Subgroup.mem_subgroupOf]
    rw [hZcdef, Subgroup.mem_subgroupOf] at hx
    exact (Subgroup.zpowers_le.mpr hzAbar) hx
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := by
    intro b hb
    rw [hB, Subgroup.mem_subgroupOf] at hb
    obtain ⟨a, ha, hab⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hab, ← map_pow]
    have ha3 : (a : ↥L) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA.1.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [ha3, map_one]
  have hB9 : Nat.card B ≤ 9 := by
    have h1 : Nat.card B = Nat.card Abar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAbarC).toEquiv
    rw [h1, hAbar, card_map_mk_subgroupOf hA.1, hAL9]
  have hCH : C ≤ H₀ := by
    have htop := Proof155w.eq_top_of_invariant_two_of_cover (C := ↥C) hCp Zc hZC hZ3 eA hZB hB3
      hB9 (H := H₀.subgroupOf C) (fun R hR2 hBR => by
        intro r hr
        rw [Subgroup.mem_subgroupOf]
        refine hlift (R.map C.subtype) (hR2.map C.subtype) (Subgroup.map_subtype_le R) ?_
          ⟨r, hr, rfl⟩
        rintro _ ⟨a, ha, rfl⟩
        have haC : π a ∈ C := hAbarC ⟨a, ha, rfl⟩
        have haB : (⟨π a, haC⟩ : ↥C) ∈ B := by
          rw [hB, Subgroup.mem_subgroupOf]
          exact ⟨a, ha, rfl⟩
        exact Subgroup.le_normalizer_map C.subtype ⟨⟨π a, haC⟩, hBR haB, rfl⟩)
    intro x hx
    have : (⟨x, hx⟩ : ↥C) ∈ H₀.subgroupOf C := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  intro x hx
  have hπx : π ⟨x, hZL hx⟩ ∈ H₀ := by
    apply hCH
    rw [← hZ]
    exact ⟨⟨x, hZL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨j, hj, hjx⟩ := hπx
  have hjθ : j⁻¹ * ⟨x, hZL hx⟩ ∈ θ := by
    rw [← QuotientGroup.eq]
    exact hjx
  have hjH : (j : G) ∈ H := Subgroup.mem_subgroupOf.mp hj
  have hjZ : ((j⁻¹ * ⟨x, hZL hx⟩ : ↥L) : G) ∈ Z := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Z.mul_mem (Z.inv_mem (hHZ hjH)) hx
  have h1 : ((j⁻¹ * ⟨x, hZL hx⟩ : ↥L) : G) ∈ H := hθH ⟨hjZ, ⟨_, hjθ, rfl⟩⟩
  have h3 : x = (j : G) * ((j⁻¹ * ⟨x, hZL hx⟩ : ↥L) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h3]
  exact H.mul_mem hjH h1

end CFSG.RankThree.PartTwo.Sec15.Proof15Res7
