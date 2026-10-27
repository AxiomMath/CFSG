module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Step
import CFSG.Mathlib.GroupTheory.BurnsideNormalizerPPrimeCore
import CFSG.Walter.J1.Fusion
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

open scoped commutatorElement

private lemma commute_b0_b2 {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) : Commute b₀ (B.b 2) := by
  rw [← hB.2.1]
  exact B.comm 0 2

private lemma commute_zpowers_sup {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) :
    ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ Subgroup.zpowers (B.b 2), Commute a b := by
  intro a ha b hb
  rw [Subgroup.mem_zpowers_iff] at ha hb
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  exact (commute_b0_b2 hB).zpow_zpow m n

private def Qsubgroup {G : Type} [Group G]
    (H J O : Subgroup G) (hO_le_H : O ≤ H) (hO_normal : (O.subgroupOf H).Normal) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ x ∈ J, ⁅g, x⁆ ∈ O}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    intro x hx
    simp
  mul_mem' := by
    rintro g h ⟨hgH, hgJ⟩ ⟨hhH, hhJ⟩
    refine ⟨H.mul_mem hgH hhH, fun x hx => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h1 : g * ⁅h, x⁆ * g⁻¹ ∈ O := by
      have hmem : (⟨g, hgH⟩ : H) * (⟨⁅h, x⁆, hO_le_H (hhJ x hx)⟩ : H) *
          (⟨g, hgH⟩ : H)⁻¹ ∈ O.subgroupOf H :=
        hO_normal.conj_mem _ (Subgroup.mem_subgroupOf.mpr (hhJ x hx)) _
      simpa using Subgroup.mem_subgroupOf.mp hmem
    exact O.mul_mem h1 (hgJ x hx)
  inv_mem' := by
    rintro g ⟨hgH, hgJ⟩
    refine ⟨H.inv_mem hgH, fun x hx => ?_⟩
    rw [commutatorElement_inv_left]
    have hmem : (⟨g, hgH⟩ : H)⁻¹ * (⟨⁅g, x⁆, hO_le_H (hgJ x hx)⟩ : H)⁻¹ *
        (⟨g, hgH⟩ : H) ∈ O.subgroupOf H := by
      simpa [inv_inv] using hO_normal.conj_mem (⟨⁅g, x⁆, hO_le_H (hgJ x hx)⟩ : H)⁻¹
        (Subgroup.mem_subgroupOf.mpr (O.inv_mem (hgJ x hx)))
        (⟨g, hgH⟩ : H)⁻¹
    simpa [commutatorElement_inv] using Subgroup.mem_subgroupOf.mp hmem

theorem mem_sup_of_commutator_mem_primeCore {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hnorm : ∀ g ∈ Subgroup.centralizer ({B.b 2} : Set G), ∀ x ∈ nineJ K (B.b 2),
      g * x * g⁻¹ ∈ nineJ K (B.b 2) ⊔ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    {g : G} (hg : g ∈ Subgroup.centralizer ({B.b 2} : Set G))
    (hgJ : ∀ x ∈ nineJ K (B.b 2),
      g * x * g⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G))) :
    g ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) ⊔ Subgroup.zpowers b₀ ⊔
      Subgroup.zpowers (B.b 2) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := Subgroup.centralizer ({B.b 2} : Set G)
  let J := nineJ K (B.b 2)
  let O := GLAPPrimeCoreOf 3 H
  let P := Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
  have hO_le_H : O ≤ H := Subgroup.map_subtype_le _
  have hO_normal : (O.subgroupOf H).Normal := gLAPPrimeCoreOf_normal 3 H
  have hJ_le_H : J ≤ H := by
    unfold J nineJ H
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hJ_le_K : J ≤ K := by
    unfold J nineJ
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hK_le_Cb0 : K ≤ Subgroup.centralizer ({b₀} : Set G) := by
    obtain ⟨-, hHyp, -⟩ := hstd
    exact hHyp.2.1
  have hb0H : b₀ ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (commute_b0_b2 hB).symm.eq
  have hb2H : B.b 2 ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  let Q : Subgroup G := Qsubgroup H J O hO_le_H hO_normal
  have hQ_le_H : Q ≤ H := fun g hg => hg.1
  have hQ_normal : (Q.subgroupOf H).Normal := by
    refine ⟨fun n hn c => ?_⟩
    have hnQ : (n : G) ∈ Q := Subgroup.mem_subgroupOf.mp hn
    rcases hnQ with ⟨hnH, hnJ⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨H.mul_mem (H.mul_mem c.2 hnH) (H.inv_mem c.2), fun x hx => ?_⟩
    have hcomm : ((c : G) * (n : G) * (c : G)⁻¹) * x * ((c : G) * (n : G) * (c : G)⁻¹)⁻¹ * x⁻¹ =
        (c : G) * ((n : G) * ((c⁻¹ : G) * x * (c : G)) * (n : G)⁻¹ *
          ((c⁻¹ : G) * x * (c : G))⁻¹) * (c : G)⁻¹ := by group
    change ((↑c : G) * (↑n : G) * (↑c : G)⁻¹) * x * ((↑c : G) * (↑n : G) * (↑c : G)⁻¹)⁻¹ *
      x⁻¹ ∈ O
    rw [hcomm]
    have hc_inv : (c⁻¹ : G) ∈ H := H.inv_mem c.2
    have hw : ((c⁻¹ : G) * x * (c : G)) ∈ J ⊔ O := by
      simpa using hnorm (c⁻¹ : G) hc_inv x hx
    have hcommO := commutator_mem_gLAPPrimeCoreOf_of_mem_sup hJ_le_H hnH hnJ hw
    have hmemH : (n : G) * ((c⁻¹ : G) * x * (c : G)) * (n : G)⁻¹ *
        ((c⁻¹ : G) * x * (c : G))⁻¹ ∈ H := by
      have h1 : ((c⁻¹ : G) * x * (c : G)) ∈ H := H.mul_mem (H.mul_mem hc_inv (hJ_le_H hx)) c.2
      exact H.mul_mem (H.mul_mem (H.mul_mem hnH h1) (H.inv_mem hnH)) (H.inv_mem h1)
    have hmem : (⟨c, c.2⟩ : H) * (⟨(n : G) * ((c⁻¹ : G) * x * (c : G)) * (n : G)⁻¹ *
        ((c⁻¹ : G) * x * (c : G))⁻¹, hmemH⟩ : H) * (⟨c, c.2⟩ : H)⁻¹ ∈ O.subgroupOf H :=
      hO_normal.conj_mem _ hcommO _
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hb0Q : b₀ ∈ Q := by
    refine ⟨hb0H, fun x hx => ?_⟩
    have hxK : x ∈ K := hJ_le_K hx
    have hxcb0 : x ∈ Subgroup.centralizer ({b₀} : Set G) := hK_le_Cb0 hxK
    have hcomm : b₀ * x = x * b₀ := (Subgroup.mem_centralizer_iff.mp hxcb0) b₀ (by simp)
    simp [commutatorElement_def, hcomm]
  have hb2Q : B.b 2 ∈ Q := by
    refine ⟨hb2H, fun x hx => ?_⟩
    have hxcb2 : x ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
      unfold J nineJ at hx
      exact (Subgroup.commutator_le_self _).trans inf_le_right hx
    have hcomm : B.b 2 * x = x * B.b 2 := (Subgroup.mem_centralizer_iff.mp hxcb2) (B.b 2) (by simp)
    simp [commutatorElement_def, hcomm]
  have hP_le_Q : P ≤ Q := by
    intro x hx
    rw [show P = Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) from rfl] at hx
    rcases (mem_sup_of_commute (commute_zpowers_sup hB)).mp hx with ⟨a, ha, b, hb, rfl⟩
    exact Q.mul_mem (Subgroup.zpowers_le_of_mem hb0Q ha) (Subgroup.zpowers_le_of_mem hb2Q hb)
  have hP_le_H : P ≤ H := by
    intro x hx
    rw [show P = Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) from rfl] at hx
    rcases (mem_sup_of_commute (commute_zpowers_sup hB)).mp hx with ⟨a, ha, b, hb, rfl⟩
    exact H.mul_mem (Subgroup.zpowers_le_of_mem hb0H ha) (Subgroup.zpowers_le_of_mem hb2H hb)
  have hNQ_le_CQ : Subgroup.normalizer (P : Set G) ⊓ Q ≤ Subgroup.centralizer (P : Set G) ⊓ Q := by
    intro y hy
    rcases Subgroup.mem_inf.mp hy with ⟨hyN, hyQ⟩
    rcases hyQ with ⟨hyH, hyJ⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨hyH, hyJ⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hb0P : b₀ ∈ P := Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
    have hyP : y * b₀ * y⁻¹ ∈ P := by
      rw [Subgroup.mem_normalizer_iff] at hyN
      exact (hyN b₀).mp hb0P
    obtain ⟨d, hdD, k, hdk⟩ := exists_eq_mul_zpow_of_conj_mem_sup hstd hB hrec hyH hyJ hyP
    rcases Subgroup.mem_inf.mp hdD with ⟨hdCb0, hdCK⟩
    have hd_b0 : Commute d b₀ := by
      have := (Subgroup.mem_centralizer_iff.mp hdCb0) b₀ (by simp)
      exact this.symm
    have hd_b2 : Commute d (B.b 2) := by
      have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
      have := (Subgroup.mem_centralizer_iff.mp hdCK) (B.b 2) hb2K
      exact this.symm
    have hy_b0 : Commute y b₀ := by
      rw [hdk]
      exact hd_b0.mul_left ((commute_b0_b2 hB).symm.zpow_left k)
    have hy_b2 : Commute y (B.b 2) := by
      rw [hdk]
      exact hd_b2.mul_left ((Commute.refl (B.b 2)).zpow_left k)
    rw [show P = Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) from rfl] at hp
    rcases (mem_sup_of_commute (commute_zpowers_sup hB)).mp hp with ⟨a, ha, b, hb, rfl⟩
    rw [Subgroup.mem_zpowers_iff] at ha hb
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨n, rfl⟩ := hb
    exact ((hy_b0.zpow_right m).mul_right (hy_b2.zpow_right n)).eq.symm
  have hb0_3 : IsPGroup 3 (Subgroup.zpowers b₀) := by
    have hord : orderOf b₀ = 3 := by
      obtain ⟨hord, -, -⟩ := hstd.2.1
      exact hord
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  have hb2_3 : IsPGroup 3 (Subgroup.zpowers (B.b 2)) := by
    have hord : orderOf (B.b 2) = 3 := B.ord 2
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  have hcomm_p : Subgroup.zpowers (B.b 2) ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    intro y hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [Subgroup.mem_zpowers_iff]
    have hc : Commute (B.b 2) b₀ := (commute_b0_b2 hB).symm
    exact ⟨m, by
      rw [hc.zpow_zpow k m |>.eq, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hP3 : IsPGroup 3 P := by
    rw [show P = Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) from rfl]
    exact IsPGroup.to_sup_of_normal_left' hb0_3 hb2_3 hcomm_p
  have hZp : IsPGroup 3 (P.subgroupOf H) := hP3.comap_subtype
  have hNp : ∀ g ∈ Q.subgroupOf H, (∃ k : ℕ, g ^ 3 ^ k = 1) →
      g ∈ Subgroup.normalizer (P.subgroupOf H) → g ∈ P.subgroupOf H := by
    intro g hgQ hpow hgN
    obtain ⟨k, hk⟩ := hpow
    obtain ⟨hgH, hgJ⟩ := Subgroup.mem_subgroupOf.mp hgQ
    have hgNG : (g : G) ∈ Subgroup.normalizer (P : Set G) := by
      have hmem : g ∈ (Subgroup.normalizer (P : Set G)).subgroupOf H := by
        rwa [Subgroup.subgroupOf_normalizer_eq hP_le_H]
      exact Subgroup.mem_subgroupOf.mp hmem
    have hgP : (g : G) * b₀ * (g : G)⁻¹ ∈ P := by
      rw [Subgroup.mem_normalizer_iff] at hgNG
      exact (hgNG b₀).mp (Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀))
    obtain ⟨d, hdD, m, hdm⟩ := exists_eq_mul_zpow_of_conj_mem_sup hstd hB hrec hgH hgJ hgP
    cases k with
    | zero =>
      have hg1 : g = 1 := by simpa using hk
      rw [hg1]
      exact Subgroup.one_mem _
    | succ n =>
      have hg_pow : (g : G) ^ 3 ^ (n + 1) = 1 := by simpa using congrArg Subtype.val hk
      have hd_b2 : Commute d (B.b 2) := by
        have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
        have hdCK : d ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hdD).2
        exact ((Subgroup.mem_centralizer_iff.mp hdCK) (B.b 2) hb2K).symm
      have hd_pow : d ^ 3 ^ (n + 1) = 1 := by
        have hb2_pow : (B.b 2 ^ m) ^ 3 ^ (n + 1) = 1 := by
          have hb2_ord : orderOf (B.b 2) = 3 := B.ord 2
          have h3 : B.b 2 ^ 3 = 1 := by
            rw [← orderOf_dvd_iff_pow_eq_one, hb2_ord]
          have hm : (B.b 2 ^ m) ^ 3 = 1 := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
          rw [pow_succ, mul_comm, pow_mul, hm, one_pow]
        have hcomm : Commute d (B.b 2 ^ m) := hd_b2.zpow_right m
        have h := congrArg (fun x => x * (B.b 2 ^ m) ^ (-(3 ^ (n + 1) : ℤ))) hg_pow
        simp only [one_mul] at h
        rw [hdm, hcomm.mul_pow, hb2_pow, mul_one] at h
        have h' := congrArg (fun x => x * ((B.b 2 ^ m) ^ (-(3 ^ (n + 1) : ℤ)))⁻¹) h
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using h'
      have hd_zpowers : d ∈ Subgroup.zpowers b₀ :=
        mem_zpowers_of_mem_inf_centralizer_of_pow_eq_one hstd hB hrec hfus hdD hd_pow
      rw [Subgroup.mem_subgroupOf]
      rw [hdm]
      rw [show P = Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) from rfl]
      exact Subgroup.mul_mem_sup hd_zpowers
        (Subgroup.zpow_mem (Subgroup.zpowers (B.b 2)) (Subgroup.mem_zpowers (B.b 2)) m)
  have hPH_le_QH : P.subgroupOf H ≤ Q.subgroupOf H := by
    intro x hx
    exact hP_le_Q hx
  have hSylow : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf H) (Q.subgroupOf H) := by
    refine ⟨CFSG.Walter.J1.sylowOfNormalizer
      ((P.subgroupOf H).subgroupOf (Q.subgroupOf H)) ?_ ?_, ?_⟩
    · exact hZp.comap_subtype
    · intro g hg hpow
      have hgH : (g : ↥H) ∈ Subgroup.normalizer (P.subgroupOf H : Set ↥H) := by
        have hmem : g ∈ (Subgroup.normalizer (P.subgroupOf H : Set ↥H)).subgroupOf
            (Q.subgroupOf H) := by
          rwa [Subgroup.subgroupOf_normalizer_eq hPH_le_QH]
        exact Subgroup.mem_subgroupOf.mp hmem
      have hpowH : ∃ k : ℕ, (g : ↥H) ^ 3 ^ k = 1 := by
        obtain ⟨k, hk⟩ := hpow
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      exact Subgroup.mem_subgroupOf.mpr (hNp (g : ↥H) g.2 hpowH hgH)
    · change ((P.subgroupOf H).subgroupOf (Q.subgroupOf H)).map
          (Q.subgroupOf H).subtype = P.subgroupOf H
      rw [Subgroup.map_subgroupOf_eq_of_le hPH_le_QH]
  have hNC : Subgroup.normalizer (P.subgroupOf H : Set ↥H) ⊓ (Q.subgroupOf H) ≤
      Subgroup.centralizer (P.subgroupOf H : Set ↥H) := by
    intro y hy
    rcases Subgroup.mem_inf.mp hy with ⟨hyN, hyQ⟩
    have hyG : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
      have hmem : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf H := by
        rw [Subgroup.subgroupOf_normalizer_eq hP_le_H]
        exact hyN
      exact Subgroup.mem_subgroupOf.mp hmem
    have hmem : (y : G) ∈ Subgroup.centralizer (P : Set G) ⊓ Q :=
      hNQ_le_CQ (Subgroup.mem_inf.mpr ⟨hyG, hyQ⟩)
    have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hmem).1
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    apply Subtype.ext
    exact hyC (z : G) (Subgroup.mem_subgroupOf.mp hz)
  have hN_le : Q.subgroupOf H ≤ CFSG.pPrimeCore 3 H ⊔ P.subgroupOf H := by
    simpa [sup_comm] using
      CFSG.GroupTheory.le_sup_pPrimeCore_of_isSylowOf_normalizer_le_centralizer hSylow hNC
  have hgQ : g ∈ Q := ⟨hg, hgJ⟩
  have hgH : g ∈ H := hg
  have hmem_sub : (⟨g, hgH⟩ : H) ∈ Q.subgroupOf H := hgQ
  have hmem_sup : (⟨g, hgH⟩ : H) ∈ CFSG.pPrimeCore 3 H ⊔ P.subgroupOf H := hN_le hmem_sub
  have hmap : g ∈ GLAPPrimeCoreOf 3 H ⊔ P := by
    have h : g ∈ (CFSG.pPrimeCore 3 H ⊔ P.subgroupOf H).map H.subtype :=
      Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, hmem_sup, rfl⟩
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP_le_H] at h
  rw [sup_assoc]
  exact hmap

end CFSG.StandardType.FrameRoute.FS81

end
