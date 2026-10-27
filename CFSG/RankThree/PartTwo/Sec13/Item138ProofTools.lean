module

import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item138Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

section Theta

theorem inf_theta_eq_bot {X : Subgroup G} (hX : IsPGroup 3 X) (L : Subgroup G) :
    X ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (Sec6.theta_solvable_and_not_dvd L).2)

omit [Finite G] in
theorem mem_theta_iff {L : Subgroup G} (y : L) :
    y ∈ aschbacherSolvableCore 3 L ↔ (y : G) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
  (Subgroup.mem_map_iff_mem L.subtype_injective).symm

omit [Finite G] in
theorem mk_eq_mk_iff {L : Subgroup G} (y z : L) :
    (y : L ⧸ aschbacherSolvableCore 3 L) = (z : L ⧸ aschbacherSolvableCore 3 L) ↔
      (y : G)⁻¹ * z ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [QuotientGroup.eq, mem_theta_iff]
  rfl

omit [Finite G] in
theorem conj_mem_theta {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    l * t * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
  (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hl) t).mp ht

theorem conj_mem_theta_of_normalizer {L : Subgroup G} {x t : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (ht : t ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    x * t * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
  (Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_theta L hx) t).mp ht

omit [Finite G] in
theorem mul_inv_mem_theta_of_inv_mul_mem {L : Subgroup G} {y z : G} (hy : y ∈ L)
    (h : y⁻¹ * z ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    z * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have := conj_mem_theta hy h
  rwa [show y * (y⁻¹ * z) * y⁻¹ = z * y⁻¹ by group] at this

omit [Finite G] in
theorem inv_mul_mem_theta_of_mul_inv_mem {L : Subgroup G} {y z : G} (hy : y ∈ L)
    (h : z * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    y⁻¹ * z ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have := conj_mem_theta (inv_mem hy) h
  rwa [show y⁻¹ * (z * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * z by group] at this

end Theta

section Frattini

variable {L E : Subgroup G}

theorem mem_normalizer_of_map_le {H : Subgroup G} {w : G}
    (h : H.map (MulAut.conj w).toMonoidHom ≤ H) : w ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])

theorem isSylowOf_sup_theta (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hE3 : IsPGroup 3 E) :
    CFSG.ABGLocalTools.IsSylowOf 3 E (E ⊔ inSubgroup (aschbacherSolvableCore 3) L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θG := inSubgroup (aschbacherSolvableCore 3) L
  have hEθ : E ≤ Subgroup.normalizer (θG : Set G) :=
    hEN.trans (Sec6.normalizer_le_normalizer_theta L)
  have hcard : Nat.card (E ⊔ θG : Subgroup G) = Nat.card E * Nat.card θG := by
    have := Sec6.card_sup_mul_card_inf hEθ
    rwa [inf_theta_eq_bot hE3 L, Subgroup.card_bot, mul_one] at this
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_left, hE3, ?_⟩
  have h1 := Subgroup.relIndex_mul_card E (E ⊔ θG)
  rw [inf_eq_left.mpr (le_sup_left : E ≤ E ⊔ θG), hcard] at h1
  have hpos : 0 < Nat.card E := Nat.card_pos
  have h2 : E.relIndex (E ⊔ θG) = Nat.card θG := by
    rw [mul_comm (Nat.card E)] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  rw [h2]
  exact (Sec6.theta_solvable_and_not_dvd L).2

theorem exists_mem_normalizer_of_conj_mem (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hE3 : IsPGroup 3 E) {w : G} (hwL : w ∈ L)
    (hw : ∀ x ∈ E, w * x * w⁻¹ ∈ E ⊔ inSubgroup (aschbacherSolvableCore 3) L) :
    ∃ m ∈ L, m ∈ Subgroup.normalizer (E : Set G) ∧
      m * w⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  have hθL : θG ≤ L := Sec6.theta_le L
  have hEθ : E ≤ Subgroup.normalizer (θG : Set G) :=
    hEN.trans (Sec6.normalizer_le_normalizer_theta L)
  have hLθ : L ≤ Subgroup.normalizer (θG : Set G) := Sec6.le_normalizer_theta L
  have hwT : w ∈ Subgroup.normalizer ((E ⊔ θG : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      exact hw x hx
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_sup_right (conj_mem_theta hwL ht)
  obtain ⟨n, hnT, m, hmN, hwnm⟩ := Sec18.exists_mul_of_isSylowOf (isSylowOf_sup_theta hEN hE3)
    (K := Subgroup.zpowers w) (Subgroup.zpowers_le.mpr hwT) (Subgroup.mem_zpowers w)
  have hnT' : n ∈ ((E ⊔ θG : Subgroup G) : Set G) := hnT
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E θG hEθ] at hnT'
  obtain ⟨x, hx, t, ht, rfl⟩ := hnT'
  have hxt : x * t⁻¹ * x⁻¹ ∈ θG :=
    (Subgroup.mem_normalizer_iff.mp (hEθ hx) t⁻¹).mp (inv_mem ht)
  have hm : x * m = x * t⁻¹ * x⁻¹ * w := by rw [hwnm]; group
  refine ⟨x * m, ?_, mul_mem (Subgroup.le_normalizer hx) hmN, ?_⟩
  · rw [hm]
    exact mul_mem (hθL hxt) hwL
  · rw [hm, mul_inv_cancel_right]
    exact hxt

theorem conj_mem_sup_of_fixed (hEN : E ≤ Subgroup.normalizer (L : Set G)) (w : L)
    (hfix : ∀ (x : G) (hx : x ∈ E),
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩)
        (w : L ⧸ aschbacherSolvableCore 3 L) = (w : L ⧸ aschbacherSolvableCore 3 L)) :
    ∀ x ∈ E, (w : G) * x * (w : G)⁻¹ ∈ E ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  intro x hx
  have hx' : x⁻¹ ∈ E := inv_mem hx
  have h := hfix x⁻¹ hx'
  rw [Sec4.thetaQuotMulAut_mk, mk_eq_mk_iff, Sec4.normalizerMonoidHom_apply_coe] at h
  have hu := mul_inv_mem_theta_of_inv_mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hEN hx') (w : G)).mp w.2) h
  have heq : (w : G) * x * (w : G)⁻¹ = x * ((x⁻¹ * (w : G) * x⁻¹⁻¹) * (w : G)⁻¹) := by group
  have hu' : (x⁻¹ * (w : G) * x⁻¹⁻¹) * (w : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have := inv_mem hu
    rwa [mul_inv_rev, inv_inv] at this
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hu')

theorem exists_mem_of_fixed (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hE3 : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    {w : L ⧸ aschbacherSolvableCore 3 L} (hw3 : w ^ 3 = 1)
    (hfix : ∀ (x : G) (hx : x ∈ E),
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩) w = w) :
    ∃ n : L, (n : G) ∈ E ∧ (n : L ⧸ aschbacherSolvableCore 3 L) = w := by
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective w
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3.2 g g.2)⟩
  obtain ⟨m, hmL, hmN, hmw⟩ := exists_mem_normalizer_of_conj_mem hEN hEp w₀.2
    (conj_mem_sup_of_fixed hEN w₀ hfix)
  set M : Subgroup L := (Subgroup.normalizer (E : Set G)).comap L.subtype with hM
  have hmk : ((⟨m, hmL⟩ : L) : L ⧸ θ) = (w₀ : L ⧸ θ) := by
    rw [mk_eq_mk_iff]
    refine inv_mul_mem_theta_of_mul_inv_mem hmL ?_
    have := inv_mem hmw
    rwa [mul_inv_rev, inv_inv] at this
  have hB : IsPGroup 3 (Subgroup.zpowers (w₀ : L ⧸ θ)) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have hBM : Subgroup.zpowers (w₀ : L ⧸ θ) ≤ M.map (QuotientGroup.mk' θ) := by
    rw [Subgroup.zpowers_le]
    exact ⟨⟨m, hmL⟩, hmN, hmk⟩
  obtain ⟨S, -, hSM, hS3, hSB⟩ := exists_isPGroup_le_map_eq hB hBM IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  have hwS : (w₀ : L ⧸ θ) ∈ S.map (QuotientGroup.mk' θ) := by
    rw [hSB]
    exact Subgroup.mem_zpowers _
  obtain ⟨n, hnS, hnw⟩ := hwS
  have hnw' : (n : L ⧸ θ) = (w₀ : L ⧸ θ) := hnw
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  have hn3 : n ^ 3 = 1 :=
    hinj (S.pow_mem hnS 3) S.one_mem (by rw [map_pow, map_one]; exact hnw ▸ hw3)
  have hn3' : (n : G) ^ 3 = 1 := by
    have := congrArg (Subtype.val : L → G) hn3
    simpa using this
  have hnN : (n : G) ∈ Subgroup.normalizer (E : Set G) := hSM hnS
  have hcomm : ∀ x ∈ E, x * (n : G) = (n : G) * x := by
    intro x hx
    have h1 : x * (n : G) * x⁻¹ * (n : G)⁻¹ ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp hnN x⁻¹).mp (inv_mem hx)
      rw [show x * (n : G) * x⁻¹ * (n : G)⁻¹ = x * ((n : G) * x⁻¹ * (n : G)⁻¹) by group]
      exact mul_mem hx this
    have h2 : x * (n : G) * x⁻¹ * (n : G)⁻¹ ∈ θG := by
      have h := hfix x hx
      rw [← hnw', Sec4.thetaQuotMulAut_mk, mk_eq_mk_iff, Sec4.normalizerMonoidHom_apply_coe] at h
      refine mul_inv_mem_theta_of_inv_mul_mem n.2 ?_
      have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
    have h3 : x * (n : G) * x⁻¹ * (n : G)⁻¹ ∈ E ⊓ θG := ⟨h1, h2⟩
    rw [inf_theta_eq_bot hEp L, Subgroup.mem_bot] at h3
    calc x * (n : G) = x * (n : G) * x⁻¹ * (n : G)⁻¹ * ((n : G) * x) := by group
      _ = (n : G) * x := by rw [h3, one_mul]
  by_contra hnE
  have hnE' : (n : G) ∉ E := fun h => hnE ⟨n, h, hnw'⟩
  obtain ⟨hab, -⟩ := Sec5.isElemAbelian_sup_zpowers hE3 hnE' hn3' hcomm
  have heq := hEmax _ hab le_sup_left
  exact hnE' (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end Frattini

section Fusion

variable {H : Type*} [Group H] [Finite H]

theorem exists_conj_of_map_mk {S : Subgroup H} (hS : IsPGroup 3 S)
    (htr : ∀ x ∈ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)), x ≠ 1 →
      ∀ y ∈ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)), y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer
          ((S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) :
            Subgroup (H ⧸ aschbacherSolvableCore 3 H)) : Set (H ⧸ aschbacherSolvableCore 3 H)),
          n * x * n⁻¹ = y)
    {x y : H} (hx : x ∈ S) (hx1 : x ≠ 1) (hy : y ∈ S) (hy1 : y ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (S : Set H), n * x * n⁻¹ = y := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS
  have hne : ∀ z ∈ S, z ≠ 1 → π z ≠ 1 := fun z hz hz1 h =>
    hz1 (hinj hz S.one_mem (by rw [h, map_one]))
  obtain ⟨n, hn, hnxy⟩ := htr (π x) (Subgroup.mem_map_of_mem _ hx) (hne x hx hx1) (π y)
    (Subgroup.mem_map_of_mem _ hy) (hne y hy hy1)
  rw [normalizer_map_mk_eq hS] at hn
  obtain ⟨n', hn', rfl⟩ := hn
  refine ⟨n', hn', hinj ((Subgroup.mem_normalizer_iff.mp hn' x).mp hx) hy ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hnxy

end Fusion

end CFSG.RankThree.PartTwo.Sec13.Item138Proof
