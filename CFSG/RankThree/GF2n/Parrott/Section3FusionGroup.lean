module

public import Mathlib.GroupTheory.Transfer
public import CFSG.Quasithin.Background.A3Structure36BAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.DihedralInv

public section

namespace CFSG.RankThree.GF2n.Parrott

private lemma eq_of_normalizer_le {G : Type*} [Group G] [Finite G] {F P : Subgroup G}
    (hP : IsPGroup 2 P) (hFP : F ≤ P)
    (hN : ∀ g : G, g ∈ Subgroup.normalizer (F : Set G) → g ∈ F) : F = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hNC
  have hnorm : Subgroup.normalizer ((F.subgroupOf P : Subgroup ↥P) : Set ↥P) = F.subgroupOf P := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_subgroupOf]
    apply hN
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ P
    · have h2 := (Subgroup.mem_normalizer_iff.mp hx) (⟨g, hg⟩ : P)
      simpa [Subgroup.mem_subgroupOf] using h2
    · constructor
      · intro hgF
        exact absurd (hFP hgF) hg
      · intro hgF
        exfalso
        apply hg
        have h3 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ P :=
          P.mul_mem (P.mul_mem (P.inv_mem x.2) (hFP hgF)) x.2
        have e : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) = g := by group
        rwa [e] at h3
  have htop : F.subgroupOf P = ⊤ := hNC _ hnorm
  exact le_antisymm hFP (Subgroup.subgroupOf_eq_top.mp htop)

private lemma conj_pow_of_conj {G : Type*} [Group G] {x r : G}
    (h : x * r * x⁻¹ = r⁻¹) (n : ℕ) : x * r ^ n * x⁻¹ = (r⁻¹) ^ n := by
  have hxr : (MulAut.conj x) r = r⁻¹ := by
    rw [MulAut.conj_apply]
    exact h
  have h' := map_pow (MulAut.conj x) r n
  rw [hxr] at h'
  rwa [MulAut.conj_apply] at h'

private lemma conjNormal_eq_inv_of_disjoint_centralizer {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} [Q.Normal] {z : G} (hz : z * z = 1)
    (hdisj : Disjoint Q (Subgroup.centralizer ({z} : Set G))) (q : Q) :
    MulAut.conjNormal (H := Q) z q = q⁻¹ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hσ : ∀ x : Q,
      MulAut.conjNormal (H := Q) z (MulAut.conjNormal (H := Q) z x) = x := by
    intro x
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    rw [hzinv]
    calc z * (z * ↑x * z) * z = (z * z) * ↑x * (z * z) := by group
      _ = ↑x := by rw [hz, one_mul, mul_one]
  have hfix : ∀ x : Q, MulAut.conjNormal (H := Q) z x = x → x = 1 := by
    intro x hx
    have hxval : z * (x : G) * z⁻¹ = (x : G) := by
      have := congrArg Subtype.val hx
      simpa [MulAut.conjNormal_apply] using this
    rw [hzinv] at hxval
    have hxcomm : (x : G) * z = z * (x : G) := by
      have h1 : z * (x : G) * z = (x : G) := hxval
      have h1' : z * ((x : G) * z) = (x : G) := by rwa [mul_assoc] at h1
      have h2 : z * (z * ((x : G) * z)) = z * (x : G) := by rw [h1']
      rwa [← mul_assoc, hz, one_mul] at h2
    have hxR : (x : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxcomm
    have hxbot : (x : G) ∈ Q ⊓ Subgroup.centralizer ({z} : Set G) := ⟨x.2, hxR⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  exact (CFSG.Quasithin.A36B.eq_inv_of_fixedPointFree
    (MulAut.conjNormal (H := Q) z) hσ hfix).1 q

private lemma le_centralizer_mul_of_conjNormal_eq_inv {G : Type*} [Group G] {Q : Subgroup G}
    [Q.Normal] {z₁ z₂ : G} (hz₁ : z₁ * z₁ = 1) (hz₂ : z₂ * z₂ = 1)
    (h₁ : ∀ q : Q, MulAut.conjNormal (H := Q) z₁ q = q⁻¹)
    (h₂ : ∀ q : Q, MulAut.conjNormal (H := Q) z₂ q = q⁻¹) :
    Q ≤ Subgroup.centralizer ({z₁ * z₂} : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hq₁ : z₁ * q * z₁⁻¹ = q⁻¹ := by
    have := congrArg Subtype.val (h₁ ⟨q, hq⟩)
    simpa [MulAut.conjNormal_apply] using this
  have hq₂ : z₂ * q * z₂⁻¹ = q⁻¹ := by
    have := congrArg Subtype.val (h₂ ⟨q, hq⟩)
    simpa [MulAut.conjNormal_apply] using this
  have h₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁
  have h₂inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂
  have hq₁z : z₁ * q * z₁ = q⁻¹ := by simpa [h₁inv] using hq₁
  have hq₂z : z₂ * q * z₂ = q⁻¹ := by simpa [h₂inv] using hq₂
  have hqz₁ : q * z₁ = z₁ * q⁻¹ := by
    calc q * z₁ = (z₁ * z₁) * (q * z₁) := by rw [hz₁, one_mul]
      _ = z₁ * (z₁ * q * z₁) := by group
      _ = z₁ * q⁻¹ := by rw [hq₁z]
  have hq₂inv : z₂ * q⁻¹ * z₂ = q := by
    have := congrArg Inv.inv hq₂z
    simpa [mul_inv_rev, h₂inv, mul_assoc] using this
  have hqz₂ : q⁻¹ * z₂ = z₂ * q := by
    calc q⁻¹ * z₂ = (z₂ * z₂) * (q⁻¹ * z₂) := by rw [hz₂, one_mul]
      _ = z₂ * (z₂ * q⁻¹ * z₂) := by group
      _ = z₂ * q := by rw [hq₂inv]
  calc q * (z₁ * z₂) = (q * z₁) * z₂ := by group
    _ = (z₁ * q⁻¹) * z₂ := by rw [hqz₁]
    _ = z₁ * (q⁻¹ * z₂) := by group
    _ = z₁ * (z₂ * q) := by rw [hqz₂]
    _ = (z₁ * z₂) * q := by group

theorem eq_top_of_normalizer_le_of_isPGroup_centralizer {C : Type*} [Group C] [Finite C]
    {F : Subgroup C} (hF : IsPGroup 2 F) (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hN : ∀ g : C, g ∈ Subgroup.normalizer (F : Set C) → g ∈ F)
    {z₁ z₂ : C} (hz₁ : z₁ * z₁ = 1) (hz₂ : z₂ * z₂ = 1)
    (hC₁ : IsPGroup 2 (Subgroup.centralizer ({z₁} : Set C)))
    (hC₂ : IsPGroup 2 (Subgroup.centralizer ({z₂} : Set C)))
    (hC₁₂ : IsPGroup 2 (Subgroup.centralizer ({z₁ * z₂} : Set C))) :
    F = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hFP⟩ := hF.exists_le_sylow
  have hFP_eq : F = (P : Subgroup C) := eq_of_normalizer_le P.isPGroup' hFP hN
  have hnorm_eq : Subgroup.normalizer (P : Set C) = Subgroup.normalizer (F : Set C) :=
    congrArg (fun H : Subgroup C => Subgroup.normalizer (H : Set C)) hFP_eq.symm
  have hPN : Subgroup.normalizer (P : Set C) ≤ Subgroup.centralizer (P : Set C) := by
    intro g hg
    rw [hnorm_eq] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hgF : g ∈ F := hN g hg
    have hpF : p ∈ F := hFP_eq.symm ▸ hp
    exact (hFab g hgF p hpF).symm
  let Q : Subgroup C := (MonoidHom.transferSylow P hPN).ker
  have hQnormal : Q.Normal := MonoidHom.normal_ker (MonoidHom.transferSylow P hPN)
  have : Q.Normal := hQnormal
  have hcomp : Q.IsComplement' (P : Subgroup C) :=
    MonoidHom.ker_transferSylow_isComplement' P hPN
  have hdisj₁ : Disjoint Q (Subgroup.centralizer ({z₁} : Set C)) :=
    MonoidHom.ker_transferSylow_disjoint P hPN (Subgroup.centralizer ({z₁} : Set C)) hC₁
  have hdisj₂ : Disjoint Q (Subgroup.centralizer ({z₂} : Set C)) :=
    MonoidHom.ker_transferSylow_disjoint P hPN (Subgroup.centralizer ({z₂} : Set C)) hC₂
  have hdisj₁₂ : Disjoint Q (Subgroup.centralizer ({z₁ * z₂} : Set C)) :=
    MonoidHom.ker_transferSylow_disjoint P hPN
      (Subgroup.centralizer ({z₁ * z₂} : Set C)) hC₁₂
  have hinv₁ : ∀ q : Q, MulAut.conjNormal (H := Q) z₁ q = q⁻¹ :=
    fun q => conjNormal_eq_inv_of_disjoint_centralizer hz₁ hdisj₁ q
  have hinv₂ : ∀ q : Q, MulAut.conjNormal (H := Q) z₂ q = q⁻¹ :=
    fun q => conjNormal_eq_inv_of_disjoint_centralizer hz₂ hdisj₂ q
  have hQle : Q ≤ Subgroup.centralizer ({z₁ * z₂} : Set C) :=
    le_centralizer_mul_of_conjNormal_eq_inv hz₁ hz₂ hinv₁ hinv₂
  have hQbot : Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hq' : q ∈ Q ⊓ Subgroup.centralizer ({z₁ * z₂} : Set C) := ⟨hq, hQle hq⟩
    rw [hdisj₁₂.eq_bot, Subgroup.mem_bot] at hq'
    exact hq'
  have hsup : Q ⊔ (P : Subgroup C) = ⊤ := hcomp.sup_eq_top
  rw [hQbot, bot_sup_eq] at hsup
  rw [hFP_eq]
  exact hsup

theorem exists_commute_of_not_isConj {G : Type*} [Group G] [Finite G] {x z : G}
    (hx : x * x = 1) (hz : z * z = 1) (hxz : ¬ IsConj x z) :
    ∃ w : G, w * w = 1 ∧ w ≠ 1 ∧ x * w = w * x ∧ z * w = w * z := by
  have hx2 : x ^ 2 = 1 := by simpa [pow_two] using hx
  have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hz
  have hnotodd : ¬ Odd (orderOf (x * z)) := fun hodd =>
    hxz (CFSG.EvenSporadicStandard.HNRecog.Section3.isConj_of_odd_orderOf_mul hx2 hz2 hodd)
  have heven : Even (orderOf (x * z)) := Nat.not_odd_iff_even.mp hnotodd
  obtain ⟨n, hn⟩ := heven
  have hpos : 0 < orderOf (x * z) := orderOf_pos _
  have hnpos : 0 < n := by omega
  have hnlt : n < orderOf (x * z) := by omega
  have hn2 : orderOf (x * z) = 2 * n := by rw [hn, two_mul]
  have hww : (x * z) ^ n * (x * z) ^ n = 1 := by
    rw [← pow_add, ← two_mul, ← hn2, pow_orderOf_eq_one]
  have hwne : (x * z) ^ n ≠ 1 := pow_ne_one_of_lt_orderOf hnpos.ne' hnlt
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hxr : x * (x * z) * x⁻¹ = (x * z)⁻¹ := by
    rw [mul_inv_rev, hxinv, hzinv]
    calc x * (x * z) * x = (x * x) * z * x := by rw [mul_assoc x x z]
      _ = z * x := by rw [hx, one_mul]
  have hzr : z * (x * z) * z⁻¹ = (x * z)⁻¹ := by
    rw [mul_inv_rev, hxinv, hzinv]
    calc z * (x * z) * z = z * x * (z * z) := by group
      _ = z * x := by rw [hz, mul_one]
  have hxw : x * (x * z) ^ n * x⁻¹ = (x * z) ^ n := by
    have h1 := conj_pow_of_conj hxr n
    rw [h1, inv_pow]
    exact inv_eq_of_mul_eq_one_right hww
  have hzw : z * (x * z) ^ n * z⁻¹ = (x * z) ^ n := by
    have h1 := conj_pow_of_conj hzr n
    rw [h1, inv_pow]
    exact inv_eq_of_mul_eq_one_right hww
  refine ⟨(x * z) ^ n, hww, hwne, ?_, ?_⟩
  · calc x * (x * z) ^ n = (x * (x * z) ^ n * x⁻¹) * x := by group
      _ = (x * z) ^ n * x := by rw [hxw]
  · calc z * (x * z) ^ n = (z * (x * z) ^ n * z⁻¹) * z := by group
      _ = (x * z) ^ n * z := by rw [hzw]

end CFSG.RankThree.GF2n.Parrott
