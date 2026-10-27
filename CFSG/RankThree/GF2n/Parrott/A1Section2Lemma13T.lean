module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13V
public import CFSG.GroupTheory.ExtraspecialInvolutionIndexTwo
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Algebra

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem alpha2_mul_sigma1 : alpha2 * sigma1 = sigma1 * alpha2 := by
  decide +kernel

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem mem_zpowers_of_mem_J0_of_commute {a : G} (ha : a ∈ CJ z s1)
    (hc : ∀ b ∈ CJ z s1, a * b = b * a) : a ∈ zpowers z := by
  apply hy.mem_zpowers_of_commute_J ((CJ_le_J _) ha)
  intro j hj
  obtain ⟨b, hb, w, hw, rfl⟩ := hy.exists_mul_J0_W hj
  calc a * (b * w) = (a * b) * w := by group
    _ = (b * a) * w := by rw [hc b hb]
    _ = b * (a * w) := by group
    _ = b * (w * a) := by rw [hy.comm1 a ha w hw]
    _ = b * w * a := by group

theorem exists_not_commute_J0 : ∃ a ∈ CJ z s1, ∃ b ∈ CJ z s1, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hle : CJ z s1 ≤ zpowers z := fun a ha =>
    hy.mem_zpowers_of_mem_J0_of_commute ha (fun b hb => hcon a ha b hb)
  have h1 := Subgroup.card_le_of_le hle
  rw [hy.card_J0, hy.card_zpowers_z] at h1
  omega

theorem isExtraspecial2_J0 : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (CJ z s1) := by
  have hcomm_le : ⁅CJ z s1, CJ z s1⁆ ≤ zpowers z := by
    rw [← hy.hA1.commutator]
    exact Subgroup.commutator_mono (CJ_le_J _) (CJ_le_J _)
  have hcomm_eq : ⁅CJ z s1, CJ z s1⁆ = zpowers z := by
    apply le_antisymm hcomm_le
    obtain ⟨a, ha, b, hb, hab⟩ := hy.exists_not_commute_J0
    have hmem : ⁅a, b⁆ ∈ ⁅CJ z s1, CJ z s1⁆ := Subgroup.commutator_mem_commutator ha hb
    have hz' : ⁅a, b⁆ ∈ zpowers z := hcomm_le hmem
    rcases hy.mem_zpowers_z_iff.mp hz' with h1 | h1
    · exfalso
      apply hab
      rw [commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · rw [Subgroup.zpowers_le]
      rw [h1] at hmem
      exact hmem
  have hcenter : (Subgroup.center (CJ z s1)).map (CJ z s1).subtype = zpowers z := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      apply hy.mem_zpowers_of_mem_J0_of_commute a.2
      intro b hb
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨b, hb⟩).symm
    · intro x hx
      have hxJ0 : x ∈ CJ z s1 := hy.zpowers_le_J0 hx
      refine ⟨⟨x, hxJ0⟩, Subgroup.mem_center_iff.mpr fun b => ?_, rfl⟩
      apply Subtype.ext
      have := hy.commute_of_mem_zpowers_of_mem_H (J_le_H ((CJ_le_J _) b.2)) hx
      exact this
  refine ⟨IsPGroup.of_card (n := 3) (by rw [hy.card_J0]; norm_num), hcomm_eq.trans hcenter.symm,
    by rw [hcomm_eq, hy.card_zpowers_z]⟩

end Hyp

theorem conj_mem_J {g j : G} (hg : g ∈ H z) (hj : j ∈ J z) : g * j * g⁻¹ ∈ J z := by
  have hjH : j ∈ H z := J_le_H hj
  have h := (J_subgroupOf_normal z).conj_mem ⟨j, hjH⟩ (Subgroup.mem_subgroupOf.mpr hj) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem mem_CJ_conj_iff {g σ : G} (hg : g ∈ H z) (hgσ : g * σ = σ * g) (a : G) :
    a ∈ CJ z σ ↔ g * a * g⁻¹ ∈ CJ z σ := by
  have hgσ' : g⁻¹ * σ = σ * g⁻¹ := by
    calc g⁻¹ * σ = g⁻¹ * (σ * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * σ) * g⁻¹ := by rw [hgσ]
      _ = σ * g⁻¹ := by group
  have key : ∀ x y : G, x ∈ H z → x * σ = σ * x → y ∈ CJ z σ → x * y * x⁻¹ ∈ CJ z σ := by
    intro x y hx hxσ hy
    obtain ⟨hyc, hyJ⟩ := mem_CJ.mp hy
    refine mem_CJ.mpr ⟨?_, conj_mem_J hx hyJ⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    have hxσ' : x⁻¹ * σ = σ * x⁻¹ := by
      calc x⁻¹ * σ = x⁻¹ * (σ * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * σ) * x⁻¹ := by rw [hxσ]
        _ = σ * x⁻¹ := by group
    calc x * y * x⁻¹ * σ = x * y * (x⁻¹ * σ) := by group
      _ = x * y * (σ * x⁻¹) := by rw [hxσ']
      _ = x * (y * σ) * x⁻¹ := by group
      _ = x * (σ * y) * x⁻¹ := by rw [hyc]
      _ = (x * σ) * y * x⁻¹ := by group
      _ = (σ * x) * y * x⁻¹ := by rw [hxσ]
      _ = σ * (x * y * x⁻¹) := by group
  constructor
  · exact key g a hg hgσ
  · intro h
    have := key g⁻¹ (g * a * g⁻¹) ((H z).inv_mem hg) hgσ' h
    simpa [mul_assoc] using this

@[expose] def conjAut (A : Subgroup G) (g : G) (hg : ∀ a : G, a ∈ A ↔ g * a * g⁻¹ ∈ A) :
    MulAut ↥A where
  toFun a := ⟨g * a * g⁻¹, (hg a).1 a.2⟩
  invFun a := ⟨g⁻¹ * a * g, (hg _).2 (by simp [mul_assoc])⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem conjAut_apply_coe (A : Subgroup G) (g : G) (hg : ∀ a : G, a ∈ A ↔ g * a * g⁻¹ ∈ A)
    (a : ↥A) : ((conjAut A g hg a : ↥A) : G) = g * a * g⁻¹ := rfl

section Lift

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

theorem exists_lift_alpha2 :
    ∃ i : ↥(H z), qHP D i = ⟨alpha2, alpha2_mem_Q⟩ ∧ Commute i (s1HP D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP1 : IsPGroup 3 (Subgroup.zpowers (s1HP D)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_s1HP, pow_one])
  obtain ⟨x, -, hx, hxσ⟩ := exists_commute_mem_fibre (qHP D) (S := ⊤) hP1 le_top
    (not_three_dvd_card_ker_inf D ⊤) (m₀ := liftP D ⟨alpha2, alpha2_mem_Q⟩) (Subgroup.mem_top _)
    (by
      rw [qHP_liftP]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [map_zpow, qHP_s1HP]
      apply Commute.eq
      apply Commute.zpow_left
      exact Subtype.ext alpha2_mul_sigma1.symm)
  rw [qHP_liftP] at hx
  exact ⟨x, hx, (hxσ (s1HP D) (Subgroup.mem_zpowers _)).symm⟩

theorem exists_t1 (hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G)) :
    ∃ t₁ : G, t₁ ∈ H z ∧ ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z ∧
      t₁ * ((s1HP D : ↥(H z)) : G) = ((s1HP D : ↥(H z)) : G) * t₁ ∧
      t₁ * ((s2HP D : ↥(H z)) : G) = ((s2HP D : ↥(H z)) : G) * t₁ ∧
      (∀ a ∈ CJ z ((s1HP D : ↥(H z)) : G), t₁ * a = a * t₁) ∧ t₁ * t₁ ∈ zpowers z := by
  obtain ⟨i, hi, hiσ⟩ := exists_lift_alpha2 D
  set s1 : G := ((s1HP D : ↥(H z)) : G) with hs1
  set s2 : G := ((s2HP D : ↥(H z)) : G) with hs2
  set tt : G := ((tHP D : ↥(H z)) : G) with htt
  have hmemJ : ∀ x : ↥(H z), qHP D x = 1 → (x : G) ∈ J z := by
    intro x hx
    have hk : x ∈ (qHP D).ker := hx
    rw [ker_qHP] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  have hi4 : ((i : G) ^ 4) ∈ J z := by
    have : qHP D (i ^ 4) = 1 := by
      rw [map_pow, hi]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      exact alpha2_pow_four
    simpa using hmemJ _ this
  have hi2k : i ^ (2 ^ 11) = 1 := by
    have h1 := pow_card_eq_one' (G := J z) (x := ⟨(i : G) ^ 4, hi4⟩)
    rw [hy.hA1.card_J] at h1
    have h2 : ((i : G) ^ 4) ^ 2 ^ 9 = 1 := congrArg Subtype.val h1
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [show (2 : ℕ) ^ 11 = 4 * 2 ^ 9 by norm_num, pow_mul]
    exact h2
  have hiσ' : (i : G) * s1 = s1 * (i : G) := congrArg Subtype.val hiσ.eq
  have htσ1 : tt * s1 = s1 * tt := congrArg Subtype.val (commute_tHP_s1HP D).eq
  have htσ2 : tt * s2 = s2 * tt := congrArg Subtype.val (commute_tHP_s2HP D).eq
  have hnorm_i := mem_CJ_conj_iff i.2 hiσ'
  have hnorm_t := mem_CJ_conj_iff (tHP D).2 htσ1
  have hB : Nat.card (imV z (CJ z s1)) = 4 := by
    have h := card_imV hy.hA1 (CJ_le_J _) hy.zpowers_le_J0
    rw [hy.card_J0] at h
    omega
  have hφ : ∀ v, conjVA z i v ∈ imV z (CJ z s1) ↔ v ∈ imV z (CJ z s1) :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_J0 i hnorm_i
  have hk : ∀ v ∈ imV z (CJ z s1), (conjVA z i ^ 2 ^ 11) v = v := by
    intro v _
    rw [← map_pow, hi2k, map_one]
    rfl
  have hsq := sq_apply_eq_of_pow_two_pow _ hB _ hφ hk
  have hj'J : tt * ((i : G) ^ 2)⁻¹ ∈ J z := by
    have : qHP D (tHP D * (i ^ 2)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hi, qHP_tHP]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_two, alpha2_sq, mul_inv_cancel]
    simpa using hmemJ _ this
  have htriv : ∀ a ∈ CJ z s1, tt * a * tt⁻¹ * a⁻¹ ∈ zpowers z := by
    intro a ha
    let j' : ↥(H z) := ⟨tt * ((i : G) ^ 2)⁻¹, J_le_H hj'J⟩
    have he : tHP D = j' * i ^ 2 := Subtype.ext (by simp [j', tt])
    have hv : conjVA z (tHP D) (pi z ⟨a, (CJ_le_J _) ha⟩) = pi z ⟨a, (CJ_le_J _) ha⟩ := by
      rw [he, map_mul, MulAut.mul_apply, map_pow,
        hsq _ (pi_mem_imV (A := CJ z s1) (a := ⟨a, (CJ_le_J _) ha⟩) ha)]
      exact conjVA_apply_of_mem_J hy.hA1 (g := j') hj'J _
    exact (conjVA_pi_eq_iff hy.hA1 (tHP D) ⟨a, (CJ_le_J _) ha⟩).mp hv
  let σ : MulAut ↥(CJ z s1) := conjAut (CJ z s1) tt hnorm_t
  obtain ⟨q₀, hq₀⟩ := CFSG.GroupTheory.exists_conj_eq_of_forall_apply_mul_inv_mem_center
    (CFSG.IsExtraspecial2.toIsExtraspecialPGroup hy.isExtraspecial2_J0) σ (by
      intro x
      have hmem := htriv x x.2
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply_coe, σ]
      exact (hy.commute_of_mem_zpowers_of_mem_H (J_le_H ((CJ_le_J _) b.2)) hmem))
  have hq₀' : ∀ a ∈ CJ z s1, tt * a * tt⁻¹ = (q₀ : G) * a * (q₀ : G)⁻¹ := by
    intro a ha
    have := congrArg Subtype.val (hq₀ ⟨a, ha⟩)
    simpa [σ, conjAut_apply_coe] using this
  have hq₀s1 : (q₀ : G) * s1 = s1 * (q₀ : G) := by
    have := (mem_CJ.mp q₀.2).1
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hq₀s2 : (q₀ : G) * s2 = s2 * (q₀ : G) := by
    have hq₀2 : (q₀ : G) ∈ CJ z s2 := hy.heq ▸ q₀.2
    have := (mem_CJ.mp hq₀2).1
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  refine ⟨(q₀ : G)⁻¹ * tt, (H z).mul_mem ((H z).inv_mem (J_le_H ((CJ_le_J _) q₀.2))) (tHP D).2,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := conj_mem_J ((H z).inv_mem (tHP D).2) ((J z).inv_mem ((CJ_le_J _) q₀.2))
    have e : tt⁻¹ * ((q₀ : G)⁻¹ * tt) = tt⁻¹ * (q₀ : G)⁻¹ * tt⁻¹⁻¹ := by group
    rw [e]
    exact h
  · calc (q₀ : G)⁻¹ * tt * s1 = (q₀ : G)⁻¹ * (tt * s1) := by group
      _ = (q₀ : G)⁻¹ * (s1 * tt) := by rw [htσ1]
      _ = ((q₀ : G)⁻¹ * s1) * tt := by group
      _ = (s1 * (q₀ : G)⁻¹) * tt := by
        rw [show (q₀ : G)⁻¹ * s1 = s1 * (q₀ : G)⁻¹ from by
          calc (q₀ : G)⁻¹ * s1 = (q₀ : G)⁻¹ * (s1 * q₀) * (q₀ : G)⁻¹ := by group
            _ = (q₀ : G)⁻¹ * (q₀ * s1) * (q₀ : G)⁻¹ := by rw [hq₀s1]
            _ = s1 * (q₀ : G)⁻¹ := by group]
      _ = s1 * ((q₀ : G)⁻¹ * tt) := by group
  · calc (q₀ : G)⁻¹ * tt * s2 = (q₀ : G)⁻¹ * (tt * s2) := by group
      _ = (q₀ : G)⁻¹ * (s2 * tt) := by rw [htσ2]
      _ = ((q₀ : G)⁻¹ * s2) * tt := by group
      _ = (s2 * (q₀ : G)⁻¹) * tt := by
        rw [show (q₀ : G)⁻¹ * s2 = s2 * (q₀ : G)⁻¹ from by
          calc (q₀ : G)⁻¹ * s2 = (q₀ : G)⁻¹ * (s2 * q₀) * (q₀ : G)⁻¹ := by group
            _ = (q₀ : G)⁻¹ * (q₀ * s2) * (q₀ : G)⁻¹ := by rw [hq₀s2]
            _ = s2 * (q₀ : G)⁻¹ := by group]
      _ = s2 * ((q₀ : G)⁻¹ * tt) := by group
  · intro a ha
    have h := hq₀' a ha
    calc (q₀ : G)⁻¹ * tt * a = (q₀ : G)⁻¹ * (tt * a * tt⁻¹) * tt := by group
      _ = (q₀ : G)⁻¹ * ((q₀ : G) * a * (q₀ : G)⁻¹) * tt := by rw [h]
      _ = a * ((q₀ : G)⁻¹ * tt) := by group
  ·
    set t1 : G := (q₀ : G)⁻¹ * tt with ht1
    have ht1J : t1 * t1 ∈ J z := by
      have hq : qHP D (tHP D * tHP D) = 1 := by
        rw [map_mul, qHP_tHP]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        exact t_sq
      have httJ : tt * tt ∈ J z := by simpa using hmemJ _ hq
      have e : t1 * t1 = (q₀ : G)⁻¹ * (tt * (q₀ : G)⁻¹ * tt⁻¹) * (tt * tt) := by
        rw [ht1]; group
      rw [e]
      exact (J z).mul_mem ((J z).mul_mem ((J z).inv_mem ((CJ_le_J _) q₀.2))
        (conj_mem_J (tHP D).2 ((J z).inv_mem ((CJ_le_J _) q₀.2)))) httJ
    have hcent : ∀ a ∈ CJ z s1, t1 * a = a * t1 := by
      intro a ha
      have h := hq₀' a ha
      calc t1 * a = (q₀ : G)⁻¹ * (tt * a * tt⁻¹) * tt := by rw [ht1]; group
        _ = (q₀ : G)⁻¹ * ((q₀ : G) * a * (q₀ : G)⁻¹) * tt := by rw [h]
        _ = a * t1 := by rw [ht1]; group
    have ht1s1 : t1 * s1 = s1 * t1 := by
      calc t1 * s1 = (q₀ : G)⁻¹ * (tt * s1) := by rw [ht1]; group
        _ = (q₀ : G)⁻¹ * (s1 * tt) := by rw [htσ1]
        _ = ((q₀ : G)⁻¹ * s1) * tt := by group
        _ = (s1 * (q₀ : G)⁻¹) * tt := by
          rw [show (q₀ : G)⁻¹ * s1 = s1 * (q₀ : G)⁻¹ from by
            calc (q₀ : G)⁻¹ * s1 = (q₀ : G)⁻¹ * (s1 * q₀) * (q₀ : G)⁻¹ := by group
              _ = (q₀ : G)⁻¹ * (q₀ * s1) * (q₀ : G)⁻¹ := by rw [hq₀s1]
              _ = s1 * (q₀ : G)⁻¹ := by group]
        _ = s1 * t1 := by rw [ht1]; group
    have hsqJ0 : t1 * t1 ∈ CJ z s1 := by
      refine mem_CJ.mpr ⟨?_, ht1J⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t1 * t1 * s1 = t1 * (t1 * s1) := by group
        _ = t1 * (s1 * t1) := by rw [ht1s1]
        _ = (t1 * s1) * t1 := by group
        _ = (s1 * t1) * t1 := by rw [ht1s1]
        _ = s1 * (t1 * t1) := by group
    apply hy.mem_zpowers_of_mem_J0_of_commute hsqJ0
    intro b hb
    calc t1 * t1 * b = t1 * (t1 * b) := by group
      _ = t1 * (b * t1) := by rw [hcent b hb]
      _ = (t1 * b) * t1 := by group
      _ = (b * t1) * t1 := by rw [hcent b hb]
      _ = b * (t1 * t1) := by group

end Lift

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
