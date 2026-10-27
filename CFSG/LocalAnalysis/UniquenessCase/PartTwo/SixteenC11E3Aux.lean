module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Lin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_finite_mulAut {W : Type} [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun e : MulAut W => (e : W → W)) fun _ _ h => MulEquiv.ext (congrFun h)

private theorem s1611e3_gen_of_normal_seven {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) {X : Subgroup (MulAut (Vtil V₀ V h125.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h125.isElemAbelian) (hXcard : Nat.card X = 7)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h125.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X) :
    ∃ z : MulAut (Vtil V₀ V h125.isElemAbelian),
      orderOf z = 7 ∧ (∀ v, z v = v → v = 1) ∧ X = Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have hodd : Odd (Nat.card X) := by rw [hXcard]; norm_num
  have hXn : (X.subgroupOf (Mbar D.M V₀ V h125.isElemAbelian)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hXnorm g g.2 n hn⟩
  have hfixX := s16c1610_fixV_eq_bot D h.hx h.h61 h.h127 h.h1214 h125 hXM hXn hXne hodd
  haveI : IsCyclic X := isCyclic_of_prime_card hXcard
  obtain ⟨z, hzgen⟩ := IsCyclic.exists_generator (α := X)
  have hzSub : orderOf z = Nat.card X := orderOf_eq_card_of_forall_mem_zpowers hzgen
  have hz : orderOf (z : MulAut (Vtil V₀ V h125.isElemAbelian)) = 7 := by
    rw [Subgroup.orderOf_coe, hzSub, hXcard]
  have hXeq : X = Subgroup.zpowers (z : MulAut (Vtil V₀ V h125.isElemAbelian)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hzgen ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.mpr z.2
  refine ⟨(z : MulAut (Vtil V₀ V h125.isElemAbelian)), hz, ?_, hXeq⟩
  intro v hv
  have hv' : v ∈ fixV (Subgroup.zpowers (z : MulAut (Vtil V₀ V h125.isElemAbelian))) :=
    (mem_fixV_zpowers _ v).2 hv
  rw [← hXeq, hfixX] at hv'
  exact Subgroup.mem_bot.1 hv'

theorem s1611e3_three_le_mBar_of_normal_seven {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) {X : Subgroup (MulAut (Vtil V₀ V h125.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h125.isElemAbelian) (hXcard : Nat.card X = 7)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h125.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hrk : 6 ≤ rk (Vtil V₀ V h125.isElemAbelian)) :
    3 ≤ mBar D.M V₀ V h125.isElemAbelian := by
  obtain ⟨z, hz, hzfix, hXeq⟩ := s1611e3_gen_of_normal_seven h h125 hXM hXcard hXnorm
  unfold mBar E3.mParam
  by_cases hEven : Even (Nat.card (Mbar D.M V₀ V h125.isElemAbelian))
  · rw [if_pos hEven]
    have hne : ({n : ℕ | ∃ t ∈ Mbar D.M V₀ V h125.isElemAbelian, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))} : Set ℕ).Nonempty := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Finite (MulAut (Vtil V₀ V h125.isElemAbelian)) := s1611e3_finite_mulAut
      have hdvd : 2 ∣ Nat.card (Mbar D.M V₀ V h125.isElemAbelian) :=
        even_iff_two_dvd.mp hEven
      obtain ⟨t, ht⟩ :=
        exists_prime_orderOf_dvd_card' (G := Mbar D.M V₀ V h125.isElemAbelian) 2 hdvd
      refine ⟨rkIdx (fixV (Subgroup.zpowers (t : MulAut (Vtil V₀ V h125.isElemAbelian)))),
        t, t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩
    obtain ⟨t, htM, ht2, hval⟩ := Nat.sInf_mem hne
    rw [hval]
    have hzX : z ∈ X := by rw [hXeq]; exact Subgroup.mem_zpowers z
    have hn : t * z * t⁻¹ ∈ Subgroup.zpowers z := by
      have h1 := hXnorm t htM z hzX
      rwa [hXeq] at h1
    exact s1611e3_three_le_rkIdx_of_normalizes (s15_Infra_vtil_sq_eq_one V₀ V h125.isElemAbelian)
      hrk hz hzfix ht2 hn
  · rw [if_neg hEven]
    omega

theorem s1611e3_cent_of_normal_seven {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) {X : Subgroup (MulAut (Vtil V₀ V h125.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h125.isElemAbelian) (hXcard : Nat.card X = 7)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h125.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hodd : Odd (rk (Vtil V₀ V h125.isElemAbelian))) :
    ∀ t ∈ Mbar D.M V₀ V h125.isElemAbelian, orderOf t = 2 → ∀ x ∈ X, t * x = x * t := by
  obtain ⟨z, hz, hzfix, hXeq⟩ := s1611e3_gen_of_normal_seven h h125 hXM hXcard hXnorm
  intro t htM ht2 x hxX
  have hzX : z ∈ X := by rw [hXeq]; exact Subgroup.mem_zpowers z
  have hn : t * z * t⁻¹ ∈ Subgroup.zpowers z := by
    have h1 := hXnorm t htM z hzX
    rwa [hXeq] at h1
  have htz : t * z = z * t :=
    s1611e3_comm_of_normalizes_of_odd (s15_Infra_vtil_sq_eq_one V₀ V h125.isElemAbelian)
      hodd hz hzfix ht2 hn
  have hxzp : x ∈ Subgroup.zpowers z := hXeq ▸ hxX
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxzp
  have hcomm : Commute t z := htz
  rw [← hk]
  exact (hcomm.zpow_right k).eq

theorem s1611e3_v1Sub_eq_bot_of_fix (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hfix : ∀ w ∈ wTil ⊥ V hV L, (∀ l ∈ lBar ⊥ V hV L, l w = w) → w = 1) :
    v1Sub D.M ⊥ V hV L = ⊥ := by
  rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
  suffices hbot : wSub ⊥ V hV L ⊓ centralizer (L : Set G) = ⊥ by
    rw [hbot, iSup_eq_bot]
    intro m
    rw [conjSubgroup]
    exact Subgroup.map_bot _
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwW, hwC⟩ := hw
  obtain ⟨x, hxval, hxS⟩ := (mem_preTil ⊥ V hV (wTil ⊥ V hV L)).1 hwW
  have hx1 : mkTil ⊥ V hV x = 1 := by
    apply hfix
    · exact hxS
    · intro l hl
      rw [lBar] at hl
      obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L l).1 hl
      rw [actTil_mk]
      apply congrArg (mkTil ⊥ V hV)
      apply IntMod.val_injective
      rw [actStab_apply_val, hxval]
      have hc := Subgroup.mem_centralizer_iff.1 hwC (g : G) hgL
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hxone : x = 1 := by
    have h := (mkTil_eq_iff ⊥ V hV x 1).1 (by simpa using hx1)
    rw [Subgroup.mem_bot] at h
    apply IntMod.val_injective
    simpa using h
  rw [← hxval, hxone]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
