module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedClass
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem comm_of_commutator_eq_one {x a : G} (h : x * a * x⁻¹ * a⁻¹ = 1) : x * a = a * x := by
  have h1 : x * a * x⁻¹ = a := by
    calc x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
      _ = a := by rw [h, one_mul]
  calc x * a = (x * a * x⁻¹) * x := by group
    _ = a * x := by rw [h1]

theorem mul_mem_zpowers_of_not_mem_zpowers (S : Setting z E F) (hZ4 : Nat.card ↥(ZQ z) = 4)
    {u v : ↥(ZQ z)} (hu : (u : G) ∉ Subgroup.zpowers z) (hv : (v : G) ∉ Subgroup.zpowers z) :
    ((v * u : ↥(ZQ z)) : G) ∈ Subgroup.zpowers z := by
  set K : Subgroup ↥(ZQ z) := (Subgroup.zpowers z).subgroupOf (ZQ z) with hK
  have hzle : Subgroup.zpowers z ≤ ZQ z := (Subgroup.zpowers_le).mpr (z_mem_ZQ S)
  have hKcard : Nat.card ↥K = 2 := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers,
      S.hyp.orderOf_z]
  have hindex : K.index = 2 := by
    have h := K.index_mul_card
    rw [hKcard, hZ4] at h
    omega
  obtain ⟨b, hb⟩ := Subgroup.index_eq_two_iff.mp hindex
  have hnK : ∀ w : ↥(ZQ z), (w : G) ∉ Subgroup.zpowers z → w * b ∈ K := by
    intro w hw
    have hwK : w ∉ K := fun hmem => hw (Subgroup.mem_subgroupOf.mp hmem)
    rcases hb w with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hwK
  have h1 := hnK u hu
  have h2 := hnK v hv
  have h3 : v * u⁻¹ ∈ K := by
    have := K.mul_mem h2 (K.inv_mem h1)
    simpa [mul_assoc] using this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (ZQ_mul_self S u)
  rw [huinv] at h3
  exact Subgroup.mem_subgroupOf.mp h3

theorem exists_mem_Q_commutator_eq_z (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (haZ : a ∉ ZQ z) : ∃ q ∈ Q z, q * a * q⁻¹ * a⁻¹ = z := by
  have hnot : ¬ ∀ q ∈ Q z, a * q = q * a := by
    intro hall
    apply haZ
    refine Subgroup.mem_inf.mpr ⟨haQ, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    exact (hall q hq).symm
  push Not at hnot
  obtain ⟨q, hq, hne⟩ := hnot
  have hmem : ⁅q, a⁆ ∈ Subgroup.zpowers z := commutator_mem_zpowers_of_mem_Q S hq haQ
  rcases eq_one_or_z_of_mem_zpowers S hmem with h1 | h1
  · exfalso
    apply hne
    rw [commutatorElement_def] at h1
    calc a * q = (q * a * q⁻¹ * a⁻¹) * (a * q) := by rw [h1, one_mul]
      _ = q * a := by group
  · exact ⟨q, hq, by rw [commutatorElement_def] at h1; exact h1⟩

theorem inv_mul_mem_CHbar_of_not_mem (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ4 : Nat.card ↥(ZQ z) = 4) {Y : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q)
    (hZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u) {y₁ y₂ : Hbar z} (h₁ : y₁ ∈ Y)
    (h₂ : y₂ ∈ Y) (n₁ : y₁ ∉ CHbar S a) (n₂ : y₂ ∉ CHbar S a) :
    y₂⁻¹ * y₁ ∈ CHbar S a := by
  have haQ : a ∈ Q z := h.mem_Q
  set f : ↥(H z) →* Hbar z := QuotientGroup.mk' ((Q z).subgroupOf (H z)) with hf
  have hPZ : ∀ x : ↥(H z), QuotientGroup.mk x ∈ Y → ∀ v ∈ ZQ z,
      (x : G) * v * (x : G)⁻¹ = v := by
    intro x hx v hv
    have h1 := congrArg Subtype.val (hZ _ hx ⟨v, hv⟩)
    have h2 := rhoZ_mk S x ⟨v, hv⟩
    exact h2.symm.trans h1
  have hmemZ : ∀ x : ↥(preimageInH Y), (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ ∈ ZQ z := by
    intro x
    exact mem_ZQ_of_rhoLin_apply_aVec_eq S haQ x.1.2 (hfix (f x.1) (Subgroup.mem_comap.mp x.2))
  obtain ⟨φ, hφ⟩ := exists_monoidHom_preimage_commutator (a := a) (P := Y) hPZ hmemZ
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [S.hyp.orderOf_z, pow_two] at this
  obtain ⟨q, hq, hqz⟩ := exists_mem_Q_commutator_eq_z S haQ h.not_mem_ZQ
  have hqH : q ∈ H z := Q_le_H S hq
  have hqY : (⟨q, hqH⟩ : ↥(H z)) ∈ preimageInH Y := by
    rw [preimageInH, Subgroup.mem_comap]
    have : f ⟨q, hqH⟩ = 1 := by
      rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hq
    rw [this]
    exact Y.one_mem
  have hφq : (φ ⟨⟨q, hqH⟩, hqY⟩ : G) = z := by
    rw [hφ]
    exact hqz
  have claimA : ∀ x : ↥(preimageInH Y), (φ x : G) ∈ Subgroup.zpowers z →
      (QuotientGroup.mk x.1 : Hbar z) ∈ CHbar S a := by
    intro x hx
    rcases eq_one_or_z_of_mem_zpowers S hx with h1 | h1
    · rw [hφ x] at h1
      refine (mem_CHbar_iff S a _).mpr ⟨x.1, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_commutator_eq_one h1
    · have h2 : (φ (x * ⟨⟨q, hqH⟩, hqY⟩) : G) = 1 := by
        rw [map_mul, Subgroup.coe_mul, h1, hφq, hzz]
      rw [hφ] at h2
      refine (mem_CHbar_iff S a _).mpr ⟨(x * ⟨⟨q, hqH⟩, hqY⟩).1, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact comm_of_commutator_eq_one h2
      · have hq1 : (QuotientGroup.mk (⟨q, hqH⟩ : ↥(H z)) : Hbar z) = 1 := by
          rw [QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hq
        have : (x * ⟨⟨q, hqH⟩, hqY⟩).1 = x.1 * ⟨q, hqH⟩ := rfl
        rw [this, QuotientGroup.mk_mul, hq1, mul_one]
  obtain ⟨ℓ₁, rfl⟩ := QuotientGroup.mk_surjective y₁
  obtain ⟨ℓ₂, rfl⟩ := QuotientGroup.mk_surjective y₂
  have hℓ₁ : ℓ₁ ∈ preimageInH Y := Subgroup.mem_comap.mpr h₁
  have hℓ₂ : ℓ₂ ∈ preimageInH Y := Subgroup.mem_comap.mpr h₂
  have hnot₁ : (φ ⟨ℓ₁, hℓ₁⟩ : G) ∉ Subgroup.zpowers z := fun hmem => n₁ (claimA ⟨ℓ₁, hℓ₁⟩ hmem)
  have hnot₂ : (φ ⟨ℓ₂, hℓ₂⟩ : G) ∉ Subgroup.zpowers z := fun hmem => n₂ (claimA ⟨ℓ₂, hℓ₂⟩ hmem)
  have hprod := mul_mem_zpowers_of_not_mem_zpowers S hZ4 hnot₁ hnot₂
  have hinv : (φ ⟨ℓ₂, hℓ₂⟩)⁻¹ = φ ⟨ℓ₂, hℓ₂⟩ := inv_eq_of_mul_eq_one_right (ZQ_mul_self S _)
  have hmem : (φ ((⟨ℓ₂, hℓ₂⟩ : ↥(preimageInH Y))⁻¹ * ⟨ℓ₁, hℓ₁⟩) : G) ∈ Subgroup.zpowers z := by
    rw [map_mul, map_inv, hinv]
    exact hprod
  have := claimA _ hmem
  rw [Subgroup.coe_mul, Subgroup.coe_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
  exact this

theorem inv_mul_mem_CHbar_of_fix_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ4 : Nat.card ↥(ZQ z) = 4) (hZX : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    {g₁ g₂ : Hbar z} (h₁ : g₁ ∈ Xsub S a) (h₂ : g₂ ∈ Xsub S a)
    (f₁ : rhoLin S g₁ (aVec S h.mem_Q) = aVec S h.mem_Q)
    (f₂ : rhoLin S g₂ (aVec S h.mem_Q) = aVec S h.mem_Q)
    (n₁ : g₁ ∉ CHbar S a) (n₂ : g₂ ∉ CHbar S a) : g₂⁻¹ * g₁ ∈ CHbar S a := by
  let Y : Subgroup (Hbar z) :=
    { carrier := {y | y ∈ Xsub S a ∧ rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q}
      mul_mem' := fun {x y} hx hy => ⟨(Xsub S a).mul_mem hx.1 hy.1, by
        rw [rhoLin_mul, LinearEquiv.mul_apply, hy.2, hx.2]⟩
      one_mem' := ⟨(Xsub S a).one_mem, by
        have : rhoLin S 1 = 1 := by rw [rhoLin, map_one]; rfl
        rw [this]; rfl⟩
      inv_mem' := fun {x} hx => ⟨(Xsub S a).inv_mem hx.1, by
        rw [rhoLin_inv]
        calc (rhoLin S x)⁻¹ (aVec S h.mem_Q) = (rhoLin S x)⁻¹ (rhoLin S x (aVec S h.mem_Q)) := by
              rw [hx.2]
          _ = aVec S h.mem_Q := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl⟩ }
  exact inv_mul_mem_CHbar_of_not_mem S h hZ4 (Y := Y) (fun y hy => hy.2)
    (fun y hy => hZX y hy.1) ⟨h₁, f₁⟩ ⟨h₂, f₂⟩ n₁ n₂

theorem ncard_conj_fixer_le_two (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ4 : Nat.card ↥(ZQ z) = 4) (hZX : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (hR2 : Nat.card ↥(Rbar S a) = 2) {r : ↥(Xsub S a)} (hrR : (r : Hbar z) ∈ Rbar S a)
    (hr1 : (r : Hbar z) ≠ 1) :
    {d : ↥(Xsub S a) | ∃ g : ↥(Xsub S a), rhoX S a g (aVec S h.mem_Q) = aVec S h.mem_Q ∧
      d = g * r * g⁻¹}.ncard ≤ 2 := by
  classical
  have hcomm : ∀ g : ↥(Xsub S a), (g : Hbar z) ∈ CHbar S a → g * r * g⁻¹ = r := by
    intro g hg
    have := commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR2 hrR hr1 hg
    have h1 : g * r = r * g := Subtype.ext this
    rw [h1]
    group
  by_cases hex : ∃ g₀ : ↥(Xsub S a), rhoX S a g₀ (aVec S h.mem_Q) = aVec S h.mem_Q ∧
      (g₀ : Hbar z) ∉ CHbar S a
  · obtain ⟨g₀, hg₀, hn₀⟩ := hex
    have hsub : {d : ↥(Xsub S a) | ∃ g : ↥(Xsub S a),
        rhoX S a g (aVec S h.mem_Q) = aVec S h.mem_Q ∧ d = g * r * g⁻¹} ⊆
        {r, g₀ * r * g₀⁻¹} := by
      rintro d ⟨g, hg, rfl⟩
      by_cases hgC : (g : Hbar z) ∈ CHbar S a
      · exact Or.inl (hcomm g hgC)
      · right
        have h1 := inv_mul_mem_CHbar_of_fix_Xsub S h hZ4 hZX g.2 g₀.2 hg hg₀ hgC hn₀
        have h2 : (g₀⁻¹ * g : ↥(Xsub S a)) * r * (g₀⁻¹ * g : ↥(Xsub S a))⁻¹ = r :=
          hcomm _ (by simpa using h1)
        have h3 : g * r * g⁻¹ = g₀ * ((g₀⁻¹ * g) * r * (g₀⁻¹ * g)⁻¹) * g₀⁻¹ := by group
        rw [h3, h2]
        rfl
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_insert_le r ({g₀ * r * g₀⁻¹} : Set ↥(Xsub S a))
    rw [Set.ncard_singleton] at h2
    omega
  · push Not at hex
    have hsub : {d : ↥(Xsub S a) | ∃ g : ↥(Xsub S a),
        rhoX S a g (aVec S h.mem_Q) = aVec S h.mem_Q ∧ d = g * r * g⁻¹} ⊆ {r} := by
      rintro d ⟨g, hg, rfl⟩
      exact hcomm g (hex g hg)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at h1
    omega

end CFSG.RankThree.GF2n.Stroth78
