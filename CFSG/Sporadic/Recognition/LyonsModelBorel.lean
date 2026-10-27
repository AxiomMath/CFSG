module

public import CFSG.Sporadic.Recognition.LyonsModelStage
public import CFSG.Sporadic.Recognition.LyonsModelTransport

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open Equiv Equiv.Perm Subgroup CFSG.Blueprint

section Model

variable (hM : ModelChecks)
include hM

theorem yB_comm_xB : yB * xB = xB * yB := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_yB, coe_xB]
  exact (cp1_facts hM.tab hM.struct hM.cp1).1

theorem yB_pow_three : yB ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_yB, Subgroup.coe_one]
  exact (cp1_facts hM.tab hM.struct hM.cp1).2.1

theorem yB_ne_one : yB ≠ 1 := by
  intro h
  apply (cp1_facts hM.tab hM.struct hM.cp1).2.2.1
  have := congrArg Subtype.val h
  rwa [coe_yB, Subgroup.coe_one] at this

theorem yB_not_mem_zpowers_xB : yB ∉ zpowers xB := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk' : xG ^ k = y0G := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow, coe_xB, coe_yB] at this
  obtain ⟨-, -, hne1, hne2, hne3, -⟩ := cp1_facts hM.tab hM.struct hM.cp1
  have hx3 : xG ^ 3 = 1 := by
    have := congrArg Subtype.val (xB_pow_three hM.tab hM.struct)
    rwa [Subgroup.coe_pow, coe_xB, Subgroup.coe_one] at this
  have hR : R0G = xG⁻¹ := by rw [xG_def, inv_inv]
  have hx2 : xG ^ 2 = xG⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hx3
  rcases zpow_cases hx3 k with h | h | h
  · rw [h] at hk'
    exact hne1 hk'.symm
  · rw [h] at hk'
    apply hne2
    rw [← hk', hR, ← pow_two, hx2]
  · rw [h, hx2] at hk'
    exact hne3 (by rw [← hk', hR])

theorem fB_pow_five : fB ^ 5 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_fB, Subgroup.coe_one]
  exact (cp1_facts hM.tab hM.struct hM.cp1).2.2.2.2.2.1

theorem fB_ne_one : fB ≠ 1 := by
  intro h
  apply (cp1_facts hM.tab hM.struct hM.cp1).2.2.2.2.2.2.1
  have := congrArg Subtype.val h
  rwa [coe_fB, Subgroup.coe_one] at this

theorem fB_comm_yB : fB * yB = yB * fB := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_yB, coe_fB]
  exact (cp1_facts hM.tab hM.struct hM.cp1).2.2.2.2.2.2.2.1

theorem nB_yB : nB * yB * nB⁻¹ = yB := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_yB, coe_nB, mul_assoc]
  exact (cp1_facts hM.tab hM.struct hM.cp1).2.2.2.2.2.2.2.2.1

theorem nB_xB : nB * xB * nB⁻¹ = xB⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_xB, coe_nB,
    mul_assoc]
  exact (cp1_facts hM.tab hM.struct hM.cp1).2.2.2.2.2.2.2.2.2

end Model

theorem mem_K0_of_pow_five (h : tabCheck = true) (hc : coverCheck = true)
    (hs : structCheck = true) {u : B0} (hu : u ^ 5 = 1) : u ∈ K0 := by
  have hn : K0.Normal := (K0_normal_index_le_two h hs).1
  have h1 : u ^ K0.index ∈ K0 := Subgroup.pow_index_mem K0 u
  rw [K0_index_two h hc hs] at h1
  have : u = (u ^ 2) ^ 3 := by
    rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ', hu, mul_one]
  rw [this]
  exact pow_mem h1 3

section Cert

variable (hM : ModelChecks)
include hM

theorem fB_comm_xB : fB * xB = xB * fB :=
  comm_xB_of_mem_K0 hM (mem_K0_of_pow_five hM.tab hM.cover hM.struct (fB_pow_five hM))

theorem inv_centre_K0 :
    ∀ b : B0, b ∉ K0 → ∀ z : ↥K0, z ∈ Subgroup.center ↥K0 → b * (z : B0) * b⁻¹ = (z : B0)⁻¹ := by
  intro b hb z hz
  have hz' : (z : B0) ∈ zpowers xB :=
    K0_center hM.tab hM.cover hM.struct z z.2 (fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz'
  have hbx := (K0_centralizer_and_inv hM.tab hM.cover hM.struct).2 b hb
  rw [← hn, ← conj_zpow, hbx, inv_zpow]

end Cert

section G

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

omit [Finite G] in
theorem x₂_mem_normX (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : (x₂ : G) ∈ NormX (x₁ : G) :=
  centralizer_le_normX (mem_centralizer_singleton_iff.2 (D.comm₂₁ S))

omit [Finite G] in
theorem x₃_mem_normX (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : (x₃ : G) ∈ NormX (x₁ : G) :=
  centralizer_le_normX (mem_centralizer_singleton_iff.2 (D.comm₃₁ S))

omit [Finite G] in
theorem x₁_pow_three (S : LyStd ρ x₁ x₂ x₃) : (x₁ : G) ^ 3 = 1 := by
  have := congrArg Subtype.val S.pow₁
  simpa using this

omit [Finite G] in
theorem x₁_ne_one (S : LyStd ρ x₁ x₂ x₃) : (x₁ : G) ≠ 1 := by
  intro h
  have : x₁ = 1 := Subtype.ext h
  have h2 := S.rho₁
  rw [this, map_one] at h2
  exact absurd h2 (by decide)

theorem isConj_of_five_dvd
    {K : Type*} [Group K] (e : K ≃* NativeSporadic.McL) {a b : K} (ha : orderOf a = 3)
    (hb : orderOf b = 3) (ha5 : 5 ∣ Nat.card ↥(centralizer ({a} : Set K)))
    (hb5 : 5 ∣ Nat.card ↥(centralizer ({b} : Set K))) : IsConj a b := by
  obtain ⟨r₁, r₂, -, -, -, c₂, hall⟩ := exists_two_classes_of_mulEquiv e
  exact isConj_of_card_eq_aux c₂ hall ha hb (card_centralizer_eq_of_five_dvd e ha ha5)
    (card_centralizer_eq_of_five_dvd e hb hb5)

theorem exists_conj_x₂_mul_zpow
    (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {y f : G}
    (hy : y * (x₁ : G) = (x₁ : G) * y) (hy3 : y ^ 3 = 1) (hyn : y ∉ zpowers (x₁ : G))
    (hf : f * (x₁ : G) = (x₁ : G) * f) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1) (hfy : f * y = y * f) :
    ∃ m : G, m * (x₁ : G) = (x₁ : G) * m ∧ ∃ k : ℤ, m * (x₂ : G) * m⁻¹ = y * (x₁ : G) ^ k := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have hX3 := x₁_pow_three S
  let yM : ↥(centralizer ({(x₁ : G)} : Set G)) := ⟨y, mem_centralizer_singleton_iff.2 hy⟩
  let fM : ↥(centralizer ({(x₁ : G)} : Set G)) := ⟨f, mem_centralizer_singleton_iff.2 hf⟩
  have hyq : orderOf (QuotientGroup.mk yM : CentQuot (x₁ : G)) = 3 := by
    have h3 : (QuotientGroup.mk yM : CentQuot (x₁ : G)) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : yM ^ 3 = 1 := Subtype.ext hy3
      rw [this]
      rfl
    have hne : (QuotientGroup.mk yM : CentQuot (x₁ : G)) ≠ 1 := fun h1 =>
      hyn (mem_zpowers_of_mk_eq_one (x₁ : G) h1)
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime h3 hne
  have hfq : orderOf (QuotientGroup.mk fM : CentQuot (x₁ : G)) = 5 := by
    have h5 : (QuotientGroup.mk fM : CentQuot (x₁ : G)) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : fM ^ 5 = 1 := Subtype.ext hf5
      rw [this]
      rfl
    have hne : (QuotientGroup.mk fM : CentQuot (x₁ : G)) ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_mk_eq_one (x₁ : G) h1)
      have hf3 : f ^ 3 = 1 := by
        have hk' : (x₁ : G) ^ k = f := hk
        rw [← hk', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hX3, one_zpow]
      apply hf1
      calc f = (f ^ 3) ^ 2 * (f ^ 5)⁻¹ := by group
        _ = 1 := by rw [hf3, hf5]; group
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime h5 hne
  have hcomm : (QuotientGroup.mk fM : CentQuot (x₁ : G)) * QuotientGroup.mk yM =
      QuotientGroup.mk yM * QuotientGroup.mk fM := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hfy
  have hfC : (QuotientGroup.mk fM : CentQuot (x₁ : G)) ∈
      centralizer ({(QuotientGroup.mk yM : CentQuot (x₁ : G))} : Set (CentQuot (x₁ : G))) :=
    mem_centralizer_singleton_iff.2 hcomm
  have h5dvd : 5 ∣ Nat.card ↥(centralizer ({(QuotientGroup.mk yM : CentQuot (x₁ : G))} :
      Set (CentQuot (x₁ : G)))) := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hord : orderOf (⟨QuotientGroup.mk fM, hfC⟩ : ↥(centralizer
        ({(QuotientGroup.mk yM : CentQuot (x₁ : G))} : Set (CentQuot (x₁ : G))))) = 5 := by
      rw [Subgroup.orderOf_mk]
      exact hfq
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hconj := isConj_of_five_dvd e (D.orderOf_x₂Q S) hyq (D.five_dvd_card_centralizer_x₂Q S)
    h5dvd
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective c
  have hk : (QuotientGroup.mk (yM⁻¹ * (m * D.x₂M S * m⁻¹)) : CentQuot (x₁ : G)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    change (QuotientGroup.mk yM : CentQuot (x₁ : G))⁻¹ *
      (QuotientGroup.mk m * D.x₂Q S * (QuotientGroup.mk m)⁻¹) = 1
    rw [hc]
    group
  obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_mk_eq_one (x₁ : G) hk)
  have hk'' : (x₁ : G) ^ k = y⁻¹ * ((m : G) * (x₂ : G) * (m : G)⁻¹) := hk'
  refine ⟨(m : G), mem_centralizer_singleton_iff.1 m.2, k, ?_⟩
  calc (m : G) * (x₂ : G) * (m : G)⁻¹ = y * (y⁻¹ * ((m : G) * (x₂ : G) * (m : G)⁻¹)) := by
        group
    _ = y * (x₁ : G) ^ k := by rw [hk'']

end G

section Line

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem exists_mulEquiv_line
    (hM : ModelChecks) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (ν : ↥(NormX (x₁ : G)) ≃* B0) (h1 : ν ⟨(x₁ : G), self_mem_normX (x₁ : G)⟩ = xB) :
    ∃ ν' : ↥(NormX (x₁ : G)) ≃* B0, ν' ⟨(x₁ : G), self_mem_normX (x₁ : G)⟩ = xB ∧
      ν' ⟨(x₂ : G), x₂_mem_normX D S⟩ = yB := by
  let b₁ : ↥(NormX (x₁ : G)) := ⟨(x₁ : G), self_mem_normX (x₁ : G)⟩
  let b₂ : ↥(NormX (x₁ : G)) := ⟨(x₂ : G), x₂_mem_normX D S⟩
  have hb₁ : ν b₁ = xB := h1
  let y₁ : ↥(NormX (x₁ : G)) := ν.symm yB
  let f₁ : ↥(NormX (x₁ : G)) := ν.symm fB
  have hy₁ : ν y₁ = yB := ν.apply_symm_apply yB
  have hf₁ : ν f₁ = fB := ν.apply_symm_apply fB
  have hyc : y₁ * b₁ = b₁ * y₁ := by
    apply ν.injective
    rw [map_mul, map_mul, hy₁, hb₁]
    exact yB_comm_xB hM
  have hfc : f₁ * b₁ = b₁ * f₁ := by
    apply ν.injective
    rw [map_mul, map_mul, hf₁, hb₁]
    exact fB_comm_xB hM
  have hfy : f₁ * y₁ = y₁ * f₁ := by
    apply ν.injective
    rw [map_mul, map_mul, hf₁, hy₁]
    exact fB_comm_yB hM
  have hy3 : y₁ ^ 3 = 1 := by
    apply ν.injective
    rw [map_pow, hy₁, map_one]
    exact yB_pow_three hM
  have hf5 : f₁ ^ 5 = 1 := by
    apply ν.injective
    rw [map_pow, hf₁, map_one]
    exact fB_pow_five hM
  have hf1 : f₁ ≠ 1 := by
    intro h
    apply fB_ne_one hM
    rw [← hf₁, h, map_one]
  have hyn : (y₁ : G) ∉ zpowers (x₁ : G) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : b₁ ^ k = y₁ := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
    apply yB_not_mem_zpowers_xB hM
    rw [← hy₁, ← hk', map_zpow, hb₁]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  obtain ⟨m, hm, k, hk⟩ := exists_conj_x₂_mul_zpow D S (y := (y₁ : G)) (f := (f₁ : G))
    (congrArg Subtype.val hyc) (congrArg Subtype.val hy3) hyn (congrArg Subtype.val hfc)
    (congrArg Subtype.val hf5) (fun h => hf1 (Subtype.ext h)) (congrArg Subtype.val hfy)
  have hmB : m ∈ NormX (x₁ : G) := centralizer_le_normX (mem_centralizer_singleton_iff.2 hm)
  let mB : ↥(NormX (x₁ : G)) := ⟨m, hmB⟩
  let ν₂ : ↥(NormX (x₁ : G)) ≃* B0 := (MulAut.conj mB).trans ν
  have hν₂ : ∀ b, ν₂ b = ν (mB * b * mB⁻¹) := fun b => rfl
  have h₂1 : ν₂ b₁ = xB := by
    rw [hν₂]
    have : mB * b₁ * mB⁻¹ = b₁ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext hm
    rw [this, hb₁]
  have h₂2 : ν₂ b₂ = yB * xB ^ k := by
    rw [hν₂]
    have : mB * b₂ * mB⁻¹ = y₁ * b₁ ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      exact hk
    rw [this, map_mul, map_zpow, hy₁, hb₁]
  let n' : ↥(NormX (x₁ : G)) := ν₂.symm nB
  have hn' : ν₂ n' = nB := ν₂.apply_symm_apply nB
  have hn'₂ : n' * b₂ * n'⁻¹ = b₂ * b₁ ^ (2 * (-k)) := by
    apply ν₂.injective
    rw [map_mul, map_mul, map_inv, map_mul, map_zpow, hn', h₂1, h₂2]
    have e1 : nB * (yB * xB ^ k) * nB⁻¹ = yB * xB⁻¹ ^ k := by
      calc nB * (yB * xB ^ k) * nB⁻¹ = (nB * yB * nB⁻¹) * (nB * xB ^ k * nB⁻¹) := by group
        _ = yB * xB⁻¹ ^ k := by rw [← conj_zpow, nB_yB hM, nB_xB hM]
    have e2 : (yB * xB ^ k) * xB ^ (2 * -k) = yB * xB⁻¹ ^ k := by
      rw [mul_assoc, ← zpow_add, inv_zpow', show k + 2 * -k = -k by ring]
    rw [e1, e2]
  have hrig : (n' : G) * (x₂ : G) * (n' : G)⁻¹ = (x₂ : G) * (x₁ : G) ^ (2 * (-k)) := by
    have := congrArg Subtype.val hn'₂
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      Subgroup.coe_zpow] at this
    exact this
  have hx1k : (x₁ : G) ^ (2 * (-k)) = 1 := D.zpow_eq_one_of_conj_mul S hrig
  have hx1k' : (x₁ : G) ^ (-k) = 1 :=
    zpow_eq_one_of_zpow_two_mul (x₁_pow_three S) (x₁_ne_one S) hx1k
  have hb₁k : b₁ ^ (-k) = 1 := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hx1k')
  have hxk : xB ^ k = 1 := by
    have h3 : xB ^ (-k) = 1 := by
      rw [← h₂1, ← map_zpow, hb₁k, map_one]
    rw [zpow_neg, inv_eq_one] at h3
    exact h3
  exact ⟨ν₂, h₂1, by rw [h₂2, hxk, mul_one]⟩

theorem card_normalizer_zpowers_x₂
    (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(normalizer (zpowers (⟨(x₂ : G), x₂_mem_normX D S⟩ : ↥(NormX (x₁ : G))) :
      Set ↥(NormX (x₁ : G)))) = 349920 := by
  have e : normalizer (zpowers (⟨(x₂ : G), x₂_mem_normX D S⟩ : ↥(NormX (x₁ : G))) :
      Set ↥(NormX (x₁ : G))) = (NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G)) := by
    rw [NN, inf_subgroupOf_left, subgroupOf_normalizer_eq (zpowers_le.2 (x₂_mem_normX D S)),
      subgroupOf_zpowers_of_mem (x₂_mem_normX D S)]
  have hle : NN (x₁ : G) (x₂ : G) ≤ NormX (x₁ : G) := inf_le_left
  rw [e, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  exact D.card_NN' S

end Line

section Stage1

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem normal_zpowers_normX {H : Type*} [Group H] (X : H) :
    (zpowers (⟨X, self_mem_normX X⟩ : ↥(NormX X))).Normal := by
  rw [← subgroupOf_zpowers_of_mem (self_mem_normX X)]
  exact (normal_subgroupOf_iff_le_normalizer (zpowers_le.2 (self_mem_normX X))).2 le_rfl

theorem inv_centre_normX (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∀ b : ↥(NormX (x₁ : G)),
      b ∉ (centralizer ({(x₁ : G)} : Set G)).subgroupOf (NormX (x₁ : G)) →
      ∀ z : ↥((centralizer ({(x₁ : G)} : Set G)).subgroupOf (NormX (x₁ : G))),
        z ∈ Subgroup.center
          ↥((centralizer ({(x₁ : G)} : Set G)).subgroupOf (NormX (x₁ : G))) →
        b * (z : ↥(NormX (x₁ : G))) * b⁻¹ = (z : ↥(NormX (x₁ : G)))⁻¹ := by
  intro b hb z hz
  have hbx : (b : G) * (x₁ : G) * (b : G)⁻¹ = (x₁ : G)⁻¹ := by
    rcases conj_eq_or_inv (x₁_pow_three S) (x₁_ne_one S) b.2 with h | h
    · exfalso
      apply hb
      rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    · exact h
  have hcen : subgroupOfEquivOfLe (centralizer_le_normX (X := (x₁ : G))) z ∈
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) := by
    rw [← Subgroup.map_center_eq (subgroupOfEquivOfLe (centralizer_le_normX (X := (x₁ : G))))]
    exact Subgroup.mem_map_of_mem _ hz
  rw [D.center_centralizer S] at hcen
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcen
  have hk' : (x₁ : G) ^ k = ((z : ↥(NormX (x₁ : G))) : G) := by
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at this
    exact this
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, ← hk', ← conj_zpow,
    hbx, inv_zpow]

theorem nonempty_mulEquiv_normX
    (hM : ModelChecks) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nonempty (↥(NormX (x₁ : G)) ≃* B0) := by
  obtain ⟨e⟩ := D.nonempty_mulEquiv_mclCover S
  let φ₂ : K0 ≃* McLMultiplier.MclCover := K0EquivCover hM.tab hM.cover hM.struct
  let μ : ((centralizer ({(x₁ : G)} : Set G)).subgroupOf (NormX (x₁ : G))) ≃* K0 :=
    ((subgroupOfEquivOfLe centralizer_le_normX).trans e).trans φ₂.symm
  obtain ⟨ν, -⟩ := exists_mulEquiv_extend_of_mclCover
    (D.index_centralizer_normX S.pow₁ S.rho₁) (K0_index_two hM.tab hM.cover hM.struct) φ₂ μ
    (inv_centre_normX D S) (inv_centre_K0 hM)
  exact ⟨ν⟩

theorem exists_mulEquiv_borel_marked
    (hM : ModelChecks) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ φ : ↥(NormX (x₁ : G)) ≃* B0,
      φ ⟨(x₁ : G), self_mem_normX (x₁ : G)⟩ = xB ∧
      (φ ⟨(x₂ : G), x₂_mem_normX D S⟩ = yB ∨ φ ⟨(x₂ : G), x₂_mem_normX D S⟩ = yB⁻¹) ∧
      (φ ⟨(x₃ : G), x₃_mem_normX D S⟩ = wB ∨ φ ⟨(x₃ : G), x₃_mem_normX D S⟩ = wB⁻¹) := by
  obtain ⟨ν⟩ := nonempty_mulEquiv_normX hM D S
  have hn3 : orderOf (⟨(x₁ : G), self_mem_normX (x₁ : G)⟩ : ↥(NormX (x₁ : G))) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact LyData.orderOf_x₁ S
  obtain ⟨ν₁, h₁⟩ := exists_equiv_map_eq_xB hM hn3 (normal_zpowers_normX (x₁ : G)) ν
  obtain ⟨ν₂, h₂, h₂'⟩ := exists_mulEquiv_line hM D S ν₁ h₁
  obtain ⟨u, hu₂, -, hu₁, -⟩ := D.exists_swap23 S
  have huc : (u : G) * (x₁ : G) = (x₁ : G) * (u : G) := by
    have := congrArg Subtype.val hu₁
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hu₂' : (u : G) * (x₂ : G) * (u : G)⁻¹ = (x₃ : G) := by
    have := congrArg Subtype.val hu₂
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  let uB : ↥(NormX (x₁ : G)) :=
    ⟨(u : G), centralizer_le_normX (mem_centralizer_singleton_iff.2 huc)⟩
  have hu : uB * ⟨(x₂ : G), x₂_mem_normX D S⟩ * uB⁻¹ = ⟨(x₃ : G), x₃_mem_normX D S⟩ :=
    Subtype.ext hu₂'
  have hc : (⟨(x₃ : G), x₃_mem_normX D S⟩ : ↥(NormX (x₁ : G))) * ⟨(x₂ : G), x₂_mem_normX D S⟩ =
      ⟨(x₂ : G), x₂_mem_normX D S⟩ * ⟨(x₃ : G), x₃_mem_normX D S⟩ :=
    Subtype.ext (D.comm₃₂ S)
  have hne1 : (⟨(x₃ : G), x₃_mem_normX D S⟩ : ↥(NormX (x₁ : G))) ≠
      ⟨(x₂ : G), x₂_mem_normX D S⟩ := by
    intro h
    have h' : x₃ = x₂ := Subtype.ext (congrArg (fun b : ↥(NormX (x₁ : G)) => (b : G)) h)
    have := congrArg ρ h'
    rw [S.rho₃, S.rho₂] at this
    exact absurd this (by decide)
  have hne2 : (⟨(x₃ : G), x₃_mem_normX D S⟩ : ↥(NormX (x₁ : G))) ≠
      (⟨(x₂ : G), x₂_mem_normX D S⟩ : ↥(NormX (x₁ : G)))⁻¹ := by
    intro h
    have h' : x₃ = x₂⁻¹ := Subtype.ext (congrArg (fun b : ↥(NormX (x₁ : G)) => (b : G)) h)
    have := congrArg ρ h'
    rw [S.rho₃, map_inv, S.rho₂] at this
    exact absurd this (by decide)
  obtain ⟨ν₃, h₃₁, h₃₂, h₃₃⟩ := exists_equiv_lines hM ν₂ h₂ h₂' hu hc hne1 hne2
    (card_normalizer_zpowers_x₂ D S)
  exact exists_equiv_sign hM ν₃ h₃₁ h₃₂ h₃₃

theorem exists_mulEquiv_borel
    (hM : ModelChecks) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ φ : ↥(NormX (x₁ : G)) ≃* B0,
      φ ⟨(x₁ : G), self_mem_normX (x₁ : G)⟩ = xB ∧
      ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Y0 ∧
      ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
        (NormX (x₁ : G))).map φ.toMonoidHom = Tx ∧
      ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
        (NormX (x₁ : G))).map φ.toMonoidHom = Txy := by
  obtain ⟨φ, h1, h2, h3⟩ := exists_mulEquiv_borel_marked hM D S
  obtain ⟨e1, e2, e3⟩ := map_normalizers_of_mulEquiv (self_mem_normX (x₁ : G))
    (x₂_mem_normX D S) (x₃_mem_normX D S) φ h1 h2 h3
  exact ⟨φ, h1, e1, e2, e3⟩

theorem card_Y0_of_borel
    (hM : ModelChecks) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : Nat.card Y0 = 349920 := by
  obtain ⟨φ, -, h2, -, -⟩ := exists_mulEquiv_borel hM D S
  have hle : NN (x₁ : G) (x₂ : G) ≤ NormX (x₁ : G) := inf_le_left
  rw [← h2, Subgroup.card_map_of_injective φ.injective,
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  exact D.card_NN' S

end Stage1

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
