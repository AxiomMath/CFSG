module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaShult
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaBender
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaStmts
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.CGT.T75D.ComponentSplit
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.PCore.FixedSubgroupCore

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

section CentralProduct

variable {Y : Type} [Group Y] [Finite Y]

structure Cor2BetaB4Core (K : Subgroup Y) : Prop where
  fac : ∀ y : Y, ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set Y), y = k * c
  two : ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∃ n : ℕ, z ^ (2 ^ n) = 1

variable {K : Subgroup Y}

theorem Cor2BetaB4Core.normal (h : Cor2BetaB4Core K) : K.Normal := by
  refine ⟨fun x hx y => ?_⟩
  obtain ⟨k, hk, c, hc, rfl⟩ := h.fac y
  have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  have : k * c * x * (k * c)⁻¹ = k * x * k⁻¹ := by
    calc k * c * x * (k * c)⁻¹ = k * (c * x) * c⁻¹ * k⁻¹ := by group
      _ = k * (x * c) * c⁻¹ * k⁻¹ := by rw [hcx]
      _ = k * x * k⁻¹ := by group
  rw [this]
  exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)

theorem Cor2BetaB4Core.central_mem (h : Cor2BetaB4Core K) (P : Sylow 2 Y) {z : Y} (hz : z ∈ K)
    (hzc : ∀ k ∈ K, k * z = z * k) : z ∈ (P : Subgroup Y) := by
  have hcen : ∀ y : Y, y * z = z * y := by
    intro y
    obtain ⟨k, hk, c, hc, rfl⟩ := h.fac y
    have h1 : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc z hz
    calc k * c * z = k * (c * z) := by group
      _ = k * (z * c) := by rw [h1]
      _ = (k * z) * c := by group
      _ = (z * k) * c := by rw [hzc k hk]
      _ = z * (k * c) := by group
  obtain ⟨n, hn⟩ := h.two z hz hzc
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
      one_zpow]
    rfl
  haveI : (Subgroup.zpowers z).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : g * z ^ m * g⁻¹ = z ^ m := by
      rw [(Commute.zpow_right (show Commute g z from hcen g) m).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem_zpowers z m
  exact IsPGroup.le_sylow_of_normal hp P (Subgroup.mem_zpowers z)

theorem Cor2BetaB4Core.mem_sylow_of_mul (h : Cor2BetaB4Core K) (P : Sylow 2 Y) {k c : Y}
    (hk : k ∈ K) (hc : c ∈ Subgroup.centralizer (K : Set Y)) (hkc : k * c ∈ (P : Subgroup Y)) :
    k ∈ (P : Subgroup Y) := by
  set C : Subgroup Y := Subgroup.centralizer (K : Set Y) with hC
  have hKC : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb a ha
  let πK : Subgroup Y :=
    { carrier := {x | x ∈ K ∧ ∃ c ∈ C, x * c ∈ (P : Subgroup Y)}
      mul_mem' := by
        rintro a b ⟨ha, c₁, hc₁, hac⟩ ⟨hb, c₂, hc₂, hbc⟩
        refine ⟨K.mul_mem ha hb, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        have e : a * b * (c₁ * c₂) = (a * c₁) * (b * c₂) := by
          calc a * b * (c₁ * c₂) = a * (b * c₁) * c₂ := by group
            _ = a * (c₁ * b) * c₂ := by rw [hKC b hb c₁ hc₁]
            _ = (a * c₁) * (b * c₂) := by group
        rw [e]
        exact (P : Subgroup Y).mul_mem hac hbc
      one_mem' := ⟨K.one_mem, 1, C.one_mem, by simpa using (P : Subgroup Y).one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, c₁, hc₁, hac⟩
        refine ⟨K.inv_mem ha, c₁⁻¹, C.inv_mem hc₁, ?_⟩
        have e : a⁻¹ * c₁⁻¹ = (a * c₁)⁻¹ := by
          calc a⁻¹ * c₁⁻¹ = (c₁ * a)⁻¹ := by group
            _ = (a * c₁)⁻¹ := by rw [← hKC a ha c₁ hc₁]
        rw [e]
        exact (P : Subgroup Y).inv_mem hac }
  let πC : Subgroup Y :=
    { carrier := {x | x ∈ C ∧ ∃ a ∈ K, a * x ∈ (P : Subgroup Y)}
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁, a₁, ha₁, h₁⟩ ⟨hb₂, a₂, ha₂, h₂⟩
        refine ⟨C.mul_mem hb₁ hb₂, a₁ * a₂, K.mul_mem ha₁ ha₂, ?_⟩
        have e : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
          calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
            _ = a₁ * (b₁ * a₂) * b₂ := by rw [hKC a₂ ha₂ b₁ hb₁]
            _ = (a₁ * b₁) * (a₂ * b₂) := by group
        rw [e]
        exact (P : Subgroup Y).mul_mem h₁ h₂
      one_mem' := ⟨C.one_mem, 1, K.one_mem, by simpa using (P : Subgroup Y).one_mem⟩
      inv_mem' := by
        rintro b ⟨hb, a₁, ha₁, h₁⟩
        refine ⟨C.inv_mem hb, a₁⁻¹, K.inv_mem ha₁, ?_⟩
        have e : a₁⁻¹ * b⁻¹ = (a₁ * b)⁻¹ := by
          calc a₁⁻¹ * b⁻¹ = (b * a₁)⁻¹ := by group
            _ = (a₁ * b)⁻¹ := by rw [← hKC a₁ ha₁ b hb]
        rw [e]
        exact (P : Subgroup Y).inv_mem h₁ }
  have hπK : IsPGroup 2 πK := by
    intro x
    obtain ⟨hxK, c₁, hc₁, hxc⟩ := x.2
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨(x : Y) * c₁, hxc⟩
    have hm' : ((x : Y) * c₁) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcomm : Commute (x : Y) c₁ := hKC _ hxK _ hc₁
    rw [hcomm.mul_pow] at hm'
    have hzK : (x : Y) ^ 2 ^ m ∈ K := K.pow_mem hxK _
    have hzc : ∀ a ∈ K, a * (x : Y) ^ 2 ^ m = (x : Y) ^ 2 ^ m * a := by
      intro a ha
      have h1 : (x : Y) ^ 2 ^ m = (c₁ ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm'
      rw [h1]
      have := hKC a ha (c₁ ^ 2 ^ m)⁻¹ (C.inv_mem (C.pow_mem hc₁ _))
      exact this
    obtain ⟨n, hn⟩ := h.two _ hzK hzc
    refine ⟨m + n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_add, pow_mul, hn]
    rfl
  have hπC : IsPGroup 2 πC := by
    intro x
    obtain ⟨hxC, a₁, ha₁, hxa⟩ := x.2
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨a₁ * (x : Y), hxa⟩
    have hm' : (a₁ * (x : Y)) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcomm : Commute a₁ (x : Y) := hKC _ ha₁ _ hxC
    rw [hcomm.mul_pow] at hm'
    have hzK : (x : Y) ^ 2 ^ m ∈ K := by
      have h1 : (x : Y) ^ 2 ^ m = (a₁ ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hm'
      rw [h1]
      exact K.inv_mem (K.pow_mem ha₁ _)
    have hzc : ∀ a ∈ K, a * (x : Y) ^ 2 ^ m = (x : Y) ^ 2 ^ m * a := fun a ha =>
      hKC a ha _ (C.pow_mem hxC _)
    obtain ⟨n, hn⟩ := h.two _ hzK hzc
    refine ⟨m + n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_add, pow_mul, hn]
    rfl
  have hnorm : πC ≤ Subgroup.normalizer (πK : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hbC : b ∈ C := hb.1
    constructor
    · intro hx
      have : b * x * b⁻¹ = x := by
        rw [← hKC x hx.1 b hbC]
        group
      rw [this]
      exact hx
    · intro hx
      have h1 : b * x * b⁻¹ ∈ πK := hx
      have hy := hKC _ h1.1 b hbC
      have e : x = b * x * b⁻¹ := by
        calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
          _ = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hy]
          _ = b * x * b⁻¹ := by group
      rw [e]
      exact h1
  have hπ2 : IsPGroup 2 (πC ⊔ πK : Subgroup Y) := hπC.to_sup_of_normal_right' hπK hnorm
  have hle : (P : Subgroup Y) ≤ πC ⊔ πK := by
    intro p hp
    obtain ⟨k', hk', c', hc', rfl⟩ := h.fac p
    have h1 : k' ∈ πK := ⟨hk', c', hc', hp⟩
    have h2 : c' ∈ πC := ⟨hc', k', hk', hp⟩
    have := Subgroup.mul_mem_sup h2 h1
    rwa [← hKC k' hk' c' hc'] at this
  have hEq := P.is_maximal' hπ2 hle
  have hkπ : k ∈ πK := ⟨hk, c, hc, hkc⟩
  rw [← hEq]
  exact Subgroup.mem_sup_right hkπ

theorem Cor2BetaB4Core.exists_sylow (h : Cor2BetaB4Core K) (P : Sylow 2 Y) :
    ∃ PK : Sylow 2 ↥K, ∀ x : ↥K, x ∈ (PK : Subgroup ↥K) ↔ (x : Y) ∈ (P : Subgroup Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.normal
  obtain ⟨PK, hPK⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  refine ⟨PK, fun x => ?_⟩
  rw [hPK, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

theorem cor2Beta_b4_mem_smul {A : Type} [Group A] (T : Sylow 2 A) (g y : A) :
    y ∈ ((g • T : Sylow 2 A) : Subgroup A) ↔ g⁻¹ * y * g ∈ (T : Subgroup A) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem Cor2BetaB4Core.exists_conj (h : Cor2BetaB4Core K) (P P' : Sylow 2 Y) :
    ∃ k ∈ K, ∀ x ∈ K, x ∈ (P' : Subgroup Y) → k * x * k⁻¹ ∈ (P : Subgroup Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PK, hPK⟩ := h.exists_sylow P
  obtain ⟨PK', hPK'⟩ := h.exists_sylow P'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K PK' PK
  refine ⟨g, g.2, fun x hx hxP' => ?_⟩
  have h1 : (⟨x, hx⟩ : ↥K) ∈ (PK' : Subgroup ↥K) := (hPK' _).mpr hxP'
  have h2 : g * ⟨x, hx⟩ * g⁻¹ ∈ ((g • PK' : Sylow 2 ↥K) : Subgroup ↥K) := by
    rw [cor2Beta_b4_mem_smul]
    have e : g⁻¹ * (g * (⟨x, hx⟩ : ↥K) * g⁻¹) * g = ⟨x, hx⟩ := by group
    rw [e]
    exact h1
  rw [hg] at h2
  exact (hPK _).mp h2

end CentralProduct

section CentralQuotient

variable {A : Type} [Group A] [Finite A]

theorem cor2Beta_b4_lift_normalizer {T : Subgroup A} (hZT : Subgroup.center A ≤ T)
    {n : A ⧸ Subgroup.center A}
    (hn : n ∈ Subgroup.normalizer ((T.map (QuotientGroup.mk' (Subgroup.center A)) :
      Subgroup _) : Set (A ⧸ Subgroup.center A))) :
    ∃ x : A, QuotientGroup.mk' (Subgroup.center A) x = n ∧
      x ∈ Subgroup.normalizer (T : Set A) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center A) n
  refine ⟨x, rfl, ?_⟩
  set q := QuotientGroup.mk' (Subgroup.center A) with hq
  have h1 := Subgroup.comap_normalizer_eq_of_surjective (T.map q)
    (QuotientGroup.mk'_surjective (Subgroup.center A))
  have h2 : (T.map q).comap q = T := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZT]
  rw [h2] at h1
  have : x ∈ (Subgroup.normalizer ((T.map q : Subgroup _) :
      Set (A ⧸ Subgroup.center A))).comap q := hn
  rw [h1] at this
  exact this

theorem cor2Beta_b4_abelian (T : Sylow 2 A) (hZT : Subgroup.center A ≤ (T : Subgroup A))
    {τ : A} (hτT : τ ∈ (T : Subgroup A)) (hτc : ∀ x ∈ (T : Subgroup A), x * τ = τ * x)
    (hτZ : τ ∉ Subgroup.center A)
    (htrans : ∀ x ∈ (T : Subgroup A).map (QuotientGroup.mk' (Subgroup.center A)),
      ∀ y ∈ (T : Subgroup A).map (QuotientGroup.mk' (Subgroup.center A)), x ≠ 1 → y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (((T : Subgroup A).map (QuotientGroup.mk' (Subgroup.center A)) :
        Subgroup _) : Set (A ⧸ Subgroup.center A)), n⁻¹ * x * n = y) :
    ∀ a ∈ (T : Subgroup A), ∀ b ∈ (T : Subgroup A), a * b = b * a := by
  classical
  set q := QuotientGroup.mk' (Subgroup.center A) with hq
  set CT : Subgroup A := Subgroup.centralizer ((T : Subgroup A) : Set A) with hCT
  have hZC : Subgroup.center A ≤ CT := fun z hz => by
    rw [hCT, Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.mp hz g
  have hτC : τ ∈ CT := by
    rw [hCT, Subgroup.mem_centralizer_iff]
    exact hτc
  have hs1 : q τ ≠ 1 := fun h => hτZ ((QuotientGroup.eq_one_iff τ).mp h)
  have key : ∀ a ∈ (T : Subgroup A), a ∈ CT := by
    intro a ha
    by_cases haq : q a = 1
    · exact hZC ((QuotientGroup.eq_one_iff a).mp haq)
    · obtain ⟨n, hn, hna⟩ := htrans (q τ) ⟨τ, hτT, rfl⟩ (q a) ⟨a, ha, rfl⟩ hs1 haq
      obtain ⟨x, hxn, hx⟩ := cor2Beta_b4_lift_normalizer hZT hn
      have h1 : q (x⁻¹ * τ * x) = q a := by
        rw [map_mul, map_mul, map_inv, hxn]
        exact hna
      have hz : (x⁻¹ * τ * x)⁻¹ * a ∈ Subgroup.center A := QuotientGroup.eq.mp h1
      have hxτ : x⁻¹ * τ * x ∈ CT := by
        rw [hCT, Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : x * y * x⁻¹ ∈ (T : Subgroup A) := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
        have h2 := hτc _ hy'
        calc y * (x⁻¹ * τ * x) = x⁻¹ * ((x * y * x⁻¹) * τ) * x := by group
          _ = x⁻¹ * (τ * (x * y * x⁻¹)) * x := by rw [h2]
          _ = x⁻¹ * τ * x * y := by group
      have : a = (x⁻¹ * τ * x) * ((x⁻¹ * τ * x)⁻¹ * a) := by group
      rw [this]
      exact CT.mul_mem hxτ (hZC hz)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (key a ha) b hb).symm

theorem cor2Beta_b4_isPGroup_zpowers {M : Type} [Group M] {u : M} (hu : u * u = 1) :
    IsPGroup 2 (Subgroup.zpowers u) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hu2 : u ^ 2 = 1 := by rw [sq]; exact hu
  rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hu2]

theorem cor2Beta_b4_isPGroup_pair {M : Type} [Group M] {u v : M} (hu : u * u = 1) (hv : v * v = 1)
    (huv : u * v = v * u) : IsPGroup 2 (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup M) := by
  have hnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set M) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute u v from huv) k)).eq
  rw [sup_comm]
  exact (cor2Beta_b4_isPGroup_zpowers hv).to_sup_of_normal_right'
    (cor2Beta_b4_isPGroup_zpowers hu) hnorm

theorem cor2Beta_b4_lift_commute (T : Sylow 2 A) (hZT : Subgroup.center A ≤ (T : Subgroup A))
    (hTab : ∀ a ∈ (T : Subgroup A), ∀ b ∈ (T : Subgroup A), a * b = b * a)
    {τ : A} (hτT : τ ∈ (T : Subgroup A)) (hτ2 : τ * τ ∈ Subgroup.center A) (x₀ : A)
    (hy : QuotientGroup.mk' (Subgroup.center A) (x₀ * τ * x₀⁻¹) *
        QuotientGroup.mk' (Subgroup.center A) τ =
      QuotientGroup.mk' (Subgroup.center A) τ *
        QuotientGroup.mk' (Subgroup.center A) (x₀ * τ * x₀⁻¹)) :
    (x₀ * τ * x₀⁻¹) * τ = τ * (x₀ * τ * x₀⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (Subgroup.center A) with hq
  have hq0 : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hs2 : q τ * q τ = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hτ2
  have hττ : x₀ * τ * x₀⁻¹ * (x₀ * τ * x₀⁻¹) = τ * τ := by
    have h := Subgroup.mem_center_iff.mp hτ2 x₀
    calc x₀ * τ * x₀⁻¹ * (x₀ * τ * x₀⁻¹) = x₀ * (τ * τ) * x₀⁻¹ := by group
      _ = (τ * τ) * x₀ * x₀⁻¹ := by rw [h]
      _ = τ * τ := by group
  have hy2 : q (x₀ * τ * x₀⁻¹) * q (x₀ * τ * x₀⁻¹) = 1 := by
    rw [← map_mul, hττ, map_mul]
    exact hs2
  have hR := cor2Beta_b4_isPGroup_pair hs2 hy2 hy.symm
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (A ⧸ Subgroup.center A) (T.mapSurjective hq0) Q
  obtain ⟨x₁, rfl⟩ := hq0 g
  have hlift : ∀ u : A, q u ∈ ((Q : Subgroup _)) → x₁⁻¹ * u * x₁ ∈ (T : Subgroup A) := by
    intro u hu
    rw [← hg, cor2Beta_b4_mem_smul, Sylow.coe_mapSurjective] at hu
    obtain ⟨a₁, ha₁, hae⟩ := hu
    have h1 : q (x₁⁻¹ * u * x₁) = q a₁ := by
      rw [map_mul, map_mul, map_inv]
      exact hae.symm
    have h2 : a₁⁻¹ * (x₁⁻¹ * u * x₁) ∈ Subgroup.center A := QuotientGroup.eq.mp h1.symm
    have : x₁⁻¹ * u * x₁ = a₁ * (a₁⁻¹ * (x₁⁻¹ * u * x₁)) := by group
    rw [this]
    exact (T : Subgroup A).mul_mem ha₁ (hZT h2)
  have h1 := hlift τ (hRQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have h2 := hlift (x₀ * τ * x₀⁻¹) (hRQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have h3 := hTab _ h2 _ h1
  calc x₀ * τ * x₀⁻¹ * τ = x₁ * ((x₁⁻¹ * (x₀ * τ * x₀⁻¹) * x₁) * (x₁⁻¹ * τ * x₁)) * x₁⁻¹ := by group
    _ = x₁ * ((x₁⁻¹ * τ * x₁) * (x₁⁻¹ * (x₀ * τ * x₀⁻¹) * x₁)) * x₁⁻¹ := by rw [h3]
    _ = τ * (x₀ * τ * x₀⁻¹) := by group

section BenderCerts


theorem cor2Beta_b4_isBender [IsSimpleGroup (A ⧸ Subgroup.center A)]
    (hL : goldschmidtSimpleType (A ⧸ Subgroup.center A))
    (T : Sylow 2 A) (hZT : Subgroup.center A ≤ (T : Subgroup A))
    {τ : A} (hτT : τ ∈ (T : Subgroup A)) (hτc : ∀ x ∈ (T : Subgroup A), x * τ = τ * x)
    (hτZ : τ ∉ Subgroup.center A) (hτ2 : τ * τ ∈ Subgroup.center A)
    (hAw : ∀ x : A, (x * τ * x⁻¹) * τ = τ * (x * τ * x⁻¹) → x * τ * x⁻¹ ∈ (T : Subgroup A)) :
    CFSG.BenderSuzuki.IsBenderGroup (A ⧸ Subgroup.center A) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hB : CFSG.Open.fusionIsBenderGroup (A ⧸ Subgroup.center A)
  · exact CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup hB
  set q := QuotientGroup.mk' (Subgroup.center A) with hq
  have hq0 : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hK : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
          Nonempty ((A ⧸ Subgroup.center A) ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card (A ⧸ Subgroup.center A) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty ((A ⧸ Subgroup.center A) ≃* goldschmidtJ1) := by
    rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h4 | h5 | h6
    · exact absurd (Or.inl ⟨f, by omega, ⟨e⟩⟩) hB
    · exact absurd (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)) hB
    · exact absurd (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)) hB
    · exact Or.inl h4
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h6)
  obtain ⟨-, -, -, htrans⟩ :=
    CFSG.Goldschmidt.GoldType.elementary_of_clauses (K := A ⧸ Subgroup.center A) hK
      (Sylow.mapSurjective hq0 T)
  have hs1 : q τ ≠ 1 := fun h => hτZ ((QuotientGroup.eq_one_iff τ).mp h)
  have hTab := cor2Beta_b4_abelian T hZT hτT hτc hτZ htrans
  refine cor2Beta_isBender_of_wcl hL (Sylow.mapSurjective hq0 T) hs1 ⟨τ, hτT, rfl⟩ ?_
  rintro y ⟨m, hm⟩ hys
  obtain ⟨x₀, rfl⟩ := hq0 m
  have hy' : q (x₀ * τ * x₀⁻¹) = y := by
    rw [hm, map_mul, map_mul, map_inv]
  rw [← hy'] at hys
  have hcomm := cor2Beta_b4_lift_commute T hZT hTab hτT hτ2 x₀ hys
  have hmem := hAw x₀ hcomm
  rw [← hy']
  exact ⟨_, hmem, rfl⟩

end BenderCerts

theorem cor2Beta_b4_exists_two {M : Type} [Group M] (Zc : Subgroup M) (h4 : 4 ≤ Nat.card Zc)
    (a : M) :
    ∃ w₁ ∈ Zc, ∃ w₂ ∈ Zc, w₁ ≠ 1 ∧ w₁ ≠ a ∧ w₂ ≠ 1 ∧ w₂ ≠ a ∧ w₁ ≠ w₂ := by
  classical
  have hfin : (Zc : Set M).Finite := by
    by_contra hinf
    have : Nat.card Zc = 0 := Set.Infinite.card_eq_zero hinf
    omega
  have hcard : (Zc : Set M).ncard = Nat.card Zc := (Nat.card_coe_set_eq _).symm
  have h2 : ({1, a} : Set M).ncard < (Zc : Set M).ncard := by
    have := Set.ncard_insert_le (1 : M) ({a} : Set M)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨w₁, hw₁, hw₁'⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h2 (Set.toFinite _)
  have h3 : ({1, a, w₁} : Set M).ncard < (Zc : Set M).ncard := by
    have h1 := Set.ncard_insert_le (1 : M) ({a, w₁} : Set M)
    have h2 := Set.ncard_insert_le a ({w₁} : Set M)
    rw [Set.ncard_singleton] at h2
    omega
  obtain ⟨w₂, hw₂, hw₂'⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h3 (Set.toFinite _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw₁' hw₂'
  exact ⟨w₁, hw₁, w₂, hw₂, hw₁'.1, hw₁'.2, hw₂'.1, hw₂'.2.1, fun h => hw₂'.2.2 h.symm⟩

theorem cor2Beta_b4_conj_central (T : Subgroup A) {τ x : A} (hτT : τ ∈ T)
    (hτc : ∀ y ∈ T, y * τ = τ * y) (hx : x ∈ Subgroup.normalizer (T : Set A)) :
    x * τ * x⁻¹ ∈ T ∧ ∀ y ∈ T, y * (x * τ * x⁻¹) = (x * τ * x⁻¹) * y := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hx τ).mp hτT, fun y hy => ?_⟩
  have hy' : x⁻¹ * y * x ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set A)).inv_mem hx) y).mp hy
    simpa using this
  have h := hτc _ hy'
  calc y * (x * τ * x⁻¹) = x * ((x⁻¹ * y * x) * τ) * x⁻¹ := by group
    _ = x * (τ * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
    _ = (x * τ * x⁻¹) * y := by group

section Bender113


theorem cor2Beta_b4_two_elements
    (hBend : CFSG.BenderSuzuki.IsBenderGroup (A ⧸ Subgroup.center A))
    (T : Sylow 2 A) (hZT : Subgroup.center A ≤ (T : Subgroup A))
    {τ : A} (hτT : τ ∈ (T : Subgroup A)) (hτc : ∀ x ∈ (T : Subgroup A), x * τ = τ * x)
    (hτZ : τ ∉ Subgroup.center A) (hτ2 : τ * τ ∈ Subgroup.center A) :
    ∃ x₁ x₂ : A, x₁ ∈ Subgroup.normalizer ((T : Subgroup A) : Set A) ∧
      x₂ ∈ Subgroup.normalizer ((T : Subgroup A) : Set A) ∧
      x₁ * τ * x₁⁻¹ * τ⁻¹ ∉ Subgroup.center A ∧ x₂ * τ * x₂⁻¹ * τ⁻¹ ∉ Subgroup.center A ∧
      (x₁ * τ * x₁⁻¹ * τ⁻¹) * (x₂ * τ * x₂⁻¹ * τ⁻¹) ∉ Subgroup.center A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (Subgroup.center A) with hq
  have hq0 : Function.Surjective q := QuotientGroup.mk'_surjective _
  set TL := Sylow.mapSurjective hq0 T with hTLdef
  have hTLc : (TL : Subgroup (A ⧸ Subgroup.center A)) = (T : Subgroup A).map q := rfl
  have hs1 : q τ ≠ 1 := fun h => hτZ ((QuotientGroup.eq_one_iff τ).mp h)
  have hs2 : q τ * q τ = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hτ2
  have hsT : q τ ∈ (TL : Subgroup (A ⧸ Subgroup.center A)) := ⟨τ, hτT, rfl⟩
  have hsc : ∀ y ∈ (TL : Subgroup (A ⧸ Subgroup.center A)), Commute y (q τ) := by
    rintro _ ⟨a, ha, rfl⟩
    show q a * q τ = q τ * q a
    rw [← map_mul, ← map_mul, hτc a ha]
  obtain ⟨w₁, hw₁, w₂, hw₂, hw₁1, hw₁s, hw₂1, hw₂s, hw₁₂⟩ :=
    cor2Beta_b4_exists_two (Subgroup.center ↥(TL : Subgroup (A ⧸ Subgroup.center A)))
      (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.four_le_card_center hBend TL)
      (⟨q τ, hsT⟩ : ↥(TL : Subgroup (A ⧸ Subgroup.center A)))
  have hzmem : ∀ w ∈ Subgroup.center ↥(TL : Subgroup (A ⧸ Subgroup.center A)),
      ∀ y ∈ (TL : Subgroup (A ⧸ Subgroup.center A)), Commute y (w : A ⧸ Subgroup.center A) := by
    intro w hw y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩)
  have hinv : (q τ)⁻¹ = q τ := inv_eq_of_mul_eq_one_right hs2
  have hconj : ∀ w ∈ Subgroup.center ↥(TL : Subgroup (A ⧸ Subgroup.center A)),
      (w : A ⧸ Subgroup.center A) ≠ 1 → ∃ x : A,
        x ∈ Subgroup.normalizer ((T : Subgroup A) : Set A) ∧
        q x * q τ * (q x)⁻¹ = (w : A ⧸ Subgroup.center A) := by
    intro w hw hw1
    obtain ⟨g, hgN, hg⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hBend
      TL ⟨hsT, hsc⟩ hs1 ⟨w.2, hzmem w hw⟩ hw1
    have hgN' : g ∈ Subgroup.normalizer (((T : Subgroup A).map q : Subgroup _) :
        Set (A ⧸ Subgroup.center A)) := hgN
    obtain ⟨x, hxg, hxN⟩ := cor2Beta_b4_lift_normalizer hZT hgN'
    exact ⟨x, hxN, by rw [hxg]; exact hg⟩
  have hw₁1' : (w₁ : A ⧸ Subgroup.center A) ≠ 1 := fun h => hw₁1 (Subtype.ext h)
  have hw₂1' : (w₂ : A ⧸ Subgroup.center A) ≠ 1 := fun h => hw₂1 (Subtype.ext h)
  have hw₁s' : (w₁ : A ⧸ Subgroup.center A) ≠ q τ := fun h => hw₁s (Subtype.ext h)
  have hw₂s' : (w₂ : A ⧸ Subgroup.center A) ≠ q τ := fun h => hw₂s (Subtype.ext h)
  have hw₁₂' : (w₁ : A ⧸ Subgroup.center A) ≠ (w₂ : A ⧸ Subgroup.center A) :=
    fun h => hw₁₂ (Subtype.ext h)
  obtain ⟨x₁, hx₁N, hx₁⟩ := hconj w₁ hw₁ hw₁1'
  obtain ⟨x₂, hx₂N, hx₂⟩ := hconj w₂ hw₂ hw₂1'
  have hqv : ∀ x : A, q (x * τ * x⁻¹ * τ⁻¹) = q x * q τ * (q x)⁻¹ * q τ := by
    intro x
    simp only [map_mul, map_inv, hinv]
  have hz₂2 : (w₂ : A ⧸ Subgroup.center A) * (w₂ : A ⧸ Subgroup.center A) = 1 := by
    have := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hBend TL w₂.2
      (fun y hy => (hzmem w₂ hw₂ y hy).symm)
    exact this
  refine ⟨x₁, x₂, hx₁N, hx₂N, ?_, ?_, ?_⟩
  · intro h
    have h1 : q (x₁ * τ * x₁⁻¹ * τ⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h
    rw [hqv, hx₁] at h1
    exact hw₁s' (by rw [eq_inv_of_mul_eq_one_left h1, hinv])
  · intro h
    have h1 : q (x₂ * τ * x₂⁻¹ * τ⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h
    rw [hqv, hx₂] at h1
    exact hw₂s' (by rw [eq_inv_of_mul_eq_one_left h1, hinv])
  · intro h
    have h1 : q ((x₁ * τ * x₁⁻¹ * τ⁻¹) * (x₂ * τ * x₂⁻¹ * τ⁻¹)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h
    rw [map_mul, hqv, hqv, hx₁, hx₂] at h1
    have hc : (w₂ : A ⧸ Subgroup.center A) * q τ = q τ * (w₂ : A ⧸ Subgroup.center A) :=
      (hsc _ w₂.2).eq
    have h2 : (w₁ : A ⧸ Subgroup.center A) * (w₂ : A ⧸ Subgroup.center A) = 1 := by
      calc (w₁ : A ⧸ Subgroup.center A) * (w₂ : A ⧸ Subgroup.center A)
          = (w₁ : A ⧸ Subgroup.center A) * (w₂ : A ⧸ Subgroup.center A) * (q τ * q τ) := by
            rw [hs2, mul_one]
        _ = (w₁ : A ⧸ Subgroup.center A) * ((w₂ : A ⧸ Subgroup.center A) * q τ) * q τ := by group
        _ = (w₁ : A ⧸ Subgroup.center A) * (q τ * (w₂ : A ⧸ Subgroup.center A)) * q τ := by
            rw [hc]
        _ = (w₁ : A ⧸ Subgroup.center A) * q τ * ((w₂ : A ⧸ Subgroup.center A) * q τ) := by group
        _ = 1 := h1
    exact hw₁₂' ((eq_inv_of_mul_eq_one_left h2).trans (inv_eq_of_mul_eq_one_right hz₂2))

end Bender113

end CentralQuotient

section ClaimData

variable {Y : Type} [Group Y] [Finite Y]

theorem cor2Beta_b4_mul_comm {K : Subgroup Y} {a b c : Y} (ha : a ∈ K) (hb : b ∈ K)
    (hc : c ∈ Subgroup.centralizer (K : Set Y)) (hab : a * b = b * a) :
    (a * c) * (b * c) = (b * c) * (a * c) := by
  have h1 : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a ha
  have h2 : b * c = c * b := Subgroup.mem_centralizer_iff.mp hc b hb
  calc a * c * (b * c) = a * (c * b) * c := by group
    _ = a * (b * c) * c := by rw [← h2]
    _ = (a * b) * c * c := by group
    _ = (b * a) * c * c := by rw [hab]
    _ = b * (a * c) * c := by group
    _ = b * (c * a) * c := by rw [h1]
    _ = b * c * (a * c) := by group

structure Cor2BetaB4Out (K P : Subgroup Y) (t v : Y) : Prop where
  mem_K : v ∈ K
  mem_P : v ∈ P
  sq : v * v = 1
  weak : ∃ u ∈ CFSG.LargeExtraspecial.S11.wclSet t, v = u * t
  noncentral : ∃ k ∈ K, k * v ≠ v * k

section Claim


theorem cor2Beta_b4_claim {K : Subgroup Y} (hK : Cor2BetaB4Core K)
    [IsSimpleGroup (↥K ⧸ Subgroup.center ↥K)]
    (hGt : goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K))
    (P : Sylow 2 Y) {t : Y} (ht2 : t * t = 1) (htP : t ∈ (P : Subgroup Y))
    (htc : ∀ s ∈ (P : Subgroup Y), s * t = t * s) (hnc : ∃ y ∈ K, y * t ≠ t * y)
    (hw : ∀ y : Y, (∃ m : Y, y = m * t * m⁻¹) → y * t = t * y → y ∈ (P : Subgroup Y)) :
    CFSG.BenderSuzuki.IsBenderGroup (↥K ⧸ Subgroup.center ↥K) ∧
      ∃ v₁ v₂ : Y, Cor2BetaB4Out K (P : Subgroup Y) t v₁ ∧ Cor2BetaB4Out K (P : Subgroup Y) t v₂ ∧
        v₁ * v₂ = v₂ * v₁ ∧ ∃ k ∈ K, k * (v₁ * v₂) ≠ (v₁ * v₂) * k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hKn : K.Normal := hK.normal
  obtain ⟨τ₀, hτ₀K, c, hc, htτc⟩ := hK.fac t
  have hcK : ∀ k ∈ K, k * c = c * k := fun k hk => Subgroup.mem_centralizer_iff.mp hc k hk
  have hτ₀P : τ₀ ∈ (P : Subgroup Y) := hK.mem_sylow_of_mul P hτ₀K hc (htτc ▸ htP)
  have hcP : c ∈ (P : Subgroup Y) := by
    have : c = τ₀⁻¹ * t := by rw [htτc]; group
    rw [this]
    exact (P : Subgroup Y).mul_mem ((P : Subgroup Y).inv_mem hτ₀P) htP
  obtain ⟨PK, hPK⟩ := hK.exists_sylow P
  let τ : ↥K := ⟨τ₀, hτ₀K⟩
  have hτT : τ ∈ (PK : Subgroup ↥K) := (hPK τ).mpr hτ₀P
  have hτc : ∀ x ∈ (PK : Subgroup ↥K), x * τ = τ * x := by
    intro x hx
    have hxP : (x : Y) ∈ (P : Subgroup Y) := (hPK x).mp hx
    have h1 : (x : Y) * t = t * x := htc _ hxP
    apply Subtype.ext
    have h2 : (x : Y) * τ₀ * c = (τ₀ * x) * c := by
      calc (x : Y) * τ₀ * c = x * t := by rw [htτc]; group
        _ = t * x := h1
        _ = τ₀ * c * x := by rw [htτc]
        _ = τ₀ * (c * x) := by group
        _ = τ₀ * (x * c) := by rw [← hcK x x.2]
        _ = τ₀ * x * c := by group
    exact mul_right_cancel h2
  have hτZ : τ ∉ Subgroup.center ↥K := by
    intro hz
    obtain ⟨y, hyK, hy⟩ := hnc
    apply hy
    have h1 : (⟨y, hyK⟩ : ↥K) * τ = τ * ⟨y, hyK⟩ := Subgroup.mem_center_iff.mp hz ⟨y, hyK⟩
    have h2 : y * τ₀ = τ₀ * y := congrArg Subtype.val h1
    calc y * t = y * τ₀ * c := by rw [htτc]; group
      _ = τ₀ * y * c := by rw [h2]
      _ = τ₀ * (y * c) := by group
      _ = τ₀ * (c * y) := by rw [hcK y hyK]
      _ = t * y := by rw [htτc]; group
  have hττ : τ₀ * τ₀ * (c * c) = 1 := by
    calc τ₀ * τ₀ * (c * c) = τ₀ * (c * τ₀) * c := by
          rw [← hcK τ₀ hτ₀K]; group
      _ = t * t := by rw [htτc]; group
      _ = 1 := ht2
  have hττc : τ₀ * τ₀ ∈ Subgroup.centralizer (K : Set Y) := by
    have : τ₀ * τ₀ = c⁻¹ * c⁻¹ := by
      calc τ₀ * τ₀ = τ₀ * τ₀ * (c * c) * (c⁻¹ * c⁻¹) := by group
        _ = c⁻¹ * c⁻¹ := by rw [hττ]; group
    rw [this]
    exact (Subgroup.centralizer (K : Set Y)).mul_mem ((Subgroup.centralizer (K : Set Y)).inv_mem hc)
      ((Subgroup.centralizer (K : Set Y)).inv_mem hc)
  have hτ2 : τ * τ ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hττc g g.2)
  have hZT : Subgroup.center ↥K ≤ (PK : Subgroup ↥K) := by
    intro z hz
    refine (hPK z).mpr (hK.central_mem P z.2 fun k hk => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  have hconjK : ∀ x : ↥K, (x : Y) * τ₀ * (x : Y)⁻¹ ∈ K := fun x =>
    K.mul_mem (K.mul_mem x.2 hτ₀K) (K.inv_mem x.2)
  have hconjt : ∀ x : ↥K, (x : Y) * t * (x : Y)⁻¹ = ((x : Y) * τ₀ * (x : Y)⁻¹) * c := by
    intro x
    rw [htτc]
    calc (x : Y) * (τ₀ * c) * (x : Y)⁻¹ = (x : Y) * τ₀ * (c * (x : Y)⁻¹) := by group
      _ = (x : Y) * τ₀ * ((x : Y)⁻¹ * c) := by rw [← hcK _ (K.inv_mem x.2)]
      _ = ((x : Y) * τ₀ * (x : Y)⁻¹) * c := by group
  have hcommt : ∀ x : ↥K,
      ((x : Y) * τ₀ * (x : Y)⁻¹) * τ₀ = τ₀ * ((x : Y) * τ₀ * (x : Y)⁻¹) →
      ((x : Y) * t * (x : Y)⁻¹) * t = t * ((x : Y) * t * (x : Y)⁻¹) := by
    intro x hx
    rw [hconjt x, htτc]
    exact cor2Beta_b4_mul_comm (hconjK x) hτ₀K hc hx
  have hAw : ∀ x : ↥K, (x * τ * x⁻¹) * τ = τ * (x * τ * x⁻¹) →
      x * τ * x⁻¹ ∈ (PK : Subgroup ↥K) := by
    intro x hx
    have hmem := hw _ ⟨x, rfl⟩ (hcommt x (congrArg Subtype.val hx))
    rw [hconjt x] at hmem
    exact (hPK (x * τ * x⁻¹)).mpr (hK.mem_sylow_of_mul P (hconjK x) hc hmem)
  have hBend : CFSG.BenderSuzuki.IsBenderGroup (↥K ⧸ Subgroup.center ↥K) :=
    cor2Beta_b4_isBender hGt PK hZT hτT hτc hτZ hτ2 hAw
  refine ⟨hBend, ?_⟩
  obtain ⟨x₁, x₂, hx₁N, hx₂N, hv₁, hv₂, hv₁₂⟩ :=
    cor2Beta_b4_two_elements hBend PK hZT hτT hτc hτZ hτ2
  have hcc : c * c = τ₀⁻¹ * τ₀⁻¹ := by
    calc c * c = (τ₀ * τ₀)⁻¹ * (τ₀ * τ₀ * (c * c)) := by group
      _ = τ₀⁻¹ * τ₀⁻¹ := by rw [hττ]; group
  have hvx : ∀ x : ↥K, (x : Y) * t * (x : Y)⁻¹ * t = ((x * τ * x⁻¹ * τ⁻¹ : ↥K) : Y) := by
    intro x
    rw [hconjt x]
    change _ = (x : Y) * τ₀ * (x : Y)⁻¹ * τ₀⁻¹
    calc (x : Y) * τ₀ * (x : Y)⁻¹ * c * t
        = (x : Y) * τ₀ * (x : Y)⁻¹ * (c * (τ₀ * c)) := by rw [htτc]; group
      _ = (x : Y) * τ₀ * (x : Y)⁻¹ * ((c * τ₀) * c) := by group
      _ = (x : Y) * τ₀ * (x : Y)⁻¹ * ((τ₀ * c) * c) := by rw [← hcK τ₀ hτ₀K]
      _ = (x : Y) * τ₀ * (x : Y)⁻¹ * τ₀ * (c * c) := by group
      _ = (x : Y) * τ₀ * (x : Y)⁻¹ * τ₀⁻¹ := by rw [hcc]; group
  have hout : ∀ x : ↥K, x ∈ Subgroup.normalizer ((PK : Subgroup ↥K) : Set ↥K) →
      x * τ * x⁻¹ * τ⁻¹ ∉ Subgroup.center ↥K →
      Cor2BetaB4Out K (P : Subgroup Y) t ((x * τ * x⁻¹ * τ⁻¹ : ↥K) : Y) ∧
        (x : Y) * t * (x : Y)⁻¹ * t = t * ((x : Y) * t * (x : Y)⁻¹) ∧
        (x * τ * x⁻¹ ∈ (PK : Subgroup ↥K) ∧ ∀ y ∈ (PK : Subgroup ↥K), y * (x * τ * x⁻¹) =
          (x * τ * x⁻¹) * y) := by
    intro x hx hnz
    obtain ⟨hτxT, hτxc⟩ := cor2Beta_b4_conj_central (PK : Subgroup ↥K) hτT hτc hx
    have hcomm : ((x : Y) * t * (x : Y)⁻¹) * t = t * ((x : Y) * t * (x : Y)⁻¹) :=
      hcommt x (congrArg Subtype.val (hτxc τ hτT).symm)
    have hu : (x : Y) * t * (x : Y)⁻¹ ∈ (P : Subgroup Y) := hw _ ⟨x, rfl⟩ hcomm
    have hu2 : ((x : Y) * t * (x : Y)⁻¹) * ((x : Y) * t * (x : Y)⁻¹) = 1 := by
      calc ((x : Y) * t * (x : Y)⁻¹) * ((x : Y) * t * (x : Y)⁻¹)
          = (x : Y) * (t * t) * (x : Y)⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hcomm, hτxT, hτxc⟩
    · exact (x * τ * x⁻¹ * τ⁻¹ : ↥K).2
    · rw [← hvx x]
      exact (P : Subgroup Y).mul_mem hu htP
    · rw [← hvx x]
      calc (x : Y) * t * (x : Y)⁻¹ * t * ((x : Y) * t * (x : Y)⁻¹ * t)
          = ((x : Y) * t * (x : Y)⁻¹) * (t * ((x : Y) * t * (x : Y)⁻¹)) * t := by group
        _ = ((x : Y) * t * (x : Y)⁻¹) * (((x : Y) * t * (x : Y)⁻¹) * t) * t := by rw [hcomm]
        _ = (((x : Y) * t * (x : Y)⁻¹) * ((x : Y) * t * (x : Y)⁻¹)) * (t * t) := by group
        _ = 1 := by rw [hu2, ht2]; group
    · exact ⟨(x : Y) * t * (x : Y)⁻¹, ⟨x, rfl, hcomm⟩, (hvx x).symm⟩
    · by_contra hcon
      push Not at hcon
      apply hnz
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon (g : Y) g.2)
  have h₁ := hout x₁ hx₁N hv₁
  have h₂ := hout x₂ hx₂N hv₂
  obtain ⟨-, -, ha₁T, ha₁c⟩ := h₁
  obtain ⟨-, -, ha₂T, ha₂c⟩ := h₂
  refine ⟨_, _, (hout x₁ hx₁N hv₁).1, (hout x₂ hx₂N hv₂).1, ?_, ?_⟩
  · have hbT : τ⁻¹ ∈ (PK : Subgroup ↥K) := (PK : Subgroup ↥K).inv_mem hτT
    have c12 : Commute (x₁ * τ * x₁⁻¹) (x₂ * τ * x₂⁻¹) := (ha₁c _ ha₂T).symm
    have c1b : Commute (x₁ * τ * x₁⁻¹) τ⁻¹ := (ha₁c _ hbT).symm
    have c2b : Commute (x₂ * τ * x₂⁻¹) τ⁻¹ := (ha₂c _ hbT).symm
    have hcommK : Commute (x₁ * τ * x₁⁻¹ * τ⁻¹) (x₂ * τ * x₂⁻¹ * τ⁻¹) :=
      (c12.mul_right c1b).mul_left ((c2b.symm).mul_right (Commute.refl _))
    exact congrArg Subtype.val hcommK.eq
  · by_contra hcon
    push Not at hcon
    apply hv₁₂
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon (g : Y) g.2)

end Claim

end ClaimData

section Transport

theorem cor2Beta_b4_quotCenter_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nonempty ((A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B)) := by
  refine ⟨QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    have := Subgroup.mem_center_iff.mp ha g'
    simpa using congrArg e this
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    show e.symm x ∈ Subgroup.center A
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    have := Subgroup.mem_center_iff.mp hx (e g)
    simpa using this

theorem cor2Beta_b4_isBender_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.BenderSuzuki.IsBenderGroup X) : CFSG.BenderSuzuki.IsBenderGroup Y := by
  rcases h with ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩
  · exact .isPSL2 n hn (e.symm.trans e')
  · exact .isSuzuki n hn (e.symm.trans e')
  · exact .isPSU3 n hn (e.symm.trans e')

theorem cor2Beta_b4_noncentral_conj {X : Type} [Group X] {t : X} {Kb : Subgroup X}
    (hKH : Kb ≤ Subgroup.normalClosure ({t} : Set X))
    (hKs : IsSimpleGroup (↥Kb ⧸ Subgroup.center ↥Kb)) :
    ∃ g : X, ∃ y ∈ Kb, y * (g * t * g⁻¹) ≠ (g * t * g⁻¹) * y := by
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.normalClosure ({t} : Set X) ≤ Subgroup.centralizer (Kb : Set X) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨a₁, ha₁, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    have : a₁ = t := ha₁
    subst this
    exact (hcon g y hy).symm.symm
  haveI : Subsingleton (↥Kb ⧸ Subgroup.center ↥Kb) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_centralizer_iff.mp (hle (hKH a.2)) g g.2
    have h2 := Subgroup.mem_centralizer_iff.mp (hle (hKH b.2)) g g.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : X) * ((a : X)⁻¹ * b) = ((g : X) * (a : X)⁻¹) * b := by group
      _ = ((a : X)⁻¹ * g) * b := by
          rw [Commute.eq (Commute.inv_right (show Commute (g : X) a from h1))]
      _ = (a : X)⁻¹ * (g * b) := by group
      _ = (a : X)⁻¹ * (b * g) := by rw [h2]
      _ = ((a : X)⁻¹ * b) * g := by group
  obtain ⟨x, y, hxy⟩ := hKs.toNontrivial.exists_pair_ne
  exact hxy (Subsingleton.elim x y)

end Transport

section Final


theorem cor2Beta_b4_final {X : Type} [Group X] [Finite X] {Hb Kb : Subgroup X} [hHn : Hb.Normal]
    (hKH : Kb ≤ Hb) (hcore : Cor2BetaB4Core (Kb.subgroupOf Hb))
    (hKs : IsSimpleGroup (↥Kb ⧸ Subgroup.center ↥Kb))
    (hGt : goldschmidtSimpleType (↥Kb ⧸ Subgroup.center ↥Kb))
    (S : Sylow 2 X) {t : X} (ht2 : t * t = 1) (htS : t ∈ (S : Subgroup X))
    (htc : ∀ s ∈ (S : Subgroup X), s * t = t * s)
    (hab : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl t))
    (hHt : Hb ≤ Subgroup.normalClosure ({t} : Set X)) (htH : t ∈ Hb) :
    CFSG.BenderSuzuki.IsBenderGroup (↥Kb ⧸ Subgroup.center ↥Kb) ∧
      ∃ V : Subgroup X, V ≤ Kb ∧ V ≤ CFSG.LargeExtraspecial.S11.wcl t ∧ IsKleinFour ↥V ∧
        ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Kb, k * v ≠ v * k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWS, hsc⟩ := CFSG.LargeExtraspecial.S11.wcl_stronglyClosed S htS htc hab
  set KY : Subgroup ↥Hb := Kb.subgroupOf Hb with hKY
  let eK : ↥KY ≃* ↥Kb := Subgroup.subgroupOfEquivOfLe hKH
  obtain ⟨eQ⟩ := cor2Beta_b4_quotCenter_equiv eK
  haveI := hKs
  haveI hKYs : IsSimpleGroup (↥KY ⧸ Subgroup.center ↥KY) := eQ.isSimpleGroup
  have hGtY : goldschmidtSimpleType (↥KY ⧸ Subgroup.center ↥KY) :=
    CFSG.CGT.T75D.goldschmidtSimpleType_of_mulEquiv eQ.symm hGt
  obtain ⟨g₀, y₀, hy₀K, hy₀⟩ := cor2Beta_b4_noncentral_conj (t := t) (hKH.trans hHt) hKs
  set S' : Sylow 2 X := g₀ • S with hS'
  set t' : X := g₀ * t * g₀⁻¹ with ht'
  have hmemS' : ∀ y : X, y ∈ (S' : Subgroup X) ↔ g₀⁻¹ * y * g₀ ∈ (S : Subgroup X) :=
    cor2Beta_b4_mem_smul S g₀
  have ht'2 : t' * t' = 1 := by
    calc g₀ * t * g₀⁻¹ * (g₀ * t * g₀⁻¹) = g₀ * (t * t) * g₀⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have ht'S' : t' ∈ (S' : Subgroup X) := by
    rw [hmemS']
    have : g₀⁻¹ * t' * g₀ = t := by rw [ht']; group
    rw [this]
    exact htS
  have ht'c : ∀ s ∈ (S' : Subgroup X), s * t' = t' * s := by
    intro s hs
    have h1 := htc _ ((hmemS' s).mp hs)
    calc s * t' = g₀ * ((g₀⁻¹ * s * g₀) * t) * g₀⁻¹ := by rw [ht']; group
      _ = g₀ * (t * (g₀⁻¹ * s * g₀)) * g₀⁻¹ := by rw [h1]
      _ = t' * s := by rw [ht']; group
  have ht'H : t' ∈ Hb := hHn.conj_mem t htH g₀
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S (N := Hb)
  obtain ⟨P', hP'⟩ := CFSG.Glauberman.sylow_inf_normal S' (N := Hb)
  have hPmem : ∀ y : ↥Hb, y ∈ (P : Subgroup ↥Hb) ↔ (y : X) ∈ (S : Subgroup X) := by
    intro y
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  have hP'mem : ∀ y : ↥Hb, y ∈ (P' : Subgroup ↥Hb) ↔ (y : X) ∈ (S' : Subgroup X) := by
    intro y
    rw [hP', Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  have hwcl : ∀ u : ↥Hb, (∃ m : ↥Hb, u = m * (⟨t', ht'H⟩ : ↥Hb) * m⁻¹) →
      u * (⟨t', ht'H⟩ : ↥Hb) = (⟨t', ht'H⟩ : ↥Hb) * u →
      g₀⁻¹ * (u : X) * g₀ ∈ CFSG.LargeExtraspecial.S11.wclSet t := by
    rintro u ⟨m, hm⟩ huc
    have huX : (u : X) = (m : X) * t' * (m : X)⁻¹ := congrArg Subtype.val hm
    have hucX : (u : X) * t' = t' * (u : X) := congrArg Subtype.val huc
    refine ⟨g₀⁻¹ * (m : X) * g₀, ?_, ?_⟩
    · rw [huX, ht']
      group
    · calc g₀⁻¹ * (u : X) * g₀ * t = g₀⁻¹ * ((u : X) * t') * g₀ := by rw [ht']; group
        _ = g₀⁻¹ * (t' * (u : X)) * g₀ := by rw [hucX]
        _ = t * (g₀⁻¹ * (u : X) * g₀) := by rw [ht']; group
  have hnc : ∃ y ∈ KY, y * (⟨t', ht'H⟩ : ↥Hb) ≠ (⟨t', ht'H⟩ : ↥Hb) * y :=
    ⟨⟨y₀, hKH hy₀K⟩, hy₀K, fun h => hy₀ (congrArg Subtype.val h)⟩
  have hw : ∀ y : ↥Hb, (∃ m : ↥Hb, y = m * (⟨t', ht'H⟩ : ↥Hb) * m⁻¹) →
      y * (⟨t', ht'H⟩ : ↥Hb) = (⟨t', ht'H⟩ : ↥Hb) * y → y ∈ (P' : Subgroup ↥Hb) := by
    intro y hy hyc
    rw [hP'mem, hmemS']
    exact hWS (CFSG.LargeExtraspecial.S11.subset_wcl t (hwcl y hy hyc))
  obtain ⟨hBendY, v₁, v₂, hv₁, hv₂, hv₁₂, hv₁₂nc⟩ := cor2Beta_b4_claim hcore hGtY P'
    (Subtype.ext ht'2) ((hP'mem _).mpr ht'S')
    (fun s hs => Subtype.ext (ht'c _ ((hP'mem s).mp hs))) hnc hw
  have hBendKb := cor2Beta_b4_isBender_of_mulEquiv eQ hBendY
  obtain ⟨k, hkK, hk⟩ := hcore.exists_conj P P'
  have hout : ∀ v : ↥Hb, Cor2BetaB4Out KY (P' : Subgroup ↥Hb) (⟨t', ht'H⟩ : ↥Hb) v →
      ((k * v * k⁻¹ : ↥Hb) : X) ∈ Kb ∧ ((k * v * k⁻¹ : ↥Hb) : X) ∈ (S : Subgroup X) ∧
        ((k * v * k⁻¹ : ↥Hb) : X) * ((k * v * k⁻¹ : ↥Hb) : X) = 1 ∧
        ((k * v * k⁻¹ : ↥Hb) : X) ∈ CFSG.LargeExtraspecial.S11.wcl t ∧
        ∃ k' ∈ Kb, k' * ((k * v * k⁻¹ : ↥Hb) : X) ≠ ((k * v * k⁻¹ : ↥Hb) : X) * k' := by
    intro v hv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact KY.mul_mem (KY.mul_mem hkK hv.mem_K) (KY.inv_mem hkK)
    · exact (hPmem _).mp (hk v hv.mem_K hv.mem_P)
    · have := congrArg (fun z : ↥Hb => (z : X)) (show (k * v * k⁻¹) * (k * v * k⁻¹) = 1 by
        calc (k * v * k⁻¹) * (k * v * k⁻¹) = k * (v * v) * k⁻¹ := by group
          _ = 1 := by rw [hv.sq]; group)
      exact this
    · obtain ⟨u, hu, hvu⟩ := hv.weak
      obtain ⟨m, hm, huc⟩ := hu
      have hu1 := hwcl u ⟨m, hm⟩ huc
      have hb : g₀⁻¹ * (u : X) * g₀ * t ∈ CFSG.LargeExtraspecial.S11.wcl t :=
        mul_mem (CFSG.LargeExtraspecial.S11.subset_wcl t hu1)
          (CFSG.LargeExtraspecial.S11.self_mem_wcl t)
      have hvX : (v : X) = g₀ * (g₀⁻¹ * (u : X) * g₀ * t) * g₀⁻¹ := by
        have : (v : X) = (u : X) * t' := congrArg Subtype.val hvu
        rw [this, ht']
        group
      have haS : (k : X) * g₀ * (g₀⁻¹ * (u : X) * g₀ * t) * ((k : X) * g₀)⁻¹ ∈
          (S : Subgroup X) := by
        have h1 := (hPmem _).mp (hk v hv.mem_K hv.mem_P)
        have e : ((k * v * k⁻¹ : ↥Hb) : X) =
            (k : X) * g₀ * (g₀⁻¹ * (u : X) * g₀ * t) * ((k : X) * g₀)⁻¹ := by
          show (k : X) * (v : X) * (k : X)⁻¹ = _
          rw [hvX]
          group
        rw [← e]
        exact h1
      have := hsc _ hb (((k : X) * g₀)⁻¹) (by simpa using haS)
      have e : ((k * v * k⁻¹ : ↥Hb) : X) =
          (((k : X) * g₀)⁻¹)⁻¹ * (g₀⁻¹ * (u : X) * g₀ * t) * ((k : X) * g₀)⁻¹ := by
        show (k : X) * (v : X) * (k : X)⁻¹ = _
        rw [hvX]
        group
      rw [e]
      exact this
    · obtain ⟨k', hk'K, hk'⟩ := hv.noncentral
      refine ⟨((k * k' * k⁻¹ : ↥Hb) : X), ?_, ?_⟩
      · exact KY.mul_mem (KY.mul_mem hkK hk'K) (KY.inv_mem hkK)
      · intro h
        apply hk'
        have h' : (k * k' * k⁻¹) * (k * v * k⁻¹) = (k * v * k⁻¹) * (k * k' * k⁻¹) := Subtype.ext h
        calc k' * v = k⁻¹ * ((k * k' * k⁻¹) * (k * v * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * v * k⁻¹) * (k * k' * k⁻¹)) * k := by rw [h']
          _ = v * k' := by group
  obtain ⟨hK1, hS1, hsq1, hW1, hnc1⟩ := hout v₁ hv₁
  obtain ⟨hK2, hS2, hsq2, hW2, hnc2⟩ := hout v₂ hv₂
  set a₁ : X := ((k * v₁ * k⁻¹ : ↥Hb) : X) with ha₁
  set a₂ : X := ((k * v₂ * k⁻¹ : ↥Hb) : X) with ha₂
  have hcomm : a₁ * a₂ = a₂ * a₁ := by
    have : (k * v₁ * k⁻¹) * (k * v₂ * k⁻¹) = (k * v₂ * k⁻¹) * (k * v₁ * k⁻¹) := by
      calc (k * v₁ * k⁻¹) * (k * v₂ * k⁻¹) = k * (v₁ * v₂) * k⁻¹ := by group
        _ = k * (v₂ * v₁) * k⁻¹ := by rw [hv₁₂]
        _ = (k * v₂ * k⁻¹) * (k * v₁ * k⁻¹) := by group
    exact congrArg (fun z : ↥Hb => (z : X)) this
  have hnc12 : ∃ k' ∈ Kb, k' * (a₁ * a₂) ≠ (a₁ * a₂) * k' := by
    obtain ⟨k', hk'K, hk'⟩ := hv₁₂nc
    refine ⟨((k * k' * k⁻¹ : ↥Hb) : X), KY.mul_mem (KY.mul_mem hkK hk'K) (KY.inv_mem hkK), ?_⟩
    intro h
    apply hk'
    have h' : (k * k' * k⁻¹) * ((k * v₁ * k⁻¹) * (k * v₂ * k⁻¹)) =
        ((k * v₁ * k⁻¹) * (k * v₂ * k⁻¹)) * (k * k' * k⁻¹) := Subtype.ext h
    calc k' * (v₁ * v₂)
        = k⁻¹ * ((k * k' * k⁻¹) * ((k * v₁ * k⁻¹) * (k * v₂ * k⁻¹))) * k := by group
      _ = k⁻¹ * (((k * v₁ * k⁻¹) * (k * v₂ * k⁻¹)) * (k * k' * k⁻¹)) * k := by rw [h']
      _ = (v₁ * v₂) * k' := by group
  have ha₁1 : a₁ ≠ 1 := by
    intro h
    obtain ⟨k', -, hk'⟩ := hnc1
    exact hk' (by rw [h]; simp)
  have ha₂1 : a₂ ≠ 1 := by
    intro h
    obtain ⟨k', -, hk'⟩ := hnc2
    exact hk' (by rw [h]; simp)
  have ha₁₂ : a₁ ≠ a₂ := by
    intro h
    obtain ⟨k', -, hk'⟩ := hnc12
    have : a₁ * a₂ = 1 := by rw [← h]; exact hsq1
    exact hk' (by rw [this]; simp)
  refine ⟨hBendKb, CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a₁ a₂ hsq1 hsq2 hcomm,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ ({a₁ * a₂, a₁, a₂, 1} : Set X) := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact Kb.mul_mem hK1 hK2
    · exact hK1
    · exact hK2
    · exact Kb.one_mem
  · intro x hx
    have hx' : x ∈ ({a₁ * a₂, a₁, a₂, 1} : Set X) := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact mul_mem hW1 hW2
    · exact hW1
    · exact hW2
    · exact one_mem _
  · exact CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a₁ a₂ hsq1 hsq2 ha₁1
      ha₂1 ha₁₂ hcomm
  · intro v hv hv1
    have hv' : v ∈ ({a₁ * a₂, a₁, a₂, 1} : Set X) := hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
    rcases hv' with rfl | rfl | rfl | rfl
    · exact hnc12
    · exact hnc1
    · exact hnc2
    · exact absurd rfl hv1

end Final

section Glue

theorem cor2Beta_b4_central_two_power {Y : Type} [Group Y] [Finite Y]
    (hO : goldschmidtOddCore Y = ⊥) {z : Y} (hz : ∀ y : Y, y * z = z * y) :
    ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
  have hpos : 0 < orderOf z := orderOf_pos z
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨k, ?_⟩
  set w : Y := z ^ (2 ^ k) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (by positivity) (⟨m, hk⟩ : 2 ^ k ∣ orderOf z), hk]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hwc : ∀ y : Y, y * w = w * y := fun y =>
    (Commute.pow_right (show Commute y z from hz y) _).eq
  haveI hRn : (Subgroup.zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : g * w ^ j * g⁻¹ = w ^ j := by
      rw [(Commute.zpow_right (show Commute g w from hwc g) j).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem_zpowers w j
  have hRodd : Odd (Nat.card (Subgroup.zpowers w)) := by
    rw [Nat.card_zpowers, hwo]
    exact hm
  have hRle : Subgroup.zpowers w ≤ goldschmidtOddCore Y := le_sSup ⟨hRn, hRodd⟩
  rw [hO] at hRle
  exact Subgroup.mem_bot.mp (hRle (Subgroup.mem_zpowers w))

theorem cor2Beta_b4_isComponentOf_top {X : Type} [Group X] {Kb Hb : Subgroup X}
    (hK : IsComponentOf Kb Hb) : IsComponentOf (Kb.subgroupOf Hb) (⊤ : Subgroup ↥Hb) :=
  (CFSG.isComponent_iff_open _).mp
    ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.1).mp
      (CFSG.Assembly.isComponentOf_iff_open.mpr hK))

theorem cor2Beta_b4_core_of_goldschmidt {Q Y : Type} [Group Q] [Group Y] [Finite Y] (ψ : Q ≃* Y)
    (ha : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hc : ∀ K' : Subgroup Q, IsComponentOf K' ⊤ →
      goldschmidtSimpleType (↥K' ⧸ Subgroup.center ↥K'))
    (hO : goldschmidtOddCore Y = ⊥) {K : Subgroup Y} (hKc : IsComponentOf K ⊤) :
    Cor2BetaB4Core K ∧ goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K) := by
  haveI : Finite Q := Finite.of_equiv Y ψ.symm
  set K' : Subgroup Q := K.map ψ.symm.toMonoidHom with hK'
  have hK'c : IsComponentOf K' ⊤ :=
    (CFSG.isComponent_iff_open K').mp
      (CFSG.LocalCores.isComponent_map_mulEquiv ψ.symm ((CFSG.isComponent_iff_open K).mpr hKc))
  have hsup := CFSG.CGT.T75D.comp_sup_centralizer ha hK'c
  haveI hnorm := CFSG.CGT.T75D.comp_normal ha hK'c
  have hfac : ∀ y : Y, ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set Y), y = k * c := by
    intro y
    have hy : ψ.symm y ∈ K' ⊔ Subgroup.centralizer (K' : Set Q) := by
      rw [hsup]
      trivial
    obtain ⟨k', hk', c', hc', hkc⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    obtain ⟨k₀, hk₀, rfl⟩ := hk'
    refine ⟨k₀, hk₀, ψ c', ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp hc' (ψ.symm x) ⟨x, hx, rfl⟩
      have h2 := congrArg ψ this
      simpa using h2
    · have := congrArg ψ hkc
      simpa using this.symm
  have htwo : ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    intro z hz hzc
    have hcen : ∀ y : Y, y * z = z * y := by
      intro y
      obtain ⟨k, hk, c, hc, rfl⟩ := hfac y
      have h1 : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc z hz
      calc k * c * z = k * (c * z) := by group
        _ = k * (z * c) := by rw [h1]
        _ = (k * z) * c := by group
        _ = (z * k) * c := by rw [hzc k hk]
        _ = z * (k * c) := by group
    exact cor2Beta_b4_central_two_power hO hcen
  have hG := hc K' hK'c
  let e1 : ↥K ≃* ↥K' := K.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective
  obtain ⟨e2⟩ := cor2Beta_b4_quotCenter_equiv e1
  exact ⟨⟨hfac, htwo⟩, CFSG.CGT.T75D.goldschmidtSimpleType_of_mulEquiv e2.symm hG⟩

end Glue

section Main

theorem cor2Beta_b4_psi {G : Type} [Group G] (H N : Subgroup G) [N.Normal]
    (hN : N = CFSG.Goldschmidt.oddCoreOf H) :
    Nonempty ((↥H ⧸ goldschmidtOddCore ↥H) ≃* ↥(H.map (QuotientGroup.mk' N))) := by
  let ρ : ↥H →* ↥(H.map (QuotientGroup.mk' N)) := (QuotientGroup.mk' N).subgroupMap H
  have hρ : Function.Surjective ρ := (QuotientGroup.mk' N).subgroupMap_surjective H
  have hker : ρ.ker = goldschmidtOddCore ↥H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' N (x : G) = 1 := congrArg Subtype.val h
      have h2 : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
      rw [hN] at h2
      obtain ⟨y, hy, hyx⟩ := h2
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro h
      apply Subtype.ext
      have : (x : G) ∈ N := by
        rw [hN]
        exact ⟨x, h, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

theorem cor2Beta_b4_oddCore_bot {G : Type} [Group G] [Finite G] (H N : Subgroup G) [N.Normal]
    (hN : N = CFSG.Goldschmidt.oddCoreOf H) :
    goldschmidtOddCore ↥(H.map (QuotientGroup.mk' N)) = ⊥ := by
  obtain ⟨ψ⟩ := cor2Beta_b4_psi H N hN
  rw [CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore]
  refine CFSG.pPrimeCore_eq_bot_of_mulEquiv 2 ψ ?_
  rw [← CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore]
  exact CFSG.Goldschmidt.goldschmidtOddCore_quotient_eq_bot ↥H

theorem cor2Beta_b4_wcl_map {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    (CFSG.LargeExtraspecial.S11.wcl t).map (QuotientGroup.mk' N) =
      CFSG.LargeExtraspecial.S11.wcl (QuotientGroup.mk' N t) := by
  unfold CFSG.LargeExtraspecial.S11.wcl
  rw [MonoidHom.map_closure]
  congr 1
  ext y'
  constructor
  · rintro ⟨y, ⟨m, hm, hc⟩, rfl⟩
    refine ⟨QuotientGroup.mk' N m, ?_, ?_⟩
    · rw [hm]
      simp
    · rw [← map_mul, ← map_mul, hc]
  · intro hy'
    obtain ⟨y, hy, hyy⟩ := cor2Beta_wclSet_lift hN ht1 ht2 hy'
    exact ⟨y, hy, hyy⟩

end Main

section Main2


theorem cor2Beta_component_data {G : Type} [Group G] [Finite G]
    (hGold : Goldschmidt1974)
    {S : Sylow 2 G} {t : G} (hs : ShultSetup S t) {N : Subgroup G} [N.Normal]
    (hN : N = CFSG.Goldschmidt.oddCoreOf (normalClosure ({t} : Set G)))
    {Kb : Subgroup (G ⧸ N)}
    (hK : IsComponentOf Kb ((normalClosure ({t} : Set G)).map (QuotientGroup.mk' N))) :
    CFSG.BenderSuzuki.IsBenderGroup (↥Kb ⧸ Subgroup.center ↥Kb) ∧
      ∃ V : Subgroup (G ⧸ N), V ≤ Kb ∧
        V ≤ (CFSG.LargeExtraspecial.S11.wcl t).map (QuotientGroup.mk' N) ∧ IsKleinFour ↥V ∧
        ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Kb, k * v ≠ v * k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hNodd : Odd (Nat.card N) := by
    rw [hN]
    exact odd_card_oddCoreOf _
  obtain ⟨hWS, hsc⟩ := CFSG.LargeExtraspecial.S11.wcl_stronglyClosed S hs.mem hs.central hs.abelian
  obtain ⟨ha, -, hc⟩ := hGold G S (CFSG.LargeExtraspecial.S11.wcl t) hWS hs.abelian hsc
  have hMH : Subgroup.normalClosure ((CFSG.LargeExtraspecial.S11.wcl t : Subgroup G) : Set G) =
      Subgroup.normalClosure ({t} : Set G) := by
    apply le_antisymm
    · refine Subgroup.normalClosure_le_normal fun y hy => ?_
      refine (Subgroup.closure_le _).mpr ?_ hy
      rintro _ ⟨m, rfl, -⟩
      exact (inferInstance : (Subgroup.normalClosure ({t} : Set G)).Normal).conj_mem t
        (Subgroup.subset_normalClosure (Set.mem_singleton t)) m
    · exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr
        (CFSG.LargeExtraspecial.S11.self_mem_wcl t))
  have hHbt : (Subgroup.normalClosure ({t} : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.normalClosure ({QuotientGroup.mk' N t} : Set (G ⧸ N)) := by
    rw [Subgroup.map_normalClosure _ _ hπs, Set.image_singleton]
  have hKt := hK
  rw [← hMH] at hN hK
  set M : Subgroup G := Subgroup.normalClosure ((CFSG.LargeExtraspecial.S11.wcl t : Subgroup G) :
    Set G) with hM
  have hMn : M.Normal := inferInstance
  haveI hHbn : (M.map (QuotientGroup.mk' N)).Normal := hMn.map _ hπs
  have hKH : Kb ≤ M.map (QuotientGroup.mk' N) := hK.1
  have hOY : goldschmidtOddCore ↥(M.map (QuotientGroup.mk' N)) = ⊥ :=
    cor2Beta_b4_oddCore_bot M N hN
  obtain ⟨ψ⟩ := cor2Beta_b4_psi M N hN
  have hKc := cor2Beta_b4_isComponentOf_top hK
  obtain ⟨hcore, hGtY⟩ := cor2Beta_b4_core_of_goldschmidt ψ ha hc hOY hKc
  obtain ⟨eQ⟩ := cor2Beta_b4_quotCenter_equiv
    (Subgroup.subgroupOfEquivOfLe hKH : ↥(Kb.subgroupOf (M.map (QuotientGroup.mk' N))) ≃* ↥Kb)
  have hGt : goldschmidtSimpleType (↥Kb ⧸ Subgroup.center ↥Kb) :=
    CFSG.CGT.T75D.goldschmidtSimpleType_of_mulEquiv eQ hGtY
  have hKs : IsSimpleGroup (↥Kb ⧸ Subgroup.center ↥Kb) := hK.2.2.2
  have ht1 : QuotientGroup.mk' N t ≠ 1 := by
    intro h
    exact hs.ne_one (cor2Beta_eq_one_of_odd hNodd ((QuotientGroup.eq_one_iff _).mp h) hs.sq)
  have ht2 : QuotientGroup.mk' N t * QuotientGroup.mk' N t = 1 := by
    rw [← map_mul, hs.sq, map_one]
  have htS : QuotientGroup.mk' N t ∈ (Sylow.mapSurjective hπs S : Subgroup (G ⧸ N)) :=
    ⟨t, hs.mem, rfl⟩
  have htc : ∀ s ∈ (Sylow.mapSurjective hπs S : Subgroup (G ⧸ N)),
      s * QuotientGroup.mk' N t = QuotientGroup.mk' N t * s := by
    rintro _ ⟨s, hs', rfl⟩
    rw [← map_mul, ← map_mul, hs.central s hs']
  have hwcl := cor2Beta_b4_wcl_map hNodd hs.ne_one hs.sq
  have hab : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl (QuotientGroup.mk' N t)) := by
    rw [← hwcl]
    exact CFSG.Goldschmidt.isMulCommutative_map hs.abelian _
  have hHt : M.map (QuotientGroup.mk' N) ≤ Subgroup.normalClosure
      ({QuotientGroup.mk' N t} : Set (G ⧸ N)) := by
    rw [hMH, hHbt]
  have htH : QuotientGroup.mk' N t ∈ M.map (QuotientGroup.mk' N) :=
    ⟨t, Subgroup.le_normalClosure (CFSG.LargeExtraspecial.S11.self_mem_wcl t), rfl⟩
  obtain ⟨hB, V, hVK, hVW, hV4, hVnc⟩ := cor2Beta_b4_final hKH hcore hKs hGt
    (Sylow.mapSurjective hπs S) ht2 htS htc hab hHt htH
  exact ⟨hB, V, hVK, by rw [hwcl]; exact hVW, hV4, hVnc⟩

end Main2

theorem cor2Beta_componentData_holds (hGold : Goldschmidt1974) :
    Cor2BetaComponentDataStatement := by
  intro G _ _ S t hs N _ hN Kb hK
  exact cor2Beta_component_data hGold hs hN hK

end CFSG.RankThree.GF2n.Tim77
