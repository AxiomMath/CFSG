module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Rank1
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.C57

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure Setup (H M₀ R K : Subgroup G) : Prop where
  sylow : IsSylowTwoOf R H
  charTwo : CharTwo H
  uniqueMax : ∃ N : Subgroup G, IsUniqueMaxOver H R N
  R_le : R ≤ M₀
  normal_R : M₀ ≤ Subgroup.normalizer (R : Set G)
  noCommon : C5.NoCommonNormal R H M₀
  block : IsChi0Block H K
  K_eq : K = oTwoUpper H
  thompson : ⁅K, thompsonJ R⁆ = K
  maxN : IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (K : Set G))

theorem oTwoUpper_sup_eq [Finite G] {T H : Subgroup G} (hT : IsSylowTwoOf T H) :
    oTwoUpper H ⊔ T = H := by
  classical
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  refine le_antisymm (sup_le hKH hT.1) ?_
  have h1 : (oTwoUpper H ⊔ T).relIndex H ∣ T.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : (oTwoUpper H ⊔ T).relIndex H ∣ (oTwoUpper H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  have h3 : ∃ m : ℕ, (oTwoUpper H).relIndex H = 2 ^ m := by
    have hn : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper H)
    have hp : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H h.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := h3
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    apply hT.2.2
    have h2d : 2 ∣ (oTwoUpper H ⊔ T).relIndex H := by
      rw [hj]
      exact dvd_pow_self 2 hne
    exact h2d.trans h1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

namespace Setup

variable {H M₀ R K : Subgroup G} (h : Setup H M₀ R K)
include h

theorem short : IsShort2 K := h.block.1.1

theorem K_le : K ≤ H := h.K_eq ▸ oTwoUpper_le H

theorem le_normalizer_K : H ≤ Subgroup.normalizer (K : Set G) :=
  h.K_eq ▸ le_normalizer_oTwoUpper H

theorem R_le_H : R ≤ H := h.sylow.1

theorem isPGroup_R : IsPGroup 2 R := h.sylow.2.1

theorem R_le_normalizer_K : R ≤ Subgroup.normalizer (K : Set G) := h.R_le_H.trans h.le_normalizer_K

theorem pCoreOf_le_R : pCoreOf 2 H ≤ R := h.sylow.pCoreOf_le

variable [Finite G]

theorem H_eq : H = K ⊔ R := by
  rw [h.K_eq]
  exact (oTwoUpper_sup_eq h.sylow).symm

theorem blockQ_le_pCoreOf : blockQ K ≤ pCoreOf 2 H :=
  C1.le_pCoreOf_of_normalized ((C1.blockQ_le K).trans h.K_le)
    (fun _ hg => C1.mem_normalizer_blockQ (h.le_normalizer_K hg)) (C1.blockQ_isPGroup K)

theorem blockU_le_pCoreOf : blockU K ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ h.short).trans h.blockQ_le_pCoreOf

theorem blockU_le_R : blockU K ≤ R := h.blockU_le_pCoreOf.trans h.pCoreOf_le_R

theorem inf_centralizer_eq : H ⊓ Subgroup.centralizer (blockU K : Set G) = pCoreOf 2 H :=
  C1.inf_centralizer_blockU_eq h.short h.K_le h.le_normalizer_K fun _ hg => by
    rw [h.K_eq]; exact exists_pow_mem_oTwoUpper H hg

theorem R_inf_centralizer_eq : R ⊓ Subgroup.centralizer (blockU K : Set G) = pCoreOf 2 H := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨h.pCoreOf_le_R hg, ?_⟩)
  · rw [← h.inf_centralizer_eq]; exact ⟨h.R_le_H hg.1, hg.2⟩
  · rw [← h.inf_centralizer_eq] at hg; exact hg.2

theorem pCoreOf_comm {p u : G} (hp : p ∈ pCoreOf 2 H) (hu : u ∈ blockU K) : p * u = u * p := by
  rw [← h.inf_centralizer_eq] at hp
  exact (Subgroup.mem_centralizer_iff.mp hp.2 u hu).symm

theorem comm_mem_blockU {p k : G} (hp : p ∈ pCoreOf 2 H) (hk : k ∈ K) :
    p * k * p⁻¹ * k⁻¹ ∈ blockU K :=
  C1.commutator_mem_blockU_of_mem_blockQ h.short
    (fun _ hl => C1.commutator_mem_blockQ_of_mem_pCoreOf h.K_le h.le_normalizer_K hp hl) k hk

omit [Finite G] in
theorem blockU_ne_bot : blockU K ≠ ⊥ := by
  intro hU
  have hlt := h.short.2.2.2.2.1
  rw [hU] at hlt
  exact not_lt_bot hlt

theorem R_ne_bot : R ≠ ⊥ := fun hR => h.blockU_ne_bot (le_bot_iff.mp (hR ▸ h.blockU_le_R))

theorem mem_normalizer_H {g : G} (hg : g ∈ M₀ ⊓ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [h.H_eq]
  exact C1.mem_normalizer_sup hg.2 (h.normal_R hg.1)

theorem mem_normalizer_pCoreOf {g : G} (hg : g ∈ M₀ ⊓ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  C1.mem_normalizer_blockQ (L := H) (h.mem_normalizer_H hg)

theorem eq_bot {x : G} (hx : x ∈ M₀) (hxK : x ∉ Subgroup.normalizer (K : Set G))
    {X : Subgroup G} (hXR : X ≤ R) (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hNX : M₀ ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  by_contra hne
  refine h.noCommon X hXR hne (h.H_eq ▸ sup_le hKX hRX) ?_
  have hle : M₀ ⊓ Subgroup.normalizer (K : Set G) ≤ M₀ ⊓ Subgroup.normalizer (X : Set G) :=
    le_inf inf_le_left hNX
  have hlt : M₀ ⊓ Subgroup.normalizer (K : Set G) < M₀ ⊓ Subgroup.normalizer (X : Set G) := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have hmem : x ∈ M₀ ⊓ Subgroup.normalizer (X : Set G) := ⟨hx, hxX⟩
    rw [← heq] at hmem
    exact hxK hmem.2
  have := h.maxN.2 _ hlt inf_le_left
  exact fun g hg => (this.symm ▸ hg : g ∈ M₀ ⊓ Subgroup.normalizer (X : Set G)).2

theorem conj_le_R {x : G} (hx : x ∈ M₀) : conjSubgroup (blockU K) x ≤ R := by
  have := C5.conjSubgroup_mono h.blockU_le_R x
  rwa [C5.conjSubgroup_eq_self (h.normal_R hx)] at this

theorem exists_conj_not_le : ∃ x ∈ M₀, ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  set P := pCoreOf 2 H with hP
  set X : Subgroup G := ⨅ (m : G) (_ : m ∈ M₀), conjSubgroup P m with hX
  have hmem : ∀ y, y ∈ X ↔ ∀ m ∈ M₀, m * y * m⁻¹ ∈ P := by
    intro y
    simp only [hX, Subgroup.mem_iInf, mem_conjSubgroup_iff]
  have hXP : X ≤ P := fun y hy => by simpa using (hmem y).1 hy 1 (one_mem _)
  have hUX : blockU K ≤ X := by
    intro u hu
    refine (hmem u).2 fun m hm => hcon m⁻¹ (inv_mem hm) ?_
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hu
  have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    constructor
    · intro hy m hm
      have := hy (m * g) (mul_mem hm hg)
      simpa [mul_assoc] using this
    · intro hy m hm
      have := hy (m * g⁻¹) (mul_mem hm (inv_mem hg))
      simpa [mul_assoc] using this
  have hconjK : ∀ k ∈ K, ∀ y ∈ X, k * y * k⁻¹ ∈ X := by
    intro k hk y hy
    have hc : k * y * k⁻¹ * y⁻¹ ∈ blockU K := by
      have := inv_mem (h.comm_mem_blockU (hXP hy) hk)
      simpa [mul_assoc] using this
    have : k * y * k⁻¹ = (k * y * k⁻¹ * y⁻¹) * y := by group
    rw [this]
    exact mul_mem (hUX hc) hy
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconjK k hk y hy, fun hy => ?_⟩
    have := hconjK k⁻¹ (inv_mem hk) _ hy
    simpa [mul_assoc] using this
  have hne : X ≠ ⊥ := fun hb => h.blockU_ne_bot (le_bot_iff.mp (hb ▸ hUX))
  exact h.noCommon X (hXP.trans h.pCoreOf_le_R) hne
    (h.H_eq ▸ sup_le hKX (h.R_le.trans hM₀X)) hM₀X

theorem conj_inv_not_le {x : G} (hx : x ∈ M₀)
    (hx1 : ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H) :
    ¬ conjSubgroup (blockU K) x⁻¹ ≤ pCoreOf 2 H := by
  intro hle
  apply hx1
  intro v hv
  rw [← h.R_inf_centralizer_eq]
  refine ⟨h.conj_le_R hx hv, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : x * u * x⁻¹ ∈ conjSubgroup (blockU K) x⁻¹ := by
    rw [mem_conjSubgroup_iff]; simpa [mul_assoc] using hu
  have hv' : x * v * x⁻¹ ∈ blockU K := mem_conjSubgroup_iff.mp hv
  have hc := h.pCoreOf_comm (hle hu') hv'
  have : x * (u * v) * x⁻¹ = x * (v * u) * x⁻¹ := by
    calc x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
      _ = (x * v * x⁻¹) * (x * u * x⁻¹) := hc
      _ = x * (v * u) * x⁻¹ := by group
  simpa using this

theorem not_mem_normalizer {x : G} (hx1 : ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H) :
    x ∉ Subgroup.normalizer (K : Set G) := by
  intro hxK
  apply hx1
  rw [C5.conjSubgroup_eq_self (C1.mem_normalizer_blockU hxK)]
  exact h.blockU_le_pCoreOf

theorem isMinimalParabolic : IsMinimalParabolic R H := by
  obtain ⟨N, hN⟩ := h.uniqueMax
  have hNmem : N ∈ maxOver H R := by rw [hN]; exact Set.mem_singleton N
  refine ⟨h.sylow, fun hHR => h.noCommon R le_rfl h.R_ne_bot hHR h.normal_R, N, hNmem.2,
    hNmem.1.1, fun X hRX hXH => ?_⟩
  obtain ⟨N', hN'max, hXN'⟩ := exists_isMaxSubgroupIn hXH
  have hN' : N' ∈ maxOver H R := ⟨hN'max, hRX.trans hXN'⟩
  rw [hN] at hN'
  exact hXN'.trans (le_of_eq hN')

end Setup

theorem relIndex_eq_two {M₀ N Y : Subgroup G} {x : G} (hmax : IsMaxSubgroupIn M₀ N)
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hx : x ∈ M₀) (hxY : conjSubgroup Y x ≠ Y)
    (horb : ∀ m ∈ M₀, conjSubgroup Y m = Y ∨ conjSubgroup Y m = conjSubgroup Y x) :
    N.relIndex M₀ = 2 := by
  set St := M₀ ⊓ Subgroup.normalizer (Y : Set G) with hSt
  have hxSt : x ∉ St := fun hm => hxY (conjSubgroup_eq_iff_mem_normalizer.mpr hm.2)
  have hNSt : N = St := by
    by_contra hne
    have hlt : N < St := lt_of_le_of_ne (le_inf hmax.1.le hNY) hne
    have := hmax.2 St hlt inf_le_left
    exact hxSt (this.symm ▸ hx)
  have hxx : conjSubgroup Y (x * x) = Y := by
    rcases horb (x * x) (mul_mem hx hx) with h1 | h1
    · exact h1
    · exfalso
      apply hxY
      have := congrArg (fun A => conjSubgroup A x⁻¹) h1
      simp only [conjSubgroup_conjSubgroup, mul_inv_cancel_right, mul_inv_cancel,
        conjSubgroup_one] at this
      exact this
  rw [hNSt, Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hx⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hSt, Subgroup.mem_inf]
  have hb := b.2
  have hbx : (b : G) * x ∈ M₀ := mul_mem hb hx
  simp only [hb, hbx, true_and]
  rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_eq_iff_mem_normalizer,
    ← conjSubgroup_conjSubgroup]
  rcases horb b hb with h1 | h1
  · rw [h1]
    exact Or.inr ⟨rfl, hxY⟩
  · rw [h1, conjSubgroup_conjSubgroup, hxx]
    refine Or.inl ⟨rfl, fun h2 => hxY (h1 ▸ h2)⟩

end CFSG.Quasithin.H13.Ch4.C57
