module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem isSylowOf_top {p : ℕ} [Fact p.Prime] (T : Sylow p G) :
    CFSG.ABGLocalTools.IsSylowOf p (T : Subgroup G) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, T.isPGroup', ?_⟩
  rw [relIndex_top_right]
  exact T.not_dvd_index

theorem frattini_le_sup {p : ℕ} [Fact p.Prime] {R Y X : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ normalizer (Y : Set G)) (hR : CFSG.ABGLocalTools.IsSylowOf p R Y) :
    X ≤ Y ⊔ (X ⊓ normalizer (R : Set G)) := by
  have hRY : R ≤ Y := ((CFSG.ABGLocalTools.isSylowOf_iff).mp hR).1
  have hRX : R ≤ X := hRY.trans hYX
  have : (Y.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hYX).mpr hXY
  have hR' : CFSG.ABGLocalTools.IsSylowOf p (R.subgroupOf X) (Y.subgroupOf X) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr hRX, inf_eq_left.mpr hYX]
    exact hR
  obtain ⟨P, hP⟩ := hR'
  have h := Sylow.normalizer_sup_eq_top P
  rw [hP, ← subgroupOf_normalizer_eq hRX] at h
  intro x hx
  have hx' : (⟨x, hx⟩ : X) ∈ (normalizer (R : Set G)).subgroupOf X ⊔ Y.subgroupOf X := by
    rw [h]
    exact mem_top _
  have h2 := mem_map_of_mem X.subtype hx'
  rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hYX,
    sup_comm, inf_comm] at h2
  exact h2

theorem isSylowOf_sup_of_inf {p : ℕ} [Fact p.Prime] {N₁ R : Subgroup G}
    (hRN : R ≤ normalizer (N₁ : Set G)) (hR : IsPGroup p R)
    (hS : CFSG.ABGLocalTools.IsSylowOf p (R ⊓ N₁) N₁) :
    CFSG.ABGLocalTools.IsSylowOf p R (N₁ ⊔ R) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS ⊢
  obtain ⟨-, -, hdvd⟩ := hS
  refine ⟨le_sup_right, hR, ?_⟩
  have hY : N₁ ⊔ R ≤ normalizer (N₁ : Set G) := sup_le le_normalizer hRN
  have : (N₁.subgroupOf (N₁ ⊔ R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hY
  have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (N₁.subgroupOf (N₁ ⊔ R))
    (R.subgroupOf (N₁ ⊔ R))
  have h2 : N₁.subgroupOf (N₁ ⊔ R) ⊔ R.subgroupOf (N₁ ⊔ R) = ⊤ := by
    apply map_injective (N₁ ⊔ R).subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right, ← MonoidHom.range_eq_map,
      range_subtype]
  rw [h2, relIndex_top_right, relIndex_subgroupOf le_sup_left] at h1
  intro hd
  apply hdvd
  rw [inf_relIndex_right, ← h1]
  exact hd

omit [Finite G] in
theorem mem_normalizer_inf {A C : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hC : g ∈ normalizer (C : Set G)) : g ∈ normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hC ⊢
  intro x
  have h1 := hA x
  have h2 := hC x
  exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {Y : Subgroup G} {g : G} (h1 : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (h2 : ∀ y ∈ Y, g⁻¹ * y * g ∈ Y) : g ∈ normalizer (Y : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have h := h2 _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h

theorem supplement_frattini {L N R L₁ : Subgroup G} (T : Sylow 2 G) [N.Normal]
    (hRT : R ≤ T) (hTNR : (T : Subgroup G) ⊓ N ≤ R)
    (hRc : ∀ r ∈ R, ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ N)
    (hL₁L : L₁ ≤ L) (hTL₁ : (T : Subgroup G) ≤ normalizer (L₁ : Set G)) :
    L₁ = (L₁ ⊓ N) ⊔ (L₁ ⊓ normalizer (R : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNtop : normalizer (N : Set G) = ⊤ := normalizer_eq_top_iff.mpr inferInstance
  have hRL₁ : R ≤ normalizer (L₁ : Set G) := hRT.trans hTL₁
  have hRR : R ≤ normalizer (R : Set G) := le_normalizer
  have hL₁L₁ : L₁ ≤ normalizer (L₁ : Set G) := le_normalizer
  have hTN₁ : (T : Subgroup G) ≤ normalizer ((L₁ ⊓ N : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (hTL₁ ht) (hNtop ▸ mem_top t)
  have hRN₁ : R ≤ normalizer ((L₁ ⊓ N : Subgroup G) : Set G) := hRT.trans hTN₁
  have hS1 : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) ((L₁ ⊓ N) ⊔ T) :=
    (isSylowOf_top T).of_le le_sup_right le_top
  have hS2 := hS1.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTN₁)
  have hTR : (T : Subgroup G) ⊓ (L₁ ⊓ N) = R ⊓ (L₁ ⊓ N) :=
    le_antisymm (le_inf ((inf_le_inf_left _ inf_le_right).trans hTNR) inf_le_right)
      (inf_le_inf_right _ hRT)
  rw [hTR] at hS2
  have hS3 := isSylowOf_sup_of_inf hRN₁ (T.isPGroup'.to_le hRT) hS2
  have hconj : ∀ l ∈ L₁, ∀ y ∈ (L₁ ⊓ N) ⊔ R, l * y * l⁻¹ ∈ (L₁ ⊓ N) ⊔ R := by
    intro l hl y hy
    have hy' : y ∈ (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := hy
    rw [coe_mul_of_right_le_normalizer_left _ _ hRN₁, Set.mem_mul] at hy'
    obtain ⟨n, hn, r, hr, rfl⟩ := hy'
    have hn' : l * n * l⁻¹ ∈ L₁ ⊓ N :=
      (mem_normalizer_iff.mp (mem_normalizer_inf (hL₁L₁ hl) (hNtop ▸ mem_top l))
        n).mp hn
    have hc : l * r * l⁻¹ * r⁻¹ ∈ L₁ ⊓ N := by
      refine mem_inf.mpr ⟨?_, hRc r hr l (hL₁L hl)⟩
      have h1 : r * l⁻¹ * r⁻¹ ∈ L₁ :=
        (mem_normalizer_iff.mp (hRL₁ hr) l⁻¹).mp (inv_mem hl)
      rw [show l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) by group]
      exact mul_mem hl h1
    rw [show l * (n * r) * l⁻¹ = (l * n * l⁻¹) * (l * r * l⁻¹ * r⁻¹) * r by group]
    exact mul_mem (mul_mem (mem_sup_left hn') (mem_sup_left hc)) (mem_sup_right hr)
  have hconjR : ∀ r ∈ R, ∀ y ∈ (L₁ ⊓ N) ⊔ R, r * y * r⁻¹ ∈ (L₁ ⊓ N) ⊔ R := by
    intro r hr y hy
    have hy' : y ∈ (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := hy
    rw [coe_mul_of_right_le_normalizer_left _ _ hRN₁, Set.mem_mul] at hy'
    obtain ⟨n, hn, r', hr', rfl⟩ := hy'
    have hn' : r * n * r⁻¹ ∈ L₁ ⊓ N := (mem_normalizer_iff.mp (hRN₁ hr) n).mp hn
    rw [show r * (n * r') * r⁻¹ = (r * n * r⁻¹) * (r * r' * r⁻¹) by group]
    exact mul_mem (mem_sup_left hn') (mem_sup_right (mul_mem (mul_mem hr hr') (inv_mem hr)))
  have hXY : L₁ ⊔ R ≤ normalizer (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := by
    refine sup_le (fun l hl => mem_normalizer_of_conj_mem (hconj l hl) ?_)
      (fun r hr => mem_normalizer_of_conj_mem (hconjR r hr) ?_)
    · intro y hy
      simpa using hconj l⁻¹ (inv_mem hl) y hy
    · intro y hy
      simpa using hconjR r⁻¹ (inv_mem hr) y hy
  have hYX : (L₁ ⊓ N) ⊔ R ≤ L₁ ⊔ R := sup_le_sup_right inf_le_left R
  have hFr := frattini_le_sup hYX hXY hS3
  refine le_antisymm (fun l hl => ?_) (sup_le inf_le_left inf_le_left)
  have hl' : l ∈ ((((L₁ ⊓ N) ⊔ R) ⊔ ((L₁ ⊔ R) ⊓ normalizer (R : Set G)) : Subgroup G) :
      Set G) := hFr (mem_sup_left hl)
  rw [coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hXY), Set.mem_mul] at hl'
  obtain ⟨y, hy, a, ha, rfl⟩ := hl'
  have hy' : y ∈ (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left _ _ hRN₁, Set.mem_mul] at hy'
  obtain ⟨n, hn, r, hr, rfl⟩ := hy'
  obtain ⟨haX, haN⟩ := mem_inf.mp ha
  have haX' : a ∈ ((L₁ ⊔ R : Subgroup G) : Set G) := haX
  rw [coe_mul_of_right_le_normalizer_left _ _ hRL₁, Set.mem_mul] at haX'
  obtain ⟨l', hl', r', hr', rfl⟩ := haX'
  have hl'N : l' ∈ normalizer (R : Set G) := by
    have := mul_mem haN (inv_mem (hRR hr'))
    rwa [mul_inv_cancel_right] at this
  set a₁ := r * l' * r⁻¹ with ha₁
  have ha₁L : a₁ ∈ L₁ := (mem_normalizer_iff.mp (hRL₁ hr) l').mp hl'
  have ha₁N : a₁ ∈ normalizer (R : Set G) :=
    mul_mem (mul_mem (hRR hr) hl'N) (inv_mem (hRR hr))
  have hr'' : r * r' ∈ L₁ := by
    have e : r * r' = a₁⁻¹ * n⁻¹ * (n * r * (l' * r')) := by rw [ha₁]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem ha₁L) (inv_mem (mem_inf.mp hn).1)) hl
  have hA : a₁ * (r * r') ∈ L₁ ⊓ normalizer (R : Set G) :=
    mem_inf.mpr ⟨mul_mem ha₁L hr'', mul_mem ha₁N (hRR (mul_mem hr hr'))⟩
  rw [show n * r * (l' * r') = n * (a₁ * (r * r')) by rw [ha₁]; group]
  exact mul_mem (mem_sup_left hn) (mem_sup_right hA)

theorem supplement_residual_eq {L N R K L₁ : Subgroup G} (T : Sylow 2 G) [N.Normal]
    (hRT : R ≤ T) (hTNR : (T : Subgroup G) ⊓ N ≤ R)
    (hRc : ∀ r ∈ R, ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ N)
    (hK : K = perfectCore (L ⊓ normalizer (R : Set G))) (hLNK : L = N ⊔ K)
    (hKperf : ⁅K, K⁆ = K) (hKNR : K ⊓ N ≤ R)
    (hL₁L : L₁ ≤ L) (hTL₁ : (T : Subgroup G) ≤ normalizer (L₁ : Set G)) (hLNL₁ : L = N ⊔ L₁) :
    L₁ = (L₁ ⊓ N) ⊔ (L₁ ⊓ normalizer (R : Set G)) ∧
      perfectCore (L₁ ⊓ normalizer (R : Set G)) = K ∧ K ≤ L₁ ∧ L₁ = (L₁ ⊓ N) ⊔ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNtop : normalizer (N : Set G) = ⊤ := normalizer_eq_top_iff.mpr inferInstance
  have hFr := supplement_frattini T hRT hTNR hRc hL₁L hTL₁
  set A₁ := L₁ ⊓ normalizer (R : Set G) with hA₁
  set K₁ := perfectCore A₁ with hK₁
  have hRL₁ : R ≤ normalizer (L₁ : Set G) := hRT.trans hTL₁
  have hLNA : L = N ⊔ A₁ := by
    rw [hLNL₁]
    conv_lhs => rw [hFr]
    rw [← sup_assoc, sup_eq_left.mpr (inf_le_right : L₁ ⊓ N ≤ N)]
  have hKmap : ⁅K.map (QuotientGroup.mk' N), K.map (QuotientGroup.mk' N)⁆ =
      K.map (QuotientGroup.mk' N) := by
    rw [← map_commutator, hKperf]
  have hLmap : L.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
    rw [hLNK, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hAmap : A₁.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N) := by
    rw [hLNA, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hK₁map : K₁.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N) := by
    rw [hK₁, map_perfectCore, hAmap, hLmap, perfectCore_eq_self_of_perfect hKmap]
  have hLNK₁ : L ≤ N ⊔ K₁ := by
    intro l hl
    have h1 : l ∈ (K₁.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
      rw [hK₁map]
      exact mem_comap.mpr (mem_map_of_mem _ hl)
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_comm] at h1
    exact h1
  have hK₁K : K₁ ≤ K := by
    rw [hK, hK₁]
    exact perfectCore_mono (inf_le_inf_right _ hL₁L)
  have hKdec : K = K₁ ⊔ (K ⊓ N) := by
    refine le_antisymm (fun k hk => ?_) (sup_le hK₁K inf_le_left)
    have hk' : k ∈ ((N ⊔ K₁ : Subgroup G) : Set G) := hLNK₁ (hLNK ▸ mem_sup_right hk)
    rw [coe_mul_of_right_le_normalizer_left _ _ (hNtop ▸ le_top), Set.mem_mul] at hk'
    obtain ⟨n, hn, k₁, hk₁, rfl⟩ := hk'
    have hnK : n ∈ K := by
      have := mul_mem hk (inv_mem (hK₁K hk₁))
      rwa [mul_inv_cancel_right] at this
    rw [sup_comm]
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hnK, hn⟩)) (mem_sup_right hk₁)
  have hRR : R ≤ normalizer (R : Set G) := le_normalizer
  have hNN : normalizer (R : Set G) ≤
      normalizer ((normalizer (R : Set G) : Subgroup G) : Set G) := le_normalizer
  have hRA : R ≤ normalizer (A₁ : Set G) := fun r hr =>
    mem_normalizer_inf (hRL₁ hr) (hNN (hRR hr))
  have hRK₁ : R ≤ normalizer (K₁ : Set G) := hRA.trans (normalizer_le_normalizer_perfectCore A₁)
  have hKK₁ : K ≤ normalizer (K₁ : Set G) := by
    rw [hKdec]
    exact sup_le le_normalizer (hKNR.trans hRK₁)
  have hK₁n : (K₁.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hK₁K).mpr hKK₁
  have hKNs : Group.IsSolvable (K ⊓ N : Subgroup G) := by
    have hp : IsPGroup 2 (K ⊓ N : Subgroup G) := T.isPGroup'.to_le (hKNR.trans hRT)
    have := hp.isNilpotent
    infer_instance
  have hKeq : K₁ = K := by
    refine le_antisymm hK₁K ?_
    have h := perfectCore_le_of_sup_solvable hK₁K hK₁n hKdec hKNs
    rwa [perfectCore_eq_self_of_perfect hKperf] at h
  have hKL₁ : K ≤ L₁ := hKeq ▸ (perfectCore_le A₁).trans inf_le_left
  refine ⟨hFr, hKeq, hKL₁, le_antisymm (fun l hl => ?_) (sup_le inf_le_left hKL₁)⟩
  have hl' : l ∈ ((N ⊔ K : Subgroup G) : Set G) := hLNK ▸ hL₁L hl
  rw [coe_mul_of_right_le_normalizer_left _ _ (hNtop ▸ le_top), Set.mem_mul] at hl'
  obtain ⟨n, hn, k, hk, rfl⟩ := hl'
  have hnL : n ∈ L₁ := by
    have := mul_mem hl (inv_mem (hKL₁ hk))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hnL, hn⟩)) (mem_sup_right hk)

end CFSG.Quasithin.H13.NQBlock
