module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeGrp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normal_subgroupOf_sup_zpowers {I Y₀ : Subgroup G} {u : G} (hIY : I ≤ Y₀)
    (hY : Y₀ ≤ Subgroup.normalizer (I : Set G)) (hu : u ∈ Subgroup.normalizer (I : Set G)) :
    (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hIY.trans le_sup_left)).mpr
    (sup_le hY (Subgroup.zpowers_le.mpr hu))

@[expose] def uMem (Y₀ : Subgroup G) (u : G) : ↥(Y₀ ⊔ Subgroup.zpowers u) :=
  ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩

@[expose] def quotY (I Y₀ : Subgroup G) (u : G)
    [(I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)).Normal] :
    Subgroup (↥(Y₀ ⊔ Subgroup.zpowers u) ⧸ I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)) :=
  (Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)).map (QuotientGroup.mk' _)

@[expose] def quotU (I Y₀ : Subgroup G) (u : G)
    [(I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)).Normal] :
    ↥(Y₀ ⊔ Subgroup.zpowers u) ⧸ I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) :=
  QuotientGroup.mk (uMem Y₀ u)

variable {I Y₀ : Subgroup G} {u : G} [(I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)).Normal]

theorem mem_quotY_iff {x : ↥(Y₀ ⊔ Subgroup.zpowers u) ⧸ I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)} :
    x ∈ quotY I Y₀ u ↔
      ∃ y : G, ∃ hy : y ∈ Y₀ ⊔ Subgroup.zpowers u, y ∈ Y₀ ∧ QuotientGroup.mk ⟨y, hy⟩ = x := by
  unfold quotY
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.1, a.2, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · rintro ⟨y, hy, hyY, rfl⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr hyY, rfl⟩

theorem card_quotY (hIY : I ≤ Y₀) : Nat.card (quotY I Y₀ u) = I.relIndex Y₀ := by
  have hker : (QuotientGroup.mk' (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u))).ker =
      I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) := QuotientGroup.ker_mk' _
  have h1 := Subgroup.relIndex_ker (Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u))
    (QuotientGroup.mk' (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)))
  rw [hker] at h1
  unfold quotY
  rw [← h1]
  exact Subgroup.relIndex_subgroupOf le_sup_left

theorem exists_commutator_notMem_of_quotY
    (h : ∃ x ∈ quotY I Y₀ u, ∃ y ∈ quotY I Y₀ u, ⁅x, y⁆ ≠ 1) :
    ∃ x ∈ Y₀, ∃ y ∈ Y₀, ⁅x, y⁆ ∉ I := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  rw [mem_quotY_iff] at hx hy
  obtain ⟨a, ha, haY, rfl⟩ := hx
  obtain ⟨b, hb, hbY, rfl⟩ := hy
  refine ⟨a, haY, b, hbY, fun hmem => hxy ?_⟩
  have h1 := map_commutatorElement (QuotientGroup.mk' (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)))
    (⟨a, ha⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)) ⟨b, hb⟩
  have h2 : (⁅(⟨a, ha⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)), ⟨b, hb⟩⁆) ∈
      I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) := by
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hmem
  have h3 := (QuotientGroup.eq_one_iff _).mpr h2
  rw [QuotientGroup.mk'_apply] at h1
  exact h1 ▸ h3

theorem mk_mul_quotU_comm {y : G} (hy : y ∈ Y₀ ⊔ Subgroup.zpowers u)
    (hc : y * u * y⁻¹ * u⁻¹ ∈ I) :
    (QuotientGroup.mk ⟨y, hy⟩ :
        ↥(Y₀ ⊔ Subgroup.zpowers u) ⧸ I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)) *
        quotU I Y₀ u =
      quotU I Y₀ u * QuotientGroup.mk ⟨y, hy⟩ := by
  unfold quotU
  have : ⁅(⟨y, hy⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)), uMem Y₀ u⁆ ∈
      I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) := by
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def, uMem] using hc
  have h2 := (QuotientGroup.eq_one_iff _).mpr this
  have h3 := map_commutatorElement (QuotientGroup.mk' (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)))
    (⟨y, hy⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)) (uMem Y₀ u)
  rw [QuotientGroup.mk'_apply] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp (h3 ▸ h2)

theorem quotY_sup_zpowers_quotU_eq_top :
    quotY I Y₀ u ⊔ Subgroup.zpowers (quotU I Y₀ u) = ⊤ := by
  have hL : (Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) :
        Subgroup ↥(Y₀ ⊔ Subgroup.zpowers u)) ⊔ Subgroup.zpowers (uMem Y₀ u) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (Y₀ ⊔ Subgroup.zpowers u))
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      Subgroup.map_top, Subgroup.range_subtype]
    rfl
  have hmap := congrArg
    (Subgroup.map (QuotientGroup.mk' (I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)))) hL
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap
  simpa [quotY, quotU, QuotientGroup.mk'_apply] using hmap

private theorem s763B_mk_mem_quotY_iff (hIY : I ≤ Y₀) (l : ↥(Y₀ ⊔ Subgroup.zpowers u)) :
    (QuotientGroup.mk l :
        ↥(Y₀ ⊔ Subgroup.zpowers u) ⧸ I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)) ∈
      quotY I Y₀ u ↔ (l : G) ∈ Y₀ := by
  constructor
  · intro hx
    rw [mem_quotY_iff] at hx
    obtain ⟨y, hy, hyY, hEq⟩ := hx
    have hmem : (⟨y, hy⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u))⁻¹ * l ∈
        I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) := QuotientGroup.eq.mp hEq
    have hmemI : y⁻¹ * (l : G) ∈ I := by
      have h := Subgroup.mem_subgroupOf.mp hmem
      simpa using h
    have hl : (l : G) = y * (y⁻¹ * (l : G)) := by group
    rw [hl]
    exact Y₀.mul_mem hyY (hIY hmemI)
  · intro hlY
    rw [mem_quotY_iff]
    exact ⟨(l : G), l.2, hlY, rfl⟩

theorem pInvol_quotY {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hIY : I ≤ Y₀)
    (hexp : ∀ y ∈ Y₀, y ^ p ∈ I) (hcl : ∀ x ∈ Y₀, ∀ y ∈ Y₀, ∀ z ∈ Y₀, ⁅⁅x, y⁆, z⁆ ∈ I)
    (hu2 : u * u = 1) (huY : u ∈ Subgroup.normalizer (Y₀ : Set G))
    (hgen : Y₀ ≤ ⁅Y₀, Subgroup.zpowers u⁆ ⊔ I) :
    PInvol p (quotY I Y₀ u) (quotU I Y₀ u) := by
  let N : Subgroup ↥(Y₀ ⊔ Subgroup.zpowers u) :=
    I.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)
  have hQeq : Subgroup.map (QuotientGroup.mk' N) (Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)) =
      quotY I Y₀ u := rfl
  have hUeq : (QuotientGroup.mk' N) (uMem Y₀ u) = quotU I Y₀ u := rfl
  have hN : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap1 : Subgroup.map (Subgroup.subtype (Y₀ ⊔ Subgroup.zpowers u))
        (⁅Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u), Subgroup.zpowers (uMem Y₀ u)⁆ ⊔ N) =
      ⁅Y₀, Subgroup.zpowers u⁆ ⊔ I := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le (hIY.trans le_sup_left),
      Subgroup.map_subgroupOf_eq_of_le le_sup_left]
    rfl
  have hA : Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u) ≤
      ⁅Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u), Subgroup.zpowers (uMem Y₀ u)⁆ ⊔ N := by
    intro y' hy'
    have hyG : (y' : G) ∈ Y₀ := Subgroup.mem_subgroupOf.mp hy'
    have hgeny : (y' : G) ∈ Subgroup.map (Subgroup.subtype (Y₀ ⊔ Subgroup.zpowers u))
        (⁅Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u),
          Subgroup.zpowers (uMem Y₀ u)⁆ ⊔ N) := by
      rw [hmap1]
      exact hgen hyG
    rw [Subgroup.mem_map] at hgeny
    obtain ⟨d, hd, hdg⟩ := hgeny
    have : y' = d := Subtype.ext hdg.symm
    rwa [this]
  have hmapB : Subgroup.map (QuotientGroup.mk' N)
        (⁅Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u),
          Subgroup.zpowers (uMem Y₀ u)⁆ ⊔ N) =
      ⁅quotY I Y₀ u, Subgroup.zpowers (quotU I Y₀ u)⁆ := by
    rw [Subgroup.map_sup, hN, sup_bot_eq, Subgroup.map_commutator, MonoidHom.map_zpowers,
      hQeq, hUeq]
  have hle : quotY I Y₀ u ≤ ⁅quotY I Y₀ u, Subgroup.zpowers (quotU I Y₀ u)⁆ :=
    calc quotY I Y₀ u
        = Subgroup.map (QuotientGroup.mk' N) (Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u)) :=
          hQeq.symm
      _ ≤ Subgroup.map (QuotientGroup.mk' N)
            (⁅Y₀.subgroupOf (Y₀ ⊔ Subgroup.zpowers u),
              Subgroup.zpowers (uMem Y₀ u)⁆ ⊔ N) := Subgroup.map_mono hA
      _ = ⁅quotY I Y₀ u, Subgroup.zpowers (quotU I Y₀ u)⁆ := hmapB
  refine ⟨hp, hp2, ?_, ?_, ?_, ?_, hle⟩
  · intro x hx
    rw [mem_quotY_iff] at hx
    obtain ⟨y, hy, hyY, rfl⟩ := hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hexp y hyY
  · intro x hx y hy z hz
    rw [mem_quotY_iff] at hx hy hz
    obtain ⟨a, ha, haY, rfl⟩ := hx
    obtain ⟨b, hb, hbY, rfl⟩ := hy
    obtain ⟨c, hc, hcY, rfl⟩ := hz
    change ⁅⁅(QuotientGroup.mk' N) (⟨a, ha⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)),
        (QuotientGroup.mk' N) (⟨b, hb⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u))⁆,
        (QuotientGroup.mk' N) (⟨c, hc⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u))⁆ = 1
    rw [← map_commutatorElement (QuotientGroup.mk' N)
          (⟨a, ha⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u))
          (⟨b, hb⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)),
        ← map_commutatorElement (QuotientGroup.mk' N)
          (⁅(⟨a, ha⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)),
            (⟨b, hb⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u))⁆)
          (⟨c, hc⟩ : ↥(Y₀ ⊔ Subgroup.zpowers u)),
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hcl a haY b hbY c hcY
  · unfold quotU
    have hu' : (uMem Y₀ u) * (uMem Y₀ u) = 1 := by
      apply Subtype.ext
      simp [uMem, hu2]
    rw [← QuotientGroup.mk_mul, hu', QuotientGroup.mk_one]
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [s763B_mk_mem_quotY_iff hIY l]
    have hmem : quotU I Y₀ u * QuotientGroup.mk l * (quotU I Y₀ u)⁻¹ =
        QuotientGroup.mk (uMem Y₀ u * l * (uMem Y₀ u)⁻¹) := by
      unfold quotU
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rw [hmem, s763B_mk_mem_quotY_iff hIY]
    have hcoe : ((uMem Y₀ u * l * (uMem Y₀ u)⁻¹ : ↥(Y₀ ⊔ Subgroup.zpowers u)) : G) =
        u * (l : G) * u⁻¹ := by
      simp [uMem]
    rw [hcoe]
    exact Subgroup.mem_normalizer_iff.mp huY (l : G)

end CFSG.LocalAnalysis.WeakClosure81
