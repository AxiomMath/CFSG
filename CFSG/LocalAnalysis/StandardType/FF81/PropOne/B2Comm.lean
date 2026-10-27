module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Package

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem comm_eq_one_iff {G : Type} [Group G] {b x : G} :
    b * x * b⁻¹ * x⁻¹ = 1 ↔ x * b = b * x := by
  constructor
  · intro h
    have h2 : b * x * b⁻¹ = x := by rwa [mul_inv_eq_one] at h
    have h3 : b * x = x * b := by
      calc b * x = (b * x * b⁻¹) * b := by group
        _ = x * b := by rw [h2]
    exact h3.symm
  · intro h
    rw [← h]
    group

private theorem comm_mul {G : Type} [Group G] {B : Subgroup G}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {b : G} (hbB : ∀ x ∈ B, b * x * b⁻¹ ∈ B) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) :
    b * (x * y) * b⁻¹ * (x * y)⁻¹ =
      (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := by
  have hφy : b * y * b⁻¹ * y⁻¹ ∈ B := B.mul_mem (hbB y hy) (B.inv_mem hy)
  have hcxφy : Commute x (b * y * b⁻¹ * y⁻¹) := hB x hx (b * y * b⁻¹ * y⁻¹) hφy
  calc b * (x * y) * b⁻¹ * (x * y)⁻¹
      = b * x * (y * b⁻¹ * y⁻¹) * x⁻¹ := by group
    _ = b * x * (b⁻¹ * (b * y * b⁻¹ * y⁻¹)) * x⁻¹ := by
          rw [show y * b⁻¹ * y⁻¹ = b⁻¹ * (b * y * b⁻¹ * y⁻¹) by group]
    _ = b * x * b⁻¹ * (b * y * b⁻¹ * y⁻¹) * x⁻¹ := by group
    _ = b * x * b⁻¹ * ((b * y * b⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = b * x * b⁻¹ * (x⁻¹ * (b * y * b⁻¹ * y⁻¹)) := by
          rw [hcxφy.inv_left.eq.symm]
    _ = (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := by group

theorem exists_commSubgroup {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    (hB₂ : B2Package b z B₂) :
    ∃ T : Subgroup G, T ≤ B₂ ∧ bOne z ≤ T ∧ Nat.card T = 3 ^ 4 ∧
      ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ ∈ Subgroup.zpowers (GGFF.zs z 0) := by
  have hS : GGFF.SettingCore b L z := h.settingCore
  have hB₁_le_L : bOne z ≤ L := GGFF.SettingCore.tor_le z
  have hB₁_le_cen : bOne z ≤ Subgroup.centralizer ({b} : Set G) :=
    hB₁_le_L.trans h.hypA.le
  have hb₁_mem : GGFF.zs z 0 ∈ bOne z := Subgroup.subset_closure ⟨0, rfl⟩
  have hb₁_cube : GGFF.zs z 0 ^ 3 = 1 := hS.zs_pow 0
  have hb₁_ne : GGFF.zs z 0 ≠ 1 := fun h1 =>
    h.model.z_ne_one 0 (Subtype.ext (by simpa [GGFF.zs] using h1))
  have hB₂comm' : ∀ a b : ↥B₂, a * b = b * a := isMulCommutative_iff.mp hB₂.abel.1
  have hB₂comm : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB₂comm' ⟨x, hx⟩ ⟨y, hy⟩)
  let Φ : ↥B₂ →* ↥(bOne z) :=
    MonoidHom.mk' (fun x => ⟨b * (x : G) * b⁻¹ * (x : G)⁻¹, hB₂.comm x x.2⟩)
      (fun x y => by
        apply Subtype.ext
        show b * ((x : G) * (y : G)) * b⁻¹ * ((x : G) * (y : G))⁻¹ =
          (b * (x : G) * b⁻¹ * (x : G)⁻¹) * (b * (y : G) * b⁻¹ * (y : G)⁻¹)
        exact comm_mul hB₂comm hB₂.b_nor x.2 y.2)
  have hker : Φ.ker = (bOne z).subgroupOf B₂ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      apply hB₂.fix x x.2
      have hx1 : b * (x : G) * b⁻¹ * (x : G)⁻¹ = 1 := by
        have h' := congrArg (fun u : ↥(bOne z) => (u : G)) hx
        change b * (x : G) * b⁻¹ * (x : G)⁻¹ = 1 at h'
        exact h'
      exact comm_eq_one_iff.mp hx1
    · intro hx
      apply Subtype.ext
      change b * (x : G) * b⁻¹ * (x : G)⁻¹ = 1
      exact comm_eq_one_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hB₁_le_cen hx) b (by simp)).symm)
  have hcardKer : Nat.card Φ.ker = 27 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₂.B₁_le).toEquiv]
    exact hS.card_torG
  have hcardRange : Nat.card Φ.range = 27 := by
    have h := Subgroup.card_ker_mul_card_range Φ
    rw [hcardKer, hB₂.card] at h
    have h3 : (3 : ℕ) ^ 6 = 27 * 27 := by norm_num
    rw [h3] at h
    exact Nat.mul_left_cancel (by norm_num) h
  have hrange_top : Φ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq Φ.range (by rw [hcardRange, hS.card_torG])
  have hΦsurj : Function.Surjective Φ := MonoidHom.range_eq_top.mp hrange_top
  let a : ↥(bOne z) := ⟨GGFF.zs z 0, hb₁_mem⟩
  let H : Subgroup ↥(bOne z) := Subgroup.zpowers a
  have ha_cube : a ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hb₁_cube
  have ha_ne : a ≠ 1 := fun h1 => hb₁_ne (by
    have h' := congrArg (fun u : ↥(bOne z) => (u : G)) h1
    simpa [a] using h')
  have hHcard : Nat.card H = 3 := by
    change Nat.card (Subgroup.zpowers a) = 3
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha_cube ha_ne
  have hHindex : H.index = 9 := by
    have h := Subgroup.card_mul_index H
    rw [hHcard, hS.card_torG] at h
    omega
  have hcomapIndex : (H.comap Φ).index = 9 := by
    rw [Subgroup.index_comap_of_surjective (H := H) (f := Φ) hΦsurj, hHindex]
  have hcomapCard : Nat.card (H.comap Φ) = 81 := by
    have h := Subgroup.card_mul_index (H.comap Φ)
    rw [hcomapIndex, hB₂.card] at h
    have h3 : (3 : ℕ) ^ 6 = 81 * 9 := by norm_num
    rw [h3] at h
    exact Nat.mul_right_cancel (by norm_num) h
  refine ⟨(H.comap Φ).map B₂.subtype, Subgroup.map_subtype_le (H.comap Φ), ?_, ?_, ?_⟩
  · intro x hx
    have hxB₂ : x ∈ B₂ := hB₂.B₁_le hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxB₂⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hΦx : Φ ⟨x, hxB₂⟩ = 1 := by
      apply Subtype.ext
      change b * x * b⁻¹ * x⁻¹ = 1
      exact comm_eq_one_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hB₁_le_cen hx) b (by simp)).symm)
    rw [hΦx]
    exact H.one_mem
  · rw [Subgroup.card_map_of_injective (f := B₂.subtype) B₂.subtype_injective, hcomapCard]
    norm_num
  · rintro t ⟨y, hy, rfl⟩
    have hyH : Φ y ∈ H := Subgroup.mem_comap.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyH
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    change (GGFF.zs z 0) ^ k = (Φ y : G)
    have h1 := congrArg (fun u : ↥(bOne z) => (u : G)) hk
    simpa [a] using h1

end CFSG.StandardType.FF81.PropOne

end
