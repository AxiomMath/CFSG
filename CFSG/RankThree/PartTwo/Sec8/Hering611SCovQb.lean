module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQa

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {P : Type*} [Group P] [Finite P] {σ : MulAut P} {Zh : Subgroup P}

private theorem sup_zpowers_eq_of_card {G : Type*} [Group G] [Finite G] {E Z : Subgroup G}
    (hZE : Z ≤ E) (hZ : Nat.card Z = 3) (hE : Nat.card E = 9) {w : G} (hwE : w ∈ E)
    (hwZ : w ∉ Z) : Z ⊔ Subgroup.zpowers w = E := by
  have hS : Z ⊔ Subgroup.zpowers w ≤ E := sup_le hZE (Subgroup.zpowers_le.mpr hwE)
  have hdE : Nat.card ↥(Z ⊔ Subgroup.zpowers w) ∣ 9 := by
    have := Subgroup.card_dvd_of_le hS
    rwa [hE] at this
  have hdZ : 3 ∣ Nat.card ↥(Z ⊔ Subgroup.zpowers w) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Z ≤ Z ⊔ Subgroup.zpowers w)
    rwa [hZ] at this
  have hne : Nat.card ↥(Z ⊔ Subgroup.zpowers w) ≠ 3 := by
    intro h3
    have hEq : Z = Z ⊔ Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    apply hwZ
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have h9 : Nat.card ↥(Z ⊔ Subgroup.zpowers w) = 9 := by
    obtain ⟨k, hk⟩ := hdZ
    rw [hk] at hdE hne ⊢
    have hk3 : k ≤ 3 := by
      have := Nat.le_of_dvd (by norm_num) hdE
      omega
    interval_cases k <;> revert hdE hne <;> norm_num
  exact Subgroup.eq_of_le_of_card_ge hS (by omega)

private theorem comm_covW_of_comm (h : CoverP P σ Zh) {y : P} (hy : y ∈ covW Zh h.central)
    (hyZ : y ∉ Zh) {q : P} (hq : q * y = y * q) {r : P} (hr : r ∈ covW Zh h.central) :
    q * r = r * q := by
  have hE := sup_zpowers_eq_of_card (Zh_le_covW h) h.card_Z (covW_card h) hy hyZ
  have hK : covW Zh h.central ≤ Subgroup.centralizer ({q} : Set P) := by
    rw [← hE]
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp (h.central hz) q).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hK hr)).symm

private theorem index_centralizer_eq_three (h : CoverP P σ Zh) {w : P}
    (hw : w ∈ covW Zh h.central) {p : P} (hp : w * p ≠ p * w) :
    (Subgroup.centralizer ({w} : Set P)).index = 3 := by
  have hmem : ∀ q : P, q * w * q⁻¹ * w⁻¹ ∈ Zh := by
    intro q
    have h1 : (w * q * w⁻¹ * q⁻¹)⁻¹ ∈ Zh := Zh.inv_mem (mem_covW.mp hw q)
    have e : (w * q * w⁻¹ * q⁻¹)⁻¹ = q * w * q⁻¹ * w⁻¹ := by group
    rwa [e] at h1
  have hcen : ∀ b : P, ∀ g : P, g * (b * w * b⁻¹ * w⁻¹) = (b * w * b⁻¹ * w⁻¹) * g :=
    fun b => Subgroup.mem_center_iff.mp (h.central (hmem b))
  let f : P →* Zh := MonoidHom.mk' (fun q => ⟨q * w * q⁻¹ * w⁻¹, hmem q⟩) (by
    intro a b
    apply Subtype.ext
    show a * b * w * (a * b)⁻¹ * w⁻¹ = (a * w * a⁻¹ * w⁻¹) * (b * w * b⁻¹ * w⁻¹)
    have e1 : a * b * w * (a * b)⁻¹ * w⁻¹ =
        (a * (b * w * b⁻¹ * w⁻¹) * a⁻¹) * (a * w * a⁻¹ * w⁻¹) := by group
    have e2 : a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ = b * w * b⁻¹ * w⁻¹ := by
      rw [hcen b a]
      group
    rw [e1, e2]
    exact (hcen b (a * w * a⁻¹ * w⁻¹)).symm)
  have hker : f.ker = Subgroup.centralizer ({w} : Set P) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hq
      have h1 : q * w * q⁻¹ * w⁻¹ = 1 := congrArg Subtype.val hq
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    · intro hq
      apply Subtype.ext
      show q * w * q⁻¹ * w⁻¹ = 1
      rw [hq]
      group
  have hrange : Nat.card f.range = 3 := by
    have hdvd : Nat.card f.range ∣ 3 := by
      have := Subgroup.card_subgroup_dvd_card f.range
      rwa [h.card_Z] at this
    have hne1 : Nat.card f.range ≠ 1 := by
      intro h1
      have hbot : f.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hmem1 : f p ∈ f.range := MonoidHom.mem_range.mpr ⟨p, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem1
      have h2 : p * w * p⁻¹ * w⁻¹ = 1 := congrArg Subtype.val hmem1
      exact hp (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm
    exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
  rw [← hker, Subgroup.index_ker, hrange]

theorem covW_le_center (h : CoverP P σ Zh) {w : P} (hw : w ∈ covW Zh h.central) (p : P) :
    w * p = p * w := by
  by_contra hne
  have hwZ : w ∉ Zh := fun hZ => hne (Subgroup.mem_center_iff.mp (h.central hZ) p).symm
  have hxW : σ w ∈ covW Zh h.central := sigma_mem_covW h hw
  have hxZ : σ w ∉ Zh := by
    intro hx
    have h1 : σ (σ w) = σ w := h.sigma_Z _ hx
    have h2 : σ w = w := MulEquiv.injective σ h1
    rw [h2] at hx
    exact hwZ hx
  have hstab : ∀ q : P, q * w = w * q → σ q * w = w * σ q := by
    intro q hq
    have hσq : σ q * σ w = σ w * σ q := by
      have h2 := congrArg (⇑σ) hq
      simpa only [map_mul] using h2
    exact comm_covW_of_comm h hxW hxZ hσq hw
  have hZC : Zh ≤ Subgroup.centralizer ({w} : Set P) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (h.central hz) w).symm
  have hC : (Subgroup.centralizer ({w} : Set P)).index = 3 :=
    index_centralizer_eq_three h hw hne
  have hpow : ∀ r : P, (σ ^ 2).toMonoidHom r = σ (σ r) := fun r => rfl
  have hmap : (Subgroup.centralizer ({w} : Set P)).map (σ ^ 2).toMonoidHom =
      Subgroup.centralizer ({w} : Set P) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨q, hq, rfl⟩
      have hq' : q * w = w * q := Subgroup.mem_centralizer_singleton_iff.mp hq
      rw [hpow, Subgroup.mem_centralizer_singleton_iff]
      exact hstab (σ q) (hstab q hq')
    · exact (Subgroup.card_map_of_injective
        (f := (σ ^ 2).toMonoidHom) (MulEquiv.injective (σ ^ 2))).ge
  exact h.singer _ hZC hC hmap

end CFSG.RankThree.PartTwo.Sec8.Hering611
