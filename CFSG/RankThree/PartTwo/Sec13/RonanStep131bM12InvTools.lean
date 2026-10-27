module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open scoped Pointwise commutatorElement

namespace M12Inv

theorem exists_zpow_mul_of_mem_zpowers_sup' {G : Type*} [Group G] {K : Subgroup G} {e x : G}
    (hKe : K ≤ Subgroup.centralizer ({e} : Set G)) (hx : x ∈ Subgroup.zpowers e ⊔ K) :
    ∃ (i : ℤ) (k : G), k ∈ K ∧ x = e ^ i * k := by
  have hN : Subgroup.zpowers e ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · have h := Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)
      have : e * k * e⁻¹ = k := by rw [← h, mul_inv_cancel_right]
      rwa [this]
    · have h := Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)
      have h2 : e * k * e⁻¹ * e = e * (e * k * e⁻¹) := h
      have h3 : e * k = e * (e * k * e⁻¹) := by
        calc e * k = e * k * e⁻¹ * e := by group
          _ = e * (e * k * e⁻¹) := h2
      have h4 : k = e * k * e⁻¹ := mul_left_cancel h3
      rw [← h4] at hk
      exact hk
  have hx' : x ∈ ((Subgroup.zpowers e ⊔ K : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx'
  obtain ⟨a, ha, k, hk, hak⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨i, k, hk, hak.symm⟩

theorem isElemAbelian_sup_of_commute {G : Type*} [Group G] {E F : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hF : CFSG.Open.IsElemAbelian 3 F)
    (hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e) : CFSG.Open.IsElemAbelian 3 (E ⊔ F) := by
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hN : E ≤ Subgroup.normalizer (F : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer F (Subgroup.mem_centralizer_iff.mpr fun f hf =>
      (hcomm e he f hf).symm)
  have hset : ((E ⊔ F : Subgroup G) : Set G) = E * F :=
    Subgroup.coe_mul_of_left_le_normalizer_right E F hN
  have hmem : ∀ x ∈ E ⊔ F, ∃ e ∈ E, ∃ f ∈ F, x = e * f := fun x hx => by
    have : x ∈ ((E ⊔ F : Subgroup G) : Set G) := hx
    rw [hset] at this
    obtain ⟨e, he, f, hf, h⟩ := this
    exact ⟨e, he, f, hf, h.symm⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, f, hf, hx⟩ := hmem x x.2
    obtain ⟨e', he', f', hf', hy⟩ := hmem y y.2
    show (x : G) * y = y * x
    rw [hx, hy]
    have c1 : Commute e e' := hEc e he e' he'
    have c2 : Commute e f' := hcomm e he f' hf'
    have c3 : Commute f e' := (hcomm e' he' f hf).symm
    have c4 : Commute f f' := hFc f hf f' hf'
    exact (Commute.mul_left (c1.mul_right c2) (c3.mul_right c4)).eq
  · obtain ⟨e, he, f, hf, rfl⟩ := hmem x hx
    have c : Commute e f := hcomm e he f hf
    rw [c.mul_pow, hE.2 e he, hF.2 f hf, mul_one]

theorem commutatorElement_mul_mul' {G : Type*} [Group G] {x y s₁ s₂ : G} (h1 : Commute x s₁)
    (h2 : Commute x y) (h3 : Commute x s₂) (h4 : Commute y s₁) (h5 : Commute y s₂) :
    ⁅x * s₁, y * s₂⁆ = ⁅s₁, s₂⁆ := by
  have hx : Commute x (s₁ * y * s₂ * s₁⁻¹) :=
    ((h1.mul_right h2).mul_right h3).mul_right h1.inv_right
  have hy : Commute y (s₂ * s₁⁻¹ * s₂⁻¹) := (h5.mul_right h4.inv_right).mul_right h5.inv_right
  calc ⁅x * s₁, y * s₂⁆ = x * (s₁ * y * s₂ * s₁⁻¹) * x⁻¹ * (s₂⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]; group
    _ = (s₁ * y * s₂ * s₁⁻¹) * (s₂⁻¹ * y⁻¹) := by rw [hx.eq, mul_inv_cancel_right]
    _ = s₁ * (y * (s₂ * s₁⁻¹ * s₂⁻¹)) * y⁻¹ := by group
    _ = s₁ * ((s₂ * s₁⁻¹ * s₂⁻¹) * y) * y⁻¹ := by rw [hy.eq]
    _ = ⁅s₁, s₂⁆ := by rw [commutatorElement_def]; group

theorem zpow_eq_one_of_zpow_mem' {G : Type*} [Group G] {c : G} (hc3 : c ^ 3 = 1)
    {M : Subgroup G} (hcM : c ∉ M) {k : ℤ} (hk : c ^ k ∈ M) : c ^ k = 1 := by
  have hck : c ^ k = c ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, show (c ^ (3 : ℤ)) = 1 by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hc3], one_zpow, one_mul]
  have h3 : 0 ≤ k % 3 ∧ k % 3 < 3 := ⟨Int.emod_nonneg k (by norm_num), Int.emod_lt_of_pos k
    (by norm_num)⟩
  rw [hck] at hk ⊢
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hk
    exact absurd hk hcM
  · exfalso
    rw [h] at hk
    have h4 : c ^ (2 : ℤ) * c ^ (2 : ℤ) ∈ M := M.mul_mem hk hk
    rw [← zpow_add, show (2 : ℤ) + 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
      show (c ^ (3 : ℤ)) = 1 by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hc3], one_mul] at h4
    exact hcM h4

theorem zpowers_inf_eq_bot' {G : Type*} [Group G] {c : G} (hc3 : c ^ 3 = 1) {M : Subgroup G}
    (hcM : c ∉ M) : Subgroup.zpowers c ⊓ M = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxM⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Subgroup.mem_bot).mpr (zpow_eq_one_of_zpow_mem' hc3 hcM hxM)

theorem pow_three_mul_of_central {G : Type*} [Group G] {f e u : G} (hf3 : f ^ 3 = 1)
    (he3 : e ^ 3 = 1) (h1 : e * f = u * (f * e)) (hu3 : u ^ 3 = 1) (huf : u * f = f * u)
    (hue : u * e = e * u) : (f * e) ^ 3 = 1 := by
  have hf3' : f * f * f = 1 := by rw [← pow_three']; exact hf3
  have he3' : e * e * e = 1 := by rw [← pow_three']; exact he3
  have hu3' : u * u * u = 1 := by rw [← pow_three']; exact hu3
  have L1 : f * e * (f * e) = u * (f * f * (e * e)) := by
    calc f * e * (f * e) = f * (e * f) * e := by group
      _ = f * (u * (f * e)) * e := by rw [h1]
      _ = (f * u) * (f * e) * e := by group
      _ = (u * f) * (f * e) * e := by rw [← huf]
      _ = u * (f * f * (e * e)) := by group
  have L2 : e * e * f = u * u * (f * (e * e)) := by
    calc e * e * f = e * (e * f) := by group
      _ = e * (u * (f * e)) := by rw [h1]
      _ = (e * u) * (f * e) := by group
      _ = (u * e) * (f * e) := by rw [← hue]
      _ = u * (e * f) * e := by group
      _ = u * (u * (f * e)) * e := by rw [h1]
      _ = u * u * (f * (e * e)) := by group
  have hfuu : (f * f) * (u * u) = (u * u) * (f * f) := by
    have h : Commute f u := huf.symm
    exact ((h.mul_left h).mul_right (h.mul_left h)).eq
  calc (f * e) ^ 3 = f * e * (f * e) * (f * e) := by rw [pow_three']
    _ = u * (f * f * (e * e)) * (f * e) := by rw [L1]
    _ = u * (f * f) * ((e * e) * f) * e := by group
    _ = u * (f * f) * (u * u * (f * (e * e))) * e := by rw [L2]
    _ = u * ((f * f) * (u * u)) * (f * (e * e)) * e := by group
    _ = u * ((u * u) * (f * f)) * (f * (e * e)) * e := by rw [hfuu]
    _ = (u * u * u) * (f * f * f) * (e * e * e) := by group
    _ = 1 := by rw [hu3', hf3', he3']; group

theorem zpow_pow_three_eq_one {G : Type*} [Group G] {c : G} (hc3 : c ^ 3 = 1) (k : ℤ) :
    (c ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]

end M12Inv

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
