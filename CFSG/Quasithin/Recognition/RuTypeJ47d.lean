module

public import CFSG.Quasithin.Recognition.RuTypeJ47Sig
public import CFSG.Quasithin.Recognition.RuTypeJ47b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin Sigma47

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

open Classical in
@[expose] noncomputable def phiG (x : G) : SigmaL2F4 :=
  if h : x ∈ ruH M.T then M.φ ⟨x, h⟩ else 1

omit [Finite G] in
theorem phiG_of_mem {x : G} (hx : x ∈ ruH M.T) : M.phiG x = M.φ ⟨x, hx⟩ := by
  rw [phiG, dite_eq_left hx]

omit [Finite G] in
theorem phiG_mul {x y : G} (hx : x ∈ ruH M.T) (hy : y ∈ ruH M.T) :
    M.phiG (x * y) = M.phiG x * M.phiG y := by
  rw [M.phiG_of_mem hx, M.phiG_of_mem hy, M.phiG_of_mem (mul_mem hx hy), ← map_mul]
  rfl

omit [Finite G] in
theorem phiG_inv {x : G} (hx : x ∈ ruH M.T) : M.phiG x⁻¹ = (M.phiG x)⁻¹ := by
  rw [M.phiG_of_mem hx, M.phiG_of_mem (inv_mem hx), ← map_inv]
  rfl

omit [Finite G] in
theorem phiG_pow {x : G} (hx : x ∈ ruH M.T) (n : ℕ) : M.phiG (x ^ n) = M.phiG x ^ n := by
  rw [M.phiG_of_mem hx, M.phiG_of_mem (pow_mem hx n), ← map_pow]
  rfl

omit [Finite G] in
theorem phiG_eq_one_iff {x : G} (hx : x ∈ ruH M.T) : M.phiG x = 1 ↔ x ∈ ruQ M.T := by
  rw [M.phiG_of_mem hx]
  have : (⟨x, hx⟩ : ruH M.T) ∈ M.φ.ker ↔ x ∈ ruQ M.T := by
    rw [M.φ_ker, Subgroup.mem_subgroupOf]
  exact this

omit [Finite G] in
theorem phiG_conj {g x : G} (hg : g ∈ ruH M.T) (hx : x ∈ ruH M.T) :
    M.phiG (g * x * g⁻¹) = M.phiG g * M.phiG x * (M.phiG g)⁻¹ := by
  rw [M.phiG_mul (mul_mem hg hx) (inv_mem hg), M.phiG_mul hg hx, M.phiG_inv hg]

theorem pow_eq_one_of_mem_Q {q : G} (hq : q ∈ ruQ M.T) : q ^ 2048 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard _ hq
  rw [M.toRuData.card_Q] at h
  exact orderOf_dvd_iff_pow_eq_one.mp (by simpa using h)

noncomputable abbrev P5c (b g : G) : Subgroup G := (P5 b).map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_P5c {b g x : G} : x ∈ P5c b g ↔ g⁻¹ * x * g ∈ P5 b := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

omit [Finite G] in
theorem conj_mem_P5c {b g x : G} (hx : x ∈ P5 b) : g * x * g⁻¹ ∈ P5c b g := by
  rw [mem_P5c]; group; exact hx

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem card_P5c
    (g : G) : Nat.card (P5c b g) = 125 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_P5_eq_125 hbH hb5]

theorem not_comm_P5c
    (g : G) : ¬ ∀ x ∈ P5c b g, ∀ y ∈ P5c b g, x * y = y * x := by
  intro h
  apply not_comm_P5 hbH hb5
  intro x hx y hy
  have := h _ (conj_mem_P5c (g := g) hx) _ (conj_mem_P5c (g := g) hy)
  calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [this]
    _ = y * x := by group

theorem pow_five_P5c
    {g x : G} (hx : x ∈ P5c b g) : x ^ 5 = 1 := by
  have h := pow_five_eq_one_P5 hbH hb5 (mem_P5c.mp hx)
  have e : (g⁻¹ * x * g) ^ 5 = g⁻¹ * x ^ 5 * g := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, conj_pow]; group
  rw [e] at h
  calc x ^ 5 = g * (g⁻¹ * x ^ 5 * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

omit [Finite G] hbH hb5 in
theorem comm_center_P5c {g x : G} (hx : x ∈ P5c b g) :
    x * (g * b * g⁻¹) = (g * b * g⁻¹) * x := by
  have h := comm_b_P5 (mem_P5c.mp hx)
  calc x * (g * b * g⁻¹) = g * ((g⁻¹ * x * g) * b) * g⁻¹ := by group
    _ = g * (b * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = (g * b * g⁻¹) * x := by group

theorem mem_P5c_of_pow_five {g x : G}
    (hxc : x * (g * b * g⁻¹) = (g * b * g⁻¹) * x) (hx5 : x ^ 5 = 1) : x ∈ P5c b g := by
  rw [mem_P5c]
  refine mem_P5_of_pow_five hbH hb5 (mem_G5.mpr ?_) ?_
  · calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [hxc]
      _ = b * (g⁻¹ * x * g) := by group
  · rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, conj_pow, hx5]; group

theorem comm_mem_P5c
    {g x y : G} (hx : x ∈ P5c b g) (hy : y ∈ P5c b g) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (g * b * g⁻¹) := by
  have h := comm_mem_zpowers_P5 hbH hb5 (mem_P5c.mp hx) (mem_P5c.mp hy)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, hk]
  group

theorem card_P5c_inf_centralizer
    {g i : G} (hiz : IsConj M.z i) (hi2 : i * i = 1)
    (hib : i * (g * b * g⁻¹) * i⁻¹ = (g * b * g⁻¹)⁻¹) :
    Nat.card (P5c b g ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5 := by
  have hi'z : IsConj M.z (g⁻¹ * i * g) := hiz.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hi'2 : (g⁻¹ * i * g) * (g⁻¹ * i * g) = 1 := by
    calc (g⁻¹ * i * g) * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g := by group
      _ = 1 := by rw [hi2]; group
  have hi'b : (g⁻¹ * i * g) * b * (g⁻¹ * i * g)⁻¹ = b⁻¹ := by
    calc (g⁻¹ * i * g) * b * (g⁻¹ * i * g)⁻¹ = g⁻¹ * (i * (g * b * g⁻¹) * i⁻¹) * g := by group
      _ = b⁻¹ := by rw [hib]; group
  have h := card_P5_inf_centralizer hbH hb5 hi'z hi'2 hi'b
  have e : (P5c b g ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) =
      (P5 b ⊓ Subgroup.centralizer ({g⁻¹ * i * g} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, mem_P5c, MulAut.conj_symm_apply,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hx
      calc g⁻¹ * x * g * (g⁻¹ * i * g) = g⁻¹ * (x * i) * g := by group
        _ = g⁻¹ * (i * x) * g := by rw [hx]
        _ = g⁻¹ * i * g * (g⁻¹ * x * g) := by group
    · intro hx
      calc x * i = g * (g⁻¹ * x * g * (g⁻¹ * i * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * i * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
        _ = i * x := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective, h]

end Five

end RuDataM

end CFSG.Quasithin.RuType
