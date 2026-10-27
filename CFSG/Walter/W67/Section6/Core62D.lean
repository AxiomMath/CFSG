module

public import CFSG.Walter.W67.Section6.Core62C
public import CFSG.Walter.W67.Section6.PlaneGL

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External

omit [Finite G] in
theorem mem_Vsub_left (x₀ y₀ : G) : x₀ ∈ Vsub x₀ y₀ :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)

omit [Finite G] in
theorem mem_Vsub_right (x₀ y₀ : G) : y₀ ∈ Vsub x₀ y₀ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀)

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

theorem exists_d_y₀ : ∃ m : ℕ, d * y₀ * d⁻¹ = y₀ ^ m := by
  have h1 : d * y₀ * d⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp h.d_P₁ y₀).mp h.y₀_mem
  have h2 := zpowers_eq_of_cyclic h.P₁_cyc h1 h.y₀_mem (orderOf_conj_mul d y₀)
  have h3 : d * y₀ * d⁻¹ ∈ Subgroup.zpowers y₀ := h2 ▸ Subgroup.mem_zpowers _
  obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite y₀).mem_powers_iff_mem_zpowers.mpr h3
  exact ⟨m, hm.symm⟩

omit [Finite G] in
theorem x₀_ne_one : x₀ ≠ 1 := by
  intro h1
  have := h.orderOf_x₀
  rw [h1, orderOf_one] at this
  exact (Fact.out : r.Prime).one_lt.ne this

omit [Finite G] in
theorem y₀_ne_one : y₀ ≠ 1 := by
  intro h1
  have := h.orderOf_y₀
  rw [h1, orderOf_one] at this
  exact (Fact.out : r.Prime).one_lt.ne this

theorem le_M_of_plane {N : Subgroup G}
    (hNV : N ≤ Subgroup.normalizer ((Vsub x₀ y₀ : Subgroup G) : Set G)) (hJN : J ∈ N)
    (hdN : d ∈ N) (hcop : Nat.Coprime r (Nat.card (conjHom hNV).range))
    (h2 : (Nat.card N).factorization 2 ≤ 1) : N ≤ M := by
  have hrp : r.Prime := Fact.out
  have : Fact (1 < r) := ⟨hrp.one_lt⟩
  set e : Vsub x₀ y₀ := ⟨x₀, mem_Vsub_left x₀ y₀⟩ with he_def
  set f : Vsub x₀ y₀ := ⟨y₀, mem_Vsub_right x₀ y₀⟩ with hf_def
  have he : e ≠ 1 := fun h1 => h.x₀_ne_one (congrArg Subtype.val h1)
  have hf : f ∉ Subgroup.zpowers e := by
    intro hfe
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfe
    have hyx : y₀ = x₀ ^ k := by
      have := congrArg Subtype.val hk
      simpa [he_def, hf_def] using this.symm
    have hy : y₀ ∈ Subgroup.zpowers x₀ ⊓ Subgroup.zpowers y₀ :=
      ⟨hyx ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k, Subgroup.mem_zpowers _⟩
    rw [h.X_inf_Y, Subgroup.mem_bot] at hy
    exact h.y₀_ne_one hy
  obtain ⟨m, hm⟩ := h.exists_d_y₀
  have hy₀r : y₀ ^ r = 1 := by rw [← h.orderOf_y₀, pow_orderOf_eq_one]
  have hym : ∀ n : ℕ, y₀ ^ n = y₀ ^ ((n : ZMod r)).val := fun n => by
    rw [ZMod.val_natCast, ← h.orderOf_y₀, pow_mod_orderOf]
  have hk : (m : ZMod r) ≠ 1 := by
    intro hk1
    apply h.d_y₀
    rw [hm, hym, hk1, ZMod.val_one, pow_one]
  set ρ := conjHom hNV with hρ
  have h2' : (Nat.card ρ.range).factorization 2 ≤ 1 :=
    ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_range_dvd ρ) 2).trans h2
  have hte : ρ ⟨J, hJN⟩ e = e := by
    apply Subtype.ext
    rw [hρ, conjHom_apply]
    change J * x₀ * J⁻¹ = x₀
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le h.x₀_mem), mul_inv_cancel_right]
  have htf : ρ ⟨J, hJN⟩ f = f⁻¹ := by
    apply Subtype.ext
    rw [hρ, conjHom_apply]
    exact h.P₁_inv y₀ h.y₀_mem
  have hδe : ρ ⟨d, hdN⟩ e = e := by
    apply Subtype.ext
    rw [hρ, conjHom_apply]
    change d * x₀ * d⁻¹ = x₀
    rw [← Subgroup.mem_centralizer_iff.mp h.d_P₀ x₀ h.x₀_mem, mul_inv_cancel_right]
  have hδf : ρ ⟨d, hdN⟩ f = f ^ ((m : ZMod r)).val := by
    apply Subtype.ext
    rw [hρ, conjHom_apply, Subgroup.coe_pow]
    change d * y₀ * d⁻¹ = y₀ ^ ((m : ZMod r)).val
    rw [hm, hym]
  have hδo : Odd (orderOf (⟨d, hdN⟩ : N)) := by
    rw [Subgroup.orderOf_mk]
    exact h.d_odd
  have hcomm := GL2.comm_of_plane h.plane he hf h.r_ne_two ρ hcop h2' hte htf hδe hδf hk hδo
  intro g hg
  rw [← h.normalizer_X]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcomm ⟨g, hg⟩).2
  have hgx : g * x₀ * g⁻¹ = x₀ ^ k := by
    have := congrArg Subtype.val hk
    rw [hρ, conjHom_apply] at this
    simpa [he_def] using this.symm
  apply JT.mem_normalizer_of_conj_mem
  intro z hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← conj_zpow, hgx, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

omit [Finite G] in
theorem P₀_ne_bot : P₀ ≠ ⊥ := fun h1 => h.x₀_ne_one (by
  have : x₀ ∈ (⊥ : Subgroup G) := h1 ▸ h.x₀_mem
  exact (Subgroup.mem_bot).mp this)

omit [Finite G] in
theorem three_le : 3 ≤ r := by
  have h2 := (Fact.out : r.Prime).two_le
  have := h.r_ne_two
  omega

theorem false_of_le_M (T : Sylow r G) {W : Subgroup G}
    (hweak : WeaklyClosedIn (T : Subgroup G) W)
    (hcond : (∀ u z : G, u ∈ W → z ∈ W → engelSymbol (r - 1) u z = 1) ∨
      W.subgroupOf (T : Subgroup G) ≤ Subgroup.upperCentralSeries (T : Subgroup G) (r - 1))
    (hP₀N : P₀ ≤ Subgroup.normalizer (W : Set G))
    (hNM : Subgroup.normalizer (W : Set G) ≤ M) : False := by
  have htop := hallPResidual_normalizer_eq_top h.perfect T hweak hcond
  have hP₀M : P₀ ≤ M := hP₀N.trans hNM
  refine hallPResidual_ne_top (K₀ := ⊥) (H := M) (H₃ := M₁) (P₀ := P₀)
    (fun _ _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _) bot_le
    (fun x hx => Subgroup.mem_sup_left ⟨hx, hNM hx⟩) h.M_pow
    (fun x hx => by
      have : x ∈ (⊥ : Subgroup G) := hx.2
      rw [Subgroup.mem_bot] at this
      rw [this]
      exact M₁.one_mem)
    (fun x hx => ⟨hP₀N hx, hP₀M hx⟩) h.P₀_M₁ h.P₀_ne_bot h.P₀_r htop

theorem false_of_card_P (hPc : Nat.card ↥(P₀ ⊔ P₁) = r ^ (Nat.card G).factorization r) :
    False := by
  by_cases hab : ∀ a ∈ P₀ ⊔ P₁, ∀ b ∈ P₀ ⊔ P₁, a * b = b * a
  ·
    set T : Sylow r G := Sylow.ofCard _ hPc with hT
    have hTP : (T : Subgroup G) = P₀ ⊔ P₁ := Sylow.coe_ofCard _ _
    have hNV := h.normalizer_le
    set N := Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) with hN
    have hcop : Nat.Coprime r (Nat.card (conjHom hNV).range) := by
      rw [← Subgroup.index_ker]
      set K := (conjHom hNV).ker with hK
      have hPK : (P₀ ⊔ P₁).subgroupOf N ≤ K := by
        intro x hx
        rw [hK, MonoidHom.mem_ker]
        refine MulEquiv.ext fun v => Subtype.ext ?_
        rw [conjHom_apply, MulAut.one_apply]
        have := Subgroup.mem_centralizer_iff.mp (h.V_le_center v.2) x hx
        rw [this, mul_inv_cancel_right]
      apply (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
      intro hdvd
      have h1 := K.card_mul_index
      have h2 : r ^ (Nat.card G).factorization r ∣ Nat.card K := by
        rw [← hPc, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (Subgroup.le_normalizer : P₀ ⊔ P₁ ≤ N)).toEquiv]
        exact Subgroup.card_dvd_of_le hPK
      have h3 : r ^ ((Nat.card G).factorization r + 1) ∣ Nat.card N := by
        rw [← h1, pow_succ]
        exact Nat.mul_dvd_mul h2 hdvd
      exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out
        (h3.trans (Subgroup.card_subgroup_dvd_card N))
    have hNM := h.le_M_of_plane hNV h.J_mem_normalizer h.d_mem_normalizer hcop
      (h.factorization_two_le h.isPGroup_P le_rfl le_rfl)
    refine h.false_of_le_M T (W := (T : Subgroup G)) (weaklyClosedIn_self T)
      (Or.inl (engelSymbol_eq_one_of_comm h.three_le (by rw [hTP]; exact hab))) ?_ ?_
    · rw [hTP]
      exact le_sup_left.trans Subgroup.le_normalizer
    · rw [hTP]
      exact hNM
  ·
    obtain ⟨⟨g, hgP₀⟩, hg⟩ := h.P₀_cyc.exists_generator
    have hP₀g : P₀ ≤ Subgroup.zpowers g := by
      intro a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
      have : g ^ k = a := congrArg Subtype.val hk
      rw [← this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) k
    exact false_of_metacyclic h.perfect h.r_ne_two hPc (C := P₁) le_sup_right
      (sup_le h.P₀_le_N Subgroup.le_normalizer) h.P₁_cyc (Subgroup.mem_sup_left hgP₀)
      (sup_le (hP₀g.trans le_sup_right) le_sup_left) hab

end Hyp62

end CFSG.Walter.W67.Sec6
