module

public import CFSG.Quasithin.Recognition.HSType129e
public import CFSG.Quasithin.Recognition.HSType15b

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

@[expose] def τ3 : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 3 4

@[expose] def ω3 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 5

theorem τ3_pow_three : τ3 ^ 3 = 1 := by decide

theorem τ3_ne_one : τ3 ≠ 1 := by decide

theorem τ3_inv_ne : τ3⁻¹ ≠ τ3 := by decide

theorem ω3_mul_τ3 : ω3 * τ3 * ω3⁻¹ = τ3 := by decide

theorem actS6_τ3_spE0 : actS6 τ3 (spE 0) = spE 0 := by decide

theorem orderOf_τ3 : orderOf τ3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime τ3_pow_three τ3_ne_one

theorem mem_zpowers_τ3 {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ Subgroup.zpowers τ3) :
    σ = 1 ∨ σ = τ3 ∨ σ = τ3 * τ3 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_τ3] at hσ
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hσ
  rw [Finset.mem_range] at hk
  interval_cases k
  · left; simp
  · right; left; simp
  · right; right; simp [sq]

theorem zpowers_τ3_mul_ω3 : ∀ σ ∈ ({1, τ3, τ3 * τ3} : Finset (Equiv.Perm (Fin 6))),
    (σ * ω3) ^ 3 = 1 ∧ (σ * ω3) * τ3 = τ3 * (σ * ω3) ∧
      ∀ ρ ∈ ({1, τ3, τ3 * τ3} : Finset (Equiv.Perm (Fin 6))), σ * ω3 ≠ ρ := by
  decide +kernel

theorem eq_of_mem_zpowers_three {G : Type*} [Group G] {x y : G} (hx3 : orderOf x = 3)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x⁻¹ := by
  classical
  have hxxx : x * x * x = 1 := by rw [← pow_three', ← hx3, pow_orderOf_eq_one]
  have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [hx3]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hx3] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hk
  interval_cases k
  · left; simp
  · right; left; simp
  · right; right
    simp only [sq]
    calc x * x = x * x * x * x⁻¹ := by group
      _ = x⁻¹ := by rw [hxxx, one_mul]

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

theorem pow_four_cube (n : ↥(hsNB z s)) (hn : M.π n ^ 3 = 1) :
    ((n ^ 4 : ↥(hsNB z s)) : G) ^ 3 = 1 ∧ M.π (n ^ 4) = M.π n := by
  have hn3 : ((n ^ 3 : ↥(hsNB z s)) : G) ∈ hsB z s := (M.ker (n ^ 3)).mp (by rw [map_pow, hn])
  have e := M.mul_self_of_mem_hsB hn3
  rw [Subgroup.coe_pow] at e
  refine ⟨?_, ?_⟩
  · rw [Subgroup.coe_pow, ← pow_mul]
    calc (n : G) ^ (4 * 3) = ((n : G) ^ 3 * (n : G) ^ 3) ^ 2 := by group
      _ = 1 := by rw [e, one_pow]
  · rw [map_pow, show M.π n ^ 4 = M.π n ^ 3 * M.π n by group, hn, one_mul]

include M in
theorem exists_pair_three [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    ∃ x w : G, x ∈ hsH z ∧ orderOf x = 3 ∧ w * x = x * w ∧ orderOf w = 3 ∧
      w ∉ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n₀, hn₀⟩ := M.π_surj τ3
  obtain ⟨hx3, hπx⟩ := M.pow_four_cube n₀ (by rw [hn₀]; exact τ3_pow_three)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥(hsNB z s), x₀ = n₀ ^ 4 := ⟨_, rfl⟩
  rw [← hx₀] at hx3 hπx
  rw [hn₀] at hπx
  have hx₀1 : (x₀ : G) ≠ 1 := fun h1 => τ3_ne_one (by
    rw [← hπx, show x₀ = 1 from Subtype.ext h1, map_one])
  have hox : orderOf (x₀ : G) = 3 := orderOf_eq_prime hx3 hx₀1
  have hx₀H : (x₀ : G) ∈ hsH z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have := M.act x₀ (spE 0)
    rw [hπx, actS6_τ3_spE0, M.e0] at this
    calc (x₀ : G) * z = (x₀ : G) * z * (x₀ : G)⁻¹ * x₀ := by group
      _ = z * x₀ := by rw [this]
  set W := M.pre (Subgroup.zpowers τ3) with hW
  have hcardW : Nat.card W = 48 := by
    rw [hW, M.card_pre h hsmemH hsnotK hss hg₀, Nat.card_zpowers, orderOf_τ3]
  have hx₀W : (x₀ : G) ∈ W := M.mem_pre.mpr ⟨x₀.2,
    show M.π x₀ ∈ Subgroup.zpowers τ3 by rw [hπx]; exact Subgroup.mem_zpowers _⟩
  obtain ⟨w₁, hw₁⟩ := M.π_surj ω3
  have hy₀π : M.π (w₁ * x₀ * w₁⁻¹) = τ3 := by
    rw [map_mul, map_mul, map_inv, hw₁, hπx, ω3_mul_τ3]
  have hy₀W : ((w₁ * x₀ * w₁⁻¹ : ↥(hsNB z s)) : G) ∈ W := M.mem_pre.mpr ⟨(w₁ * x₀ * w₁⁻¹).2,
    show M.π (w₁ * x₀ * w₁⁻¹) ∈ Subgroup.zpowers τ3 by rw [hy₀π]; exact Subgroup.mem_zpowers _⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥W, (a : G) = x₀ := ⟨⟨x₀, hx₀W⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ↥W, (b : G) = (w₁ : G) * x₀ * (w₁ : G)⁻¹ := ⟨⟨_, hy₀W⟩, by simp⟩
  have hoa : orderOf (a : G) = 3 := by rw [ha, hox]
  have hob : orderOf (b : G) = 3 := by
    rw [hb, show (w₁ : G) * x₀ * (w₁ : G)⁻¹ = MulAut.conj (w₁ : G) x₀ from rfl,
      MulEquiv.orderOf_eq, hox]
  have hap : IsPGroup 3 ↥(Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hoa, pow_one])
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hob, pow_one])
  have hidx : ∀ c : ↥W, orderOf (c : G) = 3 → ¬ 3 ∣ (Subgroup.zpowers c).index := by
    intro c hc
    have h1 := (Subgroup.zpowers c).card_mul_index
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hc, hcardW] at h1
    have : (Subgroup.zpowers c).index = 16 := by omega
    rw [this]
    decide
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥W (hbp.toSylow (hidx _ hob))
    (hap.toSylow (hidx _ hoa))
  have hcb : c * b * c⁻¹ ∈ Subgroup.zpowers a := by
    have h1 : c * b * c⁻¹ ∈ (c • hbp.toSylow (hidx _ hob) : Sylow 3 ↥W) := by
      rw [mem_smul_sylow', show c⁻¹ * (c * b * c⁻¹) * c = b by group]
      exact Subgroup.mem_zpowers _
    rw [hc] at h1
    exact h1
  obtain ⟨hcN, hcπ⟩ := M.mem_pre.mp c.2
  obtain ⟨c', hc'c, hc'π⟩ : ∃ c' : ↥(hsNB z s), (c' : G) = c ∧ M.π c' ∈ Subgroup.zpowers τ3 :=
    ⟨⟨c, hcN⟩, rfl, hcπ⟩
  obtain ⟨v, hv⟩ : ∃ v : ↥(hsNB z s), v = c' * w₁ := ⟨_, rfl⟩
  have hvx : (v : G) * x₀ * (v : G)⁻¹ ∈ Subgroup.zpowers (x₀ : G) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcb
    have e := congrArg Subtype.val hj
    rw [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha, hb] at e
    rw [hv, Subgroup.coe_mul, hc'c,
      show (c : G) * w₁ * x₀ * ((c : G) * w₁)⁻¹ = c * (w₁ * x₀ * (w₁ : G)⁻¹) * (c : G)⁻¹ by group,
      ← e]
    exact Subgroup.zpow_mem_zpowers _ j
  have hπv : M.π v = M.π c' * ω3 := by rw [hv, map_mul, hw₁]
  have hσ : M.π c' ∈ ({1, τ3, τ3 * τ3} : Finset (Equiv.Perm (Fin 6))) := by
    rcases mem_zpowers_τ3 hc'π with h1 | h1 | h1 <;> simp [h1]
  obtain ⟨hv3, hvτ, hvnot⟩ := zpowers_τ3_mul_ω3 _ hσ
  rw [← hπv] at hv3 hvτ hvnot
  have hvx' : (v : G) * x₀ = x₀ * v := by
    rcases eq_of_mem_zpowers_three hox hvx with h1 | h1 | h1
    · exfalso
      apply hx₀1
      calc (x₀ : G) = (v : G)⁻¹ * ((v : G) * x₀ * (v : G)⁻¹) * v := by group
        _ = 1 := by rw [h1]; group
    · calc (v : G) * x₀ = (v : G) * x₀ * (v : G)⁻¹ * v := by group
        _ = x₀ * v := by rw [h1]
    · exfalso
      have e : v * x₀ * v⁻¹ = x₀⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, map_inv, hπx, hvτ, mul_inv_cancel_right] at e'
      exact τ3_inv_ne e'.symm
  obtain ⟨hw3, hπw⟩ := M.pow_four_cube v hv3
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥(hsNB z s), w₀ = v ^ 4 := ⟨_, rfl⟩
  rw [← hw₀] at hw3 hπw
  have hπw' : M.π w₀ ∉ Subgroup.zpowers τ3 := by
    intro hm
    rcases mem_zpowers_τ3 hm with h1 | h1 | h1
    · exact hvnot 1 (by simp) (hπw.symm.trans h1)
    · exact hvnot τ3 (by simp) (hπw.symm.trans h1)
    · exact hvnot (τ3 * τ3) (by simp) (hπw.symm.trans h1)
  have hw₀1 : (w₀ : G) ≠ 1 := fun h1 => hπw' (by
    rw [show w₀ = 1 from Subtype.ext h1, map_one]
    exact Subgroup.one_mem _)
  refine ⟨x₀, w₀, hx₀H, hox, ?_, orderOf_eq_prime hw3 hw₀1, fun hm => hπw' ?_⟩
  · rw [hw₀, Subgroup.coe_pow]
    exact (Commute.pow_left (show Commute (v : G) x₀ from hvx') 4).eq
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hm
    have e : w₀ = x₀ ^ j := Subtype.ext (by rw [Subgroup.coe_zpow, hj])
    rw [e, map_zpow, hπx]
    exact Subgroup.zpow_mem_zpowers _ j

end S6Model

theorem exists_mem_centralizer_three [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) : ∃ w : G, w * x = x * w ∧ orderOf w = 3 ∧ w ∉ Subgroup.zpowers x := by
  obtain ⟨s, ⟨hsmemH, -⟩, hss, hsinv, g₀, hg₀⟩ := h.exists_invol_inverts_ZQ
  have hsnotK := h.not_mem_K_of_inverts hsinv
  obtain ⟨M⟩ := h.nonempty_s6Model hsmemH hsnotK hss hg₀
  obtain ⟨x₀, w₀, hx₀H, hx₀3, hwx, hw3, hwX⟩ := M.exists_pair_three h hsmemH hsnotK hss hg₀
  obtain ⟨g, -, hg⟩ := h.exists_conj_three hxH hx3 hx₀H hx₀3
  refine ⟨g * w₀ * g⁻¹, ?_, ?_, fun hm => hwX ?_⟩
  · have e : g * w₀ * g⁻¹ * (g * x₀ * g⁻¹) = g * x₀ * g⁻¹ * (g * w₀ * g⁻¹) := by
      calc g * w₀ * g⁻¹ * (g * x₀ * g⁻¹) = g * (w₀ * x₀) * g⁻¹ := by group
        _ = g * (x₀ * w₀) * g⁻¹ := by rw [hwx]
        _ = g * x₀ * g⁻¹ * (g * w₀ * g⁻¹) := by group
    rcases hg with hg | hg
    · rwa [hg] at e
    · rw [hg] at e
      calc g * w₀ * g⁻¹ * x = x * (x⁻¹ * (g * w₀ * g⁻¹)) * x := by group
        _ = x * ((g * w₀ * g⁻¹) * x⁻¹) * x := by rw [← e]
        _ = x * (g * w₀ * g⁻¹) := by group
  · rw [show g * w₀ * g⁻¹ = MulAut.conj g w₀ from rfl, MulEquiv.orderOf_eq, hw3]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hx : x = g * x₀ * g⁻¹ ∨ x⁻¹ = g * x₀ * g⁻¹ := by
      rcases hg with hg | hg
      · exact Or.inl hg.symm
      · exact Or.inr hg.symm
    have hconj : ∀ m : ℤ, (g * x₀ * g⁻¹) ^ m = g * x₀ ^ m * g⁻¹ := fun m => conj_zpow
    rcases hx with hx | hx
    · rw [hx, hconj] at hk
      have : w₀ = x₀ ^ k := by
        calc w₀ = g⁻¹ * (g * w₀ * g⁻¹) * g := by group
          _ = g⁻¹ * (g * x₀ ^ k * g⁻¹) * g := by rw [hk]
          _ = x₀ ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ k
    · have hk' : g * w₀ * g⁻¹ = (x⁻¹) ^ (-k) := by rw [zpow_neg, inv_zpow, inv_inv, hk]
      rw [hx, hconj] at hk'
      have : w₀ = x₀ ^ (-k) := by
        calc w₀ = g⁻¹ * (g * w₀ * g⁻¹) * g := by group
          _ = g⁻¹ * (g * x₀ ^ (-k) * g⁻¹) * g := by rw [hk']
          _ = x₀ ^ (-k) := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ (-k)

theorem cenQuot_s4_or_s5'
    {G : Type} [Group G] [Finite G] {z : G} {V : Subgroup G} (h : HSSetting z V) {x : G}
    (hxH : x ∈ hsH z) (hx3 : orderOf x = 3) :
    Nonempty (cenQuot x ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (cenQuot x ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨w, hwx, hw3, hwX⟩ := h.exists_mem_centralizer_three hxH hx3
  exact h.cenQuot_s4_or_s5 hxH hx3 hwx hw3 hwX

end HSSetting

end CFSG.Quasithin.HSType
