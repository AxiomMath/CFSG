module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206p
import CFSG.LocalAnalysis.UniquenessCase.UC22S206l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptCore ptHom)

variable {G : Type} [Group G]

theorem uc22s206q_conj_center {W : Type*} [Group W] {z : W} (hz : z ∈ Subgroup.center W)
    (w : W) : z * w * z⁻¹ = w := by
  rw [← Subgroup.mem_center_iff.mp hz w, mul_inv_cancel_right]

theorem uc22s206q_conj_mul {W : Type*} [Group W] {z : W} (hz : z ∈ Subgroup.center W)
    (x w : W) : x * (z * w) * x⁻¹ = z * (x * w * x⁻¹) := by
  calc x * (z * w) * x⁻¹ = x * z * w * x⁻¹ := by group
    _ = z * x * w * x⁻¹ := by rw [Subgroup.mem_center_iff.mp hz x]
    _ = z * (x * w * x⁻¹) := by group

theorem uc22s206q_conj_mul_mul {W : Type*} [Group W] {z₁ z₂ : W}
    (hz₁ : z₁ ∈ Subgroup.center W) (hz₂ : z₂ ∈ Subgroup.center W) (w y : W) :
    z₁ * w * (z₂ * y) * (z₁ * w)⁻¹ = z₂ * (w * y * w⁻¹) := by
  calc z₁ * w * (z₂ * y) * (z₁ * w)⁻¹ = z₁ * (w * (z₂ * y) * w⁻¹) * z₁⁻¹ := by group
    _ = w * (z₂ * y) * w⁻¹ := uc22s206q_conj_center hz₁ _
    _ = z₂ * (w * y * w⁻¹) := uc22s206q_conj_mul hz₂ w y

theorem uc22s206q_order_three {W : Type*} [Group W] {x g : W}
    (hu : x ^ 3 ∈ Subgroup.center W) (hζ : g * x * g⁻¹ * x ∈ Subgroup.center W) :
    ∃ z ∈ Subgroup.center W, (x * z) ^ 3 = 1 := by
  obtain ⟨ζ, hζc, e⟩ : ∃ ζ ∈ Subgroup.center W, g * x * g⁻¹ = ζ * x⁻¹ := ⟨_, hζ, by group⟩
  have h2 : x ^ 3 * x ^ 3 = ζ ^ 3 := by
    have h3 : x ^ 3 = ζ ^ 3 * (x ^ 3)⁻¹ := by
      calc x ^ 3 = g * x ^ 3 * g⁻¹ := by
            rw [Subgroup.mem_center_iff.mp hu g, mul_inv_cancel_right]
        _ = (ζ * x⁻¹) ^ 3 := by rw [← conj_pow, e]
        _ = ζ ^ 3 * (x ^ 3)⁻¹ := by
            rw [Commute.mul_pow (Subgroup.mem_center_iff.mp hζc x⁻¹).symm, inv_pow]
    exact eq_mul_inv_iff_mul_eq.mp h3
  refine ⟨ζ * (x ^ 3)⁻¹, mul_mem hζc (inv_mem hu), ?_⟩
  rw [Commute.mul_pow (Subgroup.mem_center_iff.mp (mul_mem hζc (inv_mem hu)) x),
    Commute.mul_pow (Subgroup.mem_center_iff.mp (inv_mem hu) ζ), ← h2]
  group

theorem uc22s206q_lift {W S : Type*} [Group W] [Group S] (π : W →* S)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center W) {a h : S}
    (ha3 : a ^ 3 = 1) (ha : h * a * h⁻¹ = a⁻¹) : ∃ x : W, x ^ 3 = 1 ∧ π x = a := by
  obtain ⟨x₀, rfl⟩ := hπ a
  obtain ⟨g, rfl⟩ := hπ h
  have hc : ∀ {w : W}, π w = 1 → w ∈ Subgroup.center W := fun {w} hw => by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hw
  obtain ⟨z, hz, hz3⟩ := uc22s206q_order_three (hc (by rw [map_pow, ha3])) (g := g)
    (hc (by rw [map_mul, map_mul, map_mul, map_inv, ha, inv_mul_cancel]))
  refine ⟨x₀ * z, hz3, ?_⟩
  have hπz : π z = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hz)
  rw [map_mul, hπz, mul_one]

theorem uc22s206q_commute {W : Type*} [Group W] {x y g : W}
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center W) (hx3 : x ^ 3 = 1)
    (hgx : g * x * g⁻¹ * x ∈ Subgroup.center W)
    (hgy : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.center W) : x * y = y * x := by
  obtain ⟨c, hc, e1⟩ : ∃ c ∈ Subgroup.center W, x * y * x⁻¹ = c * y := ⟨_, hxy, by group⟩
  obtain ⟨z₁, hz₁, e2⟩ : ∃ z ∈ Subgroup.center W, g * x * g⁻¹ = z * x⁻¹ := ⟨_, hgx, by group⟩
  obtain ⟨z₂, hz₂, e3⟩ : ∃ z ∈ Subgroup.center W, g * y * g⁻¹ = z * y := ⟨_, hgy, by group⟩
  have hA : z₂ * (x⁻¹ * y * x⁻¹⁻¹) = z₂ * (c * y) := by
    calc z₂ * (x⁻¹ * y * x⁻¹⁻¹) = z₁ * x⁻¹ * (z₂ * y) * (z₁ * x⁻¹)⁻¹ :=
          (uc22s206q_conj_mul_mul hz₁ hz₂ x⁻¹ y).symm
      _ = g * (x * y * x⁻¹) * g⁻¹ := by rw [← e2, ← e3]; group
      _ = c * (g * y * g⁻¹) := by rw [e1, uc22s206q_conj_mul hc g y]
      _ = z₂ * (c * y) := by
          rw [e3, ← mul_assoc, ← mul_assoc, Subgroup.mem_center_iff.mp hz₂ c]
  have hB := mul_left_cancel hA
  have hC : y = c * (c * y) := by
    calc y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
      _ = c * (c * y) := by rw [e1, uc22s206q_conj_mul hc x⁻¹ y, hB]
  have hD : y = c * (c * (c * y)) := by
    calc y = x ^ 3 * y * (x ^ 3)⁻¹ := by rw [hx3]; group
      _ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by rw [pow_three]; group
      _ = c * (c * (c * y)) := by
          rw [e1, uc22s206q_conj_mul hc x y, e1, uc22s206q_conj_mul hc x (c * y),
            uc22s206q_conj_mul hc x y, e1]
  have hc1 : c = 1 := by
    have h1 : c * y = 1 * y := by
      calc c * y = c * (c * (c * y)) := by rw [← hC]
        _ = 1 * y := by rw [← hD, one_mul]
    exact mul_right_cancel h1
  rw [hc1, one_mul] at e1
  exact mul_inv_eq_iff_eq_mul.mp e1

theorem uc22s206q_zpow_eq_one {W S : Type*} [Group W] [Group S] (π : W →* S) {x : W}
    (hx3 : x ^ 3 = 1) (hx1 : π x ≠ 1) {m : ℤ} (hm : π x ^ m = 1) : x ^ m = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : orderOf (π x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hx1
  have h2 : orderOf x = 3 := orderOf_eq_prime hx3 fun h => hx1 (by rw [h, map_one])
  rw [← orderOf_dvd_iff_zpow_eq_one, h1] at hm
  rw [← orderOf_dvd_iff_zpow_eq_one, h2]
  exact hm

theorem uc22s206q_E9 {S : Type*} [Group S] {a b h : S} (hab : a * b = b * a) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha : h * a * h⁻¹ = a)
    (hb : h * b * h⁻¹ = b⁻¹) :
    IsElemAbelian 3 (zpowers a ⊔ zpowers b) ∧
      Nat.card ↥(zpowers a ⊔ zpowers b) = 3 ^ (1 + 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine uc22s206p_elemAbelian_sup (isElemAbelian_zpowers ha3) (isElemAbelian_zpowers hb3)
    (fun x hx y hy => ?_) (uc22s206p_disjoint ha hb hb3) ?_ ?_
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow hab m n
  · rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1, pow_one]
  · rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1, pow_one]

theorem uc22s206q_E27 {W S : Type*} [Group W] [Group S] (π : W →* S) {x y z : W}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hz : z ∈ Subgroup.center W)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hπz : π z = 1) (hx1 : π x ≠ 1) (hy1 : π y ≠ 1)
    (hd : Disjoint (zpowers (π x)) (zpowers (π y))) :
    IsElemAbelian 3 (zpowers x ⊔ (zpowers y ⊔ zpowers z)) ∧
      Nat.card ↥(zpowers x ⊔ (zpowers y ⊔ zpowers z)) = 3 ^ (1 + (1 + 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ∀ {w : W}, w ^ 3 = 1 → w ≠ 1 → Nat.card (zpowers w) = 3 ^ 1 := fun h3 h1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime h3 h1, pow_one]
  have hne : ∀ {w : W}, π w ≠ 1 → w ≠ 1 := fun h h1 => h (by rw [h1, map_one])
  have hd₁ : Disjoint (zpowers y) (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro w hwy hwz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hwy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hwz
    refine uc22s206q_zpow_eq_one π hy3 hy1 ?_
    rw [← map_zpow, ← hk, map_zpow, hπz, one_zpow]
  obtain ⟨hB, hBcard⟩ := uc22s206p_elemAbelian_sup (isElemAbelian_zpowers hy3)
    (isElemAbelian_zpowers hz3)
    (fun a _ b hb => Subgroup.mem_center_iff.mp ((zpowers_le.mpr hz) hb) a) hd₁
    (hcard hy3 (hne hy1)) (hcard hz3 hz1)
  have hle : zpowers y ⊔ zpowers z ≤ (zpowers (π y)).comap π :=
    sup_le (zpowers_le.mpr (mem_comap.mpr (mem_zpowers _)))
      (zpowers_le.mpr (by rw [mem_comap, hπz]; exact one_mem _))
  have hd₂ : Disjoint (zpowers x) (zpowers y ⊔ zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro w hwx hwB
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hwx
    refine uc22s206q_zpow_eq_one π hx3 hx1 ?_
    rw [← map_zpow]
    exact Subgroup.disjoint_def.mp hd (by rw [map_zpow]; exact zpow_mem_zpowers _ _)
      (mem_comap.mp (hle hwB))
  have hC : zpowers y ⊔ zpowers z ≤ Subgroup.centralizer (zpowers x : Set W) := by
    refine sup_le (zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_))
      (zpowers_le.mpr (Subgroup.center_le_centralizer _ hz))
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw
    exact Commute.zpow_left hxy m
  exact uc22s206p_elemAbelian_sup (isElemAbelian_zpowers hx3) hB
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hC hb) a ha) hd₂
    (hcard hx3 (hne hx1)) hBcard

theorem uc22s206q_not_dvd {W S : Type*} [Group W] [Finite W] [Group S] (π : W →* S)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center W) {a b h₁ h₂ : S}
    (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (h1a : h₁ * a * h₁⁻¹ = a⁻¹) (h1b : h₁ * b * h₁⁻¹ = b) (h2a : h₂ * a * h₂⁻¹ = a)
    (h2b : h₂ * b * h₂⁻¹ = b⁻¹) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup W) ≤ 2) :
    ¬ 3 ∣ Nat.card (Subgroup.center W) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ {w : W}, π w = 1 → w ∈ Subgroup.center W := fun {w} hw => by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hw
  obtain ⟨x, hx3, rfl⟩ := uc22s206q_lift π hπ hker ha3 h1a
  obtain ⟨y, hy3, rfl⟩ := uc22s206q_lift π hπ hker hb3 h2b
  obtain ⟨g, rfl⟩ := hπ h₁
  have hxy : x * y = y * x := by
    refine uc22s206q_commute (g := g) (hc ?_) hx3 (hc ?_) (hc ?_)
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab, mul_inv_cancel_right,
        mul_inv_cancel]
    · rw [map_mul, map_mul, map_mul, map_inv, h1a, inv_mul_cancel]
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1b, mul_inv_cancel]
  intro h3d
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3d
  have hz3 : (z : W) ^ 3 = 1 := by
    rw [← hz]
    exact congrArg Subtype.val (pow_orderOf_eq_one z)
  have hz1 : (z : W) ≠ 1 := fun h => by
    rw [show z = 1 from Subtype.ext h, orderOf_one] at hz
    omega
  have hπz : π z = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact z.2)
  obtain ⟨hE, hEcard⟩ := uc22s206q_E27 π hx3 hy3 hxy z.2 hz3 hz1 hπz ha1 hb1
    (uc22s206p_disjoint h2a h2b hb3)
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hE hEcard
  omega

theorem uc22s206q_pRank [Finite G] {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9}
    {W : Type*} [Group W] [Finite W] (ψ : ↥(ptCore α i) →* W ⧸ Subgroup.center W)
    (hψ : ψ.range ≠ ⊥) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup W) ≤ 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (W ⧸ Subgroup.center W)) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, h₁, h₂, hab, ha3, hb3, h1a, h1b, h2a, h2b, ha1, hb1⟩ :=
    uc22s206p_elements α hα hker i
  have hle : ∀ k, ψ k = 1 → ptHom α i k = 1 := fun k hk => by
    by_contra hk1
    apply hψ
    have htop := uc22s206l_eq_top_of_normal α hα hker ψ.normal_ker (MonoidHom.mem_ker.mpr hk)
      hk1
    rw [eq_bot_iff]
    rintro _ ⟨k', rfl⟩
    have hk' : k' ∈ ψ.ker := by
      rw [htop]
      exact mem_top k'
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp hk')
  have hconj : ∀ {h x y : ↥(ptCore α i)}, h * x * h⁻¹ = y → ψ h * ψ x * (ψ h)⁻¹ = ψ y :=
    fun hxy => by rw [← map_inv, ← map_mul, ← map_mul, hxy]
  have hab' : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hab]
  have ha3' : ψ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hb3' : ψ b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have ha1' : ψ a ≠ 1 := fun h => ha1 (hle a h)
  have hb1' : ψ b ≠ 1 := fun h => hb1 (hle b h)
  apply le_antisymm
  · exact (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center W)
      (uc22s206q_not_dvd (QuotientGroup.mk' (Subgroup.center W))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hab' ha3' hb3' ha1' hb1'
        ((hconj h1a).trans (map_inv ψ a)) (hconj h1b) (hconj h2a)
        ((hconj h2b).trans (map_inv ψ b)) h3)).le.trans h3
  · obtain ⟨hE, hEcard⟩ := uc22s206q_E9 hab' ha3' hb3' ha1' hb1' (hconj h2a)
      ((hconj h2b).trans (map_inv ψ b))
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hEcard

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
