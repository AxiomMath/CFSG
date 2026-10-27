module

public import CFSG.RankThree.SubgroupLists2.SpectralBounds
public import Mathlib.GroupTheory.Commutator.Finite

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

section GroupLemmas

variable {G : Type*} [Group G]

theorem commute_of_conj_eq_inv (hZ3 : ∀ z ∈ Subgroup.center G, z ^ 3 = 1) {x y g : G}
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center G)
    (hgx : x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.center G)
    (hgy : y * (g * y * g⁻¹) ∈ Subgroup.center G) : x * y = y * x := by
  set ζ := x * y * x⁻¹ * y⁻¹ with hζdef
  set z₁ := x⁻¹ * (g * x * g⁻¹) with hz₁def
  set z₂ := y * (g * y * g⁻¹) with hz₂def
  have hζ : ∀ a : G, a * ζ = ζ * a := Subgroup.mem_center_iff.mp hxy
  have hz₁ : ∀ a : G, a * z₁ = z₁ * a := Subgroup.mem_center_iff.mp hgx
  have hz₂ : ∀ a : G, a * z₂ = z₂ * a := Subgroup.mem_center_iff.mp hgy
  have hgx' : g * x * g⁻¹ = x * z₁ := by rw [hz₁def]; group
  have hgy' : g * y * g⁻¹ = y⁻¹ * z₂ := by rw [hz₂def]; group
  have hxy' : x * y = ζ * y * x := by rw [hζdef]; group
  have e1 : (x * z₁) * (y⁻¹ * z₂) = ζ * ((y⁻¹ * z₂) * (x * z₁)) := by
    rw [← hgx', ← hgy']
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (ζ * y * x) * g⁻¹ := by rw [hxy']
      _ = (g * ζ) * (y * x) * g⁻¹ := by group
      _ = (ζ * g) * (y * x) * g⁻¹ := by rw [hζ g]
      _ = ζ * (g * y * g⁻¹ * (g * x * g⁻¹)) := by group
  have e2 : x * y⁻¹ * (z₁ * z₂) = ζ * (y⁻¹ * x) * (z₁ * z₂) := by
    calc x * y⁻¹ * (z₁ * z₂) = x * (y⁻¹ * z₁) * z₂ := by group
      _ = x * (z₁ * y⁻¹) * z₂ := by rw [hz₁ y⁻¹]
      _ = (x * z₁) * (y⁻¹ * z₂) := by group
      _ = ζ * ((y⁻¹ * z₂) * (x * z₁)) := e1
      _ = ζ * (y⁻¹ * (z₂ * x) * z₁) := by group
      _ = ζ * (y⁻¹ * (x * z₂) * z₁) := by rw [hz₂ x]
      _ = ζ * (y⁻¹ * x) * (z₂ * z₁) := by group
      _ = ζ * (y⁻¹ * x) * (z₁ * z₂) := by rw [hz₂ z₁]
  have e3 : x * y⁻¹ = ζ * (y⁻¹ * x) := mul_right_cancel e2
  have e4 : y⁻¹ * x = ζ * (x * y⁻¹) := by
    calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
      _ = y⁻¹ * (ζ * y * x) * y⁻¹ := by rw [hxy']
      _ = (y⁻¹ * ζ) * y * x * y⁻¹ := by group
      _ = (ζ * y⁻¹) * y * x * y⁻¹ := by rw [hζ y⁻¹]
      _ = ζ * (x * y⁻¹) := by group
  have e5 : ζ * ζ = 1 := by
    have h : ζ * ζ * (x * y⁻¹) = 1 * (x * y⁻¹) := by
      rw [one_mul, mul_assoc, ← e4, ← e3]
    exact mul_right_cancel h
  have hζ1 : ζ = 1 := by
    have h3 : ζ ^ 3 = 1 := hZ3 ζ hxy
    calc ζ = ζ * (ζ * ζ) := by rw [e5, mul_one]
      _ = ζ ^ 3 := (pow_three ζ).symm
      _ = 1 := h3
  rw [hxy', hζ1, one_mul]

theorem pow_three_eq_one_of_conj_eq_inv (hZ3 : ∀ z ∈ Subgroup.center G, z ^ 3 = 1) {y g : G}
    (hy3 : y ^ 3 ∈ Subgroup.center G) (hgy : y * (g * y * g⁻¹) ∈ Subgroup.center G) :
    y ^ 3 = 1 := by
  set z₂ := y * (g * y * g⁻¹) with hz₂def
  have hz₂ : ∀ a : G, a * z₂ = z₂ * a := Subgroup.mem_center_iff.mp hgy
  have hgy' : g * y * g⁻¹ = y⁻¹ * z₂ := by rw [hz₂def]; group
  have hc : (y⁻¹ * z₂) ^ 3 = y⁻¹ ^ 3 * z₂ ^ 3 := (show Commute y⁻¹ z₂ from hz₂ y⁻¹).mul_pow 3
  have h1 : g * y ^ 3 * g⁻¹ = y ^ 3 := by
    rw [Subgroup.mem_center_iff.mp hy3 g, mul_inv_cancel_right]
  have h2 : y ^ 3 = y⁻¹ ^ 3 := by
    rw [← h1, ← conj_pow, hgy', hc, hZ3 z₂ hgy, mul_one]
  have h6 : y ^ 3 * y ^ 3 = 1 := by
    calc y ^ 3 * y ^ 3 = y⁻¹ ^ 3 * y ^ 3 := by rw [← h2]
      _ = 1 := by rw [inv_pow, inv_mul_cancel]
  have h9 : (y ^ 3) ^ 3 = 1 := hZ3 _ hy3
  calc y ^ 3 = (y ^ 3) ^ 3 * (y ^ 3 * y ^ 3)⁻¹ := by group
    _ = 1 := by rw [h9, h6, one_mul, inv_one]

theorem pow_three_eq_one_of_conj_eq_mul (hZ3 : ∀ z ∈ Subgroup.center G, z ^ 3 = 1) {x y h : G}
    (hxy : x * y = y * x) (hy3 : y ^ 3 = 1)
    (hhy : (y * x)⁻¹ * (h * y * h⁻¹) ∈ Subgroup.center G) : x ^ 3 = 1 := by
  set z := (y * x)⁻¹ * (h * y * h⁻¹) with hzdef
  have hz : ∀ a : G, a * z = z * a := Subgroup.mem_center_iff.mp hhy
  have hhy' : h * y * h⁻¹ = y * x * z := by rw [hzdef]; group
  have h1 : (h * y * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  rw [hhy', (show Commute (y * x) z from hz (y * x)).mul_pow, hZ3 z hhy, mul_one,
    Commute.mul_pow hxy.symm, hy3, one_mul] at h1
  exact h1

end GroupLemmas

variable {K : Type*} [Field K] [Finite K]

theorem false_of_three_square (h3 : (3 : K) ≠ 0) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {e₁ e₂ g h : H ⧸ Subgroup.center H}
    (he₁ : e₁ ^ 3 = 1) (he₂ : e₂ ^ 3 = 1) (he₁₂ : e₁ * e₂ = e₂ * e₁) (he₁1 : e₁ ≠ 1)
    (hg₁ : g * e₁ * g⁻¹ = e₁) (hg₂ : g * e₂ * g⁻¹ = e₂⁻¹) (hh₁ : h * e₁ * h⁻¹ = e₁)
    (hh₂ : h * e₂ * h⁻¹ = e₂ * e₁) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e₁
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective e₂
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective h
  have hc : ∀ a : H, (a : H ⧸ Subgroup.center H) = 1 → a ∈ Subgroup.center H :=
    fun a ha => (QuotientGroup.eq_one_iff a).mp ha
  have hgy : y * (g' * y * g'⁻¹) ∈ Subgroup.center H := hc _ (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hg₂, mul_inv_cancel])
  have hxy : x * y = y * x := commute_of_conj_eq_inv hZ3
    (hc _ (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, he₁₂]
      group))
    (hc _ (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hg₁, inv_mul_cancel]))
    hgy
  have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_conj_eq_inv hZ3
    (hc _ (by rw [QuotientGroup.mk_pow, he₂])) hgy
  have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_conj_eq_mul (h := h') hZ3 hxy hy3 (hc _ (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, QuotientGroup.mk_mul, hh₂, inv_mul_cancel]))
  set X : GL (Fin 3) K := (x : GL (Fin 3) K) with hXdef
  set Y : GL (Fin 3) K := (y : GL (Fin 3) K) with hYdef
  set T := Subgroup.closure ({X, Y} : Set (GL (Fin 3) K)) with hTdef
  have hXY : X * Y = Y * X := congrArg Subtype.val hxy
  have hX3 : X ^ 3 = 1 := congrArg Subtype.val hx3
  have hY3 : Y ^ 3 = 1 := congrArg Subtype.val hy3
  have hTH : T ≤ H := by
    rw [hTdef, Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | rfl
    exacts [x.2, y.2]
  have hpair : ({X, Y} : Set (GL (Fin 3) K)).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [Commute.refl _, hXY, hXY.symm, Commute.refl _]
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    Set.centralizer_centralizer_comm_of_comm hpair a
      (Subgroup.closure_le_centralizer_centralizer _ ha) b
      (Subgroup.closure_le_centralizer_centralizer _ hb)
  have hTexp : ∀ a ∈ T, a ^ 3 = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      exacts [hX3, hY3]
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [Commute.mul_pow (hTcomm a ha b hb), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hTdet : ∀ a ∈ T, (a : Matrix (Fin 3) (Fin 3) K).det = 1 := fun a ha => hdet a (hTH ha)
  have h3' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast h3
  have hT9 : Nat.card T ≤ 9 := by
    have := card_le_sq_of_elementary h3' T hTcomm hTexp hTdet
    norm_num at this
    exact this
  set ψ : T →* H ⧸ Subgroup.center H :=
    (QuotientGroup.mk' (Subgroup.center H)).comp (Subgroup.inclusion hTH) with hψ
  have hxT : X ∈ T := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyT : Y ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hψx : ψ ⟨X, hxT⟩ = (x : H ⧸ Subgroup.center H) := rfl
  have hψy : ψ ⟨Y, hyT⟩ = (y : H ⧸ Subgroup.center H) := rfl
  have hxE : (x : H ⧸ Subgroup.center H) ∈ ψ.range := ⟨_, hψx⟩
  have hyE : (y : H ⧸ Subgroup.center H) ∈ ψ.range := ⟨_, hψy⟩
  have hEp : IsPGroup 3 ψ.range := by
    rintro ⟨_, ⟨a, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← map_pow, show a ^ 3 = 1 from Subtype.ext (hTexp a a.2),
      map_one, Subgroup.coe_one]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  have hconj : ∀ w ∈ Subgroup.zpowers (x : H ⧸ Subgroup.center H),
      (h' : H ⧸ Subgroup.center H) * w * (h' : H ⧸ Subgroup.center H)⁻¹ = w := by
    rintro _ ⟨k, rfl⟩
    simp only
    rw [← conj_zpow, hh₁]
  have hyZ : (y : H ⧸ Subgroup.center H) ∉ Subgroup.zpowers (x : H ⧸ Subgroup.center H) := by
    intro hy
    have h1 := hconj _ hy
    rw [hh₂] at h1
    exact he₁1 (mul_left_cancel (h1.trans (mul_one _).symm))
  have hlt : Subgroup.zpowers (x : H ⧸ Subgroup.center H) < ψ.range :=
    lt_of_le_of_ne (Subgroup.zpowers_le.mpr hxE) fun h => hyZ (h ▸ hyE)
  have hcardx : Nat.card (Subgroup.zpowers (x : H ⧸ Subgroup.center H)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he₁ he₁1]
  have h3n : 3 < 3 ^ n := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hcardx, hn] at this
  have hn2 : 2 ≤ n := by
    by_contra hn2
    push Not at hn2
    interval_cases n <;> norm_num at h3n
  have hE9 : 9 ≤ Nat.card ψ.range := by
    rw [hn]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hTE : Nat.card T ≤ Nat.card ψ.range := by omega
  have hbij := ψ.rangeRestrict_surjective.bijective_of_nat_card_le hTE
  obtain ⟨a, haT, ha1, c, hac⟩ := exists_scalar_of_card_eq_nine h3 T hTcomm hTexp hTdet
    (le_antisymm hT9 (hE9.trans (Nat.card_le_card_of_surjective _ ψ.rangeRestrict_surjective)))
  have hacen : (⟨a, hTH haT⟩ : H) ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    apply Units.ext
    change ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) =
      (a : Matrix (Fin 3) (Fin 3) K) * ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hac]
    exact (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).symm
  have hψa : ψ.rangeRestrict ⟨a, haT⟩ = ψ.rangeRestrict 1 := by
    apply Subtype.ext
    rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, map_one]
    exact (QuotientGroup.eq_one_iff _).mpr hacen
  exact ha1 (congrArg Subtype.val (hbij.1 hψa))

end CFSG.RankThree.SubgroupLists
