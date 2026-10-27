module

public import CFSG.Quasithin.Background.SmithB45TorF4W
public import CFSG.Quasithin.Background.SmithB45TorLift
public import CFSG.Quasithin.Background.SmithB42F4Main

public section

namespace CFSG.Quasithin.B45Tor

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp CFSG.Quasithin.B42F4

theorem ppd_four_ree {a ℓ : ℕ} (hℓ : ℓ.Prime) (hord : orderOf (2 : ZMod ℓ) = 4 * (2 * a + 1)) :
    3 < ℓ ∧ ((ℓ : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 ∨
      (ℓ : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, orderOf_eq_zero_iff'.2 (fun n hn => by rw [zero_pow (by omega)]; exact zero_ne_one)]
      at hord
    omega
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h2 : orderOf (2 : ZMod 3) ∣ 2 := orderOf_dvd_of_pow_eq_one (by decide)
    rw [hord] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨by have := hℓ.two_le; omega, ?_⟩
  set x : ZMod ℓ := 2 ^ (2 * a + 1) with hx
  set s : ZMod ℓ := 2 ^ (a + 1) with hs'
  have hs : s ^ 2 = 2 * x := by rw [hs', hx]; ring
  have h4 : x ^ 4 = 1 := by
    rw [hx, ← pow_mul, show (2 * a + 1) * 4 = 4 * (2 * a + 1) by ring, ← hord,
      pow_orderOf_eq_one]
  have h2 : x ^ 2 ≠ 1 := fun h1 => by
    have : 4 * (2 * a + 1) ∣ 2 * (2 * a + 1) :=
      hord ▸ orderOf_dvd_of_pow_eq_one (by rw [mul_comm, pow_mul, ← hx, h1])
    have := Nat.le_of_dvd (by omega) this
    omega
  have e1 : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
    rw [show (x ^ 2 - 1) * (x ^ 2 + 1) = x ^ 4 - 1 by ring, h4, sub_self]
  have e2 : x ^ 2 + 1 = 0 := (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 h2)
  have hprod : (x - s + 1) * (x + s + 1) = 0 := by
    have e : (x - s + 1) * (x + s + 1) = (x ^ 2 + 1) + (2 * x - s ^ 2) := by ring
    rw [e, e2, hs, sub_self, add_zero]
  rcases mul_eq_zero.1 hprod with h | h
  · left
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h
  · right
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h

theorem closure_le_normalizer_GL23 {G : Type*} [Group G] {R : Subgroup G} {i j h t : G}
    (hd : IsGL23Data R i j h t) :
    Subgroup.closure ({i, j, h, t} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [hd.mem_i, hd.mem_j, hd.mem_h, hd.mem_t]

section Module

variable {K : Type}
  [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
  (hK : Nat.card K = 2 ^ (2 * a + 1))
variable {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
  (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥)
  (e : L ⧸ Subgroup.center L ≃* F4.reeGamma K a)

include ha hK hV hZL in
theorem exists_classT_index :
    ∃ y : L, (y : MulAut V) * y = 1 ∧
      IsTConj a K ((modelProj L e y : F4.reeGamma K a) : ModGL F4.tag K) ∧
      2 ^ (12 * (2 * a + 1)) ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  obtain ⟨p, hp, hp2, hord⟩ := exists_prime_orderOf_two_eq (4 * (2 * a + 1)) (by omega) (by omega)
  obtain ⟨hp3, hpd⟩ := ppd_four_ree hp hord
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, i, j, h, t, hRc, hRp, hRcard, hd, hii, hT⟩ := exists_reePlane ha hK hp hp3 hpd
  obtain ⟨y, hy⟩ := modelProj_surjective L e (i * i)
  have hm : ∀ n : ℕ, 0 < n → orderOf (2 : ZMod p) ∣ 2 * n → 2 * (2 * a + 1) ≤ n := by
    intro n hn hdvd
    rw [hord] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    exact Nat.le_of_dvd hn ⟨c, by linarith⟩
  have hidx := two_pow_le_index_of_orbits hV L hZL e hp2 hRc hRp hRcard
    (closure_le_normalizer_GL23 hd)
    (fun K hKR hK => six_le_orbit hp2 (by omega) hRc hRp hRcard hd hKR hK) hii
    hd.toIsQ8Data.inv_ii hm hy
  refine ⟨y, ?_, by rw [hy]; exact hT,
    by rw [show 12 * (2 * a + 1) = 6 * (2 * (2 * a + 1)) by ring]; exact hidx⟩
  have h1 : modelProj L e (y * y) = 1 := by rw [map_mul, hy, hii]
  have h2 := mem_center_of_modelProj_eq_one L e h1
  rw [hZL, Subgroup.mem_bot] at h2
  exact congrArg Subtype.val h2

include ha hK hV hZL in
theorem two_pow_le_index_classT {x : L}
    (hx : IsTConj a K ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K)) :
    2 ^ (12 * (2 * a + 1)) ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨y, -, hyT, hidx⟩ := exists_classT_index ha hK hV L hZL e
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨g', hg', hgy⟩ := hyT
  have hconj : modelProj L e x = ⟨g⁻¹ * g', mul_mem (inv_mem hg) hg'⟩ * modelProj L e y *
      (⟨g⁻¹ * g', mul_mem (inv_mem hg) hg'⟩ : F4.reeGamma K a)⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e1 : ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K) =
        g⁻¹ * sylowL a K 1 * g := by rw [← hgx]; group
    rw [e1, ← hgy]
    group
  rw [index_eq_of_modelProj_conj L hZL e hconj]
  exact hidx

include ha hK hV hZL in
theorem two_pow_le_index_classZ {x : L}
    (hx : IsZConj a K ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K)) :
    2 ^ (6 * (2 * a + 1)) ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨p₁, hp₁, p₂, hp₂, ht⟩ := exists_tOne_eq_conj_mul_conj (a := a) hK
  obtain ⟨l₁, hl₁⟩ := modelProj_surjective L e ⟨p₁ * g, mul_mem hp₁ hg⟩
  obtain ⟨l₂, hl₂⟩ := modelProj_surjective L e ⟨p₂ * g, mul_mem hp₂ hg⟩
  set xt : L := l₁ * x * l₁⁻¹ * (l₂ * x * l₂⁻¹) with hxt
  have hxtT : IsTConj a K ((modelProj L e xt : F4.reeGamma K a) : ModGL F4.tag K) := by
    refine ⟨1, one_mem _, ?_⟩
    have e1 : ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K) =
        g⁻¹ * sylowH a K 0 1 * g := by rw [← hgx]; group
    rw [hxt, map_mul, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hl₁, hl₂]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, e1, one_mul, inv_one, mul_one]
    rw [ht]
    group
  have h1 := two_pow_le_index_classT ha hK hV L hZL e hxtT
  have h2 : (fixV (Subgroup.zpowers (xt : MulAut V))).index ≤
      (fixV (Subgroup.zpowers (x : MulAut V))).index ^ 2 := by
    have hxtV : (xt : MulAut V) = (l₁ : MulAut V) * x * (l₁ : MulAut V)⁻¹ *
        ((l₂ : MulAut V) * x * (l₂ : MulAut V)⁻¹) := rfl
    rw [hxtV, sq]
    refine (CFSG.QuasithinUnique.Setup.X5.index_fixV_mul_le _ _).trans ?_
    rw [CFSG.QuasithinUnique.Setup.X5.index_fixV_conj,
      CFSG.QuasithinUnique.Setup.X5.index_fixV_conj]
  by_contra hlt
  push Not at hlt
  have h3 : (fixV (Subgroup.zpowers (x : MulAut V))).index ^ 2 < (2 ^ (6 * (2 * a + 1))) ^ 2 :=
    Nat.pow_lt_pow_left hlt two_ne_zero
  rw [← pow_mul, show 6 * (2 * a + 1) * 2 = 12 * (2 * a + 1) by ring] at h3
  omega

end Module

end CFSG.Quasithin.B45Tor
