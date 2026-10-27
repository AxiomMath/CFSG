module

public import CFSG.Quasithin.Background.SmithB45TorD4B
public import CFSG.Quasithin.Background.SmithB45TorLift
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.SmithB45TorCrit

public section

namespace CFSG.Quasithin.B45Tor

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp CFSG.Quasithin.B42D4

theorem ppd_six {ℓ m : ℕ} (hℓ : ℓ.Prime) (hm : 1 ≤ m) (h : orderOf (2 : ZMod ℓ) = 6 * m) :
    3 < ℓ ∧ ℓ ∣ (2 ^ m) ^ 2 - 2 ^ m + 1 := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, orderOf_eq_zero_iff'.2 (fun n hn => by rw [zero_pow (by omega)]; exact zero_ne_one)]
      at h
    omega
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h2 : orderOf (2 : ZMod 3) ∣ 2 := orderOf_dvd_of_pow_eq_one (by decide)
    rw [h] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨by have := hℓ.two_le; omega, ?_⟩
  set x : ZMod ℓ := 2 ^ m with hx
  have h6 : x ^ 6 = 1 := by rw [hx, ← pow_mul, mul_comm, ← h, pow_orderOf_eq_one]
  have h3 : x ^ 3 ≠ 1 := fun h1 => by
    have : 6 * m ∣ 3 * m := h ▸ orderOf_dvd_of_pow_eq_one (by rw [mul_comm, pow_mul, ← hx, h1])
    have := Nat.le_of_dvd (by omega) this
    omega
  have h2 : x ^ 2 ≠ 1 := fun h1 => by
    have : 6 * m ∣ 2 * m := h ▸ orderOf_dvd_of_pow_eq_one (by rw [mul_comm, pow_mul, ← hx, h1])
    have := Nat.le_of_dvd (by omega) this
    omega
  have e1 : (x ^ 3 - 1) * (x ^ 3 + 1) = 0 := by
    rw [show (x ^ 3 - 1) * (x ^ 3 + 1) = x ^ 6 - 1 by ring, h6, sub_self]
  have e2 : x ^ 3 + 1 = 0 := (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 h3)
  have e3 : (x + 1) * (x ^ 2 - x + 1) = 0 := by rw [← e2]; ring
  have e4 : x + 1 ≠ 0 := fun h0 => h2 (by
    have : x ^ 2 - 1 = (x + 1) * (x - 1) := by ring
    rw [h0, zero_mul] at this
    exact sub_eq_zero.1 this)
  have e5 : x ^ 2 - x + 1 = 0 := (mul_eq_zero.1 e3).resolve_left e4
  have hle : 2 ^ m ≤ (2 ^ m) ^ 2 := Nat.le_self_pow two_ne_zero _
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hle]
  rw [← hx]
  exact e5

theorem cast_phi6 (f : ℕ) :
    (((2 ^ f) ^ 2 - 2 ^ f + 1 : ℕ) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + (-1) * (2 ^ f : ℕ) + 1 := by
  have hle : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow two_ne_zero _
  push_cast [Nat.cast_sub hle]
  ring

theorem exists_plane_prime {f : ℕ} (hf : 1 ≤ f) :
    ∃ (ε : ℤ) (d p : ℕ), (ε = 1 ∨ ε = -1) ∧
      (d : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1 ∧ p.Prime ∧ 3 < p ∧ p ∣ d ∧
      ∀ n : ℕ, 0 < n → orderOf (2 : ZMod p) ∣ 2 * n → 3 * f ≤ n := by
  rcases Nat.lt_or_ge f 2 with h1 | h2
  · obtain rfl : f = 1 := by omega
    refine ⟨1, 7, 7, Or.inl rfl, by norm_num, by norm_num, by norm_num, dvd_rfl, ?_⟩
    have h7 : orderOf (2 : ZMod 7) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime (by decide) (by decide)
    intro n hn hdvd
    rw [h7] at hdvd
    omega
  · obtain ⟨p, hp, -, hord⟩ := exists_prime_orderOf_two_eq (6 * f) (by omega) (by omega)
    obtain ⟨hp3, hpd⟩ := ppd_six hp hf hord
    refine ⟨-1, (2 ^ f) ^ 2 - 2 ^ f + 1, p, Or.inr rfl, cast_phi6 f, hp, hp3, hpd, ?_⟩
    intro n hn hdvd
    rw [hord] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    exact Nat.le_of_dvd hn ⟨c, by linarith⟩

section Module

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
variable {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
  (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥)
  (e : L ⧸ Subgroup.center L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hf hK hσ hV hZL in
theorem exists_classB_index :
    ∃ y : L, (y : MulAut V) * y = 1 ∧
      ConjC σ ((modelProj L e y : C₀) : ModGL TwistTag.D4.tag K) (ox₁ σ 1) ∧
      2 ^ (12 * f) ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  obtain ⟨ε, d, p, hε, hd, hp, hp3, hpd, hm⟩ := exists_plane_prime hf
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, i, j, h, hRc, hRp, hRcard, hq, hii, hB, -⟩ :=
    exists_threeSix_classB hf hK σ hσ hε hd hp hp3 hpd
  obtain ⟨y, hy⟩ := modelProj_surjective L e (i * i)
  have hidx := two_pow_le_index_of_orbits hV L hZL e (by omega) hRc hRp hRcard
    (closure_le_normalizer hq) (fun K hKR hK => four_le_orbit (by omega) hRp hq hKR hK) hii
    hq.inv_ii hm hy
  refine ⟨y, ?_, by rw [hy]; exact hB, by rw [show 12 * f = 4 * (3 * f) by ring]; exact hidx⟩
  have h1 : modelProj L e (y * y) = 1 := by rw [map_mul, hy, hii]
  have h2 := mem_center_of_modelProj_eq_one L e h1
  rw [hZL, Subgroup.mem_bot] at h2
  exact congrArg Subtype.val h2

include hf hK hσ hV hZL in
theorem two_pow_le_index_classB {x : L}
    (hx : ConjC σ ((modelProj L e x : C₀) : ModGL TwistTag.D4.tag K) (ox₁ σ 1)) :
    2 ^ (12 * f) ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨y, -, hyB, hidx⟩ := exists_classB_index hf hK σ hσ hV L hZL e
  obtain ⟨g, hg, hgy⟩ := hyB.trans σ hx.symm
  have hconj : modelProj L e x = ⟨g, hg⟩ * modelProj L e y * (⟨g, hg⟩ : C₀)⁻¹ :=
    Subtype.ext hgy.symm
  rw [index_eq_of_modelProj_conj L hZL e hconj]
  exact hidx

include hf hK hσ hV hZL e in
theorem two_pow_le_card : 2 ^ (24 * f) ≤ Nat.card V := by
  obtain ⟨y, hy, -, hidx⟩ := exists_classB_index hf hK σ hσ hV L hZL e
  calc 2 ^ (24 * f) = (2 ^ (12 * f)) ^ 2 := by rw [← pow_mul]; ring_nf
    _ ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index ^ 2 := Nat.pow_le_pow_left hidx 2
    _ ≤ Nat.card V := index_fixV_sq_le_card hV hy

include hf hK hσ hV hZL e in
theorem two_pow_le_index_phi6 {ℓ : ℕ} (hℓ : ℓ.Prime) (hord : orderOf (2 : ZMod ℓ) = 6 * f)
    {g : MulAut V} (hg : g ∈ L) (hgo : orderOf g = ℓ) :
    2 ^ (3 * orderOf (2 : ZMod ℓ)) ≤ (fixV (Subgroup.zpowers g)).index := by
  obtain ⟨hℓ3, hℓd⟩ := ppd_six hℓ hf hord
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨R, i, j, h, hRc, hRp, hRcard, hq, -, -, hconj⟩ :=
    exists_threeSix_classB hf hK σ hσ (Or.inr rfl) (cast_phi6 f) hℓ hℓ3 hℓd
  set x : L := ⟨g, hg⟩ with hxdef
  have hxo : orderOf (modelProj L e x) = ℓ := by
    rw [orderOf_injective _ (modelProj_injective L hZL e), ← Subgroup.orderOf_coe]
    exact hgo
  obtain ⟨c, hc⟩ := hconj _ hxo
  obtain ⟨x₁, hx₁⟩ := modelProj_surjective L e (c * modelProj L e x * c⁻¹)
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    rw [map_one] at hx₁
    have h1 : modelProj L e x = 1 := by
      calc modelProj L e x = c⁻¹ * (c * modelProj L e x * c⁻¹) * c := by group
        _ = 1 := by rw [← hx₁]; group
    rw [h1, orderOf_one] at hxo
    exact hℓ.one_lt.ne hxo
  have hidx := two_pow_le_index_of_orbits_mem hV L hZL e (by omega) hRc hRp hRcard
    (closure_le_normalizer hq) (fun K hKR hK => four_le_orbit (by omega) hRp hq hKR hK)
    (x := x₁) (by rw [hx₁]; exact hc) hx₁1
  rw [index_eq_of_modelProj_conj L hZL e hx₁] at hidx
  exact hidx

include hf hK hσ hV hZL e in
theorem doubleDispOut_trialityD4 :
    DoubleDispOut L (fun ℓ => ∃ e : ℕ, 2 * e = f ∧ orderOf (2 : ZMod ℓ) = 12 * e) := by
  refine doubleDispOut_of_orderOf_eq ?_
  rintro ℓ ⟨e', he', hord⟩ hℓ - g hg hgo -
  have hord' : orderOf (2 : ZMod ℓ) = 6 * f := by rw [hord]; omega
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_)
    (two_pow_le_index_phi6 hf hK σ hσ hV L hZL e hℓ hord' hg hgo)
  omega

end Module

end CFSG.Quasithin.B45Tor
