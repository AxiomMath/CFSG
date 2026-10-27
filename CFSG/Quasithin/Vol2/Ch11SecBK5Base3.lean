module

public import CFSG.Quasithin.Background.HSL3PairNPrime
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base11

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank K8
open scoped Pointwise

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def actPerm : ↥(normD K) →* Equiv.Perm (Option K) where
  toFun x :=
    { toFun := act x
      invFun := act x⁻¹
      left_inv := act_inv_act x
      right_inv := fun p => by
        have := act_inv_act x⁻¹ p
        rwa [inv_inv] at this }
  map_one' := Equiv.ext act_one
  map_mul' x y := Equiv.ext (act_mul x y)

theorem mem_dgSub_of_act {x : MulAut (W6 K)} (hx : x ∈ normD K) (hlin : x ∈ linSub)
    (hact : ∀ p, act ⟨x, hx⟩ p = p) : x ∈ dgSub K := by
  obtain ⟨A, M, rfl⟩ := exists_tensHom hx hlin
  have key : ∀ p : Option K, ∃ c : K,
      (M : Matrix (Fin 2) (Fin 2) K) 0 0 * ptA p + (M : Matrix (Fin 2) (Fin 2) K) 0 1 * ptB p =
        c * ptA p ∧
      (M : Matrix (Fin 2) (Fin 2) K) 1 0 * ptA p + (M : Matrix (Fin 2) (Fin 2) K) 1 1 * ptB p =
        c * ptB p := by
    intro p
    have h := (act_eq_iff _ _ _).mp (hact p)
    unfold natPt at h
    rw [map_natSub_tensHom] at h
    exact exists_smul_of_natSub_eq h
  obtain ⟨c₁, e₁, e₂⟩ := key none
  obtain ⟨c₂, e₃, e₄⟩ := key (some 0)
  obtain ⟨c₃, e₅, e₆⟩ := key (some 1)
  simp only [ptA, ptB, mul_zero, mul_one, add_zero, zero_add] at e₁ e₂ e₃ e₄ e₅ e₆
  refine mem_dgSub_of_scalar A M e₁ e₄ ?_
  rw [e₁, add_zero] at e₅
  rw [e₄, zero_add] at e₆
  rw [e₅, e₆]

omit [Finite K] in
theorem mem_diagSL_of_two_pow [CharP K 2] {x : MulAut (W6 K)} (hx : x ∈ dgSub K) {j : ℕ}
    (hxj : x ^ 2 ^ j = 1) : x ∈ diagSL K := by
  obtain ⟨A, rfl⟩ := hx
  have hAj : A ^ 2 ^ j = 1 := by
    apply matAut_dgHom_injective
    rw [matAut_dgHom_pow, matAut_dgHom_one]
    exact hxj
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K).det) hAj
    simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, Units.val_one, Matrix.det_one] at h1
    exact SL3Pair.eq_one_of_pow_two_pow h1
  exact matAut_dgHom_mem_diagSL (SL3Pair.mem_statedSL_iff.mpr hdet)

theorem permute_lin [CharP K 2] {B S : Subgroup (MulAut (W6 K))} (hBN : B ≤ normD K)
    (hSN : S ≤ normD K) (hBodd : Odd (Nat.card B)) (hS : IsPGroup 2 S)
    (hBS : (B : Set (MulAut (W6 K))) * S = S * B) :
    ((B ⊓ linSub : Subgroup (MulAut (W6 K))) : Set (MulAut (W6 K))) *
        ((S ⊓ diagSL K : Subgroup (MulAut (W6 K))) : Set (MulAut (W6 K))) =
      ((S ⊓ diagSL K : Subgroup (MulAut (W6 K))) : Set (MulAut (W6 K))) *
        ((B ⊓ linSub : Subgroup (MulAut (W6 K))) : Set (MulAut (W6 K))) := by
  classical
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  have hDL : diagSL K ≤ dgSub K := by
    rintro _ ⟨g, -, rfl⟩
    exact matAut_dgHom_mem_dgSub g
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linSub := dgSub_le_linSub (hDL hu.2)
  have hub : u * b ∈ (S : Set (MulAut (W6 K))) * B := Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubL : u * b ∈ linSub := linSub.mul_mem huL hb.2
  let φ := semiHom (K := K)
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hσ1 : φ ⟨b', hBN hb'⟩ = 1 := by
    have h1 : φ ⟨b', hBN hb'⟩ * φ ⟨s, hSN hs⟩ = 1 := by
      rw [← map_mul]
      have hm : u * b ∈ normD K := by
        rw [← hbs']
        exact (normD K).mul_mem (hBN hb') (hSN hs)
      have : (⟨b', hBN hb'⟩ * ⟨s, hSN hs⟩ : ↥(normD K)) = ⟨u * b, hm⟩ := Subtype.ext hbs'
      rw [this]
      exact (semiHom_eq_one_iff _).mpr hubL
    have h2 : φ ⟨b', hBN hb'⟩ ^ Nat.card B = 1 := by
      rw [← map_pow]
      have : (⟨b', hBN hb'⟩ : ↥(normD K)) ^ Nat.card B = 1 := Subtype.ext (by simpa using hb'k)
      rw [this, map_one]
    have h3 : φ ⟨b', hBN hb'⟩ ^ 2 ^ j = 1 := by
      have h4 : φ ⟨s, hSN hs⟩ ^ 2 ^ j = 1 := by
        rw [← map_pow]
        have : (⟨s, hSN hs⟩ : ↥(normD K)) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hsj)
        rw [this, map_one]
      rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h4, inv_one]
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))
  have hb'L : b' ∈ linSub := (semiHom_eq_one_iff _).mp hσ1
  have hse : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
  have hsL : s ∈ linSub := by
    rw [hse]
    exact linSub.mul_mem (linSub.inv_mem hb'L) hubL
  have hact : ∀ p, act ⟨s, hSN hs⟩ p = p := by
    have hbb : b'⁻¹ * b ∈ B := B.mul_mem (B.inv_mem hb') hb.1
    have huD : actPerm (⟨u, hSN hu.1⟩ : ↥(normD K)) = 1 := by
      obtain ⟨g, rfl⟩ := hDL hu.2
      exact Equiv.ext fun p => act_dg rfl p
    have e1 : actPerm (⟨s, hSN hs⟩ : ↥(normD K)) = actPerm (⟨b'⁻¹ * b, hBN hbb⟩ : ↥(normD K)) := by
      have : (⟨s, hSN hs⟩ : ↥(normD K)) = ⟨b', hBN hb'⟩⁻¹ * ⟨u, hSN hu.1⟩ * ⟨b, hBN hb.1⟩ := by
        apply Subtype.ext
        change s = b'⁻¹ * u * b
        rw [hse, mul_assoc]
      rw [this, map_mul, map_mul, huD, mul_one, ← map_mul]
      congr 1
    have e2 : actPerm (⟨b'⁻¹ * b, hBN hbb⟩ : ↥(normD K)) ^ Nat.card B = 1 := by
      rw [← map_pow]
      have : (⟨b'⁻¹ * b, hBN hbb⟩ : ↥(normD K)) ^ Nat.card B = 1 := Subtype.ext (by
        simpa using orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hbb))
      rw [this, map_one]
    have e3 : actPerm (⟨s, hSN hs⟩ : ↥(normD K)) ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have : (⟨s, hSN hs⟩ : ↥(normD K)) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hsj)
      rw [this, map_one]
    rw [← e1] at e2
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e3))
    intro p
    have := congrArg (fun π : Equiv.Perm (Option K) => π p) h1
    exact this
  have hsD := mem_diagSL_of_two_pow (mem_dgSub_of_act (hSN hs) hsL hact) hsj
  exact ⟨b', ⟨hb', hb'L⟩, s, ⟨hs, hsD⟩, hbs⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
