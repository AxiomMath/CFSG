module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefs

public section

namespace CFSG.StandardType.A8Coord

open Matrix Multiplicative

private theorem a8tn_zeta_pow_eq_mod (m : ℕ) :
    ggSL9Zeta ^ m = ggSL9Zeta ^ (m % 7) := by
  conv_lhs => rw [← pow_mod_orderOf]
  rw [orderOf_ggSL9Zeta]

private theorem a8tn_zmod_two_pow_val (e : ZMod 3) :
    ((2 : ZMod 7) ^ e.val).val = 2 ^ e.val := by
  fin_cases e <;> decide

private theorem a8tn_zeta_pow_two (x : ZMod 7) (e : ZMod 3) :
    (((ggSL9Zeta ^ x.val : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ (2 ^ e.val) =
      ((ggSL9Zeta ^ (x * (2 : ZMod 7) ^ e.val).val : (GaloisField 2 3)ˣ) :
        GaloisField 2 3) := by
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  rw [← pow_mul, ZMod.val_mul, a8tn_zmod_two_pow_val]
  exact a8tn_zeta_pow_eq_mod (x.val * 2 ^ e.val)

private theorem a8tn_zeta_pow_val_mul (a b : ZMod 7) :
    ggSL9Zeta ^ (a * b).val = (ggSL9Zeta ^ a.val) ^ b.val := by
  rw [← pow_mul, ZMod.val_mul]
  conv_rhs => rw [a8tn_zeta_pow_eq_mod]

private theorem a8tn_pow_two_cancel (x : GaloisField 2 3) (a : ZMod 3) :
    (x ^ 2 ^ a.val) ^ 2 ^ (-a).val = x := by
  rw [← pow_mul]
  have h : 2 ^ a.val * 2 ^ (-a).val = 1 ∨ 2 ^ a.val * 2 ^ (-a).val = 8 := by
    fin_cases a <;> decide
  rcases h with h | h
  · rw [h, pow_one]
  · rw [h, ggSL9_pow_eight]

private theorem a8tn_pow_two_cancel' (x : GaloisField 2 3) (a : ZMod 3) :
    (x ^ 2 ^ (-a).val) ^ 2 ^ a.val = x := by
  rw [← pow_mul]
  have h : 2 ^ (-a).val * 2 ^ a.val = 1 ∨ 2 ^ (-a).val * 2 ^ a.val = 8 := by
    fin_cases a <;> decide
  rcases h with h | h
  · rw [h, pow_one]
  · rw [h, ggSL9_pow_eight]

private noncomputable def a8tn_monFun (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (v : GGSL9V) : GGSL9V :=
  fun i => v (π.symm i) ^ 2 ^ (k (π.symm i)).val

private theorem a8tn_monFun_add (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (v w : GGSL9V) :
    a8tn_monFun π k (v + w) = a8tn_monFun π k v + a8tn_monFun π k w := by
  funext i
  simp only [a8tn_monFun, Pi.add_apply]
  rw [add_pow_char_pow]

private theorem a8tn_monFun_comp (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (v : GGSL9V) :
    a8tn_monFun π.symm (fun j => -k (π.symm j)) (a8tn_monFun π k v) = v := by
  funext i
  simp only [a8tn_monFun, Equiv.symm_symm, Equiv.symm_apply_apply]
  exact a8tn_pow_two_cancel (v i) (k i)

private theorem a8tn_monFun_comp' (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (v : GGSL9V) :
    a8tn_monFun π k (a8tn_monFun π.symm (fun j => -k (π.symm j)) v) = v := by
  funext i
  simp only [a8tn_monFun, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact a8tn_pow_two_cancel' (v i) (k (π.symm i))

private noncomputable def a8tn_mon (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  { AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk' (a8tn_monFun π k) (a8tn_monFun_add π k)) with
    invFun := a8tn_monFun π.symm (fun j => -k (π.symm j))
    left_inv := a8tn_monFun_comp π k
    right_inv := a8tn_monFun_comp' π k }

private theorem a8tn_mon_apply (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) (v : GGSL9V)
    (i : Fin 3) :
    a8tn_mon π k v i = v (π.symm i) ^ 2 ^ (k (π.symm i)).val := rfl

private theorem a8tn_mon_inv_apply (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) (v : GGSL9V)
    (i : Fin 3) :
    ((a8tn_mon π k)⁻¹) v i = v (π i) ^ 2 ^ ((-k i).val) := by
  have h : (a8tn_mon π k)⁻¹ = a8tn_mon π.symm (fun j => -k (π.symm j)) :=
    LinearEquiv.ext fun w => rfl
  rw [h, a8tn_mon_apply]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]

private theorem a8tn_vecMul_a8MonK3 (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (f : Fin 3 → ZMod 7) (i : Fin 3) :
    vecMul f (a8MonK3 π k) i = f (π.symm i) * (2 : ZMod 7) ^ (k (π.symm i)).val := by
  rw [Matrix.vecMul_apply_eq_sum]
  simp only [a8MonK3, Matrix.of_apply]
  rw [Finset.sum_eq_single (π.symm i)
      (fun b _ hb => by
        have h : π b ≠ i := fun hh => hb (Equiv.injective π (by rw [hh, Equiv.apply_symm_apply]))
        simp [h])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp [Equiv.symm_apply_apply]

private theorem a8tn_mon_conj (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (f : Fin 3 → ZMod 7) :
    a8tn_mon π k * ggSL9TorusCoord (Multiplicative.ofAdd f) * (a8tn_mon π k)⁻¹ =
      ggSL9TorusCoord (Multiplicative.ofAdd (vecMul f (a8MonK3 π k))) := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, a8tn_mon_apply, ggSL9TorusCoord_apply,
    a8tn_mon_inv_apply, ggSL9TorusCoord_apply, a8tn_vecMul_a8MonK3]
  simp only [Equiv.apply_symm_apply]
  rw [mul_pow, a8tn_pow_two_cancel', a8tn_zeta_pow_two]

theorem ggSL9_exists_monomial (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    ∃ n : GGSL9V ≃ₗ[ZMod 2] GGSL9V, ∀ f : Fin 3 → ZMod 7,
      n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹ =
        ggSL9TorusCoord (Multiplicative.ofAdd (vecMul f (a8MonK3 π k))) :=
  ⟨a8tn_mon π k, fun f => a8tn_mon_conj π k f⟩

private def a8tn_MH (j : Fin 3) : Subgroup (Multiplicative (Fin 3 → ZMod 7)) where
  carrier := {x | toAdd x j = 0}
  one_mem' := by simp [toAdd_one]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [toAdd_mul, Pi.add_apply, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [toAdd_inv, Pi.neg_apply, hx, neg_zero]

private theorem a8tn_mem_MH (j : Fin 3) (x : Multiplicative (Fin 3 → ZMod 7)) :
    x ∈ a8tn_MH j ↔ toAdd x j = 0 := Iff.rfl

private noncomputable def a8tn_H (j : Fin 3) : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  (a8tn_MH j).map ggSL9TorusCoord

private theorem a8tn_mem_H (j : Fin 3) (t : GGSL9V ≃ₗ[ZMod 2] GGSL9V) :
    t ∈ a8tn_H j ↔ ∃ f : Fin 3 → ZMod 7, f j = 0 ∧
      ggSL9TorusCoord (Multiplicative.ofAdd f) = t := by
  constructor
  · intro ht
    obtain ⟨x, hx, hxt⟩ := (Subgroup.mem_map).mp ht
    exact ⟨toAdd x, (a8tn_mem_MH j x).mp hx, by rw [ofAdd_toAdd]; exact hxt⟩
  · rintro ⟨f, hf, rfl⟩
    exact (Subgroup.mem_map).mpr ⟨Multiplicative.ofAdd f,
      (a8tn_mem_MH j _).mpr (by rw [toAdd_ofAdd]; exact hf), rfl⟩

private theorem a8tn_H_le_torus (j : Fin 3) : a8tn_H j ≤ ggSL9Torus := by
  intro t ht
  obtain ⟨f, _, rfl⟩ := (a8tn_mem_H j t).mp ht
  rw [← range_ggSL9TorusCoord]
  exact ⟨Multiplicative.ofAdd f, rfl⟩

private theorem a8tn_zeta_ne_one :
    ((ggSL9Zeta : (GaloisField 2 3)ˣ) : GaloisField 2 3) ≠ 1 := by
  intro h
  have h1 : ggSL9Zeta = 1 := Units.val_eq_one.mp h
  have h2 : orderOf ggSL9Zeta = 1 := orderOf_eq_one_iff.mpr h1
  rw [orderOf_ggSL9Zeta] at h2
  exact absurd h2 (by norm_num)

private theorem a8tn_zeta_ne_zero :
    ((ggSL9Zeta : (GaloisField 2 3)ˣ) : GaloisField 2 3) ≠ 0 :=
  Units.ne_zero ggSL9Zeta

private theorem a8tn_add_eq_zero_iff (x y : GaloisField 2 3) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + 0 := by rw [add_zero]
      _ = x + (x + y) := by rw [h, add_zero]
      _ = (x + x) + y := by rw [add_assoc]
      _ = 0 + y := by rw [CharTwo.add_self_eq_zero]
      _ = y := by rw [zero_add]
  · intro h
    rw [h, CharTwo.add_self_eq_zero]

private theorem a8tn_val_one : (1 : ZMod 7).val = 1 := by decide

private theorem a8tn_zeta_one : ggSL9Zeta ^ (1 : ZMod 7).val = ggSL9Zeta := by
  rw [a8tn_val_one, pow_one]

private theorem a8tn_zeta_pow_ne_one {m : ℕ} (hm : 0 < m) (hlt : m < 7) :
    ggSL9Zeta ^ m ≠ 1 := by
  intro h
  have hd : 7 ∣ m := by
    have := orderOf_dvd_of_pow_eq_one h
    rwa [orderOf_ggSL9Zeta] at this
  exact absurd (Nat.eq_zero_of_dvd_of_lt hd hlt) (Nat.pos_iff_ne_zero.mp hm)

private theorem a8tn_zeta_field_pow_ne_one {m : ℕ} (hm : 0 < m) (hlt : m < 7) :
    ((ggSL9Zeta : GaloisField 2 3) ^ m) ≠ 1 := by
  intro h
  rw [← Units.val_pow_eq_pow_val] at h
  exact a8tn_zeta_pow_ne_one hm hlt (Units.val_eq_one.mp h)

private def a8tn_W (i : Fin 3) : Submodule (ZMod 2) GGSL9V where
  carrier := {v | ∀ j, j ≠ i → v j = 0}
  zero_mem' := by intro j _; rfl
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro c x hx j hj; simp [hx j hj]

private theorem a8tn_mem_W (i : Fin 3) (v : GGSL9V) :
    v ∈ a8tn_W i ↔ ∀ j, j ≠ i → v j = 0 := Iff.rfl

private noncomputable def a8tn_WInvFun (i : Fin 3) (c : GaloisField 2 3) : a8tn_W i :=
  ⟨Pi.single i c, (a8tn_mem_W i _).mpr fun l hl => by rw [Pi.single_eq_of_ne hl]⟩

private theorem a8tn_WInvFun_coe (i : Fin 3) (c : GaloisField 2 3) :
    ((a8tn_WInvFun i c : a8tn_W i) : GGSL9V) = Pi.single i c := rfl

private noncomputable def a8tn_WLinEquiv (i : Fin 3) :
    a8tn_W i ≃ₗ[ZMod 2] GaloisField 2 3 where
  toFun v := v.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := a8tn_WInvFun i
  left_inv v := by
    apply Subtype.ext
    funext l
    rw [a8tn_WInvFun_coe]
    by_cases hl : l = i
    · subst hl; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hl]
      exact ((a8tn_mem_W i v.1).mp v.2 l hl).symm
  right_inv c := by
    change (a8tn_WInvFun i c : a8tn_W i).1 i = c
    rw [a8tn_WInvFun_coe, Pi.single_eq_same]

private theorem a8tn_finrank_W (i : Fin 3) :
    Module.finrank (ZMod 2) (a8tn_W i) = 3 := by
  rw [LinearEquiv.finrank_eq (a8tn_WLinEquiv i),
    GaloisField.finrank 2 (by norm_num : (3 : ℕ) ≠ 0)]

private theorem a8tn_finrank_map_W (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V) (i : Fin 3) :
    Module.finrank (ZMod 2) ((a8tn_W i).map (n : GGSL9V →ₗ[ZMod 2] GGSL9V)) = 3 := by
  rw [LinearEquiv.finrank_map_eq, a8tn_finrank_W]

private theorem a8tn_W_injective : Function.Injective a8tn_W := by
  intro i j hij
  by_contra hne
  have hmem : Pi.single i (1 : GaloisField 2 3) ∈ a8tn_W j := by
    rw [← hij]
    intro l hl
    rw [Pi.single_eq_of_ne hl]
  have h0 : (Pi.single i (1 : GaloisField 2 3) : GGSL9V) i = 0 :=
    (a8tn_mem_W j (Pi.single i (1 : GaloisField 2 3))).mp hmem i hne
  rw [Pi.single_eq_same] at h0
  exact one_ne_zero h0

private def a8tn_fix (K : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) :
    Submodule (ZMod 2) GGSL9V where
  carrier := {v | ∀ t ∈ K, t v = v}
  zero_mem' := by intro t _; rw [map_zero]
  add_mem' := by intro x y hx hy t ht; rw [map_add, hx t ht, hy t ht]
  smul_mem' := by intro c x hx t ht; rw [map_smul, hx t ht]

private theorem a8tn_H_apply_single (i : Fin 3) {t : GGSL9V ≃ₗ[ZMod 2] GGSL9V}
    (ht : t ∈ a8tn_H i) : t (Pi.single i (1 : GaloisField 2 3)) = Pi.single i 1 := by
  obtain ⟨f, hf, rfl⟩ := (a8tn_mem_H i t).mp ht
  funext l
  rw [ggSL9TorusCoord_apply]
  by_cases hl : l = i
  · subst hl; rw [hf, Pi.single_eq_same, ZMod.val_zero, pow_zero]; simp
  · rw [Pi.single_eq_of_ne hl, mul_zero]

private theorem a8tn_fix_H (i : Fin 3) : a8tn_fix (a8tn_H i) = a8tn_W i := by
  ext v
  constructor
  · intro hv j hj
    have hf₀ : (Pi.single j (1 : ZMod 7) : Fin 3 → ZMod 7) i = 0 := by
      rw [Pi.single_eq_of_ne (Ne.symm hj)]
    have ht : ggSL9TorusCoord
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod 7) : Fin 3 → ZMod 7)) ∈ a8tn_H i :=
      (a8tn_mem_H i _).mpr ⟨(Pi.single j (1 : ZMod 7) : Fin 3 → ZMod 7), hf₀, rfl⟩
    have hfix := hv _ ht
    have hcoord := congrFun hfix j
    have hf₀j : (Pi.single j (1 : ZMod 7) : Fin 3 → ZMod 7) j = 1 := by
      rw [Pi.single_eq_same]
    rw [ggSL9TorusCoord_apply, hf₀j, a8tn_val_one, pow_one] at hcoord
    have h' : ((ggSL9Zeta : GaloisField 2 3) - 1) * v j = 0 := by
      rw [sub_mul, one_mul, hcoord, sub_self]
    rcases mul_eq_zero.mp h' with hζ | hvj
    · exact absurd (sub_eq_zero.mp hζ) a8tn_zeta_ne_one
    · exact hvj
  · intro hv t ht
    obtain ⟨f, hf, rfl⟩ := (a8tn_mem_H i t).mp ht
    funext l
    rw [ggSL9TorusCoord_apply]
    by_cases hl : l = i
    · subst hl; rw [hf, ZMod.val_zero, pow_zero]; simp
    · rw [show v l = 0 from hv l hl, mul_zero]

private noncomputable def a8tn_conj (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (K : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) :
    Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  K.map (MulAut.conj n).toMonoidHom

private theorem a8tn_mem_conj (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (K : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (t : GGSL9V ≃ₗ[ZMod 2] GGSL9V) :
    t ∈ a8tn_conj n K ↔ n⁻¹ * t * n ∈ K := by
  constructor
  · intro ht
    obtain ⟨x, hx, hxt⟩ := (Subgroup.mem_map).mp ht
    have hx' : n⁻¹ * ((MulAut.conj n).toMonoidHom x) * n = x := by
      change n⁻¹ * (n * x * n⁻¹) * n = x
      group
    rw [← hxt, hx']
    exact hx
  · intro ht
    refine (Subgroup.mem_map).mpr ⟨n⁻¹ * t * n, ht, ?_⟩
    change n * (n⁻¹ * t * n) * n⁻¹ = t
    group

private theorem a8tn_conj_le_torus (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (K : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (hK : K ≤ ggSL9Torus) :
    a8tn_conj n K ≤ ggSL9Torus := by
  intro t ht
  have hy : n⁻¹ * t * n ∈ ggSL9Torus := hK ((a8tn_mem_conj n K t).mp ht)
  have hnt := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * t * n)).mp hy
  rwa [show n * (n⁻¹ * t * n) * n⁻¹ = t by group] at hnt

private theorem a8tn_map_W_eq_fix_conj (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V) (i : Fin 3) :
    (a8tn_W i).map (n : GGSL9V →ₗ[ZMod 2] GGSL9V) =
      a8tn_fix (a8tn_conj n (a8tn_H i)) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩ t ht
    have hwt : (n⁻¹ * t * n) w = w := by
      have hwfix : w ∈ a8tn_fix (a8tn_H i) := by rwa [a8tn_fix_H]
      exact hwfix _ ((a8tn_mem_conj n (a8tn_H i) t).mp ht)
    have hconj : t * n = n * (n⁻¹ * t * n) := by group
    calc t (n w) = (t * n) w := rfl
      _ = (n * (n⁻¹ * t * n)) w := by rw [hconj]
      _ = n ((n⁻¹ * t * n) w) := by rw [LinearEquiv.mul_apply]
      _ = n w := by rw [hwt]
  · intro hv
    refine ⟨n⁻¹ v, ?_, by simp⟩
    rw [← a8tn_fix_H]
    intro s hs
    have hs' : n * s * n⁻¹ ∈ a8tn_conj n (a8tn_H i) := by
      rw [a8tn_mem_conj]
      rwa [show n⁻¹ * (n * s * n⁻¹) * n = s by group]
    have hfix := hv _ hs'
    have h2 : n (s (n⁻¹ v)) = v := by
      simpa only [LinearEquiv.mul_apply] using hfix
    calc s (n⁻¹ v) = n⁻¹ (n (s (n⁻¹ v))) :=
          (LinearEquiv.symm_apply_apply n (s (n⁻¹ v))).symm
      _ = n⁻¹ v := by rw [h2]

private theorem a8tn_exists_pi (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) :
    ∃ j : Fin 3, n (Pi.single i (1 : GaloisField 2 3)) j ≠ 0 ∧
      a8tn_conj n (a8tn_H i) ≤ a8tn_H j := by
  have hsingle : (Pi.single i (1 : GaloisField 2 3) : GGSL9V) ≠ 0 := by
    intro h
    have := congrFun h i
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  have hu : n (Pi.single i (1 : GaloisField 2 3)) ≠ 0 := by
    intro h
    exact hsingle (n.injective (by rw [h, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j, n (Pi.single i (1 : GaloisField 2 3)) j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext fun j => by simpa using hc j)
  refine ⟨j, hj, fun t ht => ?_⟩
  have htT : t ∈ ggSL9Torus :=
    a8tn_conj_le_torus n hn (a8tn_H i) (a8tn_H_le_torus i) ht
  rw [← range_ggSL9TorusCoord] at htT
  obtain ⟨x, hx⟩ := htT
  have htu : t (n (Pi.single i (1 : GaloisField 2 3))) =
      n (Pi.single i (1 : GaloisField 2 3)) := by
    have hy : n⁻¹ * t * n ∈ a8tn_H i := (a8tn_mem_conj n (a8tn_H i) t).mp ht
    have hfix : (n⁻¹ * t * n) (Pi.single i (1 : GaloisField 2 3)) = Pi.single i 1 :=
      a8tn_H_apply_single i hy
    have hconj : t * n = n * (n⁻¹ * t * n) := by group
    calc t (n (Pi.single i (1 : GaloisField 2 3)))
        = (t * n) (Pi.single i (1 : GaloisField 2 3)) := rfl
      _ = (n * (n⁻¹ * t * n)) (Pi.single i (1 : GaloisField 2 3)) := by rw [hconj]
      _ = n ((n⁻¹ * t * n) (Pi.single i (1 : GaloisField 2 3))) := by
            rw [LinearEquiv.mul_apply]
      _ = n (Pi.single i (1 : GaloisField 2 3)) := by rw [hfix]
  rw [a8tn_mem_H]
  refine ⟨toAdd x, ?_, ?_⟩
  · by_contra hxj
    have hx' : ggSL9TorusCoord (Multiplicative.ofAdd (toAdd x)) = t := by
      rw [ofAdd_toAdd]; exact hx
    have hcoord := congrFun htu j
    rw [← hx', ggSL9TorusCoord_apply] at hcoord
    have h' : (((ggSL9Zeta ^ (toAdd x j).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) - 1)
        * (n (Pi.single i (1 : GaloisField 2 3)) j) = 0 := by
      rw [sub_mul, one_mul, hcoord, sub_self]
    rcases mul_eq_zero.mp h' with hζ | h0
    · exact a8tn_zeta_pow_ne_one
        (Nat.pos_of_ne_zero fun h => hxj ((ZMod.val_eq_zero (toAdd x j)).mp h)) (ZMod.val_lt _)
        (Units.val_eq_one.mp (sub_eq_zero.mp hζ))
    · exact absurd h0 hj
  · rw [ofAdd_toAdd]; exact hx

private noncomputable def a8tn_pi (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) : Fin 3 :=
  Classical.choose (a8tn_exists_pi n hn i)

private theorem a8tn_pi_ne_zero (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) : n (Pi.single i (1 : GaloisField 2 3)) (a8tn_pi n hn i) ≠ 0 :=
  (Classical.choose_spec (a8tn_exists_pi n hn i)).1

private theorem a8tn_conj_H_le_H (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) : a8tn_conj n (a8tn_H i) ≤ a8tn_H (a8tn_pi n hn i) :=
  (Classical.choose_spec (a8tn_exists_pi n hn i)).2

private theorem a8tn_W_pi_eq_fix (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) :
    a8tn_W (a8tn_pi n hn i) = a8tn_fix (a8tn_conj n (a8tn_H i)) := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv t ht
    have htH : t ∈ a8tn_H (a8tn_pi n hn i) := a8tn_conj_H_le_H n hn i ht
    obtain ⟨f, hf, rfl⟩ := (a8tn_mem_H _ t).mp htH
    funext l
    rw [ggSL9TorusCoord_apply]
    by_cases hl : l = a8tn_pi n hn i
    · subst hl; rw [hf, ZMod.val_zero, pow_zero]; simp
    · rw [show v l = 0 from hv l hl, mul_zero]
  · rw [← a8tn_map_W_eq_fix_conj n i, a8tn_finrank_map_W, a8tn_finrank_W]

private theorem a8tn_map_W_eq_W_pi (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) :
    (a8tn_W i).map (n : GGSL9V →ₗ[ZMod 2] GGSL9V) = a8tn_W (a8tn_pi n hn i) := by
  rw [a8tn_map_W_eq_fix_conj n i, ← a8tn_W_pi_eq_fix n hn i]

private theorem a8tn_map_symm_map (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (p : Submodule (ZMod 2) GGSL9V) :
    (p.map (n : GGSL9V →ₗ[ZMod 2] GGSL9V)).map
        (n.symm : GGSL9V →ₗ[ZMod 2] GGSL9V) = p := by
  ext v
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨u, hu, huw⟩ := (Submodule.mem_map).mp hw
    rw [← hwv, ← huw]
    simpa using hu
  · intro hv
    exact ⟨n v, ⟨v, hv, rfl⟩, by simp⟩

private theorem a8tn_pi_injective (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) :
    Function.Injective (a8tn_pi n hn) := by
  intro i j hij
  apply a8tn_W_injective
  have h : (a8tn_W i).map (n : GGSL9V →ₗ[ZMod 2] GGSL9V) =
      (a8tn_W j).map (n : GGSL9V →ₗ[ZMod 2] GGSL9V) := by
    rw [a8tn_map_W_eq_W_pi n hn i, a8tn_map_W_eq_W_pi n hn j, hij]
  have h2 := congrArg (fun p : Submodule (ZMod 2) GGSL9V =>
    p.map (n.symm : GGSL9V →ₗ[ZMod 2] GGSL9V)) h
  rwa [a8tn_map_symm_map, a8tn_map_symm_map] at h2

private noncomputable def a8tn_piEquiv (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (a8tn_pi n hn) (a8tn_pi_injective n hn).bijective_of_finite

private theorem a8tn_piEquiv_apply (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) : a8tn_piEquiv n hn i = a8tn_pi n hn i :=
  Equiv.ofBijective_apply _ _ _

private theorem a8tn_alpha_exists (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (f : Fin 3 → ZMod 7) :
    ∃ g : Multiplicative (Fin 3 → ZMod 7),
      ggSL9TorusCoord g = n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹ := by
  have ht : n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹ ∈ ggSL9Torus :=
    (Subgroup.mem_normalizer_iff.mp hn (ggSL9TorusCoord (Multiplicative.ofAdd f))).mp (by
      rw [← range_ggSL9TorusCoord]
      exact ⟨Multiplicative.ofAdd f, rfl⟩)
  rwa [← range_ggSL9TorusCoord] at ht

private noncomputable def a8tn_alpha (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (f : Fin 3 → ZMod 7) : Fin 3 → ZMod 7 :=
  toAdd (Classical.choose (a8tn_alpha_exists n hn f))

private theorem a8tn_alpha_spec (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (f : Fin 3 → ZMod 7) :
    ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn f)) =
      n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹ := by
  rw [a8tn_alpha, ofAdd_toAdd]
  exact Classical.choose_spec (a8tn_alpha_exists n hn f)

private theorem a8tn_alpha_zero (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) :
    a8tn_alpha n hn 0 = 0 := by
  have h : ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn 0)) =
      ggSL9TorusCoord (Multiplicative.ofAdd (0 : Fin 3 → ZMod 7)) := by
    rw [a8tn_alpha_spec, ofAdd_zero, map_one]
    group
  exact Multiplicative.ofAdd.injective (ggSL9TorusCoord_injective h)

private theorem a8tn_alpha_add (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (f g : Fin 3 → ZMod 7) :
    a8tn_alpha n hn (f + g) = a8tn_alpha n hn f + a8tn_alpha n hn g := by
  have h : ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn (f + g))) =
      ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn f + a8tn_alpha n hn g)) := by
    calc ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn (f + g)))
        = n * ggSL9TorusCoord (Multiplicative.ofAdd (f + g)) * n⁻¹ := a8tn_alpha_spec n hn _
      _ = n * (ggSL9TorusCoord (Multiplicative.ofAdd f) *
              ggSL9TorusCoord (Multiplicative.ofAdd g)) * n⁻¹ := by rw [ofAdd_add, map_mul]
      _ = (n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹) *
            (n * ggSL9TorusCoord (Multiplicative.ofAdd g) * n⁻¹) := by group
      _ = ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn f)) *
            ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn g)) := by
            rw [a8tn_alpha_spec, a8tn_alpha_spec]
      _ = ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn f + a8tn_alpha n hn g)) := by
            rw [ofAdd_add, map_mul]
  exact Multiplicative.ofAdd.injective (ggSL9TorusCoord_injective h)

private noncomputable def a8tn_alphaHom (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) :
    (Fin 3 → ZMod 7) →+ (Fin 3 → ZMod 7) where
  toFun := a8tn_alpha n hn
  map_zero' := a8tn_alpha_zero n hn
  map_add' := a8tn_alpha_add n hn

private theorem a8tn_zmod_smul_eq_nsmul {M : Type*} [AddCommMonoid M] [Module (ZMod 7) M]
    (a : ZMod 7) (m : M) : a • m = a.val • m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

private theorem a8tn_alpha_zsmul_smul (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (a : ZMod 7) (f : Fin 3 → ZMod 7) :
    a8tn_alpha n hn (a • f) = a • a8tn_alpha n hn f := by
  rw [a8tn_zmod_smul_eq_nsmul a f, a8tn_zmod_smul_eq_nsmul a (a8tn_alpha n hn f)]
  exact map_nsmul (a8tn_alphaHom n hn) a.val f

private noncomputable def a8tn_gamma (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) : ZMod 7 :=
  a8tn_alpha n hn (Pi.single i (1 : ZMod 7)) (a8tn_pi n hn i)

private theorem a8tn_alpha_single (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) (a : ZMod 7) :
    a8tn_alpha n hn (Pi.single i a) =
      a • a8tn_alpha n hn (Pi.single i (1 : ZMod 7)) := by
  have hsingle : (Pi.single i a : Fin 3 → ZMod 7) = a • Pi.single i (1 : ZMod 7) := by
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · rw [Pi.single_eq_of_ne hl, Pi.smul_apply, Pi.single_eq_of_ne hl, smul_zero]
  rw [hsingle, a8tn_alpha_zsmul_smul]

private theorem a8tn_alpha_single_gamma (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) (a : ZMod 7) :
    a8tn_alpha n hn (Pi.single i a) (a8tn_pi n hn i) = a * a8tn_gamma n hn i := by
  rw [a8tn_alpha_single, Pi.smul_apply, a8tn_gamma, smul_eq_mul]

private theorem a8tn_semilinear (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (f : Fin 3 → ZMod 7) (v : GGSL9V) :
    n (ggSL9TorusCoord (Multiplicative.ofAdd f) v) =
      ggSL9TorusCoord (Multiplicative.ofAdd (a8tn_alpha n hn f)) (n v) := by
  rw [a8tn_alpha_spec n hn f]
  rw [show n (ggSL9TorusCoord (Multiplicative.ofAdd f) v) =
      (n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹) (n v) by
    conv_rhs => rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simp]

private theorem a8tn_semilinear_scalar (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) (a : ZMod 7) (v : GGSL9V) (hv : v ∈ a8tn_W i) :
    n (fun j => ((ggSL9Zeta ^ a.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * v j) =
      fun j => ((ggSL9Zeta ^ (a * a8tn_gamma n hn i).val : (GaloisField 2 3)ˣ) :
        GaloisField 2 3) * (n v) j := by
  have hv' : ggSL9TorusCoord (Multiplicative.ofAdd (Pi.single i a)) v =
      fun j => ((ggSL9Zeta ^ a.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * v j := by
    funext l
    rw [ggSL9TorusCoord_apply]
    by_cases hl : l = i
    · subst hl; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hl, hv l hl, mul_zero, mul_zero]
  rw [← hv', a8tn_semilinear n hn (Pi.single i a) v]
  have hnv : n v ∈ a8tn_W (a8tn_pi n hn i) := by
    have : n v ∈ (a8tn_W i).map (n : GGSL9V →ₗ[ZMod 2] GGSL9V) := ⟨v, hv, rfl⟩
    rwa [a8tn_map_W_eq_W_pi] at this
  have halphaeq : (a8tn_alpha n hn (Pi.single i a)) (a8tn_pi n hn i) =
      a * a8tn_gamma n hn i := a8tn_alpha_single_gamma n hn i a
  funext l
  rw [ggSL9TorusCoord_apply]
  by_cases hl : l = a8tn_pi n hn i
  · subst hl; rw [halphaeq]
  · rw [hnv l hl, mul_zero, mul_zero]

private theorem a8tn_alpha_H_zero (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) (f : Fin 3 → ZMod 7) (hf : f i = 0) :
    a8tn_alpha n hn f (a8tn_pi n hn i) = 0 := by
  have ht : ggSL9TorusCoord (Multiplicative.ofAdd f) ∈ a8tn_H i :=
    (a8tn_mem_H i _).mpr ⟨f, hf, rfl⟩
  have hK : n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹ ∈
      a8tn_conj n (a8tn_H i) := by
    rw [a8tn_mem_conj]
    rwa [show n⁻¹ * (n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹) * n =
      ggSL9TorusCoord (Multiplicative.ofAdd f) by group]
  have hH := a8tn_conj_H_le_H n hn i hK
  rw [← a8tn_alpha_spec n hn f] at hH
  rw [a8tn_mem_H] at hH
  obtain ⟨g, hg, hgt⟩ := hH
  have hge : g = a8tn_alpha n hn f := by
    exact Multiplicative.ofAdd.injective (ggSL9TorusCoord_injective hgt)
  rw [← hge]
  exact hg

private theorem a8tn_alpha_entry (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (f : Fin 3 → ZMod 7) (i : Fin 3) :
    a8tn_alpha n hn f (a8tn_pi n hn i) = f i * a8tn_gamma n hn i := by
  set f' : Fin 3 → ZMod 7 := f - f i • Pi.single i (1 : ZMod 7) with hf'
  have hf'i : f' i = 0 := by rw [hf']; simp
  have hdecomp : f = f i • Pi.single i (1 : ZMod 7) + f' := by
    rw [hf']; funext j; simp [Pi.add_apply, Pi.sub_apply]
  have hα : a8tn_alpha n hn f =
      a8tn_alpha n hn (f i • Pi.single i (1 : ZMod 7)) + a8tn_alpha n hn f' := by
    conv_lhs => rw [hdecomp]
    rw [a8tn_alpha_add]
  rw [hα, Pi.add_apply, a8tn_alpha_zsmul_smul, a8tn_alpha_H_zero n hn i f' hf'i, add_zero,
    a8tn_gamma, Pi.smul_apply, smul_eq_mul]

private theorem a8tn_exists_zeta_pow_add_one :
    ∃ c : ZMod 7, ((ggSL9Zeta ^ c.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) =
      1 + (ggSL9Zeta : GaloisField 2 3) := by
  have hne : (1 + (ggSL9Zeta : GaloisField 2 3)) ≠ 0 := by
    intro h
    have h1 : (ggSL9Zeta : GaloisField 2 3) = 1 := by
      calc (ggSL9Zeta : GaloisField 2 3) = (ggSL9Zeta : GaloisField 2 3) + 0 := by
              rw [add_zero]
        _ = (ggSL9Zeta : GaloisField 2 3) + (1 + (ggSL9Zeta : GaloisField 2 3)) := by
              rw [h, add_zero]
        _ = ((ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3)) + 1 := by abel
        _ = 0 + 1 := by rw [CharTwo.add_self_eq_zero]
        _ = 1 := by rw [zero_add]
    exact a8tn_zeta_ne_one h1
  let u : (GaloisField 2 3)ˣ := Units.mk0 (1 + (ggSL9Zeta : GaloisField 2 3)) hne
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff u ggSL9Zeta).mp
    ((mem_powers_iff_mem_zpowers (x := ggSL9Zeta) (y := u)).mpr (mem_zpowers_ggSL9Zeta u))
  refine ⟨(m : ZMod 7), ?_⟩
  rw [ZMod.val_natCast, ← a8tn_zeta_pow_eq_mod m, hm]
  rfl

private theorem a8tn_gamma_spec (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) :
    (1 + (ggSL9Zeta : GaloisField 2 3)) ^ (a8tn_gamma n hn i).val =
      1 + (ggSL9Zeta : GaloisField 2 3) ^ (a8tn_gamma n hn i).val := by
  obtain ⟨c, hc⟩ := a8tn_exists_zeta_pow_add_one
  set γ : ZMod 7 := a8tn_gamma n hn i with hγ
  set e : GGSL9V := Pi.single i (1 : GaloisField 2 3) with he
  have heW : e ∈ a8tn_W i := by
    rw [he]; intro l hl; rw [Pi.single_eq_of_ne hl]
  have hj0 : n e (a8tn_pi n hn i) ≠ 0 := by
    rw [he]; exact a8tn_pi_ne_zero n hn i
  have hc1 : n (fun l => ((ggSL9Zeta ^ c.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * e l)
        (a8tn_pi n hn i) =
      ((ggSL9Zeta ^ (c * γ).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) *
        (n e) (a8tn_pi n hn i) := by
    have := congrFun (a8tn_semilinear_scalar n hn i c e heW) (a8tn_pi n hn i)
    simpa [hγ] using this
  have h1fun : n (fun l => ((ggSL9Zeta : (GaloisField 2 3)ˣ) : GaloisField 2 3) * e l) =
      fun j => ((ggSL9Zeta ^ γ.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * (n e) j := by
    have h := a8tn_semilinear_scalar n hn i 1 e heW
    rw [show (fun l => ((ggSL9Zeta ^ (1 : ZMod 7).val : (GaloisField 2 3)ˣ) :
          GaloisField 2 3) * e l) =
        fun l => ((ggSL9Zeta : (GaloisField 2 3)ˣ) : GaloisField 2 3) * e l by
      funext l; rw [a8tn_zeta_one]] at h
    simpa [hγ] using h
  have harg : (fun l => ((ggSL9Zeta ^ c.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * e l) =
      e + fun l => ((ggSL9Zeta : (GaloisField 2 3)ˣ) : GaloisField 2 3) * e l := by
    funext l
    rw [hc]
    simp only [Pi.add_apply]
    ring
  rw [harg, map_add, h1fun] at hc1
  have hcancel : ((ggSL9Zeta ^ (c * γ).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) =
      1 + ((ggSL9Zeta ^ γ.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) := by
    have hmul : (1 + ((ggSL9Zeta ^ γ.val : (GaloisField 2 3)ˣ) : GaloisField 2 3)) *
          (n e) (a8tn_pi n hn i) =
        ((ggSL9Zeta ^ (c * γ).val : (GaloisField 2 3)ˣ) : GaloisField 2 3) *
          (n e) (a8tn_pi n hn i) := by
      rw [← hc1]
      simp only [Pi.add_apply]
      ring
    exact (mul_right_cancel₀ hj0 hmul).symm
  have goal' : ((ggSL9Zeta ^ c.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ γ.val =
      1 + ((ggSL9Zeta ^ γ.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) := by
    rw [← Units.val_pow_eq_pow_val, ← a8tn_zeta_pow_val_mul c γ]
    exact hcancel
  rw [← hc]
  conv_rhs => rw [← Units.val_pow_eq_pow_val ggSL9Zeta γ.val]
  exact goal'

private theorem a8tn_gamma_numeric {g : ℕ} (hg : g < 7)
    (h : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ g =
      1 + (ggSL9Zeta : GaloisField 2 3) ^ g) :
    g = 1 ∨ g = 2 ∨ g = 4 := by
  have h2 : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 2 =
      1 + (ggSL9Zeta : GaloisField 2 3) ^ 2 := by
    rw [add_pow_char]; ring
  have h2' : (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) ^ 2 =
      1 + (ggSL9Zeta : GaloisField 2 3) ^ 4 := by
    rw [add_pow_char]; ring
  have h4 : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 4 =
      1 + (ggSL9Zeta : GaloisField 2 3) ^ 4 := by
    calc (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 4 =
          ((1 + (ggSL9Zeta : GaloisField 2 3)) ^ 2) ^ 2 := by ring
      _ = (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) ^ 2 := by
          rw [h2]
      _ = 1 + (ggSL9Zeta : GaloisField 2 3) ^ 4 := h2'
  have h3 : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 3 =
      1 + (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 2 +
        (ggSL9Zeta : GaloisField 2 3) ^ 3 := by
    calc (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 3 =
          (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 2 *
            (1 + (ggSL9Zeta : GaloisField 2 3)) := by ring
      _ = (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) *
            (1 + (ggSL9Zeta : GaloisField 2 3)) := by rw [h2]
      _ = 1 + (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 2 +
            (ggSL9Zeta : GaloisField 2 3) ^ 3 := by ring
  have h3' : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 3 =
      (1 + (ggSL9Zeta : GaloisField 2 3)) *
        (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) := by
    rw [h3]; ring
  have h5 : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 5 =
      1 + (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4 +
        (ggSL9Zeta : GaloisField 2 3) ^ 5 := by
    calc (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 5 =
          (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 4 *
            (1 + (ggSL9Zeta : GaloisField 2 3)) := by ring
      _ = (1 + (ggSL9Zeta : GaloisField 2 3) ^ 4) *
            (1 + (ggSL9Zeta : GaloisField 2 3)) := by rw [h4]
      _ = 1 + (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4 +
            (ggSL9Zeta : GaloisField 2 3) ^ 5 := by ring
  have h6 : (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 6 =
      1 + (ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4 +
        (ggSL9Zeta : GaloisField 2 3) ^ 6 := by
    calc (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 6 =
          ((1 + (ggSL9Zeta : GaloisField 2 3)) ^ 3) ^ 2 := by ring
      _ = ((1 + (ggSL9Zeta : GaloisField 2 3)) *
            (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2)) ^ 2 := by rw [h3']
      _ = (1 + (ggSL9Zeta : GaloisField 2 3)) ^ 2 *
            (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) ^ 2 := by rw [mul_pow]
      _ = (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) *
            (1 + (ggSL9Zeta : GaloisField 2 3) ^ 4) := by rw [h2, h2']
      _ = 1 + (ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4 +
            (ggSL9Zeta : GaloisField 2 3) ^ 6 := by ring
  interval_cases g
  · exfalso
    rw [pow_zero, pow_zero] at h
    rw [CharTwo.add_self_eq_zero] at h
    exact one_ne_zero h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exfalso
    rw [h3] at h
    have h' : (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 2 = 0 := by
      have hh : (1 + (ggSL9Zeta : GaloisField 2 3) ^ 3) +
          ((ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 2) =
          (1 + (ggSL9Zeta : GaloisField 2 3) ^ 3) + 0 := by
        rw [add_zero]
        calc (1 + (ggSL9Zeta : GaloisField 2 3) ^ 3) +
              ((ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 2) =
              1 + (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 2 +
                (ggSL9Zeta : GaloisField 2 3) ^ 3 := by ring
          _ = 1 + (ggSL9Zeta : GaloisField 2 3) ^ 3 := h
      exact add_left_cancel hh
    have hfac : (ggSL9Zeta : GaloisField 2 3) * (1 + (ggSL9Zeta : GaloisField 2 3)) = 0 := by
      rw [mul_add, mul_one, ← pow_two]; exact h'
    rcases mul_eq_zero.mp hfac with hz | h1
    · exact a8tn_zeta_ne_zero hz
    · exact a8tn_zeta_ne_one
        (((a8tn_add_eq_zero_iff 1 (ggSL9Zeta : GaloisField 2 3)).mp h1).symm)
  · exact Or.inr (Or.inr rfl)
  · exfalso
    rw [h5] at h
    have h' : (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4 = 0 := by
      have hh : (1 + (ggSL9Zeta : GaloisField 2 3) ^ 5) +
          ((ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4) =
          (1 + (ggSL9Zeta : GaloisField 2 3) ^ 5) + 0 := by
        rw [add_zero]
        calc (1 + (ggSL9Zeta : GaloisField 2 3) ^ 5) +
              ((ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4) =
              1 + (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4 +
                (ggSL9Zeta : GaloisField 2 3) ^ 5 := by ring
          _ = 1 + (ggSL9Zeta : GaloisField 2 3) ^ 5 := h
      exact add_left_cancel hh
    have hfac : (ggSL9Zeta : GaloisField 2 3) * (1 + (ggSL9Zeta : GaloisField 2 3) ^ 3) = 0 := by
      have : (ggSL9Zeta : GaloisField 2 3) * (1 + (ggSL9Zeta : GaloisField 2 3) ^ 3) =
          (ggSL9Zeta : GaloisField 2 3) + (ggSL9Zeta : GaloisField 2 3) ^ 4 := by ring
      rw [this]
      exact h'
    rcases mul_eq_zero.mp hfac with hz | h1
    · exact a8tn_zeta_ne_zero hz
    · exact absurd (((a8tn_add_eq_zero_iff 1 ((ggSL9Zeta : GaloisField 2 3) ^ 3)).mp h1).symm)
        (a8tn_zeta_field_pow_ne_one (by norm_num) (by norm_num))
  · exfalso
    rw [h6] at h
    have h' : (ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4 = 0 := by
      have hh : (1 + (ggSL9Zeta : GaloisField 2 3) ^ 6) +
          ((ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4) =
          (1 + (ggSL9Zeta : GaloisField 2 3) ^ 6) + 0 := by
        rw [add_zero]
        calc (1 + (ggSL9Zeta : GaloisField 2 3) ^ 6) +
              ((ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4) =
              1 + (ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4 +
                (ggSL9Zeta : GaloisField 2 3) ^ 6 := by ring
          _ = 1 + (ggSL9Zeta : GaloisField 2 3) ^ 6 := h
      exact add_left_cancel hh
    have hfac : (ggSL9Zeta : GaloisField 2 3) ^ 2 *
        (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) = 0 := by
      have : (ggSL9Zeta : GaloisField 2 3) ^ 2 *
          (1 + (ggSL9Zeta : GaloisField 2 3) ^ 2) =
          (ggSL9Zeta : GaloisField 2 3) ^ 2 + (ggSL9Zeta : GaloisField 2 3) ^ 4 := by ring
      rw [this]
      exact h'
    rcases mul_eq_zero.mp hfac with hz | h1
    · have hz2 : (ggSL9Zeta : GaloisField 2 3) * (ggSL9Zeta : GaloisField 2 3) = 0 := by
        rwa [pow_two] at hz
      exact a8tn_zeta_ne_zero (mul_self_eq_zero.mp hz2)
    · exact absurd (((a8tn_add_eq_zero_iff 1 ((ggSL9Zeta : GaloisField 2 3) ^ 2)).mp h1).symm)
        (a8tn_zeta_field_pow_ne_one (by norm_num) (by norm_num))

private theorem a8tn_gamma_pow_two (n : GGSL9V ≃ₗ[ZMod 2] GGSL9V)
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))
    (i : Fin 3) : ∃ k : ZMod 3, (2 : ZMod 7) ^ k.val = a8tn_gamma n hn i := by
  rcases a8tn_gamma_numeric (ZMod.val_lt (a8tn_gamma n hn i)) (a8tn_gamma_spec n hn i) with
    h1 | h2 | h4
  · have hγ : a8tn_gamma n hn i = 1 := by
      rw [← ZMod.natCast_zmod_val (a8tn_gamma n hn i), h1]; norm_num
    exact ⟨0, by rw [hγ]; decide⟩
  · have hγ : a8tn_gamma n hn i = 2 := by
      rw [← ZMod.natCast_zmod_val (a8tn_gamma n hn i), h2]; norm_num
    exact ⟨1, by rw [hγ]; decide⟩
  · have hγ : a8tn_gamma n hn i = 4 := by
      rw [← ZMod.natCast_zmod_val (a8tn_gamma n hn i), h4]; norm_num
    exact ⟨2, by rw [hγ]; decide⟩

theorem ggSL9_normalizer_torus {n : GGSL9V ≃ₗ[ZMod 2] GGSL9V}
    (hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) :
    ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3), ∀ f : Fin 3 → ZMod 7,
      n * ggSL9TorusCoord (Multiplicative.ofAdd f) * n⁻¹ =
        ggSL9TorusCoord (Multiplicative.ofAdd (vecMul f (a8MonK3 π k))) := by
  refine ⟨a8tn_piEquiv n hn, fun i => Classical.choose (a8tn_gamma_pow_two n hn i), ?_⟩
  intro f
  have hk : ∀ i, (2 : ZMod 7) ^ (Classical.choose (a8tn_gamma_pow_two n hn i)).val =
      a8tn_gamma n hn i := fun i => Classical.choose_spec (a8tn_gamma_pow_two n hn i)
  have hα : a8tn_alpha n hn f =
      vecMul f (a8MonK3 (a8tn_piEquiv n hn)
        fun i => Classical.choose (a8tn_gamma_pow_two n hn i)) := by
    funext j
    set i : Fin 3 := (a8tn_piEquiv n hn).symm j with hi
    have hji : a8tn_pi n hn i = j := by
      rw [← a8tn_piEquiv_apply n hn i, hi]
      exact Equiv.apply_symm_apply (a8tn_piEquiv n hn) j
    have hpi : a8tn_pi n hn i = a8tn_piEquiv n hn i := (a8tn_piEquiv_apply n hn i).symm
    rw [← hji, a8tn_alpha_entry n hn f i, a8tn_vecMul_a8MonK3]
    rw [hpi, Equiv.symm_apply_apply, hk i]
  rw [← a8tn_alpha_spec n hn f, hα]

end CFSG.StandardType.A8Coord

end
