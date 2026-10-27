module

public import CFSG.Quasithin.Recognition.RuTypeJ25
public import CFSG.Quasithin.Recognition.RuTypeSD16

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

theorem exists_inv_mem_coset {G : Type*} [Group G] [Finite G] {x y : G} {N : Subgroup G}
    (hx : x ^ 3 = 1) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hy : y⁻¹ * (x * y * x) ∈ N)
    (hN : ¬ 3 ∣ Nat.card N) : ∃ n ∈ N, x * (y * n) * x = y * n := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxN' : ∀ n ∈ N, x⁻¹ * n * x ∈ N := by
    intro n hn
    have hxi : x⁻¹ = x * x := by
      rw [inv_eq_iff_mul_eq_one]
      calc x * (x * x) = x ^ 3 := (pow_three x).symm
        _ = 1 := hx
    have h1 := hxN _ (hxN n hn)
    have e : x⁻¹ * n * x = x * (x * n * x⁻¹) * x⁻¹ := by
      calc x⁻¹ * n * x = (x * x) * n * (x * x)⁻¹ := by rw [← hxi, inv_inv]
        _ = x * (x * n * x⁻¹) * x⁻¹ := by group
    rw [e]
    exact h1
  have hmem : ∀ n : N, y⁻¹ * (x * (y * n) * x) ∈ N := fun n => by
    have e : y⁻¹ * (x * (y * n) * x) = (y⁻¹ * (x * y * x)) * (x⁻¹ * n * x) := by group
    rw [e]
    exact N.mul_mem hy (hxN' _ n.2)
  let f : N → N := fun n => ⟨_, hmem n⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : y⁻¹ * (x * (y * a) * x) = y⁻¹ * (x * (y * b) * x) := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using h
  have : Fintype N := Fintype.ofFinite N
  let σ : Equiv.Perm N := Equiv.ofBijective f hf.bijective_of_finite
  have hσk : ∀ (k : ℕ) (n : N), ((σ ^ k) n : G) = y⁻¹ * (x ^ k * (y * n) * x ^ k) := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [pow_succ', Equiv.Perm.mul_apply]
      show y⁻¹ * (x * (y * ((σ ^ k) n : G)) * x) = _
      rw [ih n]
      group
  have hσp : σ ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun n => Subtype.ext ?_
    rw [hσk 3 n, hx]
    simp
  have hNc : ¬ 3 ∣ Fintype.card N := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨n, hn⟩ := Equiv.Perm.exists_fixed_point_of_prime hNc hσp
  refine ⟨n, n.2, ?_⟩
  have h := congrArg Subtype.val hn
  have h1 : y⁻¹ * (x * (y * n) * x) = n := h
  calc x * (y * n) * x = y * (y⁻¹ * (x * (y * n) * x)) := by group
    _ = y * n := by rw [h1]

variable {G : Type*} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

@[expose] noncomputable def t1el : G := M.exists_t1.choose

theorem t1el_mem_S : M.t1el ∈ ruS M.L := M.exists_t1.choose_spec.fst

theorem bel_t1el : (M.bel : G) * M.t1el = M.t1el * M.bel :=
  M.exists_t1.choose_spec.snd.1

theorem χ_t1el : Multiplicative.toAdd (M.χ ⟨M.t1el, M.t1el_mem_S⟩) =
    !![1, 0, 0; 0, 0, 1; 0, 1, 1] :=
  M.exists_t1.choose_spec.snd.2

theorem t1el_mem_HB : M.t1el ∈ M.HB := M.mem_HB.mpr ⟨M.t1el_mem_S, M.bel_t1el⟩

@[expose] noncomputable def Rel : G := M.jel * M.t1el

theorem jel_mem_TB : M.jel ∈ M.TB := Or.inr (by rw [mul_inv_cancel]; exact one_mem _)

theorem Rel_mem_TB : M.Rel ∈ M.TB := Or.inr (by
  show M.jel * M.t1el * M.jel⁻¹ ∈ M.HB
  exact M.jel_conj_HB M.t1el_mem_HB)

theorem jel_sq : M.jel ^ 2 = 1 := M.jel_spec.2.2.1

theorem jel_mul_self : M.jel * M.jel = 1 := by rw [← pow_two]; exact M.jel_sq

omit [Finite G] in
theorem z_mul_self : M.z * M.z = 1 := by rw [← pow_two]; exact M.z_sq

theorem Rel_pow_four : M.Rel ^ 4 = M.z := by
  obtain ⟨hjH, hjK, -, -, -⟩ := M.jel_spec
  have hji := M.jel_inv
  have ht1 := M.t1el_mem_S
  have hB1 := M.t1el_mem_HB
  obtain ⟨t2, ht2, hb2, hχ2⟩ := M.exists_t2
  have hB2 : t2 ∈ M.HB := M.mem_HB.mpr ⟨ht2, hb2⟩
  have hzc' : ∀ w ∈ ruZ M.T, ∀ g ∈ ruH M.T, w * g = g * w := fun w hw g hg => M.Z_comm_H hw hg
  have hjt1 : (M.jel * M.t1el * M.jel⁻¹)⁻¹ * t2 ∈ ruZ M.T := by
    have h1 := M.conj_HC_of_not_mem_K hjH hjK (M.HB_le_HC hB1)
    have hnt : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.nel.2) M.t1el).mp ht1
    have h2 : ((M.nel : G) * M.t1el * (M.nel : G)⁻¹)⁻¹ * t2 ∈ ruU M.L M.T := by
      have hk : (⟨_, hnt⟩ : ruS M.L)⁻¹ * ⟨t2, ht2⟩ ∈ M.χ.ker := by
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd.injective
        rw [M.toAdd_χ_mul, M.toAdd_χ_inv, M.χ_conj M.nel ⟨M.t1el, ht1⟩, M.θ_nel, M.χ_t1el, hχ2,
          SL3.n0_b0mat, toAdd_one]
        ext i j
        have h : ∀ a : ZMod 2, a + a = 0 := by decide
        exact h _
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
      exact M.V_le_U hk
    have hU : (M.jel * M.t1el * M.jel⁻¹)⁻¹ * t2 ∈ ruU M.L M.T := by
      have e : (M.jel * M.t1el * M.jel⁻¹)⁻¹ * t2 = (M.jel * M.t1el * M.jel⁻¹)⁻¹ *
          ((M.nel : G) * M.t1el * (M.nel : G)⁻¹) *
          (((M.nel : G) * M.t1el * (M.nel : G)⁻¹)⁻¹ * t2) := by group
      rw [e]
      exact mul_mem h1 h2
    exact M.mem_Z_of_HB_U (M.jel_conj_HB hB1) hB2 hU
  have hR2 : M.Rel ^ 2 = (M.jel * M.t1el * M.jel⁻¹) * M.t1el := by
    simp only [Rel, pow_two]
    rw [hji]
    group
  have hR2B : M.Rel ^ 2 ∈ M.HB := by rw [hR2]; exact mul_mem (M.jel_conj_HB hB1) hB1
  have hR2Z : M.Rel ^ 2 ∉ ruZ M.T := by
    intro hZ
    rw [hR2] at hZ
    set c := M.jel * M.t1el * M.jel⁻¹
    have hHt1 : M.t1el ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T ht1)
    have hct : c * M.t1el * M.t1el = M.t1el * (c * M.t1el) := hzc' _ hZ M.t1el hHt1
    have h1 : c * M.t1el = M.t1el * c := by
      rw [← mul_assoc] at hct
      exact mul_right_cancel hct
    have hmem : M.t1el * t2 ∈ ruZ M.T := by
      have e : M.t1el * t2 = (c * M.t1el) * (c⁻¹ * t2) := by
        calc M.t1el * t2 = (M.t1el * c) * (c⁻¹ * t2) := by group
          _ = (c * M.t1el) * (c⁻¹ * t2) := by rw [h1]
      rw [e]
      exact mul_mem hZ hjt1
    have hk : (⟨M.t1el, ht1⟩ : ruS M.L) * ⟨t2, ht2⟩ ∈ M.χ.ker := by
      rw [M.χ_ker, Subgroup.mem_subgroupOf]
      exact M.toRuData.Z_le_V hmem
    rw [MonoidHom.mem_ker] at hk
    have := congrArg Multiplicative.toAdd hk
    rw [M.toAdd_χ_mul, M.χ_t1el, hχ2, toAdd_one] at this
    exact absurd this (by decide)
  rw [show 4 = 2 * 2 by rfl, pow_mul]
  exact M.sq_eq_z_of_HB hR2B hR2Z

theorem Rel_pow_eight : M.Rel ^ 8 = 1 := by
  rw [show 8 = 4 * 2 by rfl, pow_mul, M.Rel_pow_four, pow_two, M.z_mul_self]

theorem jel_conj_Rel : M.jel * M.Rel * M.jel⁻¹ = M.Rel ^ 3 := by
  have hji := M.jel_inv
  have ht1 := M.t1el_mem_S
  have hzc : ∀ g ∈ ruH M.T, M.z * g = g * M.z := fun g hg => M.Z_comm_H M.z_mem_Z hg
  have ht1z : M.t1el ^ 2 = M.z := by
    refine M.sq_eq_z_of_HB M.t1el_mem_HB fun hZ => ?_
    have hk : (⟨M.t1el, ht1⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [M.χ_ker, Subgroup.mem_subgroupOf]
      exact M.toRuData.Z_le_V hZ
    have h0 := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hk)
    rw [M.χ_t1el, toAdd_one] at h0
    exact absurd h0 (by decide)
  have ht1i : M.t1el⁻¹ = M.t1el * M.z := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, ht1z, M.z_mul_self]
  have hR3 : M.Rel ^ 3 = M.z * M.Rel⁻¹ := by
    rw [← M.Rel_pow_four]
    group
  rw [hR3]
  simp only [Rel]
  rw [mul_inv_rev, ht1i, hji]
  have hzt : M.z * M.t1el = M.t1el * M.z :=
    hzc M.t1el (M.toRuData.T_le_H (M.toRuData.S_le_T ht1))
  calc M.jel * (M.jel * M.t1el) * M.jel = (M.jel * M.jel) * M.t1el * M.jel := by group
    _ = M.t1el * M.jel := by rw [M.jel_mul_self, one_mul]
    _ = (M.z * M.z) * M.t1el * M.jel := by rw [M.z_mul_self, one_mul]
    _ = M.z * (M.z * M.t1el) * M.jel := by group
    _ = M.z * (M.t1el * M.z) * M.jel := by rw [hzt]
    _ = M.z * (M.t1el * M.z * M.jel) := by group

theorem orderOf_Rel : orderOf M.Rel = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := M.Rel)
    (by rw [show 2 ^ 2 = 4 by rfl, M.Rel_pow_four]; exact M.z_ne_one)
    (by rw [show 2 ^ (2 + 1) = 8 by rfl]; exact M.Rel_pow_eight)
  rw [h]
  rfl

theorem Rel_pow_eq_of_mod {m n : ℕ} (h : m % 8 = n % 8) : M.Rel ^ m = M.Rel ^ n := by
  rw [← pow_mod_orderOf, M.orderOf_Rel, h, ← M.orderOf_Rel, pow_mod_orderOf]

theorem jel_pow_eq_of_mod {m n : ℕ} (h : m % 2 = n % 2) : M.jel ^ m = M.jel ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf M.jel = 2 := orderOf_eq_prime M.jel_sq (fun h1 => M.jel_not_mem_HB (by
    rw [h1]; exact one_mem _))
  rw [← pow_mod_orderOf, ho, h, ← ho, pow_mod_orderOf]

theorem jel_mul_Rel_pow (n : ℕ) : M.jel * M.Rel ^ n = M.Rel ^ (3 * n) * M.jel := by
  have h : M.jel * M.Rel ^ n * M.jel⁻¹ = M.Rel ^ (3 * n) := by
    rw [← conj_pow, M.jel_conj_Rel, ← pow_mul]
  calc M.jel * M.Rel ^ n = M.jel * M.Rel ^ n * M.jel⁻¹ * M.jel := by group
    _ = M.Rel ^ (3 * n) * M.jel := by rw [h]

theorem Rel_pow_mul_jel_ne_one (n : ℕ) : M.Rel ^ n * M.jel ≠ 1 := by
  intro h
  have hj : M.jel = (M.Rel ^ n)⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2n : M.Rel ^ (2 * n) = 1 := by
    rw [pow_mul', ← inv_inv (M.Rel ^ n), ← hj, inv_pow, M.jel_sq, inv_one]
  have h4 : 4 ∣ n := by
    have hdvd := orderOf_dvd_of_pow_eq_one h2n
    rw [M.orderOf_Rel] at hdvd
    omega
  obtain ⟨k, rfl⟩ := h4
  have hRk : M.Rel ^ (4 * k) = M.z ^ k := by rw [pow_mul, M.Rel_pow_four]
  have hzk : M.z ^ k ∈ M.HB := pow_mem (Subgroup.mem_inf.mpr ⟨M.U_le_Q (M.V_le_U M.z_mem_V),
    (M.mem_centralizer_B).mpr (M.Z_comm_H M.z_mem_Z M.bel_mem_H).symm⟩) k
  apply M.jel_not_mem_HB
  rw [hj, hRk]
  exact inv_mem hzk

@[expose] noncomputable def κ : SD16C →* G where
  toFun p := M.Rel ^ p.a.val * M.jel ^ p.e.val
  map_one' := by simp [SD16C.one_def]
  map_mul' p q := by
    obtain ⟨a, e⟩ := p
    obtain ⟨b, f⟩ := q
    show M.Rel ^ (a + (if e = 0 then b else 3 * b)).val * M.jel ^ (e + f).val =
      M.Rel ^ a.val * M.jel ^ e.val * (M.Rel ^ b.val * M.jel ^ f.val)
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) e with rfl | rfl
    · rw [ite_eq_left (rfl : (0 : ZMod 2) = 0), zero_add, ZMod.val_zero, pow_zero, mul_one,
        ← mul_assoc, ← pow_add]
      congr 1
      exact M.Rel_pow_eq_of_mod (by rw [ZMod.val_add]; omega)
    · have h1 : (1 : ZMod 2).val = 1 := rfl
      rw [ite_eq_right (by decide : ¬ ((1 : ZMod 2) = 0)), h1, pow_one]
      calc M.Rel ^ (a + 3 * b).val * M.jel ^ (1 + f).val
          = M.Rel ^ (a.val + 3 * b.val) * M.jel ^ (1 + f.val) := by
            rw [M.Rel_pow_eq_of_mod (m := (a + 3 * b).val) (n := a.val + 3 * b.val)
              (by rw [ZMod.val_add, ZMod.val_mul, show (3 : ZMod 8).val = 3 from rfl]; omega),
              M.jel_pow_eq_of_mod (m := (1 + f).val) (n := 1 + f.val)
              (by rw [ZMod.val_add, h1]; omega)]
        _ = M.Rel ^ a.val * (M.Rel ^ (3 * b.val) * M.jel) * M.jel ^ f.val := by
            rw [pow_add, pow_add, pow_one]
            simp only [mul_assoc]
        _ = M.Rel ^ a.val * (M.jel * M.Rel ^ b.val) * M.jel ^ f.val := by
            rw [M.jel_mul_Rel_pow]
        _ = M.Rel ^ a.val * M.jel * (M.Rel ^ b.val * M.jel ^ f.val) := by
            simp only [mul_assoc]

theorem κ_apply (p : SD16C) : M.κ p = M.Rel ^ p.a.val * M.jel ^ p.e.val := rfl

theorem κ_mem_TB (p : SD16C) : M.κ p ∈ M.TB :=
  mul_mem (pow_mem M.Rel_mem_TB _) (pow_mem M.jel_mem_TB _)

theorem κ_injective : Function.Injective M.κ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro p hp
  rw [MonoidHom.mem_ker, κ_apply] at hp
  rw [Subgroup.mem_bot]
  have ha : p.a.val < 8 := ZMod.val_lt p.a
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) p.e with he | he
  · rw [he, ZMod.val_zero, pow_zero, mul_one] at hp
    have hdvd := orderOf_dvd_of_pow_eq_one hp
    rw [M.orderOf_Rel] at hdvd
    have h0 : p.a.val = 0 := by omega
    have : p.a = 0 := (ZMod.val_eq_zero p.a).mp h0
    cases p
    simp only at this he
    rw [this, he]
    rfl
  · rw [he, show (1 : ZMod 2).val = 1 from rfl, pow_one] at hp
    exact absurd hp (M.Rel_pow_mul_jel_ne_one _)

theorem κ_range : M.κ.range = M.TB := by
  classical
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact M.κ_mem_TB p
  · rw [M.card_TB, ← Nat.card_congr (MonoidHom.ofInjective M.κ_injective).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_congr SD16C.equivProd, Fintype.card_prod,
      ZMod.card, ZMod.card]

theorem mem_TB_iff {x : G} : x ∈ M.TB ↔ ∃ p : SD16C, M.κ p = x := by
  rw [← M.κ_range]
  exact MonoidHom.mem_range

theorem κ_c4 : M.κ SD16C.c4 = M.z := by
  rw [κ_apply]
  show M.Rel ^ 4 * M.jel ^ 0 = M.z
  rw [pow_zero, mul_one, M.Rel_pow_four]

theorem center_TB {x : G} (hx : x ∈ M.TB) (hc : ∀ y ∈ M.TB, x * y = y * x) :
    x = 1 ∨ x = M.z := by
  obtain ⟨p, rfl⟩ := M.mem_TB_iff.mp hx
  have hp : ∀ q : SD16C, p * q = q * p := by
    intro q
    apply M.κ_injective
    rw [map_mul, map_mul]
    exact hc _ (M.κ_mem_TB q)
  rcases SD16C.center_cases p hp with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr M.κ_c4

@[expose] noncomputable def SB : Subgroup G := SD16C.SBC.map M.κ

theorem SB_le_TB : M.SB ≤ M.TB := by
  rintro _ ⟨p, -, rfl⟩
  exact M.κ_mem_TB p

theorem κ_mem_SB_iff (p : SD16C) : M.κ p ∈ M.SB ↔ p ∈ SD16C.SBC := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    rwa [← M.κ_injective hqp]
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem z_mem_SB : M.z ∈ M.SB := ⟨_, SD16C.c4_mem_SBC, M.κ_c4⟩

theorem mem_SB_of_sq {x : G} (hx : x ∈ M.TB) (hx2 : x * x = 1) : x ∈ M.SB := by
  obtain ⟨p, rfl⟩ := M.mem_TB_iff.mp hx
  refine (M.κ_mem_SB_iff p).mpr (SD16C.mem_SBC_of_sq p (M.κ_injective ?_))
  rw [map_mul, hx2, map_one]

theorem sq_of_mem_SB {x : G} (hx : x ∈ M.SB) : x * x = 1 ∨ x * x = M.z := by
  obtain ⟨p, hp, rfl⟩ := hx
  rcases SD16C.sq_of_mem_SBC p hp with h | h
  · left; rw [← map_mul, h, map_one]
  · right; rw [← map_mul, h, M.κ_c4]

theorem conj_mem_SB {t x : G} (ht : t ∈ M.TB) (hx : x ∈ M.SB) : t * x * t⁻¹ ∈ M.SB := by
  obtain ⟨p, rfl⟩ := M.mem_TB_iff.mp ht
  obtain ⟨q, hq, rfl⟩ := hx
  rw [← map_inv, ← map_mul, ← map_mul]
  exact (M.κ_mem_SB_iff _).mpr (SD16C.conj_mem_SBC p q hq)

@[expose] noncomputable def fel : G := M.κ SD16C.f

theorem fel_mem_TB : M.fel ∈ M.TB := M.κ_mem_TB _

theorem fel_sq : M.fel * M.fel = M.z := by
  rw [fel, ← map_mul, SD16C.f_sq, M.κ_c4]

theorem mul_fel_inv_mem_SB {x : G} (hx : x ∈ M.TB) (hxS : x ∉ M.SB) : x * M.fel⁻¹ ∈ M.SB := by
  obtain ⟨p, rfl⟩ := M.mem_TB_iff.mp hx
  have hp : p ∉ SD16C.SBC := fun h => hxS ((M.κ_mem_SB_iff p).mpr h)
  rw [fel, ← map_inv, ← map_mul]
  exact (M.κ_mem_SB_iff _).mpr (SD16C.mul_f_inv_mem_SBC p hp)

theorem nonempty_SB_dihedral : Nonempty (M.SB ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := SD16C.nonempty_SBC_dihedral
  exact ⟨(Subgroup.equivMapOfInjective _ M.κ M.κ_injective).symm.trans e⟩

theorem SB_prod_inv {x : G} (hx : x ∈ M.SB) :
    ∃ a b : G, a ∈ M.TB ∧ b ∈ M.TB ∧ a * a = 1 ∧ b * b = 1 ∧ x = a * b := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨a, b, ha, hb, rfl⟩ := SD16C.SBC_prod_inv p hp
  refine ⟨M.κ a, M.κ b, M.κ_mem_TB a, M.κ_mem_TB b, ?_, ?_, map_mul _ _ _⟩
  · rw [← map_mul, ha, map_one]
  · rw [← map_mul, hb, map_one]

theorem bel_comm_CHB {x : G} (hx : x ∈ M.CHB) : (M.bel : G) * x = x * M.bel :=
  (M.mem_CHB.mp hx).2

theorem TB_inf_B : ∀ x ∈ M.TB, x ∈ M.B → x = 1 := by
  intro x hxT hxB
  have h3 : orderOf x ∣ 3 := by
    rw [← M.card_B]
    exact Subgroup.orderOf_dvd_natCard _ hxB
  have h16 : orderOf x ∣ 16 := by
    rw [← M.card_TB]
    exact Subgroup.orderOf_dvd_natCard _ hxT
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h3 h16)

theorem CHB_eq_mul {x : G} (hx : x ∈ M.CHB) : ∃ t ∈ M.TB, ∃ b ∈ M.B, x = t * b := by
  classical
  let F : M.TB × M.B → M.CHB := fun p => ⟨(p.1 : G) * p.2, mul_mem (M.TB_le_CHB p.1.2)
    (M.B_le_CHB p.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨t, b⟩ ⟨t', b'⟩ h
    have h1 : (t : G) * b = t' * b' := congrArg Subtype.val h
    have h2 : (t' : G)⁻¹ * t = b' * (b : G)⁻¹ := by
      calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * (t * b) * (b : G)⁻¹ := by group
        _ = (t' : G)⁻¹ * (t' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hb'b : (b' : G) * (b : G)⁻¹ ∈ M.B := mul_mem b'.2 (inv_mem b.2)
    have h3 := M.TB_inf_B _ (mul_mem (inv_mem t'.2) t.2) (by rw [h2]; exact hb'b)
    have htt : (t : G) = t' := by
      calc (t : G) = t' * ((t' : G)⁻¹ * t) := by group
        _ = t' := by rw [h3, mul_one]
    have hbb : (b : G) = b' := by
      have := h1
      rw [htt] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext htt) (Subtype.ext hbb)
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (le_of_eq (by
    rw [Nat.card_prod, M.card_TB, M.card_B, M.card_CHB]))
  obtain ⟨⟨t, b⟩, hp⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨t, t.2, b, b.2, (congrArg Subtype.val hp).symm⟩

theorem exists_inverter : ∃ n ∈ ruH M.T, n * (M.bel : G) * n⁻¹ = (M.bel : G)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbS : ∀ s ∈ ruS M.L, (M.bel : G) * s * (M.bel : G)⁻¹ ∈ ruS M.L := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.bel.2) s).mp hs
  have hy : (M.nel : G)⁻¹ * ((M.bel : G) * M.nel * M.bel) ∈ ruS M.L := by
    have hk : M.nel⁻¹ * (M.bel * M.nel * M.bel) ∈ M.θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, M.θ_nel, M.θ_bel]
      decide +kernel
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hS3 : ¬ 3 ∣ Nat.card (ruS M.L) := by rw [M.toRuData.card_S]; norm_num
  obtain ⟨s, hs, hfix⟩ := exists_inv_mem_coset M.bel_pow_three hbS hy hS3
  refine ⟨(M.nel : G) * s, mul_mem M.nel_mem_H (M.toRuData.T_le_H (M.toRuData.S_le_T hs)), ?_⟩
  set n := (M.nel : G) * s
  calc n * (M.bel : G) * n⁻¹ = (M.bel : G)⁻¹ * ((M.bel : G) * n * M.bel) * n⁻¹ := by group
    _ = (M.bel : G)⁻¹ := by rw [hfix]; group

theorem exists_conj_bel {y : G} (hy : y ∈ ruH M.T) (hy3 : orderOf y = 3) :
    ∃ h ∈ ruH M.T, h * y * h⁻¹ = M.bel ∨ h * y * h⁻¹ = (M.bel : G)⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set H := ruH M.T
  have hcardH : Nat.card H = 2 ^ 11 * 120 := M.toRuData.card_H
  have hBp : IsPGroup 3 (Subgroup.zpowers (⟨M.bel, M.bel_mem_H⟩ : H)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk, M.orderOf_bel]
    exact ⟨1, by norm_num⟩
  obtain ⟨PB, hPB⟩ := hBp.exists_le_sylow
  have hf : (Nat.card H).factorization 3 = 1 := by
    have h1 := PB.card_eq_multiplicity
    have h3 : 3 ∣ Nat.card PB := by
      have := Subgroup.card_dvd_of_le hPB
      rwa [Nat.card_zpowers, Subgroup.orderOf_mk, M.orderOf_bel] at this
    have h4 : Nat.card PB ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
    rw [h1] at h3 h4
    generalize (Nat.card H).factorization 3 = f at h3 h4 ⊢
    rw [hcardH] at h4
    rcases Nat.lt_or_ge f 2 with h | h
    · interval_cases f
      · norm_num at h3
      · rfl
    · exfalso
      have := (pow_dvd_pow 3 h).trans h4
      norm_num at this
  have hle3 : ∀ P : Sylow 3 H, Nat.card P = 3 := fun P => by
    rw [P.card_eq_multiplicity, hf, pow_one]
  have hYp : IsPGroup 3 (Subgroup.zpowers (⟨y, hy⟩ : H)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk, hy3]
    exact ⟨1, by norm_num⟩
  obtain ⟨PY, hPY⟩ := hYp.exists_le_sylow
  have hPYeq : (PY : Subgroup H) = Subgroup.zpowers ⟨y, hy⟩ := by
    refine (Subgroup.eq_of_le_of_card_ge hPY (le_of_eq ?_)).symm
    rw [hle3, Nat.card_zpowers, Subgroup.orderOf_mk, hy3]
  have hPBeq : (PB : Subgroup H) = Subgroup.zpowers ⟨M.bel, M.bel_mem_H⟩ := by
    refine (Subgroup.eq_of_le_of_card_ge hPB (le_of_eq ?_)).symm
    rw [hle3, Nat.card_zpowers, Subgroup.orderOf_mk, M.orderOf_bel]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H PY PB
  have hmem : c * ⟨y, hy⟩ * c⁻¹ ∈ (PB : Subgroup H) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨⟨y, hy⟩, by rw [hPYeq]; exact Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩
  rw [hPBeq, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk' : (c : G) * y * (c : G)⁻¹ = (M.bel : G) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  refine ⟨c, c.2, ?_⟩
  rw [hk']
  have hb3 : (M.bel : G) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]; exact M.bel_pow_three
  rw [zpow_eq_zpow_emod k hb3] at hk' ⊢
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h | h | h
  · exfalso
    rw [h, zpow_zero] at hk'
    have hy1 : y = 1 := by
      calc y = (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * c := by group
        _ = 1 := by rw [hk']; group
    rw [hy1, orderOf_one] at hy3
    norm_num at hy3
  · left; rw [h, zpow_one]
  · right
    rw [h]
    have : (M.bel : G) ^ (2 : ℤ) * M.bel = 1 := by
      rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by rfl, hb3]
    exact eq_inv_of_mul_eq_one_left this

noncomputable abbrev GB : Subgroup G := Subgroup.centralizer (M.B : Set G)

theorem mem_GB {x : G} : x ∈ M.GB ↔ (M.bel : G) * x = x * M.bel := M.mem_centralizer_B

theorem CHB_le_GB : M.CHB ≤ M.GB := inf_le_right

theorem TB_le_GB : M.TB ≤ M.GB := M.TB_le_CHB.trans M.CHB_le_GB

theorem conj_z_GB {g : G} (hg : g * M.z * g⁻¹ ∈ M.GB) :
    ∃ k ∈ M.GB, k * M.z * k⁻¹ = g * M.z * g⁻¹ := by
  have hbz : (M.bel : G) * (g * M.z * g⁻¹) = (g * M.z * g⁻¹) * M.bel := (M.mem_GB.mp hg)
  have hH : g⁻¹ * M.bel * g ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    calc M.z * (g⁻¹ * M.bel * g) = g⁻¹ * ((g * M.z * g⁻¹) * M.bel) * g := by group
      _ = g⁻¹ * ((M.bel : G) * (g * M.z * g⁻¹)) * g := by rw [hbz]
      _ = g⁻¹ * M.bel * g * M.z := by group
  have h3 : orderOf (g⁻¹ * (M.bel : G) * g) = 3 := by
    rw [show g⁻¹ * (M.bel : G) * g = g⁻¹ * (M.bel : G) * g⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj_eq, M.orderOf_bel]
  obtain ⟨h, hhH, hh⟩ := M.exists_conj_bel hH h3
  have hhz : h * M.z * h⁻¹ = M.z := by
    rw [(M.mem_H_iff_comm.mp hhH).symm, mul_inv_cancel_right]
  set k := g * h⁻¹ with hk
  have hkz : k * M.z * k⁻¹ = g * M.z * g⁻¹ := by
    calc k * M.z * k⁻¹ = g * (h⁻¹ * M.z * h) * g⁻¹ := by rw [hk]; group
      _ = g * M.z * g⁻¹ := by
          congr 2
          calc h⁻¹ * M.z * h = h⁻¹ * (h * M.z * h⁻¹) * h := by rw [hhz]
            _ = M.z := by group
  have hkb : k⁻¹ * M.bel * k = M.bel ∨ k⁻¹ * M.bel * k = (M.bel : G)⁻¹ := by
    have e : k⁻¹ * M.bel * k = h * (g⁻¹ * M.bel * g) * h⁻¹ := by rw [hk]; group
    rw [e]
    exact hh
  rcases hkb with hb | hb
  · refine ⟨k, M.mem_GB.mpr ?_, hkz⟩
    calc (M.bel : G) * k = k * (k⁻¹ * M.bel * k) := by group
      _ = k * M.bel := by rw [hb]
  · obtain ⟨n, hnH, hn⟩ := M.exists_inverter
    have hnz : n * M.z * n⁻¹ = M.z := by
      rw [(M.mem_H_iff_comm.mp hnH).symm, mul_inv_cancel_right]
    refine ⟨k * n⁻¹, M.mem_GB.mpr ?_, ?_⟩
    · have e : (k * n⁻¹)⁻¹ * M.bel * (k * n⁻¹) = M.bel := by
        calc (k * n⁻¹)⁻¹ * M.bel * (k * n⁻¹) = n * (k⁻¹ * M.bel * k) * n⁻¹ := by group
          _ = n * (M.bel : G)⁻¹ * n⁻¹ := by rw [hb]
          _ = (n * M.bel * n⁻¹)⁻¹ := by group
          _ = M.bel := by rw [hn, inv_inv]
      calc (M.bel : G) * (k * n⁻¹) = (k * n⁻¹) * ((k * n⁻¹)⁻¹ * M.bel * (k * n⁻¹)) := by group
        _ = (k * n⁻¹) * M.bel := by rw [e]
    · calc k * n⁻¹ * M.z * (k * n⁻¹)⁻¹ = k * (n⁻¹ * M.z * n) * k⁻¹ := by group
        _ = k * M.z * k⁻¹ := by
            congr 2
            calc n⁻¹ * M.z * n = n⁻¹ * (n * M.z * n⁻¹) * n := by rw [hnz]
              _ = M.z := by group
        _ = g * M.z * g⁻¹ := hkz

theorem eq_TB_of_le {P : Subgroup G} (hP : IsPGroup 2 P) (hTP : M.TB ≤ P) (hPB : P ≤ M.GB) :
    P = M.TB := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : M.TB.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun x hx => ?_) hTP
    have : (⟨x, hx⟩ : P) ∈ M.TB.subgroupOf P := htop ▸ Subgroup.mem_top _
    exact this
  have : Finite P := inferInstance
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hxP : (x : G) ∈ P := x.2
  have hxT' : (x : G) ∉ M.TB := fun h => hxT h
  have hnorm : ∀ t ∈ M.TB, (x : G) * t * (x : G)⁻¹ ∈ M.TB := by
    intro t ht
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨t, hTP ht⟩).mp ht
    exact h1
  have hnorm' : ∀ t ∈ M.TB, (x : G)⁻¹ * t * x ∈ M.TB := by
    intro t ht
    have hmemP : (x : G)⁻¹ * t * x ∈ P := mul_mem (mul_mem (inv_mem hxP) (hTP ht)) hxP
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨_, hmemP⟩).mpr (by
      show (x : G) * ((x : G)⁻¹ * t * x) * (x : G)⁻¹ ∈ M.TB
      rw [show (x : G) * ((x : G)⁻¹ * t * x) * (x : G)⁻¹ = t by group]
      exact ht)
    exact h1
  have hzT : M.z ∈ M.TB := M.SB_le_TB M.z_mem_SB
  have hxz : (x : G) * M.z * (x : G)⁻¹ = M.z := by
    have hmem := hnorm _ hzT
    have hcen : ∀ y ∈ M.TB, (x : G) * M.z * (x : G)⁻¹ * y = y * ((x : G) * M.z * (x : G)⁻¹) := by
      intro y hy
      have hy' := hnorm' y hy
      have hzc : M.z * ((x : G)⁻¹ * y * x) = ((x : G)⁻¹ * y * x) * M.z :=
        M.Z_comm_H M.z_mem_Z (M.TB_le_CHB hy').1
      calc (x : G) * M.z * (x : G)⁻¹ * y = (x : G) * (M.z * ((x : G)⁻¹ * y * x)) * (x : G)⁻¹ := by
            group
        _ = (x : G) * (((x : G)⁻¹ * y * x) * M.z) * (x : G)⁻¹ := by rw [hzc]
        _ = y * ((x : G) * M.z * (x : G)⁻¹) := by group
    rcases M.center_TB hmem hcen with h | h
    · exfalso
      apply M.z_ne_one
      calc M.z = (x : G)⁻¹ * ((x : G) * M.z * (x : G)⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hxH : (x : G) ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    calc M.z * x = (x : G) * M.z * (x : G)⁻¹ * x := by rw [hxz]
      _ = (x : G) * M.z := by group
  have hxC : (x : G) ∈ M.CHB := ⟨hxH, hPB hxP⟩
  set K := P ⊓ M.CHB
  have hTK : M.TB ≤ K := le_inf hTP M.TB_le_CHB
  have hKlt : M.TB < K := lt_of_le_of_ne hTK (fun h => hxT' (by rw [h]; exact ⟨hxP, hxC⟩))
  have hKp : IsPGroup 2 K := hP.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hKp)
  have hdvd : Nat.card K ∣ 48 := by
    rw [← M.card_CHB]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hlt16 : 16 < Nat.card K := by
    rw [← M.card_TB]
    exact Subgroup.card_lt_of_lt hKlt
  rw [hk] at hdvd hlt16
  have hk4 : k ≤ 4 := by
    by_contra hk5
    push Not at hk5
    have h32 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 hk5
    have := h32.trans hdvd
    norm_num at this
  have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
  omega

@[expose] noncomputable def TBsyl : Sylow 2 M.GB where
  toSubgroup := M.TB.subgroupOf M.GB
  isPGroup' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.iff_card.mpr ⟨4, (card_subgroupOf_of_le M.TB_le_GB).trans M.card_TB⟩
  is_maximal' := by
    intro Q hQ hTQ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ' : IsPGroup 2 (Q.map M.GB.subtype) := hQ.map _
    have hle : M.TB ≤ Q.map M.GB.subtype := by
      intro x hx
      exact ⟨⟨x, M.TB_le_GB hx⟩, hTQ (show (⟨x, M.TB_le_GB hx⟩ : M.GB) ∈
        M.TB.subgroupOf M.GB from hx), rfl⟩
    have heq := M.eq_TB_of_le hQ' hle (Subgroup.map_subtype_le Q)
    apply le_antisymm _ hTQ
    intro y hy
    show (y : G) ∈ M.TB
    rw [← heq]
    exact ⟨y, hy, rfl⟩

theorem exists_conj_le_TB {P : Subgroup G} (hP : IsPGroup 2 P) (hPB : P ≤ M.GB) :
    ∃ g ∈ M.GB, ∀ x ∈ P, g * x * g⁻¹ ∈ M.TB := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 (P.subgroupOf M.GB) := fun g => by
    obtain ⟨k, hk⟩ := hP ⟨((g : M.GB) : G), g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨PS, hPS⟩ := hPp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M.GB PS M.TBsyl
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxPS : (⟨x, hPB hx⟩ : M.GB) ∈ (PS : Subgroup M.GB) :=
    hPS (show (⟨x, hPB hx⟩ : M.GB) ∈ P.subgroupOf M.GB from hx)
  have hmem : c * ⟨x, hPB hx⟩ * c⁻¹ ∈ (M.TBsyl : Subgroup M.GB) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, hxPS, by simp [MulAut.conj_apply]⟩
  exact hmem

theorem lemma_J27_9 {x : G} (hx : x ∈ M.GB) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ g ∈ M.GB, g * M.z * g⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hord]
    exact ⟨1, by norm_num⟩
  have hle : Subgroup.zpowers x ≤ M.GB := by
    rw [Subgroup.zpowers_le]
    exact hx
  obtain ⟨g, hgB, hg⟩ := M.exists_conj_le_TB hp hle
  set y := g * x * g⁻¹ with hy
  have hyT : y ∈ M.TB := hg x (Subgroup.mem_zpowers x)
  have hy2 : y ^ 2 = 1 := by rw [hy, conj_pow, hx2]; group
  have hy1 : y ≠ 1 := fun h => hx1 (by
    calc x = g⁻¹ * y * g := by rw [hy]; group
      _ = 1 := by rw [h]; group)
  have hyz : ∃ k ∈ M.GB, k * M.z * k⁻¹ = y := by
    by_cases hyz : y = M.z
    · exact ⟨1, one_mem _, by rw [hyz]; group⟩
    ·
      have hyHB : y ∉ M.HB := by
        intro hB
        have hyZ : y ∉ ruZ M.T := by
          intro hZ
          rcases M.mem_Z_iff.mp hZ with h | h
          · exact hy1 h
          · exact hyz h
        have := M.sq_eq_z_of_HB hB hyZ
        rw [hy2] at this
        exact M.z_ne_one this.symm
      have hyHj : y * M.jel⁻¹ ∈ M.HB :=
        (show y ∈ M.HB ∨ y * M.jel⁻¹ ∈ M.HB from hyT).resolve_left hyHB
      have hyH : y ∈ ruH M.T := (M.TB_le_CHB hyT).1
      have hyK : y ∉ M.K := by
        intro hK
        apply M.jel_spec.2.1
        have e : M.jel = (y * M.jel⁻¹)⁻¹ * y := by group
        rw [e]
        exact mul_mem (inv_mem (M.Q_le_K (Subgroup.mem_inf.mp hyHj).1)) hK
      obtain ⟨c, hc⟩ := isConj_iff.mp (M.lemma_J26.2.2.1 y hyH hyK hy2)
      exact M.conj_z_GB (g := c) (by rw [hc]; exact M.TB_le_GB hyT) |>.imp fun k hk =>
        ⟨hk.1, hk.2.trans hc⟩
  obtain ⟨k, hkB, hk⟩ := hyz
  refine ⟨g⁻¹ * k, mul_mem (inv_mem hgB) hkB, ?_⟩
  calc g⁻¹ * k * M.z * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * M.z * k⁻¹) * g := by group
    _ = x := by rw [hk, hy]; group

end RuDataM

end CFSG.Quasithin.RuType
