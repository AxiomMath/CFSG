module

public import CFSG.Quasithin.H13.L32A715f
public import CFSG.Quasithin.EmptyFaithful.S152He8Rep
public import CFSG.Quasithin.H13.L32A715e
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open
open scoped commutatorElement MatrixGroups

namespace Heis

variable {X : Type*} [Group X] (h : IsPOnePlusTwo 3 X)
include h

theorem apply_mul_eq_inv {φ : MulAut X} (hφZ : ∀ z ∈ Subgroup.center X, φ z = z) (k : X)
    (hk : φ k * k ∈ Subgroup.center X) : φ (k * (φ k * k)) = (k * (φ k * k))⁻¹ := by
  set w := φ k * k with hw
  have hc : ∀ y : X, y * w = w * y := Subgroup.mem_center_iff.mp hk
  rw [map_mul, hφZ w hk]
  have hφk : φ k = w * k⁻¹ := by rw [hw]; group
  rw [hφk, mul_inv_rev]
  have e1 : w * k⁻¹ * w = w * w * k⁻¹ := by rw [mul_assoc, hc k⁻¹, ← mul_assoc]
  have e2 : w * w = w⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three', pow_three_eq h])
  rw [e1, e2]

theorem eq_of_inv_of_inv {φ : MulAut X} (hφZ : ∀ z ∈ Subgroup.center X, φ z = z) {u v : X}
    (hu : φ u = u⁻¹) (hv : φ v = v⁻¹) (huv : u⁻¹ * v ∈ Subgroup.center X) : u = v := by
  set z := u⁻¹ * v with hz
  have hvz : v = u * z := by rw [hz]; group
  have hc : ∀ y : X, y * z⁻¹ = z⁻¹ * y :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ huv)
  have h1 : u⁻¹ * z = u⁻¹ * z⁻¹ := by
    have e := hv
    rw [hvz, map_mul, hu, hφZ z huv, mul_inv_rev, ← hc u⁻¹] at e
    exact e
  have hz1 : z = 1 := eq_one_of_eq_inv h (mul_left_cancel h1)
  rw [hvz, hz1, mul_one]

theorem exists_fixed_of_comm {φ ψ : MulAut X} (hφZ : ∀ z ∈ Subgroup.center X, φ z = z)
    (hφ : ∀ x, φ x * x ∈ Subgroup.center X) {m : ℕ} (hψ : ψ ^ 3 ^ m = 1)
    (hcomm : ∀ x, φ (ψ x) = ψ (φ x)) : ∃ a : X, a ∉ Subgroup.center X ∧ ψ a = a := by
  obtain ⟨k, hkZ, hfk⟩ := exists_mem_fixMod_of_pow h hψ
  have hψZ := fix_center_of_pow_odd h ψ (Odd.pow (by decide)) hψ
  set w := φ k * k with hw
  have hwZ : w ∈ Subgroup.center X := hφ k
  refine ⟨k * w, fun haZ => hkZ ?_, ?_⟩
  · have e : k = (k * w) * w⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ haZ (Subgroup.inv_mem _ hwZ)
  · have ha := apply_mul_eq_inv h hφZ k hwZ
    have h1 : φ (ψ (k * w)) = (ψ (k * w))⁻¹ := by rw [hcomm, ha, map_inv]
    refine (eq_of_inv_of_inv h hφZ ha h1 ?_).symm
    rw [map_mul, hψZ w hwZ]
    have e : (k * w)⁻¹ * (ψ k * w) = w⁻¹ * (k⁻¹ * (ψ k * k⁻¹) * k⁻¹⁻¹) * w⁻¹⁻¹ := by group
    rw [e]
    exact Subgroup.instNormalCenter.conj_mem _ (Subgroup.instNormalCenter.conj_mem _ hfk _) _

theorem comm_pow_right (a b : X) (j : ℕ) : ⁅a, b ^ j⁆ = ⁅a, b⁆ ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, comm_mul_right h, ih, pow_succ]

theorem comm_pow_pow (a b : X) (i j : ℕ) : ⁅a ^ i, b ^ j⁆ = ⁅a, b⁆ ^ (i * j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, comm_mul_left h, ih, comm_pow_right h, ← pow_add]
    congr 1
    ring

theorem comm_mul_pow (a b : X) (i j k l : ℕ) :
    ⁅a ^ i * b ^ j, a ^ k * b ^ l⁆ = ⁅a, b⁆ ^ (i * l) * (⁅a, b⁆⁻¹) ^ (j * k) := by
  rw [comm_mul_left h, comm_mul_right h, comm_mul_right h, comm_pow_pow h, comm_pow_pow h,
    comm_pow_pow h, comm_pow_pow h, commutatorElement_self, commutatorElement_self, one_pow,
    one_pow, one_mul, mul_one, commutatorElement_inv]

end Heis

theorem ofAdd_eq_mul (v : Fin 2 → ZMod 3) :
    Multiplicative.ofAdd v = Multiplicative.ofAdd (Pi.single 0 1) ^ (v 0).val *
      Multiplicative.ofAdd (Pi.single 1 1) ^ (v 1).val := by
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, Pi.add_apply, Pi.smul_apply]
  fin_cases i <;> simp [nsmul_eq_mul]

namespace Heis

section Coord

variable {X : Type} [Group X] (h : IsPOnePlusTwo 3 X)
include h

variable {f : Multiplicative (Fin 2 → ZMod 3) ≃* X ⧸ Subgroup.center X}

omit h in
theorem mk_eq_of_coord {a b : X}
    (ha : (a : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 0 1)))
    (hb : (b : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 1 1)))
    (v : Fin 2 → ZMod 3) :
    f (Multiplicative.ofAdd v) = ((a ^ (v 0).val * b ^ (v 1).val : X) : X ⧸ Subgroup.center X) := by
  rw [L32A.ofAdd_eq_mul v, map_mul, map_pow, map_pow, ← ha, ← hb, QuotientGroup.mk_mul,
    QuotientGroup.mk_pow, QuotientGroup.mk_pow]

omit h in
theorem exists_apply_eq {a b : X}
    (ha : (a : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 0 1)))
    (hb : (b : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 1 1)))
    (σ : MulAut X) (j : Fin 2) {x : X}
    (hx : (x : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single j 1))) :
    ∃ z ∈ Subgroup.center X, σ x = z * (a ^ ((He8.repGL f (He8.quotAut (Subgroup.center X) σ) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 j).val * b ^ ((He8.repGL f
        (He8.quotAut (Subgroup.center X) σ) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 j).val) := by
  set M := (He8.repGL f (He8.quotAut (Subgroup.center X) σ) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    with hM
  have h1 := He8.repGL_mulVec f (He8.quotAut (Subgroup.center X) σ) (Pi.single j 1)
  rw [← hM, ← hx, He8.quotAut_mk] at h1
  have h2 : f (Multiplicative.ofAdd (M.mulVec (Pi.single j 1))) =
      ((σ x : X) : X ⧸ Subgroup.center X) := by
    rw [h1]
    simp
  rw [mk_eq_of_coord ha hb] at h2
  have h3 : (M.mulVec (Pi.single j 1)) 0 = M 0 j := by simp
  have h4 : (M.mulVec (Pi.single j 1)) 1 = M 1 j := by simp
  rw [h3, h4, QuotientGroup.eq] at h2
  refine ⟨σ x * (a ^ (M 0 j).val * b ^ (M 1 j).val)⁻¹, ?_, by group⟩
  have e : σ x * (a ^ (M 0 j).val * b ^ (M 1 j).val)⁻¹ =
      (a ^ (M 0 j).val * b ^ (M 1 j).val) * ((a ^ (M 0 j).val * b ^ (M 1 j).val)⁻¹ * σ x) *
        (a ^ (M 0 j).val * b ^ (M 1 j).val)⁻¹ := by group
  rw [e]
  exact Subgroup.instNormalCenter.conj_mem _ h2 _

omit h in
theorem pow_eq_pow_of_cast_eq {c : X} (hc : c ^ 3 = 1) {n m : ℕ}
    (hnm : (n : ZMod 3) = (m : ZMod 3)) : c ^ n = c ^ m := by
  rw [← pow_mod_three_eq hc n, ← pow_mod_three_eq hc m]
  congr 1
  exact (ZMod.natCast_eq_natCast_iff' n m 3).mp hnm

theorem apply_comm_eq_pow_det {a b : X}
    (ha : (a : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 0 1)))
    (hb : (b : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 1 1)))
    (σ : MulAut X) :
    σ ⁅a, b⁆ = ⁅a, b⁆ ^ (He8.repGL f (He8.quotAut (Subgroup.center X) σ) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)).det.val := by
  set M := (He8.repGL f (He8.quotAut (Subgroup.center X) σ) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    with hM
  obtain ⟨z₁, hz₁, he₁⟩ := exists_apply_eq ha hb σ 0 ha
  obtain ⟨z₂, hz₂, he₂⟩ := exists_apply_eq ha hb σ 1 hb
  rw [← hM] at he₁ he₂
  have hσ : σ ⁅a, b⁆ = ⁅σ a, σ b⁆ := map_commutatorElement σ a b
  rw [hσ, he₁, he₂, comm_center_left h _ hz₁, comm_center_right h _ hz₂, comm_mul_pow h]
  have hc3 : ⁅a, b⁆ ^ 3 = 1 := pow_three_eq h _
  have hinv : ⁅a, b⁆⁻¹ = ⁅a, b⁆ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hc3
  rw [hinv, ← pow_mul, ← pow_add]
  apply pow_eq_pow_of_cast_eq hc3
  rw [Matrix.det_fin_two, ZMod.natCast_val, ZMod.cast_id]
  push_cast
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id,
    ZMod.cast_id, ZMod.cast_id, ZMod.cast_id]
  generalize M 0 0 = p
  generalize M 0 1 = q
  generalize M 1 0 = r
  generalize M 1 1 = s
  revert p q r s
  decide

theorem comm_ne_one_of_coord {a b : X}
    (ha : (a : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 0 1)))
    (hb : (b : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 1 1))) :
    ⁅a, b⁆ ≠ 1 := by
  intro h1
  obtain ⟨x, y, hxy⟩ := exists_comm_ne_one h
  have hco : ∀ g : X, ∃ z ∈ Subgroup.center X, g = z * (a ^ (Multiplicative.toAdd
      (f.symm (g : X ⧸ Subgroup.center X)) 0).val * b ^ (Multiplicative.toAdd
        (f.symm (g : X ⧸ Subgroup.center X)) 1).val) := by
    intro g
    have e := mk_eq_of_coord ha hb (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)))
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply, QuotientGroup.eq] at e
    refine ⟨g * (a ^ (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)) 0).val *
      b ^ (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)) 1).val)⁻¹, ?_, by group⟩
    have e2 : g * (a ^ (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)) 0).val *
        b ^ (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)) 1).val)⁻¹ =
        g * (g⁻¹ * (a ^ (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)) 0).val *
          b ^ (Multiplicative.toAdd (f.symm (g : X ⧸ Subgroup.center X)) 1).val))⁻¹ * g⁻¹ := by
      group
    rw [e2]
    exact Subgroup.instNormalCenter.conj_mem _ (Subgroup.inv_mem _ e) _
  obtain ⟨z₁, hz₁, hx⟩ := hco x
  obtain ⟨z₂, hz₂, hy⟩ := hco y
  apply hxy
  rw [hx, hy, comm_center_left h _ hz₁, comm_center_right h _ hz₂, comm_mul_pow h, h1, inv_one,
    one_pow, one_pow, one_mul]

theorem det_eq_one_of_fix {a b : X}
    (ha : (a : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 0 1)))
    (hb : (b : X ⧸ Subgroup.center X) = f (Multiplicative.ofAdd (Pi.single 1 1)))
    {σ : MulAut X} (hσ : σ ⁅a, b⁆ = ⁅a, b⁆) :
    (He8.repGL f (He8.quotAut (Subgroup.center X) σ) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
  have := Fact.mk Nat.prime_three
  set M := (He8.repGL f (He8.quotAut (Subgroup.center X) σ) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    with hM
  have e := apply_comm_eq_pow_det h ha hb σ
  rw [← hM, hσ] at e
  have hord : orderOf ⁅a, b⁆ = 3 :=
    orderOf_eq_prime (pow_three_eq h _) (comm_ne_one_of_coord h ha hb)
  have h1 : ⁅a, b⁆ ^ 1 = ⁅a, b⁆ ^ M.det.val := by rw [pow_one]; exact e
  rw [pow_eq_pow_iff_modEq, hord] at h1
  have hlt := ZMod.val_lt M.det
  have h2 : M.det.val = 1 := by
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt hlt] at h1
    exact h1.symm
  rw [← ZMod.natCast_zmod_val M.det, h2, Nat.cast_one]

end Coord

end Heis

theorem sl23_pow_four : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3), A.det = 1 → A ^ 16 = 1 →
    A ^ 4 = 1 := by
  decide +kernel

theorem sl23_mul_pow_four : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 3), A.det = 1 → A ^ 4 = 1 →
    B.det = 1 → B ^ 4 = 1 → (A * B) ^ 4 = 1 := by
  decide +kernel

theorem gl23_pow_48 (u : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : u ^ 48 = 1 := by
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  rw [← hc]
  exact pow_card_eq_one'

theorem sl32_eq_one_of_comm {c : SL(3, ZMod 2)} (hc : ∀ g : SL(3, ZMod 2), g * c = c * g) :
    c = 1 := by
  have hcZ : c ∈ Subgroup.center SL(3, ZMod 2) := Subgroup.mem_center_iff.mpr hc
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcZ
  have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
  have hr1 : r = 1 := key r (by rw [Fintype.card_fin] at hr; exact hr)
  apply Subtype.ext
  rw [← hrc, hr1]
  simp

theorem mem_normalizer_of_conj_mem_721 {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  let f : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simpa [f] using this
  have hsurj := Finite.surjective_of_injective hf
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := hsurj ⟨_, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  exact this ▸ y.2

theorem exists_pow_lift_three {G : Type*} [Group G] {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {g : G}
    {n : ℕ} (hg : g ^ 3 ^ n ∈ Q) : ∃ u : ℕ, (g ^ u) ^ 3 ^ n = 1 ∧ g⁻¹ * g ^ u ∈ Q := by
  obtain ⟨c, hc⟩ := hQ ⟨_, hg⟩
  have hc' : (g ^ 3 ^ n) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hg hc'
    refine ⟨2 ^ c, by rw [pow_zero, pow_one]; exact hc', ?_⟩
    exact Q.mul_mem (Q.inv_mem hg) (Q.pow_mem hg _)
  · have hcop : Nat.Coprime (2 ^ c) (3 ^ n) := Nat.Coprime.pow _ _ (by norm_num)
    obtain ⟨u, -, hu⟩ :=
      Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hn.ne' (by norm_num))
    refine ⟨2 ^ c * u, ?_, ?_⟩
    · rw [← pow_mul, show 2 ^ c * u * 3 ^ n = 3 ^ n * 2 ^ c * u by ring, pow_mul, pow_mul, hc',
        one_pow]
    · have e : 2 ^ c * u = 3 ^ n * (2 ^ c * u / 3 ^ n) + 1 := by
        have := Nat.div_add_mod (2 ^ c * u) (3 ^ n)
        rw [hu] at this
        omega
      rw [e, pow_succ', inv_mul_cancel_left, pow_mul]
      exact Q.pow_mem hg _

theorem mem_of_mem_sup_of_pow_three {G : Type*} [Group G] {N Q : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hQ : IsPGroup 2 ↥Q) {g : G} (hg : g ∈ Q ⊔ N)
    {k : ℕ} (hk : g ^ 3 ^ k = 1) : g ∈ N := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q N hQN] at hg
  obtain ⟨q, hq, n, hn, hqn⟩ := Set.mem_mul.mp hg
  subst hqn
  obtain ⟨a, ha⟩ := hQ ⟨q, hq⟩
  have ha' : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hpow : ∀ m : ℕ, (q ^ m)⁻¹ * (q * n) ^ m ∈ N := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (q ^ (m + 1))⁻¹ * (q * n) ^ (m + 1) =
          q⁻¹ * ((q ^ m)⁻¹ * (q * n) ^ m) * q⁻¹⁻¹ * n := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN (Q.inv_mem hq)) _).mp ih) hn
  have h2 : (q * n) ^ 2 ^ a ∈ N := by
    have := hpow (2 ^ a)
    rwa [ha', inv_one, one_mul] at this
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, pow_one] at hk
    rw [hk]
    exact N.one_mem
  have hcop : Nat.Coprime (2 ^ a) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  have h3 : 1 < 3 ^ k := Nat.one_lt_pow hk0.ne' (by norm_num)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h3
  have e : q * n = ((q * n) ^ 2 ^ a) ^ u := by
    rw [← pow_mul, ← Nat.mod_add_div (2 ^ a * u) (3 ^ k), hu, pow_add, pow_mul, hk, one_pow,
      mul_one, pow_one]
  rw [e]
  exact N.pow_mem h2 u

end CFSG.Quasithin.H13.L32A
