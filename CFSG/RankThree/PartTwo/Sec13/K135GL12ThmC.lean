module

public import CFSG.RankThree.PartTwo.Sec13.K135GL12FS
public import CFSG.RankThree.PartTwo.Sec13.K135GL12Out
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.RankThree.PartOne.SLB4A.ClassA
public import CFSG.RankThree.PartOne.SLB4A.ExcOddHcomb

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135GL12

open CFSG CFSG.RankThree.PartTwo.Sec13.K135SF TauCeti Subgroup
  CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420 CFSG.HardMathSupport.Solomon.Coordinator

section
open Subgroup

theorem not_h2a_of_E_p2 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (a b z : S)
    (hab : a * b = b * a) (ha : orderOf a = p) (hb : orderOf b = p) (hba : b ∉ Subgroup.zpowers a)
    (hz : orderOf z = 2) (haz : a * z = z * a) (hbz : b * z = z * b) :
    ∃ F : Subgroup (MulAut S), F ≤ (MulAut.conj : S →* MulAut S).range ∧
      CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ 2 ∧
      ∃ T : Subgroup S, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ φ ∈ F, T.map φ.toMonoidHom = T := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcentre : ∀ g : S, (∀ x : S, g * x = x * g) → g = 1 := by
    intro g hg
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · have hmem : g ∈ Subgroup.center S :=
        Subgroup.mem_center_iff.mpr (fun x => (hg x).symm)
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have hx : x ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.mp hx y).symm
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply hcentre g
    intro x
    have hx : g * x * g⁻¹ = x := by
      have h2 := congrArg (fun φ : MulAut S => φ x) hg
      simpa [MulAut.conj_apply] using h2
    exact (mul_inv_eq_iff_eq_mul).mp hx
  have hpm : ∀ (g : S) (n m : ℕ), orderOf g = p → g ^ ((n + m) % p) = g ^ n * g ^ m := by
    intro g n m hg
    rw [← pow_add, ← hg, pow_mod_orderOf]
  have hkey : ∀ A1 A2 B1 B2 : S, A2 * B1 = B1 * A2 →
      A1 * A2 * (B1 * B2) = A1 * B1 * (A2 * B2) := by
    intro A1 A2 B1 B2 h
    calc A1 * A2 * (B1 * B2) = A1 * (A2 * (B1 * B2)) := mul_assoc _ _ _
      _ = A1 * (B1 * (A2 * B2)) := by rw [← mul_assoc A2 B1 B2, h, mul_assoc B1 A2 B2]
      _ = A1 * B1 * (A2 * B2) := (mul_assoc _ _ _).symm
  have hmul : ∀ w w' : ZMod p × ZMod p,
      a ^ (w + w').1.val * b ^ (w + w').2.val
        = (a ^ w.1.val * b ^ w.2.val) * (a ^ w'.1.val * b ^ w'.2.val) := by
    intro w w'
    rw [Prod.fst_add, Prod.snd_add, ZMod.val_add, ZMod.val_add, hpm a _ _ ha, hpm b _ _ hb]
    exact hkey _ _ _ _ ((show Commute a b from hab).pow_pow w'.1.val w.2.val).eq
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Multiplicative (ZMod p × ZMod p) →* S,
      ∀ u, Φ u = a ^ (Multiplicative.toAdd u).1.val * b ^ (Multiplicative.toAdd u).2.val :=
    ⟨MonoidHom.mk'
      (fun u => a ^ (Multiplicative.toAdd u).1.val * b ^ (Multiplicative.toAdd u).2.val)
      (fun u v => hmul (Multiplicative.toAdd u) (Multiplicative.toAdd v)), fun u => rfl⟩
  have hpart : ∀ m n : ℕ, a ^ m * b ^ n = 1 → p ∣ n := by
    intro m n hmn
    by_contra hpn
    have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hbn : b ^ n ∈ Subgroup.zpowers a := by
      rw [eq_inv_of_mul_eq_one_right hmn]
      exact (Subgroup.zpowers a).inv_mem ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) m)
    have h1 : b ^ (n * k % p) = b ^ (n * k) := by
      have h := pow_mod_orderOf b (n * k)
      rwa [hb] at h
    have hbk : b = (b ^ n) ^ k := by
      rw [← pow_mul, ← h1, hk, pow_one]
    apply hba
    rw [hbk]
    exact (Subgroup.zpowers a).pow_mem hbn k
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rw [hΦ] at hu
    have hyb : p ∣ (Multiplicative.toAdd u).2.val := hpart _ _ hu
    have hy0 : (Multiplicative.toAdd u).2 = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hyb (ZMod.val_lt _)
    rw [hy0, ZMod.val_zero, pow_zero, mul_one] at hu
    have hxa : p ∣ (Multiplicative.toAdd u).1.val := by
      have h := orderOf_dvd_of_pow_eq_one hu
      rwa [ha] at h
    have hx0 : (Multiplicative.toAdd u).1 = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hxa (ZMod.val_lt _)
    have htoAdd : Multiplicative.toAdd u = 0 := Prod.ext hx0 hy0
    exact htoAdd
  have hpow : ∀ u : Multiplicative (ZMod p × ZMod p), u ^ p = 1 := by
    intro u
    have h0 : (u ^ p).toAdd = 0 := by
      rw [toAdd_pow]
      ext <;> simp
    exact h0
  have hinjF : Function.Injective ((MulAut.conj : S →* MulAut S).comp Φ) := by
    rw [MonoidHom.coe_comp]
    exact hconj.comp hΦinj
  have hcardZ : Nat.card (Multiplicative (ZMod p × ZMod p)) = p ^ 2 := by
    show Nat.card (ZMod p × ZMod p) = p ^ 2
    rw [Nat.card_prod, Nat.card_zmod, sq]
  refine ⟨((MulAut.conj : S →* MulAut S).comp Φ).range, ?_, ?_, ?_, zpowers z, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Φ u, rfl⟩
  · unfold CFSG.Open.IsElemAbelian
    constructor
    · refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      show (x : MulAut S) * (y : MulAut S) = (y : MulAut S) * (x : MulAut S)
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm u v]
    · intro x hx
      obtain ⟨u, rfl⟩ := hx
      rw [← map_pow, hpow u, map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hinjF).toEquiv.symm).trans hcardZ
  · intro h
    have h1 : z = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  · intro φ hφ
    obtain ⟨u, rfl⟩ := hφ
    have hcZ : Φ u * z = z * Φ u := by
      rw [hΦ u]
      exact (Commute.mul_left (Commute.pow_left (show Commute a z from haz) _)
        (Commute.pow_left (show Commute b z from hbz) _)).eq
    have hfix : (((MulAut.conj : S →* MulAut S).comp Φ) u).toMonoidHom z = z := by
      show (MulAut.conj (Φ u)) z = z
      rw [MulAut.conj_apply, hcZ, mul_inv_cancel_right]
    rw [MonoidHom.map_zpowers, hfix]

end

section
open TauCeti

private noncomputable def gl12kPi (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 4) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K))

private lemma gl12kC2_pi_eq_one {K : Type} [Field K] (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    gl12kPi K g = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) :=
  QuotientGroup.eq_one_iff g

private lemma gl12kC2_pi_eq {K : Type} [Field K] (g h : Matrix.SpecialLinearGroup (Fin 4) K) :
    gl12kPi K g = gl12kPi K h ↔
      g⁻¹ * h ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) :=
  QuotientGroup.eq

private lemma gl12kC2_center_scalar {K : Type} [Field K] (M : Matrix.SpecialLinearGroup (Fin 4) K)
    (hM : M ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K)) :
    ∃ r : K, Matrix.scalar (Fin 4) r = (M : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hM
  exact ⟨r, hr⟩

private lemma gl12kC2_pow_coe {K : Type} [Field K] (M : Matrix.SpecialLinearGroup (Fin 4) K)
    (d : Fin 4 → K) (hM : (M : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d) (n : ℕ) :
    ((M ^ n : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => d i ^ n) := by
  rw [Matrix.SpecialLinearGroup.coe_pow, hM, Matrix.diagonal_pow]
  try rfl

private lemma gl12kC2_comm_of_diag {K : Type} [Field K] (M N : Matrix.SpecialLinearGroup (Fin 4) K)
    (d e : Fin 4 → K) (hM : (M : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d)
    (hN : (N : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal e) : M * N = N * M := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM, hN,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private lemma gl12kC2_mul_scalar_apply {K : Type} [Field K] (M : Matrix (Fin 4) (Fin 4) K) (r : K)
    (i j : Fin 4) : (M * Matrix.scalar (Fin 4) r) i j = M i j * r := by
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]

private lemma gl12kC2_core {K : Type} [Field K] (x : K) (hx0 : x ≠ 0) (hx13 : x ^ 13 = 1)
    (hx1 : x ≠ 1) (hxinv : x ≠ x⁻¹) (h2 : (2 : K) ≠ 0) :
    ∃ a b z : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K,
      a * b = b * a ∧ orderOf a = 13 ∧ orderOf b = 13 ∧ b ∉ Subgroup.zpowers a ∧
        orderOf z = 2 ∧ a * z = z * a ∧ b * z = z * b := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 4) K,
      (A : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![x, x⁻¹, 1, 1] :=
    ⟨⟨Matrix.diagonal ![x, x⁻¹, 1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four, hx0]⟩,
      rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix.SpecialLinearGroup (Fin 4) K,
      (B : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![x, 1, x⁻¹, 1] :=
    ⟨⟨Matrix.diagonal ![x, 1, x⁻¹, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four, hx0]⟩,
      rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix.SpecialLinearGroup (Fin 4) K,
      (Z : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![1, 1, -1, -1] :=
    ⟨⟨Matrix.diagonal ![1, 1, -1, -1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩, rfl⟩
  have hA13 : A ^ 13 = 1 := by
    apply Subtype.ext
    rw [gl12kC2_pow_coe A _ hA 13, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [inv_pow, hx13]
  have hB13 : B ^ 13 = 1 := by
    apply Subtype.ext
    rw [gl12kC2_pow_coe B _ hB 13, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [inv_pow, hx13]
  have hZ2 : Z ^ 2 = 1 := by
    apply Subtype.ext
    rw [gl12kC2_pow_coe Z _ hZ 2, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hAB : A * B = B * A := gl12kC2_comm_of_diag A B _ _ hA hB
  have hAZ : A * Z = Z * A := gl12kC2_comm_of_diag A Z _ _ hA hZ
  have hBZ : B * Z = Z * B := gl12kC2_comm_of_diag B Z _ _ hB hZ
  have hA1 : gl12kPi K A ≠ 1 := by
    intro h
    obtain ⟨r, hr⟩ := gl12kC2_center_scalar A ((gl12kC2_pi_eq_one A).mp h)
    have e0 := congrFun (congrFun hr 0) 0
    have e1 := congrFun (congrFun hr 1) 1
    rw [hA] at e0 e1
    simp [Matrix.scalar_apply] at e0 e1
    exact hxinv (e0.symm.trans e1)
  have hB1 : gl12kPi K B ≠ 1 := by
    intro h
    obtain ⟨r, hr⟩ := gl12kC2_center_scalar B ((gl12kC2_pi_eq_one B).mp h)
    have e0 := congrFun (congrFun hr 0) 0
    have e1 := congrFun (congrFun hr 1) 1
    rw [hB] at e0 e1
    simp [Matrix.scalar_apply] at e0 e1
    exact hx1 (e0.symm.trans e1)
  have hZ1 : gl12kPi K Z ≠ 1 := by
    intro h
    obtain ⟨r, hr⟩ := gl12kC2_center_scalar Z ((gl12kC2_pi_eq_one Z).mp h)
    have e0 := congrFun (congrFun hr 0) 0
    have e2 := congrFun (congrFun hr 2) 2
    rw [hZ] at e0 e2
    simp [Matrix.scalar_apply] at e0 e2
    exact h1 (e0.symm.trans e2)
  have hnot : gl12kPi K B ∉ Subgroup.zpowers (gl12kPi K A) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : gl12kPi K (A ^ k) = gl12kPi K B := by
      rw [map_zpow]
      exact hk
    obtain ⟨r, hr⟩ := gl12kC2_center_scalar _ ((gl12kC2_pi_eq _ _).mp hk')
    have hA13z : A ^ (13 : ℤ) = 1 := by
      exact_mod_cast hA13
    have hnonneg : (0 : ℤ) ≤ k % 13 := Int.emod_nonneg k (by norm_num)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k % 13 :=
      ⟨(k % 13).toNat, Int.toNat_of_nonneg hnonneg⟩
    have hkn : A ^ k = A ^ n := by
      rw [zpow_eq_zpow_emod k hA13z, ← hn, zpow_natCast]
    have hAk : ((A ^ k : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal (fun i => ![x, x⁻¹, 1, 1] i ^ n) := by
      rw [hkn, gl12kC2_pow_coe A _ hA n]
    have hBr : (B : Matrix (Fin 4) (Fin 4) K) =
        ((A ^ k : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          Matrix.scalar (Fin 4) r := by
      rw [hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have e2 := congrFun (congrFun hBr 2) 2
    have e3 := congrFun (congrFun hBr 3) 3
    rw [gl12kC2_mul_scalar_apply, hAk, hB] at e2 e3
    simp at e2 e3
    exact hx1 (inv_eq_one.mp (e2.trans e3.symm))
  refine ⟨gl12kPi K A, gl12kPi K B, gl12kPi K Z, ?_, ?_, ?_, hnot, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hAB]
  · exact orderOf_eq_prime (by rw [← map_pow, hA13, map_one]) hA1
  · exact orderOf_eq_prime (by rw [← map_pow, hB13, map_one]) hB1
  · exact orderOf_eq_prime (by rw [← map_pow, hZ2, map_one]) hZ1
  · rw [← map_mul, ← map_mul, hAZ]
  · rw [← map_mul, ← map_mul, hBZ]

private lemma gl12kC2_transport {T G : Type} [Group T] [Group G] (ψ : T ≃* G)
    (hG : ∃ a b z : G, a * b = b * a ∧ orderOf a = 13 ∧ orderOf b = 13 ∧
      b ∉ Subgroup.zpowers a ∧ orderOf z = 2 ∧ a * z = z * a ∧ b * z = z * b) :
    ∃ a b z : T, a * b = b * a ∧ orderOf a = 13 ∧ orderOf b = 13 ∧
      b ∉ Subgroup.zpowers a ∧ orderOf z = 2 ∧ a * z = z * a ∧ b * z = z * b := by
  obtain ⟨a', b', z', h1, h2, h3, h4, h5, h6, h7⟩ := hG
  refine ⟨ψ.symm a', ψ.symm b', ψ.symm z', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h1]
  · rw [MulEquiv.orderOf_eq]
    exact h2
  · rw [MulEquiv.orderOf_eq]
    exact h3
  · intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    apply h4
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply ψ.symm.injective
    rw [map_zpow, hk]
  · rw [MulEquiv.orderOf_eq]
    exact h5
  · rw [← map_mul, ← map_mul, h6]
  · rw [← map_mul, ← map_mul, h7]

theorem exists_E_p2_of_A3_27 {q : PrimePower} (hv : (LieTypeIndex.A 3 q).Valid) (hq : q.card = 27)
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩) :
    ∃ a b z : T, a * b = b * a ∧ orderOf a = 13 ∧ orderOf b = 13 ∧ b ∉ Subgroup.zpowers a ∧
      orderOf z = 2 ∧ a * z = z * a ∧ b * z = z * b := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : q.p ^ q.exponent = 27 := (PrimePower.card_def q).symm.trans hq
  have hexp : q.exponent ≠ 0 := q.exponent_pos.ne'
  have hKcard : Nat.card (GaloisField q.p q.exponent) = 27 := by
    rw [GaloisField.card q.p q.exponent hexp]
    exact hcard
  have hdvd : 13 ∣ Nat.card (GaloisField q.p q.exponent)ˣ := by
    rw [Nat.card_units, hKcard]
    norm_num
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 13 hdvd
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  have hx0 : (u : GaloisField q.p q.exponent) ≠ 0 := u.ne_zero
  have hx13 : (u : GaloisField q.p q.exponent) ^ 13 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hx1 : (u : GaloisField q.p q.exponent) ≠ 1 := fun h => hu1 (Units.ext h)
  have hxinv : (u : GaloisField q.p q.exponent) ≠ (u : GaloisField q.p q.exponent)⁻¹ := by
    intro h
    have hsq : u * u = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      calc (u : GaloisField q.p q.exponent) * (u : GaloisField q.p q.exponent)
          = (u : GaloisField q.p q.exponent) * (u : GaloisField q.p q.exponent)⁻¹ := by
            rw [← h]
        _ = 1 := mul_inv_cancel₀ hx0
    have h3 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [hu] at h3
    norm_num at h3
  have h2 : (2 : GaloisField q.p q.exponent) ≠ 0 := by
    intro h
    have h2' : ((2 : ℕ) : GaloisField q.p q.exponent) = 0 := by exact_mod_cast h
    have hpdvd : q.p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p 2).mp h2'
    have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hpdvd
    have h27 : 2 ∣ 27 := by
      rw [← hcard, hp2]
      exact dvd_pow_self 2 hexp
    norm_num at h27
  have hcore := gl12kC2_core ((u : GaloisField q.p q.exponent)) hx0 hx13 hx1 hxinv h2
  let ψ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv)
  exact gl12kC2_transport ψ hcore

end

section
open TauCeti

private def gl12kC3_tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => gl12kC3_tri n + n

private lemma gl12kC3_tri_thirteen : gl12kC3_tri 13 = 78 := by decide

private lemma gl12kC3_pow {K : Type} [Field K] (a b c : K) (n : ℕ) :
    (!![1, a, c; 0, 1, b; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) ^ n =
      !![1, (n : K) * a, (n : K) * c + a * b * (gl12kC3_tri n : K); 0, 1, (n : K) * b; 0, 0, 1] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gl12kC3_tri, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, gl12kC3_tri] <;> ring

private def gl12kC3_U (K : Type) [Field K] : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ a b c : K, (g : Matrix (Fin 3) (Fin 3) K) = !![1, a, c; 0, 1, b; 0, 0, 1]}
  mul_mem' := by
    rintro g h ⟨a, b, c, hg⟩ ⟨a', b', c', hh⟩
    refine ⟨a + a', b + b', c + c' + a * b', ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  one_mem' := ⟨0, 0, 0, by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_three]⟩
  inv_mem' := by
    rintro g ⟨a, b, c, hg⟩
    refine ⟨-a, -b, a * b - c, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hg, Matrix.adjugate_fin_three_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

private def gl12kC3_x (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private def gl12kC3_y (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private lemma gl12kC3_x_coe (K : Type) [Field K] :
    ((gl12kC3_x K : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

private lemma gl12kC3_y_coe (K : Type) [Field K] :
    ((gl12kC3_y K : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl

private lemma gl12kC3_x_mem (K : Type) [Field K] : gl12kC3_x K ∈ gl12kC3_U K := ⟨1, 0, 0, rfl⟩

private lemma gl12kC3_y_mem (K : Type) [Field K] : gl12kC3_y K ∈ gl12kC3_U K := ⟨0, 1, 0, rfl⟩

private def gl12kC3_pi (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))

private lemma gl12kC3_xy_coe (K : Type) [Field K] :
    ((gl12kC3_x K * gl12kC3_y K : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 1, 1; 0, 1, 1; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, gl12kC3_x_coe, gl12kC3_y_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private lemma gl12kC3_yx_coe (K : Type) [Field K] :
    ((gl12kC3_y K * gl12kC3_x K : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 1, 0; 0, 1, 1; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, gl12kC3_x_coe, gl12kC3_y_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private lemma gl12kC3_comm_coe (K : Type) [Field K] :
    ((((gl12kC3_x K * gl12kC3_y K)⁻¹ * (gl12kC3_y K * gl12kC3_x K) :
      Matrix.SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = -1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, gl12kC3_xy_coe,
    gl12kC3_yx_coe, Matrix.adjugate_fin_three_of]
  norm_num [Matrix.mul_apply, Fin.sum_univ_three]

private lemma gl12kC3_not_central (K : Type) [Field K] :
    (gl12kC3_x K * gl12kC3_y K)⁻¹ * (gl12kC3_y K * gl12kC3_x K) ∉
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  have h02 := congrFun (congrFun hr 0) 2
  rw [gl12kC3_comm_coe, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (show (0 : Fin 3) ≠ 2 by decide)] at h02
  exact one_ne_zero (neg_eq_zero.mp h02.symm)

private def gl12kC3_Q (K : Type) [Field K] {T : Type} [Group T]
    (φ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) : Subgroup T :=
  ((gl12kC3_U K).map (gl12kC3_pi K)).comap φ.toMonoidHom

private lemma gl12kC3_mem_Q (K : Type) [Field K] {T : Type} [Group T]
    (φ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) (x : T) :
    x ∈ gl12kC3_Q K φ ↔ φ x ∈ (gl12kC3_U K).map (gl12kC3_pi K) := Iff.rfl

private theorem gl12kC3_main {K : Type} [Field K] (hchar : ((13 : ℕ) : K) = 0) {T : Type} [Group T]
    (φ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) :
    ∃ Q : Subgroup T, IsPGroup 13 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  have hchar' : (13 : K) = 0 := by exact_mod_cast hchar
  have h78 : (78 : K) = 0 := by
    have h : (78 : K) = 6 * 13 := by norm_num
    rw [h, hchar', mul_zero]
  have hexp : ∀ u ∈ gl12kC3_U K, u ^ 13 = 1 := by
    intro u hu
    obtain ⟨a, b, c, hu⟩ := hu
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hu, gl12kC3_pow, Matrix.SpecialLinearGroup.coe_one,
      gl12kC3_tri_thirteen]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hchar', h78, Matrix.one_apply]
  have hT : ∀ x ∈ gl12kC3_Q K φ, x ^ 13 = 1 := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp ((gl12kC3_mem_Q K φ x).mp hx)
    apply φ.injective
    rw [map_one, map_pow, ← hux, ← map_pow (gl12kC3_pi K) u 13, hexp u hu, map_one]
  have hIsP : IsPGroup 13 (gl12kC3_Q K φ) := by
    intro g
    refine ⟨1, ?_⟩
    show g ^ 13 = 1
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hT g.1 g.2
  refine ⟨gl12kC3_Q K φ, hIsP, φ.symm (gl12kC3_pi K (gl12kC3_x K)), ?_,
    φ.symm (gl12kC3_pi K (gl12kC3_y K)), ?_, ?_⟩
  · rw [gl12kC3_mem_Q K φ, φ.apply_symm_apply]
    exact Subgroup.mem_map.mpr ⟨gl12kC3_x K, gl12kC3_x_mem K, rfl⟩
  · rw [gl12kC3_mem_Q K φ, φ.apply_symm_apply]
    exact Subgroup.mem_map.mpr ⟨gl12kC3_y K, gl12kC3_y_mem K, rfl⟩
  · intro hab
    have h1 := congrArg φ hab
    rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply] at h1
    have h2 : ((gl12kC3_x K * gl12kC3_y K : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) =
        ((gl12kC3_y K * gl12kC3_x K : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact h1
    exact gl12kC3_not_central K (QuotientGroup.eq.mp h2)

theorem exists_nonabelian_pSubgroup_of_A2_13 {q : PrimePower} (hv : (LieTypeIndex.A 2 q).Valid)
    (hq : q.card = 13) {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) :
    ∃ Q : Subgroup T, IsPGroup 13 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : q.p ^ q.exponent = 13 := (PrimePower.card_def q).symm.trans hq
  have hdvd : q.p ∣ 13 := by
    rw [← hcard]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  have hp13 : q.p = 13 := (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).mp hdvd
  have hchar : ((13 : ℕ) : GaloisField q.p q.exponent) = 0 := by
    rw [← hp13]
    exact CharP.cast_eq_zero _ _
  exact gl12kC3_main hchar (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv))

end

section
open TauCeti

theorem exists_two_pow_five_A {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    (hq : q.p ≠ 2) (hr : 6 ≤ r) {T : Type} [Group T]
    (e : T ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    ∃ U : Subgroup T, (∀ x ∈ U, x ^ 2 = 1) ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      Nat.card U = 2 ^ 5 := by
  obtain ⟨U, hU, hcard⟩ := CFSG.RankThree.PartOne.SLB4A.twoPowFive_typeA
    (Or.inr (Or.inr ⟨hq, hr⟩)) e
  refine ⟨U, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,
    fun x hx y hy => ?_, hcard⟩
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)

theorem exists_two_pow_five_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid) (hq : q.p ≠ 2)
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) :
    ∃ U : Subgroup T, (∀ x ∈ U, x ^ 2 = 1) ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      Nat.card U = 2 ^ 5 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.untwistedBridge_E6 q hv hq (GaloisField q.p q.exponent) hK
  obtain ⟨K, _, _, hK', ⟨e'⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup
    CFSG.Blueprint.Chevalley.Tag.E6 (G := ValidLieTypeIndex.Group ⟨LieTypeIndex.E6 q, hv⟩)
    ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hK, ⟨e₁.symm⟩⟩
  have hodd : Nat.card K % 2 = 1 := by
    rw [hK', PrimePower.card_def]
    exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hq).pow)
  obtain ⟨U, hU, hcard⟩ := CFSG.RankThree.PartOne.SLB4A.exists_of_mulEquiv (e.trans e')
    (CFSG.RankThree.PartOne.SLB4A.exists_two_pow_five_adjoint_odd
      (CFSG.RankThree.PartOne.SLB4A.idx5 CFSG.Blueprint.Chevalley.Tag.E6 (by decide))
      (CFSG.RankThree.PartOne.SLB4A.neg_one_ne_one_of_card_odd K hodd)
      CFSG.RankThree.PartOne.SLB4A.hcombE6)
  refine ⟨U, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,
    fun x hx y hy => ?_, hcard⟩
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)

end

theorem surv13_A : ∀ x ∈ survA, 13 ^ 3 ∣ orderA x.1 (x.2.1 ^ x.2.2) →
    x ∈ [(2, 13, 1), (3, 3, 3), (8, 3, 1), (9, 3, 1), (10, 3, 1), (11, 3, 1)] := by
  decide +kernel

theorem surv13_TA : ∀ x ∈ survTA, ¬ 13 ^ 3 ∣ orderTwistedA x.1 (x.2.1 ^ x.2.2) := by
  decide +kernel

theorem surv13_B : ∀ x ∈ survB, ¬ 13 ^ 3 ∣ orderBC x.1 (x.2.1 ^ x.2.2) := by
  decide +kernel

theorem surv13_C : ∀ x ∈ survC, ¬ 13 ^ 3 ∣ orderBC x.1 (x.2.1 ^ x.2.2) := by
  decide +kernel

theorem surv13_D : ∀ x ∈ survD, ¬ 13 ^ 3 ∣ orderD x.1 (x.2.1 ^ x.2.2) := by
  decide +kernel

theorem surv13_TD : ∀ x ∈ survTD, ¬ 13 ^ 3 ∣ orderTwistedD x.1 (x.2.1 ^ x.2.2) := by
  decide +kernel

theorem surv13_F4 : ¬ 13 ^ 3 ∣ orderF4 (3 ^ 1) := by decide +kernel

theorem surv13_G2 : ∀ x ∈ survG2, ¬ 13 ^ 3 ∣ orderG2 (x.1 ^ x.2) := by decide +kernel

theorem surv13_D4t : ∀ x ∈ survD4t, ¬ 13 ^ 3 ∣ orderTrialityD4 (x.1 ^ x.2) := by decide +kernel

theorem surv13_suzuki : ¬ 13 ^ 3 ∣ orderSuzuki (2 ^ (2 * 1 + 1)) := by decide +kernel

theorem surv13_tits : ¬ 13 ^ 3 ∣ orderTits := by decide +kernel

theorem gl12_conj_injective {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center S := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  intro a b hab
  have h1 : ∀ x : S, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun f : MulAut S => f x) hab
    simpa [MulAut.conj_apply] using this
  have hmem : b⁻¹ * a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h2 : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by
      calc (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by group
        _ = b⁻¹ * (b * x * b⁻¹) * b := by rw [h1 x]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rw [hcen, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm


theorem gl12_exists_P0 {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {p : ℕ} (P : Subgroup (MulAut S))
    (hPinn : ∀ x ∈ P, x ∈ (MulAut.conj : S →* MulAut S).range) (hexp : ∀ x ∈ P, x ^ p = 1) :
    ∃ P0 : Subgroup S, (∀ x ∈ P0, x ^ p = 1) ∧ Nat.card P0 = Nat.card P := by
  have hinj := gl12_conj_injective hS hnab
  refine ⟨P.comap (MulAut.conj : S →* MulAut S), ?_, ?_⟩
  · intro x hx
    have hx' : (MulAut.conj : S →* MulAut S) x ∈ P := hx
    have h := hexp _ hx'
    rw [← map_pow] at h
    exact hinj (by rw [h, map_one])
  · have hmap : (P.comap (MulAut.conj : S →* MulAut S)).map (MulAut.conj : S →* MulAut S) = P := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (fun x hx => hPinn x hx)
    calc Nat.card (P.comap (MulAut.conj : S →* MulAut S))
        = Nat.card ((P.comap (MulAut.conj : S →* MulAut S)).map (MulAut.conj : S →* MulAut S)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card P := by rw [hmap]


theorem kF135GL12_of_inputs
    (hOut : KFactOutGL12)
    (hB : LieOrderBridge)
    (hSpor : ∀ (s : SporadicName) {T : Type} [Group T], T ≃* (CFSGIndex.sporadic s).Group →
        Nat.card T = CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder s)
    (hA5 : ∀ {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid), q.p ≠ 2 → 6 ≤ r →
        ∀ {T : Type} [Group T], (T ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) →
          ∃ U : Subgroup T, (∀ x ∈ U, x ^ 2 = 1) ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
            Nat.card U = 2 ^ 5)
    (hE6 : ∀ {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid), q.p ≠ 2 →
        ∀ {T : Type} [Group T], (T ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) →
          ∃ U : Subgroup T, (∀ x ∈ U, x ^ 2 = 1) ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
            Nat.card U = 2 ^ 5)
    (hL4 : ∀ {q : PrimePower} (hv : (LieTypeIndex.A 3 q).Valid), q.card = 27 →
        ∀ {T : Type} [Group T], (T ≃* ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩) →
          ∃ a b z : T, a * b = b * a ∧ orderOf a = 13 ∧ orderOf b = 13 ∧ b ∉ Subgroup.zpowers a ∧
            orderOf z = 2 ∧ a * z = z * a ∧ b * z = z * b)
    (hL3 : ∀ {q : PrimePower} (hv : (LieTypeIndex.A 2 q).Valid), q.card = 13 →
        ∀ {T : Type} [Group T], (T ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) →
          ∃ Q : Subgroup T, IsPGroup 13 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a)
    (hH2 : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
        ∀ {p : ℕ}, p.Prime → ∀ (a b z : S), a * b = b * a → orderOf a = p → orderOf b = p →
          b ∉ Subgroup.zpowers a → orderOf z = 2 → a * z = z * a → b * z = z * b →
          ∃ F : Subgroup (MulAut S), F ≤ (MulAut.conj : S →* MulAut S).range ∧
            CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ 2 ∧
            ∃ T : Subgroup S, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ φ ∈ F, T.map φ.toMonoidHom = T) :
    KF135GL12 := by
  intro S _ _ hK hS hnab hGL p hp hp7 P hP hcard hexp hH2a
  haveI : Fact p.Prime := ⟨hp⟩
  have hPinn : ∀ x ∈ P, x ∈ (MulAut.conj : S →* MulAut S).range := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · exact hOut S hK hS hnab hGL p hp hp7 x (orderOf_eq_prime (hexp x hx) hx1)
  obtain ⟨P0, hP0exp, hP0card⟩ := gl12_exists_P0 hS hnab P hPinn hexp
  have hP0card3 : p ^ 3 ≤ Nat.card P0 := by rw [hP0card]; exact hcard
  have hdivS : Nat.card S ∣ gl12Order := gl12Data_card_dvd hGL
  obtain ⟨n, X, hXg, hXf, ρ, K, hKn, hn, -, -, hker, hodd, ⟨e⟩, hinv⟩ := hGL
  have hle := gl12Sec_card_le hn ρ K hker e hp7 P0 hP0exp
  by_cases h13 : p = 13
  swap
  · exfalso
    have h5 : 5 ≤ orderOf (3 : ZMod p) := (gl12_three_orderOf_facts hp7).1 h13
    have hdiv2 : n / orderOf (3 : ZMod p) ≤ 2 := by
      have := Nat.div_le_div hn h5 (by omega)
      simpa using this
    have h1 : Nat.card P0 ≤ p ^ 2 := hle.trans (Nat.pow_le_pow_right hp.pos hdiv2)
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  subst h13
  have h3 : orderOf (3 : ZMod 13) = 3 := (gl12_three_orderOf_facts hp7).2 rfl
  rw [h3] at hle
  have hn9 : 9 ≤ n := by
    have h1 : 13 ^ 3 ≤ 13 ^ (n / 3) := hP0card3.trans hle
    have h2 : 3 ≤ n / 3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    omega
  have hP0pg : IsPGroup 13 P0 := fun x => ⟨1, Subtype.ext (by simpa using hP0exp x.1 x.2)⟩
  have h13S : 13 ^ 3 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP0pg
    have h1 : 13 ^ 3 ≤ 13 ^ k := hk ▸ hP0card3
    have h2 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    exact ((pow_dvd_pow 13 h2).trans (hk ▸ dvd_refl _)).trans
      (hk ▸ Subgroup.card_subgroup_dvd_card P0)
  haveI := hS
  obtain ⟨i, ⟨e'⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.isCatalogGroup_of_isKGroup_simple hK
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e'.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating m hm =>
    exfalso
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcardS : Nat.card S = m.factorial / 2 := by
      have h1 : Nat.card S = Nat.card (alternatingGroup (Fin m)) := Nat.card_congr e'.toEquiv
      rw [h1, nat_card_alternatingGroup (α := Fin m)]
      simp
    rw [hcardS] at hdivS h13S
    by_cases hm16 : m ≤ 16
    · have key : ∀ m ∈ List.range 17, 2 ≤ m → ¬ 13 ^ 3 ∣ m.factorial / 2 := by decide +kernel
      exact key m (List.mem_range.2 (by omega)) (by omega) h13S
    · have h17 : 17 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h3 : m.factorial = 2 * (m.factorial / 2) := (Nat.mul_div_cancel' h2).symm
      rw [h3] at h17
      have h4 : 17 ∣ m.factorial / 2 :=
        ((Nat.Prime.dvd_mul (by norm_num)).1 h17).resolve_left (by norm_num)
      have h5 : 17 ∣ gl12Order := h4.trans hdivS
      exact absurd h5 (by norm_num [gl12Order])
  | sporadic s =>
    exfalso
    have hcS := hSpor s e'
    rw [hcS] at hdivS h13S
    have key : ∀ s : SporadicName, CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder s ∣ gl12Order →
        ¬ 13 ^ 3 ∣ CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder s := by
      intro s
      cases s <;> decide +kernel
    exact key s hdivS h13S
  | lie d =>
    exfalso
    have hord : Nat.card S = lieOrderFormula d.1 := hB d S ⟨e'⟩
    have hdiv' : lieOrderFormula d.1 ∣ gl12Order := hord ▸ hdivS
    have hs := lie_census d.2 hdiv'
    have h13' : 13 ^ 3 ∣ lieOrderFormula d.1 := hord ▸ h13S
    obtain ⟨d, hv⟩ := d
    cases d with
    | A n q =>
      have hmem : (n, q.p, q.exponent) ∈ survA := hs
      have hord13 : 13 ^ 3 ∣ orderA n (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      have hx := surv13_A _ hmem hord13
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, hp13, hf1⟩ | ⟨rfl, hp3, hf3⟩ | ⟨rfl, hp3, hf1⟩ | ⟨rfl, hp3, hf1⟩ |
          ⟨rfl, hp3, hf1⟩ | ⟨rfl, hp3, hf1⟩
      · have hq13 : q.card = 13 := by rw [PrimePower.card_def, hp13, hf1]; norm_num
        obtain ⟨Q, hQ, a, ha, b, hb, hab⟩ := hL3 hv hq13 e'
        exact hab (gl12Sec_comm hn ρ K hker e hp7 Q hQ a ha b hb)
      · have hq27 : q.card = 27 := by rw [PrimePower.card_def, hp3, hf3]; norm_num
        obtain ⟨a, b, z, hab, ha, hb, hba, hz, haz, hbz⟩ := hL4 hv hq27 e'
        obtain ⟨F, hF1, hF2, hF3, T, hT1, hT2, hT3⟩ := hH2 hS hnab hp a b z hab ha hb hba hz haz hbz
        obtain ⟨φ, hφF, hφ⟩ := hH2a F hF1 hF2 hF3 T hT1 hT2
        exact hφ (hT3 φ hφF)
      all_goals
        obtain ⟨U, hU2, hUc, hUcard⟩ := hA5 hv (by omega) (by omega) e'
        have := gl12_n_le_eight_of_elemAbelian_two ρ K hodd e hinv U hU2 hUc hUcard
        omega
    | twistedA n q =>
      have hmem : (n, q.p, q.exponent) ∈ survTA := hs
      have hord13 : 13 ^ 3 ∣ orderTwistedA n (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_TA _ hmem hord13
    | B n q =>
      have hmem : (n, q.p, q.exponent) ∈ survB := hs
      have hord13 : 13 ^ 3 ∣ orderBC n (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_B _ hmem hord13
    | C n q =>
      have hmem : (n, q.p, q.exponent) ∈ survC := hs
      have hord13 : 13 ^ 3 ∣ orderBC n (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_C _ hmem hord13
    | D n q =>
      have hmem : (n, q.p, q.exponent) ∈ survD := hs
      have hord13 : 13 ^ 3 ∣ orderD n (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_D _ hmem hord13
    | twistedD n q =>
      have hmem : (n, q.p, q.exponent) ∈ survTD := hs
      have hord13 : 13 ^ 3 ∣ orderTwistedD n (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_TD _ hmem hord13
    | E6 q =>
      have hs' : (q.p, q.exponent) = (3, 1) := hs
      obtain ⟨hp3, hf1⟩ := Prod.mk.inj hs'
      obtain ⟨U, hU2, hUc, hUcard⟩ := hE6 hv (by omega) e'
      have := gl12_n_le_eight_of_elemAbelian_two ρ K hodd e hinv U hU2 hUc hUcard
      omega
    | E7 q => exact False.elim hs
    | E8 q => exact False.elim hs
    | F4 q =>
      have hs' : (q.p, q.exponent) = (3, 1) := hs
      obtain ⟨hp3, hf1⟩ := Prod.mk.inj hs'
      apply surv13_F4
      simpa [lieOrderFormula, PrimePower.card_def, hp3, hf1] using h13'
    | G2 q =>
      have hmem : (q.p, q.exponent) ∈ survG2 := hs
      have hord13 : 13 ^ 3 ∣ orderG2 (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_G2 _ hmem hord13
    | twistedE6 q => exact False.elim hs
    | trialityD4 q =>
      have hmem : (q.p, q.exponent) ∈ survD4t := hs
      have hord13 : 13 ^ 3 ∣ orderTrialityD4 (q.p ^ q.exponent) := by
        simpa [lieOrderFormula, PrimePower.card_def] using h13'
      exact surv13_D4t _ hmem hord13
    | suzuki m =>
      have hm1 : m = 1 := hs
      subst hm1
      exact surv13_suzuki (by simpa [lieOrderFormula] using h13')
    | reeG2 m => exact False.elim hs
    | reeF4 m => exact False.elim hs
    | tits =>
      exact surv13_tits (by simpa [lieOrderFormula] using h13')

theorem gl12_card_sporadic
    (s : SporadicName) {T : Type} [Group T]
    (e : T ≃* (CFSGIndex.sporadic s).Group) :
    Nat.card T = CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder s := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr b.toEquiv,
    CFSG.ComponentClassification.CatFC.card_carrier_eq_sporOrder_all s]

theorem kF135GL12_holds :
    KF135GL12 :=
  kF135GL12_of_inputs kFactOutGL12_holds lieOrderBridge_holds
    (fun s {T} [Group T] e => gl12_card_sporadic s e) exists_two_pow_five_A
    (fun {q} hv hq {T} [Group T] e => exists_two_pow_five_E6 (q := q) hv hq e)
    exists_E_p2_of_A3_27 exists_nonabelian_pSubgroup_of_A2_13 not_h2a_of_E_p2

end CFSG.RankThree.PartTwo.Sec13.K135GL12
