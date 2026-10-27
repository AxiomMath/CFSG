module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeFaithful

open CFSG.RankThree.PartTwo.KFacts.KS116Proof (toProjSL)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

section Center

variable {F : Type} [Field F]

theorem eq_scalar_of_toProjSL_eq_one {A : SL(2, F)} (h : toProjSL F A = 1) :
    ∃ r : F, r ^ 2 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) F) = r • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h1 : A ∈ (Matrix.SpecialLinearGroup.toPGL :
      SL(2, F) →* Matrix.ProjGenLinGroup (Fin 2) F).ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val h
  rw [Matrix.SpecialLinearGroup.toPGL_ker, Matrix.SpecialLinearGroup.mem_center_iff] at h1
  obtain ⟨r, hr, hA⟩ := h1
  refine ⟨r, by simpa using hr, ?_⟩
  rw [← hA, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem toProjSL_eq_one_of_scalar {A : SL(2, F)} {r : F} (hr : r ^ 2 = 1)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = r • (1 : Matrix (Fin 2) (Fin 2) F)) :
    toProjSL F A = 1 := by
  have h1 : A ∈ Subgroup.center SL(2, F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨r, by simpa using hr, ?_⟩
    rw [hA, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker] at h1
  exact Subtype.ext h1

theorem toProjSL_eq_of_matrix_smul {X Y : SL(2, F)} {r : F} (hr : r ^ 2 = 1)
    (h : (X : Matrix (Fin 2) (Fin 2) F) = r • (Y : Matrix (Fin 2) (Fin 2) F)) :
    toProjSL F X = toProjSL F Y := by
  have h1 : toProjSL F (Y⁻¹ * X) = 1 := by
    refine toProjSL_eq_one_of_scalar hr ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

end Center

section Klein

variable {F : Type} [Field F]

theorem exists_klein (h2 : (2 : F) ≠ 0) (hxy : ∃ x y : F, x ^ 2 + y ^ 2 = -1) :
    ∃ a b : projSL 2 F, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 := by
  obtain ⟨x, y, hxy⟩ := hxy
  let a₀ : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
  let b₀ : SL(2, F) := ⟨!![x, y; y, -x], by rw [Matrix.det_fin_two_of]; linear_combination -hxy⟩
  have hab : ((a₀ * b₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![y, -x; -x, -y] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![x, y; y, -x] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hba : ((b₀ * a₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![-y, x; x, y] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change (!![x, y; y, -x] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have haa : ((a₀ * a₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hbb : ((b₀ * b₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change (!![x, y; y, -x] : Matrix (Fin 2) (Fin 2) F) * !![x, y; y, -x] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination hxy
  refine ⟨toProjSL F a₀, toProjSL F b₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul]
    exact toProjSL_eq_one_of_scalar (by norm_num) haa
  · rw [← map_mul]
    exact toProjSL_eq_one_of_scalar (by norm_num) hbb
  · rw [← map_mul, ← map_mul]
    refine toProjSL_eq_of_matrix_smul (r := -1) (by norm_num) ?_
    rw [hab, hba]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro h
    obtain ⟨r, -, hr⟩ := eq_scalar_of_toProjSL_eq_one h
    have h01 := congrFun (congrFun hr 0) 1
    simp [a₀] at h01
  · intro h
    obtain ⟨r, -, hr⟩ := eq_scalar_of_toProjSL_eq_one h
    have h01 := congrFun (congrFun hr 0) 1
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp [b₀] at h01 h00 h11
    have hx : x = 0 := by
      have h' : 2 * x = 0 := by linear_combination h00 - h11
      exact (mul_eq_zero.mp h').resolve_left h2
    rw [hx, h01] at hxy
    norm_num at hxy
  · rw [← map_mul]
    intro h
    obtain ⟨r, -, hr⟩ := eq_scalar_of_toProjSL_eq_one h
    rw [hab] at hr
    have h01 := congrFun (congrFun hr 0) 1
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp at h01 h00 h11
    have hy : y = 0 := by
      have h' : 2 * y = 0 := by linear_combination h00 - h11
      exact (mul_eq_zero.mp h').resolve_left h2
    rw [hy, h01] at hxy
    norm_num at hxy

end Klein

section Consequence

variable {G : Type*} [Group G] {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_involution_of_klein {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a * b ≠ 1)
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (ρ : G →* Module.End K V)
    (h7 : 7 ≤ Module.finrank K V) :
    ∃ t : G, orderOf t = 2 ∧ 3 ≤ Module.finrank K (LinearMap.ker (ρ t - 1)) := by
  have hrank := LSSolvableProof.finrank_le_add_ker h2 (a := ρ a) (b := ρ b)
    (by rw [← map_mul, ha, map_one]) (by rw [← map_mul, hb, map_one])
    (by rw [← map_mul, ← map_mul, hab])
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  rw [← map_mul] at hrank
  by_contra hcon
  push Not at hcon
  have h1 := hcon a (orderOf_eq_prime (by rw [pow_two]; exact ha) ha1)
  have h2' := hcon b (orderOf_eq_prime (by rw [pow_two]; exact hb) hb1)
  have h3 := hcon (a * b) (orderOf_eq_prime (by rw [pow_two]; exact hab2) hab1)
  omega

end Consequence

section Dihedral

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ker_sub_one_sup_ker_add_one (h2 : (2 : K) ≠ 0) {S : Module.End K V} (hS : S * S = 1) :
    LinearMap.ker (S - 1) ⊔ LinearMap.ker (S + 1) = ⊤ := by
  have hSS : ∀ v, S (S v) = v := fun v => by
    rw [← Module.End.mul_apply, hS, Module.End.one_apply]
  rw [eq_top_iff]
  intro v _
  have h1 : v + S v ∈ LinearMap.ker (S - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_add, hSS]
    abel
  have h3 : v - S v ∈ LinearMap.ker (S + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_sub, hSS]
    abel
  have hv : v = (2 : K)⁻¹ • (v + S v) + (2 : K)⁻¹ • (v - S v) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hv]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ h1))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ h3))

theorem finrank_le_two_mul_ker_add [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {ℓ : ℕ}
    (hℓ : Odd ℓ) {B S : Module.End K V} (hB : B ^ ℓ = 1) (hS : S * S = 1)
    (hBS : B * S * B = S) :
    Module.finrank K V ≤ 2 * Module.finrank K (LinearMap.ker (S - 1)) +
      Module.finrank K (LinearMap.ker (B - 1)) := by
  obtain ⟨m, rfl⟩ := hℓ
  set Bi : Module.End K V := B ^ (2 * m) with hBi
  have hBBi : B * Bi = 1 := by rw [hBi, ← pow_succ']; exact hB
  have hBiB : Bi * B = 1 := by rw [hBi, ← pow_succ]; exact hB
  have hSB : S * B = Bi * S := by
    calc S * B = (Bi * B) * (S * B) := by rw [hBiB, one_mul]
      _ = Bi * (B * S * B) := by simp only [mul_assoc]
      _ = Bi * S := by rw [hBS]
  have hB' : B = S * Bi * S := by
    calc B = (S * S) * B := by rw [hS, one_mul]
      _ = S * (S * B) := by simp only [mul_assoc]
      _ = S * (Bi * S) := by rw [hSB]
      _ = S * Bi * S := by simp only [mul_assoc]
  have hSBi : S * Bi = B * S := by
    calc S * Bi = S * Bi * (S * S) := by rw [hS, mul_one]
      _ = (S * Bi * S) * S := by simp only [mul_assoc]
      _ = B * S := by rw [← hB']
  set ψ : Module.End K V := B - Bi with hψ
  have hψS : S * ψ = -(ψ * S) := by
    rw [hψ, mul_sub, sub_mul, hSB, hSBi, neg_sub]
  have hker : ∀ v, ψ v = 0 → (B - 1) v = 0 := by
    intro v hv
    have hBv : B v = Bi v := by
      rw [hψ, LinearMap.sub_apply, sub_eq_zero] at hv
      exact hv
    have hB2 : (B * B) v = v := by
      rw [Module.End.mul_apply, hBv, ← Module.End.mul_apply, hBBi, Module.End.one_apply]
    have hpow : ∀ k : ℕ, ((B * B) ^ k) v = v := by
      intro k
      induction k with
      | zero => rw [pow_zero, Module.End.one_apply]
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hB2, ih]
    have hBe : B = (B * B) ^ (m + 1) := by
      calc B = B ^ (2 * m + 1) * B := by rw [hB, one_mul]
        _ = B ^ (2 * m + 1 + 1) := (pow_succ B (2 * m + 1)).symm
        _ = (B * B) ^ (m + 1) := by
          rw [← sq, ← pow_mul]
          exact congrArg (B ^ ·) (by ring)
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    conv_lhs => rw [hBe]
    exact hpow _
  set Vp := LinearMap.ker (S - 1) with hVp
  set Vm := LinearMap.ker (S + 1) with hVm
  have hSm : ∀ v ∈ Vm, S v = -v := by
    intro v hv
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hv
    exact eq_neg_of_add_eq_zero_left hv
  set φ : ↥Vm →ₗ[K] V := ψ.comp Vm.subtype with hφ
  have hrange : LinearMap.range φ ≤ Vp := by
    rintro _ ⟨⟨v, hv⟩, rfl⟩
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    change S (ψ v) = ψ v
    have h1 : S (ψ v) = -(ψ (S v)) := by
      have := LinearMap.congr_fun hψS v
      rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply] at this
      exact this
    rw [h1, hSm v hv, map_neg, neg_neg]
  have hkerle : Submodule.map Vm.subtype (LinearMap.ker φ) ≤ LinearMap.ker (B - 1) := by
    rintro _ ⟨⟨v, hv⟩, hφv, rfl⟩
    rw [LinearMap.mem_ker]
    exact hker v hφv
  have h1 : Module.finrank K ↥(LinearMap.range φ) + Module.finrank K ↥(LinearMap.ker φ) =
      Module.finrank K ↥Vm := LinearMap.finrank_range_add_finrank_ker φ
  have h2' : Module.finrank K ↥(LinearMap.range φ) ≤ Module.finrank K ↥Vp :=
    Submodule.finrank_mono hrange
  have h3 : Module.finrank K ↥(LinearMap.ker φ) ≤ Module.finrank K ↥(LinearMap.ker (B - 1)) := by
    rw [← Submodule.finrank_map_subtype_eq Vm (LinearMap.ker φ)]
    exact Submodule.finrank_mono hkerle
  have h4 : Module.finrank K V ≤ Module.finrank K ↥Vp + Module.finrank K ↥Vm := by
    calc Module.finrank K V = Module.finrank K ↥(⊤ : Submodule K V) := (finrank_top K V).symm
      _ = Module.finrank K ↥(Vp ⊔ Vm) := by rw [ker_sub_one_sup_ker_add_one h2 hS]
      _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
  omega

end Dihedral

section Counting

theorem six_add_finrank_ker_le {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hppd : ∀ j : ℕ, ℓ ∣ p ^ j - 1 ↔ 6 ∣ j) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {B : Module.End (ZMod p) V} (hB : B ^ ℓ = 1) (hB1 : B ≠ 1) :
    6 + Module.finrank (ZMod p) (LinearMap.ker (B - 1)) ≤ Module.finrank (ZMod p) V := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Fintype V := Fintype.ofFinite V
  set f : Function.End V := (B : V → V) with hf
  have hfℓ : f ^ ℓ ^ 1 = 1 := by
    funext v
    rw [pow_one]
    have h := LinearMap.congr_fun hB v
    rw [Module.End.pow_apply, Module.End.one_apply] at h
    exact h
  have hmod := Equiv.Perm.card_fixedPoints_modEq hfℓ
  have hfix : Function.fixedPoints f = (LinearMap.ker (B - 1) : Set V) := by
    ext v
    rw [Function.mem_fixedPoints_iff, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  have hcardV : Fintype.card V = p ^ Module.finrank (ZMod p) V := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hcardK : Fintype.card ↑(Function.fixedPoints f) =
      p ^ Module.finrank (ZMod p) (LinearMap.ker (B - 1)) := by
    rw [← Nat.card_eq_fintype_card, hfix]
    exact (Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(LinearMap.ker (B - 1)))).trans
      (by rw [Nat.card_zmod])
  rw [hcardV, hcardK] at hmod
  set n := Module.finrank (ZMod p) V with hn
  set c := Module.finrank (ZMod p) (LinearMap.ker (B - 1)) with hc
  have hcn : c ≤ n := Submodule.finrank_le _
  obtain ⟨d, hd⟩ : ∃ d, n = c + d := ⟨n - c, by omega⟩
  have hcop : Nat.gcd ℓ (p ^ c) = 1 :=
    Nat.Coprime.pow_right c ((Nat.coprime_primes Fact.out Fact.out).mpr hℓp)
  have hmod' : p ^ d ≡ 1 [MOD ℓ] := by
    refine Nat.ModEq.cancel_left_of_coprime hcop ?_
    rw [← pow_add, mul_one, ← hd]
    exact hmod
  have hdvd : ℓ ∣ p ^ d - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).mp hmod'.symm
  have h6 : 6 ∣ d := (hppd d).mp hdvd
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hB1
    have htop : LinearMap.ker (B - 1) = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    rw [LinearMap.ker_eq_top, sub_eq_zero] at htop
    exact htop
  have : 6 ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h6
  omega

end Counting

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeFaithful
