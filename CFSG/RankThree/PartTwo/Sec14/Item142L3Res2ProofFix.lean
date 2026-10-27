module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofTorus

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC hS)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {K : Type} [Field K]

theorem sq_add_self_add_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ ^ 2 + τ + 1 = 0 := by
  have h1 : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hτ1)

theorem exists_pow_eq_of_cube {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ε : K}
    (hε : ε ^ 3 = 1) : ∃ i : ℕ, ε = τ ^ i := by
  have hω := sq_add_self_add_one hτ hτ1
  have h : (ε - 1) * (ε - τ) * (ε - τ ^ 2) = 0 := by
    linear_combination hε + (ε - ε ^ 2) * hω + (ε - 1) * hτ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by rw [pow_zero]; exact sub_eq_zero.mp h⟩
    · exact ⟨1, by rw [pow_one]; exact sub_eq_zero.mp h⟩
  · exact ⟨2, sub_eq_zero.mp h⟩

theorem pow_eq_pow_of_mod {τ : K} (hτ : τ ^ 3 = 1) {a b : ℕ} (h : a % 3 = b % 3) :
    τ ^ a = τ ^ b := by
  rw [pow_eq_pow_mod a hτ, pow_eq_pow_mod b hτ, h]

theorem mul_pow_eq_smul {g L : Matrix (Fin 3) (Fin 3) K} {c : K} (h : g * L = c • (L * g))
    (n : ℕ) : g * L ^ n = c ^ n • (L ^ n * g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g * L ^ (n + 1) = (g * L ^ n) * L := by rw [pow_succ, Matrix.mul_assoc]
      _ = c ^ n • (L ^ n * (g * L)) := by rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
      _ = c ^ (n + 1) • (L ^ (n + 1) * g) := by
          rw [h, Matrix.mul_smul, smul_smul, ← pow_succ, ← Matrix.mul_assoc, ← pow_succ]

theorem pow_mul_eq_smul {g L : Matrix (Fin 3) (Fin 3) K} {c : K} (h : g * L = c • (L * g))
    (n : ℕ) : g ^ n * L = c ^ n • (L * g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * L = g * (g ^ n * L) := by rw [pow_succ', Matrix.mul_assoc]
      _ = c ^ n • ((g * L) * g ^ n) := by rw [ih, Matrix.mul_smul, Matrix.mul_assoc]
      _ = c ^ (n + 1) • (L * g ^ (n + 1)) := by
          rw [h, Matrix.smul_mul, smul_smul, ← pow_succ, Matrix.mul_assoc, ← pow_succ']

theorem pow_three_eq_one_of_mul_eq {g L : Matrix (Fin 3) (Fin 3) K} {c β : K} (hg : g ≠ 0)
    (hβ : β ≠ 0) (hL3 : L ^ 3 = β • 1) (h : g * L = c • (L * g)) : c ^ 3 = 1 := by
  have h3 := mul_pow_eq_smul h 3
  rw [hL3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h3
  have h0 : (β - c ^ 3 * β) • g = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.mp h0 with h0 | h0
  · have : (1 - c ^ 3) * β = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h1 | h1
    · linear_combination -h1
    · exact absurd h1 hβ
  · exact absurd h0 hg

theorem coe_ne_zero (g : GL (Fin 3) K) : (g : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
  intro h
  have := congrArg Matrix.det h
  rw [Matrix.det_zero] at this
  exact (g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero this

variable {p f : ℕ}

theorem projOf_mem_of_fix_line {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hd : diagTau hτ ∈ slPi false 3 (p ^ f) K)
    {N : Subgroup (projImage (slPi false 3 (p ^ f) K))} {L : GL (Fin 3) K} {β : K} (hβ : β ≠ 0)
    (hL3 : (L : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1)
    (hdL : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L =
      τ • ((L : Matrix (Fin 3) (Fin 3) K) * (diagTau hτ : GL (Fin 3) K)))
    (hT : (torusU false p f K L).map (projOf (slPi false 3 (p ^ f) K)) ≤ N)
    {g : slPi false 3 (p ^ f) K} {c : K}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L =
      c • ((L : Matrix (Fin 3) (Fin 3) K) * (g : GL (Fin 3) K))) :
    projOf (slPi false 3 (p ^ f) K) g ∈
      N ⊔ Subgroup.zpowers (projOf (slPi false 3 (p ^ f) K) ⟨diagTau hτ, hd⟩) := by
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  set D : slPi false 3 (p ^ f) K := ⟨diagTau hτ, hd⟩ with hD
  have hc3 := pow_three_eq_one_of_mul_eq (coe_ne_zero _) hβ hL3 hg
  obtain ⟨i, rfl⟩ := exists_pow_eq_of_cube hτ hτ1 hc3
  set t : slPi false 3 (p ^ f) K := D ^ (2 * i) * g with ht
  have htL : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L =
      (L : Matrix (Fin 3) (Fin 3) K) * (t : GL (Fin 3) K) := by
    have hdn := pow_mul_eq_smul hdL (2 * i)
    have hcoe : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ (2 * i) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [ht, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [hcoe, Matrix.mul_assoc, hg, Matrix.mul_smul, ← Matrix.mul_assoc, hdn, Matrix.smul_mul,
      smul_smul, ← pow_add, pow_eq_pow_of_mod hτ (show (i + 2 * i) % 3 = 0 % 3 by omega),
      pow_zero, one_smul, Matrix.mul_assoc]
  have htT : t ∈ torusU false p f K L := by
    rw [mem_torusU]
    exact Units.ext htL.symm
  have hρt : ρ t ∈ N := hT ⟨t, htT, rfl⟩
  have hgt : g = D ^ (-(2 * (i : ℤ))) * t := by
    rw [ht, ← mul_assoc, ← zpow_natCast, ← _root_.zpow_add]
    push_cast
    rw [neg_add_cancel, zpow_zero, one_mul]
  rw [hgt, map_mul, map_zpow]
  have hmem := Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers (ρ D) (-(2 * (i : ℤ)))) hρt
  rwa [sup_comm] at hmem


theorem hS_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    (hS : Matrix (Fin 3) (Fin 3) K) * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ ^ 2 • (((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * hS) := by
  rw [coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hS, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-1 : K) * hτ | linear_combination (-τ) * hτ

theorem torusHom_tau_pow {τ : K} (hτ : τ ^ 3 = 1) {τu : Kˣ} (hτu : (τu : K) = τ) (i j : ℕ) :
    torusHom (τu ^ i, τu ^ j) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (τu ^ (2 * i + 2 * j)) *
        diagTau hτ ^ (2 * i + j) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val (diagTau hτ), coe_torusHom,
    Matrix.GeneralLinearGroup.coe_scalar, coe_diagTau_eq_diagonal, diagonal_pow,
    Matrix.scalar_apply, diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k
  · change ((τu ^ i : Kˣ) : K) = ((τu ^ (2 * i + 2 * j) : Kˣ) : K) * τ ^ (2 * i + j)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hτu, ← pow_add]
    exact pow_eq_pow_of_mod hτ (by omega)
  · change ((τu ^ j : Kˣ) : K) = ((τu ^ (2 * i + 2 * j) : Kˣ) : K) * (τ ^ 2) ^ (2 * i + j)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hτu, ← pow_mul, ← pow_add]
    exact pow_eq_pow_of_mod hτ (by omega)
  · change (((τu ^ i * τu ^ j)⁻¹ : Kˣ) : K) = ((τu ^ (2 * i + 2 * j) : Kˣ) : K) * 1 ^ (2 * i + j)
    rw [one_pow, mul_one, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hτu]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, ← pow_add]
    rw [pow_eq_pow_of_mod hτ (show (i + j + (2 * i + 2 * j)) % 3 = 0 % 3 by omega), pow_zero]

theorem projOf_mem_of_fix_d (hK : PiField false p f K) (hq : ModThree false (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hd : diagTau hτ ∈ slPi false 3 (p ^ f) K)
    {s : slPi false 3 (p ^ f) K} (hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS)
    (hm : p ^ f + 1 = 3 * mU (p ^ f))
    {N : Subgroup (projImage (slPi false 3 (p ^ f) K))}
    (hD : (diagMuU p f K).map (projOf (slPi false 3 (p ^ f) K)) ≤ N)
    {g : slPi false 3 (p ^ f) K} {c : K}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (diagTau hτ : GL (Fin 3) K) =
      c • (((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : GL (Fin 3) K))) :
    projOf (slPi false 3 (p ^ f) K) g ∈
      N ⊔ (Subgroup.zpowers (projOf (slPi false 3 (p ^ f) K) ⟨diagTau hτ, hd⟩) ⊔
        Subgroup.zpowers (projOf (slPi false 3 (p ^ f) K) s)) := by
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  set D : slPi false 3 (p ^ f) K := ⟨diagTau hτ, hd⟩ with hDdef
  set A := Subgroup.zpowers (ρ D) with hA
  set B := Subgroup.zpowers (ρ s) with hB
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu' : (τu : K) = τ := rfl
  have hd3 : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (1 : K) • 1 := by
    rw [one_smul, ← Units.val_pow_eq_pow_val]
    have : diagTau hτ ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, diagonal_pow, Units.val_one,
        ← diagonal_one]
      have h2 : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
      congr 1
      funext k
      fin_cases k <;> simp [hτ, h2]
    rw [this, Units.val_one]
  have hc3 := pow_three_eq_one_of_mul_eq (coe_ne_zero _) one_ne_zero hd3 hg
  obtain ⟨i, rfl⟩ := exists_pow_eq_of_cube hτ hτ1 hc3
  set t : slPi false 3 (p ^ f) K := s ^ i * g with ht
  have hSn := pow_mul_eq_smul (hS_mul_diagTau hτ) i
  have htd : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (diagTau hτ : GL (Fin 3) K) =
      ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (t : GL (Fin 3) K) := by
    have hcoe : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (hS : Matrix (Fin 3) (Fin 3) K) ^ i * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [ht, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hs]
    rw [hcoe, Matrix.mul_assoc, hg, Matrix.mul_smul, ← Matrix.mul_assoc, hSn, Matrix.smul_mul,
      smul_smul, ← pow_mul, ← pow_add,
      pow_eq_pow_of_mod hτ (show (i + 2 * i) % 3 = 0 % 3 by omega), pow_zero, one_smul,
      Matrix.mul_assoc]
  have htC : (t : GL (Fin 3) K) ∈ slPi false 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} := by
    refine Subgroup.mem_inf.mpr ⟨t.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Units.ext htd
  rw [centralizer_diagTau_eq hK hq hτ hτ1] at htC
  obtain ⟨⟨a, b⟩, hab⟩ := htC
  have ha : (a : Kˣ) ^ (p ^ f + 1) = 1 := (mem_rootsOfUnity _ _).mp a.2
  have hb : (b : Kˣ) ^ (p ^ f + 1) = 1 := (mem_rootsOfUnity _ _).mp b.2
  have htab : (t : GL (Fin 3) K) = torusHom ((a : Kˣ), (b : Kˣ)) := hab.symm
  obtain ⟨u, v, huv⟩ : IsCoprime ((3 : ℕ) : ℤ) (mU (p ^ f) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (coprime_mU (p ^ f)).symm
  have hzpow : ∀ (x : Kˣ) (z : ℤ), x ^ (p ^ f + 1) = 1 → x ^ (z * 3 * mU (p ^ f)) = 1 := by
    intro x z hx
    rw [show z * 3 * (mU (p ^ f) : ℤ) = ((p ^ f + 1 : ℕ) : ℤ) * z by
      rw [hm]; push_cast; ring, _root_.zpow_mul, zpow_natCast, hx, _root_.one_zpow]
  have htz : ∀ z : ℤ, ((t ^ z : slPi false 3 (p ^ f) K) : GL (Fin 3) K) =
      torusHom ((a : Kˣ) ^ z, (b : Kˣ) ^ z) := by
    intro z
    rw [Subgroup.coe_zpow, htab, ← map_zpow, Prod.pow_mk]
  have h1 : ρ (t ^ (u * 3)) ∈ N := by
    refine hD ⟨t ^ (u * 3), mem_diagMuU.mpr ⟨(a : Kˣ) ^ (u * 3), (b : Kˣ) ^ (u * 3), ?_, ?_,
      htz _⟩, rfl⟩
    · rw [mem_rootsOfUnity, ← zpow_natCast, ← _root_.zpow_mul]
      exact hzpow _ u ha
    · rw [mem_rootsOfUnity, ← zpow_natCast, ← _root_.zpow_mul]
      exact hzpow _ u hb
  have h2 : ρ (t ^ (v * mU (p ^ f))) ∈ A := by
    have hcube : ∀ x : Kˣ, x ^ (p ^ f + 1) = 1 → ∃ k : ℕ, x ^ (v * mU (p ^ f)) = τu ^ k := by
      intro x hx
      have hx3 : ((x ^ (v * mU (p ^ f)) : Kˣ) : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul,
          show v * (mU (p ^ f) : ℤ) * ((3 : ℕ) : ℤ) = v * 3 * mU (p ^ f) by push_cast; ring,
          hzpow x v hx, Units.val_one]
      obtain ⟨k, hk⟩ := exists_pow_eq_of_cube hτ hτ1 hx3
      exact ⟨k, Units.ext (by rw [hk, Units.val_pow_eq_pow_val, hτu'])⟩
    obtain ⟨k₁, hk₁⟩ := hcube _ ha
    obtain ⟨k₂, hk₂⟩ := hcube _ hb
    have he : ρ (t ^ (v * mU (p ^ f))) = ρ D ^ (2 * k₁ + k₂) := by
      apply Subtype.ext
      rw [coe_projOf, htz, hk₁, hk₂, torusHom_tau_pow hτ hτu', map_mul,
        mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul, map_pow, Subgroup.coe_pow,
        coe_projOf]
    rw [he]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hsplit : t = t ^ (u * 3) * t ^ (v * mU (p ^ f)) := by
    rw [← _root_.zpow_add]
    push_cast at huv
    rw [huv, zpow_one]
  have hgt : g = s ^ (-(i : ℤ)) * (t ^ (u * 3) * t ^ (v * mU (p ^ f))) := by
    rw [← hsplit, ht, ← mul_assoc, ← zpow_natCast, ← _root_.zpow_add, neg_add_cancel, zpow_zero,
      one_mul]
  rw [hgt, map_mul, map_mul, map_zpow]
  refine Subgroup.mul_mem _ ?_ (Subgroup.mul_mem _ ?_ ?_)
  · exact (le_sup_right.trans le_sup_right : B ≤ N ⊔ (A ⊔ B)) (Subgroup.zpow_mem_zpowers _ _)
  · exact (le_sup_left : N ≤ N ⊔ (A ⊔ B)) h1
  · exact (le_sup_left.trans le_sup_right : A ≤ N ⊔ (A ⊔ B)) h2

end CFSG.RankThree.PartTwo.Sec14.L3PGLU
