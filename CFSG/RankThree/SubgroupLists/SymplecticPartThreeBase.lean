module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerPair
public import CFSG.RankThree.SubgroupLists.SymplecticSqZero

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem eq_or_eq_neg_of_cliffB_eq_one (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G) {d e : GL V₄ K}
    (hdG : d ∈ G) (heG : e ∈ G) (hd : IsNCInv d) (he : IsNCInv e)
    (hB : cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) = 1 ∨
      cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) = -1) :
    e = d ∨ e = -d := by
  have hdM := (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
  have heM := (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
  have hdd : (d : Matrix V₄ V₄ K) * d = 1 := by rw [← Units.val_mul, hd.2.1, Units.val_one]
  have hee : (e : Matrix V₄ V₄ K) * e = 1 := by rw [← Units.val_mul, he.2.1, Units.val_one]
  have hsq := mul_sq_of_involutions h2 hdM heM hdd hee
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd.2.1
  rcases hB with h | h
  ·
    have hsz : IsSqZero (d * e) := by
      rw [IsSqZero, Units.val_mul]
      have : ((d : Matrix V₄ V₄ K) * e - 1) * ((d : Matrix V₄ V₄ K) * e - 1) =
          (d : Matrix V₄ V₄ K) * e * ((d : Matrix V₄ V₄ K) * e) -
            (2 : K) • ((d : Matrix V₄ V₄ K) * e) + 1 := by
        rw [two_smul]; noncomm_ring
      rw [this, hsq, h, mul_one]
      abel
    have h1 := hU0 _ (G.mul_mem hdG heG) hsz
    left
    calc e = d⁻¹ * (d * e) := by group
      _ = d := by rw [h1, mul_one, hdinv]
  ·
    have hsz : IsSqZero (-(d * e)) := by
      rw [IsSqZero, Units.val_neg, Units.val_mul]
      have : (-((d : Matrix V₄ V₄ K) * e) - 1) * (-((d : Matrix V₄ V₄ K) * e) - 1) =
          (d : Matrix V₄ V₄ K) * e * ((d : Matrix V₄ V₄ K) * e) +
            (2 : K) • ((d : Matrix V₄ V₄ K) * e) + 1 := by
        rw [two_smul]; noncomm_ring
      rw [this, hsq, h]
      simp only [mul_neg, mul_one, neg_smul]
      abel
    have hm : -(d * e) ∈ G := by
      rw [show -(d * e) = -1 * (d * e) by simp]
      exact G.mul_mem hneg (G.mul_mem hdG heG)
    have h1 := hU0 _ hm hsz
    right
    have hde : d * e = -1 := by rw [← neg_neg (d * e), h1]
    calc e = d⁻¹ * (d * e) := by group
      _ = -d := by rw [hde, mul_neg_one, hdinv]

theorem mul_self_eq_zero_of_isNilpotent_of_commute (h2 : (2 : K) ≠ 0) {u : GL V₄ K}
    (hu : IsNCInv u) {N : Matrix V₄ V₄ K} (hN : IsNilpotent N)
    (hNu : N * (u : Matrix V₄ V₄ K) = (u : Matrix V₄ V₄ K) * N) : N * N = 0 := by
  classical
  have huu : (u : Matrix V₄ V₄ K) * u = 1 := by rw [← Units.val_mul, hu.2.1, Units.val_one]
  have hm2 := finrank_eig_neg_one_eq_two h2 hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
  have hp2 : finrank K (eigSp (u : Matrix V₄ V₄ K) 1) = 2 := by
    have := finrank_eig_add_finrank_eig h2 huu
    omega
  have key : ∀ μ : K, finrank K (eigSp (u : Matrix V₄ V₄ K) μ) = 2 →
      ∀ v ∈ eigSp (u : Matrix V₄ V₄ K) μ, N *ᵥ (N *ᵥ v) = 0 := by
    intro μ hμ v hv
    set E := eigSp (u : Matrix V₄ V₄ K) μ with hE
    have hpres : ∀ w ∈ E, Matrix.toLin' N w ∈ E := by
      intro w hw
      rw [hE, mem_eigSp] at hw ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hNu, ← Matrix.mulVec_mulVec, hw,
        Matrix.mulVec_smul]
    set φ : Module.End K E := (Matrix.toLin' N).restrict hpres with hφ
    have hφnil : IsNilpotent φ := by
      refine Module.End.isNilpotent.restrict hpres ?_
      simpa using hN
    have hchar := hφnil.charpoly_eq_X_pow_finrank
    rw [hμ] at hchar
    have hcay := LinearMap.aeval_self_charpoly φ
    rw [hchar] at hcay
    simp only [map_pow, Polynomial.aeval_X] at hcay
    have := congrArg (fun f : Module.End K E => ((f ⟨v, hv⟩ : E) : V₄ → K)) hcay
    simp only [pow_two, Module.End.mul_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] at this
    rw [hφ] at this
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  obtain ⟨h₁, h₂, hv⟩ := mem_eig_add_mem_eig h2 huu v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_add, Matrix.mulVec_add, key 1 hp2 _ h₁, key (-1) hm2 _ h₂, add_zero]

theorem two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)

theorem eq_one_of_pow_eq_one_of_commute {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ K)} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {u : GL V₄ K} (hu : IsNCInv u) {x : GL V₄ K} (hxG : x ∈ G)
    (hxu : x * u = u * x) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x = 1 := by
  apply hU0 x hxG
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hnil : IsNilpotent ((x : Matrix V₄ V₄ K) - 1) := by
    refine ⟨p ^ k, ?_⟩
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right _), ← Units.val_pow_eq_pow_val, hxk,
      Units.val_one, one_pow, sub_self]
  have hcomm : ((x : Matrix V₄ V₄ K) - 1) * (u : Matrix V₄ V₄ K) =
      (u : Matrix V₄ V₄ K) * ((x : Matrix V₄ V₄ K) - 1) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, ← Units.val_mul, hxu, Units.val_mul]
  exact mul_self_eq_zero_of_isNilpotent_of_commute h2 hu hnil hcomm

theorem not_dvd_orderOf_of_commute [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ K)} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {u : GL V₄ K} (hu : IsNCInv u) {x : GL V₄ K} (hxG : x ∈ G)
    (hxu : x * u = u * x) : ¬ p ∣ orderOf x := by
  intro hdvd
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hy := orderOf_pow_orderOf_div hx0 hdvd
  set y := x ^ (orderOf x / p) with hy_def
  have hyG : y ∈ G := G.pow_mem hxG _
  have hyu : y * u = u * y := (Commute.pow_left hxu _).eq
  have hy1 : y ^ (p ^ 1) = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using this
  have := eq_one_of_pow_eq_one_of_commute hp2 hU0 hu hyG hyu hy1
  rw [this, orderOf_one] at hy
  exact (Fact.out : p.Prime).one_lt.ne hy

end CFSG.RankThree.SubgroupLists
