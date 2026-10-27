module

public import CFSG.Quasithin.Background.HSL3NPrime
public import CFSG.Quasithin.Background.HTriangular

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix Pointwise

variable {K : Type} [Field K]

theorem two_mul_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ≤ 2 ^ k :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [pow_succ]
    omega

theorem le_of_dvd_mul_pow_sub_one {c n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (h : 2 ^ c - 1 ∣ m * (2 ^ n - 1)) : c ≤ n := by
  by_contra hcn
  push Not at hcn
  set d := Nat.gcd c n with hd
  have hdc : d ∣ c := Nat.gcd_dvd_left c n
  have hdn : d ∣ n := Nat.gcd_dvd_right c n
  have hd1 : 1 ≤ d := Nat.gcd_pos_of_pos_right c (by omega)
  have hdn' : d ≤ n := Nat.le_of_dvd (by omega) hdn
  have h2d : 2 * d ≤ c := by
    obtain ⟨t, ht⟩ := hdc
    have ht2 : 2 ≤ t := by
      by_contra h'
      push Not at h'
      interval_cases t
      · rw [mul_zero] at ht
        omega
      · rw [mul_one] at ht
        omega
    calc 2 * d ≤ d * t := by nlinarith
      _ = c := ht.symm
  have hg : Nat.gcd (2 ^ c - 1) (2 ^ n - 1) = 2 ^ d - 1 := Nat.pow_sub_one_gcd_pow_sub_one 2 c n
  have h2d1 : 2 ≤ 2 ^ d :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  have hgpos : 0 < Nat.gcd (2 ^ c - 1) (2 ^ n - 1) := by rw [hg]; omega
  have hdiv : (2 ^ c - 1) / Nat.gcd (2 ^ c - 1) (2 ^ n - 1) ∣ m := by
    have hcop := Nat.coprime_div_gcd_div_gcd hgpos
    refine hcop.dvd_of_dvd_mul_right ?_
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have hga := Nat.gcd_dvd_left (2 ^ c - 1) (2 ^ n - 1)
    have hgb := Nat.gcd_dvd_right (2 ^ c - 1) (2 ^ n - 1)
    apply Nat.eq_of_mul_eq_mul_right hgpos
    calc m * ((2 ^ n - 1) / Nat.gcd (2 ^ c - 1) (2 ^ n - 1)) *
          Nat.gcd (2 ^ c - 1) (2 ^ n - 1) = m * (2 ^ n - 1) := by
          rw [mul_assoc, Nat.div_mul_cancel hgb]
      _ = (2 ^ c - 1) * k := hk
      _ = (2 ^ c - 1) / Nat.gcd (2 ^ c - 1) (2 ^ n - 1) * k *
          Nat.gcd (2 ^ c - 1) (2 ^ n - 1) := by
          rw [mul_right_comm, Nat.div_mul_cancel hga]
  have hle := Nat.le_of_dvd hm hdiv
  have hlow : 2 ^ (c - d) ≤ (2 ^ c - 1) / Nat.gcd (2 ^ c - 1) (2 ^ n - 1) := by
    rw [Nat.le_div_iff_mul_le hgpos, hg]
    have e : 2 ^ (c - d) * 2 ^ d = 2 ^ c := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have h1 : 1 ≤ 2 ^ (c - d) := Nat.one_le_two_pow
    rw [Nat.mul_sub_one, e]
    omega
  have hc : c ≤ 2 ^ (c - d) := by
    have := two_mul_le_two_pow (k := c - d) (by omega)
    omega
  omega

theorem mul_comm_of_subset {G : Type*} [Group G] {H L : Subgroup G}
    (h : (L : Set G) * H ⊆ H * L) : (H : Set G) * L = L * H := by
  refine Set.Subset.antisymm (fun x hx => ?_) h
  have hx' : x⁻¹ ∈ (L : Set G) * H := by
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨b⁻¹, L.inv_mem hb, a⁻¹, H.inv_mem ha, by group⟩
  obtain ⟨a, ha, b, hb, hab⟩ := h hx'
  refine ⟨b⁻¹, L.inv_mem hb, a⁻¹, H.inv_mem ha, ?_⟩
  have hab' : a * b = x⁻¹ := hab
  show b⁻¹ * a⁻¹ = x
  rw [← _root_.mul_inv_rev, hab', inv_inv]

@[expose] noncomputable def linPair (K : Type) [Field K] : Subgroup (MulAut (PairMod K)) :=
  ((linSub (ι := Fin 3) (K := K)).prod linSub).map (pairHom₂ K)

theorem mem_linPair {x : MulAut (PairMod K)} :
    x ∈ linPair K ↔ ∃ a b : MulAut (StdMod (Fin 3) K), a ∈ linSub ∧ b ∈ linSub ∧
      x = pairAut a b := by
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem linPair_le_pairSub : linPair K ≤ pairSub K := Subgroup.map_le_range _ _

theorem pairHom_mem_linPair (γ : GL (Fin 3) K) : pairHom γ ∈ linPair K :=
  mem_linPair.mpr ⟨_, _, isSemilinear_matAut γ, isSemilinear_matAut (dualGL γ), rfl⟩

theorem pairSL_le_linPair : pairSL K ≤ linPair K := by
  rintro _ ⟨γ, -, rfl⟩
  exact pairHom_mem_linPair γ

theorem mem_linPair_of {a b : MulAut (StdMod (Fin 3) K)} (hx : pairAut a b ∈ pairNorm K)
    (ha : IsSemilinear a (RingEquiv.refl K)) : pairAut a b ∈ linPair K :=
  mem_linPair.mpr ⟨a, b, ha, rel_semilinear hx ha, rfl⟩

theorem fstHom_eq {x : ↥(pairSub K)} {a b : MulAut (StdMod (Fin 3) K)}
    (h : (x : MulAut (PairMod K)) = pairAut a b) : fstHom K x = a := by
  have : x = ⟨pairAut a b, pairAut_mem_pairSub a b⟩ := Subtype.ext h
  rw [this, fstHom_pairAut]

@[expose] noncomputable def linFst (K : Type) [Field K] : ↥(linPair K) →* GL (Fin 3) K :=
  (MonoidHom.ofInjective (matHom_injective (ι := Fin 3) (K := K))).symm.toMonoidHom.comp
    (((fstHom K).comp (Subgroup.inclusion linPair_le_pairSub)).codRestrict matHom.range
      fun x => by
        obtain ⟨a, b, ha, -, hx⟩ := mem_linPair.mp x.2
        obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub ha
        exact ⟨A, (fstHom_eq (x := Subgroup.inclusion linPair_le_pairSub x) hx).symm⟩)

theorem matAut_linFst {x : ↥(linPair K)} {a b : MulAut (StdMod (Fin 3) K)}
    (h : (x : MulAut (PairMod K)) = pairAut a b) : matAut (linFst K x) = a := by
  change matHom ((MonoidHom.ofInjective (matHom_injective (ι := Fin 3) (K := K))).symm _) = a
  rw [MonoidHom.apply_ofInjective_symm]
  exact fstHom_eq (x := Subgroup.inclusion linPair_le_pairSub x) h

theorem linFst_rho {x : ↥(linPair K)} {u : Matrix.SpecialLinearGroup (Fin 3) K}
    (h : (x : MulAut (PairMod K)) = SL3One.rho u) :
    linFst K x = Matrix.SpecialLinearGroup.toGL u :=
  matHom_injective (matAut_linFst (h.trans rfl))

theorem eq_one_of_pow_two_pow [CharP K 2] {μ : K} {j : ℕ} (hμ : μ ^ 2 ^ j = 1) : μ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (μ - 1) ^ 2 ^ j = 0 := by rw [sub_pow_char_pow, one_pow, hμ, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero j two_ne_zero)).mp h)

theorem toAddMap_pow_of_rel {D : GL (Fin 3) K} {x : MulAut (StdMod (Fin 3) K)} {μ : K}
    (h : ∀ w, toAddMap x w = μ • ((D : Matrix (Fin 3) (Fin 3) K) *ᵥ w)) (k : ℕ)
    (w : Fin 3 → K) :
    toAddMap (x ^ k) w = μ ^ k • (((D ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Units.val_one, one_mulVec, one_smul]
    rfl
  | succ k ih =>
    rw [pow_succ x, toAddMap_mul, h, ih, pow_succ μ, pow_succ D, Units.val_mul, mulVec_smul,
      smul_smul, mulVec_mulVec]

theorem mem_pairSL_of_two_pow [CharP K 2] {s : MulAut (PairMod K)} (hsN : s ∈ pairNorm K)
    (hsL : s ∈ linPair K) {j : ℕ} (hs : s ^ 2 ^ j = 1) : s ∈ pairSL K := by
  obtain ⟨a, b, ha, -, rfl⟩ := mem_linPair.mp hsL
  obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub ha
  obtain ⟨μ, hμ⟩ := rel_linear hsN
  rw [pairAut_pow] at hs
  obtain ⟨hA, hb⟩ := pairAut_injective (hs.trans pairAut_one.symm)
  have hA' : A ^ 2 ^ j = 1 := matHom_injective (by
    rw [map_pow, map_one]
    exact hA)
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    refine eq_one_of_pow_two_pow (j := j) ?_
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hA', Units.val_one, Matrix.det_one]
  have hD : (dualGL A) ^ 2 ^ j = 1 := by rw [← dualHom_apply, ← map_pow, hA', map_one]
  have hμ1 : μ = 1 := by
    have h1 := toAddMap_pow_of_rel hμ (2 ^ j) (Pi.single 0 1)
    rw [hb, hD, Units.val_one, one_mulVec, toAddMap_one] at h1
    have h2 := congrFun h1 0
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h2
    exact eq_one_of_pow_two_pow h2.symm
  have hb' : b = matAut (dualGL A) := toAddMap_injective fun w => by
    rw [hμ, hμ1, one_smul, toAddMap_matAut]
  rw [hb']
  exact pairHom_mem_pairSL (mem_statedSL_iff.mpr hdet)

variable [Finite K]

theorem exists_semilinear_of_mem {x : MulAut (PairMod K)} (hxN : x ∈ pairNorm K)
    (hxS : x ∈ pairSub K) :
    ∃ a b : MulAut (StdMod (Fin 3) K), ∃ σ : K ≃+* K,
      x = pairAut a b ∧ IsSemilinear a σ ∧ IsSemilinear b σ := by
  set z : ↥(pairSub K) := ⟨x, hxS⟩
  have hxe : x = pairAut (fstHom K z) (sndHom K z) := eq_pairAut z
  obtain ⟨h₁, -⟩ := fstHom_mem_natNorm (x := z) hxN
  obtain ⟨σ, hσ⟩ :=
    exists_semilinear (hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)) h₁
  refine ⟨_, _, σ, hxe, hσ, ?_⟩
  have h := hxN
  rw [hxe] at h
  exact rel_semilinear h hσ

theorem permute_linPair [CharP K 2] {B S : Subgroup (MulAut (PairMod K))}
    (hBN : B ≤ pairNorm K) (hSN : S ≤ pairNorm K) (hBodd : Odd (Nat.card B))
    (hS : IsPGroup 2 S) (hBS : (B : Set (MulAut (PairMod K))) * S = S * B) :
    ((B ⊓ linPair K : Subgroup (MulAut (PairMod K))) : Set (MulAut (PairMod K))) *
        ((S ⊓ pairSL K : Subgroup (MulAut (PairMod K))) : Set (MulAut (PairMod K))) =
      ((S ⊓ pairSL K : Subgroup (MulAut (PairMod K))) : Set (MulAut (PairMod K))) *
        ((B ⊓ linPair K : Subgroup (MulAut (PairMod K))) : Set (MulAut (PairMod K))) := by
  classical
  apply mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linPair K := pairSL_le_linPair hu.2
  have hub : u * b ∈ (S : Set (MulAut (PairMod K))) * B := Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubL : u * b ∈ linPair K := (linPair K).mul_mem huL hb.2
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  have hb'S : b' ∈ pairSub K := mem_pairSub_of_odd (hBN hb') hBodd hb'k
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hse' : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
  have hsS : s ∈ pairSub K := by
    rw [hse']
    exact (pairSub K).mul_mem ((pairSub K).inv_mem hb'S) (linPair_le_pairSub hubL)
  obtain ⟨b₁, b₂, σ, hb'e, hσ₁, -⟩ := exists_semilinear_of_mem (hBN hb') hb'S
  obtain ⟨s₁, s₂, τ, hse, hτ₁, -⟩ := exists_semilinear_of_mem (hSN hs) hsS
  obtain ⟨l₁, l₂, hl₁, -, hle⟩ := mem_linPair.mp hubL
  have h1 : b₁ * s₁ = l₁ := by
    have h' := hbs'
    rw [hb'e, hse, hle, pairAut_mul] at h'
    exact (pairAut_injective h').1
  have hστ : σ * τ = 1 := by
    have h' := hσ₁.mul hτ₁
    rw [h1] at h'
    exact h'.unique hl₁
  have hσk : σ ^ Nat.card B = 1 := by
    have h2 := hσ₁.pow (Nat.card B)
    have h3 : b₁ ^ Nat.card B = 1 := by
      rw [hb'e, pairAut_pow] at hb'k
      exact (pairAut_injective (hb'k.trans pairAut_one.symm)).1
    rw [h3] at h2
    exact h2.unique isSemilinear_one
  have hτj : τ ^ 2 ^ j = 1 := by
    have h2 := hτ₁.pow (2 ^ j)
    have h3 : s₁ ^ 2 ^ j = 1 := by
      rw [hse, pairAut_pow] at hsj
      exact (pairAut_injective (hsj.trans pairAut_one.symm)).1
    rw [h3] at h2
    exact h2.unique isSemilinear_one
  have hσ1 : σ = 1 := by
    have hτσ : τ = σ⁻¹ := eq_inv_of_mul_eq_one_right hστ
    have hσj : σ ^ 2 ^ j = 1 := by
      rw [hτσ, inv_pow, inv_eq_one] at hτj
      exact hτj
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσj))
  rw [hσ1] at hσ₁
  have hb'L : b' ∈ linPair K := by
    have h' := hBN hb'
    rw [hb'e] at h' ⊢
    exact mem_linPair_of h' hσ₁
  have hsL : s ∈ linPair K := by
    rw [hse']
    exact (linPair K).mul_mem ((linPair K).inv_mem hb'L) hubL
  exact ⟨b', ⟨hb', hb'L⟩, s, ⟨hs, mem_pairSL_of_two_pow (hSN hs) hsL hsj⟩, hbs⟩

theorem pow_eq_one_of_mem_borGL [CharP K 2] {A : GL (Fin 3) K} (hA : A ∈ Tri.borGL 3 K)
    (hodd : Odd (orderOf A)) : A ^ (Nat.card K - 1) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hdiag : ∀ (k : ℕ) (i : Fin 3), ((A ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      ((A : Matrix (Fin 3) (Fin 3) K) i i) ^ k := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, LinearFlag.mul_apply_self_of_isUpperTriangular
        ((Tri.borGL 3 K).pow_mem hA k) hA, ih, pow_succ]
  have hne : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro i h
    have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
    rw [Matrix.det_of_isUpperTriangular hA] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h)
  set D := A ^ (Nat.card K - 1) with hDdef
  have hD : D ∈ Tri.borGL 3 K := (Tri.borGL 3 K).pow_mem hA _
  have hD1 : ∀ i, (D : Matrix (Fin 3) (Fin 3) K) i i = 1 := fun i => by
    rw [hDdef, hdiag, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (hne i)
  have hDU : D ∈ Tri.uni3 K := by
    have hdet : (D : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular hD]
      simp [hD1]
    let u : Matrix.SpecialLinearGroup (Fin 3) K := ⟨D, hdet⟩
    refine ⟨u, ?_, Units.ext rfl⟩
    rw [SetLike.mem_coe, LinearFlag.mem_unitriangular]
    exact ⟨fun i j hij => hD hij, hD1⟩
  obtain ⟨j, hj⟩ := Tri.isPGroup_uni3 ⟨D, hDU⟩
  have hDj : D ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h1 : orderOf A ∣ (Nat.card K - 1) * 2 ^ j :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hDj)
  have hcop : Nat.Coprime (orderOf A) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h1)

theorem le_of_permutes [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hX1 : pairSL K ≤ X) (hX2 : X ≤ pairNorm K)
    {Y B S : Subgroup (MulAut (PairMod K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (PairMod K))) * S = S * B) : c ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hBN : B ≤ pairNorm K := hBX.trans hX2
  have hSN : S ≤ pairNorm K := hS.le.trans hX2
  have hperm := permute_linPair hBN hSN hBodd hS.isPGroup hBS
  have hLnX : ((pairSL K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ pairSL K).comap SL3One.rho with hU'
  have hU'map : U'.map SL3One.rho = S ⊓ pairSL K :=
    Subgroup.map_comap_eq_self (by rw [SL3One.range_rho]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map SL3One.rho =
      pairSL K := by
    rw [← MonoidHom.range_eq_map, SL3One.range_rho]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective SL3One.rho_injective, hU'map, htopmap]
    exact hU
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) K) :=
    hU'syl.isPGroup.toSylow (by
      have := hU'syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) K) P' P₀
  have hgU : U'.map (MulAut.conj g).toMonoidHom = LinearFlag.unitriangular 3 K := by
    rw [← hP₀, ← hg, LinearFlag.coe_sylow_smul]
    rfl
  set c₀ := SL3One.rho g with hc₀
  have hU₁ : (S ⊓ pairSL K).map (MulAut.conj c₀).toMonoidHom =
      (LinearFlag.unitriangular 3 K).map SL3One.rho := by
    rw [← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * SL3One.rho x * c₀⁻¹ = SL3One.rho (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linPair K).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linPair K := pairSL_le_linPair (SL3One.rho_mem_pairSL g)
  have hc₀N : c₀ ∈ pairNorm K := pairSL_le_pairNorm (SL3One.rho_mem_pairSL g)
  have hB₁L : B₁ ≤ linPair K := by
    rintro _ ⟨b, hb, rfl⟩
    exact (linPair K).mul_mem ((linPair K).mul_mem hc₀L hb.2) ((linPair K).inv_mem hc₀L)
  have hB₁N : B₁ ≤ pairNorm K := by
    rintro _ ⟨b, hb, rfl⟩
    exact (pairNorm K).mul_mem ((pairNorm K).mul_mem hc₀N (hBN hb.1)) ((pairNorm K).inv_mem hc₀N)
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha.1 b hb.1]
  set U₁ := (LinearFlag.unitriangular 3 K).map SL3One.rho with hU₁def
  have hU₁L : U₁ ≤ linPair K := by
    rintro _ ⟨u, -, rfl⟩
    exact pairSL_le_linPair (SL3One.rho_mem_pairSL u)
  have hperm₁ : (B₁ : Set (MulAut (PairMod K))) * (U₁ : Set (MulAut (PairMod K))) =
      (U₁ : Set (MulAut (PairMod K))) * B₁ := by
    rw [← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm,
      Set.image_mul]
  set B₂ := (B₁.subgroupOf (linPair K)).map (linFst K) with hB₂
  have hU₂ : (U₁.subgroupOf (linPair K)).map (linFst K) = Tri.uni3 K := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hux⟩ := hx
      rw [linFst_rho hux.symm]
      exact ⟨u, hu, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨⟨SL3One.rho u, hU₁L ⟨u, hu, rfl⟩⟩, ⟨u, hu, rfl⟩, linFst_rho rfl⟩
  have hB₂ab : ∀ a ∈ B₂, ∀ b ∈ B₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB₁ab _ ha _ hb)
  have hB₂odd : Odd (Nat.card B₂) := by
    have h1 : Nat.card B₂ ∣ Nat.card (B₁.subgroupOf (linPair K)) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (B₁.subgroupOf (linPair K)) = Nat.card B₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁L).toEquiv
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linPair K) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    have h4 : Nat.card ↥(B ⊓ linPair K) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_left
    rw [h2, h3] at h1
    exact Odd.of_dvd_nat hBodd (h1.trans h4)
  have hB₂U : (B₂ : Set (GL (Fin 3) K)) * (Tri.uni3 K : Set (GL (Fin 3) K)) =
      (Tri.uni3 K : Set (GL (Fin 3) K)) * B₂ := by
    rw [← hU₂, hB₂, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul,
      Tri.subgroupOf_mul_comm hB₁L hU₁L hperm₁]
  have htri : B₂ ≤ Tri.borGL 3 K := Tri.triangular_three hK4 hB₂ab hB₂odd hB₂U
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    set A := linFst K ⟨z, hB₁L hz⟩ with hA
    have hAB : A ∈ B₂ := ⟨⟨z, hB₁L hz⟩, hz, rfl⟩
    have hAodd : Odd (orderOf A) := Odd.of_dvd_nat hB₂odd (Subgroup.orderOf_dvd_natCard B₂ hAB)
    have hA1 := pow_eq_one_of_mem_borGL (htri hAB) hAodd
    obtain ⟨a, x₂, -, -, hze⟩ := mem_linPair.mp (hB₁L hz)
    have haA : matAut A = a := matAut_linFst (x := ⟨z, hB₁L hz⟩) hze
    rw [← haA] at hze
    have hzN := hB₁N hz
    rw [hze] at hzN
    obtain ⟨μ, hμ⟩ := rel_linear hzN
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      have h1 := hμ (Pi.single 0 1)
      rw [zero_smul, toAddMap_eq_zero_iff] at h1
      have h2 := congrFun h1 0
      simp at h2
    have hμq : μ ^ (Nat.card K - 1) = 1 := by
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one μ hμ0
    have hx₂ : x₂ ^ (Nat.card K - 1) = 1 := toAddMap_injective fun w => by
      rw [toAddMap_pow_of_rel hμ, hμq, one_smul, ← dualHom_apply, ← map_pow, hA1, map_one,
        Units.val_one, one_mulVec, toAddMap_one]
    rw [hze, pairAut_pow, hx₂, ← matHom_apply, ← map_pow, hA1, map_one]
    exact pairAut_one
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (PairMod K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (PairMod K)) ∈ B := hYB y.2
  have hyk : (y : MulAut (PairMod K)) ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hyB)
  have hyS := mem_pairSub_of_odd (hBN hyB) hBodd hyk
  obtain ⟨y₁, y₂, σ, hye, hσ₁, -⟩ := exists_semilinear_of_mem (hBN hyB) hyS
  set m := orderOf σ with hm
  have hmn : m ∣ n := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
    have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := by
    have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
    exact orderOf_pos σ
  have hym : (y : MulAut (PairMod K)) ^ m ∈ B ⊓ linPair K := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h1 : IsSemilinear (y₁ ^ m) (RingEquiv.refl K) := by
      have h' := hσ₁.pow m
      rw [hm, pow_orderOf_eq_one] at h'
      exact h'
    have h2 : (y : MulAut (PairMod K)) ^ m ∈ pairNorm K := (pairNorm K).pow_mem (hBN hyB) m
    rw [hye, pairAut_pow] at h2 ⊢
    exact mem_linPair_of h2 h1
  have hypow : (y : MulAut (PairMod K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (PairMod K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ n - 1) := by
    rw [← hyo, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hX1 : pairSL K ≤ X) (hX2 : X ≤ pairNorm K) :
    E3.nPrime X ≤ n := by
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end SL3Pair

end H

end CFSG.Quasithin
