module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148N

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup diagonal)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem diagUnits_mem_glPi148 (hK : PiField π p f K) {u : Kˣ}
    (hu : u ∈ rootsOfUnity (qSubPi π (p ^ f)) K) : diagUnits u 1 1 ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h]
    have hnorm : h.bar (u : K) * u = 1 := by
      rw [mem_rootsOfUnity] at hu
      rw [h.bar_apply, ← pow_succ]
      have := congrArg Units.val hu
      rw [Units.val_pow_eq_pow_val, Units.val_one] at this
      exact this
    rw [coe_diagUnits, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · exact hnorm
    · simp
    · simp
  · exact mem_glPi_true _ _

theorem det_diagUnits148 (u : Kˣ) : GeneralLinearGroup.det (diagUnits u 1 1) = u := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagUnits, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem diagUnits_comm148 (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem mul_comm_of_mk_comm_of_coprime148 {y m : GL (Fin 3) K}
    (hmy : ProjGenLinGroup.mk m * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk m)
    (hcop : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk m))) : m * y = y * m := by
  obtain ⟨u, hu⟩ := Sec17.Proof17Res7.exists_conj_of_mk_comm hmy
  set s := GeneralLinearGroup.scalar (Fin 3) u with hs
  have hscomm : ∀ g : GL (Fin 3) K, g * s = s * g := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u g).eq
  have hu3 : u ^ 3 = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hu
    rw [map_mul, map_mul, map_inv, map_mul] at h1
    have h2 : GeneralLinearGroup.det s = u ^ 3 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, hs, det_scalar, Units.val_pow_eq_pow_val]
    rw [h2, mul_comm (GeneralLinearGroup.det m), mul_assoc, mul_inv_cancel, mul_one] at h1
    have h3 : u ^ 3 * GeneralLinearGroup.det y = 1 * GeneralLinearGroup.det y := by
      rw [← h1, one_mul]
    exact (mul_right_cancel h3)
  have hpow : ∀ k : ℕ, m ^ k * y * (m ^ k)⁻¹ = s ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc m ^ (k + 1) * y * (m ^ (k + 1))⁻¹ = m * (m ^ k * y * (m ^ k)⁻¹) * m⁻¹ := by group
        _ = m * (s ^ k * y) * m⁻¹ := by rw [ih]
        _ = s ^ k * (m * y * m⁻¹) := by
          have hsk : ∀ g : GL (Fin 3) K, g * s ^ k = s ^ k * g := fun g =>
            (Commute.pow_right (show Commute g s from hscomm g) k).eq
          calc m * (s ^ k * y) * m⁻¹ = (m * s ^ k) * y * m⁻¹ := by group
            _ = (s ^ k * m) * y * m⁻¹ := by rw [hsk m]
            _ = s ^ k * (m * y * m⁻¹) := by group
        _ = s ^ k * (s * y) := by rw [hu]
        _ = s ^ (k + 1) * y := by rw [pow_succ, mul_assoc]
  set n := orderOf (ProjGenLinGroup.mk m) with hn
  have hmn : ProjGenLinGroup.mk (m ^ n) = 1 := by rw [map_pow, hn, pow_orderOf_eq_one]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hmn
  obtain ⟨v, hv⟩ := hmn
  have hsn : s ^ n = 1 := by
    have h1 := hpow n
    rw [← hv] at h1
    have h2 : GeneralLinearGroup.scalar (Fin 3) v * y * (GeneralLinearGroup.scalar (Fin 3) v)⁻¹ =
        y := by
      have hc : y * GeneralLinearGroup.scalar (Fin 3) v = GeneralLinearGroup.scalar (Fin 3) v * y :=
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar v y).eq
      rw [← hc, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 : s ^ n * y = 1 * y := by rw [← h1, one_mul]
    exact mul_right_cancel h3
  have hun : u ^ n = 1 := by
    have h1 : GeneralLinearGroup.scalar (Fin 3) (u ^ n) = 1 := by rw [map_pow, ← hs, hsn]
    have h2 := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K) 0 0)) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2)
  have hu1 : u = 1 := by
    have h1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have h2 : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hun
    have h3 : orderOf u ∣ Nat.gcd 3 n := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hs1 : s = 1 := by rw [hs, hu1, map_one]
  rw [hs1, one_mul] at hu
  calc m * y = m * y * m⁻¹ * m := by group
    _ = y * m := by rw [hu]

theorem false_of_irreducible_slPi148 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hxL : x ∈ slPi π 3 (p ^ f) K) {c : Kˣ}
    (hx3 : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) c)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set X := (x : Matrix (Fin 3) (Fin 3) K) with hX
  have hdet : X.det = 1 := ((mem_slPi_iff hπ).mp hxL).2
  have hxm : X ^ 3 = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hx3
    simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    rw [hX, h1, Matrix.smul_one_eq_diagonal]
  by_cases hcube : ∃ μ : K, μ ^ 3 = (c : K)
  · obtain ⟨μ, hμ⟩ := hcube
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    have h0 := one_add_tau_add_sq hτ hτ1
    obtain ⟨l₂, hl₂⟩ : ∃ l₂ : K, l₂ = μ * τ := ⟨_, rfl⟩
    obtain ⟨l₃, hl₃⟩ : ∃ l₃ : K, l₃ = μ * τ ^ 2 := ⟨_, rfl⟩
    obtain ⟨m₃, hm₃⟩ : ∃ m₃ : K, m₃ = μ ^ 3 := ⟨_, rfl⟩
    have key : (Polynomial.X - Polynomial.C μ) * (Polynomial.X - Polynomial.C l₂) *
        (Polynomial.X - Polynomial.C l₃) = (Polynomial.X ^ 3 - Polynomial.C m₃ :
          Polynomial K) := by
      have h0' : (1 : Polynomial K) + Polynomial.C τ + Polynomial.C τ ^ 2 = 0 := by
        have := congrArg Polynomial.C h0
        simpa [map_add, map_pow] using this
      have hτ' : (Polynomial.C τ : Polynomial K) ^ 3 = 1 := by
        rw [← map_pow, hτ, map_one]
      rw [hl₂, hl₃, hm₃]
      simp only [map_mul, map_pow]
      linear_combination (-(Polynomial.C μ) * Polynomial.X ^ 2 +
        Polynomial.C μ ^ 2 * Polynomial.C τ * Polynomial.X) * h0' - Polynomial.C μ ^ 3 * hτ'
    have hprod : (X - μ • 1) * (X - l₂ • 1) * (X - l₃ • 1) = 0 := by
      have h1 := congrArg (Polynomial.aeval X) key
      simp only [map_mul, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one] at h1
      rw [h1, hm₃, hμ, hxm, sub_self]
    have hdet0 := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at hdet0
    obtain ⟨l, hl⟩ : ∃ l : K, (X - l • 1).det = 0 := by
      rcases mul_eq_zero.mp hdet0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact ⟨μ, h'⟩
        · exact ⟨l₂, h'⟩
      · exact ⟨l₃, h⟩
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hl
    have hXv : X *ᵥ v = l • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
      exact hv
    set W := Submodule.span K {v} with hW
    have hinv : ∀ w ∈ W, X *ᵥ w ∈ W := by
      intro w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [Matrix.mulVec_smul, hXv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    rcases hirr W hinv with hbot | htop
    · exact hv0 ((Submodule.span_singleton_eq_bot).mp hbot)
    · have h1 : Module.finrank K W = 1 := finrank_span_singleton hv0
      rw [htop, finrank_top, Module.finrank_fin_fun] at h1
      omega
  · push Not at hcube
    have h1 := det_eq_of_cube hcube hxm
    rw [hdet] at h1
    exact hcube 1 (by rw [one_pow, h1])

theorem comm_of_diagonal148 {A B : GL (Fin 3) K} {a b : Fin 3 → K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal a)
    (hB : (B : Matrix (Fin 3) (Fin 3) K) = diagonal b) : A * B = B * A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hA, hB, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem model_kf148 (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {x g : GL (Fin 3) K}
    (hxL : x ∈ slPi π 3 (p ^ f) K) (hx1 : ProjGenLinGroup.mk x ≠ 1)
    (hx3 : ProjGenLinGroup.mk x ^ 3 = 1) (hg : g ∈ glPi π 3 (p ^ f) K)
    (hgx : ProjGenLinGroup.mk g * ProjGenLinGroup.mk x =
      ProjGenLinGroup.mk x * ProjGenLinGroup.mk g) :
    ∃ c ∈ glPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk c * ProjGenLinGroup.mk x = ProjGenLinGroup.mk x * ProjGenLinGroup.mk c ∧
      c⁻¹ * g ∈ slPi π 3 (p ^ f) K ∧
      ∀ m ∈ slPi π 3 (p ^ f) K,
        ProjGenLinGroup.mk m * ProjGenLinGroup.mk x = ProjGenLinGroup.mk x * ProjGenLinGroup.mk m →
        Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk m)) →
        ProjGenLinGroup.mk c * ProjGenLinGroup.mk m =
          ProjGenLinGroup.mk m * ProjGenLinGroup.mk c := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hxH : x ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hxL
  have hxZ : x ∉ zPi π 3 (p ^ f) K := by
    intro h
    rw [zPi_eq hπ hq' hτ hτ1] at h
    apply hx1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact h.2
  have hx3Z : x ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hxH 3, ?_⟩
    have h1 : ProjGenLinGroup.mk (x ^ 3) = 1 := by rw [map_pow, hx3]
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    exact h1
  obtain ⟨y, ⟨z, hz, rfl⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hxH hxZ hx3Z
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    exact hz.2
  have hmkz : ProjGenLinGroup.mk z = 1 := by
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact hzS
  have hmky : ProjGenLinGroup.mk (x * z) = ProjGenLinGroup.mk x := by
    rw [map_mul, hmkz, mul_one]
  set u := GeneralLinearGroup.det g with hu
  have hu1 : u ∈ rootsOfUnity (qSubPi π (p ^ f)) K := det_mem_rootsOfUnity hK hg
  set d := diagUnits u 1 1 with hd
  have hdH : d ∈ glPi π 3 (p ^ f) K := diagUnits_mem_glPi148 hK hu1
  have hdet : GeneralLinearGroup.det d = u := det_diagUnits148 u
  have hkey : ∀ m ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk m * ProjGenLinGroup.mk x = ProjGenLinGroup.mk x * ProjGenLinGroup.mk m →
      Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk m)) → m * (x * z) = (x * z) * m := by
    intro m _ hmx hcop
    rw [← hmky] at hmx
    exact mul_comm_of_mk_comm_of_coprime148 hmx hcop
  have hbuild : ∀ (g₀ D : GL (Fin 3) K), g₀ ∈ glPi π 3 (p ^ f) K → g₀⁻¹ * (x * z) * g₀ = D →
      D * d = d * D →
      (∀ m ∈ slPi π 3 (p ^ f) K, m * D = D * m → m * d = d * m) →
      ∃ c ∈ glPi π 3 (p ^ f) K,
        ProjGenLinGroup.mk c * ProjGenLinGroup.mk x =
          ProjGenLinGroup.mk x * ProjGenLinGroup.mk c ∧
        c⁻¹ * g ∈ slPi π 3 (p ^ f) K ∧
        ∀ m ∈ slPi π 3 (p ^ f) K,
          ProjGenLinGroup.mk m * ProjGenLinGroup.mk x =
            ProjGenLinGroup.mk x * ProjGenLinGroup.mk m →
          Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk m)) →
          ProjGenLinGroup.mk c * ProjGenLinGroup.mk m =
            ProjGenLinGroup.mk m * ProjGenLinGroup.mk c := by
    intro g₀ D hg₀ hD hDd hLd
    have hy : x * z = g₀ * D * g₀⁻¹ := by rw [← hD]; group
    refine ⟨g₀ * d * g₀⁻¹, mul_mem (mul_mem hg₀ hdH) (inv_mem hg₀), ?_, ?_, ?_⟩
    · have hc : (g₀ * d * g₀⁻¹) * (x * z) = (x * z) * (g₀ * d * g₀⁻¹) := by
        rw [hy]
        calc g₀ * d * g₀⁻¹ * (g₀ * D * g₀⁻¹) = g₀ * (d * D) * g₀⁻¹ := by group
          _ = g₀ * (D * d) * g₀⁻¹ := by rw [hDd]
          _ = g₀ * D * g₀⁻¹ * (g₀ * d * g₀⁻¹) := by group
      rw [← hmky, ← map_mul, ← map_mul, hc]
    · rw [mem_slPi_iff hπ]
      refine ⟨mul_mem (inv_mem (mul_mem (mul_mem hg₀ hdH) (inv_mem hg₀))) hg, ?_⟩
      rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, map_mul, map_mul, map_inv, hdet]
      have : GeneralLinearGroup.det g₀ * u * (GeneralLinearGroup.det g₀)⁻¹ = u := by
        rw [mul_comm (GeneralLinearGroup.det g₀), mul_assoc, mul_inv_cancel, mul_one]
      rw [this, hu, inv_mul_cancel, Units.val_one]
    · intro m hm hmx hcop
      have hmy := hkey m hm hmx hcop
      have hm' : g₀⁻¹ * m * g₀ ∈ slPi π 3 (p ^ f) K := by
        have := conj_mem_slPi hπ (inv_mem hg₀) hm
        rwa [inv_inv] at this
      have hm'D : (g₀⁻¹ * m * g₀) * D = D * (g₀⁻¹ * m * g₀) := by
        rw [← hD]
        calc g₀⁻¹ * m * g₀ * (g₀⁻¹ * (x * z) * g₀) = g₀⁻¹ * (m * (x * z)) * g₀ := by group
          _ = g₀⁻¹ * ((x * z) * m) * g₀ := by rw [hmy]
          _ = g₀⁻¹ * (x * z) * g₀ * (g₀⁻¹ * m * g₀) := by group
      have hm'd := hLd _ hm' hm'D
      have hc : m * (g₀ * d * g₀⁻¹) = (g₀ * d * g₀⁻¹) * m := by
        calc m * (g₀ * d * g₀⁻¹) = g₀ * ((g₀⁻¹ * m * g₀) * d) * g₀⁻¹ := by group
          _ = g₀ * (d * (g₀⁻¹ * m * g₀)) * g₀⁻¹ := by rw [hm'd]
          _ = (g₀ * d * g₀⁻¹) * m := by group
      rw [← map_mul, ← map_mul, hc]
  rcases hcases with ⟨⟨g₀, hg₀, hD⟩, -, -⟩ | ⟨⟨g₀, hg₀, e, he, hD⟩, -, -⟩ | ⟨-, hirr, -⟩
  ·
    refine hbuild g₀ (diagTau hτ) hg₀ hD
      (comm_of_diagonal148 (coe_diagTau_eq_diagonal hτ) (coe_diagUnits u 1 1)) ?_
    intro m hm hmD
    have hmC : m ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} :=
      Subgroup.mem_inf.mpr ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmD⟩
    rw [centralizer_diagTau_eq hK hq hτ hτ1] at hmC
    obtain ⟨ab, rfl⟩ := hmC
    exact comm_of_diagonal148 (coe_torusHom _) (coe_diagUnits u 1 1)
  ·
    have he1 : e ≠ 1 := by
      rintro rfl
      rcases he with he | he
      · exact hτ1 (by rw [← he, Units.val_one])
      · have h2 : τ ^ 2 = 1 := by rw [← he, Units.val_one]
        apply hτ1
        have h0 : τ ≠ 0 := by
          rintro rfl
          simp at hτ
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, h2, div_one]
    refine hbuild g₀ (diagE e) hg₀ hD (diagUnits_comm148 e 1 1 u 1 1) ?_
    intro m hm hmD
    have hmC : m ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE e} :=
      Subgroup.mem_inf.mpr ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmD⟩
    rw [centralizer_diagE_eq hK he1] at hmC
    obtain ⟨B, -, rfl⟩ := hmC
    exact blockHom_commute u B
  ·
    exfalso
    rw [zPi_eq hπ hq' hτ hτ1] at hx3Z
    obtain ⟨-, c, hc⟩ := Subgroup.mem_inf.mp hx3Z
    exact false_of_irreducible_slPi148 hK hq hxL hc.symm hirr

end CFSG.RankThree.PartTwo.Sec14.Ronan148N
