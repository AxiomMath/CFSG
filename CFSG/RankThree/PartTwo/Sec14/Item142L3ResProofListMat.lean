module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessModel
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofDefs
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix Polynomial CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.SeitzGeneration (heisC)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

variable {K : Type} [Field K]

theorem heisC_mul_diagonal (β a b c : K) :
    heisC β * diagonal ![a, b, c] = diagonal ![c, a, b] * heisC β := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [heisC, mul_comm]

theorem diagonal_mul_heisC {τ : K} (hτ : τ ^ 3 = 1) (β : K) :
    diagonal ![τ, τ ^ 2, 1] * heisC β = τ • (heisC β * diagonal ![τ, τ ^ 2, 1]) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [heisC] <;>
    first | ring1 | linear_combination -hτ

theorem mul_pow_three_of_mul_eq_smul {A C : Matrix (Fin 3) (Fin 3) K} {t : K} (ht : t ^ 3 = 1)
    (h : A * C = t • (C * A)) : (A * C) ^ 3 = A ^ 3 * C ^ 3 := by
  have h' : C * A = t ^ 2 • (A * C) := by
    rw [h, smul_smul, ← pow_succ, ht, one_smul]
  have e1 : (A * C) ^ 3 = A * (C * A) * (C * A) * C := by
    simp only [pow_three, Matrix.mul_assoc]
  have e2 : A * (C * A) * (C * A) * C = (t ^ 2 * t ^ 2) • (A * A * (C * A) * C * C) := by
    conv_lhs => rw [h']
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  have e3 : A * A * (C * A) * C * C = t ^ 2 • (A * A * A * (C * C * C)) := by
    conv_lhs => rw [h']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [e1, e2, e3, smul_smul, show t ^ 2 * t ^ 2 * t ^ 2 = (t ^ 3) ^ 2 by ring, ht, one_pow,
    one_smul]
  simp only [pow_three, Matrix.mul_assoc]

theorem diagonal_pow_mul_heisC {τ : K} (hτ : τ ^ 3 = 1) (β : K) (i : ℕ) :
    diagonal ![τ, τ ^ 2, 1] ^ i * heisC β =
      τ ^ i • (heisC β * diagonal ![τ, τ ^ 2, 1] ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc diagonal ![τ, τ ^ 2, 1] ^ (i + 1) * heisC β =
        diagonal ![τ, τ ^ 2, 1] ^ i * (diagonal ![τ, τ ^ 2, 1] * heisC β) := by
          rw [pow_succ, Matrix.mul_assoc]
      _ = τ • ((diagonal ![τ, τ ^ 2, 1] ^ i * heisC β) * diagonal ![τ, τ ^ 2, 1]) := by
          rw [diagonal_mul_heisC hτ, Matrix.mul_smul, Matrix.mul_assoc]
      _ = τ ^ (i + 1) • (heisC β * diagonal ![τ, τ ^ 2, 1] ^ (i + 1)) := by
          rw [ih, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, ← pow_succ, pow_succ τ i,
            mul_comm τ]

theorem diagonal_tau_pow_three {τ : K} (hτ : τ ^ 3 = 1) :
    diagonal ![τ, τ ^ 2, 1] ^ 3 = (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa using hτ
  · change (τ ^ 2) ^ 3 = 1
    rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hτ, one_pow]
  · simp

theorem diagonal_pow_mul_heisC_pow_three {τ : K} (hτ : τ ^ 3 = 1) (β : K) (i : ℕ) :
    (diagonal ![τ, τ ^ 2, 1] ^ i * heisC β) ^ 3 = β • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have ht : (τ ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  rw [mul_pow_three_of_mul_eq_smul ht (diagonal_pow_mul_heisC hτ β i), ← pow_mul, mul_comm,
    pow_mul, diagonal_tau_pow_three hτ, one_pow, Matrix.one_mul, heisC_pow_three]

theorem offDiag_of_comm_d {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {X : GL (Fin 3) K}
    (hX : ProjGenLinGroup.mk X * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk X)
    (hX3 : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk X))) :
    ∀ i j : Fin 3, i ≠ j → (X : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
  Sec17.Proof17Res7.offDiag_of_comm_diagTau hτ hτ1
    (Res8Hess.commute_of_mk_commute_of_coprime' hX hX3)

theorem mk_comm_of_offDiag {X Y : GL (Fin 3) K}
    (hX : ∀ i j : Fin 3, i ≠ j → (X : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (hY : ∀ i j : Fin 3, i ≠ j → (Y : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ProjGenLinGroup.mk X * ProjGenLinGroup.mk Y =
      ProjGenLinGroup.mk Y * ProjGenLinGroup.mk X := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Sec17.Proof17Res7.eq_diagonal_of_offDiag hX,
    Sec17.Proof17Res7.eq_diagonal_of_offDiag hY, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem offDiag_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ∀ i j : Fin 3, i ≠ j → ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  intro i j hij
  rw [coe_diagTau_eq_diagonal]
  exact diagonal_apply_ne _ hij

theorem offDiag_of_comm_conj {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {β : K}
    {cβ : GL (Fin 3) K} (hcβ : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β)
    {z : ProjGenLinGroup (Fin 3) K}
    (hzd : z * ProjGenLinGroup.mk (diagTau hτ) = ProjGenLinGroup.mk (diagTau hτ) * z)
    (hz1 : z ≠ 1) (hz3 : Nat.Coprime 3 (orderOf z)) {G : GL (Fin 3) K}
    (h1 : z * ProjGenLinGroup.mk G = ProjGenLinGroup.mk G * z)
    (h2 : ProjGenLinGroup.mk cβ * z * (ProjGenLinGroup.mk cβ)⁻¹ * ProjGenLinGroup.mk G =
      ProjGenLinGroup.mk G * (ProjGenLinGroup.mk cβ * z * (ProjGenLinGroup.mk cβ)⁻¹))
    (h3 : (ProjGenLinGroup.mk cβ)⁻¹ * z * ProjGenLinGroup.mk cβ * ProjGenLinGroup.mk G =
      ProjGenLinGroup.mk G * ((ProjGenLinGroup.mk cβ)⁻¹ * z * ProjGenLinGroup.mk cβ)) :
    ∀ i j : Fin 3, i ≠ j → (G : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨Z, rfl⟩ := ProjGenLinGroup.mk_surjective z
  have hZoff := offDiag_of_comm_d hτ hτ1 hzd hz3
  have hZd := Sec17.Proof17Res7.eq_diagonal_of_offDiag hZoff
  set a := (Z : Matrix (Fin 3) (Fin 3) K) 0 0
  set b := (Z : Matrix (Fin 3) (Fin 3) K) 1 1
  set c := (Z : Matrix (Fin 3) (Fin 3) K) 2 2
  have key : ∀ W : GL (Fin 3) K, ProjGenLinGroup.mk W * ProjGenLinGroup.mk G =
      ProjGenLinGroup.mk G * ProjGenLinGroup.mk W →
      Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk W)) →
      (W : Matrix (Fin 3) (Fin 3) K) * G = (G : Matrix (Fin 3) (Fin 3) K) * W := by
    intro W hW hW3
    have := Res8Hess.commute_of_mk_commute_of_coprime' hW hW3
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) this
  have k1 := key Z h1 hz3
  have k2 := key (cβ * Z * cβ⁻¹) (by simpa only [map_mul, map_inv] using h2) (by
    rw [map_mul, map_mul, map_inv, Res8Hess.orderOf_conj_eq]
    exact hz3)
  have k3 := key (cβ⁻¹ * Z * cβ) (by simpa only [map_mul, map_inv] using h3) (by
    rw [map_mul, map_mul, map_inv,
      show (ProjGenLinGroup.mk cβ)⁻¹ * ProjGenLinGroup.mk Z * ProjGenLinGroup.mk cβ =
        (ProjGenLinGroup.mk cβ)⁻¹ * ProjGenLinGroup.mk Z * (ProjGenLinGroup.mk cβ)⁻¹⁻¹ by
          rw [inv_inv], Res8Hess.orderOf_conj_eq]
    exact hz3)
  have hcd : (cβ : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] =
      diagonal ![c, a, b] * cβ := by
    rw [hcβ]
    exact heisC_mul_diagonal β a b c
  have hcd' : (cβ : Matrix (Fin 3) (Fin 3) K) * diagonal ![b, c, a] =
      diagonal ![a, b, c] * cβ := by
    rw [hcβ]
    exact heisC_mul_diagonal β b c a
  have hc1 : ((cβ * Z * cβ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![c, a, b] := by
    rw [Units.val_mul, Units.val_mul, hZd, hcd, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hc2 : ((cβ⁻¹ * Z * cβ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![b, c, a] := by
    rw [Units.val_mul, Units.val_mul, hZd, Matrix.mul_assoc, ← hcd', ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  rw [hc1] at k2
  rw [hc2] at k3
  rw [hZd] at k1
  have hcyc : ∀ t : Fin 3, (G : Matrix (Fin 3) (Fin 3) K) * diagonal (Res8Hess.cycDiag' a b c t) =
      diagonal (Res8Hess.cycDiag' a b c t) * G := by
    intro t
    fin_cases t
    · exact k1.symm
    · exact k2.symm
    · exact k3.symm
  have habc : ¬ (a = b ∧ b = c) := by
    rintro ⟨hab, hbc⟩
    apply hz1
    have hZs : (Z : Matrix (Fin 3) (Fin 3) K) =
        c • ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hZd, hab, hbc, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [mk_eq_of_coe_eq_smul hZs, map_one]
  intro i j hij
  obtain ⟨t, ht⟩ := Res8Hess.exists_cycDiag'_ne habc hij
  exact entry_eq_zero_of_commute_diagonal (hcyc t) ht

open IntermediateField in
theorem commute_of_commute_poly [Finite K] {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = ℓ • 1) {z x : Matrix (Fin 3) (Fin 3) K}
    (hzy : z * y = y * z) (hz : ∀ c : K, z ≠ c • 1) (hxz : x * z = z * x) :
    x * y = y * x := by
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  obtain ⟨ζ, rfl⟩ := (mem_range_cubeHom hℓ hy z).mpr hzy
  set pb := AdjoinRoot.powerBasis' (monic_cube ℓ) with hpb
  have hF3 : Module.finrank K (cubeField ℓ) = 3 := by
    rw [pb.finrank]
    exact natDegree_cube ℓ
  have : FiniteDimensional K (cubeField ℓ) := pb.finite
  have hζ : ζ ∉ (⊥ : IntermediateField K (cubeField ℓ)) := by
    intro h
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp h
    apply hz c
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  have htop : K⟮ζ⟯ = ⊤ := by
    have hdvd : Module.finrank K K⟮ζ⟯ ∣ 3 := by
      have h := IntermediateField.finrank_dvd_of_le_right (le_top : K⟮ζ⟯ ≤ ⊤)
      rwa [IntermediateField.finrank_top', hF3] at h
    have h1 : Module.finrank K K⟮ζ⟯ ≠ 1 := fun h =>
      hζ (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h)
    have h3 : Module.finrank K K⟮ζ⟯ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h h1
      · exact h
    exact IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [h3, IntermediateField.finrank_top', hF3])
  have hroot : AdjoinRoot.root (X ^ 3 - C ℓ : K[X]) ∈ Algebra.adjoin K {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic ζ), htop]
    exact IntermediateField.mem_top
  have hmap : cubeHom hy (AdjoinRoot.root (X ^ 3 - C ℓ : K[X])) ∈
      Algebra.adjoin K {cubeHom hy ζ} := by
    rw [← Set.image_singleton, ← AlgHom.map_adjoin]
    exact ⟨_, hroot, rfl⟩
  rw [cubeHom_root] at hmap
  have hle : Algebra.adjoin K {cubeHom hy ζ} ≤ Subalgebra.centralizer K {x} := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hxz
  exact (Subalgebra.mem_centralizer_iff K).mp (hle hmap) x rfl

theorem commute_of_commute_type3 [Finite K] {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    {B : GL (Fin 3) K} (hB : (B : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) {X Y : GL (Fin 3) K}
    (hX : X * B = B * X) (hY : Y * B = B * Y) : X * Y = Y * X := by
  have := (centralizer_cyclic_card hℓ hB).1
  have h := mul_comm' (⟨X, Subgroup.mem_centralizer_singleton_iff.mpr hX⟩ :
      Subgroup.centralizer ({B} : Set (GL (Fin 3) K)))
    ⟨Y, Subgroup.mem_centralizer_singleton_iff.mpr hY⟩
  exact congrArg Subtype.val h

theorem comm_of_comm_type3 [Finite K] {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {B : GL (Fin 3) K}
    (hB : (B : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) {z : ProjGenLinGroup (Fin 3) K}
    (hzB : z * ProjGenLinGroup.mk B = ProjGenLinGroup.mk B * z) (hz1 : z ≠ 1)
    (hz3 : Nat.Coprime 3 (orderOf z)) {g : ProjGenLinGroup (Fin 3) K} (hg : z * g = g * z) :
    g * ProjGenLinGroup.mk B = ProjGenLinGroup.mk B * g ∧
      ∀ h : ProjGenLinGroup (Fin 3) K, z * h = h * z → g * h = h * g := by
  obtain ⟨Z, rfl⟩ := ProjGenLinGroup.mk_surjective z
  have hZB : Z * B = B * Z := Res8Hess.commute_of_mk_commute_of_coprime' hzB hz3
  have hZs : ∀ c : K, (Z : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hz1
    have : (Z : Matrix (Fin 3) (Fin 3) K) =
        c • ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hc, Units.val_one]
    rw [mk_eq_of_coe_eq_smul this, map_one]
  have key : ∀ H : GL (Fin 3) K, ProjGenLinGroup.mk Z * ProjGenLinGroup.mk H =
      ProjGenLinGroup.mk H * ProjGenLinGroup.mk Z → H * B = B * H := by
    intro H hH
    have hZH : Z * H = H * Z := Res8Hess.commute_of_mk_commute_of_coprime' hH hz3
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    refine commute_of_commute_poly hℓ hB (z := Z) ?_ hZs ?_
    · exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hZB
    · exact (congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hZH).symm
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
  have hGB := key G hg
  refine ⟨by rw [← map_mul, ← map_mul, hGB], fun h hh => ?_⟩
  obtain ⟨H, rfl⟩ := ProjGenLinGroup.mk_surjective h
  rw [← map_mul, ← map_mul, commute_of_commute_type3 hℓ hB hGB (key H hh)]

theorem offDiag_of_mk_eq {X Y : GL (Fin 3) K} (h : ProjGenLinGroup.mk X = ProjGenLinGroup.mk Y)
    (hX : ∀ i j : Fin 3, i ≠ j → (X : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ∀ i j : Fin 3, i ≠ j → (Y : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  intro i j hij
  rw [← hu, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, hX i j hij, zero_mul]

section E

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K}
  (hcβ : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β)

include hcβ in
theorem mk_d_comm_c :
    ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cβ =
      ProjGenLinGroup.mk cβ * ProjGenLinGroup.mk (diagTau hτ) := by
  rw [← map_mul, ← map_mul]
  apply mk_eq_of_coe_eq_smul (a := τ)
  rw [Units.val_mul, Units.val_mul, coe_diagTau_eq_diagonal, hcβ]
  exact diagonal_mul_heisC hτ β

theorem mk_d_pow_three : ProjGenLinGroup.mk (diagTau hτ) ^ 3 = 1 := by
  rw [← map_pow]
  have : diagTau hτ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, diagonal_tau_pow_three hτ,
      Units.val_one]
  rw [this, map_one]

include hcβ in
theorem mk_c_pow_three : ProjGenLinGroup.mk cβ ^ 3 = 1 := by
  rw [← map_pow, ← map_one ProjGenLinGroup.mk]
  apply mk_eq_of_coe_eq_smul (a := β)
  rw [Units.val_pow_eq_pow_val, hcβ, heisC_pow_three, Units.val_one]

include hτ1 in
theorem mk_d_ne_one : ProjGenLinGroup.mk (diagTau hτ) ≠ 1 := by
  intro h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hu
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagTau] at e0 e2
  simp at e0 e2
  rw [e2, Units.val_one] at e0
  exact hτ1 e0.symm

include hcβ in
theorem mk_c_not_mem :
    ProjGenLinGroup.mk cβ ∉ Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [Sec4.zpow_emod_three (mk_d_pow_three hτ) k] at hk
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  rw [← Int.toNat_of_nonneg h0, zpow_natCast, ← map_pow] at hk
  have hoff : ∀ i j : Fin 3, i ≠ j →
      ((diagTau hτ ^ (k % 3).toNat : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, diagonal_pow]
    exact diagonal_apply_ne _ hij
  have h10 := offDiag_of_mk_eq hk hoff 1 0 (by decide)
  rw [hcβ] at h10
  simp [heisC] at h10

theorem comm_iff_comm_inv {G : Type*} [Group G] (b x : G) :
    x * b = b * x ↔ x * b⁻¹ = b⁻¹ * x :=
  ⟨fun h => (Commute.inv_right h).eq, fun h => by simpa using (Commute.inv_right h).eq⟩

include hcβ in
theorem exists_partner {b : ProjGenLinGroup (Fin 3) K}
    (hb : b ∈ Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ)) (hb1 : b ≠ 1) :
    ∃ b' : ProjGenLinGroup (Fin 3) K, (b' = b ∨ b' = b⁻¹) ∧
      (b' = ProjGenLinGroup.mk (diagTau hτ) ∨
        ∃ i : ℕ, b' = ProjGenLinGroup.mk (diagTau hτ ^ i * cβ)) := by
  set D := ProjGenLinGroup.mk (diagTau hτ) with hD
  set C := ProjGenLinGroup.mk cβ with hC
  have hDC : D * C = C * D := mk_d_comm_c hτ hcβ
  have hD3 : D ^ 3 = 1 := mk_d_pow_three hτ
  have hC3 : C ^ 3 = 1 := mk_c_pow_three hcβ
  obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hDC hb
  rw [Sec4.zpow_emod_three hD3 i, Sec4.zpow_emod_three hC3 j] at hb1 ⊢
  have hi0 : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
  have hj0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have hi3 : (i % 3).toNat < 3 := by omega
  have hj3 : (j % 3).toNat < 3 := by omega
  rw [← Int.toNat_of_nonneg hi0, ← Int.toNat_of_nonneg hj0, zpow_natCast, zpow_natCast] at hb1 ⊢
  generalize (i % 3).toNat = m at hb1 hi3 ⊢
  generalize (j % 3).toNat = n at hb1 hj3 ⊢
  interval_cases n
  · rw [pow_zero, mul_one] at hb1 ⊢
    interval_cases m
    · exact absurd (pow_zero D) hb1
    · exact ⟨D, Or.inl (pow_one D).symm, Or.inl rfl⟩
    · refine ⟨D, Or.inr (eq_inv_of_mul_eq_one_left ?_), Or.inl rfl⟩
      rw [← pow_succ', hD3]
  · refine ⟨D ^ m * C, Or.inl (by rw [pow_one]), Or.inr ⟨m, by rw [map_mul, map_pow]⟩⟩
  · refine ⟨D ^ (2 * m) * C, Or.inr (eq_inv_of_mul_eq_one_left ?_),
      Or.inr ⟨2 * m, by rw [map_mul, map_pow]⟩⟩
    calc D ^ (2 * m) * C * (D ^ m * C ^ 2) = D ^ (2 * m) * (C * D ^ m) * C ^ 2 := by group
      _ = D ^ (2 * m) * (D ^ m * C) * C ^ 2 := by rw [(Commute.pow_left hDC m).eq.symm]
      _ = D ^ (3 * m) * C ^ 3 := by
          rw [show 3 * m = 2 * m + m by ring, pow_add, pow_succ' C 2]
          group
      _ = 1 := by rw [pow_mul, hD3, one_pow, hC3, one_mul]

@[expose] def thetaSet (b : ProjGenLinGroup (Fin 3) K) : Set (ProjGenLinGroup (Fin 3) K) :=
  {x | x * b = b * x ∧ Nat.Coprime 3 (orderOf x)}

@[expose] def thetaP (b : ProjGenLinGroup (Fin 3) K) : Subgroup (ProjGenLinGroup (Fin 3) K) :=
  Subgroup.closure (thetaSet b)

end E

theorem comm_of_mem_thetaP {b x : ProjGenLinGroup (Fin 3) K} (hx : x ∈ thetaP b) :
    x * b = b * x := by
  have hle : thetaP b ≤ Subgroup.centralizer {b} :=
    (Subgroup.closure_le _).mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr hy.1
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem mem_thetaP_of {b x : ProjGenLinGroup (Fin 3) K} (hxb : x * b = b * x)
    (hx3 : Nat.Coprime 3 (orderOf x)) : x ∈ thetaP b :=
  Subgroup.subset_closure ⟨hxb, hx3⟩

theorem thetaP_facts {b : ProjGenLinGroup (Fin 3) K}
    (h : ∀ x ∈ thetaSet b, ∀ y ∈ thetaSet b, x * y = y * x) :
    (∀ x ∈ thetaP b, ∀ y ∈ thetaP b, x * y = y * x) ∧
      ∀ x ∈ thetaP b, Nat.Coprime 3 (orderOf x) := by
  have : IsMulCommutative (thetaP b) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => h x hx y hy
  have h1 : ∀ x ∈ thetaP b, ∀ y ∈ thetaP b, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : thetaP b) ⟨y, hy⟩)
  refine ⟨h1, fun x hx => ?_⟩
  have hx' : x ∈ Subgroup.closure (thetaSet b) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => rw [orderOf_one]; exact Nat.coprime_one_right 3
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := h1 x hx y hy
    exact Nat.Coprime.coprime_dvd_right (hc.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
      (Nat.Coprime.mul_right ihx ihy)
  | inv x hx ihx => rw [orderOf_inv]; exact ihx

theorem conj_mem_thetaP {b x : ProjGenLinGroup (Fin 3) K} (g : ProjGenLinGroup (Fin 3) K)
    (hx : x ∈ thetaP b) : g * x * g⁻¹ ∈ thetaP (g * b * g⁻¹) := by
  have hx' : x ∈ Subgroup.closure (thetaSet b) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx =>
    refine mem_thetaP_of ?_ (by rw [Res8Hess.orderOf_conj_eq]; exact hx.2)
    calc g * x * g⁻¹ * (g * b * g⁻¹) = g * (x * b) * g⁻¹ := by group
      _ = g * (b * x) * g⁻¹ := by rw [hx.1]
      _ = g * b * g⁻¹ * (g * x * g⁻¹) := by group
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ ihx ihy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact mul_mem ihx ihy
  | inv x _ ihx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ihx

section E2

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K}
  (hcβ : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) (hβ : ¬ ∃ μ : K, μ ^ 3 = β)

include hcβ hβ in
theorem type3_of_partner (i : ℕ) :
    (∀ μ : K, μ ^ 3 ≠ β) ∧
      (((diagTau hτ ^ i * cβ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 = β • 1 := by
  refine ⟨fun μ hμ => hβ ⟨μ, hμ⟩, ?_⟩
  rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, hcβ]
  exact diagonal_pow_mul_heisC_pow_three hτ β i

include hτ1 hcβ hβ in
theorem thetaSet_comm [Finite K] {b : ProjGenLinGroup (Fin 3) K}
    (hb : b ∈ Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ)) (hb1 : b ≠ 1) :
    ∀ x ∈ thetaSet b, ∀ y ∈ thetaSet b, x * y = y * x := by
  obtain ⟨b', hbb', hb'⟩ := exists_partner hτ hcβ hb hb1
  have hiff : ∀ x : ProjGenLinGroup (Fin 3) K, x * b = b * x ↔ x * b' = b' * x := by
    intro x
    rcases hbb' with rfl | rfl
    · exact Iff.rfl
    · exact comm_iff_comm_inv b x
  rintro x ⟨hxb, hx3⟩ y ⟨hyb, hy3⟩
  rw [hiff] at hxb hyb
  obtain ⟨X, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨Y, rfl⟩ := ProjGenLinGroup.mk_surjective y
  rcases hb' with rfl | ⟨i, rfl⟩
  · exact mk_comm_of_offDiag (offDiag_of_comm_d hτ hτ1 hxb hx3) (offDiag_of_comm_d hτ hτ1 hyb hy3)
  · obtain ⟨hℓ, hB⟩ := type3_of_partner hτ hcβ hβ i
    rw [← map_mul, ← map_mul, commute_of_commute_type3 hℓ hB
      (Res8Hess.commute_of_mk_commute_of_coprime' hxb hx3)
      (Res8Hess.commute_of_mk_commute_of_coprime' hyb hy3)]

include hτ1 hcβ hβ in
theorem torus_facts [Finite K] {R : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hcR : ProjGenLinGroup.mk cβ ∈ Subgroup.normalizer (R : Set (ProjGenLinGroup (Fin 3) K)))
    {b' : ProjGenLinGroup (Fin 3) K}
    (hb' : b' = ProjGenLinGroup.mk (diagTau hτ) ∨
      ∃ i : ℕ, b' = ProjGenLinGroup.mk (diagTau hτ ^ i * cβ))
    {z : ProjGenLinGroup (Fin 3) K} (hzR : z ∈ R)
    (hzC : z ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)))
    (hzb : z * b' = b' * z) (hz1 : z ≠ 1) (hR3 : ∀ x ∈ R, Nat.Coprime 3 (orderOf x)) :
    (∀ g ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)),
      ∀ h ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)), g * h = h * g) ∧
      b' ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) := by
  have hz3 := hR3 z hzR
  rcases hb' with rfl | ⟨i, rfl⟩
  ·
    set C := ProjGenLinGroup.mk cβ with hC
    have hcR' : C⁻¹ ∈ Subgroup.normalizer (R : Set (ProjGenLinGroup (Fin 3) K)) := inv_mem hcR
    have hz'R : C * z * C⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcR z).mp hzR
    have hz''R : C⁻¹ * z * C ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp hcR' z).mp hzR
      rwa [inv_inv] at this
    have hz'C : C * z * C⁻¹ ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) :=
      Res8Hess.mem_centralizer_conj' hcR hzC
    have hz''C : C⁻¹ * z * C ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) := by
      have := Res8Hess.mem_centralizer_conj' hcR' hzC
      rwa [inv_inv] at this
    have hdiag : ∀ G : GL (Fin 3) K, z * ProjGenLinGroup.mk G = ProjGenLinGroup.mk G * z →
        C * z * C⁻¹ * ProjGenLinGroup.mk G = ProjGenLinGroup.mk G * (C * z * C⁻¹) →
        C⁻¹ * z * C * ProjGenLinGroup.mk G = ProjGenLinGroup.mk G * (C⁻¹ * z * C) →
        ∀ i j : Fin 3, i ≠ j → (G : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
      fun G h1 h2 h3 => offDiag_of_comm_conj hτ hτ1 hcβ hzb hz1 hz3 h1 h2 h3
    have hcent : ∀ g ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)),
        ∃ G : GL (Fin 3) K, ProjGenLinGroup.mk G = g ∧
          ∀ i j : Fin 3, i ≠ j → (G : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
      intro g hg
      obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
      have hg' := Subgroup.mem_centralizer_iff.mp hg
      exact ⟨G, rfl, hdiag G (hg' z hzR) (hg' _ hz'R) (hg' _ hz''R)⟩
    refine ⟨fun g hg h hh => ?_, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    · obtain ⟨G, rfl, hG⟩ := hcent g hg
      obtain ⟨H, rfl, hH⟩ := hcent h hh
      exact mk_comm_of_offDiag hG hH
    · obtain ⟨Rm, rfl⟩ := ProjGenLinGroup.mk_surjective r
      have e1 := Subgroup.mem_centralizer_iff.mp hzC _ hr
      have e2 := Subgroup.mem_centralizer_iff.mp hz'C _ hr
      have e3 := Subgroup.mem_centralizer_iff.mp hz''C _ hr
      exact mk_comm_of_offDiag (hdiag Rm e1.symm e2.symm e3.symm) (offDiag_diagTau hτ)
  ·
    obtain ⟨hℓ, hB⟩ := type3_of_partner hτ hcβ hβ i
    refine ⟨fun g hg h hh => ?_, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    · exact (comm_of_comm_type3 hℓ hB hzb hz1 hz3
        (Subgroup.mem_centralizer_iff.mp hg z hzR)).2 h
        (Subgroup.mem_centralizer_iff.mp hh z hzR)
    · exact (comm_of_comm_type3 hℓ hB hzb hz1 hz3
        (Subgroup.mem_centralizer_iff.mp hzC r hr).symm).1

include hτ1 hcβ in
theorem e_facts [Finite K] :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ)) ∧
    Nat.card (Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ) : Subgroup (ProjGenLinGroup (Fin 3) K)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := ProjGenLinGroup.mk (diagTau hτ) with hD
  set C := ProjGenLinGroup.mk cβ with hC
  have hDC : D * C = C * D := mk_d_comm_c hτ hcβ
  have hD3 : D ^ 3 = 1 := mk_d_pow_three hτ
  have hC3 : C ^ 3 = 1 := mk_c_pow_three hcβ
  have hCD : C ∉ Subgroup.zpowers D := mk_c_not_mem hτ hcβ
  have hC1 : C ≠ 1 := fun h => hCD (h ▸ one_mem _)
  have hDo : orderOf D = 3 := orderOf_eq_prime hD3 (mk_d_ne_one hτ hτ1)
  have hCo : orderOf C = 3 := orderOf_eq_prime hC3 hC1
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup hDC x.2
    obtain ⟨k, l, hkl⟩ := Sec4.exists_zpow_mul_of_mem_sup hDC y.2
    change (x : ProjGenLinGroup (Fin 3) K) * y = y * x
    rw [hij, hkl]
    have hc := fun a b : ℤ => (Commute.zpow_zpow hDC a b).eq
    calc D ^ i * C ^ j * (D ^ k * C ^ l) = D ^ i * (C ^ j * D ^ k) * C ^ l := by group
      _ = D ^ i * (D ^ k * C ^ j) * C ^ l := by rw [← hc k j]
      _ = D ^ k * D ^ i * (C ^ j * C ^ l) := by group
      _ = D ^ k * D ^ i * (C ^ l * C ^ j) := by group
      _ = D ^ k * (D ^ i * C ^ l) * C ^ j := by group
      _ = D ^ k * (C ^ l * D ^ i) * C ^ j := by rw [hc i l]
      _ = D ^ k * C ^ l * (D ^ i * C ^ j) := by group
  · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hDC hx
    rw [(Commute.zpow_zpow hDC i j).mul_pow, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, mul_comm (j : ℤ),
      _root_.zpow_mul]
    simp [hD3, hC3]
  · rw [Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hCo hCD (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hDC k).eq)), Nat.card_zpowers, hDo]

include hτ1 hcβ hβ in
theorem exists_thetaP_of_pGroup [Finite K] {r : ℕ} [Fact r.Prime] (hr3 : r ≠ 3)
    {R : Subgroup (ProjGenLinGroup (Fin 3) K)} (hRr : IsPGroup r R) (hR1 : R ≠ ⊥)
    (hER : Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ) ≤
        Subgroup.normalizer (R : Set (ProjGenLinGroup (Fin 3) K))) :
    ∃ b ∈ Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
        Subgroup.zpowers (ProjGenLinGroup.mk cβ), b ≠ 1 ∧
      (∀ x ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)),
        Nat.Coprime 3 (orderOf x) → x ∈ thetaP b) ∧
      ∀ U : Subgroup (ProjGenLinGroup (Fin 3) K),
        U ≤ Subgroup.normalizer (R : Set (ProjGenLinGroup (Fin 3) K)) →
        ¬ 3 ∣ Nat.card U →
        Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
            Subgroup.zpowers (ProjGenLinGroup.mk cβ) ≤
          Subgroup.normalizer (U : Set (ProjGenLinGroup (Fin 3) K)) →
          U ≤ thetaP b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set E := Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
    Subgroup.zpowers (ProjGenLinGroup.mk cβ) with hE
  obtain ⟨hEab, hE9⟩ := e_facts hτ hτ1 hcβ
  have hcE : ProjGenLinGroup.mk cβ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hRnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  have hZnt := hRr.center_nontrivial
  obtain ⟨⟨z₀, hz₀c⟩, hz₀1⟩ := exists_ne (1 : Subgroup.center R)
  set Z := R ⊓ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) with hZ
  have hz₀Z : (z₀ : ProjGenLinGroup (Fin 3) K) ∈ Z := by
    refine ⟨z₀.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.mp hz₀c ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hZ1 : Z ≠ ⊥ := by
    intro hZ0
    rw [hZ0, Subgroup.mem_bot] at hz₀Z
    exact hz₀1 (Subtype.ext (Subtype.ext hz₀Z))
  have hEZ : E ≤ Subgroup.normalizer (Z : Set (ProjGenLinGroup (Fin 3) K)) :=
    Res8Hess.le_normalizer_inf' hER (hER.trans (Res8Hess.normalizer_le_normalizer_centralizer' R))
  have hR3 : ∀ x ∈ R, Nat.Coprime 3 (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hRr ⟨x, hx⟩
    have h1 : orderOf x ∣ r ^ k := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right _
      ((Nat.coprime_primes Nat.prime_three Fact.out).mpr (Ne.symm hr3)))
  have hZ2 : IsPGroup r Z := hRr.to_le inf_le_left
  have hcop : Nat.Coprime 3 (Nat.card Z) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three Fact.out).mpr
      (Ne.symm hr3))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Z hEab (by rw [hE9]; norm_num) hEZ hcop
  obtain ⟨U₀, hU₀, hZU₀⟩ : ∃ U₀ ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
      Z ⊓ Subgroup.centralizer (U₀ : Set (ProjGenLinGroup (Fin 3) K)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hZ1
    rw [← hgen]
    exact iSup₂_eq_bot.mpr hcon
  obtain ⟨hU₀E, hU₀3⟩ := hU₀
  have hU₀nt : Nontrivial U₀ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU₀3]; norm_num)
  obtain ⟨⟨b₀, hbU⟩, hb1⟩ := exists_ne (1 : U₀)
  have hb₀1 : b₀ ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨⟨z, hzZ, hzU⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZU₀
  have hzb₀ : (z : ProjGenLinGroup (Fin 3) K) * b₀ = b₀ * z :=
    (Subgroup.mem_centralizer_iff.mp hzU b₀ hbU).symm
  have hz1' : (z : ProjGenLinGroup (Fin 3) K) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hb₀E : b₀ ∈ E := hU₀E hbU
  obtain ⟨b, hbb₀, hb⟩ := exists_partner hτ hcβ hb₀E hb₀1
  have hbE : b ∈ E := by
    rcases hbb₀ with rfl | rfl
    · exact hb₀E
    · exact inv_mem hb₀E
  have hb1' : b ≠ 1 := by
    rcases hbb₀ with rfl | rfl
    · exact hb₀1
    · exact inv_ne_one.mpr hb₀1
  have hzb : (z : ProjGenLinGroup (Fin 3) K) * b = b * z := by
    rcases hbb₀ with rfl | rfl
    · exact hzb₀
    · exact (comm_iff_comm_inv b₀ _).mp hzb₀
  obtain ⟨hCab, hbC⟩ := torus_facts hτ hτ1 hcβ hβ (hER hcE) hb hzZ.1 hzZ.2 hzb hz1' hR3
  have hb3 : b ^ 3 = 1 := hEab.2 b hbE
  refine ⟨b, hbE, hb1', fun x hx hx3 => mem_thetaP_of (hCab x hx b hbC) hx3,
    fun U hUR hU3 hEU => ?_⟩
  intro u hu
  have hu3 : Nat.Coprime 3 (orderOf u) := Res8Hess.coprime_orderOf_of_mem hU3 hu
  have hbU' : b * u * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hEU hbE) u).mp hu
  set c := u⁻¹ * (b * u * b⁻¹) with hc
  have hcU : c ∈ U := mul_mem (inv_mem hu) hbU'
  have huN : u⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) : Subgroup _) :
        Set (ProjGenLinGroup (Fin 3) K)) :=
    Res8Hess.normalizer_le_normalizer_centralizer' R (inv_mem (hUR hu))
  have hcC : c ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) := by
    have h1 : u⁻¹ * b * u⁻¹⁻¹ ∈ Subgroup.centralizer (R : Set (ProjGenLinGroup (Fin 3) K)) :=
      (Subgroup.mem_normalizer_iff.mp huN b).mp hbC
    have e : c = u⁻¹ * b * u⁻¹⁻¹ * b⁻¹ := by rw [hc]; group
    rw [e]
    exact mul_mem h1 (inv_mem hbC)
  have hcb : c * b = b * c := hCab c hcC b hbC
  have hpow : ∀ n : ℕ, b ^ n * u * (b ^ n)⁻¹ = u * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hbc : b * c ^ n * b⁻¹ = c ^ n := by
        rw [(Commute.pow_left hcb n).eq.symm, mul_inv_cancel_right]
      calc b ^ (n + 1) * u * (b ^ (n + 1))⁻¹ = b * (b ^ n * u * (b ^ n)⁻¹) * b⁻¹ := by
            rw [pow_succ']; group
        _ = b * (u * c ^ n) * b⁻¹ := by rw [ih]
        _ = (b * u * b⁻¹) * (b * c ^ n * b⁻¹) := by group
        _ = u * c * c ^ n := by rw [hbc, hc, mul_inv_cancel_left]
        _ = u * c ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hc3 : c ^ 3 = 1 := by
    have h := hpow 3
    rw [hb3, one_mul, inv_one, mul_one] at h
    have := congrArg (fun x => u⁻¹ * x) h
    simpa using this.symm
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h2 : Nat.Coprime 3 (orderOf c) := Res8Hess.coprime_orderOf_of_mem hU3 hcU
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h2 h1 (dvd_refl _))
  refine mem_thetaP_of ?_ hu3
  have e : b * u * b⁻¹ = u := by
    have := hc1
    rw [hc] at this
    calc b * u * b⁻¹ = u * (u⁻¹ * (b * u * b⁻¹)) := by group
      _ = u := by rw [this, mul_one]
  calc u * b = b * u * b⁻¹ * b := by rw [e]
    _ = b * u := by group

include hτ1 hcβ hβ in
theorem exists_le_thetaP [Finite K] {Y : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hY3 : ¬ 3 ∣ Nat.card Y)
    (hEY : Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ) ≤
        Subgroup.normalizer (Y : Set (ProjGenLinGroup (Fin 3) K))) :
    ∃ b ∈ Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
        Subgroup.zpowers (ProjGenLinGroup.mk cβ), b ≠ 1 ∧ Y ≤ thetaP b := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hE9 := (e_facts hτ hτ1 hcβ).2
  have hE3 : IsPGroup 3 (Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ) : Subgroup (ProjGenLinGroup (Fin 3) K)) :=
    IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  exact Res8Hess.exists_le_of_family hE3 thetaP
    ⟨_, Subgroup.mem_sup_left (Subgroup.mem_zpowers _), mk_d_ne_one hτ hτ1⟩
    (fun b hbE hb1 => (thetaP_facts (thetaSet_comm hτ hτ1 hcβ hβ hbE hb1)).1)
    (fun r _ hr3 R hRr hR1 hER => exists_thetaP_of_pGroup hτ hτ1 hcβ hβ hr3 hRr hR1 hER)
    Y hY3 hEY

include hτ1 hcβ in
theorem eq_one_of_comm_d_c {x : ProjGenLinGroup (Fin 3) K}
    (hxd : x * ProjGenLinGroup.mk (diagTau hτ) = ProjGenLinGroup.mk (diagTau hτ) * x)
    (hxc : x * ProjGenLinGroup.mk cβ = ProjGenLinGroup.mk cβ * x)
    (hx3 : Nat.Coprime 3 (orderOf x)) : x = 1 := by
  obtain ⟨X, rfl⟩ := ProjGenLinGroup.mk_surjective x
  have hXd := Sec17.Proof17Res7.eq_diagonal_of_offDiag (offDiag_of_comm_d hτ hτ1 hxd hx3)
  have hXc := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    (Res8Hess.commute_of_mk_commute_of_coprime' hxc hx3)
  simp only [Units.val_mul] at hXc
  rw [hXd, hcβ, heisC_mul_diagonal] at hXc
  have e10 := congrFun (congrFun hXc 1) 0
  have e21 := congrFun (congrFun hXc 2) 1
  simp [Matrix.diagonal_mul, heisC] at e10 e21
  have hs : (X : Matrix (Fin 3) (Fin 3) K) =
      (X : Matrix (Fin 3) (Fin 3) K) 2 2 • ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Units.val_one]
    conv_lhs => rw [hXd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e21]
  rw [mk_eq_of_coe_eq_smul hs, map_one]

end E2

end CFSG.RankThree.PartTwo.Sec14.L3PGL
