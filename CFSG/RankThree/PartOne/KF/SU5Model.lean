module

public import CFSG.RankThree.CentralLift.EvenScalarCover
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveDiagonalize

public section

namespace CFSG.RankThree.PartOne.KFSU5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCEvenUnitaryFive

theorem exists_su5_iso {Lg : Type} [Group Lg] [Finite Lg] [Group.IsPerfect Lg]
    (hcard : Nat.card (Subgroup.center Lg) = 5) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : Lg ⧸ Subgroup.center Lg ≃* StatedProj (StatedSU 5 (2 ^ f) K)) :
    5 ∣ 2 ^ f + 1 ∧ Nonempty (StatedSU 5 (2 ^ f) K ≃* Lg) := by
  classical
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let η : Lg →* StatedProj (StatedSU 5 (2 ^ f) K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Lg))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center Lg := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (x : Lg ⧸ Subgroup.center Lg) = 1 ↔ x ∈ Subgroup.center Lg
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  have hCp : IsPGroup 5 η.ker := by
    rw [hker]
    exact IsPGroup.of_card (p := 5) (n := 1) (by rw [hcard]; norm_num)
  obtain ⟨⟨φ, hφ, -⟩, hmain⟩ :=
    CFSG.RankThree.CentralLift.even_field_unitary_perfect_central_large_prime_scalar_cover
      (p := 5) Nat.prime_five (by norm_num) hU (n := 5) (by norm_num) η hη hker.le hCp
  obtain ⟨hsurj, hkerD, -, -, ⟨ψ⟩, -, hdvd⟩ := hmain φ hφ
  have hηcard : Nat.card η.ker = 5 := by rw [hker, hcard]
  have h5 : 5 ∣ 2 ^ f + 1 := by
    rw [hηcard] at hdvd
    exact (Nat.dvd_gcd_iff.mp hdvd).2
  refine ⟨h5, ?_⟩
  set D := (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K) with hD
  have hDcard : Nat.card D = 5 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 5)).2.2]
    exact Nat.gcd_eq_left h5
  have hquot : Nat.card (D ⧸ φ.ker.subgroupOf D) = 5 :=
    (Nat.card_congr ψ.toEquiv.symm).trans hηcard
  have hBcard : Nat.card (φ.ker.subgroupOf D) = 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker.subgroupOf D)
    rw [hDcard, hquot] at h1
    omega
  have hBbot : φ.ker.subgroupOf D = ⊥ := Subgroup.card_eq_one.mp hBcard
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxD : x ∈ D := hkerD hx
    have hB : (⟨x, hxD⟩ : D) ∈ φ.ker.subgroupOf D := hx
    rw [hBbot] at hB
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hB)
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

section Diagonal

variable {f : ℕ} {K : Type} [Field K]

theorem unitarySU_le_primeFormUnitary (h : UnitaryFieldData 2 f K) :
    unitarySU 2 f K 5 ≤ primeFormUnitary h (idGram K 5) := fun g hg => by
  have := ((mem_unitarySU_iff h).mp hg).2
  rw [mem_primeFormUnitary]
  simpa [idGram] using this

theorem conj_mem_unitarySU (h : UnitaryFieldData 2 f K) {P : GL (Fin 5) K}
    (hP : P ∈ primeFormUnitary h (idGram K 5)) {g : GL (Fin 5) K} (hg : g ∈ unitarySU 2 f K 5) :
    P * g * P⁻¹ ∈ unitarySU 2 f K 5 := by
  rw [unitarySU_eq_gramSU h 5, mem_gramSU_iff_unitary] at hg ⊢
  refine ⟨mul_mem (mul_mem hP hg.1) (inv_mem hP), ?_⟩
  have h1 := hg.2
  have h2 : ((P * g * P⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det =
      ((P : Matrix (Fin 5) (Fin 5) K)).det * ((g : Matrix (Fin 5) (Fin 5) K)).det *
        ((P⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det := by
    simp only [Units.val_mul, Matrix.det_mul]
  rw [h2, h1, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one]

@[expose] noncomputable def conjSU (h : UnitaryFieldData 2 f K)
    (P : primeFormUnitary h (idGram K 5)) :
    unitarySU 2 f K 5 ≃* unitarySU 2 f K 5 where
  toFun g := ⟨(P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹, conj_mem_unitarySU h P.2 g.2⟩
  invFun g := ⟨(P : GL (Fin 5) K)⁻¹ * g * (P : GL (Fin 5) K), by
    have := conj_mem_unitarySU h (inv_mem P.2) g.2
    simpa using this⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g g' := Subtype.ext (by simp [mul_assoc])

theorem coe_conjSU (h : UnitaryFieldData 2 f K) (P : primeFormUnitary h (idGram K 5))
    (g : unitarySU 2 f K 5) :
    ((conjSU h P g : unitarySU 2 f K 5) : GL (Fin 5) K) =
      (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹ := rfl

theorem exists_diagonal_su5_iso {Lg : Type} [Group Lg] [Finite Lg] [Group.IsPerfect Lg]
    (hcard : Nat.card (Subgroup.center Lg) = 5) (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : Lg ⧸ Subgroup.center Lg ≃* StatedProj (StatedSU 5 (2 ^ f) K))
    (A₀ : Subgroup Lg) (hA₀exp : ∀ a ∈ A₀, a ^ 5 = 1)
    (hA₀comm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hA₀card : Nat.card A₀ = 5 ^ 3) :
    5 ∣ 2 ^ f + 1 ∧ ∃ ψ : unitarySU 2 f K 5 ≃* Lg, ∀ g : unitarySU 2 f K 5, ψ g ∈ A₀ →
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag := by
  classical
  obtain ⟨h5, ⟨ψ₀⟩⟩ := exists_su5_iso hcard hf hK e
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hle := unitarySU_le_primeFormUnitary hU
  set Ã₀ : Subgroup (unitarySU 2 f K 5) := A₀.comap (ψ₀ : unitarySU 2 f K 5 →* Lg) with hÃ₀
  have hmem : ∀ x : unitarySU 2 f K 5, x ∈ Ã₀ ↔ ψ₀ x ∈ A₀ := fun x => Iff.rfl
  have hÃexp : ∀ x ∈ Ã₀, x ^ 5 = 1 := fun x hx =>
    ψ₀.injective (by rw [map_pow, map_one]; exact hA₀exp _ ((hmem x).mp hx))
  have hÃcomm : ∀ x ∈ Ã₀, ∀ y ∈ Ã₀, x * y = y * x := fun x hx y hy =>
    ψ₀.injective (by
      rw [map_mul, map_mul]
      exact hA₀comm _ ((hmem x).mp hx) _ ((hmem y).mp hy))
  have hÃcard : Nat.card Ã₀ = 5 ^ 3 := by
    rw [hÃ₀, Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective ψ₀.symm.injective]
    exact hA₀card
  set G' : Subgroup (primeFormUnitary hU (idGram K 5)) :=
    Ã₀.map (Subgroup.inclusion hle) with hG'
  have hG'card : Nat.card G' = 5 ^ 3 := by
    rw [hG', Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)]
    exact hÃcard
  have hG'mem : ∀ x ∈ G', ∃ x₀ ∈ Ã₀, Subgroup.inclusion hle x₀ = x := fun x hx => by
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp hx
    exact ⟨x₀, hx₀, hx⟩
  have hGcomm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hG'mem y hy
    rw [← map_mul, ← map_mul, hÃcomm x₀ hx₀ y₀ hy₀]
  have hGpow5 : ∀ x ∈ G', x ^ 5 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    rw [← map_pow, hÃexp x₀ hx₀, map_one]
  have hGnc : ¬ IsCyclic G' := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have h1 : orderOf g = Nat.card G' := orderOf_eq_card_of_forall_mem_zpowers hg
    have h2 : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hGpow5 g g.2))
    have h3 := Nat.le_of_dvd (by norm_num) h2
    rw [h1, hG'card] at h3
    norm_num at h3
  have hGpow : ∀ x ∈ G', x ^ 5 ∈ idScalarKernel hU 5 := fun x hx => by
    rw [hGpow5 x hx]; exact one_mem _
  obtain ⟨P, hP⟩ := exists_unitary_diagonalizing hU h5 G' hGcomm hGnc hGpow
  refine ⟨h5, (conjSU hU P).trans ψ₀, fun g hg => ?_⟩
  have hx₀ : conjSU hU P g ∈ Ã₀ := hg
  have hdiag := hP _ (Subgroup.mem_map.mpr ⟨_, hx₀, rfl⟩)
  have : (((P⁻¹ * Subgroup.inclusion hle (conjSU hU P g) * P :
      primeFormUnitary hU (idGram K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    congr 1
    simp [coe_conjSU, mul_assoc]
  rw [this] at hdiag
  exact hdiag

end Diagonal

end CFSG.RankThree.PartOne.KFSU5
