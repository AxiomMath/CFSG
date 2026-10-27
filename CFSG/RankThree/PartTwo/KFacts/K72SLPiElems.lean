module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

theorem exists_slPi_of_isSLThreePiAt {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : IsSLThreePiAt X (2 ^ (3 * n))) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π 2 (3 * n) K ∧
      ModThree π (2 ^ (3 * n)) ∧ Nonempty (X ≃* slPi π 3 (2 ^ (3 * n)) K) := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩⟩ := hX
  · exact ⟨true, K, inferInstance, ⟨Nat.prime_two, by omega, hK⟩, hq, ⟨e⟩⟩
  · exact ⟨false, K, inferInstance, ⟨Nat.prime_two, by omega, hK⟩, hq, ⟨e⟩⟩

theorem mem_center_of_mulEquiv {X M : Type*} [Group X] [Group M] (e : X ≃* M) {x : X}
    (hx : x ∈ Subgroup.center X) : e x ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro m
  obtain ⟨y, rfl⟩ := e.surjective m
  rw [← map_mul, ← map_mul, hx y]

theorem nine_dvd_qSubPi {π : Bool} {n : ℕ} (hq : ModThree π (2 ^ (3 * n))) :
    9 ∣ qSubPi π (2 ^ (3 * n)) := by
  have hcube : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [hcube] at hq ⊢
  have hq₀ := modThree_of_cube hq
  obtain ⟨k, hk⟩ := three_dvd_qSubPi hq₀
  rw [qSubPi_cube_eq hq₀, hk]
  exact ⟨k * (3 * (2 ^ n / 3) ^ 2 + 3 * (2 ^ n / 3) + 1), by ring⟩

section Scalars

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem mem_rootsOfUnity_qSubPi_of_pow_three (hq : ModThree π (p ^ f)) {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) : ζ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  obtain ⟨k, hk⟩ := three_dvd_qSubPi hq
  rw [mem_rootsOfUnity, hk, pow_mul, hζ, one_pow]

theorem torusHom_self_eq_scalar {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    torusHom (ζ, ζ) = GeneralLinearGroup.scalar (Fin 3) ζ := by
  have h : (ζ * ζ)⁻¹ = ζ := inv_eq_of_mul_eq_one_left (by rw [← pow_three]; exact hζ)
  apply Units.ext
  rw [coe_torusHom, GeneralLinearGroup.coe_scalar, scalar_apply]
  dsimp only
  rw [h]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem scalar_mem_slPi_of_pow_three (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) : GeneralLinearGroup.scalar (Fin 3) ζ ∈ slPi π 3 (p ^ f) K := by
  rw [← torusHom_self_eq_scalar hζ]
  exact torusHom_mem_slPi hK (mem_rootsOfUnity_qSubPi_of_pow_three hq hζ)
    (mem_rootsOfUnity_qSubPi_of_pow_three hq hζ)

theorem exists_scalar_of_mem_center (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {z : slPi π 3 (p ^ f) K} (hz : z ∈ Subgroup.center (slPi π 3 (p ^ f) K)) :
    ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ (z : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) ζ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨ζ, hζ⟩ : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)).symm
  exact ⟨ζ, pow_three_eq_one_of_scalar_mem_slPi hπ (by rw [hζ]; exact z.2), hζ.symm⟩

theorem card_center_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (Subgroup.center (slPi π 3 (p ^ f) K)) = 3 := by
  have := hK.finite
  let φ : rootsOfUnity 3 K → Subgroup.center (slPi π 3 (p ^ f) K) := fun ζ =>
    ⟨⟨GeneralLinearGroup.scalar (Fin 3) (ζ : Kˣ), scalar_mem_slPi_of_pow_three hK hq
      ((mem_rootsOfUnity _ _).mp ζ.2)⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (ζ : Kˣ)
          (g : GL (Fin 3) K)).eq⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h := congrArg (fun x : Subgroup.center (slPi π 3 (p ^ f) K) =>
        ((x : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hab
      exact Subtype.ext (scalar_injective_three h)
    · rintro ⟨z, hz⟩
      obtain ⟨ζ, hζ3, hζ⟩ := exists_scalar_of_mem_center hK hq hz
      exact ⟨⟨ζ, (mem_rootsOfUnity _ _).mpr hζ3⟩, Subtype.ext (Subtype.ext hζ.symm)⟩
  rw [← Nat.card_eq_of_bijective φ hφ]
  exact CFSG.LinearGroups.card_rootsOfUnity_of_dvd
    (dvd_trans (three_dvd_qSubPi hq) (qSubPi_dvd hK))

theorem exists_pow_three_eq_of_nine_dvd (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) {ζ : Kˣ} (hζ3 : ζ ^ 3 = 1) :
    ∃ μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K, μ ^ 3 = ζ := by
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  have hT := card_rootsOfUnity_qSubPi hK hq
  obtain ⟨k, hk⟩ := h9
  have hexp : Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / 3 = 3 * k := by
    rw [hT, hk]
    omega
  set t : rootsOfUnity (qSubPi π (p ^ f)) K := ⟨ζ, mem_rootsOfUnity_qSubPi_of_pow_three hq hζ3⟩
  have ht : t ^ (Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / 3) = 1 := by
    rw [hexp]
    apply Subtype.ext
    change ζ ^ (3 * k) = 1
    rw [pow_mul, hζ3, one_pow]
  obtain ⟨s, hs⟩ := exists_pow_eq_of_pow_div
    (by rw [hT, hk]; exact Dvd.intro (3 * k) (by ring)) ht
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

end Scalars

section Swap

variable {K : Type} [Field K]

@[expose] def swapZeroOne : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapZeroOne :
    ((swapZeroOne : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] :=
  rfl

theorem swapZeroOne_sq : (swapZeroOne : GL (Fin 3) K) ^ 2 = 1 := by
  apply Units.ext
  rw [sq, Units.val_mul, coe_swapZeroOne, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem swapZeroOne_ne_one : (swapZeroOne : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp [coe_swapZeroOne] at this

theorem det_swapZeroOne [CharP K 2] :
    ((swapZeroOne : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_swapZeroOne, det_fin_three]
  simp [CharTwo.neg_eq]

theorem swapZeroOne_mem_slPi [CharP K 2] {π : Bool} {f : ℕ}
    (hπ : π = false → UnitaryFieldData 2 f K) : swapZeroOne ∈ slPi π 3 (2 ^ f) K := by
  cases π
  · rw [mem_slPi_false (hπ rfl)]
    refine ⟨det_swapZeroOne, ?_⟩
    rw [coe_swapZeroOne]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply]
  · rw [mem_slPi_true]
    exact det_swapZeroOne

theorem swapZeroOne_mul_torusHom (a : Kˣ) :
    swapZeroOne * torusHom (a, a) = torusHom (a, a) * swapZeroOne := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_swapZeroOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem eq_of_diagonal_commute_cycThree {a b c : K}
    (h : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] =
      diagonal ![a, b, c] * ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    a = b ∧ b = c := by
  rw [coe_cycThree] at h
  have h10 := congrFun (congrFun h 1) 0
  have h21 := congrFun (congrFun h 2) 1
  simp [mul_diagonal, diagonal_mul] at h10 h21
  exact ⟨h10, h21⟩

end Swap

section Elements

variable {π : Bool} {K : Type} [Field K]

theorem exists_uvt_slPi {n : ℕ} (hK : PiField π 2 (3 * n) K) (hq : ModThree π (2 ^ (3 * n)))
    {z : slPi π 3 (2 ^ (3 * n)) K} (hz : z ∈ Subgroup.center (slPi π 3 (2 ^ (3 * n)) K))
    (hz1 : z ≠ 1) :
    ∃ u v t : slPi π 3 (2 ^ (3 * n)) K, u ^ 3 = 1 ∧ v ^ 3 = z ∧ u * v = v * u ∧
      (∀ i j : ℕ, u ^ i * v ^ j ∈ Subgroup.center (slPi π 3 (2 ^ (3 * n)) K) →
        3 ∣ i ∧ 3 ∣ j) ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ t * v = v * t := by
  have hπ : π = false → UnitaryFieldData 2 (3 * n) K := fun h => by subst h; exact hK.unitary
  have := hK.charP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ3, hζz⟩ := exists_scalar_of_mem_center hK hq hz
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    exact hz1 (Subtype.ext (by rw [hζz, map_one]; rfl))
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  obtain ⟨μ, hμT, hμ3⟩ := exists_pow_three_eq_of_nine_dvd hK hq (nine_dvd_qSubPi hq) hζ3
  have hζT := mem_rootsOfUnity_qSubPi_of_pow_three hq hζ3
  set u : slPi π 3 (2 ^ (3 * n)) K :=
    ⟨torusHom (ζ, ζ ^ 2), torusHom_mem_slPi hK hζT (pow_mem hζT 2)⟩
  set v : slPi π 3 (2 ^ (3 * n)) K := ⟨torusHom (μ, μ), torusHom_mem_slPi hK hμT hμT⟩
  have hcoe : ∀ i j : ℕ, ((u ^ i * v ^ j : slPi π 3 (2 ^ (3 * n)) K) : GL (Fin 3) K) =
      torusHom (ζ ^ i * μ ^ j, (ζ ^ 2) ^ i * μ ^ j) := by
    intro i j
    change torusHom (ζ, ζ ^ 2) ^ i * torusHom (μ, μ) ^ j = _
    rw [← map_pow, ← map_pow, ← map_mul, Prod.pow_mk, Prod.pow_mk, Prod.mk_mul_mk]
  refine ⟨u, v, ⟨swapZeroOne, swapZeroOne_mem_slPi hπ⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change torusHom (ζ, ζ ^ 2) ^ 3 = 1
    rw [← map_pow, Prod.pow_mk, hζ3, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hζ3,
      one_pow]
    exact map_one torusHom
  · apply Subtype.ext
    change torusHom (μ, μ) ^ 3 = (z : GL (Fin 3) K)
    rw [← map_pow, Prod.pow_mk, hμ3, hζz, torusHom_self_eq_scalar hζ3]
  · apply Subtype.ext
    change torusHom (ζ, ζ ^ 2) * torusHom (μ, μ) = torusHom (μ, μ) * torusHom (ζ, ζ ^ 2)
    rw [← map_mul, ← map_mul, mul_comm]
  · intro i j hij
    have hc : (cycThree : GL (Fin 3) K) * torusHom (ζ ^ i * μ ^ j, (ζ ^ 2) ^ i * μ ^ j) =
        torusHom (ζ ^ i * μ ^ j, (ζ ^ 2) ^ i * μ ^ j) * cycThree := by
      rw [← hcoe]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hij ⟨cycThree, cycThree_mem_slPi hπ⟩)
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, coe_torusHom] at hc'
    obtain ⟨h1, h2⟩ := eq_of_diagonal_commute_cycThree hc'
    have h1' : ζ ^ i * μ ^ j = (ζ ^ 2) ^ i * μ ^ j := Units.ext h1
    have h2' : (ζ ^ 2) ^ i * μ ^ j = ((ζ ^ i * μ ^ j) * ((ζ ^ 2) ^ i * μ ^ j))⁻¹ := Units.ext h2
    have hi : ζ ^ i = 1 := by
      have h3 := mul_right_cancel h1'
      rw [← pow_mul, mul_comm 2 i, pow_mul, sq] at h3
      exact left_eq_mul.mp h3
    have hi2 : (ζ ^ 2) ^ i = 1 := by rw [← pow_mul, mul_comm, pow_mul, hi, one_pow]
    rw [hi, hi2, one_mul] at h2'
    have h3 : (μ ^ j) ^ 3 = 1 := by
      rw [pow_three]
      exact eq_inv_iff_mul_eq_one.mp h2'
    have hj : ζ ^ j = 1 := by rw [← hμ3, ← pow_mul, mul_comm, pow_mul, h3]
    rw [← hord]
    exact ⟨orderOf_dvd_of_pow_eq_one hi, orderOf_dvd_of_pow_eq_one hj⟩
  · intro h
    exact swapZeroOne_ne_one (congrArg Subtype.val h)
  · apply Subtype.ext
    change (swapZeroOne : GL (Fin 3) K) ^ 2 = 1
    exact swapZeroOne_sq
  · apply Subtype.ext
    change swapZeroOne * torusHom (μ, μ) = torusHom (μ, μ) * swapZeroOne
    exact swapZeroOne_mul_torusHom μ

end Elements

theorem card_center_of_isSLThreePiAt {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * n))) : Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_slPi_of_isSLThreePiAt hn hX
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact card_center_slPi hK hq

theorem exists_uvt_of_isSLThreePiAt {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * n))) {z : X} (hz : z ∈ Subgroup.center X)
    (hz1 : z ≠ 1) :
    ∃ u v t : X, u ^ 3 = 1 ∧ v ^ 3 = z ∧ u * v = v * u ∧
      (∀ i j : ℕ, u ^ i * v ^ j ∈ Subgroup.center X → 3 ∣ i ∧ 3 ∣ j) ∧
      t ≠ 1 ∧ t ^ 2 = 1 ∧ t * v = v * t := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_slPi_of_isSLThreePiAt hn hX
  obtain ⟨u, v, t, hu, hv, huv, hc, ht1, ht2, htv⟩ := exists_uvt_slPi hK hq
    (mem_center_of_mulEquiv e hz) (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
  refine ⟨e.symm u, e.symm v, e.symm t, ?_, ?_, ?_, fun i j hij => hc i j ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hu, map_one]
  · rw [← map_pow, hv, MulEquiv.symm_apply_apply]
  · rw [← map_mul, ← map_mul, huv]
  · have := mem_center_of_mulEquiv e hij
    rwa [map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  · intro h
    exact ht1 (e.symm.injective (h.trans (map_one e.symm).symm))
  · rw [← map_pow, ht2, map_one]
  · rw [← map_mul, ← map_mul, htv]

end CFSG.RankThree.PartTwo.KFacts
