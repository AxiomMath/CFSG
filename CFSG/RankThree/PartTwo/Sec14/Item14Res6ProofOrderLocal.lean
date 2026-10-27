module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofOrderTools
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.RankThree.Asc83Table.Reduction

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Res6Order

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem factorization_three : (604800 : ℕ).factorization 3 = 3 :=
  CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num) (by norm_num)

theorem exists_sylow_le (hcard : Nat.card X = 604800) (H : Subgroup X)
    (h27 : 27 ∣ Nat.card H) : ∃ P : Sylow 3 X, (P : Subgroup X) ≤ H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 3)
    (by norm_num; exact h27)
  refine ⟨Sylow.ofCard (K.map H.subtype) ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hK, hcard, factorization_three]
  · exact Subgroup.map_subtype_le K

theorem card_sylow_center (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) :
    Nat.card (P : Subgroup X) = 27 ∧
      Nat.card ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :
        Subgroup X) = 3 := by
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  exact ⟨hHeis.2.1, (j2_sylow_facts h415 hX P).1⟩

theorem le_of_nine_dvd (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {Q : Subgroup X}
    (hQP : Q ≤ P) (h9 : 9 ∣ Nat.card Q) :
    (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) ≤ Q := by
  have h27 := (card_sylow_center h415 hX P).1
  have hdvd : Nat.card Q ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hQP
  have hQ : Nat.card Q = 9 ∨ Nat.card Q = 27 := by
    have h27' : (27 : ℕ) = 3 ^ 3 := by norm_num
    rw [h27'] at hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hk'] at h9 ⊢
    interval_cases k <;> simp_all
  rcases hQ with hQ9 | hQ27
  · exact KFacts.KS14.j2_inf_centralizer_le_of_card_nine h415 hX P hQP hQ9
  · have hQeq : Q = P := Subgroup.eq_of_le_of_card_ge hQP (by rw [hQ27, h27])
    rw [hQeq]
    exact inf_le_left

theorem conjugate_eq_of_le_normalizer (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {h : X}
    (hK : conjugate ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) h ≤
      Subgroup.normalizer
        (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
          Set X)) :
    conjugate ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) h =
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  have hZ3 : Nat.card Z = 3 := (j2_sylow_facts h415 hX P).1
  have hwc : ∀ g : X, conjugate Z g ≤ P → conjugate Z g = Z := (j2_sylow_facts h415 hX P).2.1
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hKp : IsPGroup 3 (conjugate Z h) :=
    IsPGroup.of_card (n := 1) (by rw [card_conjugate, hZ3, pow_one])
  obtain ⟨P', hP'⟩ := (hKp.to_sup_of_normal_right' hZp hK).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P'
  have hP'eq : (P' : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_sylow_smul_eq_map]
  have h1 : conjugate Z g = Z :=
    hwc g (conjugate_le_of_le_map (hP'eq ▸ le_sup_right.trans hP'))
  have h2 : conjugate (conjugate Z h) g = Z := by
    rw [conjugate_conjugate]
    exact hwc (h * g) (by
      rw [← conjugate_conjugate]
      exact conjugate_le_of_le_map (hP'eq ▸ le_sup_left.trans hP'))
  exact conjugate_injective (h2.trans h1.symm)

theorem not_nine_dvd_of_le_centralizer
    (hC9 : ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E)
    {u : X} (hu1 : u ≠ 1) (hu3 : ¬ 3 ∣ orderOf u) {Q : Subgroup X}
    (hQ : Q ≤ Subgroup.centralizer ({u} : Set X)) : ¬ 9 ∣ Nat.card Q := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := Q) 3 (n := 2)
    (by norm_num; exact h9)
  set E := E₀.map Q.subtype with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective Q.subtype_injective, hE₀]
    norm_num
  have huE : u ∈ E := by
    refine hC9 E hE9 (Subgroup.mem_centralizer_iff.mpr fun e he => ?_)
    have heQ : e ∈ Q := Subgroup.map_subtype_le E₀ he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQ heQ)
  have hu9 : u ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := E) (x := ⟨u, huE⟩)
    rw [hE9] at h
    exact congrArg Subtype.val h
  have hdvd : orderOf u ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num; exact hu9)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exact hu1 (orderOf_eq_one_iff.mp (by simpa using hk'))
  · exact hu3 (hk' ▸ dvd_refl _)
  · exact hu3 (hk' ▸ dvd_pow_self 3 two_ne_zero)

theorem card_modEq_one_of_le_normalizer (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hC9 : ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E)
    (P : Sylow 3 X) {U : Subgroup X} (hU3 : ¬ 3 ∣ Nat.card U)
    (hPU : (P : Subgroup X) ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card U ≡ 1 [MOD 9] := by
  classical
  have h27 := (card_sylow_center h415 hX P).1
  have hmem : ∀ (p : (P : Subgroup X)) (u : U), (p : X) * u * (p : X)⁻¹ ∈ U := fun p u =>
    (Subgroup.mem_normalizer_iff.mp (hPU p.2) u).mp u.2
  let _ : MulAction (P : Subgroup X) U :=
    { smul := fun p u => ⟨(p : X) * u * (p : X)⁻¹, hmem p u⟩
      one_smul := fun u => Subtype.ext (by
        change ((1 : (P : Subgroup X)) : X) * u * ((1 : (P : Subgroup X)) : X)⁻¹ = u
        simp)
      mul_smul := fun p q u => Subtype.ext (by
        change ((p : X) * q) * u * ((p : X) * q)⁻¹ =
          (p : X) * ((q : X) * u * (q : X)⁻¹) * (p : X)⁻¹
        group) }
  refine card_modEq_one_of_orbit_dvd (G := (P : Subgroup X)) (1 : U) (fun p => Subtype.ext (by
    change (p : X) * 1 * (p : X)⁻¹ = 1
    group)) fun u hu => ?_
  set T := MulAction.stabilizer (P : Subgroup X) u with hT
  have hTC : T.map (P : Subgroup X).subtype ≤ Subgroup.centralizer ({(u : X)} : Set X) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (t : X) * u * (t : X)⁻¹ = u := congrArg Subtype.val ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (t : X) * u = (t : X) * u * (t : X)⁻¹ * t := by group
      _ = u * t := by rw [h1]
  have hu1 : (u : X) ≠ 1 := fun h => hu (Subtype.ext h)
  have hu3 : ¬ 3 ∣ orderOf (u : X) := by
    intro h
    apply hU3
    rw [Subgroup.orderOf_coe] at h
    exact h.trans (orderOf_dvd_natCard u)
  have hT9 : ¬ 9 ∣ Nat.card T := by
    have h := not_nine_dvd_of_le_centralizer hC9 hu1 hu3 hTC
    rwa [Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective] at h
  have horb : Nat.card (MulAction.orbit (P : Subgroup X) u) * Nat.card T = 27 := by
    have h1 := MulAction.index_stabilizer (P : Subgroup X) u
    rw [← Nat.card_coe_set_eq] at h1
    rw [← h1, ← h27, mul_comm, ← hT]
    exact T.card_mul_index
  have hTd : Nat.card T ∣ 27 := Dvd.intro_left _ horb
  have h27' : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27'] at hTd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hTd
  rw [hk'] at horb hT9
  interval_cases k
  · exact ⟨3, by omega⟩
  · exact ⟨1, by omega⟩
  · exact absurd (dvd_refl _) hT9
  · exact absurd ⟨3, by norm_num⟩ hT9

theorem card_dvd_of_isPGroup_two (hcard : Nat.card X = 604800) {U : Subgroup X}
    (hU : IsPGroup 2 U) : Nat.card U ∣ 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hU.exists_card_eq
  have hdvd : 2 ^ j ∣ 2 ^ 7 * 4725 := by
    rw [← hj, show (2 : ℕ) ^ 7 * 4725 = 604800 by norm_num, ← hcard]
    exact Subgroup.card_subgroup_dvd_card U
  rw [hj]
  exact (Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 4725)) hdvd)

theorem false_of_le_normalizer_isPGroup_two (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hC9 : ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E)
    (P : Sylow 3 X) {U : Subgroup X} (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hPU : (P : Subgroup X) ≤ Subgroup.normalizer (U : Set X)) : False := by
  have hcard : Nat.card X = 604800 := KFacts.KS14.card_eq_of_j2 hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h27 := (card_sylow_center h415 hX P).1
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    obtain ⟨j, hj⟩ := hU2.exists_card_eq
    rw [hj] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmod := card_modEq_one_of_le_normalizer h415 hX hC9 P hU3 hPU
  have hU64 : Nat.card U = 64 := by
    have hdvd := card_dvd_of_isPGroup_two hcard hU2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU1 (Subgroup.eq_bot_of_card_eq U (by simpa using hk'))
    rw [hk'] at hmod ⊢
    unfold Nat.ModEq at hmod
    interval_cases k <;> simp_all
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := (P : Subgroup X)) 3 (n := 2)
    (by rw [h27]; norm_num)
  set A := A₀.map (P : Subgroup X).subtype with hA
  have hAP : A ≤ P := Subgroup.map_subtype_le A₀
  have hA9 : Nat.card A = 9 := by
    rw [hA, Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective, hA₀]
    norm_num
  obtain ⟨-, -, -, -, h5⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨S, -, hSset, hS3, ⟨T, ⟨eT⟩⟩, -⟩ := h5 A ⟨hAP, hA9⟩
  have hS64 : Nat.card S = 64 := by
    rw [Nat.card_congr eT.toEquiv, Sylow.card_eq_multiplicity, KFacts.KS14.card_projSL_three_four,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_two
        (show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num) (by norm_num)]
    norm_num
  have hUinv : U ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hU2, hAP.trans hPU⟩
  obtain ⟨M, hUM, hMmax⟩ := Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups ⊤ A (piOf 2)))
    hUinv
  have hMmem : M ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) := hMmax
  rw [hSset] at hMmem
  obtain ⟨x₀, hx₀, rfl⟩ := hMmem
  have hUeq : U = conjugate S x₀ :=
    Subgroup.eq_of_le_of_card_ge hUM (by rw [card_conjugate, hS64, hU64])
  have himage : (conjugate S) '' ((P : Subgroup X) : Set X) = {U} := by
    ext M'
    simp only [Set.mem_image, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have e : conjugate S x = conjugate (conjugate S x₀) (x₀⁻¹ * x) := by
        rw [conjugate_conjugate, mul_inv_cancel_left]
      rw [e, ← hUeq]
      exact conjugate_eq_of_mem_normalizer (hPU (mul_mem (inv_mem hx₀) hx))
    · rintro rfl
      exact ⟨x₀, hx₀, hUeq.symm⟩
  rw [hSset, himage, Set.ncard_singleton] at hS3
  omega

theorem card_normalizer_center (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) :
    Nat.card (Subgroup.normalizer
      (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
        Set X)) = 2160 := by
  obtain ⟨-, -, ⟨-, -, ⟨eN⟩⟩, -⟩ := h415 X hX P _ rfl _ rfl
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hZ3 : Nat.card Z = 3 := (j2_sylow_facts h415 hX P).1
  have hPGL : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2)) = 720 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := CFSG.GorensteinWalter.pgl2_card_formula (GaloisField 3 2)
    rw [GaloisField.card 3 2 (by norm_num)] at h
    rw [h]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Z.subgroupOf (Subgroup.normalizer (Z : Set X))), Nat.card_congr eN.toEquiv, hPGL,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hZ3]

end Res6Order

end CFSG.RankThree.PartTwo.Sec14
