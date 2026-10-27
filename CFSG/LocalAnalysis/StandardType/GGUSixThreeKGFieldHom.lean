module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

private theorem conj_scalar_fix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : GL ι K) (c : Kˣ) :
    MulAut.conj A (GeneralLinearGroup.scalar ι c) = GeneralLinearGroup.scalar ι c := by
  rw [MulAut.conj_apply, ← CFSG.StandardType.TypeA.PGLTor.scalar_mul_comm c A, mul_assoc,
    mul_inv_cancel, mul_one]

private theorem conj_of_scalar_fix {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Kˣ)
    (X : GL ι K) : MulAut.conj (GeneralLinearGroup.scalar ι c) X = X := by
  rw [MulAut.conj_apply, CFSG.StandardType.TypeA.PGLTor.scalar_mul_comm c X, mul_assoc,
    mul_inv_cancel, mul_one]

private theorem conj_eq_of_scalar_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {N M : GL ι K}
    {t : Kˣ} (h : GeneralLinearGroup.scalar ι t = N * M * (M * N)⁻¹) :
    MulAut.conj N M = GeneralLinearGroup.scalar ι t * M := by
  rw [MulAut.conj_apply]
  calc N * M * N⁻¹ = (N * M * (M * N)⁻¹) * M := by group
    _ = GeneralLinearGroup.scalar ι t * M := by rw [← h]

private theorem mul_eq_of_conj_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {N M : GL ι K}
    {t : Kˣ} (h : MulAut.conj N M = GeneralLinearGroup.scalar ι t * M) :
    N * M = GeneralLinearGroup.scalar ι t * (M * N) := by
  rw [MulAut.conj_apply] at h
  calc N * M = N * M * N⁻¹ * N := by group
    _ = (GeneralLinearGroup.scalar ι t * M) * N := by rw [h]
    _ = GeneralLinearGroup.scalar ι t * (M * N) := by rw [mul_assoc]

private theorem conj_mul_step {ι : Type*} [Fintype ι] [DecidableEq ι] {N N' M : GL ι K}
    {t t' : Kˣ} (ht : MulAut.conj N M = GeneralLinearGroup.scalar ι t * M)
    (ht' : MulAut.conj N' M = GeneralLinearGroup.scalar ι t' * M) :
    MulAut.conj (N * N') M = GeneralLinearGroup.scalar ι (t * t') * M := by
  rw [map_mul, MulAut.mul_apply, ht', map_mul, conj_scalar_fix, ht, ← mul_assoc, ← map_mul,
    mul_comm t' t]

private theorem scalar_eq_of_conj_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N M : GL ι K} {t t' : Kˣ} (ht : MulAut.conj N M = GeneralLinearGroup.scalar ι t * M)
    (ht' : MulAut.conj N M = GeneralLinearGroup.scalar ι t' * M) : t = t' :=
  CFSG.StandardType.TypeA.PGLTor.eq_of_scalar_mul_eq (x := M) (by rw [← ht, ← ht'])

theorem exists_unitary_lift [Finite K] (hKd : UnitaryFieldData 2 n K)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))}
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    {a : MulAut (LargeEvenProj (unitarySU 2 n K 6))} (ha : a ∈ Ab) :
    ∃ (N : GL (Fin 6) K)
      (hN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      N ∈ primeFormUnitary hKd (idGram K 6) ∧
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hN⟩ = a := by
  classical
  have hgu : LargeEvenGUSet (Fin 6) K (2 ^ n) ⊆
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    gu_subset_normalizer (d := 6) hKd
  obtain ⟨M', hM'gu, hM'eq⟩ := TableB.exists_eq_projConj hgu (hAbI a ha)
  obtain ⟨u, hu⟩ := TableBU63.exists_unitary_of_gu hKd hM'gu
  have hsN : GeneralLinearGroup.scalar (Fin 6) u ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableB.scalar_mem_normalizer _ ⟨u, rfl⟩
  have hYN : GeneralLinearGroup.scalar (Fin 6) u * M' ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ hsN (hgu hM'gu)
  refine ⟨GeneralLinearGroup.scalar (Fin 6) u * M', hYN, hu, ?_⟩
  have e : (⟨GeneralLinearGroup.scalar (Fin 6) u * M', hYN⟩ :
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
      ⟨GeneralLinearGroup.scalar (Fin 6) u, hsN⟩ * ⟨M', hgu hM'gu⟩ := rfl
  rw [e, map_mul, TableB.projConj_of_scalar _ ⟨u, rfl⟩, one_mul]
  exact hM'eq.symm

theorem exists_commChar [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))}
    (hAb : CFSG.Open.IsElemAbelian 3 Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    {M : GL (Fin 6) K} (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hMA : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ ∈ Ab) :
    ∃ χ : Ab →* Kˣ, (∀ a, χ a ^ 3 = 1) ∧
      ∀ (a : Ab) (N : GL (Fin 6) K)
        (hN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hN⟩ =
            (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) →
          N * M = GeneralLinearGroup.scalar (Fin 6) (χ a) * (M * N) := by
  classical
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 := congrArg Prod.fst he
    simp only at h1
    omega
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set NN := Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) with hNN
  set ρ := TableB.projConj (unitarySU 2 n K 6) with hρ
  have hgu : LargeEvenGUSet (Fin 6) K (2 ^ n) ⊆ NN := gu_subset_normalizer (d := 6) hKd
  let Q : NN → Kˣ → Prop := fun N t =>
    MulAut.conj (N : GL (Fin 6) K) M = GeneralLinearGroup.scalar (Fin 6) t * M
  have hQ_exists : ∀ (N : NN), ρ N ∈ Ab → ∃ t : Kˣ, Q N t := by
    intro N hNA
    have hcomm : ρ (N * ⟨M, hMN⟩) = ρ (⟨M, hMN⟩ * N) := by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAb hNA hMA
    have h1 : ρ ((N * ⟨M, hMN⟩) * (⟨M, hMN⟩ * N)⁻¹) = 1 := by
      rw [map_mul, map_inv, hcomm, mul_inv_cancel]
    obtain ⟨t, ht⟩ :=
      TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq hp3 hpq h1
    refine ⟨t, ?_⟩
    have e : (((N * ⟨M, hMN⟩) * (⟨M, hMN⟩ * N)⁻¹ : NN) : GL (Fin 6) K) =
        (N : GL (Fin 6) K) * M * (M * (N : GL (Fin 6) K))⁻¹ := rfl
    rw [e] at ht
    exact conj_eq_of_scalar_eq ht
  have hQ_congr : ∀ (N N' : NN), ρ N = ρ N' → ∀ {t t' : Kˣ},
      Q N t → Q N' t' → t = t' := by
    intro N N' hNN' t t' ht ht'
    have h1 : ρ (N' * N⁻¹) = 1 := by rw [map_mul, map_inv, hNN', mul_inv_cancel]
    obtain ⟨s, hs⟩ :=
      TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq hp3 hpq h1
    have hs' : (N' : GL (Fin 6) K) =
        GeneralLinearGroup.scalar (Fin 6) s * (N : GL (Fin 6) K) := by
      rw [hs]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hQN' : Q N' t := by
      show MulAut.conj (N' : GL (Fin 6) K) M = GeneralLinearGroup.scalar (Fin 6) t * M
      rw [hs', map_mul, MulAut.mul_apply, conj_of_scalar_fix, ht]
    exact scalar_eq_of_conj_eq hQN' ht'
  have hlift : ∀ a : Ab, ∃ N : NN, ρ N = (a : MulAut _) := by
    intro a
    obtain ⟨N, hNgu, hNeq⟩ := TableB.exists_eq_projConj hgu (hAbI a a.2)
    exact ⟨⟨N, hgu hNgu⟩, hNeq.symm⟩
  let lift : Ab → NN := fun a => Classical.choose (hlift a)
  have lift_spec : ∀ a, ρ (lift a) = (a : MulAut _) := fun a => Classical.choose_spec (hlift a)
  have lift_mem : ∀ a, ρ (lift a) ∈ Ab := fun a => by rw [lift_spec a]; exact a.2
  let χ₀ : Ab → Kˣ := fun a => Classical.choose (hQ_exists (lift a) (lift_mem a))
  have χ₀_spec_lift : ∀ a, Q (lift a) (χ₀ a) := fun a =>
    Classical.choose_spec (hQ_exists (lift a) (lift_mem a))
  have χ₀_spec : ∀ (a : Ab) (N : NN), ρ N = (a : MulAut _) → Q N (χ₀ a) := by
    intro a N hN
    obtain ⟨t, ht⟩ := hQ_exists N (by rw [hN]; exact a.2)
    have hteq : t = χ₀ a :=
      hQ_congr N (lift a) (by rw [hN, lift_spec a]) ht (χ₀_spec_lift a)
    rwa [hteq] at ht
  have hmul : ∀ a b : Ab, χ₀ (a * b) = χ₀ a * χ₀ b := by
    intro a b
    have hProd : Q (lift a * lift b) (χ₀ (a * b)) := by
      apply χ₀_spec
      rw [map_mul, lift_spec a, lift_spec b, Subgroup.coe_mul]
    have hCalc : Q (lift a * lift b) (χ₀ a * χ₀ b) := by
      show MulAut.conj ((lift a * lift b : NN) : GL (Fin 6) K) M =
        GeneralLinearGroup.scalar (Fin 6) (χ₀ a * χ₀ b) * M
      rw [Subgroup.coe_mul]
      exact conj_mul_step (χ₀_spec_lift a) (χ₀_spec_lift b)
    exact hQ_congr (lift a * lift b) (lift a * lift b) rfl hProd hCalc
  let χ : Ab →* Kˣ := MonoidHom.mk' χ₀ hmul
  refine ⟨χ, ?_, ?_⟩
  · intro a
    have ha3 : a ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hAb.2 (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) a.2
    calc χ a ^ 3 = χ (a ^ 3) := (map_pow χ a 3).symm
      _ = χ 1 := by rw [ha3]
      _ = 1 := map_one χ
  · intro a N hN hprojN
    have hQN : Q ⟨N, hN⟩ (χ a) := χ₀_spec a ⟨N, hN⟩ hprojN
    exact mul_eq_of_conj_eq hQN

theorem exists_ne_one_ker_two {H : Type*} [Group H] (hH : Nat.card H = 27) (χ₁ χ₂ : H →* Kˣ)
    (h₁ : ∀ h, χ₁ h ^ 3 = 1) (h₂ : ∀ h, χ₂ h ^ 3 = 1) :
    ∃ h : H, h ≠ 1 ∧ χ₁ h = 1 ∧ χ₂ h = 1 := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  let ψ : H →* Kˣ × Kˣ := χ₁.prod χ₂
  have hle9 : Nat.card ψ.range ≤ 9 := by
    set S : Finset K := (Polynomial.nthRoots 3 (1 : K)).toFinset with hSdef
    have hS : S.card ≤ 3 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
    have hmem : ∀ x : ψ.range,
        (((x : Kˣ × Kˣ).1 : K) ∈ S ∧ ((x : Kˣ × Kˣ).2 : K) ∈ S) := by
      intro x
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp x.2
      have hga : (x : Kˣ × Kˣ).1 = χ₁ g := by
        simpa [ψ, MonoidHom.prod_apply] using (congrArg Prod.fst hg).symm
      have hgb : (x : Kˣ × Kˣ).2 = χ₂ g := by
        simpa [ψ, MonoidHom.prod_apply] using (congrArg Prod.snd hg).symm
      refine ⟨?_, ?_⟩
      · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
        rw [hga, ← Units.val_pow_eq_pow_val, h₁ g, Units.val_one]
      · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
        rw [hgb, ← Units.val_pow_eq_pow_val, h₂ g, Units.val_one]
    let f : ψ.range → ↥S × ↥S := fun x =>
      (⟨((x : Kˣ × Kˣ).1 : K), (hmem x).1⟩, ⟨((x : Kˣ × Kˣ).2 : K), (hmem x).2⟩)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have h1 : (((x : Kˣ × Kˣ).1 : K)) = (((y : Kˣ × Kˣ).1 : K)) :=
        congrArg (fun z : ↥S × ↥S => ((z.1 : ↥S) : K)) hxy
      have h2 : (((x : Kˣ × Kˣ).2 : K)) = (((y : Kˣ × Kˣ).2 : K)) :=
        congrArg (fun z : ↥S × ↥S => ((z.2 : ↥S) : K)) hxy
      exact Prod.ext (Units.ext h1) (Units.ext h2)
    calc Nat.card ψ.range ≤ Nat.card (↥S × ↥S) := Nat.card_le_card_of_injective f hf
      _ = S.card * S.card := by simp [Nat.card_prod]
      _ ≤ 3 * 3 := Nat.mul_le_mul hS hS
      _ = 9 := by norm_num
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = 27 := by
    rw [Subgroup.card_ker_mul_card_range, hH]
  have hker3 : 3 ≤ Nat.card ψ.ker := by
    have hle : 27 ≤ Nat.card ψ.ker * 9 := by
      rw [← hcard]
      exact Nat.mul_le_mul_left _ hle9
    omega
  have hne : ψ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hker3
    omega
  obtain ⟨⟨h, hhker⟩, hh1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have h2 : (χ₁ h, χ₂ h) = (1, 1) := by
    have := MonoidHom.mem_ker.mp hhker
    simpa [ψ, MonoidHom.prod_apply] using this
  exact ⟨h, fun h1 => hh1 (Subtype.ext h1), (Prod.ext_iff.mp h2).1, (Prod.ext_iff.mp h2).2⟩

theorem card_le_nine {G : Type*} [Group G] (Ab : Subgroup G) (u v : G)
    (h : ∀ a ∈ Ab, ∃ k j : ℕ, k < 3 ∧ j < 3 ∧ a = u ^ k * v ^ j) : Nat.card Ab ≤ 9 := by
  classical
  let f : Fin 3 × Fin 3 → G := fun p => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ)
  have hsurj : Function.Surjective
      (fun p : {p : Fin 3 × Fin 3 // f p ∈ Ab} => (⟨f p, p.2⟩ : Ab)) := by
    intro a
    obtain ⟨k, j, hk, hj, ha⟩ := h a a.2
    refine ⟨⟨(⟨k, hk⟩, ⟨j, hj⟩), ?_⟩, ?_⟩
    · have hfk : f (⟨k, hk⟩, ⟨j, hj⟩) = (a : G) := by simp [f, ha]
      rw [hfk]; exact a.2
    · apply Subtype.ext
      simp [f, ha]
  calc Nat.card Ab ≤ Nat.card {p : Fin 3 × Fin 3 // f p ∈ Ab} :=
        Nat.card_le_card_of_surjective _ hsurj
    _ ≤ Nat.card (Fin 3 × Fin 3) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = 9 := by simp [Nat.card_eq_fintype_card]

end CFSG.StandardType.UnitSixThreeKG

end
