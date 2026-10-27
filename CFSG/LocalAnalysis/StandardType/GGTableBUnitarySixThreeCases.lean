module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningHermitian

public section

namespace CFSG.StandardType

namespace TableBU63

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel TableBUD TableBUE TypeA.PGLTor

section Central

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

theorem isToral_of_central [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x)
    (hall : ∀ x ∈ G, ∃ c : Kˣ, x ^ p = GeneralLinearGroup.scalar ι (c ^ p)) : IsToral G := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp hpK
  set H₁ : Set (GL ι K) := {y | y ∈ G ∧ y ^ p = 1} with hH₁
  have hH₁fin : Finite H₁ := Subtype.finite
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ H₁ (fun x hx y hy => hcent y hy.1 hy.2 x hx.1)
    (fun x hx => hx.2)
  refine ⟨A₀, fun x hx i j hij => ?_⟩
  obtain ⟨c, hc⟩ := hall x hx
  set y := GeneralLinearGroup.scalar ι c⁻¹ * x with hy
  have hyH : y ∈ H₁ := ⟨G.mul_mem (hG.scalar_mem _) hx, pow_eq_one_of_pow_eq_scalar_pow hc⟩
  have hxy : x = GeneralLinearGroup.scalar ι c * y := by
    rw [hy, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hxy]
  change conjMatrix A₀ _ i j = 0
  rw [conjMatrix_scalar_mul, Matrix.smul_apply,
    show conjMatrix A₀ y i j = 0 from hA₀ y hyH i j hij, smul_zero]

end Central

section Unitary

variable {K : Type} [Field K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem exists_unitary_of_gu {M : GL (Fin d) K} (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin d) u * M ∈ primeFormUnitary h (idGram K d) := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  have hbar : h.bar μ = μ := by rw [UnitaryFieldData.bar_apply]; exact hμq
  obtain ⟨u₀, hu₀⟩ := CFSG.RankThree.PartOne.KCUnitaryHerm.exists_bar_mul_eq h hbar
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hu₀
    exact hμ0 hu₀.symm
  refine ⟨(Units.mk0 u₀ hu₀0)⁻¹, ?_⟩
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one, Units.val_mul,
    GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hmap : (u₀⁻¹ • (M : Matrix (Fin d) (Fin d) K)).map h.bar =
      h.bar u₀⁻¹ • (M : Matrix (Fin d) (Fin d) K).map h.bar := by
    ext i j
    simp
  rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_pow_eq_map_bar h,
    hμ, smul_smul, map_inv₀]
  have hb0 : h.bar u₀ ≠ 0 := (map_ne_zero h.bar).mpr hu₀0
  have e : h.bar u₀⁻¹ * u₀⁻¹ * μ = 1 := by
    rw [map_inv₀, ← hu₀]
    field_simp
  rw [show (h.bar u₀)⁻¹ * u₀⁻¹ * μ = h.bar u₀⁻¹ * u₀⁻¹ * μ by rw [map_inv₀], e, one_smul]

end Unitary

section Cases

variable {K : Type} [Field K] [Finite K] {n : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
theorem scalar_mul_pow {d : ℕ} (u : Kˣ) (M : GL (Fin d) K) (k : ℕ) :
    (GeneralLinearGroup.scalar (Fin d) u * M) ^ k =
      GeneralLinearGroup.scalar (Fin d) (u ^ k) * M ^ k := by
  rw [(TypeA.PGLTor.commute_scalar u M).mul_pow k, map_pow]

include h in
theorem fieldType_or_heis (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))} (hAb : IsElemAbelian 3 Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    (hcard : 3 ^ 3 ≤ Nat.card Ab)
    (hnofr : ¬ ∃ P ∈ primeFormUnitary h (idGram K 6), ∀ a ∈ Ab, ∃ (M : GL (Fin 6) K)
      (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer h hM⟩) :
    (∃ (M : GL (Fin 6) K)
        (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) (l : Kˣ),
      M ∈ primeFormUnitary h (idGram K 6) ∧ M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l ∧
      (∀ c : Kˣ, c ^ 3 ≠ l) ∧ TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ ∈ Ab) ∨
    (∃ (x y z : GL (Fin 6) K)
      (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
      (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
      (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) (ζ : Kˣ),
      x ∈ primeFormUnitary h (idGram K 6) ∧ y ∈ primeFormUnitary h (idGram K 6) ∧
      z ∈ primeFormUnitary h (idGram K 6) ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈ Ab ∧
      x ^ 3 = 1 ∧ z ^ 3 = 1 ∧ ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
      x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x) ∧ x * z = z * x ∧ y * z = z * y ∧
      z ∉ LargeEvenScalars (Fin 6) K) := by
  classical
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hN := gu_subset_normalizer (d := 6) h
  set NN := Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) with hNN
  set ρ := TableB.projConj (unitarySU 2 n K 6) with hρ
  set N₀ : Subgroup NN := Ab.comap ρ with hN₀
  set χ : NN →* MulAut (projectiveSL 6 K) := (conjAut 6 K).comp NN.subtype with hχ
  set X := N₀.map χ with hX
  have hscal : ∀ M, ρ M = 1 → χ M = 1 := by
    intro M hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hXab : IsElemAbelian 3 X := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hAb hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (by rw [map_pow]; exact hAb.2 _ hM)
  have hXU : ∀ x ∈ X, ∃ M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n), conjAut 6 K M = x := by
    rintro _ ⟨M, hM, rfl⟩
    obtain ⟨M', hM'gu, hM'eq⟩ := TableB.exists_eq_projConj hN (hAbI _ hM)
    refine ⟨M', hM'gu, ?_⟩
    have hM'eq' : ρ M = ρ ⟨M', hN hM'gu⟩ := hM'eq
    have h1 : ρ ((⟨M', hN hM'gu⟩ : NN)⁻¹ * M) = 1 := by
      rw [map_mul, map_inv, hM'eq', inv_mul_cancel]
    have h2 := hscal _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hlift : ∀ a : Ab, ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      (a : MulAut _) = ρ ⟨M, hN hM⟩ := fun a => TableB.exists_eq_projConj hN (hAbI a a.2)
  choose Mf hMf hMfeq using hlift
  have hMN : ∀ a : Ab, (⟨Mf a, hN (hMf a)⟩ : NN) ∈ N₀ := fun a => by
    show ρ _ ∈ Ab
    rw [← hMfeq a]
    exact a.2
  let f : Ab → X := fun a => ⟨χ ⟨Mf a, hN (hMf a)⟩, _, hMN a, rfl⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : χ ((⟨Mf a, hN (hMf a)⟩ : NN)⁻¹ * ⟨Mf b, hN (hMf b)⟩) = 1 := by
      have := congrArg Subtype.val hab
      simp only [f] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    have hz := mem_scalars_of_eq_scalar hc
    have h2 : ρ ((⟨Mf a, hN (hMf a)⟩ : NN)⁻¹ * ⟨Mf b, hN (hMf b)⟩) = 1 := by
      have he : (⟨Mf a, hN (hMf a)⟩ : NN)⁻¹ * ⟨Mf b, hN (hMf b)⟩ =
          ⟨_, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
      rw [he]
      exact TableB.projConj_of_scalar _ hz
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    apply Subtype.ext
    rw [hMfeq a, hMfeq b, h2]
  have hle := Nat.card_le_card_of_injective f hf
  set G := X.comap (conjAut 6 K) with hG
  have hGp : IsProjElem 3 G := TypeA.isProjElem_comap (by norm_num) hXab
  have hN₀gu : ∀ M ∈ N₀, ∃ (c : Kˣ) (M' : GL (Fin 6) K)
      (hM' : M' ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      (M : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c * M' ∧ ρ ⟨M', hN hM'⟩ = ρ M := by
    intro M hM
    obtain ⟨M', hM'gu, hM'eq⟩ := TableB.exists_eq_projConj hN (hAbI _ hM)
    have hM'eq' : ρ M = ρ ⟨M', hN hM'gu⟩ := hM'eq
    have h1 : ρ (M * (⟨M', hN hM'gu⟩ : NN)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hM'eq', mul_inv_cancel]
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq h1
    refine ⟨c, M', hM'gu, ?_, hM'eq'.symm⟩
    have e : ((M * (⟨M', hN hM'gu⟩ : NN)⁻¹ : NN) : GL (Fin 6) K) =
        (M : GL (Fin 6) K) * M'⁻¹ := rfl
    rw [hc, e]
    group
  have hGdesc : ∀ g ∈ G, ∃ (c : Kˣ) (M : GL (Fin 6) K)
      (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      g = GeneralLinearGroup.scalar (Fin 6) c * M ∧ ρ ⟨M, hN hM⟩ ∈ Ab := by
    intro g hg
    obtain ⟨M, hM, hMg⟩ := hg
    obtain ⟨c, M', hM', hMM', hρM'⟩ := hN₀gu M hM
    have h1 : conjAut 6 K (g * (M : GL (Fin 6) K)⁻¹) = 1 := by
      rw [map_mul, map_inv, show conjAut 6 K (M : GL (Fin 6) K) = χ M from rfl, hMg,
        mul_inv_cancel]
    obtain ⟨c₀, hc₀⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar (by norm_num) hc₀
    refine ⟨u * c, M', hM', ?_, by rw [hρM']; exact hM⟩
    calc g = (g * (M : GL (Fin 6) K)⁻¹) * M := by group
      _ = GeneralLinearGroup.scalar (Fin 6) u * (GeneralLinearGroup.scalar (Fin 6) c * M') := by
          rw [hu, hMM']
      _ = GeneralLinearGroup.scalar (Fin 6) (u * c) * M' := by rw [map_mul, mul_assoc]
  have hGmem : ∀ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ρ ⟨M, hN hM⟩ ∈ Ab → M ∈ G := fun M hM hρM => ⟨⟨M, hN hM⟩, hρM, rfl⟩
  have hgood : ∀ v ∈ G, v ^ 3 = 1 → ∃ hvN : v ∈ NN,
      v ∈ primeFormUnitary h (idGram K 6) ∧ ρ ⟨v, hvN⟩ ∈ Ab := by
    intro v hv hv3
    obtain ⟨c, M, hM, hvM, hMA⟩ := hGdesc v hv
    have hsN : GeneralLinearGroup.scalar (Fin 6) c ∈ NN :=
      TableB.scalar_mem_normalizer _ ⟨c, rfl⟩
    have hvN : v ∈ NN := by rw [hvM]; exact NN.mul_mem hsN (hN hM)
    refine ⟨hvN, mem_primeFormUnitary_of_pow_eq_one h hpq (by norm_num) hM (c := (c : K)) ?_ hv3,
      ?_⟩
    · rw [hvM, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul]
    · have e : (⟨v, hvN⟩ : NN) = ⟨_, hsN⟩ * ⟨M, hN hM⟩ := Subtype.ext hvM
      rw [e, map_mul, TableB.projConj_of_scalar _ ⟨c, rfl⟩, one_mul]
      exact hMA
  have htor : ¬ IsToral G := by
    intro htor
    apply hnofr
    obtain ⟨P, hP, hPd⟩ := exists_unitary_diag_of_isToral h hp3 hpq (by norm_num) hXab hXU htor
    refine ⟨P, hP, fun a ha => ?_⟩
    obtain ⟨M, hM, hMa⟩ := TableB.exists_eq_projConj hN (hAbI a ha)
    exact ⟨M, hM, hPd M (hGmem M hM (hMa ▸ ha)), hMa⟩
  by_cases hF : ∃ g ∈ G, ∀ c : Kˣ, g ^ 3 ≠ GeneralLinearGroup.scalar (Fin 6) (c ^ 3)
  ·
    left
    obtain ⟨g, hg, hgF⟩ := hF
    obtain ⟨c, M, hM, hgM, hMA⟩ := hGdesc g hg
    obtain ⟨u, hu⟩ := exists_unitary_of_gu h hM
    obtain ⟨l, hl⟩ := hGp.pow_scalar g hg
    have hsN : GeneralLinearGroup.scalar (Fin 6) u ∈ NN :=
      TableB.scalar_mem_normalizer _ ⟨u, rfl⟩
    have hM₀N : GeneralLinearGroup.scalar (Fin 6) u * M ∈ NN := NN.mul_mem hsN (hN hM)
    have hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) ((c ^ 3)⁻¹ * l) := by
      rw [hgM, scalar_mul_pow] at hl
      rw [map_mul, ← hl, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    refine ⟨_, hM₀N, u ^ 3 * ((c ^ 3)⁻¹ * l), hu, ?_, ?_, ?_⟩
    · rw [scalar_mul_pow, hM3, ← map_mul]
    · intro e he
      apply hgF (e * c * u⁻¹)
      rw [hl]
      congr 1
      apply Units.ext
      have he' := congrArg Units.val he
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val] at he' ⊢
      rw [mul_pow, mul_pow, he']
      have hu0 := u.ne_zero
      have hc0 := c.ne_zero
      field_simp
    · have e : (⟨_, hM₀N⟩ : NN) = ⟨_, hsN⟩ * ⟨M, hN hM⟩ := rfl
      rw [e, map_mul, TableB.projConj_of_scalar _ ⟨u, rfl⟩, one_mul]
      exact hMA
  ·
    right
    push Not at hF
    have hnc : ∃ x ∈ G, x ^ 3 = 1 ∧ ∃ y ∈ G, y * x ≠ x * y := by
      by_contra hcon
      push Not at hcon
      exact htor (isToral_of_central hp3 (dvd_card_sub_one hK hpq) hGp hcon hF)
    obtain ⟨x, hx, hx3, y₀, hy₀, hxy₀⟩ := hnc
    obtain ⟨c₀, hc₀⟩ := hF y₀ hy₀
    set y := GeneralLinearGroup.scalar (Fin 6) c₀⁻¹ * y₀ with hydef
    have hy : y ∈ G := G.mul_mem (hGp.scalar_mem _) hy₀
    have hy3 : y ^ 3 = 1 := pow_eq_one_of_pow_eq_scalar_pow hc₀
    obtain ⟨ζ, hζ⟩ := hGp.comm_scalar x hx y hy
    have hζ1 : ζ ≠ 1 := by
      rintro rfl
      rw [map_one, one_mul] at hζ
      apply hxy₀
      have e : y₀ = GeneralLinearGroup.scalar (Fin 6) c₀ * y := by
        rw [hydef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      rw [e, mul_assoc, ← hζ, ← mul_assoc, TypeA.PGLTor.scalar_mul_comm, mul_assoc]
    have hζ3 : ζ ^ 3 = 1 := by
      have e := commChar_pow_eq_one hGp hx ⟨y, hy⟩
      rwa [commChar_eq hGp hx (x := ⟨y, hy⟩) hζ] at e
    have hz : ∃ w ∈ G, w * x = x * w ∧ w * y = y * w ∧ w ∉ LargeEvenScalars (Fin 6) K := by
      by_contra hcon
      push Not at hcon
      have hXI : (X : Set (MulAut (projectiveSL 6 K))) ⊆ Set.range (conjAut 6 K) := by
        intro a ha
        obtain ⟨M, -, hM⟩ := hXU a ha
        exact ⟨M, hM⟩
      have hGcard : Nat.card G = Nat.card X * (Nat.card K - 1) :=
        TypeA.card_comap_eq (by norm_num) hXI
      set χx := (commChar hGp hx).codRestrict (rootsOfUnity 3 K)
        (fun w => (mem_rootsOfUnity _ _).mpr (commChar_pow_eq_one hGp hx w)) with hχx
      set χy := (commChar hGp hy).codRestrict (rootsOfUnity 3 K)
        (fun w => (mem_rootsOfUnity _ _).mpr (commChar_pow_eq_one hGp hy w)) with hχy
      set Φ := χx.prod χy with hΦ
      have hk1 : Nat.card Φ.ker ≤ Nat.card K - 1 := by
        have hsc : ∀ w : Φ.ker, ∃ u : Kˣ,
            GeneralLinearGroup.scalar (Fin 6) u = ((w : G) : GL (Fin 6) K) := by
          intro w
          have hw : Φ (w : G) = 1 := w.2
          have hw1 : χx (w : G) = 1 := congrArg Prod.fst hw
          have hw2 : χy (w : G) = 1 := congrArg Prod.snd hw
          have e1 : commChar hGp hx (w : G) = 1 := congrArg Subtype.val hw1
          have e2 : commChar hGp hy (w : G) = 1 := congrArg Subtype.val hw2
          rw [commChar_eq_one_iff] at e1 e2
          exact hcon _ (w : G).2 e1.symm e2.symm
        choose fu hfu using hsc
        have hinj : Function.Injective fu := fun a b hab =>
          Subtype.ext (Subtype.ext (by rw [← hfu, ← hfu, hab]))
        rw [← Nat.card_units K]
        exact Nat.card_le_card_of_injective fu hinj
      have hr9 : Nat.card Φ.range ≤ 9 := by
        calc Nat.card Φ.range ≤ Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) :=
              Subgroup.card_le_card_group _
          _ = Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
          _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 3) (card_rootsOfUnity K 3)
      have h1 := Subgroup.card_ker_mul_card_range Φ
      have hK1 : 0 < Nat.card K - 1 := by
        have := Finite.one_lt_card (α := K)
        omega
      have h27 : 27 * (Nat.card K - 1) ≤ Nat.card G := by
        rw [hGcard]
        exact Nat.mul_le_mul_right _ (by norm_num at hcard; omega)
      have h9 : Nat.card G ≤ (Nat.card K - 1) * 9 := by
        rw [← h1]
        exact Nat.mul_le_mul hk1 hr9
      omega
    obtain ⟨w, hw, hwx, hwy, hws⟩ := hz
    obtain ⟨c₁, hc₁⟩ := hF w hw
    set z := GeneralLinearGroup.scalar (Fin 6) c₁⁻¹ * w with hzdef
    have hzG : z ∈ G := G.mul_mem (hGp.scalar_mem _) hw
    have hz3 : z ^ 3 = 1 := pow_eq_one_of_pow_eq_scalar_pow hc₁
    have hzx : x * z = z * x := by
      rw [hzdef, ← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm, mul_assoc, ← hwx, mul_assoc]
    have hzy : y * z = z * y := by
      rw [hzdef, ← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm, mul_assoc, ← hwy, mul_assoc]
    have hzs : z ∉ LargeEvenScalars (Fin 6) K := by
      rintro ⟨u, hu⟩
      apply hws
      refine ⟨c₁ * u, ?_⟩
      rw [map_mul, hu, hzdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    obtain ⟨hxN, hxu, hxA⟩ := hgood x hx hx3
    obtain ⟨hyN, hyu, hyA⟩ := hgood y hy hy3
    obtain ⟨hzN, hzu, hzA⟩ := hgood z hzG hz3
    exact ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3, hz3, hζ3, hζ1, hζ, hzx,
      hzy, hzs⟩

end Cases

end TableBU63

end CFSG.StandardType
