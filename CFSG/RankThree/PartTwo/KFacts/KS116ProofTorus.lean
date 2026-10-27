module

public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTools
public import CFSG.RankThree.PartTwo.KFacts.KS116

public section

namespace CFSG.RankThree.PartTwo.KFacts

namespace KS116Proof

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply)

variable {F : Type} [Field F] [CharP F 2]

theorem eq_inv_or_mul_self_eq_one (A B : SL(2, F)) (hAB : A * B = B * A)
    (htr : A 0 0 + A 1 1 = B 0 0 + B 1 1) : B = A⁻¹ ∨ (A⁻¹ * B) * (A⁻¹ * B) = 1 := by
  by_cases h : (A⁻¹ * B : SL(2, F)) 0 0 + (A⁻¹ * B : SL(2, F)) 1 1 = 0
  · exact Or.inr (mul_self_eq_one_of_trace _ h)
  · left
    have hdet : ((A : Matrix (Fin 2) (Fin 2) F) + B).det ≠ 0 := by
      rw [det_add]
      exact h
    have hz := add_mul_add_inv_eq_zero A B hAB htr
    have h0 : (B : Matrix (Fin 2) (Fin 2) F) + ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        0 := by
      have h1 := congrArg (fun X => ((A : Matrix (Fin 2) (Fin 2) F) + B).adjugate * X) hz
      simp only [Matrix.mul_zero, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
        Matrix.one_mul] at h1
      exact (smul_eq_zero.mp h1).resolve_left hdet
    apply Subtype.ext
    rw [eq_neg_of_add_eq_zero_left h0, CharTwo.neg_eq]

theorem eq_or_eq_inv_of_trace_eq {T : Subgroup SL(2, F)} [Finite T] (hodd : Odd (Nat.card T))
    (hcomm : ∀ A ∈ T, ∀ B ∈ T, A * B = B * A) {A B : SL(2, F)} (hA : A ∈ T) (hB : B ∈ T)
    (htr : A 0 0 + A 1 1 = B 0 0 + B 1 1) : B = A ∨ B = A⁻¹ := by
  rcases eq_inv_or_mul_self_eq_one A B (hcomm A hA B hB) htr with h | h
  · exact Or.inr h
  · left
    set s : T := ⟨A⁻¹ * B, T.mul_mem (T.inv_mem hA) hB⟩
    have hs2 : s ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact h)
    have hcop : Nat.Coprime 2 (Nat.card T) := (Nat.coprime_two_left).mpr hodd
    have hs1 : orderOf s = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hs2)
      (orderOf_dvd_natCard s)
    have hs : A⁻¹ * B = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hs1)
    calc B = A * (A⁻¹ * B) := by group
      _ = A := by rw [hs, mul_one]

theorem card_le_two_mul_card_image_trace [Fintype F] [DecidableEq F] {T : Subgroup SL(2, F)}
    [DecidablePred (· ∈ T)] (hodd : Odd (Nat.card T))
    (hcomm : ∀ A ∈ T, ∀ B ∈ T, A * B = B * A) :
    Nat.card T ≤
      2 * ((Finset.univ.filter (· ∈ T)).image (fun A : SL(2, F) => A 0 0 + A 1 1)).card := by
  classical
  have hcard : Nat.card T = (Finset.univ.filter (· ∈ T)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  apply Finset.card_le_mul_card_image
  intro b hb
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hb
  have hAT : A ∈ T := (Finset.mem_filter.mp hA).2
  calc ((Finset.univ.filter (· ∈ T)).filter
          (fun B : SL(2, F) => B 0 0 + B 1 1 = A 0 0 + A 1 1)).card
      ≤ ({A, A⁻¹} : Finset SL(2, F)).card := by
        apply Finset.card_le_card
        intro B hB
        rw [Finset.mem_filter, Finset.mem_filter] at hB
        rcases eq_or_eq_inv_of_trace_eq hodd hcomm hAT hB.1.2 hB.2.symm with h | h <;>
          simp [h]
    _ ≤ 2 := Finset.card_le_two

theorem card_fix_sq_le {K : Type} [Field K] [Fintype K] [DecidableEq K] (σ : K ≃+* K)
    (hσ : σ ≠ 1) : (Finset.univ.filter (fun x => σ x = x)).card ^ 2 ≤ Fintype.card K := by
  obtain ⟨y, hy⟩ : ∃ y, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  set E := Finset.univ.filter (fun x => σ x = x)
  rw [pow_two, ← Finset.card_product, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => p.1 + p.2 * y) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, E, Finset.mem_filter,
    Finset.mem_univ, true_and] at hab hab'
  simp only at h
  by_cases hb : b = b'
  · subst hb
    simp only [Prod.mk.injEq, and_true]
    linear_combination h
  · exfalso
    have hb' : b - b' ≠ 0 := sub_ne_zero.mpr hb
    have hy' : y = (a' - a) / (b - b') := by
      field_simp
      linear_combination h
    apply hy
    rw [hy', map_div₀, map_sub, map_sub, hab.1, hab.2, hab'.1, hab'.2]

theorem fieldAut_eq_one_of_fix [Fintype F] [DecidableEq F] (h8 : 8 ≤ Fintype.card F)
    {T : Subgroup SL(2, F)} (hodd : Odd (Nat.card T)) (hcomm : ∀ A ∈ T, ∀ B ∈ T, A * B = B * A)
    (hcard : Fintype.card F - 1 ≤ Nat.card T) (M : SL(2, F)) (σ : F ≃+* F)
    (hfix : ∀ A ∈ T, M * slFieldAut F σ A * M⁻¹ = A) : σ = 1 := by
  classical
  by_contra hσ
  have hsub : (Finset.univ.filter (· ∈ T)).image (fun A : SL(2, F) => A 0 0 + A 1 1) ⊆
      Finset.univ.filter (fun x => σ x = x) := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
    have hAT : A ∈ T := (Finset.mem_filter.mp hA).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← trace_slFieldAut, ← trace_conj M, hfix A hAT]
  have h1 := card_le_two_mul_card_image_trace hodd hcomm
  have h2 := Finset.card_le_card hsub
  have h3 := card_fix_sq_le σ hσ
  set Q := Fintype.card F
  set e := (Finset.univ.filter (fun x => σ x = x)).card
  have hT : Q - 1 ≤ 2 * e := hcard.trans (h1.trans (by omega))
  have hQ : (Q - 1) * (Q - 1) ≤ 4 * Q := by
    calc (Q - 1) * (Q - 1) ≤ (2 * e) * (2 * e) := Nat.mul_le_mul hT hT
      _ = 4 * e ^ 2 := by ring
      _ ≤ 4 * Q := by omega
  have hQ' : Q - 1 + 1 = Q := by omega
  nlinarith

omit [CharP F 2] in
theorem exists_eq_smul_add_smul_of_commute {X G : Matrix (Fin 2) (Fin 2) F}
    (hX : ¬ (X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1)) (h : G * X = X * G) :
    ∃ a b : F, G = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • X := by
  have e : ∀ i j, (G * X) i j = (X * G) i j := fun i j => by rw [h]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  by_cases hq : X 0 1 = 0
  · by_cases hr : X 1 0 = 0
    · have hps : X 0 0 - X 1 1 ≠ 0 := fun hps => hX ⟨hq, hr, sub_eq_zero.mp hps⟩
      have hy : G 0 1 = 0 := by
        have : G 0 1 * (X 0 0 - X 1 1) = 0 := by rw [hq] at h01; linear_combination -h01
        exact (mul_eq_zero.mp this).resolve_right hps
      have hz : G 1 0 = 0 := by
        have : G 1 0 * (X 0 0 - X 1 1) = 0 := by rw [hr] at h10; linear_combination h10
        exact (mul_eq_zero.mp this).resolve_right hps
      refine ⟨G 0 0 - (G 0 0 - G 1 1) / (X 0 0 - X 1 1) * X 0 0,
        (G 0 0 - G 1 1) / (X 0 0 - X 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq, hr, hy, hz]
      field_simp
      ring
    · have hy : G 0 1 = 0 := by
        have : G 0 1 * X 1 0 = 0 := by rw [hq] at h00; linear_combination h00
        exact (mul_eq_zero.mp this).resolve_right hr
      refine ⟨G 0 0 - G 1 0 / X 1 0 * X 0 0, G 1 0 / X 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq, hy] <;> field_simp
      first | ring1 | linear_combination -h10 | linear_combination h10
  · refine ⟨G 0 0 - G 0 1 / X 0 1 * X 0 0, G 0 1 / X 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
      first | ring1 | linear_combination h00 | linear_combination -h00 |
        linear_combination h01 | linear_combination -h01

omit [CharP F 2] in
theorem det_smul_add_smul (X : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • X).det =
      a ^ 2 + a * b * (X 0 0 + X 1 1) + b ^ 2 * X.det := by
  simp [det_fin_two]
  ring

theorem card_centralizer_le [Fintype F] [DecidableEq F] {t₀ : SL(2, F)} (ht : t₀ ≠ 1) :
    Nat.card (Subgroup.centralizer ({t₀} : Set SL(2, F))) ≤ Fintype.card F + 1 := by
  classical
  set X : Matrix (Fin 2) (Fin 2) F := (t₀ : Matrix (Fin 2) (Fin 2) F) with hXdef
  have hX : ¬ (X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1) := by
    rintro ⟨hq, hr, hps⟩
    apply ht
    have hd := det_entries t₀
    change X 0 0 * X 1 1 + X 0 1 * X 1 0 = 1 at hd
    rw [hq, zero_mul, add_zero, ← hps, ← pow_two] at hd
    have h1 := eq_one_of_sq_eq_one hd
    apply Subtype.ext
    change X = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, hr, h1, ← hps]
  set C := Subgroup.centralizer ({t₀} : Set SL(2, F))
  have key : ∀ G : C, ∃ ab : F × F,
      ((G : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) +
        ab.2 • X := by
    intro G
    have hG := Subgroup.mem_centralizer_iff.mp G.2 t₀ (Set.mem_singleton t₀)
    have hG' : ((G : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X =
        X * ((G : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      have := congrArg (fun Y : SL(2, F) => (Y : Matrix (Fin 2) (Fin 2) F)) hG
      simp only [Matrix.SpecialLinearGroup.coe_mul] at this
      exact this.symm
    obtain ⟨a, b, hab⟩ := exists_eq_smul_add_smul_of_commute hX hG'
    exact ⟨(a, b), hab⟩
  choose ab hab using key
  have hdet : ∀ G : C, (ab G).1 ^ 2 + (ab G).1 * (ab G).2 * (X 0 0 + X 1 1) + (ab G).2 ^ 2 = 1 := by
    intro G
    have h1 := ((G : SL(2, F))).2
    rw [hab G, det_smul_add_smul] at h1
    have hX1 : X.det = 1 := t₀.2
    rw [hX1, mul_one] at h1
    exact h1
  let ψ : C → Option F := fun G => if (ab G).2 = 0 then none else some ((ab G).1 / (ab G).2)
  have hψ : Function.Injective ψ := by
    intro G G' h
    have hGG : (ab G) = (ab G') → G = G' := fun hab' => by
      apply Subtype.ext
      apply Subtype.ext
      rw [hab G, hab G', hab']
    apply hGG
    simp only [ψ] at h
    by_cases hb : (ab G).2 = 0 <;> by_cases hb' : (ab G').2 = 0 <;>
      simp only [hb, hb', ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    · have ha := hdet G
      have ha' := hdet G'
      rw [hb, mul_zero, zero_mul, add_zero, zero_pow two_ne_zero, add_zero] at ha
      rw [hb', mul_zero, zero_mul, add_zero, zero_pow two_ne_zero, add_zero] at ha'
      rw [Prod.ext_iff, hb, hb', eq_one_of_sq_eq_one ha, eq_one_of_sq_eq_one ha']
      exact ⟨rfl, rfl⟩
    · set s := (ab G).1 / (ab G).2 with hs
      have ha : (ab G).1 = s * (ab G).2 := by rw [hs]; field_simp
      have ha' : (ab G').1 = s * (ab G').2 := by rw [h]; field_simp
      have hd := hdet G
      have hd' := hdet G'
      rw [ha] at hd
      rw [ha'] at hd'
      have hd2 : (s ^ 2 + s * (X 0 0 + X 1 1) + 1) * (ab G).2 ^ 2 = 1 := by
        linear_combination hd
      have hd2' : (s ^ 2 + s * (X 0 0 + X 1 1) + 1) * (ab G').2 ^ 2 = 1 := by
        linear_combination hd'
      have hN0 : s ^ 2 + s * (X 0 0 + X 1 1) + 1 ≠ 0 := fun h0 => by
        rw [h0, zero_mul] at hd2
        exact zero_ne_one hd2
      have hbb : (ab G).2 = (ab G').2 :=
        CharTwo.sq_inj.mp (mul_left_cancel₀ hN0 (hd2.trans hd2'.symm))
      rw [Prod.ext_iff, ha, ha', hbb]
      exact ⟨rfl, rfl⟩
  calc Nat.card C ≤ Nat.card (Option F) := Nat.card_le_card_of_injective ψ hψ
    _ = Fintype.card F + 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_option]

theorem mem_zpowers_of_commute [Fintype F] [DecidableEq F] (h4 : 4 ≤ Fintype.card F)
    {t₀ : SL(2, F)} (hord : orderOf t₀ = Fintype.card F - 1 ∨ orderOf t₀ = Fintype.card F + 1)
    {M : SL(2, F)} (hM : M * t₀ = t₀ * M) : M ∈ Subgroup.zpowers t₀ := by
  set C := Subgroup.centralizer ({t₀} : Set SL(2, F))
  have ht : t₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hle : Subgroup.zpowers t₀ ≤ C :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr (by
      rintro h (rfl : h = t₀)
      rfl))
  have hMC : M ∈ C := Subgroup.mem_centralizer_iff.mpr (by
    rintro h (rfl : h = t₀)
    exact hM.symm)
  have hCle := card_centralizer_le ht
  have hdvd : orderOf t₀ ∣ Nat.card C := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card C := Nat.card_pos
  have heq : Subgroup.zpowers t₀ = C := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers]
    obtain ⟨k, hk⟩ := hdvd
    rcases hord with hord | hord <;> rw [hord] at hk ⊢ <;> rw [hk] at hCle hpos ⊢
    · have hk1 : k ≤ 1 := by
        by_contra hk1
        have : (Fintype.card F - 1) * 2 ≤ (Fintype.card F - 1) * k :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hk0 : 0 < k := Nat.pos_of_mul_pos_left hpos
      have : k = 1 := by omega
      rw [this, mul_one]
    · have hk0 : 0 < k := Nat.pos_of_mul_pos_left hpos
      calc (Fintype.card F + 1) * k ≤ Fintype.card F + 1 := hCle
        _ = Fintype.card F + 1 := rfl
  rw [heq]
  exact hMC

end KS116Proof

open KS116Proof Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut)

theorem torusSelfCentralizingL2 : TorusSelfCentralizingL2 := by
  intro f hf T hT hcard φ hφ
  classical
  set F := GaloisField 2 f
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 f (by omega)
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top T).mp hT
  obtain ⟨M, σ, hMσ⟩ := exists_conj_slFieldAut F φ
  set E := projSLEquiv F
  set t₀ := E.symm g
  have hord : orderOf t₀ = Nat.card T := by
    rw [MulEquiv.orderOf_eq, ← Nat.card_zpowers, hg]
  have hfixg : ∀ k : ℤ, φ (g ^ k) = g ^ k := fun k =>
    hφ _ (hg ▸ Subgroup.zpow_mem_zpowers g k)
  have hfix : ∀ A ∈ Subgroup.zpowers t₀, M * slFieldAut F σ A * M⁻¹ = A := by
    intro A hA
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hA
    apply E.injective
    rw [← hMσ, map_zpow, MulEquiv.apply_symm_apply, hfixg]
  have hcomm : ∀ A ∈ Subgroup.zpowers t₀, ∀ B ∈ Subgroup.zpowers t₀, A * B = B * A := by
    intro A hA B hB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hA
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hB
    exact (zpow_mul_comm t₀ k l)
  have hcardT : Nat.card (Subgroup.zpowers t₀) = Nat.card T := by rw [Nat.card_zpowers, hord]
  have hodd : Odd (Nat.card (Subgroup.zpowers t₀)) := by
    rw [hcardT]
    have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) h8
    rcases hcard with h | h <;> rw [h]
    · exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    · exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hσ : σ = 1 := fieldAut_eq_one_of_fix (by rw [hF]; exact h8) hodd hcomm
    (by rw [hcardT, hF]; rcases hcard with h | h <;> omega) M σ hfix
  have hM : M ∈ Subgroup.zpowers t₀ := by
    apply mem_zpowers_of_commute (by rw [hF]; omega) (by rw [hord, hF]; exact hcard)
    have h := hfix t₀ (Subgroup.mem_zpowers t₀)
    rw [hσ, map_one, MulAut.one_apply] at h
    calc M * t₀ = M * t₀ * M⁻¹ * M := by group
      _ = t₀ * M := by rw [h]
  refine ⟨E M, ?_, fun x => ?_⟩
  · rw [← hg]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hM
    rw [← hk, map_zpow, MulEquiv.apply_symm_apply]
    exact Subgroup.zpow_mem_zpowers g k
  · obtain ⟨A, rfl⟩ := E.surjective x
    rw [hMσ, hσ, map_one, MulAut.one_apply, map_mul, map_mul, map_inv]

end CFSG.RankThree.PartTwo.KFacts
