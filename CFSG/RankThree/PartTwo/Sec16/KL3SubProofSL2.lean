module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KL3SubProof

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP

section Order3

variable {F : Type} [Field F] [CharP F 2]

@[expose] def ord3SL2 (F : Type) [Field F] [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    simp only [mul_one, zero_sub]
    exact CharTwo.neg_eq 1⟩

theorem coe_ord3SL2 : ((ord3SL2 F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; 1, 1] := rfl

theorem ord3SL2_pow_three : ord3SL2 F ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h : ((ord3SL2 F * ord3SL2 F * ord3SL2 F : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_ord3SL2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h2
  rw [pow_three, ← mul_assoc]
  exact Subtype.ext h

theorem ord3SL2_ne_one : ord3SL2 F ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [coe_ord3SL2] at h1

theorem orderOf_ord3SL2 : orderOf (ord3SL2 F) = 3 :=
  orderOf_eq_prime ord3SL2_pow_three ord3SL2_ne_one

theorem three_dvd_card_psl2 : 3 ∣ Nat.card (PSL2MatrixGroup F) := by
  have h := orderOf_injective (mkPSL F) mkPSL_injective (ord3SL2 F)
  rw [orderOf_ord3SL2] at h
  rw [← h]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_pgl2 : 3 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) :=
  three_dvd_card_psl2.trans (Subgroup.card_dvd_of_injective _
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective)

end Order3

section Pair

variable {F : Type} [Field F] [CharP F 2]

@[expose] def pairHom (F : Type) [Field F] [CharP F 2] (s₁ s₂ : F) :
    Multiplicative (ZMod 2 × ZMod 2) →* SpecialLinearGroup (Fin 2) F where
  toFun c := u2 (ZMod.castHom (dvd_refl 2) F c.toAdd.1 * s₁ +
    ZMod.castHom (dvd_refl 2) F c.toAdd.2 * s₂)
  map_one' := by simp [u2_zero]
  map_mul' c d := by
    rw [← u2_add]
    congr 1
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, map_add]
    ring

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem pairHom_injective {s₁ s₂ : F} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h₁₂ : s₁ ≠ s₂) :
    Function.Injective (pairHom F s₁ s₂) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [MonoidHom.mem_ker] at hc
  have hc' : u2 (ZMod.castHom (dvd_refl 2) F c.toAdd.1 * s₁ +
      ZMod.castHom (dvd_refl 2) F c.toAdd.2 * s₂) = u2 0 := by
    rw [u2_zero]
    exact hc
  have hz := u2_injective hc'
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  rcases zmod_two_cases c.toAdd.1 with h1 | h1 <;> rcases zmod_two_cases c.toAdd.2 with h2 | h2 <;>
    rw [h1, h2] at hz <;> simp only [map_zero, map_one, zero_mul, one_mul, zero_add,
      add_zero] at hz
  · exact Prod.ext h1 h2
  · exact absurd hz h₂
  · exact absurd hz h₁
  · exact absurd (by linear_combination hz - s₂ * (CharTwo.two_eq_zero : (2 : F) = 0)) h₁₂

theorem four_dvd_card_of_root_pair {M : Subgroup (SpecialLinearGroup (Fin 2) F)} {s₁ s₂ : F}
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h₁₂ : s₁ ≠ s₂) (hu₁ : u2 s₁ ∈ M) (hu₂ : u2 s₂ ∈ M) :
    4 ∣ Nat.card M := by
  have hle : (pairHom F s₁ s₂).range ≤ M := by
    rintro _ ⟨c, rfl⟩
    change u2 _ ∈ M
    rw [u2_add]
    refine M.mul_mem ?_ ?_
    · rcases zmod_two_cases c.toAdd.1 with h | h <;> rw [h] <;> simp [u2_zero, hu₁, M.one_mem]
    · rcases zmod_two_cases c.toAdd.2 with h | h <;> rw [h] <;> simp [u2_zero, hu₂, M.one_mem]
  have hcard : Nat.card (pairHom F s₁ s₂).range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (pairHom_injective h₁ h₂ h₁₂)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end Pair

section Dickson


open CFSG.Glauberman.Dickson

theorem false_of_root_elements {F : Type} [Field F] [Finite F] [CharP F 2]
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)} (h3 : ¬ 3 ∣ Nat.card M) {s₁ s₂ b : F}
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h₁₂ : s₁ ≠ s₂) (hb : b ≠ 0) (hu₁ : u2 s₁ ∈ M)
    (hu₂ : u2 s₂ ∈ M) (hl : l2 b ∈ M) : False := by
  classical
  obtain ⟨f, hf1, hF⟩ := exists_card_eq_two_pow F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := mkPSL_injective (F := F)
  have hHcard : Nat.card (M.map (mkPSL F)) = Nat.card M := Subgroup.card_map_of_injective hinj
  have h4 : 4 ∣ Nat.card M := four_dvd_card_of_root_pair h₁ h₂ h₁₂ hu₁ hu₂
  have hFodd : Odd (2 ^ f - 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rcases h1 with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hFodd' : Odd (2 ^ f + 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hFodd.not_two_dvd_nat)
  let H : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  have h3H : ¬ 3 ∣ Nat.card H := by
    change ¬ 3 ∣ Nat.card (M.map (mkPSL F))
    rw [hHcard]
    exact h3
  let x : H := ⟨mkPSL F (u2 s₁), Subgroup.mem_map_of_mem _ hu₁⟩
  let y : H := ⟨mkPSL F (l2 b), Subgroup.mem_map_of_mem _ hl⟩
  have hxy : x * y ≠ y * x := by
    intro h
    have h' := congrArg Subtype.val h
    apply u2_mul_l2_ne (mul_ne_zero h₁ hb)
    apply hinj
    rw [map_mul, map_mul]
    exact h'
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simp [x, pow_two, ← map_mul, u2_mul_self]
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simp [y, pow_two, ← map_mul, l2_mul_self]
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := 2) (f := f) hF
      H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, -, -, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, -, ⟨eP⟩, -⟩ | ⟨m, hm0, -, ⟨eP⟩, -⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  ·
    have hzodd : Odd z := by
      simp only [hF, hg, Nat.div_one] at hz
      rcases hz with h | h
      · exact Odd.of_dvd_nat hFodd h
      · exact Odd.of_dvd_nat hFodd' h
    have h42 : 4 ∣ 2 * z := by
      rw [← hcard]
      change 4 ∣ Nat.card (M.map (mkPSL F))
      rw [hHcard]
      exact h4
    obtain ⟨c, hc⟩ := hzodd
    omega
  ·
    apply h3H
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  · exfalso
    have h1 : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
    omega
  ·
    apply h3H
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  ·
    have htodd : Odd t :=
      Odd.of_dvd_nat hFodd (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    have := hN
    have hxN : x ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hx2
    have hyN : y ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hy2
    have hcN := hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N) ⟨y, hyN⟩
    exact hxy (congrArg Subtype.val hcN)
  ·
    apply h3H
    rw [Nat.card_congr eP.toEquiv]
    exact three_dvd_card_psl2
  ·
    apply h3H
    rw [Nat.card_congr eP.toEquiv]
    exact three_dvd_card_pgl2

end Dickson

end KL3SubProof

end CFSG.RankThree.PartTwo.Sec16
