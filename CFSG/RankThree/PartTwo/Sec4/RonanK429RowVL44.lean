module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL44Eig
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL44Blk
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL44
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (SL4 zL tL dz wreathFacts_L4 card_wreathW_L4
  factorization_card_SL4 coe_vecElt zeta zeta_spec)
open CFSG.Assembly.RankThreeEven (projSL)

namespace RowV

theorem card_SL4_eq : Nat.card SL4 = 7 * 141004800 := by
  rw [KFacts.KS21.L44.card_M_eq]
  norm_num

theorem centQuasi_SL4 {E : Subgroup SL4} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) {s : SL4} (hs : s ∈ E) (hs1 : s ≠ 1) :
    CentQuasi s 141004800 60480 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW zL tL)
    (by rw [card_wreathW_L4, factorization_card_SL4]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ wreathW zL tL :=
    Item434AltPerm.map_conj_inv_le hg
  have hEq : E.map (MulAut.conj g⁻¹).toMonoidHom = baseA zL :=
    eq_baseA_of_le_wreathW wreathFacts_L4 card_wreathW_L4 hle (Res423Two.isElemAbelian_map' _ hE)
      (by rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, hE27])
  have hs' : MulAut.conj g⁻¹ s ∈ baseA zL := hEq ▸ ⟨s, hs, rfl⟩
  obtain ⟨v, hv⟩ := (mem_baseA_iff wreathFacts_L4).mp hs'
  apply CentQuasi.of_mulEquiv (MulAut.conj g⁻¹)
  set s' := MulAut.conj g⁻¹ s with hs'def
  have hs'1 : s' ≠ 1 := fun h => hs1 ((MulAut.conj g⁻¹).injective (by rw [← hs'def, h, map_one]))
  set x : Fin 4 → GaloisField 2 2 :=
    fun k => dz 0 k ^ (v 0).val * dz 1 k ^ (v 1).val * dz 2 k ^ (v 2).val with hxdef
  have hx : (s' : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) = Matrix.diagonal x := by
    rw [← hv, coe_vecElt]
  have hx3 : ∀ k, x k ^ 3 = 1 := by
    intro k
    simp only [hxdef, mul_pow, ← pow_mul]
    rw [mul_comm (v 0).val 3, mul_comm (v 1).val 3, mul_comm (v 2).val 3, pow_mul, pow_mul,
      pow_mul, RonanK432.dz_cube, RonanK432.dz_cube, RonanK432.dz_cube, one_pow, one_pow, one_pow,
      one_mul, one_mul]
  have hprod : ∏ k, x k = 1 := by
    have h := s'.2
    rw [hx, Matrix.det_diagonal] at h
    exact h
  have hxne : ∃ k, x k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hs'1
    apply Subtype.ext
    rw [hx, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hcon k
  by_cases h7 : ∃ t ∈ Subgroup.centralizer ({s'} : Set SL4), orderOf t = 7
  · obtain ⟨t, ht, ht7⟩ := h7
    have htt : (t : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ^ 7 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← ht7, pow_orderOf_eq_one,
        Matrix.SpecialLinearGroup.coe_one]
    have ht1 : (t : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) ≠ 1 := by
      intro h
      have : t = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht7
      norm_num at ht7
    have hcomm : Matrix.diagonal x * (t : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
        (t : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) * Matrix.diagonal x := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp ht
      have h' := congrArg (fun y : SL4 => (y : Matrix (Fin 4) (Fin 4) (GaloisField 2 2))) h
      simp only [Matrix.SpecialLinearGroup.coe_mul, hx] at h'
      exact h'.symm
    obtain ⟨p, q, r, hpq, hpr, hqr, hxq, hxr⟩ :=
      l44_three_le_card_of_commute_pow_seven' hF4 htt ht1 hx3 hcomm
    set c := x p with hcdef
    have hex4 : ∀ p q r : Fin 4, ∃ i : Fin 4, i ≠ p ∧ i ≠ q ∧ i ≠ r := by decide
    have hall4 : ∀ p q r i j : Fin 4, p ≠ q → p ≠ r → q ≠ r → i ≠ p → i ≠ q → i ≠ r → j ≠ i →
        j = p ∨ j = q ∨ j = r := by decide
    obtain ⟨i, hip, hiq, hir⟩ := hex4 p q r
    have hi : ∀ j, j ≠ i → x j = c := by
      intro j hj
      rcases hall4 p q r i j hpq hpr hqr hip hiq hir hj with rfl | rfl | rfl
      · rfl
      · exact hxq.symm
      · exact hxr.symm
    have hc3 : c ^ 3 = 1 := hx3 p
    have hxi : x i = 1 := by
      rw [← Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)] at hprod
      have hrest : ∏ k ∈ Finset.univ.erase i, x k = c ^ 3 := by
        rw [Finset.prod_congr rfl fun k hk => hi k (Finset.ne_of_mem_erase hk),
          Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
      rw [hrest, hc3, mul_one] at hprod
      exact hprod
    have hc1 : c ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := hxne
      apply hk
      by_cases hki : k = i
      · rw [hki, hxi]
      · rw [hi k hki, h1]
    refine centQuasi_diagonal_block hF4 hc1 hc3 i s' ?_ 141004800
    rw [hx]
    congr 1
    funext j
    split_ifs with hj
    · rw [hj, hxi]
    · exact hi j hj
  · left
    push Not at h7
    have h7' : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({s'} : Set SL4)) := by
      intro hd
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 7 hd
      exact h7 t t.2 (by rwa [Subgroup.orderOf_coe])
    have hd : Nat.card (Subgroup.centralizer ({s'} : Set SL4)) ∣ 7 * 141004800 :=
      card_SL4_eq ▸ Subgroup.card_subgroup_dvd_card _
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7')).dvd_of_dvd_mul_left
      hd

theorem noCfgS429_projSL_four_four {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (φ : S ≃* projSL 4 (GaloisField 2 2)) : NoCfgS429 S := by
  set ψ : S ≃* SL4 := φ.trans KFacts.KS21.L44.equivSL with hψ
  refine noCfgS429_of_inner_quasi (N₁ := 141004800) (N₂ := 60480) (B := 13)
    (center_eq_bot_of_simple hs hna) ?_ ?_ (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro τ h3
    have h3' : MulAut.congr φ τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact (isInnerAut_congr φ τ).mp
      (cubeInner_of_not_three_dvd_card_outer RonanK432.not_three_dvd_card_outer_projSL4 _ h3')
  · intro E hE hE27 s hsE hs1
    apply CentQuasi.of_mulEquiv ψ
    refine centQuasi_SL4 (E := E.map ψ.toMonoidHom) (Res423Two.isElemAbelian_map' _ hE)
      (by rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hE27]) ⟨s, hsE, rfl⟩ ?_
    intro h
    exact hs1 (ψ.injective (by rw [h, map_one]))

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
