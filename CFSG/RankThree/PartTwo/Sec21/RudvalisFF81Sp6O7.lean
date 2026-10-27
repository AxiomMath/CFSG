module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Defs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6O7Model
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassAut
import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6O7

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt_positiveLong)
open Subgroup Matrix

theorem tvec_eq : FF81.Am4.tvec = siegDiag (ZMod 2) (3 : Fin 4) 1 := by
  apply mat_injective
  rw [FF81.Am4.tvec, mat_elt_positiveLong, mat_siegDiag_one]
  rfl

theorem orderOf_tvec : orderOf FF81.Am4.tvec = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [tvec_eq]
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, siegDiag_mul, show (1 : ZMod 2) + 1 = 0 from rfl, siegDiag_zero]
  · intro h
    have e := congrArg (fun g => mat 4 (ZMod 2) g (Sum.inl 3) (Sum.inr 3)) h
    simp [mat_siegDiag_one, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at e

theorem Svec_le_Pvec : FF81.Am4.Svec ≤ FF81.Am4.Pvec := by
  rw [show FF81.Am4.Pvec = centralizer ({siegDiag (ZMod 2) (3 : Fin 4) 1} : Set _) by
    rw [FF81.Am4.Pvec, Cen, tvec_eq]]
  exact complSp_le_centralizer_siegDiag

theorem statedModel_Svec :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥FF81.Am4.Svec .PSp 3 2 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    (complSpEquiv (K := ZMod 2) (m := 3) (3 : Fin 4)) Hering214.statedModel_H6

theorem Pvec_eq : FF81.Am4.Pvec = centralizer ({siegDiag (ZMod 2) (3 : Fin 4) 1} : Set _) := by
  rw [FF81.Am4.Pvec, Cen, tvec_eq]

theorem Op_Pvec : Op 2 FF81.Am4.Pvec = transvRadical (ZMod 2) (3 : Fin 4) := by
  rw [Pvec_eq]
  exact CFSG.StandardType.KGSp.pCoreOf_centralizer_siegDiag (F := ZMod 2) (m := 3) le_rfl 3

theorem setMul_Pvec : setMul (Op 2 FF81.Am4.Pvec) FF81.Am4.Svec = FF81.Am4.Pvec := by
  rw [Op_Pvec]
  ext g
  constructor
  · rintro ⟨q, hq, s, hs, rfl⟩
    rw [Pvec_eq]
    exact mul_mem (transvRadical_le_centralizer hq) (complSp_le_centralizer_siegDiag hs)
  · intro hg
    have hg' : g ∈ centralizer ({siegDiag (ZMod 2) (3 : Fin 4) 1} : Set _) := by
      rwa [← Pvec_eq]
    set g₁ : centralizer ({siegDiag (ZMod 2) (3 : Fin 4) 1} : Set (StatedSp 4 (ZMod 2))) :=
      ⟨g, hg'⟩
    exact ⟨g * (comprHom (ZMod 2) 3 g₁)⁻¹, mul_inv_comprHom_mem_transvRadical g₁,
      comprHom (ZMod 2) 3 g₁, comprHom_mem_complSp g₁, by group⟩

theorem tvec_mem_commutator : FF81.Am4.tvec ∈ ⁅FF81.Am4.Pvec, FF81.Am4.Pvec⁆ := by
  rw [Pvec_eq, commutator_centralizer_siegDiag_two (K := ZMod 2) (by simp) (m := 3) le_rfl 3,
    tvec_eq]
  exact mem_centralizer_singleton_iff.mpr rfl

section Radical

@[expose] def emb6 : Fin 6 → Fin 4 ⊕ Fin 4 :=
  ![.inl 0, .inl 1, .inl 2, .inr 0, .inr 1, .inr 2]

theorem emb6_not_mem (i : Fin 6) : emb6 i ∉ coords (3 : Fin 4) := by
  rw [mem_coords]
  fin_cases i <;> decide

theorem exists_emb6 {t : Fin 4 ⊕ Fin 4} (ht : t ∉ coords (3 : Fin 4)) : ∃ i, emb6 i = t := by
  rw [mem_coords] at ht
  revert t
  decide

theorem row_mul {q q' : StatedSp 4 (ZMod 2)} (hq : q ∈ transvRadical (ZMod 2) (3 : Fin 4))
    (hq' : q' ∈ transvRadical (ZMod 2) (3 : Fin 4)) {t : Fin 4 ⊕ Fin 4}
    (ht : t ∉ coords (3 : Fin 4)) :
    mat 4 (ZMod 2) (q * q') (Sum.inl 3) t =
      mat 4 (ZMod 2) q (Sum.inl 3) t + mat 4 (ZMod 2) q' (Sum.inl 3) t := by
  have htp : t ≠ Sum.inl 3 := fun h => ht (h ▸ inl_mem_coords 3)
  rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add t (Sum.inl 3) htp]
  · rw [hq'.2 t ht t htp, Matrix.one_apply_eq, mul_one, hq.1 (Sum.inl 3), Matrix.one_apply_eq,
      one_mul]
  · rintro u ⟨hut, hup⟩
    rw [hq'.2 t ht u hup, Matrix.one_apply_ne hut, mul_zero]

@[expose] noncomputable def psi8 :
    ↥(transvRadical (ZMod 2) (3 : Fin 4)) →* Multiplicative (Fin 6 → ZMod 2) where
  toFun q := Multiplicative.ofAdd fun i => mat 4 (ZMod 2) q (Sum.inl 3) (emb6 i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    have h : emb6 i ≠ Sum.inl 3 := fun h => emb6_not_mem i (h ▸ inl_mem_coords 3)
    simp only [toAdd_ofAdd, OneMemClass.coe_one, map_one, toAdd_one, Pi.zero_apply]
    exact Matrix.one_apply_ne h.symm
  map_mul' q q' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply, Subgroup.coe_mul]
    exact row_mul q.2 q'.2 (emb6_not_mem i)

theorem psi8_apply (q : ↥(transvRadical (ZMod 2) (3 : Fin 4))) (i : Fin 6) :
    Multiplicative.toAdd (psi8 q) i = mat 4 (ZMod 2) q (Sum.inl 3) (emb6 i) := rfl

theorem psi8_mk {g : StatedSp 4 (ZMod 2)} (hg : g ∈ transvRadical (ZMod 2) (3 : Fin 4))
    (i : Fin 6) : Multiplicative.toAdd (psi8 ⟨g, hg⟩) i = mat 4 (ZMod 2) g (Sum.inl 3) (emb6 i) :=
  rfl

theorem eq_siegDiag_of_psi8 {q : ↥(transvRadical (ZMod 2) (3 : Fin 4))} (h : psi8 q = 1) :
    (q : StatedSp 4 (ZMod 2)) =
      siegDiag (ZMod 2) 3 (mat 4 (ZMod 2) q (Sum.inl 3) (Sum.inr 3)) := by
  refine eq_siegDiag_of_mem_transvRadical q.2 fun t ht => ?_
  obtain ⟨i, rfl⟩ := exists_emb6 ht
  have e := congrFun (congrArg Multiplicative.toAdd h) i
  rwa [psi8_apply, toAdd_one, Pi.zero_apply] at e

theorem siegDiag_entry (c : ZMod 2) :
    mat 4 (ZMod 2) (siegDiag (ZMod 2) (3 : Fin 4) c) (Sum.inl 3) (Sum.inr 3) = c := by
  rw [mat_siegDiag]
  simp [Matrix.fromBlocks_apply₁₂, Matrix.single_apply]

theorem psi8_siegDiag (c : ZMod 2)
    (h : siegDiag (ZMod 2) (3 : Fin 4) c ∈ transvRadical (ZMod 2) (3 : Fin 4)) :
    psi8 ⟨siegDiag (ZMod 2) (3 : Fin 4) c, h⟩ = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [psi8_mk, mat_siegDiag, toAdd_one, Pi.zero_apply]
  fin_cases i <;> simp [emb6, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.one_apply, Matrix.single_apply]

theorem card_ker_psi8 : Nat.card psi8.ker = 2 := by
  have e : psi8.ker ≃ ZMod 2 :=
    { toFun := fun q => mat 4 (ZMod 2)
        ((q : ↥(transvRadical (ZMod 2) (3 : Fin 4))) : StatedSp 4 (ZMod 2)) (Sum.inl 3) (Sum.inr 3)
      invFun := fun c => ⟨⟨siegDiag (ZMod 2) 3 c, siegDiag_mem_transvRadical 3 c⟩,
        MonoidHom.mem_ker.mpr (psi8_siegDiag c _)⟩
      left_inv := fun q => Subtype.ext (Subtype.ext (eq_siegDiag_of_psi8
        (MonoidHom.mem_ker.mp q.2)).symm)
      right_inv := fun c => siegDiag_entry c }
  rw [Nat.card_congr e, Nat.card_zmod]

theorem emb6_injective : Function.Injective emb6 := by decide

theorem psi8_surjective : Function.Surjective psi8 := by
  have key : ∀ (g : StatedSp 4 (ZMod 2)) (hg : g ∈ transvRadical (ZMod 2) (3 : Fin 4)) (i : Fin 6),
      (∀ t, t ∉ coords (3 : Fin 4) →
        mat 4 (ZMod 2) g (Sum.inl 3) t = if t = emb6 i then 1 else 0) →
      Multiplicative.ofAdd (Pi.single i 1) ∈ psi8.range := by
    intro g hg i h
    refine MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    funext k
    rw [psi8_mk, h _ (emb6_not_mem k), toAdd_ofAdd, Pi.single_apply]
    simp only [emb6_injective.eq_iff]
  have hlevi : ∀ (j : Fin 4) (hj : (3 : Fin 4) ≠ j) (t : Fin 4 ⊕ Fin 4),
      t ∉ coords (3 : Fin 4) → mat 4 (ZMod 2) (leviTv (ZMod 2) hj 1) (Sum.inl 3) t =
        if t = Sum.inl j then 1 else 0 := by
    intro j hj t ht
    have htp : (Sum.inl 3 : Fin 4 ⊕ Fin 4) ≠ t := fun h => ht (h ▸ inl_mem_coords 3)
    have e := mat_leviTv_mul_apply hj (1 : ZMod 2) 1 t
    rw [mul_one, map_one, one_mul] at e
    rw [e, Matrix.one_apply_ne htp, zero_add, Matrix.one_apply]
    by_cases h : t = Sum.inl j
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  have hsieg : ∀ (j : Fin 4) (hj : (3 : Fin 4) ≠ j) (t : Fin 4 ⊕ Fin 4),
      t ∉ coords (3 : Fin 4) → mat 4 (ZMod 2) (siegPair (ZMod 2) 3 j 1) (Sum.inl 3) t =
        if t = Sum.inr j then 1 else 0 := by
    intro j hj t ht
    have htp : (Sum.inl 3 : Fin 4 ⊕ Fin 4) ≠ t := fun h => ht (h ▸ inl_mem_coords 3)
    have e := mat_siegPair_mul_apply hj (1 : ZMod 2) 1 t
    rw [mul_one, map_one, one_mul] at e
    rw [e, Matrix.one_apply_ne htp, zero_add, Matrix.one_apply]
    by_cases h : t = Sum.inr j
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  have hbasis : ∀ i : Fin 6, Multiplicative.ofAdd (Pi.single i 1) ∈ psi8.range := by
    intro i
    fin_cases i
    · exact key _ (leviTv_mem_transvRadical (by decide : (3 : Fin 4) ≠ 0) 1) _
        (hlevi 0 (by decide))
    · exact key _ (leviTv_mem_transvRadical (by decide : (3 : Fin 4) ≠ 1) 1) _
        (hlevi 1 (by decide))
    · exact key _ (leviTv_mem_transvRadical (by decide : (3 : Fin 4) ≠ 2) 1) _
        (hlevi 2 (by decide))
    · exact key (siegPair (ZMod 2) 3 0 1) (siegPair_mem_transvRadical 1) _ (hsieg 0 (by decide))
    · exact key (siegPair (ZMod 2) 3 1 1) (siegPair_mem_transvRadical 1) _ (hsieg 1 (by decide))
    · exact key (siegPair (ZMod 2) 3 2 1) (siegPair_mem_transvRadical 1) _ (hsieg 2 (by decide))
  intro w
  have hw : w = ∏ i : Fin 6, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd w i)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    exact (Finset.univ_sum_single _).symm
  have hmem : w ∈ psi8.range := by
    rw [hw]
    refine Subgroup.prod_mem _ fun i _ => ?_
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 (Multiplicative.toAdd w i) with h | h
    · rw [h, Pi.single_zero, ofAdd_zero]
      exact one_mem _
    · rw [h]
      exact hbasis i
  exact MonoidHom.mem_range.mp hmem

theorem card_Q3 : Nat.card ↥(transvRadical (ZMod 2) (3 : Fin 4)) = 128 := by
  have h64 : Nat.card (Multiplicative (Fin 6 → ZMod 2)) = 2 ^ 6 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have key : Nat.card ↥(transvRadical (ZMod 2) (3 : Fin 4)) = 2 * 2 ^ 6 := by
    rw [← Subgroup.card_mul_index psi8.ker, Subgroup.index_ker, card_ker_psi8,
      MonoidHom.range_eq_top.mpr psi8_surjective, Subgroup.card_top, h64]
  exact key.trans (by norm_num)

theorem mul_self_Q3 {q : StatedSp 4 (ZMod 2)} (hq : q ∈ transvRadical (ZMod 2) (3 : Fin 4)) :
    q * q = 1 := by
  rw [mul_self_eq_siegDiag hq]
  suffices h : mat 4 (ZMod 2) (q * q) (Sum.inl 3) (Sum.inr 3) = 0 by rw [h, siegDiag_zero]
  have hrow := mat_inr_apply_of_col_inl hq.1
  have hpar : ∀ t, t ∉ coords (3 : Fin 4) →
      mat 4 (ZMod 2) q (par t) (Sum.inr 3) = mat 4 (ZMod 2) q (Sum.inl 3) t := by
    intro t ht
    have htp : t ≠ Sum.inl 3 := fun h => ht (h ▸ inl_mem_coords 3)
    have key := congrFun (congrFun (mat_transpose_mul_gram_mul q) t) (Sum.inr 3)
    rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      Fintype.sum_eq_add t (Sum.inl 3) htp] at key
    · rw [hq.2 t ht t htp, Matrix.one_apply_eq, one_mul, par_inl, hrow, Matrix.one_apply_eq,
        mul_one, sgn_inl, mul_one] at key
      have hne : ¬ (Sum.inr 3 : Fin 4 ⊕ Fin 4) = par t := by
        rcases t with x | x
        · intro h
          have : x = 3 := Sum.inr_injective h.symm
          exact htp (congrArg Sum.inl this)
        · exact fun h => Sum.inr_ne_inl h
      rw [if_neg hne] at key
      have hsgn : sgn (ZMod 2) t = 1 := by
        rcases t with x | x
        · rfl
        · show (-1 : ZMod 2) = 1
          decide
      rw [hsgn, one_mul] at key
      have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h2 _ _ key
    · rintro u ⟨hut, hup⟩
      rw [hq.2 t ht u hup, Matrix.one_apply_ne hut, zero_mul]
  have hll := hq.1 (Sum.inl 3)
  rw [Matrix.one_apply_eq] at hll
  have hrr := hrow (Sum.inr 3)
  rw [Matrix.one_apply_eq] at hrr
  rw [map_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
  have h0 := hpar (Sum.inl 0) (by rw [mem_coords]; decide)
  have h1 := hpar (Sum.inl 1) (by rw [mem_coords]; decide)
  have h2 := hpar (Sum.inl 2) (by rw [mem_coords]; decide)
  have h3 := hpar (Sum.inr 0) (by rw [mem_coords]; decide)
  have h4 := hpar (Sum.inr 1) (by rw [mem_coords]; decide)
  have h5 := hpar (Sum.inr 2) (by rw [mem_coords]; decide)
  simp only [par_inl, par_inr] at h0 h1 h2 h3 h4 h5
  rw [h3, h4, h5, h0, h1, h2, hll, hrr]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hz : ∀ a b c d e f g : ZMod 2,
      a * b + c * d + e * f + 1 * g + (b * a + d * c + f * e + g * 1) = 0 := by
    intro a b c d e f g
    rw [mul_comm b a, mul_comm d c, mul_comm f e, mul_comm g 1]
    exact h2 _
  exact hz _ _ _ _ _ _ _

theorem isElemAb_Q3 : IsElemAb 2 7 (transvRadical (ZMod 2) (3 : Fin 4)) := by
  have hsq : ∀ q : ↥(transvRadical (ZMod 2) (3 : Fin 4)), q * q = 1 := fun q =>
    Subtype.ext (mul_self_Q3 q.2)
  have hinv : ∀ q : ↥(transvRadical (ZMod 2) (3 : Fin 4)), q⁻¹ = q := fun q =>
    inv_eq_of_mul_eq_one_right (hsq q)
  have hcomm : ∀ a b : ↥(transvRadical (ZMod 2) (3 : Fin 4)), a * b = b * a := fun a b => by
    rw [← hinv (a * b), _root_.mul_inv_rev, hinv, hinv]
  exact ⟨{ is_comm := ⟨hcomm⟩
           exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
             rw [pow_two]; exact hsq g }, card_Q3.trans (by norm_num)⟩

end Radical

section Main


theorem kf_sp6O7 : KF_Sp6O7 := by
  intro X _ _ L t₀ ht₀ hLC hL hTL hT hcomm
  obtain ⟨f', σ', τ', ht', hfL', hLf', hTL1', hτt', hσg', hσh', hσc', hconj'⟩ :=
    exists_coords (X := StatedSp 4 (ZMod 2)) (L := FF81.Am4.Svec) (t₀ := FF81.Am4.tvec)
      orderOf_tvec Svec_le_Pvec statedModel_Svec setMul_Pvec
      (by rw [Op_Pvec]; exact isElemAb_Q3) tvec_mem_commutator
  obtain ⟨f, σ, τ, ht, hfL, hLf, hTL1, hτt, hσg, hσh, hσc, hconj⟩ :=
    exists_coords ht₀ hLC hL hTL hT hcomm
  have hσ : σ = σ' := by
    refine MonoidHom.eq_of_eqOn_dense closure_gens_eq_top ?_
    rintro _ (rfl | rfl | rfl)
    · exact Units.ext (hσg.trans hσg'.symm)
    · exact Units.ext (hσh.trans hσh'.symm)
    · exact Units.ext (hσc.trans hσc'.symm)
  subst hσ
  have hTCX : Op 2 (Cen t₀) ≤ Cen t₀ := Subgroup.map_subtype_le _
  have hTC8 : Op 2 FF81.Am4.Pvec ≤ FF81.Am4.Pvec := Subgroup.map_subtype_le _
  have hdecX : ∀ c ∈ Cen t₀, ∃ u ∈ Op 2 (Cen t₀), ∃ l ∈ L, c = u * l := by
    intro c hc
    have hc' : c ∈ setMul (Op 2 (Cen t₀)) L := by rw [hTL]; exact hc
    obtain ⟨u, hu, l, hl, rfl⟩ := hc'
    exact ⟨u, hu, l, hl, rfl⟩
  have hdec8 : ∀ c ∈ FF81.Am4.Pvec, ∃ u ∈ Op 2 FF81.Am4.Pvec, ∃ l ∈ FF81.Am4.Svec, c = u * l := by
    intro c hc
    have hc' : c ∈ setMul (Op 2 FF81.Am4.Pvec) FF81.Am4.Svec := by rw [setMul_Pvec]; exact hc
    obtain ⟨u, hu, l, hl, rfl⟩ := hc'
    exact ⟨u, hu, l, hl, rfl⟩
  obtain ⟨Ψ, hΨl, hΨr⟩ := exists_equiv_model hTCX hLC hdecX f hfL hLf hTL1 σ τ hconj
  obtain ⟨Ψ', hΨl', hΨr'⟩ := exists_equiv_model hTC8 Svec_le_Pvec hdec8 f' hfL' hLf' hTL1' σ τ'
    hconj'
  refine ⟨Ψ'.symm.trans Ψ, ?_, fun x => ?_⟩
  · have h1 : Ψ'.symm ⟨FF81.Am4.tvec, FF81.Am4.tvec_mem_Pvec⟩ =
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 0 1)) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hΨl', ← hτt', MulEquiv.symm_apply_apply]
    rw [MulEquiv.trans_apply, h1, hΨl, ← hτt, MulEquiv.symm_apply_apply]
  · have h1 := mem_iff_left_eq_one hfL hLf hTL1 hΨl hΨr (Ψ'.symm x)
    have h2 := mem_iff_left_eq_one hfL' hLf' hTL1' hΨl' hΨr' (Ψ'.symm x)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [MulEquiv.trans_apply, h1, h2]

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6O7
