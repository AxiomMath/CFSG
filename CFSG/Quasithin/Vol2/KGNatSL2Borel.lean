module

public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.KGNatCoord

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.CGT.Timmesfeld75 CFSG.Quasithin
open scoped MatrixGroups

section Borel

variable {F : Type} [Field F]

theorem pow_borel_apply {b : SL(2, F)} (hb : b ∈ borel F) (k : ℕ) :
    (b ^ k) 1 0 = 0 ∧ (b ^ k) 0 0 = b 0 0 ^ k := by
  have hb' : b 1 0 = 0 := hb
  induction k with
  | zero => exact ⟨by rw [pow_zero, one_apply_10], by rw [pow_zero, one_apply_00, pow_zero]⟩
  | succ k ih =>
    rw [pow_succ, mul_apply_10, mul_apply_00, ih.1, ih.2, hb']
    exact ⟨by ring, by ring⟩

theorem pow_card_sub_one_mem_utri [Finite F] {b : SL(2, F)} (hb : b ∈ borel F) :
    b ^ (Nat.card F - 1) ∈ utri F := by
  have : Fintype F := Fintype.ofFinite F
  have hb' : b 1 0 = 0 := hb
  have h00 : b 0 0 ≠ 0 := by
    intro h0
    have := sl2_det b
    rw [h0, hb', zero_mul, mul_zero, sub_zero] at this
    exact zero_ne_one this
  obtain ⟨h1, h2⟩ := pow_borel_apply hb (Nat.card F - 1)
  refine ⟨h1, ?_⟩
  rw [h2, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ h00

end Borel

theorem factSL2Borel_holds : Ch11.SecC.FactSL2Borel := by
  intro F _ _ n hn hF B hB hdvd x hx hodd
  have : CharP F 2 := charP_two_of_card (by omega) hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set P := H.map B.subtype with hPdef
  have hPcard : Nat.card P = Nat.card F := by
    rw [hPdef, Subgroup.card_map_of_injective B.subtype_injective, hH, hF]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := n) (by rw [hPcard, hF])
  have hPB : P ≤ B := Subgroup.map_subtype_le H
  obtain ⟨g, hg⟩ := exists_conj_utri_eq hP2 hPcard
  have hBN : ∀ b ∈ B, g⁻¹ * b * g ∈ borel F := by
    intro b hb
    by_contra hnb
    apply hB
    have h2 : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (utri F ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (g⁻¹ * b * g) (utri F)) =
          P ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup b P := by
      rw [conjSubgroup_sup_eq_sup, conjSubgroup_conjSubgroup, hg,
        show g * (g⁻¹ * b * g) = b * g by group, ← conjSubgroup_conjSubgroup, hg]
    rw [utri_sup_conj_eq_top hnb, conjSubgroup_top] at h2
    rw [eq_top_iff, h2]
    refine sup_le hPB fun y hy => ?_
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hy
    have := B.mul_mem (B.mul_mem hb (hPB hy)) (B.inv_mem hb)
    rwa [show b * (b⁻¹ * y * b) * b⁻¹ = y by group] at this
  set b := g⁻¹ * x * g with hbdef
  have hb : b ∈ borel F := hBN x hx
  have hxb : x = g * b * g⁻¹ := by rw [hbdef]; group
  have hy := pow_card_sub_one_mem_utri hb
  have hy2 : (b ^ (Nat.card F - 1)) ^ 2 = 1 := isElemAbelian_utri.2 _ hy
  have hordb : orderOf b = orderOf x := by
    rw [hxb]
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective b
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at h
    exact h.symm
  have hodd' : Odd (orderOf (b ^ (Nat.card F - 1))) :=
    Odd.of_dvd_nat (hordb ▸ hodd) (orderOf_pow_dvd _)
  have h1 : orderOf (b ^ (Nat.card F - 1)) = 1 := by
    have hd := orderOf_dvd_of_pow_eq_one hy2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  rw [← hF, hxb, conj_pow, orderOf_eq_one_iff.mp h1, mul_one, mul_inv_cancel]

section FPF

theorem det_eq_one_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : g ∈ CFSG.Assembly.LowTwoRank.StatedSL n K) : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem mul_self_eq_one_of_mulVec_eq {F : Type} [Field F] [CharP F 2]
    {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1) {x : Fin 2 → F} (hx : M.mulVec x = x)
    (hx0 : x ≠ 0) : M * M = 1 := by
  rw [Matrix.det_fin_two] at hdet
  have e0 : M 0 0 * x 0 + M 0 1 * x 1 = x 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hx 0
  have e1 : M 1 0 * x 0 + M 1 1 * x 1 = x 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hx 1
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hD0 : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * x 0 = 0 := by
    linear_combination (M 1 1 - 1) * e0 - M 0 1 * e1
  have hD1 : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * x 1 = 0 := by
    linear_combination (M 0 0 - 1) * e1 - M 1 0 * e0
  have hD : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = 0 := by
    by_contra hne
    apply hx0
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp hD0).resolve_left hne
    · exact (mul_eq_zero.mp hD1).resolve_left hne
  have htr : M 0 0 + M 1 1 = 0 := by linear_combination hdet - hD + h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 0 * htr - hdet - h2
  · linear_combination M 0 1 * htr
  · linear_combination M 1 0 * htr
  · linear_combination M 1 1 * htr - hdet - h2

end FPF

theorem factSL2NatFPF_holds : Ch11.SecC.FactSL2NatFPF := by
  intro F _ _ n hn hF W _ H U Z π hπ h hh hodd h1 u hu hfix
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨f, hmul, hker, -, hact⟩ := exists_coord (linModelNat _) hπ
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F), π γ = ⟨h, hh⟩ :=
    hπ.1 ⟨h, hh⟩
  have hγ' : ((π γ : ↥H) : MulAut W) = h := congrArg Subtype.val hγ
  have hhu : h u ∈ U := hπ.2.2.2.1 ⟨h, hh⟩ u hu
  have hf1 : f 1 = 0 := (hker 1 U.one_mem).mpr Z.one_mem
  have hfinv : f u⁻¹ = - f u := by
    have := hmul u hu u⁻¹ (U.inv_mem hu)
    rw [mul_inv_cancel, hf1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hfix' : f (h u) = f u := by
    have := (hker _ (U.mul_mem hhu (U.inv_mem hu))).mpr hfix
    rw [hmul _ hhu _ (U.inv_mem hu), hfinv, ← sub_eq_add_neg] at this
    exact sub_eq_zero.mp this
  have hγu : f (h u) = ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (f u) := by
    rw [← hγ']
    exact (hact γ u hu).trans (linModelNat_lin _ γ (f u))
  by_contra huZ
  have hfu0 : f u ≠ 0 := fun h0 => huZ ((hker u hu).mp h0)
  have hMM := mul_self_eq_one_of_mulVec_eq (det_eq_one_of_mem_statedSL γ.2)
    (hγu.symm.trans hfix') hfu0
  have hγγ : γ * γ = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hMM
  have hh2 : h ^ 2 = 1 := by
    have := congrArg (fun g => ((π g : ↥H) : MulAut W)) hγγ
    simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, hγ'] at this
    rw [sq, this]
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hh2) with h' | h'
  · exact h1 (orderOf_eq_one_iff.mp h')
  · rw [h'] at hodd
    exact absurd hodd (by decide)

end CFSG.Quasithin.Vol2.KGNat
