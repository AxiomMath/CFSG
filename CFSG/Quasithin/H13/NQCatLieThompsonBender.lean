module

public import CFSG.Quasithin.H13.NQCatLieThompsonCore
public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.Quasithin.H13.NQCat.LieThompson

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification

theorem thompsonModel_linear {K : Type} [Group K] [Finite K] {n : ℕ} (h : BenderType K n 1 1) :
    ThompsonModel K := by
  obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  refine ⟨h.outer_linear.1, fun P hP hE α hα2 hαout _ => ?_⟩
  obtain ⟨E, hEP, -, hE16, hEC⟩ := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  obtain ⟨t, hc⟩ := exists_benderCore_psl2 e hn (hP.2.1.toSylow hP')
  rw [IsPGroup.toSylow_coe] at hc
  have hPZ : rootCenter P = P :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc.card_center, hc.card_eq, pow_one])
  have hZe : IsElemAbelian 2 (rootCenter P) :=
    isElemAbelian_of_forall (fun x hx y hy => Subgroup.mem_centralizer_iff.1 hy.2 x hx.1)
      hc.center_sq
  have hPsq : ∀ x ∈ P, x * x = 1 := fun x hx => hc.center_sq x (by rw [hPZ]; exact hx)
  have h16 : 16 ≤ 2 ^ n := by
    rw [← hc.card_center, ← hE16]
    exact Subgroup.card_le_of_le fun x hx => ⟨hEP hx, hEC hx⟩
  have hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹ := fun ⟨g, hg⟩ =>
    hαout ⟨g, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hg x]⟩
  obtain ⟨m, rfl, ⟨eF⟩, -⟩ := h.fixed_linear α hα2 hout
  have hm : 2 ≤ m := by
    by_contra hm
    have : 2 ^ (2 * m) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfix : Nat.card ↥(P ⊓ autFixed α) ≤ 2 ^ m := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      P ⊓ autFixed α ≤ autFixed α)).toEquiv,
      ← Subgroup.card_map_of_injective (f := eF.toMonoidHom) eF.injective]
    refine card_le_of_sq_eq_one_psl2 (by omega) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hPsq x hx.1), map_one]
  refine ⟨rootCenter P, inf_le_left, hZe, ?_⟩
  rw [hc.card_center]
  calc 2 * Nat.card ↥(P ⊓ autFixed α) ≤ 2 * 2 ^ m := by gcongr
    _ = 2 ^ (m + 1) := by ring
    _ < 2 ^ (2 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem thompsonModel_suzuki {K : Type} [Group K] [Finite K]
    {n e : ℕ} (h : BenderType K n 2 e) : ThompsonModel K := by
  refine ⟨h.outer_suzuki.1, fun P _ _ α hα2 hαout _ => ?_⟩
  exfalso
  obtain ⟨v, -, hv⟩ := h.exists_inner_of_sq_eq_one_suzuki α hα2
  exact hαout ⟨v, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hv x]⟩

end CFSG.Quasithin.H13.NQCat.LieThompson
