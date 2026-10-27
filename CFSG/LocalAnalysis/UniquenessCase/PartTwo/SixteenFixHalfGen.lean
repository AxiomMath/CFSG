module

import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MB
import CFSG.Quasithin.Background.G64Realize
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16fh_le_commSub_sup {D : FFModel} {H : Subgroup (MulAut W)}
    {I Z : Subgroup W} {π : D.Gam →* ↥H} (h : D.RealizesVia H I Z π)
    (hG : D.sec ≤
      Subgroup.closure {x | ∃ γ : D.Gam, ∃ y ∈ D.sec, D.act γ y * y⁻¹ = x} ⊔ D.ker) :
    I ≤ commSub I H ⊔ Z := by
  obtain ⟨-, -, hks, hIinv, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have key : ∀ x ∈ Subgroup.closure
        {x | ∃ γ : D.Gam, ∃ y ∈ D.sec, D.act γ y * y⁻¹ = x} ⊔ D.ker,
      ∃ hx : x ∈ D.sec, ∃ c : ↥I, (c : W) ∈ commSub I H ∧
        β c = QuotientGroup.mk ⟨x, hx⟩ := by
    intro x hx
    rw [← Subgroup.closure_eq D.ker, ← Subgroup.closure_union] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨γ, y, hy, rfl⟩ | hx
      · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, hy⟩)
        have hπu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I := hIinv (π γ) u u.2
        have hy' : D.act γ (y : D.Amb) ∈ D.sec := hsec γ y hy
        refine ⟨D.sec.mul_mem hy' (D.sec.inv_mem hy), ⟨_, hπu⟩ * u⁻¹,
          Subgroup.subset_closure ⟨((π γ : ↥H) : MulAut W), (π γ).2, (u : W), u.2, rfl⟩, ?_⟩
        rw [map_mul, map_inv, hβe γ u ⟨y, hy⟩ hπu hy' hu, hu]
        rfl
      · refine ⟨hks hx, 1, (commSub I H).one_mem, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hx
    | one => exact ⟨D.sec.one_mem, 1, (commSub I H).one_mem, by rw [map_one]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hx, c, hc, hcx⟩ := hx
      obtain ⟨hy, d, hd, hdy⟩ := hy
      exact ⟨D.sec.mul_mem hx hy, c * d, (commSub I H).mul_mem hc hd,
        by rw [map_mul, hcx, hdy]; rfl⟩
    | inv x _ hx =>
      obtain ⟨hx, c, hc, hcx⟩ := hx
      exact ⟨D.sec.inv_mem hx, c⁻¹, (commSub I H).inv_mem hc, by rw [map_inv, hcx]; rfl⟩
  intro w hw
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
  obtain ⟨hmx, c, hc, hcm⟩ := key m (hG m.2)
  have h1 : β (⟨w, hw⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_inv, hcm, ← hm]
    exact mul_inv_cancel _
  have h2 := (hβk _).mp h1
  have e : w = (w * (c : W)⁻¹) * c := by group
  rw [e]
  exact (commSub I H ⊔ Z).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hc)

private theorem s16fh_pairVec_mul {n : ℕ} (i k l : Fin n) :
    G64.pairVec i k * G64.pairVec i l = G64.pairVec k l := by
  apply Multiplicative.toAdd.injective
  simp only [G64.pairVec, toAdd_mul, toAdd_ofAdd]
  funext m
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> decide

private theorem s16fh_pairVec_self {n : ℕ} (i : Fin n) : G64.pairVec i i = 1 := by
  have h := s16fh_pairVec_mul i i i
  exact mul_left_cancel (h.trans (mul_one _).symm)

private theorem s16fh_pairVec_inv {n : ℕ} (i j : Fin n) :
    (G64.pairVec i j)⁻¹ = G64.pairVec i j := by
  have h : G64.pairVec i j * G64.pairVec i j = 1 := by
    rw [s16fh_pairVec_mul i j j, s16fh_pairVec_self j]
  exact inv_eq_of_mul_eq_one_right h

private theorem s16fh_pairVec_comm {n : ℕ} (i j : Fin n) :
    G64.pairVec i j = G64.pairVec j i := by
  show Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1) =
    Multiplicative.ofAdd (Pi.single j 1 + Pi.single i 1)
  rw [add_comm]

private theorem s16fh_pairVec_mem_comm {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    G64.pairVec b c ∈
      {x | ∃ γ : ↥(alternatingGroup (Fin n)), ∃ y ∈ G6.coreMod n,
        G6.permAct n (γ : Equiv.Perm (Fin n)) y * y⁻¹ = x} := by
  refine ⟨⟨Equiv.swap a b * Equiv.swap b c, ?_⟩, G64.pairVec a c,
    G64.pairVec_mem_coreMod a c, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]
    rfl
  · show G6.permAct n (Equiv.swap a b * Equiv.swap b c) (G64.pairVec a c) *
      (G64.pairVec a c)⁻¹ = G64.pairVec b c
    have hsa : (Equiv.swap a b * Equiv.swap b c) a = b := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
    have hsc : (Equiv.swap a b * Equiv.swap b c) c = a := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
    rw [G64.permAct_pairVec, hsa, hsc, s16fh_pairVec_comm b a, s16fh_pairVec_inv a c,
      s16fh_pairVec_mul a b c]

private theorem s16fh_coreMod_le_closure_pairVec {n : ℕ} (i : Fin n) :
    G6.coreMod n ≤ Subgroup.closure (Set.range fun l : Fin n => G64.pairVec i l) := by
  intro x hx
  have hx' : x = ∏ l, G64.pairVec i l ^ (Multiplicative.toAdd x l).val := by
    apply Multiplicative.toAdd.injective
    funext m
    rw [toAdd_prod, Finset.sum_apply]
    simp only [toAdd_pow, G64.pairVec, toAdd_ofAdd, Pi.smul_apply, Pi.add_apply, smul_add,
      Finset.sum_add_distrib]
    have h1 : ∑ l, (Multiplicative.toAdd x l).val •
        (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) m =
        (∑ l, Multiplicative.toAdd x l) * (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) m := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id]
    have h2 : ∑ l, (Multiplicative.toAdd x l).val •
        (Pi.single l (1 : ZMod 2) : Fin n → ZMod 2) m = Multiplicative.toAdd x m := by
      rw [Finset.sum_eq_single m]
      · rw [Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id', id]
      · intro l _ hl
        rw [Pi.single_eq_of_ne (Ne.symm hl), smul_zero]
      · simp
    rw [h1, h2, G6.mem_coreMod.1 hx, zero_mul, zero_add]
  rw [hx']
  exact Subgroup.prod_mem _ fun l _ =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self l)) _

theorem s16fh_altDn_generator {n : ℕ} (hn : 3 ≤ n) :
    (FFModel.altDn n).sec ≤
      Subgroup.closure {x | ∃ γ : (FFModel.altDn n).Gam, ∃ y ∈ (FFModel.altDn n).sec,
        (FFModel.altDn n).act γ y * y⁻¹ = x} ⊔ (FFModel.altDn n).ker := by
  have hgen : G6.coreMod n ≤ Subgroup.closure
      {x | ∃ γ : ↥(alternatingGroup (Fin n)), ∃ y ∈ G6.coreMod n,
        G6.permAct n (γ : Equiv.Perm (Fin n)) y * y⁻¹ = x} := by
    let i : Fin n := ⟨0, by omega⟩
    refine (s16fh_coreMod_le_closure_pairVec i).trans ?_
    rw [Subgroup.closure_le]
    rintro x ⟨l, rfl⟩
    beta_reduce
    by_cases hli : l = i
    · rw [hli, s16fh_pairVec_self i]
      exact Subgroup.one_mem _
    · have hcard : ({i, l} : Finset (Fin n)).card <
          (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_pair (Ne.symm hli), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      have hai : a ≠ i := fun h => ha (by simp [h])
      have hal : a ≠ l := fun h => ha (by simp [h])
      exact Subgroup.subset_closure
        (s16fh_pairVec_mem_comm (a := a) (b := i) (c := l) hai (Ne.symm hli) hal)
  intro x hx
  exact Subgroup.mem_sup_left (hgen hx)

theorem s16fh_commSub_sup_alt {n : ℕ} (hn : 3 ≤ n) {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : AlternatingNatural L I Z n) : commSub I L ⊔ Z = I := by
  obtain ⟨π, hπ⟩ := h
  refine le_antisymm (sup_le ?_ hπ.2.1) ?_
  · exact commSub_le_of_invariant fun x hx w hw => hπ.2.2.2.1 ⟨x, hx⟩ w hw
  · exact s16fh_le_commSub_sup hπ (s16fh_altDn_generator hn)

theorem s16fh_commSub_sup_nat {K : Type} [Field K] {d : ℕ} (hd : 2 ≤ d) {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (h : (FFModel.nat (StatedSL d K)).Realizes L I Z) :
    commSub I L ⊔ Z = I := by
  obtain ⟨π, hπ⟩ := h
  refine le_antisymm (sup_le ?_ hπ.2.1) ?_
  · exact commSub_le_of_invariant fun x hx w hw => hπ.2.2.2.1 ⟨x, hx⟩ w hw
  · exact s16fh_le_commSub_sup hπ (CFSG.Quasithin.H13.M338.nat_gen hd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
