module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1MathieuInputs
import CFSG.Sporadic.Schreier.M11
import CFSG.ClassicalInvolution.Q3.M11Kernel
import Certificates.Certificate15068

public section

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Ronan148R CFSG.ClassicalInvolution.Q3

namespace CertificateChecks.Batch148006

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Ronan148R CFSG.ClassicalInvolution.Q3

theorem m11_fix_base (g : NativeSporadic.M11) (h : ∀ i : Fin 11, i.val < 4 → g.1 i = i) :
    g = 1 := by
  have hC := chain m11_hyp_kernel
  have step : ∀ i < 4, g ∈ lvl Native.m11Data m11a m11b i →
      g ∈ lvl Native.m11Data m11a m11b (i + 1) := by
    intro i hi hg
    refine (hC.2.1 i (by change i < 4; omega) g hg).1 ?_
    have hb : Native.m11Data.base[i]! = i := by
      interval_cases i <;> rfl
    rw [hb]
    change CFSG.Sporadic.Th.idx 11 g i = i
    rw [CFSG.Sporadic.Th.idx_of_lt g (show i < 11 by omega)]
    exact congrArg Fin.val (h ⟨i, by omega⟩ hi)
  have h0 : g ∈ lvl Native.m11Data m11a m11b 0 := by
    rw [lvl_zero m11_hyp_kernel]
    trivial
  have h4 : g ∈ lvl Native.m11Data m11a m11b 4 :=
    step 3 (by norm_num) (step 2 (by norm_num) (step 1 (by norm_num) (step 0 (by norm_num) h0)))
  have hcard : Nat.card (lvl Native.m11Data m11a m11b 4) = 1 := by
    have hc := hC.2.2 4 (by decide)
    change _ = ∏ l ∈ Finset.Ico 4 4, _ at hc
    simpa only [Finset.Ico_self, Finset.prod_empty] using hc
  rw [Subgroup.eq_bot_of_card_eq _ hcard] at h4
  simpa using h4

def fourImages (g : NativeSporadic.M11) : Fin 4 ↪ Fin 11 :=
  (Fin.castLEEmb (show 4 ≤ 11 by norm_num)).trans g.1.toEmbedding

theorem fourImages_bijective : Function.Bijective fourImages := by
  have hinj : Function.Injective fourImages := by
    intro g g' hgg
    have hfix : g⁻¹ * g' = 1 := by
      refine m11_fix_base _ fun i hi => ?_
      have h1 : g.1 i = g'.1 i := congrArg (fun f : Fin 4 ↪ Fin 11 => f ⟨i.val, hi⟩) hgg
      change (g.1)⁻¹ (g'.1 i) = i
      rw [← h1]
      simp
    exact inv_mul_eq_one.1 hfix
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_m11_kernel, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp [Nat.descFactorial]

theorem m11_fix_four (g : Equiv.Perm (Fin 11)) (hg : g ∈ NativeSporadic.M11) (p : Fin 4 ↪ Fin 11)
    (hp : ∀ i, g (p i) = p i) : g = 1 := by
  obtain ⟨h, hh⟩ := fourImages_bijective.2 p
  have hhp : ∀ i : Fin 4, h.1 (Fin.castLE (show 4 ≤ 11 by norm_num) i) = p i :=
    fun i => congrArg (fun f : Fin 4 ↪ Fin 11 => f i) hh
  have hk : (⟨h.1⁻¹ * g * h.1, NativeSporadic.M11.mul_mem
      (NativeSporadic.M11.mul_mem (NativeSporadic.M11.inv_mem h.2) hg) h.2⟩ :
        NativeSporadic.M11) = 1 := by
    refine m11_fix_base _ fun i hi => ?_
    have h1 : h.1 i = p ⟨i.val, hi⟩ := hhp ⟨i.val, hi⟩
    change (h.1⁻¹ * g * h.1) i = i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hp, ← h1]
    simp
  have hk1 : h.1⁻¹ * g * h.1 = 1 := congrArg Subtype.val hk
  calc g = h.1 * (h.1⁻¹ * g * h.1) * h.1⁻¹ := by group
    _ = 1 := by rw [hk1]; group

theorem pow_three_or_five {g : Equiv.Perm (Fin 11)} (ho : orderOf g = 15) (x : Fin 11) :
    (g ^ 3) x = x ∨ (g ^ 5) x = x := by
  have h15 : Function.IsPeriodicPt g 15 x := by
    change (g ^ 15) x = x
    rw [← ho, pow_orderOf_eq_one]
    rfl
  have hle : Function.minimalPeriod g x ≤ 11 := by
    simpa using Function.minimalPeriod_le_card (f := ⇑g) (x := x)
  have key : ∀ m ≤ 11, m ∣ 15 → m ∣ 3 ∨ m ∣ 5 := by decide
  rcases key _ hle h15.minimalPeriod_dvd with h | h
  · exact Or.inl (Function.isPeriodicPt_iff_minimalPeriod_dvd.2 h)
  · exact Or.inr (Function.isPeriodicPt_iff_minimalPeriod_dvd.2 h)

theorem orderOf_ne_fifteen {g : Equiv.Perm (Fin 11)} (hg : g ∈ NativeSporadic.M11) :
    orderOf g ≠ 15 := by
  intro ho
  have hfix : ∀ k, (k = 3 ∨ k = 5) →
      (Finset.univ.filter fun x => (g ^ k) x = x).card < 4 := by
    intro k hk
    by_contra hc
    obtain ⟨S, hS, hS4⟩ := Finset.exists_subset_card_eq (not_lt.1 hc)
    have h1 := m11_fix_four (g ^ k) (pow_mem hg k) (S.orderEmbOfFin hS4).toEmbedding
      fun i => (Finset.mem_filter.1 (hS (S.orderEmbOfFin_mem hS4 i))).2
    have hd : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at hd
    rcases hk with rfl | rfl <;> norm_num at hd
  have hcov : (Finset.univ : Finset (Fin 11)) ⊆ (Finset.univ.filter fun x => (g ^ 3) x = x) ∪
      (Finset.univ.filter fun x => (g ^ 5) x = x) := by
    intro x _
    rcases pow_three_or_five ho x with h | h <;> simp [h]
  have hc := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have h3 := hfix 3 (Or.inl rfl)
  have h5 := hfix 5 (Or.inr rfl)
  omega

theorem m11_no_fifteen : (orderTables m11Certificate 15).length = 0 := by
  have h := card_orderOf_eq (by norm_num) m11Certificate m11Certificate_check.1 (m := 15)
    (by norm_num)
  rw [m11Certificate_originalSubgroup] at h
  rw [← h, Nat.card_eq_zero]
  exact Or.inl ⟨fun x => orderOf_ne_fifteen x.1.2 (by rw [Subgroup.orderOf_coe]; exact x.2)⟩

end CertificateChecks.Batch148006

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Ronan148R in
theorem certificate148006 : mathieuNoFifteenCheck () = true := by
  simp only [mathieuNoFifteenCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨CertificateChecks.Batch148006.m11_no_fifteen, Certificates.certificate15068⟩

end Certificates
