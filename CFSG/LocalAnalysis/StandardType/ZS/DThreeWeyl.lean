module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.MarkedWeyl
import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem coxeterConfig_lift_data {ι : Type} {M : CoxeterMatrix ι}
    {d : ι → ↥A ⧸ Subgroup.center ↥A} (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A)
    (h : CoxeterConfig (reflImage p A) M d)
    (htop : Subgroup.closure (Set.range d) = ⊤) :
    ∃ s : ι → ↥A,
      (∀ i, IsRefl p ((s i : ↥A) : U ≃ₗ[ZMod p] U)) ∧
      (∀ i, (QuotientGroup.mk (s i) : ↥A ⧸ Subgroup.center ↥A) = d i) ∧
      Function.Injective s ∧
      (∀ i, s i * s i = 1) ∧
      (∀ i j, orderOf (s i * s j) = orderOf (d i * d j)) ∧
      (∀ i j, i ≠ j → M i j = 2 → Commute (s i) (s j)) ∧
      Subgroup.closure (Set.range s) = ⊤ := by
  classical
  choose s hs using fun i =>
    exists_unique_refl_of_mem_reflImage (A := A) hirr hn (h.1 i)
  have hS : ∀ i, IsRefl p ((s i : ↥A) : U ≃ₗ[ZMod p] U) := fun i => by
    simpa using ((hs i).1).1
  have hd : ∀ i, (QuotientGroup.mk (s i) : ↥A ⧸ Subgroup.center ↥A) = d i := fun i => by
    simpa using ((hs i).1).2
  have hinv : ∀ i, s i * s i = 1 := by
    intro i
    apply Subtype.ext
    simpa using (hS i).1
  have hinj : Function.Injective s := by
    intro i j hij
    apply h.2.1
    rw [← hd i, ← hd j, hij]
  have hord : ∀ i j, orderOf (s i * s j) = orderOf (d i * d j) := by
    intro i j
    rw [← hd i, ← hd j]
    exact (hirr.orderOf_mk_mul_mk hn (hS i) (hS j)).symm
  have hcomm : ∀ i j, i ≠ j → M i j = 2 → Commute (s i) (s j) := by
    intro i j hij hMij
    refine (AbsIrred.commute_mk_iff (A := A) hirr hn (s := s i) (t := s j) (hS j)).mp ?_
    rw [hd i, hd j]
    exact h.2.2.2 i j hij hMij
  have hclos : Subgroup.closure (Set.range s) = ⊤ := by
    refine closure_eq_top_of_closure_mk_eq_top hgen hirr hn hone (S := Set.range s)
      (fun x hx => ?_) ?_
    · obtain ⟨i, rfl⟩ := hx
      exact hS i
    · rw [← htop]
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, hx⟩
        exact ⟨i, by rw [← hx, hd i]⟩
      · rintro ⟨i, hx⟩
        exact ⟨s i, ⟨i, rfl⟩, by rw [hd i, hx]⟩
  exact ⟨s, hS, hd, hinj, hinv, hord, hcomm, hclos⟩

private theorem injective_of_map_swap_ne {G : Type*} [Group G] {l : ℕ}
    (hl : l + 1 = 3 ∨ 5 ≤ l + 1) (ψ : Equiv.Perm (Fin (l + 1)) →* G) {i j : Fin l}
    (hne : ψ (Equiv.swap i.castSucc i.succ) ≠ ψ (Equiv.swap j.castSucc j.succ)) :
    Function.Injective ψ := by
  classical
  have halt : ψ.ker ≠ ⊥ → alternatingGroup (Fin (l + 1)) ≤ ψ.ker := by
    intro hKne
    rcases hl with hl3 | hl5
    · have hl2 : l = 2 := by omega
      subst l
      exact CFSG.Quasithin.F53.normal_ge_alt3 ψ.ker hKne
    · exact Equiv.Perm.alternatingGroup_le_of_normal (α := Fin (l + 1))
        (by simpa using hl5) ((Subgroup.nontrivial_iff_ne_bot ψ.ker).mpr hKne)
  have hmem : Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ ∈
      alternatingGroup (Fin (l + 1)) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne,
      Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := j)).ne]
    norm_num
  refine (MonoidHom.ker_eq_bot_iff ψ).mp (by_contra fun hKne => hne ?_)
  have h1 := MonoidHom.mem_ker.mp (halt hKne hmem)
  rw [map_mul] at h1
  rw [eq_inv_of_mul_eq_one_left h1, ← map_inv, Equiv.swap_inv]

omit [Module.Finite (ZMod p) U] in
private theorem coxeterConfig_lift_injective_A {l : ℕ} (hl : l + 1 = 3 ∨ 5 ≤ l + 1)
    (s : Fin l → ↥A) (hinj : Function.Injective s)
    (hrel : (CoxeterMatrix.A l).IsLiftable s) :
    Function.Injective ((CoxeterMatrix.A l).toCoxeterSystem.lift ⟨s, hrel⟩) := by
  obtain ⟨e, he⟩ := ggCoxeterA_mulEquivPerm l
  let F : (CoxeterMatrix.A l).Group →* ↥A :=
    (CoxeterMatrix.A l).toCoxeterSystem.lift ⟨s, hrel⟩
  let ψ : Equiv.Perm (Fin (l + 1)) →* ↥A := F.comp e.symm.toMonoidHom
  have hψ : ∀ i : Fin l, ψ (Equiv.swap i.castSucc i.succ) = s i := by
    intro i
    change F (e.symm (Equiv.swap i.castSucc i.succ)) = s i
    rw [← he i, MulEquiv.symm_apply_apply, ← CoxeterMatrix.toCoxeterSystem_simple]
    exact (CoxeterMatrix.A l).toCoxeterSystem.lift_apply_simple hrel i
  have h0 : 0 < l := by omega
  have h1 : 1 < l := by omega
  have hψinj : Function.Injective ψ :=
    injective_of_map_swap_ne hl ψ (i := ⟨0, h0⟩) (j := ⟨1, h1⟩) (by
      rw [hψ, hψ]
      exact fun h => absurd (congrArg Fin.val (hinj h)) (by simp))
  have hFeq : F = ψ.comp e.toMonoidHom := MonoidHom.ext fun x => by
    change F x = F (e.symm (e x))
    rw [MulEquiv.symm_apply_apply]
  change Function.Injective F
  rw [hFeq]
  exact hψinj.comp e.injective

theorem linWeyl_of_coxeterConfig_A (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A) {l : ℕ}
    (hl : l + 1 = 3 ∨ 5 ≤ l + 1) {d : Fin l → ↥A ⧸ Subgroup.center ↥A}
    (h : CoxeterConfig (reflImage p A) (CoxeterMatrix.A l) d)
    (htop : Subgroup.closure (Set.range d) = ⊤) : LinWeyl p A := by
  classical
  obtain ⟨s, hS, hd, hinj, hinv, hord, hcomm, hclos⟩ :=
    coxeterConfig_lift_data hgen hirr hn hone h htop
  have hW : GGIsWeylMatrix (CoxeterMatrix.A l) := by
    refine Or.inl ⟨l, Equiv.refl _, by omega, Or.inl ?_⟩
    exact (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm
  have hrel : (CoxeterMatrix.A l).IsLiftable s := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [show (CoxeterMatrix.A l) i i = 1 by simp [CoxeterMatrix.A], pow_one]
      exact hinv i
    · have hcase : (CoxeterMatrix.A l) i j = 3 ∨ (CoxeterMatrix.A l) i j = 2 := by
        simp only [CoxeterMatrix.A, Matrix.of_apply]
        split_ifs <;> omega
      rcases hcase with h3 | h2
      · rw [h3]
        have h3' : orderOf (s i * s j) = 3 := by
          rw [hord i j, h.2.2.1 i j h3]
        rw [← h3']
        exact pow_orderOf_eq_one _
      · rw [h2, (hcomm i j hij h2).mul_pow, pow_two (s i), pow_two (s j),
          hinv i, hinv j, mul_one]
  exact linWeyl_of_lift_injective hW s hS hrel hclos
    (coxeterConfig_lift_injective_A hl s hinj hrel)

theorem linWeyl_of_coxeterConfig_E (hp : p ≠ 2) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
      (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e))
    {d : ι → ↥A ⧸ Subgroup.center ↥A} (h : CoxeterConfig (reflImage p A) M d)
    (htop : Subgroup.closure (Set.range d) = ⊤) : LinWeyl p A := by
  classical
  obtain ⟨s, hS, hd, hinj, hinv, hord, hcomm, hclos⟩ :=
    coxeterConfig_lift_data hgen hirr hn hone h htop
  choose a φ hφ heq using fun i =>
    (isRefl_iff hp ((s i : ↥A) : U ≃ₗ[ZMod p] U)).mp (hS i)
  have hs : ∀ i v, ((s i : ↥A) : U ≃ₗ[ZMod p] U) v = v - φ i v • a i := by
    intro i v
    rw [heq i, Module.reflection_apply]
  have hedge : ∀ i j, M i j = 3 → φ i (a j) * φ j (a i) = 1 := by
    intro i j hMij
    have hordA : orderOf (s i * s j) = 3 := by
      rw [hord i j, h.2.2.1 i j hMij]
    have hordL : orderOf (((s i : ↥A) : U ≃ₗ[ZMod p] U) *
        ((s j : ↥A) : U ≃ₗ[ZMod p] U)) = 3 := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
      exact hordA
    rw [heq i, heq j] at hordL
    exact mul_eq_one_of_orderOf_eq_three hp (hφ i) (hφ j) hordL
  have hzero : ∀ i j, i ≠ j → M i j = 2 → φ i (a j) = 0 := by
    intro i j hij hMij
    have hcommL : Commute (((s i : ↥A) : U ≃ₗ[ZMod p] U))
        (((s j : ↥A) : U ≃ₗ[ZMod p] U)) :=
      (hcomm i j hij hMij).map A.subtype
    rw [heq i, heq j] at hcommL
    have hne : Module.reflection (hφ i) ≠ Module.reflection (hφ j) := by
      intro hEq
      have hsame : s i = s j := by
        apply Subtype.ext
        rw [heq i, heq j, hEq]
      exact hij (hinj hsame)
    exact apply_eq_zero_of_commute hp (hφ i) (hφ j) hcommL hne
  exact linWeyl_of_rootData_E hp hM a φ hφ hedge hzero s hs hclos

theorem linWeyl_of_coxeterConfig_E₆ (hp : p ≠ 2) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A)
    {d : Fin 6 → ↥A ⧸ Subgroup.center ↥A} (h : CoxeterConfig (reflImage p A) CoxeterMatrix.E₆ d)
    (htop : Subgroup.closure (Set.range d) = ⊤) : LinWeyl p A := by
  exact linWeyl_of_coxeterConfig_E (ι := Fin 6) (M := CoxeterMatrix.E₆) hp hgen hirr hn hone
    (Or.inl ⟨Equiv.refl _, (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm⟩) h htop

end CFSG.StandardType.ZS
