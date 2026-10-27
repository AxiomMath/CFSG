module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixD
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Cex156 (M V₀ V U S A X T : Subgroup G) : Prop where
  std : Std15 G
  cex : Cex15 M V₀ V U S
  CH : V₀ ≤ pCoreOf 2 (centralizer (U : Set G))
  min : IsMinPair156 M V₀ (centralizer (U : Set G)) S A X
  sylow : IsSylowIn 2 T X
  A_le_T : A ≤ T

namespace Cex156

variable {M V₀ V U S A X T : Subgroup G}

theorem A_le_X (h : Cex156 M V₀ V U S A X T) : A ≤ X := h.min.pair.A_le

theorem X_le_H (h : Cex156 M V₀ V U S A X T) : X ≤ centralizer (U : Set G) := h.min.pair.le_H

theorem T_le_X (h : Cex156 M V₀ V U S A X T) : T ≤ X := h.sylow.le

theorem A_le_M (h : Cex156 M V₀ V U S A X T) : A ≤ M := h.min.pair.A_le_M

theorem A_le_S (h : Cex156 M V₀ V U S A X T) : A ≤ S := h.min.A_le_S

theorem T_le_M (h : Cex156 M V₀ V U S A X T) : T ≤ M :=
  h.min.toPairAt.le_M_of_isSylowIn h.sylow h.A_le_T

theorem isPGroup_T (h : Cex156 M V₀ V U S A X T) : IsPGroup 2 T := h.sylow.isPGroup

theorem conj_A (h : Cex156 M V₀ V U S A X T) : ∃ g : G, A = conjSubgroup V₀ g := h.min.pair.conj

theorem isElemAbelian_A (h : Cex156 M V₀ V U S A X T) : IsElemAbelian 2 A := by
  obtain ⟨g, rfl⟩ := h.conj_A
  exact isElemAbelian_conjSubgroup' h.cex.hyp.elemAbelian₀ g

theorem A_ne_bot (h : Cex156 M V₀ V U S A X T) : A ≠ ⊥ := by
  obtain ⟨g, rfl⟩ := h.conj_A
  intro hbot
  exact h.cex.hyp.ne_bot (conjSubgroup_eq_bot_iff.1 hbot)

theorem isTI_A (h : Cex156 M V₀ V U S A X T) : CFSG.CGT.Timmesfeld75.IsTI A := by
  obtain ⟨g, rfl⟩ := h.conj_A
  exact isTI_conj h.cex.hyp.isTI g

theorem inf_centralizer_ne_bot (h : Cex156 M V₀ V U S A X T) :
    V₀ ⊓ centralizer (T : Set G) ≠ ⊥ :=
  CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
    h.isPGroup_T h.cex.hyp.elemAbelian₀.isPGroup h.cex.hyp.ne_bot
    (h.T_le_M.trans h.cex.hyp.normalizer₀.symm.le)

theorem isElemAbelian_eSub (h : Cex156 M V₀ V U S A X T) :
    IsElemAbelian 2 (eSub V₀ X T) :=
  CFSG.Open.IsElemAbelian.mono (h.cex.conjClosure_isElemAbelian h.std h.CH)
    (conjClosure_mono inf_le_left h.X_le_H)

theorem X_le_normalizer_eSub (h : Cex156 M V₀ V U S A X T) :
    X ≤ normalizer (eSub V₀ X T : Set G) :=
  le_normalizer_conjClosure _ _

theorem inf_centralizer_le_ker (h : Cex156 M V₀ V U S A X T) :
    X ⊓ centralizer (eSub V₀ X T : Set G) ≤ kerMOf M X := by
  have hXn : X ≤ normalizer (eSub V₀ X T : Set G) := h.X_le_normalizer_eSub
  have hNn : ((X ⊓ centralizer (eSub V₀ X T : Set G)).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n x hn hx
    refine ⟨X.mul_mem (X.mul_mem hx hn.1) (X.inv_mem hx),
      Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have he' : x⁻¹ * e * x ∈ eSub V₀ X T := by
      have := (Subgroup.mem_normalizer_iff.1 (hXn (X.inv_mem hx)) e).1 he
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hn.2 _ he'
    calc e * (x * n * x⁻¹) = x * ((x⁻¹ * e * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * e * x)) * x⁻¹ := by rw [hc]
      _ = x * n * x⁻¹ * e := by group
  refine le_kerMOf_of_normal inf_le_left hNn ?_
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.inf_centralizer_ne_bot
  have hzE : (z : G) ∈ eSub V₀ X T := le_conjClosure _ _ z.2
  have hz1 : (z : G) ≠ 1 := fun e => hz (Subtype.ext e)
  intro n hn
  exact h.cex.hyp.centralizer_le z.2.1 hz1
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzE) hn.2)

theorem centralizer_eSub_le_normalizer_conj (h : Cex156 M V₀ V U S A X T) {x : G} (hx : x ∈ X) :
    centralizer (eSub V₀ X T : Set G) ≤ normalizer (conjSubgroup V₀ x : Set G) := by
  intro u hu
  obtain ⟨c, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.inf_centralizer_ne_bot
  have hcV : (c : G) ∈ V₀ := c.2.1
  have hc1 : (c : G) ≠ 1 := fun hh' => hc1' (Subtype.ext hh')
  have hzmem : x⁻¹ * (c : G) * x ∈ conjSubgroup (V₀ ⊓ centralizer (T : Set G)) x := by
    rw [mem_conjSubgroup_iff]
    have hce : x * (x⁻¹ * (c : G) * x) * x⁻¹ = (c : G) := by group
    rw [hce]
    exact c.2
  have hzE : x⁻¹ * (c : G) * x ∈ eSub V₀ X T := by
    rw [eSub]
    exact conjSubgroup_le_conjClosure _ _ hx hzmem
  have hzV : x⁻¹ * (c : G) * x ∈ conjSubgroup V₀ x := by
    rw [mem_conjSubgroup_iff]
    have hce : x * (x⁻¹ * (c : G) * x) * x⁻¹ = (c : G) := by group
    rw [hce]
    exact hcV
  have hz1 : x⁻¹ * (c : G) * x ≠ 1 := by
    intro hz
    apply hc1
    have h' := congrArg (fun t => x * t * x⁻¹) hz
    simpa [mul_assoc] using h'
  have huz : x⁻¹ * (c : G) * x * u = u * (x⁻¹ * (c : G) * x) :=
    Subgroup.mem_centralizer_iff.mp hu _ hzE
  exact centralizer_le_normalizer_conj h.cex.hyp.isTI x hzV hz1
    (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact huz)

theorem commute_conj_of_ne_bot (h : Cex156 M V₀ V U S A X T)
    (hne : A ⊓ centralizer (eSub V₀ X T : Set G) ≠ ⊥) :
    ∀ x ∈ X, ∀ a ∈ A, ∀ v ∈ conjSubgroup V₀ x, a * v = v * a := by
  intro x hx a ha v hv
  have hH := h.cex.hyp
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have huN : (u : G) ∈ normalizer (conjSubgroup V₀ x : Set G) :=
    h.centralizer_eSub_le_normalizer_conj hx u.2.2
  have hN : A ⊓ normalizer (conjSubgroup V₀ x : Set G) ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨(u : G), u.2.1, huN⟩, fun hh => hu1 (Subtype.ext (by
        have h1 : (u : G) = 1 := congrArg Subtype.val hh
        exact h1))⟩
  have hP : IsPGroup 2 ↥(A ⊔ conjSubgroup V₀ x) := by
    refine h.cex.isSylowIn_centralizer.isPGroup.to_le (sup_le h.A_le_S ?_)
    exact (conjSubgroup_le_pCoreOf_of_isCalH0 ⟨h.cex.isCalH h.std, h.CH⟩ (h.X_le_H hx)).trans
      (pCoreOf_le_of_isSylowIn h.cex.isSylowIn_centralizer)
  exact commute_of_isPGroup_sup hH.elemAbelian₀ hH.isTI h.conj_A ⟨x, rfl⟩ hN hP a ha v hv

theorem inf_centralizer_eq_bot (h : Cex156 M V₀ V U S A X T) :
    A ⊓ centralizer (eSub V₀ X T : Set G) = ⊥ := by
  by_contra hne
  have hcomm := h.commute_conj_of_ne_bot hne
  have hEA : eSub V₀ X T ≤ centralizer (A : Set G) := by
    refine conjClosure_le fun x hx z hz => ?_
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    refine hcomm x⁻¹ (X.inv_mem hx) a ha (x * z * x⁻¹) (mem_conjSubgroup_iff.2 ?_)
    simpa [mul_assoc] using hz.1
  have hAE : A ≤ centralizer (eSub V₀ X T : Set G) := Subgroup.le_centralizer_iff.2 hEA
  exact h.min.pair.not_le_ker ((le_inf h.A_le_X hAE).trans h.inf_centralizer_le_ker)

theorem quad (h : Cex156 M V₀ V U S A X T) :
    ∀ a ∈ A, ∀ b ∈ A, ∀ e ∈ eSub V₀ X T, a * ⁅b, e⁆ * a⁻¹ = ⁅b, e⁆ := by
  intro a ha b hb e he
  by_cases hb1 : b = 1
  · subst hb1
    simp
  have hEel := h.isElemAbelian_eSub
  have hb2 : b * b = 1 := by simpa [pow_two] using h.isElemAbelian_A.2 b hb
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hfE : b * e * b⁻¹ ∈ eSub V₀ X T :=
    (Subgroup.mem_normalizer_iff.1 (h.X_le_normalizer_eSub (h.A_le_X hb)) e).1 he
  have hcE : ⁅b, e⁆ ∈ eSub V₀ X T := by
    rw [commutatorElement_def]
    exact (eSub V₀ X T).mul_mem hfE ((eSub V₀ X T).inv_mem he)
  have hc2 : ⁅b, e⁆ * ⁅b, e⁆ = 1 := by simpa [pow_two] using hEel.2 _ hcE
  have hbc : b * ⁅b, e⁆ * b⁻¹ = ⁅b, e⁆ := by
    have e1 : b * ⁅b, e⁆ * b⁻¹ = ⁅b, e⁆⁻¹ := by
      rw [commutatorElement_def]
      have : b * (b * e * b⁻¹ * e⁻¹) * b⁻¹ = (b * b) * e * b⁻¹ * e⁻¹ * b⁻¹ := by group
      rw [this, hb2, one_mul]
      simp [mul_assoc, hbb]
    rw [e1]
    exact inv_eq_of_mul_eq_one_right hc2
  have hcomm : b * ⁅b, e⁆ = ⁅b, e⁆ * b := mul_inv_eq_iff_eq_mul.1 hbc
  have hEA : eSub V₀ X T ⊓ A = ⊥ := by
    rw [eq_bot_iff, ← h.inf_centralizer_eq_bot]
    intro x hx
    exact ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun y hy => B2F.isElemAbelian_comm hEel hy hx.1⟩
  have hcC : ⁅b, e⁆ ∈ eSub V₀ X T ⊓ centralizer ({b} : Set G) :=
    ⟨hcE, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm⟩
  rw [← eight_one h.isTI_A le_rfl (h.A_le_X.trans h.X_le_normalizer_eSub) hEA hb hb1] at hcC
  exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hcC.2 a ha)

theorem le_centralizer_of_normal (h : Cex156 M V₀ V U S A X T) {N : Subgroup G} (hNT : N ≤ T)
    (hN : (N.subgroupOf X).Normal) : N ≤ centralizer (eSub V₀ X T : Set G) := by
  have hNX : N ≤ X := hNT.trans h.T_le_X
  have hle : eSub V₀ X T ≤ centralizer (N : Set G) := by
    refine conjClosure_le fun x hx z hz => ?_
    refine Subgroup.mem_centralizer_iff.2 fun n hn => ?_
    have hn' : x⁻¹ * n * x ∈ N := by
      have := (Subgroup.normal_subgroupOf_iff hNX).1 hN n x⁻¹ hn (X.inv_mem hx)
      simpa using this
    have hc : (x⁻¹ * n * x) * z = z * (x⁻¹ * n * x) :=
      Subgroup.mem_centralizer_iff.1 hz.2 _ (hNT hn')
    calc n * (x * z * x⁻¹) = x * ((x⁻¹ * n * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * n * x)) * x⁻¹ := by rw [hc]
      _ = x * z * x⁻¹ * n := by group
  exact Subgroup.le_centralizer_iff.2 hle

theorem commute_A_V₀ (h : Cex156 M V₀ V U S A X T) :
    ∀ a ∈ A, ∀ v ∈ V₀, a * v = v * a := by
  have hP : IsPGroup 2 ↥(A ⊔ V₀) :=
    h.cex.isSylowIn_centralizer.isPGroup.to_le (sup_le h.A_le_S h.cex.V₀_le_S)
  have hN : A ⊓ normalizer (V₀ : Set G) ≠ ⊥ := by
    rw [h.cex.hyp.normalizer₀, inf_eq_left.2 h.A_le_M]
    exact h.A_ne_bot
  exact commute_of_isPGroup_sup h.cex.hyp.elemAbelian₀ h.cex.hyp.isTI h.conj_A
    ⟨1, (conjSubgroup_one V₀).symm⟩ hN hP

theorem inf_ker_eq_bot (h : Cex156 M V₀ V U S A X T) : A ⊓ kerMOf M X = ⊥ := by
  have hC := h.le_centralizer_of_normal (inf_le_left : T ⊓ kerMOf M X ≤ T)
    (h.min.normal_inf_ker h.sylow h.A_le_T)
  rw [eq_bot_iff, ← h.inf_centralizer_eq_bot]
  intro a ha
  exact ⟨ha.1, hC ⟨h.A_le_T ha.1, ha.2⟩⟩

end Cex156

end CFSG.LocalAnalysis.WeakClosure81
