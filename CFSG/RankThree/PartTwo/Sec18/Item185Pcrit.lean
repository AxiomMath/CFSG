module

import CFSG.RankThree.PartTwo.Sec4.Census.Item44Linear
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.RankThree.PartOne.K1327.Trick
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndRep

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.RankThree.PartTwo.Sec4.Census
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section LinearAlgebra

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private theorem finrank_eigenspace_conj (f g h : Module.End K V) (hgh : g * h = 1)
    (hhg : h * g = 1) :
    Module.finrank K (Module.End.eigenspace (g * f * h) 1) =
      Module.finrank K (Module.End.eigenspace f 1) := by
  have e1 : ∀ x, h (g x) = x := fun x => by
    have := LinearMap.congr_fun hhg x
    simpa using this
  have e2 : ∀ x, g (h x) = x := fun x => by
    have := LinearMap.congr_fun hgh x
    simpa using this
  have hinj : Function.Injective g := fun x y hxy => by
    have := congrArg h hxy
    simpa only [e1] using this
  have hmap : Module.End.eigenspace (g * f * h) 1 = (Module.End.eigenspace f 1).map g := by
    ext v
    simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, one_smul,
      Module.End.mul_apply]
    constructor
    · intro hv
      refine ⟨h v, ?_, e2 v⟩
      calc f (h v) = h (g (f (h v))) := (e1 _).symm
        _ = h v := by rw [hv]
    · rintro ⟨x, hx, rfl⟩
      rw [e1 x, hx]
  rw [hmap]
  exact ((Submodule.equivMapOfInjective g hinj _).finrank_eq).symm

private theorem exists_smul_of_finrank_one [FiniteDimensional K V] {L : Submodule K V}
    (hL : Module.finrank K L = 1) {g : Module.End K V} (hg : ∀ v ∈ L, g v ∈ L) :
    ∃ a : K, ∀ v ∈ L, g v = a • v := by
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (by omega : 0 < Module.finrank K L)
  have hspan : ∀ w : L, ∃ c : K, c • u = w := (finrank_eq_one_iff_of_nonzero' u hu).mp hL
  have hgu : g (u : V) ∈ L := hg _ u.2
  obtain ⟨a, ha⟩ := hspan ⟨g (u : V), hgu⟩
  refine ⟨a, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := hspan ⟨v, hv⟩
  have hv' : v = c • (u : V) := (congrArg Subtype.val hc).symm
  have hgu' : g (u : V) = a • (u : V) := (congrArg Subtype.val ha).symm
  rw [hv', map_smul, hgu', smul_comm]

private theorem exists_smul_of_three_lines [FiniteDimensional K V] (hV : Module.finrank K V = 2)
    {L₁ L₂ L₃ : Submodule K V} (h₁ : Module.finrank K L₁ = 1) (h₂ : Module.finrank K L₂ = 1)
    (h₃ : Module.finrank K L₃ = 1) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    {g : Module.End K V} (g₁ : ∀ v ∈ L₁, g v ∈ L₁) (g₂ : ∀ v ∈ L₂, g v ∈ L₂)
    (g₃ : ∀ v ∈ L₃, g v ∈ L₃) : ∃ a : K, ∀ v : V, g v = a • v := by
  have hline : ∀ {L : Submodule K V} {u : V}, Module.finrank K L = 1 → u ∈ L → u ≠ 0 →
      Submodule.span K {u} = L := by
    intro L u hL hu hu0
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem u L).mpr hu
    · rw [finrank_span_singleton hu0, hL]
  obtain ⟨a₁, ha₁⟩ := exists_smul_of_finrank_one h₁ g₁
  obtain ⟨a₂, ha₂⟩ := exists_smul_of_finrank_one h₂ g₂
  obtain ⟨a₃, ha₃⟩ := exists_smul_of_finrank_one h₃ g₃
  have hinf : ∀ z : V, z ∈ L₁ → z ∈ L₂ → z = 0 := by
    intro z hz1 hz2
    by_contra hz0
    exact h12 ((hline h₁ hz1 hz0).symm.trans (hline h₂ hz2 hz0))
  have hsum : Module.finrank K ↥(L₁ ⊔ L₂) = 2 := by
    have hlt : L₁ < L₁ ⊔ L₂ := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      apply h12
      have hle : L₂ ≤ L₁ := by
        intro z hz
        rw [heq]
        exact Submodule.mem_sup_right hz
      exact (Submodule.eq_of_le_of_finrank_eq hle (h₂.trans h₁.symm)).symm
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (L₁ ⊔ L₂)
    omega
  have hsup : L₁ ⊔ L₂ = ⊤ := Submodule.eq_top_of_finrank_eq (hsum.trans hV.symm)
  have hdec : ∀ v : V, ∃ x ∈ L₁, ∃ y ∈ L₂, x + y = v := fun v => by
    have hv : v ∈ L₁ ⊔ L₂ := by
      rw [hsup]
      exact Submodule.mem_top
    exact Submodule.mem_sup.mp hv
  obtain ⟨u, hu3, hu0⟩ : ∃ u ∈ L₃, u ≠ 0 := by
    obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (by omega : 0 < Module.finrank K L₃)
    exact ⟨(w : V), w.2, fun h => hw (Subtype.ext h)⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hdec u
  have hx0 : x ≠ 0 := by
    intro h0
    have hyu : y = u := by
      rw [h0, zero_add] at hxy
      exact hxy
    have hu2 : u ∈ L₂ := by
      rw [← hyu]
      exact hy
    exact h23 ((hline h₃ hu3 hu0).symm.trans (hline h₂ hu2 hu0)).symm
  have hy0 : y ≠ 0 := by
    intro h0
    have hxu : x = u := by
      rw [h0, add_zero] at hxy
      exact hxy
    have hu1 : u ∈ L₁ := by
      rw [← hxu]
      exact hx
    exact h13 ((hline h₃ hu3 hu0).symm.trans (hline h₁ hu1 hu0)).symm
  have hA : (a₁ - a₃) • x + (a₂ - a₃) • y = 0 := by
    have h1 : g (x + y) = a₃ • (x + y) := by
      rw [hxy]
      exact ha₃ u hu3
    rw [map_add, ha₁ x hx, ha₂ y hy, smul_add] at h1
    rw [sub_smul, sub_smul,
      show a₁ • x - a₃ • x + (a₂ • y - a₃ • y) = (a₁ • x + a₂ • y) - (a₃ • x + a₃ • y) by abel,
      h1, sub_self]
  have hA' : (a₂ - a₃) • y + (a₁ - a₃) • x = 0 := by
    rw [add_comm]
    exact hA
  have hz1 : (a₁ - a₃) • x = 0 := by
    apply hinf
    · exact Submodule.smul_mem _ _ hx
    · rw [eq_neg_of_add_eq_zero_left hA]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)
  have hz2 : (a₂ - a₃) • y = 0 := by
    apply hinf
    · rw [eq_neg_of_add_eq_zero_left hA']
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hx)
    · exact Submodule.smul_mem _ _ hy
  have ha₁₃ : a₁ = a₃ := by
    rcases smul_eq_zero.mp hz1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx0
  have ha₂₃ : a₂ = a₃ := by
    rcases smul_eq_zero.mp hz2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hy0
  refine ⟨a₁, fun v => ?_⟩
  obtain ⟨x', hx', y', hy', rfl⟩ := hdec v
  rw [map_add, ha₁ x' hx', ha₂ y' hy', ha₂₃, ha₁₃, smul_add]

end LinearAlgebra

private theorem card_zpowers_eq_three {B : Type} [Group B] (hexp : ∀ b : B, b ^ 3 = 1) {b : B}
    (hb : b ≠ 1) : Nat.card (Subgroup.zpowers b) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (hexp b) hb]

private theorem zpowers_sup_eq_top {B : Type} [Group B] [Finite B] (hcard : Nat.card B = 9)
    (hexp : ∀ b : B, b ^ 3 = 1) {b c : B} (hb : b ≠ 1) (hc : c ∉ Subgroup.zpowers b) :
    Subgroup.zpowers b ⊔ Subgroup.zpowers c = ⊤ := by
  have hdvd : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) ∣ 9 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hge : 3 ≤ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) := by
    have := Subgroup.card_le_of_le
      (le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers c)
    rwa [card_zpowers_eq_three hexp hb] at this
  have hne : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) ≠ 3 := by
    intro h3
    apply hc
    have heq : Subgroup.zpowers b = Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge le_sup_left
        (le_of_eq (by rw [h3, card_zpowers_eq_three hexp hb]))
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have h9 : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = 9 := by
    have hle : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) ≤ 9 :=
      Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = n at hdvd hge hne hle ⊢
    interval_cases n <;> omega
  apply Subgroup.eq_top_of_card_eq
  exact h9.trans hcard.symm

private theorem exists_basis_of_card_nine {B : Type} [Group B] [Finite B] (hcard : Nat.card B = 9)
    (hexp : ∀ b : B, b ^ 3 = 1) :
    ∃ b₁ b₂ : B, b₁ ≠ 1 ∧ b₂ ∉ Subgroup.zpowers b₁ ∧ b₁ * b₂ ∉ Subgroup.zpowers b₁ ∧
      b₁ * b₂ ∉ Subgroup.zpowers b₂ := by
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : B, b₁ ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card B = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [h x, h y]⟩, ⟨1⟩⟩
    omega
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : B, b₂ ∉ Subgroup.zpowers b₁ := by
    by_contra h
    push Not at h
    have htop : Subgroup.zpowers b₁ = ⊤ := eq_top_iff.mpr fun x _ => h x
    have h3 := card_zpowers_eq_three hexp hb₁
    rw [htop, Subgroup.card_top, hcard] at h3
    omega
  have hb₂1 : b₂ ≠ 1 := fun h => hb₂ (by rw [h]; exact Subgroup.one_mem _)
  have hb₁₂ : b₁ ∉ Subgroup.zpowers b₂ := by
    intro h
    have hle : Subgroup.zpowers b₁ ≤ Subgroup.zpowers b₂ := Subgroup.zpowers_le.mpr h
    have heq : Subgroup.zpowers b₁ = Subgroup.zpowers b₂ :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (by rw [card_zpowers_eq_three hexp hb₁, card_zpowers_eq_three hexp hb₂1]))
    exact hb₂ (by rw [heq]; exact Subgroup.mem_zpowers b₂)
  refine ⟨b₁, b₂, hb₁, hb₂, fun h => hb₂ ?_, fun h => hb₁₂ ?_⟩
  · have : b₂ = b₁⁻¹ * (b₁ * b₂) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers b₁)) h
  · have : b₁ = (b₁ * b₂) * b₂⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers b₂))

private theorem la_core {K V B : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group B] [Finite B] (hV : Module.finrank K V ≤ 2)
    (hcard : Nat.card B = 9) (hexp : ∀ b : B, b ^ 3 = 1) (hcomm : ∀ b c : B, b * c = c * b)
    (ρ : B →* Module.End K V)
    (hfd : ∀ b c : B, b ≠ 1 → c ≠ 1 →
      Module.finrank K (Module.End.eigenspace (ρ b) 1) =
        Module.finrank K (Module.End.eigenspace (ρ c) 1))
    (hgen : ⨆ b : {b : B // b ≠ 1}, Module.End.eigenspace (ρ b.1) 1 = ⊤) :
    ∀ b : B, ρ b = 1 := by
  classical
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : B, b₀ ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card B = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [h x, h y]⟩, ⟨1⟩⟩
    omega
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Module.finrank K (Module.End.eigenspace (ρ b₀) 1) = f :=
    ⟨_, rfl⟩
  have hfb : ∀ b : B, b ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ b) 1) = f :=
    fun b hb => (hfd b b₀ hb hb₀).trans hf
  have hfle : f ≤ Module.finrank K V := by
    rw [← hf]
    exact Submodule.finrank_le _
  have hinv : ∀ b e : B, ∀ v ∈ Module.End.eigenspace (ρ b) 1,
      ρ e v ∈ Module.End.eigenspace (ρ b) 1 := by
    intro b e v hv
    rw [Module.End.mem_eigenspace_iff, one_smul] at hv ⊢
    rw [← Module.End.mul_apply, ← map_mul, hcomm b e, map_mul, Module.End.mul_apply, hv]
  have hfixpair : ∀ b c : B, b ≠ 1 → c ∉ Subgroup.zpowers b → ∀ e : B, ∀ v : V,
      ρ b v = v → ρ c v = v → ρ e v = v := by
    intro b c hb hc e v hbv hcv
    let St : Subgroup B :=
      { carrier := {x | ρ x v = v}
        mul_mem' := fun {x y} hx hy => by
          change ρ x v = v at hx
          change ρ y v = v at hy
          show ρ (x * y) v = v
          rw [map_mul, Module.End.mul_apply, hy, hx]
        one_mem' := by
          show ρ 1 v = v
          rw [map_one, Module.End.one_apply]
        inv_mem' := fun {x} hx => by
          change ρ x v = v at hx
          show ρ x⁻¹ v = v
          calc ρ x⁻¹ v = ρ x⁻¹ (ρ x v) := by rw [hx]
            _ = v := by
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply] }
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ St :=
      sup_le (Subgroup.zpowers_le.mpr (show b ∈ St from hbv))
        (Subgroup.zpowers_le.mpr (show c ∈ St from hcv))
    rw [zpowers_sup_eq_top hcard hexp hb hc] at hle
    exact hle (Subgroup.mem_top e)
  by_cases hcase : f = Module.finrank K V
  · intro b
    by_cases hb : b = 1
    · rw [hb, map_one]
    · have htop : Module.End.eigenspace (ρ b) 1 = ⊤ :=
        Submodule.eq_top_of_finrank_eq ((hfb b hb).trans hcase)
      ext v
      have hv : v ∈ Module.End.eigenspace (ρ b) 1 := by
        rw [htop]
        exact Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff, one_smul] at hv
      rw [Module.End.one_apply]
      exact hv
  by_cases hzero : f = 0
  · intro b
    have hbot : ∀ b : B, b ≠ 1 → Module.End.eigenspace (ρ b) 1 = ⊥ := fun b hb =>
      Submodule.finrank_eq_zero.mp ((hfb b hb).trans hzero)
    have hV0 : (⨆ b : {b : B // b ≠ 1}, Module.End.eigenspace (ρ b.1) 1) = ⊥ :=
      iSup_eq_bot.mpr fun b => hbot b.1 b.2
    rw [hgen] at hV0
    have hvz : ∀ v : V, v = 0 := fun v => by
      have hv : v ∈ (⊤ : Submodule K V) := Submodule.mem_top
      rw [hV0, Submodule.mem_bot] at hv
      exact hv
    ext v
    rw [hvz (ρ b v), Module.End.one_apply, hvz v]
  exfalso
  have hf1 : f = 1 := by omega
  have hd2 : Module.finrank K V = 2 := by omega
  have hline : ∀ b c : B, b ≠ 1 → c ∉ Subgroup.zpowers b →
      Module.End.eigenspace (ρ b) 1 ≠ Module.End.eigenspace (ρ c) 1 := by
    intro b c hb hc heq
    have hLe : ∀ e : B, e ≠ 1 →
        Module.End.eigenspace (ρ b) 1 ≤ Module.End.eigenspace (ρ e) 1 := by
      intro e _ v hv
      have hbv : ρ b v = v := by
        rw [Module.End.mem_eigenspace_iff, one_smul] at hv
        exact hv
      have hcv : ρ c v = v := by
        have hvc : v ∈ Module.End.eigenspace (ρ c) 1 := by
          rw [← heq]
          exact hv
        rw [Module.End.mem_eigenspace_iff, one_smul] at hvc
        exact hvc
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact hfixpair b c hb hc e v hbv hcv
    have hEq : ∀ e : B, e ≠ 1 →
        Module.End.eigenspace (ρ e) 1 = Module.End.eigenspace (ρ b) 1 := fun e he =>
      (Submodule.eq_of_le_of_finrank_eq (hLe e he)
        ((hfb b hb).trans (hfb e he).symm)).symm
    have hle : (⨆ e : {e : B // e ≠ 1}, Module.End.eigenspace (ρ e.1) 1) ≤
        Module.End.eigenspace (ρ b) 1 :=
      iSup_le fun e => (hEq e.1 e.2).le
    rw [hgen] at hle
    have h1 : Module.finrank K (⊤ : Submodule K V) ≤
        Module.finrank K (Module.End.eigenspace (ρ b) 1) := Submodule.finrank_mono hle
    rw [finrank_top, hfb b hb] at h1
    omega
  obtain ⟨b₁, b₂, hb₁, hb₂, hb₃a, hb₃b⟩ := exists_basis_of_card_nine hcard hexp
  have hb₂1 : b₂ ≠ 1 := fun h => hb₂ (by rw [h]; exact Subgroup.one_mem _)
  have hb₃1 : b₁ * b₂ ≠ 1 := fun h => hb₃a (by rw [h]; exact Subgroup.one_mem _)
  have hfin1 : ∀ b : B, b ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ b) 1) = 1 :=
    fun b hb => (hfb b hb).trans hf1
  have hscal : ∀ e : B, ∃ a : K, ∀ v : V, ρ e v = a • v := fun e =>
    exists_smul_of_three_lines hd2 (hfin1 b₁ hb₁) (hfin1 b₂ hb₂1) (hfin1 (b₁ * b₂) hb₃1)
      (hline b₁ b₂ hb₁ hb₂) (hline b₁ (b₁ * b₂) hb₁ hb₃a) (hline b₂ (b₁ * b₂) hb₂1 hb₃b)
      (fun v hv => hinv b₁ e v hv) (fun v hv => hinv b₂ e v hv)
      (fun v hv => hinv (b₁ * b₂) e v hv)
  choose lam hlam using hscal
  have hlam3 : ∀ e : B, lam e ^ 3 = 1 := by
    intro e
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 :=
      Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank K V)
    have h1 : ρ (e ^ 3) v = v := by
      rw [hexp e, map_one, Module.End.one_apply]
    have h2 : ρ (e ^ 3) v = (lam e ^ 3) • v := by
      simp only [pow_three, map_mul, Module.End.mul_apply, hlam, smul_smul]
    have h4 : (lam e ^ 3 - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← h2, h1, sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  haveI : Fintype B := Fintype.ofFinite B
  have hBcard' : (Finset.univ : Finset B).card = 9 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hmaps : ∀ x ∈ (Finset.univ : Finset B),
      lam x ∈ (Polynomial.nthRoots 3 (1 : K)).toFinset := by
    intro x _
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (show 0 < 3 by norm_num)]
    exact hlam3 x
  have hTcard : (Polynomial.nthRoots 3 (1 : K)).toFinset.card ≤ 3 :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots 3 (1 : K))
  obtain ⟨e, -, e', -, hne, hee⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hBcard']; omega) hmaps
  have h1' : ρ e' = ρ e := LinearMap.ext fun v => by
    rw [hlam e' v, hlam e v, hee]
  have hgone : ρ (e⁻¹ * e') = 1 := by
    rw [map_mul, h1', ← map_mul, inv_mul_cancel, map_one]
  have hg1 : e⁻¹ * e' ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  have htopg : Module.End.eigenspace (ρ (e⁻¹ * e')) 1 = ⊤ := by
    rw [hgone, eq_top_iff]
    intro v _
    rw [Module.End.mem_eigenspace_iff, Module.End.one_apply, one_smul]
  have h := hfb (e⁻¹ * e') hg1
  rw [htopg, finrank_top, hd2, hf1] at h
  omega

private theorem mem_frattiniKer_of_frattiniLin_eq_one {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {D : Subgroup Y} (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    {y : Y} (hy : frattiniLin h y = 1) : y ∈ h.frattiniKer := by
  rw [CriticalAt.mem_frattiniKer_iff]
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have := congrArg (fun f : Module.End (ZMod p) (Additive (D ⧸ frattini D)) =>
      f (Additive.ofMul (x : D ⧸ frattini D))) hy
    simp only [frattiniLin_apply, Module.End.one_apply] at this
    rw [MulAut.one_apply, CriticalAt.frattiniAct, MonoidHom.comp_apply]
    exact (quotientAutomorphism_apply _ _ _).trans (Additive.ofMul.injective this)

private theorem mem_eigenspace_of_centralizer {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {D : Subgroup Y} (h : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    {g x : Y} (hxD : x ∈ D) (hgx : x * g = g * x) :
    Additive.ofMul (QuotientGroup.mk (⟨x, hxD⟩ : D) : D ⧸ frattini D) ∈
      Module.End.eigenspace (frattiniLin h g) 1 := by
  have hconj : h.conjD g ⟨x, hxD⟩ = ⟨x, hxD⟩ := by
    apply Subtype.ext
    rw [h.conjD_apply]
    show g * x * g⁻¹ = x
    rw [← hgx, mul_inv_cancel_right]
  rw [Module.End.mem_eigenspace_iff, one_smul, frattiniLin_apply, hconj]

private theorem iSup_fix_eq_top {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {D B : Subgroup Y} (hD : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    (hle : D ≤ ⨆ b : {x : ↥B // x ≠ 1}, D ⊓ Subgroup.centralizer ({(b.1 : Y)} : Set Y)) :
    (⨆ b : {b : ↥B // b ≠ 1}, Module.End.eigenspace ((frattiniLin hD).comp B.subtype b.1) 1) =
      ⊤ := by
  have key : ∀ x : Y,
      x ∈ (⨆ b : {x : ↥B // x ≠ 1}, D ⊓ Subgroup.centralizer ({(b.1 : Y)} : Set Y)) →
      ∃ hx : x ∈ D, Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : D) : D ⧸ frattini D) ∈
        (⨆ b : {b : ↥B // b ≠ 1}, Module.End.eigenspace ((frattiniLin hD).comp B.subtype b.1) 1) := by
    intro x hx
    refine Subgroup.iSup_induction _ (C := fun x : Y => ∃ hx : x ∈ D,
      Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : D) : D ⧸ frattini D) ∈
        (⨆ b : {b : ↥B // b ≠ 1}, Module.End.eigenspace ((frattiniLin hD).comp B.subtype b.1) 1))
      hx ?_ ?_ ?_
    · intro b x hxb
      exact ⟨hxb.1, Submodule.mem_iSup_of_mem b
        (mem_eigenspace_of_centralizer hD hxb.1 (Subgroup.mem_centralizer_singleton_iff.mp hxb.2))⟩
    · refine ⟨Subgroup.one_mem D, ?_⟩
      have e0 : (Additive.ofMul (QuotientGroup.mk (⟨1, Subgroup.one_mem D⟩ : D) :
          D ⧸ frattini D)) = 0 := rfl
      rw [e0]
      exact Submodule.zero_mem _
    · rintro x y ⟨hxD, hxW⟩ ⟨hyD, hyW⟩
      refine ⟨Subgroup.mul_mem D hxD hyD, ?_⟩
      have e : (Additive.ofMul (QuotientGroup.mk (⟨x * y, Subgroup.mul_mem D hxD hyD⟩ : D) :
          D ⧸ frattini D)) = Additive.ofMul (QuotientGroup.mk (⟨x, hxD⟩ : D) : D ⧸ frattini D) +
          Additive.ofMul (QuotientGroup.mk (⟨y, hyD⟩ : D) : D ⧸ frattini D) := rfl
      rw [e]
      exact add_mem hxW hyW
  rw [eq_top_iff]
  intro w _
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
  obtain ⟨hdD, hw⟩ := key d.1 (hle d.2)
  have e1 : Additive.ofMul (QuotientGroup.mk (⟨d.1, hdD⟩ : D) : D ⧸ frattini D) = w :=
    congrArg Additive.ofMul hd
  rw [← e1]
  exact hw

private theorem frattiniLin_eq_one_of_B {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {D B S : Subgroup Y} (hD : CriticalAt p D) [IsElementaryAbelian p (D ⧸ frattini D)]
    [Module.Finite (ZMod p) (Additive (D ⧸ frattini D))]
    (hV : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 2)
    (hcopD : ¬ 3 ∣ Nat.card D) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (htrans : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ B, y ≠ 1 → ∃ s ∈ S, s * x * s⁻¹ = y) :
    ∀ b ∈ B, frattiniLin hD b = 1 := by
  have hN : Subgroup.normalizer (D : Set Y) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hD.normal
  have hBV : B ≤ Subgroup.normalizer (D : Set Y) := fun b _ => by
    rw [hN]
    exact Subgroup.mem_top b
  have hBcard : Nat.card B = 3 ^ 2 := hB9.trans (by norm_num)
  have hle := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers Nat.prime_three hB hBcard hBV
    hcopD
  have hgen := iSup_fix_eq_top hD hle
  have hfd : ∀ b c : ↥B, b ≠ 1 → c ≠ 1 →
      Module.finrank (ZMod p) (Module.End.eigenspace ((frattiniLin hD).comp B.subtype b) 1) =
        Module.finrank (ZMod p) (Module.End.eigenspace ((frattiniLin hD).comp B.subtype c) 1) := by
    intro b c hb hc
    have hb' : (b : Y) ≠ 1 := fun h => hb (Subtype.ext h)
    have hc' : (c : Y) ≠ 1 := fun h => hc (Subtype.ext h)
    obtain ⟨s, -, hs⟩ := htrans (b : Y) b.2 hb' (c : Y) c.2 hc'
    have hgh : frattiniLin hD s * frattiniLin hD s⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hhg : frattiniLin hD s⁻¹ * frattiniLin hD s = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hcomp : frattiniLin hD (c : Y) =
        frattiniLin hD s * frattiniLin hD (b : Y) * frattiniLin hD s⁻¹ := by
      rw [← hs, map_mul, map_mul]
    have key := finrank_eigenspace_conj (frattiniLin hD (b : Y)) (frattiniLin hD s)
      (frattiniLin hD s⁻¹) hgh hhg
    rw [← hcomp] at key
    exact key.symm
  have hcomm : ∀ b c : ↥B, b * c = c * b := fun b c => hB.1.is_comm.comm b c
  have hexp : ∀ b : ↥B, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hB.2 b.1 b.2)
  have hla := la_core (K := ZMod p) (V := Additive (D ⧸ frattini D)) (B := ↥B) hV hB9 hexp
    hcomm ((frattiniLin hD).comp B.subtype) hfd hgen
  intro b hb
  exact hla ⟨b, hb⟩

theorem centralizes_pCore {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hrank : ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    {B S : Subgroup Y} (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hSB : S ≤ Subgroup.normalizer (B : Set Y))
    (htrans : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ B, y ≠ 1 → ∃ s ∈ S, s * x * s⁻¹ = y) :
    ∀ b ∈ B, ∀ y ∈ CFSG.pCore p Y, b * y = y * b := by
  have hp1 : 1 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hcop3 : Nat.Coprime 3 p :=
    (Nat.coprime_primes Nat.prime_three (Fact.out : Nat.Prime p)).mpr (by omega)
  by_cases hP : CFSG.pCore p Y = ⊥
  · intro b _ y hy
    rw [hP, Subgroup.mem_bot] at hy
    rw [hy, mul_one, one_mul]
  obtain ⟨D, hD⟩ := exists_criticalAt (q := p) hp2 hP
  have hDp : IsPGroup p D := pCore_isPGroup.to_le hD.le
  have hexpD : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by simpa using hD.exp (x : Y) x.2)
  haveI hVel : IsElementaryAbelian p (D ⧸ frattini D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hDp).2.2.2.1
  haveI hVfin : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hpRankD : CFSG.pRank p D ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top p hp1 D]
    exact CFSG.SectionRank.pRank_le hp1 fun E _ hE => hrank E hE
  have hF2 : CFSG.pRank p (D ⧸ frattini D) ≤ 2 := by
    have key : ∀ (N : Subgroup ↥D) [N.Normal], N = commutator ↥D →
        CFSG.pRank p (↥D ⧸ N) ≤ 2 := by
      intro N _ hNc
      subst hNc
      exact (class_two_small_rank_order_bounds hDp hexpD hD.commutator_le_center).1 hpRankD
    exact key (frattini ↥D) (frattini_eq_commutator hDp hexpD)
  have hfinrank : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 2 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (D ⧸ frattini D))
    rw [Nat.card_zmod] at hpow
    rw [← pRank_eq_of_card_eq_pow hp1 (A := D ⧸ frattini D) hpow]
    exact hF2
  have hcopD : ¬ 3 ∣ Nat.card D := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 h3
    have h1 : orderOf t ∣ p := orderOf_dvd_of_pow_eq_one (hexpD t)
    rw [ht] at h1
    rcases Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p) 3 h1 with h | h <;> omega
  have hBk := frattiniLin_eq_one_of_B hD hfinrank hcopD hB hB9 htrans
  intro b hb y hy
  have hbK : b ∈ hD.frattiniKer := mem_frattiniKer_of_frattiniLin_eq_one hD (hBk b hb)
  have hcop : Nat.Coprime (orderOf b) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hB.2 b hb)) hcop3
  exact mul_inv_eq_iff_eq_mul.mp (hD.centralizes_of_mem_frattiniKer hbK hcop y hy)

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
