module

public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Set.Subsingleton

public section

namespace CFSG.StandardType.TypeAReflOver

open Equiv

theorem closure_swap_left_eq_top {α : Type*} [Finite α] [DecidableEq α] (c : α) :
    Subgroup.closure {σ : Equiv.Perm α | ∃ ω ≠ c, σ = Equiv.swap c ω} = ⊤ := by
  have hS : ∀ σ ∈ {σ : Equiv.Perm α | ∃ ω ≠ c, σ = Equiv.swap c ω}, σ.IsSwap := by
    rintro σ ⟨ω, hω, rfl⟩
    exact Equiv.Perm.swap_isSwap_iff.mpr hω.symm
  haveI : MulAction.IsPretransitive
      (Subgroup.closure {σ : Equiv.Perm α | ∃ ω ≠ c, σ = Equiv.swap c ω}) α := by
    refine ⟨fun x y => ?_⟩
    have hx : Equiv.swap c x ∈
        Subgroup.closure {σ : Equiv.Perm α | ∃ ω ≠ c, σ = Equiv.swap c ω} := by
      by_cases h : x = c
      · rw [h, Equiv.swap_self]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨x, h, rfl⟩
    have hy : Equiv.swap c y ∈
        Subgroup.closure {σ : Equiv.Perm α | ∃ ω ≠ c, σ = Equiv.swap c ω} := by
      by_cases h : y = c
      · rw [h, Equiv.swap_self]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨y, h, rfl⟩
    refine ⟨⟨Equiv.swap c y * Equiv.swap c x, mul_mem hy hx⟩, ?_⟩
    simp [Subgroup.smul_def, Equiv.Perm.mul_apply]
  exact closure_of_isSwap_of_isPretransitive hS

private theorem exists_equiv_fin_add_two {n m : ℕ} (hm : m = n + 2)
    (ι : Fin (n + 1) → Fin (m + 1)) (hιinj : Function.Injective ι)
    {z₁ z₂ : Fin (m + 1)} (hz₁ : z₁ ∉ Set.range ι) (hz₂ : z₂ ∉ Set.range ι)
    (hne : z₁ ≠ z₂) :
    ∃ e : Fin (n + 3) ≃ Fin (m + 1),
      (∀ a : Fin (n + 1), e a.castSucc.castSucc = ι a) ∧
      e ((Fin.last (n + 1)).castSucc) = z₁ ∧
      e (Fin.last (n + 2)) = z₂ := by
  classical
  let Z : Set (Fin (m + 1)) := (Set.range ι)ᶜ
  have hz₁Z : z₁ ∈ Z := hz₁
  have hz₂Z : z₂ ∈ Z := hz₂
  have hcard_range : Fintype.card (Set.range ι) = n + 1 := by
    have h := Fintype.card_congr (Equiv.ofInjective ι hιinj)
    simpa using h.symm
  have hZcard : Fintype.card Z = 2 := by
    change Fintype.card ↥(Set.range ι)ᶜ = 2
    rw [Fintype.card_compl_set, Fintype.card_fin, hcard_range, hm]
    omega
  let gfun : Fin 2 → Z := fun i => if i = 0 then ⟨z₁, hz₁Z⟩ else ⟨z₂, hz₂Z⟩
  have hgfun_inj : Function.Injective gfun := by
    intro i j hij
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl
      · left; exact Fin.ext rfl
      · right; exact Fin.ext rfl
    have hj : j = 0 ∨ j = 1 := by
      rcases j with ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl
      · left; exact Fin.ext rfl
      · right; exact Fin.ext rfl
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exfalso
      exact hne (by simpa [gfun] using hij)
    · exfalso
      exact hne (by simpa [gfun] using hij.symm)
    · rfl
  have hgfun_bij : Function.Bijective gfun :=
    (Fintype.bijective_iff_injective_and_card gfun).2
      ⟨hgfun_inj, by rw [Fintype.card_fin, hZcard]⟩
  let g : Fin 2 ≃ Z := Equiv.ofBijective gfun hgfun_bij
  have hg0 : (g 0 : Fin (m + 1)) = z₁ := by simp [g, gfun]
  have hg1 : (g 1 : Fin (m + 1)) = z₂ := by simp [g, gfun]
  let s : Set (Fin (m + 1)) := Set.range ι
  let eι : Fin (n + 1) ≃ s := Equiv.ofInjective ι hιinj
  have heι (a : Fin (n + 1)) : (eι a : Fin (m + 1)) = ι a := rfl
  let hmn : (n + 1) + 2 = n + 3 := by omega
  let e : Fin (n + 3) ≃ Fin (m + 1) :=
    (finCongr hmn).symm.trans
      (finSumFinEquiv.symm.trans
        ((Equiv.sumCongr eι g).trans (Equiv.Set.sumCompl s)))
  have he_apply (a : Fin (n + 1)) : e a.castSucc.castSucc = ι a := by
    have hsrc : (finCongr hmn).symm (a.castSucc.castSucc) = Fin.castAdd 2 a := by
      ext
      simp
    simp only [e, Equiv.trans_apply, hsrc, finSumFinEquiv_symm_apply_castAdd,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
    exact heι a
  have he_last1 : e ((Fin.last (n + 1)).castSucc) = z₁ := by
    have hsrc : (finCongr hmn).symm ((Fin.last (n + 1)).castSucc) =
        Fin.natAdd (n + 1) (0 : Fin 2) := by
      ext
      simp
    simp only [e, Equiv.trans_apply, hsrc, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.Set.sumCompl_apply_inr]
    exact hg0
  have he_last2 : e (Fin.last (n + 2)) = z₂ := by
    have hsrc : (finCongr hmn).symm (Fin.last (n + 2)) =
        Fin.natAdd (n + 1) (1 : Fin 2) := by
      ext
      simp
    simp only [e, Equiv.trans_apply, hsrc, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.Set.sumCompl_apply_inr]
    exact hg1
  exact ⟨e, he_apply, he_last1, he_last2⟩

theorem star_struct {M : Type*} [Group M] {n m : ℕ}
    (E : Equiv.Perm (Fin (m + 1)) →* M) (hEinj : Function.Injective E)
    (Φ : Equiv.Perm (Fin (n + 1)) →* M) (ι : Fin (n + 1) → Fin (m + 1))
    (hιinj : Function.Injective ι)
    (hι : ∀ a b, E (Equiv.swap (ι a) (ι b)) = Φ (Equiv.swap a b))
    (bb : M) (R : Set M) (hR : R.Subsingleton)
    (hdich : ∀ z, z ∉ Set.range ι →
      E (Equiv.swap (ι (Fin.last n)) z) = bb ∨ E (Equiv.swap (ι (Fin.last n)) z) ∈ R)
    (A : Subgroup M) (hΦA : ∀ σ, Φ σ ∈ A) (hbA : bb ∈ A) (hout : ¬ E.range ≤ A) :
    (∃ r ∈ R, r ∈ E.range) ∧
      E.range ≤ Subgroup.closure (Set.range Φ ∪ insert bb R) ∧ n + 1 ≤ m ∧ m ≤ n + 2 ∧
      (m = n + 2 → ∃ T : Equiv.Perm (Fin (n + 3)) →* M, Function.Injective T ∧
        T.range = E.range ∧
        (∀ a b : Fin (n + 1),
          T (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc) = Φ (Equiv.swap a b)) ∧
        T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc) = bb ∧
        T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 2))) ∈ R) := by
  classical
  let c : Fin (m + 1) := ι (Fin.last n)
  let H : Subgroup M := Subgroup.closure (Set.range Φ ∪ insert bb R)
  let S : Set (Equiv.Perm (Fin (m + 1))) :=
    {σ | ∃ ω ≠ c, σ = Equiv.swap c ω}
  have hStop : Subgroup.closure S = ⊤ := closure_swap_left_eq_top c
  have hswap_inj : ∀ {x y : Fin (m + 1)},
      Equiv.swap c x = Equiv.swap c y → x = y := by
    intro x y h
    have h' := congrArg (fun p : Equiv.Perm (Fin (m + 1)) => p c) h
    simpa using h'
  have hstar_mem : ∀ ω : Fin (m + 1), ω ≠ c → E (Equiv.swap c ω) ∈ H := by
    intro ω hω
    by_cases hωr : ω ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hωr
      have hca : c = ι (Fin.last n) := rfl
      rw [hca, hι (Fin.last n) a]
      exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
    · have hd := hdich ω hωr
      rcases hd with h | h
      · rw [show E (Equiv.swap c ω) = bb from h]
        exact Subgroup.subset_closure (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl)))
      · exact Subgroup.subset_closure (Or.inr (Set.mem_insert_iff.mpr (Or.inr h)))
  have hS_le_comap : S ≤ Subgroup.comap E H := by
    rintro σ ⟨ω, hω, rfl⟩
    exact hstar_mem ω hω
  have hE_le_H : E.range ≤ H := by
    intro x hx
    obtain ⟨σ, rfl⟩ := hx
    have htop : (⊤ : Subgroup (Equiv.Perm (Fin (m + 1)))) ≤ Subgroup.comap E H := by
      rw [← hStop]
      rw [Subgroup.closure_le]
      exact hS_le_comap
    have hσ : σ ∈ Subgroup.comap E H := htop (Subgroup.mem_top σ)
    simpa [Subgroup.mem_comap] using hσ
  have hexists : ∃ z : Fin (m + 1), z ∉ Set.range ι ∧ E (Equiv.swap c z) ≠ bb := by
    by_contra h
    have hall : ∀ z : Fin (m + 1), z ∉ Set.range ι → E (Equiv.swap c z) = bb := by
      intro z hz
      by_contra hne
      exact h ⟨z, hz, hne⟩
    let H0 : Subgroup M := Subgroup.closure (Set.range Φ ∪ {bb})
    have hstar_mem0 : ∀ ω : Fin (m + 1), ω ≠ c → E (Equiv.swap c ω) ∈ H0 := by
      intro ω hω
      by_cases hωr : ω ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hωr
        have hca : c = ι (Fin.last n) := rfl
        rw [hca, hι (Fin.last n) a]
        exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
      · rw [hall ω hωr]
        exact Subgroup.subset_closure (Or.inr (Set.mem_singleton bb))
    have hS_le_comap0 : S ≤ Subgroup.comap E H0 := by
      rintro σ ⟨ω, hω, rfl⟩
      exact hstar_mem0 ω hω
    have hE_le_H0 : E.range ≤ H0 := by
      intro x hx
      obtain ⟨σ, rfl⟩ := hx
      have htop : (⊤ : Subgroup (Equiv.Perm (Fin (m + 1)))) ≤ Subgroup.comap E H0 := by
        rw [← hStop]
        rw [Subgroup.closure_le]
        exact hS_le_comap0
      have hσ : σ ∈ Subgroup.comap E H0 := htop (Subgroup.mem_top σ)
      simpa [Subgroup.mem_comap] using hσ
    have hH0_le_A : H0 ≤ A := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨σ, rfl⟩ := hx
        exact hΦA σ
      · rw [Set.mem_singleton_iff] at hx
        rwa [hx]
    exact hout (le_trans hE_le_H0 hH0_le_A)
  obtain ⟨z₂, hz₂Z, hz₂ne⟩ := hexists
  have hz₂R : E (Equiv.swap c z₂) ∈ R := (hdich z₂ hz₂Z).resolve_left hz₂ne
  have hexR : ∃ r ∈ R, r ∈ E.range :=
    ⟨E (Equiv.swap c z₂), hz₂R, ⟨Equiv.swap c z₂, rfl⟩⟩
  have hnot_surj : ¬ Function.Surjective ι := fun hs => hz₂Z (hs z₂)
  have hlt : n + 1 < m + 1 := by
    simpa using Fintype.card_lt_of_injective_not_surjective ι hιinj hnot_surj
  have hnm : n + 1 ≤ m := by omega
  let Z : Set (Fin (m + 1)) := (Set.range ι)ᶜ
  have hz₂Z' : z₂ ∈ Z := hz₂Z
  have hinjZ : Set.InjOn (fun z : Fin (m + 1) => E (Equiv.swap c z)) Z := by
    intro x _ y _ hxy
    exact hswap_inj (hEinj hxy)
  let φ : Z → Fin 2 := fun z =>
    if E (Equiv.swap c (z : Fin (m + 1))) = bb then 0 else 1
  have hφinj : Function.Injective φ := by
    intro z z' hzz'
    by_cases hz : E (Equiv.swap c (z : Fin (m + 1))) = bb
    · have hz' : E (Equiv.swap c (z' : Fin (m + 1))) = bb := by
        by_contra hz'ne
        have h0 : φ z = 0 := by simp [φ, hz]
        have h1 : φ z' = 1 := by simp [φ, hz'ne]
        exact (by decide : (0 : Fin 2) ≠ 1) (by rw [← h0, hzz', h1])
      exact Subtype.ext (hinjZ z.2 z'.2 (hz.trans hz'.symm))
    · have hz' : E (Equiv.swap c (z' : Fin (m + 1))) ≠ bb := by
        intro hz'
        have h0 : φ z = 1 := by simp [φ, hz]
        have h1 : φ z' = 0 := by simp [φ, hz']
        exact (by decide : (1 : Fin 2) ≠ 0) (by rw [← h0, hzz', h1])
      have hr : E (Equiv.swap c (z : Fin (m + 1))) ∈ R := (hdich z z.2).resolve_left hz
      have hr' : E (Equiv.swap c (z' : Fin (m + 1))) ∈ R :=
        (hdich z' z'.2).resolve_left hz'
      exact Subtype.ext (hinjZ z.2 z'.2 (hR hr hr'))
  have hcardZ_le : Fintype.card Z ≤ 2 := by
    have h := Fintype.card_le_of_injective φ hφinj
    simpa using h
  have hcard_range : Fintype.card (Set.range ι) = n + 1 := by
    have h := Fintype.card_congr (Equiv.ofInjective ι hιinj)
    simpa using h.symm
  have hZcard : Fintype.card Z = (m + 1) - (n + 1) := by
    change Fintype.card ↥(Set.range ι)ᶜ = (m + 1) - (n + 1)
    rw [Fintype.card_compl_set, Fintype.card_fin, hcard_range]
  have hmle : m ≤ n + 2 := by
    have hle : (m + 1) - (n + 1) ≤ 2 := by
      rw [← hZcard]
      exact hcardZ_le
    omega
  refine ⟨hexR, hE_le_H, hnm, hmle, ?_⟩
  intro hm
  have hZcard2 : Fintype.card Z = 2 := by
    rw [hZcard, hm]
    omega
  have hltZ : 1 < Fintype.card Z := by rw [hZcard2]; omega
  obtain ⟨w₁, hw₁ne⟩ := Fintype.exists_ne_of_one_lt_card hltZ ⟨z₂, hz₂Z'⟩
  have hw₁Z : (w₁ : Fin (m + 1)) ∈ Z := w₁.2
  have hw₁ne_z₂ : (w₁ : Fin (m + 1)) ≠ z₂ := fun h => hw₁ne (Subtype.ext h)
  have hEw₁ : E (Equiv.swap c (w₁ : Fin (m + 1))) = bb := by
    rcases hdich (w₁ : Fin (m + 1)) w₁.2 with h | h
    · exact h
    · exfalso
      have hEq : E (Equiv.swap c (w₁ : Fin (m + 1))) = E (Equiv.swap c z₂) := hR h hz₂R
      exact hw₁ne_z₂ (hswap_inj (hEinj hEq))
  obtain ⟨e, he_apply, he_last1, he_last2⟩ :=
    exists_equiv_fin_add_two hm ι hιinj hw₁Z hz₂Z hw₁ne_z₂
  let T : Equiv.Perm (Fin (n + 3)) →* M := E.comp e.permCongrHom.toMonoidHom
  have hTinj : Function.Injective T := by
    intro σ τ h
    exact e.permCongrHom.injective (hEinj h)
  have hTrange : T.range = E.range := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨e.permCongr σ, rfl⟩
    · rintro ⟨τ, rfl⟩
      obtain ⟨σ, hσ⟩ := e.permCongrHom.surjective τ
      refine ⟨σ, ?_⟩
      change E (e.permCongr σ) = E τ
      have hσ' : e.permCongr σ = τ := hσ
      rw [hσ']
  have hpermCongr_swap : ∀ x y : Fin (n + 3),
      e.permCongr (Equiv.swap x y) = Equiv.swap (e x) (e y) := by
    intro x y
    ext z
    simp only [Equiv.permCongr_apply]
    by_cases hx : z = e x
    · subst hx
      simp
    · by_cases hy : z = e y
      · subst hy
        simp [hx]
      · have hx' : e.symm z ≠ x := by
          intro h
          apply hx
          rw [← h, e.apply_symm_apply]
        have hy' : e.symm z ≠ y := by
          intro h
          apply hy
          rw [← h, e.apply_symm_apply]
        simp [Equiv.swap_apply_def, hx, hy, hx', hy']
  have hTswap : ∀ a b : Fin (n + 1),
      T (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc) = Φ (Equiv.swap a b) := by
    intro a b
    change E (e.permCongr
      (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc)) = Φ (Equiv.swap a b)
    rw [hpermCongr_swap, he_apply a, he_apply b, hι a b]
  have hTlast1 : T (Equiv.swap (Fin.last n).castSucc.castSucc
      (Fin.last (n + 1)).castSucc) = bb := by
    change E (e.permCongr (Equiv.swap (Fin.last n).castSucc.castSucc
      (Fin.last (n + 1)).castSucc)) = bb
    rw [hpermCongr_swap, he_apply (Fin.last n), he_last1]
    simpa [c] using hEw₁
  have hTlast2 : T (Equiv.swap (Fin.last n).castSucc.castSucc
      (Fin.last (n + 2))) ∈ R := by
    change E (e.permCongr (Equiv.swap (Fin.last n).castSucc.castSucc
      (Fin.last (n + 2)))) ∈ R
    rw [hpermCongr_swap, he_apply (Fin.last n), he_last2]
    simpa [c] using hz₂R
  exact ⟨T, hTinj, hTrange, hTswap, hTlast1, hTlast2⟩

end CFSG.StandardType.TypeAReflOver

end
