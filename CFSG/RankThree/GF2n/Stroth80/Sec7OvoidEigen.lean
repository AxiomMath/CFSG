module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_ovoid_sum_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {ι : Type*} [DecidableEq ι] (E : ι → Submodule K V)
    (hE : iSupIndep E) (S : Finset ι) :
    ∑ i ∈ S, Module.finrank K (E i) ≤ Module.finrank K V := by
  have key : ∀ U : Finset ι, Module.finrank K ↥(U.sup E) = ∑ i ∈ U, Module.finrank K (E i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert a U ha ih =>
      have hdisj : Disjoint (E a) (U.sup E) := by
        rw [Finset.sup_eq_iSup]
        have h := hE.disjoint_biSup (x := a) (y := (U : Set ι)) (by simpa using ha)
        simpa using h
      have h := Submodule.finrank_sup_add_finrank_inf_eq (E a) (U.sup E)
      rw [hdisj.eq_bot, finrank_bot, add_zero] at h
      rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
      exact h
  rw [← key S]
  exact Submodule.finrank_le _

theorem sec7_ovoid_weight_sum_le {β : Type*} (S : Finset β) (a : β → ℕ) (q : ℕ)
    (hq : 2 ≤ q) (hsum : ∑ x ∈ S, a x ≤ 4) :
    ∑ x ∈ S, (if a x = 3 then q + 1 else a x) ≤ q + 2 := by
  have h1 : ∀ x ∈ S, (if a x = 3 then q + 1 else a x)
      ≤ a x + (q - 2) * (if a x = 3 then 1 else 0) := by
    intro x _
    split_ifs <;> omega
  have h2 : ∀ x ∈ S, 3 * (if a x = 3 then 1 else 0) ≤ a x := by
    intro x _
    split_ifs <;> omega
  have hD : 3 * ∑ x ∈ S, (if a x = 3 then 1 else 0) ≤ 4 := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum h2) hsum
  have hD1 : ∑ x ∈ S, (if a x = 3 then 1 else 0) ≤ 1 := by omega
  calc ∑ x ∈ S, (if a x = 3 then q + 1 else a x)
      ≤ ∑ x ∈ S, (a x + (q - 2) * (if a x = 3 then 1 else 0)) := Finset.sum_le_sum h1
    _ = ∑ x ∈ S, a x + (q - 2) * ∑ x ∈ S, (if a x = 3 then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 + (q - 2) * 1 := Nat.add_le_add hsum (Nat.mul_le_mul (le_refl _) hD1)
    _ = q + 2 := by omega

theorem sec7_ovoid_eigen_scalar {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (hV : Module.finrank K V = 4) (O : Set (Submodule K V))
    (hO1 : ∀ P ∈ O, Module.finrank K P = 1) (hcard : O.ncard = Nat.card K ^ 2 + 1)
    (hline : ∀ l : Submodule K V, Module.finrank K l = 2 → {P | P ∈ O ∧ P ≤ l}.ncard ≤ 2)
    (hplane : ∀ π : Submodule K V, Module.finrank K π = 3 →
      {P | P ∈ O ∧ P ≤ π}.ncard ≤ Nat.card K + 1)
    (T : V →ₗ[K] V) (hT : ∀ P ∈ O, ∀ x ∈ P, T x ∈ P) :
    ∃ c : K, T = c • LinearMap.id := by
  classical
  by_contra hnot
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hex : ∀ P ∈ O, ∃ c : K, P ≤ Module.End.eigenspace T c := by
    intro P hP
    have hP1 : Module.finrank K P = 1 := hO1 P hP
    have hPbot : P ≠ ⊥ := by
      rintro rfl
      simp at hP1
    obtain ⟨v, hvP, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
    have hle : K ∙ v ≤ P := (Submodule.span_singleton_le_iff_mem v P).2 hvP
    have hd : Module.finrank K (K ∙ v) = Module.finrank K P := by
      rw [finrank_span_singleton hv0, hP1]
    have hPeq : P = K ∙ v := (Submodule.eq_of_le_of_finrank_eq hle hd).symm
    have hTv : T v ∈ K ∙ v := by
      rw [← hPeq]
      exact hT P hP v hvP
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hTv
    refine ⟨c, ?_⟩
    rw [hPeq, Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
    exact hc.symm
  choose! lam hlam using hex
  have hproper : ∀ c : K, Module.End.eigenspace T c ≠ ⊤ := by
    intro c htop
    apply hnot
    refine ⟨c, LinearMap.ext fun x => ?_⟩
    have hx : x ∈ Module.End.eigenspace T c := by
      rw [htop]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    simpa using hx
  have hOfin : O.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; positivity)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Submodule K V), F = hOfin.toFinset := ⟨_, rfl⟩
  have hFmem : ∀ P, P ∈ F ↔ P ∈ O := by
    intro P
    rw [hF]
    exact hOfin.mem_toFinset
  have hFcard : F.card = Nat.card K ^ 2 + 1 := by
    rw [← hcard, hF, Set.ncard_eq_toFinset_card O hOfin]
  have hsplit : F.card = ∑ c ∈ F.image lam, (F.filter (fun P => lam P = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun P hP => Finset.mem_image_of_mem lam hP)
  have hsum4 : ∑ c ∈ F.image lam, Module.finrank K (Module.End.eigenspace T c) ≤ 4 := by
    have h := sec7_ovoid_sum_finrank_le (Module.End.eigenspace T)
      (Module.End.eigenspaces_iSupIndep T) (F.image lam)
    rw [hV] at h
    exact h
  have hbound : ∀ c ∈ F.image lam, (F.filter (fun P => lam P = c)).card ≤
      (if Module.finrank K (Module.End.eigenspace T c) = 3 then Nat.card K + 1
        else Module.finrank K (Module.End.eigenspace T c)) := by
    intro c hc
    obtain ⟨P0, hP0F, hP0c⟩ := Finset.mem_image.1 hc
    have hP0le : P0 ≤ Module.End.eigenspace T c := by
      have h := hlam P0 ((hFmem P0).1 hP0F)
      rw [hP0c] at h
      exact h
    have hpos : 1 ≤ Module.finrank K (Module.End.eigenspace T c) := by
      have h := Submodule.finrank_mono hP0le
      rw [hO1 P0 ((hFmem P0).1 hP0F)] at h
      exact h
    have hlt : Module.finrank K (Module.End.eigenspace T c) < 4 := by
      have h := Submodule.finrank_lt (hproper c)
      omega
    have hsub : ∀ P ∈ F.filter (fun P => lam P = c),
        P ∈ O ∧ P ≤ Module.End.eigenspace T c := by
      intro P hP
      have hP' := Finset.mem_filter.1 hP
      have hPO : P ∈ O := (hFmem P).1 hP'.1
      have hPc : lam P = c := hP'.2
      refine ⟨hPO, ?_⟩
      have h := hlam P hPO
      rw [hPc] at h
      exact h
    have hcount : (F.filter (fun P => lam P = c)).card ≤
        {P | P ∈ O ∧ P ≤ Module.End.eigenspace T c}.ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ (hOfin.subset (fun P hP => hP.1))
      intro P hP
      exact hsub P (Finset.mem_coe.1 hP)
    rcases (by omega : Module.finrank K (Module.End.eigenspace T c) = 1 ∨
        Module.finrank K (Module.End.eigenspace T c) = 2 ∨
        Module.finrank K (Module.End.eigenspace T c) = 3) with h1 | h2 | h3
    · have hn3 : ¬ Module.finrank K (Module.End.eigenspace T c) = 3 := by omega
      rw [if_neg hn3, h1]
      apply Finset.card_le_one.2
      intro P hP P' hP'
      obtain ⟨hPO, hPle⟩ := hsub P hP
      obtain ⟨hP'O, hP'le⟩ := hsub P' hP'
      have hPe : P = Module.End.eigenspace T c :=
        Submodule.eq_of_le_of_finrank_eq hPle (by rw [hO1 P hPO, h1])
      have hP'e : P' = Module.End.eigenspace T c :=
        Submodule.eq_of_le_of_finrank_eq hP'le (by rw [hO1 P' hP'O, h1])
      exact hPe.trans hP'e.symm
    · have hn3 : ¬ Module.finrank K (Module.End.eigenspace T c) = 3 := by omega
      rw [if_neg hn3, h2]
      exact le_trans hcount (hline _ h2)
    · rw [if_pos h3]
      exact le_trans hcount (hplane _ h3)
  have hmain : F.card ≤ Nat.card K + 2 := by
    rw [hsplit]
    calc ∑ c ∈ F.image lam, (F.filter (fun P => lam P = c)).card
        ≤ ∑ c ∈ F.image lam, (if Module.finrank K (Module.End.eigenspace T c) = 3 then
            Nat.card K + 1 else Module.finrank K (Module.End.eigenspace T c)) :=
          Finset.sum_le_sum hbound
      _ ≤ Nat.card K + 2 :=
          sec7_ovoid_weight_sum_le (F.image lam)
            (fun c => Module.finrank K (Module.End.eigenspace T c)) (Nat.card K) hq hsum4
  rw [hFcard] at hmain
  nlinarith

end CFSG.RankThree.GF2n.Stroth80
