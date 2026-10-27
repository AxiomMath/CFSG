module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertPerm
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2S08PrefixLin

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {m : ℕ}

@[expose] def prefVec (m a b : ℕ) (g : ZMod 3) : Vn (m + 1) :=
  fun i => if h : i.val < m then sortedVec m a b ⟨i.val, h⟩ else g

@[expose] def prefFun (f : ZMod 3 × ZMod 3 × ZMod 3) (c : Vn (m + 1)) (d : ZMod 3) :
    Vn (m + 1) :=
  fun i => if i.val < m then f3 f (c i) else d

@[expose] def prefCondB (f : ZMod 3 × ZMod 3 × ZMod 3) (c a : Vn (m + 1)) : Bool :=
  decide (a ⬝ᵥ c = 2) && movesB (xLast m) c a &&
    decide (∀ i j : Fin m, f3 f (c i.castSucc) = f3 f (c j.castSucc) ↔ c i.castSucc = c j.castSucc)

@[expose] def prefCovB (m : ℕ) (pats : List ((Vn (m + 1) × Vn (m + 1)) × PatV (m + 1))) : Bool :=
  (List.range (m + 1)).all fun a => (List.range (m + 1 - a)).all fun b => triples.all fun f =>
    [0, 1, 2].all fun g => [0, 1, 2].all fun d =>
      !prefCondB f (prefVec m a b g) (prefFun f (prefVec m a b g) d) ||
        decide ((prefVec m a b g, prefFun f (prefVec m a b g) d) ∈ pats.map Prod.fst)

theorem permN_xLast {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ (Fin.last m) = Fin.last m) :
    permN σ (xLast m) = xLast m := by
  funext i
  rw [permN_apply, xLast_apply, xLast_apply]
  have hσ' : σ.symm (Fin.last m) = Fin.last m := by
    rw [Equiv.symm_apply_eq]
    exact hσ.symm
  by_cases hi : i = Fin.last m
  · rw [hi, hσ']
  · rw [if_neg hi, if_neg]
    intro h
    apply hi
    have h1 := congrArg σ h
    rwa [Equiv.apply_symm_apply, hσ] at h1

variable {W A M : Subgroup (Vn (m + 1) ≃ₗ[ZMod 3] Vn (m + 1))}

theorem TestHyp.prefix_cover
    (hW : ∀ σ : Equiv.Perm (Fin (m + 1)), σ (Fin.last m) = Fin.last m → permN σ ∈ W)
    (hT : TestHyp W (xLast m) A M) {pats : List ((Vn (m + 1) × Vn (m + 1)) × PatV (m + 1))}
    (hcov : prefCovB m pats = true) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine (xLast m) u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
  intro u hu huR hux
  obtain ⟨σ, c, a, f, h, hσ, hmono, hfa, hinj, hconj⟩ := hT.exists_sorted_init hW hu huR
  have hmv := movesB_of_conj (permN_xLast hσ) hux h hconj
  have hcond : prefCondB (f 0, f 1, f 2) c a = true := by
    simp only [prefCondB, Bool.and_eq_true, decide_eq_true_eq, f3_eq]
    exact ⟨⟨h, hmv⟩, hinj⟩
  obtain ⟨a', b', hab, hc'⟩ := monotone_eq_sortedVec (fun i : Fin m => c i.castSucc) hmono
  obtain ⟨g, hg⟩ : ∃ g, c (Fin.last m) = g := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, a (Fin.last m) = d := ⟨_, rfl⟩
  have hlast : ∀ i : Fin (m + 1), ¬ i.val < m → i = Fin.last m := fun i hi =>
    Fin.ext (by rw [Fin.val_last]; have := i.isLt; omega)
  have hav : a = prefFun (f 0, f 1, f 2) c d := by
    funext i
    unfold prefFun
    by_cases hi : i.val < m
    · rw [if_pos hi, f3_eq]
      have h1 := hfa ⟨i.val, hi⟩
      rw [show (⟨i.val, hi⟩ : Fin m).castSucc = i from Fin.ext rfl] at h1
      exact h1
    · rw [if_neg hi, ← hd, hlast i hi]
  have hcv : c = prefVec m a' b' g := by
    funext i
    unfold prefVec
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      have h1 := congrFun hc' ⟨i.val, hi⟩
      rw [show (⟨i.val, hi⟩ : Fin m).castSucc = i from Fin.ext rfl] at h1
      exact h1
    · rw [dif_neg hi, ← hg, hlast i hi]
  subst hav
  subst hcv
  have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp hcov a' (List.mem_range.mpr (by omega))) b'
    (List.mem_range.mpr (by omega))) _ (mem_triples (f 0, f 1, f 2))) g (zmod3_mem_list g)) d
    (zmod3_mem_list d)
  rw [hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hc
  have hp2 : p.1.2 ⬝ᵥ p.1.1 = 2 := by
    rw [hpeq]
    exact h
  refine ⟨permN σ, hW σ hσ, p, hp, hp2, ?_⟩
  rw [hconj]
  exact refl_congr (congrArg Prod.fst hpeq).symm (congrArg Prod.snd hpeq).symm h hp2

theorem linTest_prefix_of_certOK {k ℓ : ℕ} (S : Fin ℓ → (Vn (k + 2) ≃ₗ[ZMod 3] Vn (k + 2)))
    (gens : List (Vn (k + 2) × Vn (k + 2))) (hlen : gens.length = ℓ)
    (hS : ∀ i : Fin ℓ, S i = letLin (letAt gens i)) (hk : k ≤ ℓ)
    (hadj : ∀ i : Fin k, letAt gens i =
      (Pi.single i.castSucc.castSucc 1 - Pi.single i.succ.castSucc 1,
        Pi.single i.castSucc.castSucc 1 - Pi.single i.succ.castSucc 1))
    {sets : List (List (Vn (k + 2)))} {pats : List ((Vn (k + 2) × Vn (k + 2)) × PatV (k + 2))}
    {reps : List (Vn (k + 2) × Vn (k + 2))} {s2 : List (S2V (k + 2))}
    (hOK : certOK gens (xLast (k + 1)) sets pats reps s2 = true)
    (hcov : prefCovB (k + 1) pats = true) :
    ∀ A Mg : Subgroup (Vn (k + 2) ≃ₗ[ZMod 3] Vn (k + 2)),
      TestHyp (Subgroup.closure (Set.range S)) (xLast (k + 1)) A Mg →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (xLast (k + 1)) r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (xLast (k + 1)) t → t ∈ Mg := by
  intro A Mg hT r hr hrR hrx t ht htR htx
  have hgW : ∀ l ∈ gens, letLin l ∈ Subgroup.closure (Set.range S) := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hl' : letAt gens i = gens[i] := List.getD_eq_getElem _ _ hi
    rw [← hl', ← hS ⟨i, hlen ▸ hi⟩]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hWgen : Subgroup.closure (Set.range S) ≤
      Subgroup.closure {g | ∃ l ∈ gens, g = letLin l} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Subgroup.subset_closure ⟨letAt gens i, ?_, hS i⟩
    have hi : i.val < gens.length := hlen ▸ i.isLt
    rw [show letAt gens i = gens[i.val] from List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hperm : ∀ σ : Equiv.Perm (Fin (k + 2)), σ (Fin.last (k + 1)) = Fin.last (k + 1) →
      permN σ ∈ Subgroup.closure (Set.range S) := by
    refine permN_prefix_mem_closure hk fun i => ?_
    have hne : i.castSucc.castSucc ≠ i.succ.castSucc :=
      fun h => Fin.castSucc_lt_succ.ne (Fin.castSucc_injective _ h)
    rw [hS, permN_swap _ _ hne]
    change letLin (letAt gens i) = _
    rw [hadj i, letLin_of _ (dot_sub_single_self _ _ hne)]
  exact hT.mem_of_certOK hOK hgW hWgen (hT.prefix_cover hperm hcov) hr hrR hrx ht htR htx

end CFSG.StandardType.TestLin

end
