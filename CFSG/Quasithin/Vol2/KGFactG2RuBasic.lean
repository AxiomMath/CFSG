module

public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public import CFSG.Sporadic.Schreier.RuWitReps

public noncomputable section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Quasithin.H13.KGRu

theorem invCand_eq_foldl' (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand' {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl']
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem rep_ruConjA {t u : Array ℕ} {g h : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hu : Rep 4060 u h) : Rep 4060 (ruConjA t u) (g * h * g⁻¹) :=
  rep_compA (rep_compA ht hu) (rep_invCand' ht)

theorem exists_of_any_eqA {l : Array (Array ℕ)} {t : Array ℕ}
    (h : (l.any fun u => eqA 4060 t u) = true) : ∃ i < l.size, eqA 4060 t l[i]! = true := by
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, hi, by rwa [getElem!_pos l i hi]⟩

@[expose] def g2SElt (w : List ℤ) : Equiv.Perm (Fin 4060) := evalSigned ruSGens w

theorem rep_g2SW {w : List ℤ} (hw : lettersOK 4 w = true) :
    Rep 4060 (g2SW w) (g2SElt w) :=
  rep_wordA_evalSigned (k := 4) rep_ruSGens rep_ruSGensInv w hw

theorem g2SElt_mem (w : List ℤ) : g2SElt w ∈ ruS :=
  evalSigned_mem (fun _ hg => Subgroup.subset_closure hg) w

@[expose] def g2CElt (w : List ℤ) : Equiv.Perm (Fin 4060) := evalSigned [ruC0, ruC1] w

theorem rep_g2CW {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (ruCW w) (g2CElt w) := by
  have hinv : ∀ h < 2, Rep 4060 #[ruInv ruC0A, ruInv ruC1A][h]! ([ruC0, ruC1].getD h 1)⁻¹ :=
    rep_pair_getD_inv (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1)
      (rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1)
  exact rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruC0 rep_ruC1) hinv w hw

theorem g2CElt_mem (w : List ℤ) : g2CElt w ∈ ruC := by
  refine evalSigned_mem (fun g hg => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def g2WGen (k : ℕ) : Equiv.Perm (Fin 4060) := (g2WWords.map g2SElt).getD k 1

theorem rep_g2WGenA {k : ℕ} (hk : k < 6) :
    Rep 4060 g2WGenA[k]! (g2WGen k) :=
  rep_map_getD (ws := g2WWords) (fun w hw => rep_g2SW (by revert w; decide)) k hk

theorem g2WGen_memS (k : ℕ) : g2WGen k ∈ ruS := by
  unfold g2WGen
  rw [List.getD_eq_getElem?_getD]
  cases h : (g2WWords.map g2SElt)[k]? with
  | none => exact ruS.one_mem
  | some g =>
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? h)
    exact g2SElt_mem w

@[expose] def g2W : Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure {g | ∃ k < 6, g2WGen k = g}

theorem g2WGen_mem {k : ℕ} (hk : k < 6) : g2WGen k ∈ g2W :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem g2W_le : g2W ≤ ruS := by
  rw [g2W, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact g2WGen_memS k

@[expose] def g2WElt (e : ℕ) : Equiv.Perm (Fin 4060) :=
  g2WGen 0 ^ (e % 2) * (g2WGen 1 ^ (e / 2 % 2) * (g2WGen 2 ^ (e / 4 % 2) *
    (g2WGen 3 ^ (e / 8 % 2) * (g2WGen 4 ^ (e / 16 % 2) * g2WGen 5 ^ (e / 32 % 2)))))

theorem rep_g2WProd (e : ℕ) : Rep 4060 (g2WProd e) (g2WElt e) :=
  rep_compA (rep_powA (rep_g2WGenA (by norm_num)) _) (rep_compA
    (rep_powA (rep_g2WGenA (by norm_num)) _) (rep_compA (rep_powA (rep_g2WGenA (by norm_num)) _)
      (rep_compA (rep_powA (rep_g2WGenA (by norm_num)) _) (rep_compA
        (rep_powA (rep_g2WGenA (by norm_num)) _) (rep_powA (rep_g2WGenA (by norm_num)) _)))))

theorem rep_g2WArr {e : ℕ} (he : e < 64) :
    Rep 4060 g2WArr[e]! (g2WElt e) := by
  rw [g2WArr, getElem!_pos _ e (by simpa using he), Array.getElem_ofFn]
  exact rep_g2WProd e

theorem g2WElt_mem (e : ℕ) : g2WElt e ∈ g2W := by
  unfold g2WElt
  refine g2W.mul_mem (g2W.pow_mem (g2WGen_mem (by norm_num)) _) (g2W.mul_mem
    (g2W.pow_mem (g2WGen_mem (by norm_num)) _) (g2W.mul_mem
      (g2W.pow_mem (g2WGen_mem (by norm_num)) _) (g2W.mul_mem
        (g2W.pow_mem (g2WGen_mem (by norm_num)) _) (g2W.mul_mem
          (g2W.pow_mem (g2WGen_mem (by norm_num)) _) (g2W.pow_mem (g2WGen_mem (by norm_num)) _)))))

theorem eq_g2WElt_of_g2InW {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (h : g2InW t = true) :
    ∃ e < 64, g = g2WElt e := by
  obtain ⟨e, he, heq⟩ := exists_of_any_eqA h
  have he' : e < 64 := by simpa [g2WArr] using he
  exact ⟨e, he', eq_of_eqA ht (rep_g2WArr he') heq⟩

theorem mem_g2W_of_g2InW {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (h : g2InW t = true) : g ∈ g2W := by
  obtain ⟨e, -, rfl⟩ := eq_g2WElt_of_g2InW ht h
  exact g2WElt_mem e

@[expose] def g2Sigma (r : ℕ) : Equiv.Perm (Fin 4060) := g2SElt (g2ConjWords.getD r [])

theorem g2Sigma_mem (r : ℕ) : g2Sigma r ∈ ruS := g2SElt_mem _

theorem rep_g2Sigma {r : ℕ} (hr : r < 4) :
    Rep 4060 (g2SW (g2ConjWords.getD r [])) (g2Sigma r) :=
  rep_g2SW (by revert r; decide)

@[expose] def g2Wr (r : ℕ) : Subgroup (Equiv.Perm (Fin 4060)) :=
  g2W.map (MulAut.conj (g2Sigma r)).toMonoidHom

theorem mem_g2Wr_of_any {r : ℕ} (hr : r < 4) {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : ((g2WrArr[r]!).any fun u => eqA 4060 t u) = true) : g ∈ g2Wr r := by
  obtain ⟨e, he, heq⟩ := exists_of_any_eqA h
  have hsz : (g2WrArr[r]!).size = 64 := by
    rw [g2WrArr, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    simp [g2WArr]
  have he' : e < 64 := hsz ▸ he
  have hent : (g2WrArr[r]!)[e]! = ruConjA (g2SW (g2ConjWords.getD r [])) g2WArr[e]! := by
    rw [g2WrArr, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn,
      getElem!_pos _ e (by simpa [g2WArr] using he'), Array.getElem_map,
      ← getElem!_pos g2WArr e (by simpa [g2WArr] using he')]
  rw [hent] at heq
  have hrep := rep_ruConjA (rep_g2Sigma hr) (rep_g2WArr he')
  rw [eq_of_eqA ht hrep heq]
  exact ⟨g2WElt e, g2WElt_mem e, rfl⟩

@[expose] def g2VGen (k : ℕ) : Equiv.Perm (Fin 4060) :=
  if k = 0 then g2WGen 0 else g2SElt (g2VWords.getD (k - 1) [])

theorem rep_g2VGenA {k : ℕ} (hk : k < 3) :
    Rep 4060 g2VGenA[k]! (g2VGen k) := by
  interval_cases k
  · simpa [g2VGenA, g2VGen] using rep_g2WGenA (k := 0) (by norm_num)
  · simpa [g2VGenA, g2VGen] using rep_g2SW (w := g2VWords.getD 0 []) (by decide)
  · simpa [g2VGenA, g2VGen] using rep_g2SW (w := g2VWords.getD 1 []) (by decide)

@[expose] def g2V : Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure {g | ∃ k < 3, g2VGen k = g}

theorem g2VGen_mem {k : ℕ} (hk : k < 3) : g2VGen k ∈ g2V :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

@[expose] def g2VElt (e : ℕ) : Equiv.Perm (Fin 4060) :=
  g2VGen 0 ^ (e % 2) * (g2VGen 1 ^ (e / 2 % 2) * g2VGen 2 ^ (e / 4 % 2))

theorem rep_g2VProd (e : ℕ) : Rep 4060 (g2VProd e) (g2VElt e) :=
  rep_compA (rep_powA (rep_g2VGenA (by norm_num)) _) (rep_compA
    (rep_powA (rep_g2VGenA (by norm_num)) _) (rep_powA (rep_g2VGenA (by norm_num)) _))

theorem rep_g2VArr {e : ℕ} (he : e < 8) :
    Rep 4060 g2VArr[e]! (g2VElt e) := by
  rw [g2VArr, getElem!_pos _ e (by simpa using he), Array.getElem_ofFn]
  exact rep_g2VProd e

theorem g2VElt_mem (e : ℕ) : g2VElt e ∈ g2V :=
  g2V.mul_mem (g2V.pow_mem (g2VGen_mem (by norm_num)) _) (g2V.mul_mem
    (g2V.pow_mem (g2VGen_mem (by norm_num)) _) (g2V.pow_mem (g2VGen_mem (by norm_num)) _))

theorem eq_g2VElt_of_g2InV {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (h : g2InV t = true) :
    ∃ e < 8, g = g2VElt e := by
  obtain ⟨e, he, heq⟩ := exists_of_any_eqA h
  have he' : e < 8 := by simpa [g2VArr] using he
  exact ⟨e, he', eq_of_eqA ht (rep_g2VArr he') heq⟩

theorem mem_g2V_of_g2InV {t : Array ℕ}
    {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (h : g2InV t = true) : g ∈ g2V := by
  obtain ⟨e, -, rfl⟩ := eq_g2VElt_of_g2InV ht h
  exact g2VElt_mem e

@[expose] def g2Rho (i : ℕ) : Equiv.Perm (Fin 4060) := g2CElt (g2RhoWords.getD i [])

theorem rep_g2RhoA {i : ℕ} (hi : i < 20) :
    Rep 4060 (g2RhoA i) (g2Rho i) :=
  rep_g2CW (by revert i; decide)

@[expose] def g2N (j : ℕ) : Equiv.Perm (Fin 4060) := g2CElt (g2NWords.getD j [])

theorem rep_g2NA {j : ℕ} (hj : j < 2) : Rep 4060 (g2NA j) (g2N j) :=
  rep_g2CW (by revert j; decide)

@[expose] def g2X : Equiv.Perm (Fin 4060) := g2CElt g2XWord

theorem rep_g2XA : Rep 4060 g2XA g2X := rep_g2CW (by decide)

@[expose] def g2A (i : ℕ) : Equiv.Perm (Fin 4060) := g2CElt (g2AWords.getD i [])

theorem rep_g2AA {i : ℕ} (hi : i < 3) : Rep 4060 (g2AA i) (g2A i) :=
  rep_g2CW (by revert i; decide)

end CFSG.Quasithin.H13.Ch4.G2Ru
