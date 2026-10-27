module

public import Certificates.Data.CFSGNative.H13.J4Chain
public import CFSG.Sporadic.J4.Setup
public import CFSG.Perm.VectorChain

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open scoped Matrix

@[expose] def RowV : Type := Fin 112 → ZMod 2

@[expose] def toRowV (w : Fin 112 → ZMod 2) : RowV := w

@[expose] def ofRowV (w : RowV) : Fin 112 → ZMod 2 := w

instance rowVAction : MulAction (GL (Fin 112) (ZMod 2)) RowV where
  smul g w := toRowV (ofRowV w ᵥ* (((g⁻¹ : GL (Fin 112) (ZMod 2))) :
    Matrix (Fin 112) (Fin 112) (ZMod 2)))
  one_smul w := by
    show toRowV (ofRowV w ᵥ* ((((1 : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2))) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) = w
    rw [inv_one, Units.val_one, Matrix.vecMul_one]; rfl
  mul_smul g h w := by
    show toRowV (ofRowV w ᵥ* ((((g * h)⁻¹ : GL (Fin 112) (ZMod 2))) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) =
      toRowV (ofRowV (toRowV (ofRowV w ᵥ* (((h⁻¹ : GL (Fin 112) (ZMod 2))) :
        Matrix (Fin 112) (Fin 112) (ZMod 2)))) ᵥ* (((g⁻¹ : GL (Fin 112) (ZMod 2))) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)))
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]; rfl

theorem ofRowV_smul (g : GL (Fin 112) (ZMod 2)) (w : RowV) :
    ofRowV (g • w) = ofRowV w ᵥ* (((g⁻¹ : GL (Fin 112) (ZMod 2))) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) := rfl

@[expose] def PrRep (g : GL (Fin 112) (ZMod 2)) (x : Pr) : Prop :=
  rowsMatrix x.1 = (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) ∧
    rowsMatrix x.2 = ((g⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))

theorem PrRep.one : PrRep 1 prOne := by
  refine ⟨?_, ?_⟩ <;> simp only [prOne, rowsMatrix_idRows, inv_one, Units.val_one]

theorem PrRep.mul {g h : GL (Fin 112) (ZMod 2)} {x y : Pr} (hg : PrRep g x) (hh : PrRep h y) :
    PrRep (g * h) (prMul x y) := by
  refine ⟨?_, ?_⟩
  · simp only [prMul, rowsMatrix_mulRows, hg.1, hh.1, Units.val_mul]
  · simp only [prMul, rowsMatrix_mulRows, hg.2, hh.2, _root_.mul_inv_rev, Units.val_mul]

theorem PrRep.inv {g : GL (Fin 112) (ZMod 2)} {x : Pr} (hg : PrRep g x) :
    PrRep g⁻¹ (prInv x) :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem PrRep.pow {g : GL (Fin 112) (ZMod 2)} {x : Pr} (hg : PrRep g x) (e : ℕ) :
    PrRep (g ^ e) (prPow x e) := by
  induction e with
  | zero => rw [pow_zero]; exact PrRep.one
  | succ e ih => rw [pow_succ]; exact ih.mul hg

theorem PrRep.eq_one {g : GL (Fin 112) (ZMod 2)} (hg : PrRep g prOne) : g = 1 := by
  apply Units.ext
  rw [← hg.1, Units.val_one]
  exact rowsMatrix_idRows

@[expose] def FamRep (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) : Prop :=
  ∀ i, PrRep (gs i) (xs[i]?.getD prOne)

theorem FamRep.letter {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    (l : ℤ) : PrRep (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹)
      (prLetter xs l) := by
  unfold prLetter
  split_ifs
  · exact h _
  · exact (h _).inv

theorem FamRep.word {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    (w : List ℤ) : PrRep (wordProd gs w) (prWord xs w) := by
  unfold wordProd prWord
  suffices ∀ (acc : Pr) (g : GL (Fin 112) (ZMod 2)), PrRep g acc →
      PrRep (g * (w.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod)
        (w.foldl (fun acc l => prMul acc (prLetter xs l)) acc) by
    simpa using this prOne 1 PrRep.one
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (hg.mul (h.letter l))

theorem FamRep.eq_one {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    {i : ℕ} (hi : xs.size ≤ i) : gs i = 1 := by
  have := h i
  rw [Array.getElem?_eq_none_iff.2 hi, Option.getD_none] at this
  exact this.eq_one

@[expose] def levelGensGL (gs : ℕ → GL (Fin 112) (ZMod 2)) :
    List (List (List ℤ)) → List (ℕ → GL (Fin 112) (ZMod 2))
  | [] => [gs]
  | ws :: rest => gs :: levelGensGL (fun i => wordProd gs (ws.getD i [])) rest

theorem levelGens_length (xs : Array Pr) (ws : List (List (List ℤ))) :
    (levelGens xs ws).length = ws.length + 1 := by
  induction ws generalizing xs with
  | nil => rfl
  | cons w ws ih => simp [levelGens, ih]

theorem famRep_levelGens {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    (ws : List (List (List ℤ))) (j : ℕ) :
    FamRep ((levelGensGL gs ws).getD j fun _ => 1) ((levelGens xs ws).getD j #[]) := by
  induction ws generalizing gs xs j with
  | nil =>
    cases j with
    | zero => exact h
    | succ j =>
      intro i
      simp only [levelGensGL, levelGens, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_nil, Option.getD_none]
      exact PrRep.one
  | cons w ws ih =>
    cases j with
    | zero => exact h
    | succ j =>
      simp only [levelGensGL, levelGens, List.getD_cons_succ]
      apply ih
      intro i
      show PrRep (wordProd gs (w.getD i [])) _
      rw [Array.getElem?_map, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      cases w[i]? with
      | none => simpa [wordProd] using PrRep.one
      | some wi => exact h.word wi

theorem levelGensGL_succ (gs : ℕ → GL (Fin 112) (ZMod 2)) (ws : List (List (List ℤ))) {j : ℕ}
    (hj : j < ws.length) (i : ℕ) :
    ((levelGensGL gs ws).getD (j + 1) fun _ => 1) i =
      wordProd ((levelGensGL gs ws).getD j fun _ => 1) ((ws.getD j []).getD i []) := by
  induction ws generalizing gs j with
  | nil => simp at hj
  | cons w ws ih =>
    cases j with
    | zero =>
      cases ws <;> simp [levelGensGL]
    | succ j =>
      simp only [levelGensGL, List.getD_cons_succ]
      exact ih _ (by simpa using hj)

section Level

variable {sg : ℕ → GL (Fin 112) (ZMod 2)} {gens : Array Pr}

@[expose] def pathGL (sg : ℕ → GL (Fin 112) (ZMod 2)) (p : List ℕ) : GL (Fin 112) (ZMod 2) :=
  (p.map sg).prod

theorem ptOf_spec (h : FamRep sg gens) (b : V2) {p : List ℕ} (hp : ∀ g ∈ p, g < gens.size) :
    (ptOf (gens.map fun x => frTable x.2) b p).toVec =
      ofRowV (pathGL sg p • toRowV b.toVec) := by
  induction p with
  | nil =>
    simp only [ptOf, List.foldr_nil, pathGL, List.map_nil, List.prod_nil, one_smul]; rfl
  | cons g p ih =>
    have hg : g < gens.size := hp g (List.mem_cons_self ..)
    have ih' := ih fun g' hg' => hp g' (List.mem_cons_of_mem _ hg')
    simp only [ptOf, List.foldr_cons] at ih' ⊢
    rw [show (gens.map fun x => frTable x.2)[g]! = frTable (gens[g]?.getD prOne).2 by
      rw [getElem!_pos _ g (by simpa using hg), Array.getElem_map,
        Array.getElem?_eq_getElem hg, Option.getD_some]]
    rw [frApply_toVec_eq_vecMul, ih', (h g).2,
      show pathGL sg (g :: p) = sg g * pathGL sg p by simp [pathGL], mul_smul]
    rfl

theorem applyFwd_spec (h : FamRep sg gens) (X : Array V2) {p : List ℕ}
    (hp : ∀ g ∈ p, g < gens.size) :
    rowsMatrix (applyFwd (gens.map fun x => frTable x.1) X p) =
      rowsMatrix X * (pathGL sg p : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  induction p generalizing X with
  | nil => simp [applyFwd, pathGL]
  | cons g p ih =>
    have hg : g < gens.size := hp g (List.mem_cons_self ..)
    simp only [applyFwd, List.foldl_cons] at ih ⊢
    rw [ih _ fun g' hg' => hp g' (List.mem_cons_of_mem _ hg')]
    rw [show (gens.map fun x => frTable x.1)[g]! = frTable (gens[g]?.getD prOne).1 by
      rw [getElem!_pos _ g (by simpa using hg), Array.getElem_map,
        Array.getElem?_eq_getElem hg, Option.getD_some]]
    have e : X.map (frApply (frTable (gens[g]?.getD prOne).1)) =
        mulRows X (gens[g]?.getD prOne).1 := rfl
    rw [e, rowsMatrix_mulRows, (h g).1,
      show pathGL sg (g :: p) = sg g * pathGL sg p by simp [pathGL], Units.val_mul,
      Matrix.mul_assoc]

end Level

section Chain

variable {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} {bs : List V2}
  {ws : List (List (List ℤ))}

@[expose] def levelGL (gs : ℕ → GL (Fin 112) (ZMod 2)) (ws : List (List (List ℤ))) (j : ℕ) :
    ℕ → GL (Fin 112) (ZMod 2) :=
  (levelGensGL gs ws).getD j fun _ => 1

@[expose] def trGL (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) (bs : List V2)
    (ws : List (List (List ℤ))) (j k : ℕ) : GL (Fin 112) (ZMod 2) :=
  pathGL (levelGL gs ws j) (mkLevels xs bs ws)[j]!.paths[k]!

@[expose] def levelSet (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) (bs : List V2)
    (ws : List (List (List ℤ))) (j : ℕ) : Set (GL (Fin 112) (ZMod 2)) :=
  {g | ∃ i < (mkLevels xs bs ws)[j]!.gens.size, levelGL gs ws j i = g}

theorem mkLevels_size (hlen : bs.length = ws.length + 1) :
    (mkLevels xs bs ws).size = ws.length + 1 := by
  simp [mkLevels, List.length_zip, levelGens_length, hlen]

theorem mkLevels_getElem! (hlen : bs.length = ws.length + 1) {j : ℕ} (hj : j < ws.length + 1) :
    (mkLevels xs bs ws)[j]! = mkLvl ((levelGens xs ws).getD j #[]) (bs.getD j V2.zero) := by
  have hj1 : j < (levelGens xs ws).length := by rw [levelGens_length]; exact hj
  have hj2 : j < bs.length := by rw [hlen]; exact hj
  rw [getElem!_pos _ j (by rw [mkLevels_size hlen]; exact hj)]
  simp only [mkLevels, List.getElem_toArray, Array.getElem_map, List.getElem_zip]
  rw [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2]


theorem mkLevels_spec (hlen : bs.length = ws.length + 1) {j : ℕ} (hj : j < ws.length + 1) :
    (mkLevels xs bs ws)[j]!.gens = (levelGens xs ws).getD j #[] ∧
    (mkLevels xs bs ws)[j]!.tab = ((levelGens xs ws).getD j #[]).map (fun x => frTable x.1) ∧
    (mkLevels xs bs ws)[j]!.itab = ((levelGens xs ws).getD j #[]).map (fun x => frTable x.2) ∧
    (mkLevels xs bs ws)[j]!.pts = (mkLevels xs bs ws)[j]!.paths.map
      (ptOf (((levelGens xs ws).getD j #[]).map (fun x => frTable x.2))
        (mkLevels xs bs ws)[j]!.base) := by
  rw [mkLevels_getElem! hlen hj]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem mkLevels_out (hlen : bs.length = ws.length + 1) :
    (mkLevels xs bs ws)[ws.length + 1]!.gens = #[] := by
  rw [getElem!_neg _ _ (by rw [mkLevels_size hlen]; omega)]
  rfl

@[expose] def prodTr (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) (bs : List V2)
    (ws : List (List (List ℤ))) : ℕ → List ℕ → GL (Fin 112) (ZMod 2)
  | _, [] => 1
  | i, k :: ks => trGL gs xs bs ws i k * prodTr gs xs bs ws (i + 1) ks

theorem prod_map_toList {α : Type*} [Inhabited α] (L : Array α) (f : α → ℕ) :
    (L.toList.map f).prod = ∏ j ∈ Finset.range L.size, f L[j]! := by
  rw [Finset.prod_range fun j => f L[j]!, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_ofFn]
    rw [getElem!_pos L n (by simpa using h1)]

theorem card_closure_of_chainOK (hxs : FamRep gs xs) (hlen : bs.length = ws.length + 1)
    (h : chainOK (mkLevels xs bs ws) = true) :
    Nat.card (Subgroup.closure {g | ∃ i < xs.size, gs i = g}) =
      (orbitSizes (mkLevels xs bs ws)).prod := by
  set L := mkLevels xs bs ws with hL
  have hm : L.size = ws.length + 1 := mkLevels_size hlen
  have hlev : ∀ j < ws.length + 1, levelOK L j = true := fun j hj =>
    List.all_eq_true.1 h j (List.mem_range.2 (by rw [hm]; exact hj))
  have hrep : ∀ j, FamRep (levelGL gs ws j) ((levelGens xs ws).getD j #[]) :=
    famRep_levelGens hxs ws
  have hparts : ∀ j < ws.length + 1, pathsOK L[j]! = true ∧ distinctOK L[j]! = true ∧
      (L.size ≤ j + 1 ∨ fixOK L[j]! L[j + 1]! = true) ∧
      ∀ k < L[j]!.pts.size, ∀ g < L[j]!.gens.size, schreierAt L j g k = true := by
    intro j hj
    have := hlev j hj
    simp only [levelOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, fun k hk g hg => this.2 k hk g hg⟩
  have hgsz : ∀ j < ws.length + 1, L[j]!.gens.size = ((levelGens xs ws).getD j #[]).size :=
    fun j hj => by rw [(mkLevels_spec (xs := xs) hlen hj).1]
  have hpathv : ∀ j < ws.length + 1, ∀ k : ℕ, ∀ g : ℕ, g ∈ L[j]!.paths[k]! →
      g < L[j]!.gens.size := by
    intro j hj k g hg
    have hp := (hparts j hj).1
    simp only [pathsOK, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true,
      List.all_eq_true] at hp
    by_cases hk : k < L[j]!.paths.size
    · rw [getElem!_pos _ k hk] at hg
      exact hp.2 k hk g hg
    · rw [getElem!_neg _ k hk] at hg
      change g ∈ ([] : List ℕ) at hg
      simp at hg
  have hpath0 : ∀ j < ws.length + 1, L[j]!.paths[0]! = [] := by
    intro j hj
    have hp := (hparts j hj).1
    simp only [pathsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact hp.1.2
  have hptsz : ∀ j < ws.length + 1, L[j]!.pts.size = L[j]!.paths.size := fun j hj => by
    rw [(mkLevels_spec (xs := xs) hlen hj).2.2.2, Array.size_map]
  let base : ℕ → RowV := fun j => toRowV L[j]!.base.toVec
  let gens : ℕ → Set (GL (Fin 112) (ZMod 2)) := levelSet gs xs bs ws
  let size : ℕ → ℕ := fun j => L[j]!.pts.size
  let tr : ℕ → ℕ → GL (Fin 112) (ZMod 2) := trGL gs xs bs ws
  let pt : ℕ → ℕ → RowV := fun j k => tr j k • base j
  have hgen_mem : ∀ j < ws.length + 1, ∀ i, levelGL gs ws j i ∈ Subgroup.closure (gens j) := by
    intro j hj i
    by_cases hi : i < L[j]!.gens.size
    · exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    · rw [(hrep j).eq_one (by rw [← hgsz j hj]; omega)]
      exact Subgroup.one_mem _
  have htr_mem : ∀ j < ws.length + 1, ∀ k, tr j k ∈ Subgroup.closure (gens j) := by
    intro j hj k
    show pathGL (levelGL gs ws j) _ ∈ _
    unfold pathGL
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    exact hgen_mem j hj g
  have hgens : ∀ j < ws.length + 1, gens (j + 1) ⊆ Subgroup.closure (gens j) := by
    rintro j hj _ ⟨i, hi, rfl⟩
    by_cases hj1 : j + 1 < ws.length + 1
    · show levelGL gs ws (j + 1) i ∈ _
      unfold levelGL
      rw [levelGensGL_succ gs ws (by omega) i]
      exact wordProd_mem _ (fun m => hgen_mem j hj m) _
    · have : j + 1 = ws.length + 1 := by omega
      rw [this, mkLevels_out hlen] at hi
      simp at hi
  have hmono : ∀ j i, j < ws.length + 1 → j ≤ i →
      Subgroup.closure (gens i) ≤ Subgroup.closure (gens j) := by
    intro j i hj hji
    induction i, hji using Nat.le_induction with
    | base => exact le_rfl
    | succ i hji ih =>
      by_cases hi : i < ws.length + 1
      · exact ((Subgroup.closure_le _).2 (hgens i hi)).trans ih
      · have hi' : ws.length + 1 ≤ i + 1 := by omega
        have : gens (i + 1) = ∅ := by
          ext g
          simp only [Set.mem_empty_iff_false, iff_false]
          rintro ⟨n, hn, -⟩
          rw [getElem!_neg _ _ (by rw [hm]; omega)] at hn
          exact absurd hn (by simp [default])
        rw [this, Subgroup.closure_empty]
        exact bot_le
  have hpts_eq : ∀ j < ws.length + 1, L[j]!.pts = L[j]!.paths.map
      (ptOf (((levelGens xs ws).getD j #[]).map (fun x => frTable x.2)) L[j]!.base) :=
    fun j hj => (mkLevels_spec (xs := xs) hlen hj).2.2.2
  have hpt_vec : ∀ j < ws.length + 1, ∀ k < size j,
      (L[j]!.pts[k]!).toVec = ofRowV (pt j k) := by
    intro j hj k hk
    have hk' : k < L[j]!.paths.size := by rw [← hptsz j hj]; exact hk
    have hpk : L[j]!.pts[k]! = ptOf (((levelGens xs ws).getD j #[]).map (fun x => frTable x.2))
        L[j]!.base L[j]!.paths[k]! := by
      rw [hpts_eq j hj, getElem!_pos _ k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
        getElem!_pos _ k hk']
    rw [hpk, ptOf_spec (hrep j) L[j]!.base (fun g hg => by
      rw [← hgsz j hj]; exact hpathv j hj k g hg)]
    rfl
  have hinj : ∀ j < ws.length + 1, ∀ k < size j, ∀ k' < size j, pt j k = pt j k' → k = k' := by
    intro j hj k hk k' hk' e
    have hd := (hparts j hj).2.1
    simp only [distinctOK, Bool.and_eq_true, Array.all_eq_true, List.all_eq_true,
      List.mem_range, Bool.not_eq_true'] at hd
    have hw : ∀ i < size j, (L[j]!.pts[i]!).wf = true := fun i hi => by
      rw [getElem!_pos _ i hi]; exact hd.1 i hi
    have hv : (L[j]!.pts[k]!).toVec = (L[j]!.pts[k']!).toVec := by
      rw [hpt_vec j hj k hk, hpt_vec j hj k' hk', e]
    have heq := V2.eq_of_toVec_eq (hw k hk) (hw k' hk') hv
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hd.2 k' hk' k hlt
      rw [heq, V2.beq_iff.2 rfl] at h1
      exact absurd h1 (by decide)
    · have h1 := hd.2 k hk k' hlt
      rw [heq, V2.beq_iff.2 rfl] at h1
      exact absurd h1 (by decide)
  have hchain : ∀ (ks : List ℕ) (i : ℕ) (X : Array V2), i + ks.length ≤ ws.length + 1 →
      rowsMatrix (chainFwd L i ks X) =
        rowsMatrix X * (prodTr gs xs bs ws i ks : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
    intro ks
    induction ks with
    | nil => intro i X _; simp [chainFwd, prodTr]
    | cons k ks ih =>
      intro i X hi
      simp only [List.length_cons] at hi
      have hi' : i < ws.length + 1 := by omega
      simp only [chainFwd, prodTr]
      rw [ih (i + 1) _ (by omega),
        show L[i]!.tab = ((levelGens xs ws).getD i #[]).map (fun x => frTable x.1) from
          (mkLevels_spec (xs := xs) hlen hi').2.1,
        applyFwd_spec (hrep i) X (fun g hg => by rw [← hgsz i hi']; exact hpathv i hi' k g hg),
        Units.val_mul, Matrix.mul_assoc]
      rfl
  have hprod_mem : ∀ (ks : List ℕ) (i : ℕ), i + ks.length ≤ ws.length + 1 →
      prodTr gs xs bs ws i ks ∈ Subgroup.closure (gens i) := by
    intro ks
    induction ks with
    | nil => intro i _; exact Subgroup.one_mem _
    | cons k ks ih =>
      intro i hi
      simp only [List.length_cons] at hi
      exact Subgroup.mul_mem _ (htr_mem i (by omega) k)
        (hmono i (i + 1) (by omega) (by omega) (ih (i + 1) (by omega)))
  have hsch : ∀ j < ws.length + 1, ∀ k < size j, ∀ i < L[j]!.gens.size,
      ∃ k'' < size j, levelGL gs ws j i • pt j k = pt j k'' ∧
        (tr j k'')⁻¹ * levelGL gs ws j i * tr j k ∈ Subgroup.closure (gens (j + 1)) := by
    intro j hj k hk i hi
    have hs := (hparts j hj).2.2.2 k hk i hi
    have hspec := mkLevels_spec (xs := xs) hlen hj
    have hiG : i < ((levelGens xs ws).getD j #[]).size := by rw [← hgsz j hj]; exact hi
    simp only [schreierAt] at hs
    split at hs
    · exact absurd hs (by decide)
    · rename_i k'' _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨hk'', hz⟩, hlen', hrows⟩ := hs
      refine ⟨k'', hk'', ?_, ?_⟩
      · have hz' := congrArg V2.toVec (V2.beq_iff.1 hz)
        rw [hspec.2.2.1, getElem!_pos _ i (by rw [Array.size_map]; exact hiG),
          Array.getElem_map, frApply_toVec_eq_vecMul, hpt_vec j hj k hk, hpt_vec j hj k'' hk'',
          show ((levelGens xs ws).getD j #[])[i] = ((levelGens xs ws).getD j #[])[i]?.getD prOne
            by rw [Array.getElem?_eq_getElem hiG, Option.getD_some], (hrep j i).2] at hz'
        exact (congrArg toRowV hz'.symm : _)
      · have hr := congrArg rowsMatrix (eqRows_iff.1 hrows)
        rw [hchain _ _ _ (by omega), hspec.2.1,
          applyFwd_spec (hrep j) _ (fun g hg => by rw [← hgsz j hj]; exact hpathv j hj k g hg),
          applyFwd_spec (hrep j) _ (fun g hg => by rw [← hgsz j hj]; exact hpathv j hj k'' g hg),
          rowsMatrix_idRows, Matrix.one_mul, hspec.1, (hrep j i).1] at hr
        have hgl : levelGL gs ws j i * tr j k = tr j k'' * prodTr gs xs bs ws (j + 1) _ :=
          Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hr)
        rw [mul_assoc, hgl, inv_mul_cancel_left]
        rw [hspec.2.1] at hlen'
        exact hprod_mem _ _ (by omega)
  have hfix : ∀ j < ws.length + 1, ∀ g ∈ gens (j + 1), g • base j = base j := by
    rintro j hj _ ⟨i, hi, rfl⟩
    have hj1 : j + 1 < ws.length + 1 := by
      by_contra hc
      rw [getElem!_neg _ (j + 1) (by rw [hm]; omega)] at hi
      exact absurd hi (by simp [default])
    have hfx : fixOK L[j]! L[j + 1]! = true := by
      rcases (hparts j hj).2.2.1 with hle | hfx
      · omega
      · exact hfx
    simp only [fixOK, List.all_eq_true, List.mem_range] at hfx
    have hb := congrArg V2.toVec (V2.beq_iff.1 (hfx i hi))
    have hspec1 := mkLevels_spec (xs := xs) hlen hj1
    have hiG : i < ((levelGens xs ws).getD (j + 1) #[]).size := by
      rw [← hgsz (j + 1) hj1]; exact hi
    rw [hspec1.2.1, getElem!_pos _ i (by rw [Array.size_map]; exact hiG), Array.getElem_map,
      frApply_toVec_eq_vecMul,
      show ((levelGens xs ws).getD (j + 1) #[])[i] =
        ((levelGens xs ws).getD (j + 1) #[])[i]?.getD prOne
        by rw [Array.getElem?_eq_getElem hiG, Option.getD_some], (hrep (j + 1) i).1] at hb
    show toRowV (ofRowV (base j) ᵥ* (((levelGL gs ws (j + 1) i)⁻¹ :
      GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))) = base j
    have e : ofRowV (base j) = L[j]!.base.toVec := rfl
    rw [e, ← hb, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  have hlast : gens (ws.length + 1) ⊆ {1} := by
    rintro _ ⟨i, hi, rfl⟩
    rw [mkLevels_out hlen] at hi
    exact absurd hi (by simp)
  have hg0 : gens 0 = {g | ∃ i < xs.size, gs i = g} := by
    have h1 : L[0]!.gens = xs := by
      rw [(mkLevels_spec (xs := xs) hlen (Nat.succ_pos _)).1]
      cases ws <;> rfl
    have h2 : levelGL gs ws 0 = gs := by
      unfold levelGL; cases ws <;> rfl
    ext g
    show (∃ i < L[0]!.gens.size, levelGL gs ws 0 i = g) ↔ _
    rw [h1, h2]
    rfl
  have key := CFSG.Perm.card_closure_eq_prod_of_chain (ws.length + 1) base gens size pt tr
    hgens hfix (fun j hj => by
      show 0 < L[j]!.pts.size
      have hp := (hparts j hj).1
      simp only [pathsOK, Bool.and_eq_true, decide_eq_true_eq] at hp
      rw [hptsz j hj]; exact hp.1.1)
    (fun j hj => by
      show tr j 0 • base j = base j
      rw [show tr j 0 = 1 by
        show pathGL (levelGL gs ws j) _ = 1
        rw [show (mkLevels xs bs ws)[j]!.paths[0]! = [] from hpath0 j hj]; rfl, one_smul])
    (fun j hj => by
      show pathGL (levelGL gs ws j) _ = 1
      rw [show (mkLevels xs bs ws)[j]!.paths[0]! = [] from hpath0 j hj]; rfl)
    (fun j hj k _ => htr_mem j hj k) (fun _ _ _ _ => rfl) hinj
    (fun j hj k hk g hg => by
      obtain ⟨i, hi, rfl⟩ := hg
      obtain ⟨k'', hk'', e, -⟩ := hsch j hj k hk i hi
      exact ⟨k'', hk'', e⟩)
    (fun j hj g hg k hk k' hk' e => by
      obtain ⟨i, hi, rfl⟩ := hg
      obtain ⟨k'', hk'', e', hmem⟩ := hsch j hj k hk i hi
      rwa [hinj j hj k' hk' k'' hk'' (e.symm.trans e')])
    hlast
  rw [← hg0, key, orbitSizes, prod_map_toList, hm]

end Chain

end CFSG.Quasithin.H13.J4
