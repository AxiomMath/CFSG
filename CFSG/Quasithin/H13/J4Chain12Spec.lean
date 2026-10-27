module

public import Certificates.Data.CFSGNative.H13.J4Chain12
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Sporadic.J4.Setup

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Quasithin.H13.J4.Native
open CFSG.Sporadic.J4 (wordProd wordProd_mem)
open scoped Matrix

theorem mul_card_le_of_witnesses {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (H K : Subgroup G) (b : X) (hKH : K ≤ H) (hKb : ∀ g ∈ K, g • b = b) (n : ℕ) (w : ℕ → G)
    (hw : ∀ k < n, w k ∈ H) (hinj : ∀ k < n, ∀ k' < n, w k • b = w k' • b → k = k') :
    n * Nat.card K ≤ Nat.card H := by
  have h1 : Nat.card H = Nat.card (MulAction.orbit H b) * Nat.card (MulAction.stabilizer H b) := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  have hfin : Finite (MulAction.orbit H b) := (Set.finite_range fun h : H => h • b).to_subtype
  have h2 : n ≤ Nat.card (MulAction.orbit H b) := by
    let f : Fin n → MulAction.orbit H b := fun k => ⟨w k • b, ⟨⟨w k, hw k k.2⟩, rfl⟩⟩
    have hf : Function.Injective f := fun k k' e =>
      Fin.ext (hinj k k.2 k' k'.2 (congrArg Subtype.val e))
    simpa using Nat.card_le_card_of_injective f hf
  have h3 : Nat.card K ≤ Nat.card (MulAction.stabilizer H b) := by
    have hle : K.subgroupOf H ≤ MulAction.stabilizer H b := fun x hx => by
      rw [MulAction.mem_stabilizer_iff]
      exact hKb x hx
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
    exact Subgroup.card_le_of_le hle
  rw [h1]
  exact Nat.mul_le_mul h2 h3

theorem prod_le_card_closure {G X : Type*} [Group G] [MulAction G X] [Finite G] (m : ℕ)
    (base : ℕ → X) (gens : ℕ → Set G) (size : ℕ → ℕ) (tr : ℕ → ℕ → G)
    (hgens : ∀ j < m, gens (j + 1) ⊆ Subgroup.closure (gens j))
    (hfix : ∀ j < m, ∀ g ∈ gens (j + 1), g • base j = base j)
    (htr : ∀ j < m, ∀ k < size j, tr j k ∈ Subgroup.closure (gens j))
    (hinj : ∀ j < m, ∀ k < size j, ∀ k' < size j, tr j k • base j = tr j k' • base j → k = k') :
    ∏ j ∈ Finset.range m, size j ≤ Nat.card (Subgroup.closure (gens 0)) := by
  suffices h : ∀ i ≤ m, (∏ j ∈ Finset.range i, size j) * Nat.card (Subgroup.closure (gens i)) ≤
      Nat.card (Subgroup.closure (gens 0)) from
    le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) (h m le_rfl)
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have hK : Subgroup.closure (gens (i + 1)) ≤ MulAction.stabilizer G (base i) :=
      (Subgroup.closure_le _).2 fun g hg => hfix i (by omega) g hg
    have := mul_card_le_of_witnesses (Subgroup.closure (gens i))
      (Subgroup.closure (gens (i + 1))) (base i) ((Subgroup.closure_le _).2 (hgens i (by omega)))
      (fun g hg => hK hg) (size i) (tr i) (htr i (by omega)) (hinj i (by omega))
    calc (∏ j ∈ Finset.range (i + 1), size j) * Nat.card (Subgroup.closure (gens (i + 1)))
        = (∏ j ∈ Finset.range i, size j) *
            (size i * Nat.card (Subgroup.closure (gens (i + 1)))) := by
          rw [Finset.prod_range_succ, mul_assoc]
      _ ≤ (∏ j ∈ Finset.range i, size j) * Nat.card (Subgroup.closure (gens i)) :=
          Nat.mul_le_mul_left _ this
      _ ≤ _ := ih (by omega)

@[expose] def ColV12 : Type := Fin 12 → ZMod 2

@[expose] def toColV12 (x : Fin 12 → ZMod 2) : ColV12 := x

@[expose] def ofColV12 (x : ColV12) : Fin 12 → ZMod 2 := x

instance colV12Action : MulAction (GL (Fin 12) (ZMod 2)) ColV12 where
  smul g x := toColV12 ((g : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ ofColV12 x)
  one_smul x := by
    show toColV12 (((1 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
      ofColV12 x) = x
    rw [Units.val_one, Matrix.one_mulVec]; rfl
  mul_smul g h x := by
    show toColV12 (((g * h : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
      ofColV12 x) = toColV12 ((g : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
        ofColV12 (toColV12 ((h : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ ofColV12 x)))
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]; rfl

instance : Finite ColV12 := inferInstanceAs (Finite (Fin 12 → ZMod 2))

theorem ofColV12_smul (g : GL (Fin 12) (ZMod 2)) (x : ColV12) :
    ofColV12 (g • x) = (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ ofColV12 x := rfl

@[expose] def PrRep12 (g : GL (Fin 12) (ZMod 2)) (x : Pr12) : Prop :=
  rowsMatrix 12 x.1 = (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∧
    rowsMatrix 12 x.2 = ((g⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))

theorem PrRep12.one : PrRep12 1 pr12One := by
  refine ⟨?_, ?_⟩ <;> simp only [pr12One, rowsMatrix_idRows, inv_one, Units.val_one]

theorem PrRep12.mul {g h : GL (Fin 12) (ZMod 2)} {x y : Pr12} (hg : PrRep12 g x)
    (hh : PrRep12 h y) : PrRep12 (g * h) (pr12Mul x y) := by
  refine ⟨?_, ?_⟩
  · simp only [pr12Mul, rowsMatrix_mulRows, hg.1, hh.1, Units.val_mul]
  · simp only [pr12Mul, rowsMatrix_mulRows, hg.2, hh.2, _root_.mul_inv_rev, Units.val_mul]

theorem PrRep12.inv {g : GL (Fin 12) (ZMod 2)} {x : Pr12} (hg : PrRep12 g x) :
    PrRep12 g⁻¹ (pr12Inv x) :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem PrRep12.eq_one {g : GL (Fin 12) (ZMod 2)} (hg : PrRep12 g pr12One) : g = 1 := by
  apply Units.ext
  rw [← hg.1, Units.val_one]
  exact rowsMatrix_idRows 12

@[expose] def FamRep12 (gs : ℕ → GL (Fin 12) (ZMod 2)) (xs : Array Pr12) : Prop :=
  ∀ i, PrRep12 (gs i) (xs[i]?.getD pr12One)

theorem FamRep12.word {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12} (h : FamRep12 gs xs)
    (w : List ℤ) : PrRep12 (wordProd gs w) (pr12Word xs w) := by
  unfold wordProd pr12Word
  suffices ∀ (acc : Pr12) (g : GL (Fin 12) (ZMod 2)), PrRep12 g acc →
      PrRep12 (g * (w.map fun l => if 0 < l then gs (l.toNat - 1)
          else (gs ((-l).toNat - 1))⁻¹).prod)
        (w.foldl (fun acc l => pr12Mul acc (pr12Letter xs l)) acc) by
    simpa using this pr12One 1 PrRep12.one
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    refine ih _ _ (hg.mul ?_)
    unfold pr12Letter
    split_ifs
    · exact h _
    · exact (h _).inv

theorem FamRep12.eq_one {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12} (h : FamRep12 gs xs)
    {i : ℕ} (hi : xs.size ≤ i) : gs i = 1 := by
  have := h i
  rw [Array.getElem?_eq_none_iff.2 hi, Option.getD_none] at this
  exact this.eq_one

@[expose] def levelGensGL12 (gs : ℕ → GL (Fin 12) (ZMod 2)) :
    List (List (List ℤ)) → List (ℕ → GL (Fin 12) (ZMod 2))
  | [] => [gs]
  | ws :: rest => gs :: levelGensGL12 (fun i => wordProd gs (ws.getD i [])) rest

theorem levelGens12_length (xs : Array Pr12) (ws : List (List (List ℤ))) :
    (levelGens12 xs ws).length = ws.length + 1 := by
  induction ws generalizing xs with
  | nil => rfl
  | cons w ws ih => simp [levelGens12, ih]

theorem famRep12_levelGens {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12}
    (h : FamRep12 gs xs) (ws : List (List (List ℤ))) (j : ℕ) :
    FamRep12 ((levelGensGL12 gs ws).getD j fun _ => 1) ((levelGens12 xs ws).getD j #[]) := by
  induction ws generalizing gs xs j with
  | nil =>
    cases j with
    | zero => exact h
    | succ j =>
      intro i
      simp only [levelGensGL12, levelGens12, List.getD_eq_getElem?_getD,
        List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none]
      exact PrRep12.one
  | cons w ws ih =>
    cases j with
    | zero => exact h
    | succ j =>
      simp only [levelGensGL12, levelGens12, List.getD_cons_succ]
      apply ih
      intro i
      show PrRep12 (wordProd gs (w.getD i [])) _
      rw [Array.getElem?_map, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      cases w[i]? with
      | none => simpa [wordProd] using PrRep12.one
      | some wi => exact h.word wi

theorem levelGensGL12_succ (gs : ℕ → GL (Fin 12) (ZMod 2)) (ws : List (List (List ℤ)))
    {j : ℕ} (hj : j < ws.length) (i : ℕ) :
    ((levelGensGL12 gs ws).getD (j + 1) fun _ => 1) i =
      wordProd ((levelGensGL12 gs ws).getD j fun _ => 1) ((ws.getD j []).getD i []) := by
  induction ws generalizing gs j with
  | nil => simp at hj
  | cons w ws ih =>
    cases j with
    | zero => cases ws <;> simp [levelGensGL12]
    | succ j =>
      simp only [levelGensGL12, List.getD_cons_succ]
      exact ih _ (by simpa using hj)

theorem mkLevels12_size {xs : Array Pr12} {bs : List ℕ} {ws : List (List (List ℤ))}
    (hlen : bs.length = ws.length + 1) : (mkLevels12 xs bs ws).size = ws.length + 1 := by
  simp [mkLevels12, List.length_zip, levelGens12_length, hlen]

theorem mkLevels12_getElem! {xs : Array Pr12} {bs : List ℕ} {ws : List (List (List ℤ))}
    (hlen : bs.length = ws.length + 1) {j : ℕ} (hj : j < ws.length + 1) :
    (mkLevels12 xs bs ws)[j]! = mkLvl12 ((levelGens12 xs ws).getD j #[]) (bs.getD j 0) := by
  have hj1 : j < (levelGens12 xs ws).length := by rw [levelGens12_length]; exact hj
  have hj2 : j < bs.length := by rw [hlen]; exact hj
  rw [getElem!_pos _ j (by rw [mkLevels12_size hlen]; exact hj)]
  simp only [mkLevels12, List.getElem_toArray, Array.getElem_map, List.getElem_zip]
  rw [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2]

theorem ptOf12_spec {sg : ℕ → GL (Fin 12) (ZMod 2)} {gens : Array Pr12} (h : FamRep12 sg gens)
    (b : ℕ) {p : List ℕ} (hp : ∀ g ∈ p, g < gens.size) :
    toVecD 12 (ptOf12 (gens.map fun x => transposeRows 12 x.1) b p) =
      ofColV12 ((p.map sg).prod • toColV12 (toVecD 12 b)) := by
  induction p with
  | nil => simp only [ptOf12, List.foldr_nil, List.map_nil, List.prod_nil, one_smul]; rfl
  | cons g p ih =>
    have hg : g < gens.size := hp g (List.mem_cons_self ..)
    have ih' := ih fun g' hg' => hp g' (List.mem_cons_of_mem _ hg')
    simp only [ptOf12, List.foldr_cons] at ih' ⊢
    rw [show (gens.map fun x => transposeRows 12 x.1)[g]! =
        transposeRows 12 (gens[g]?.getD pr12One).1 by
      rw [getElem!_pos _ g (by simpa using hg), Array.getElem_map,
        Array.getElem?_eq_getElem hg, Option.getD_some]]
    rw [← rowsMatrix_mulVec, ih', (h g).1, List.map_cons, List.prod_cons, mul_smul]
    rfl

theorem prod_map_toList12 {α : Type*} [Inhabited α] (L : Array α) (f : α → ℕ) :
    (L.toList.map f).prod = ∏ j ∈ Finset.range L.size, f L[j]! := by
  rw [Finset.prod_range fun j => f L[j]!, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_ofFn]
    rw [getElem!_pos L n (by simpa using h1)]

theorem prod_le_card_of_witnessOK {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12}
    {bs : List ℕ} {ws : List (List (List ℤ))} (hxs : FamRep12 gs xs)
    (hlen : bs.length = ws.length + 1) (h : witnessOK (mkLevels12 xs bs ws) = true) :
    (orbitSizes12 (mkLevels12 xs bs ws)).prod ≤
      Nat.card (Subgroup.closure {g | ∃ i < xs.size, gs i = g}) := by
  set L := mkLevels12 xs bs ws with hL
  have hm : L.size = ws.length + 1 := mkLevels12_size hlen
  have hrep : ∀ j, FamRep12 ((levelGensGL12 gs ws).getD j fun _ => 1)
      ((levelGens12 xs ws).getD j #[]) := famRep12_levelGens hxs ws
  have hparts : ∀ j < ws.length + 1, 0 < L[j]!.paths.size ∧ L[j]!.paths[0]! = [] ∧
      (∀ (k : ℕ) (hk : k < L[j]!.paths.size), ∀ g ∈ L[j]!.paths[k], g < L[j]!.gens.size) ∧
      (∀ (k : ℕ) (hk : k < L[j]!.pts.size), L[j]!.pts[k] < 4096) ∧
      (∀ k < L[j]!.pts.size, ∀ k' < k, L[j]!.pts[k]! ≠ L[j]!.pts[k']!) ∧
      (L.size ≤ j + 1 ∨ ∀ g < L[j + 1]!.gens.size,
        vecMulN 12 L[j + 1]!.cols[g]! L[j]!.base = L[j]!.base) := by
    intro j hj
    have := List.all_eq_true.1 h j (List.mem_range.2 (by rw [hm]; exact hj))
    simp only [witnessLevelOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
      Array.all_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at this
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hspec : ∀ j < ws.length + 1, L[j]!.gens = (levelGens12 xs ws).getD j #[] ∧
      L[j]!.cols = ((levelGens12 xs ws).getD j #[]).map (fun x => transposeRows 12 x.1) ∧
      L[j]!.pts = L[j]!.paths.map
        (ptOf12 (((levelGens12 xs ws).getD j #[]).map (fun x => transposeRows 12 x.1))
          L[j]!.base) := by
    intro j hj
    rw [mkLevels12_getElem! hlen hj]
    exact ⟨rfl, rfl, rfl⟩
  let sgl : ℕ → ℕ → GL (Fin 12) (ZMod 2) := fun j => (levelGensGL12 gs ws).getD j fun _ => 1
  let gens : ℕ → Set (GL (Fin 12) (ZMod 2)) := fun j => {g | ∃ i < L[j]!.gens.size, sgl j i = g}
  let tr : ℕ → ℕ → GL (Fin 12) (ZMod 2) := fun j k => ((L[j]!.paths[k]!).map (sgl j)).prod
  let base : ℕ → ColV12 := fun j => toColV12 (toVecD 12 L[j]!.base)
  have hpathv : ∀ j < ws.length + 1, ∀ k : ℕ, ∀ g : ℕ, g ∈ L[j]!.paths[k]! →
      g < L[j]!.gens.size := by
    intro j hj k g hg
    by_cases hk : k < L[j]!.paths.size
    · rw [getElem!_pos _ k hk] at hg
      exact (hparts j hj).2.2.1 k hk g hg
    · rw [getElem!_neg _ k hk] at hg
      change g ∈ ([] : List ℕ) at hg
      simp at hg
  have hgsz : ∀ j < ws.length + 1, L[j]!.gens.size = ((levelGens12 xs ws).getD j #[]).size :=
    fun j hj => by rw [(hspec j hj).1]
  have hgen_mem : ∀ j < ws.length + 1, ∀ i, sgl j i ∈ Subgroup.closure (gens j) := by
    intro j hj i
    by_cases hi : i < L[j]!.gens.size
    · exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    · show ((levelGensGL12 gs ws).getD j fun _ => 1) i ∈ _
      rw [(hrep j).eq_one (by rw [← hgsz j hj]; omega)]
      exact Subgroup.one_mem _
  have key := prod_le_card_closure (ws.length + 1) base gens (fun j => L[j]!.pts.size) tr
    (fun j hj => by
      rintro _ ⟨i, hi, rfl⟩
      by_cases hj1 : j + 1 < ws.length + 1
      · show sgl (j + 1) i ∈ _
        rw [show sgl (j + 1) i = _ from levelGensGL12_succ gs ws (by omega) i]
        exact wordProd_mem _ (fun m => hgen_mem j hj m) _
      · rw [getElem!_neg _ (j + 1) (by rw [hm]; omega)] at hi
        exact absurd hi (by simp [default]))
    (fun j hj => by
      rintro _ ⟨i, hi, rfl⟩
      have hj1 : j + 1 < ws.length + 1 := by
        by_contra hc
        rw [getElem!_neg _ (j + 1) (by rw [hm]; omega)] at hi
        exact absurd hi (by simp [default])
      have hfx := (hparts j hj).2.2.2.2.2.resolve_left (by omega) i hi
      have hiG : i < ((levelGens12 xs ws).getD (j + 1) #[]).size := by
        rw [← hgsz (j + 1) hj1]; exact hi
      rw [(hspec (j + 1) hj1).2.1, getElem!_pos _ i (by rw [Array.size_map]; exact hiG),
        Array.getElem_map] at hfx
      have hv := congrArg (toVecD 12) hfx
      rw [← rowsMatrix_mulVec,
        show ((levelGens12 xs ws).getD (j + 1) #[])[i] =
          ((levelGens12 xs ws).getD (j + 1) #[])[i]?.getD pr12One
          by rw [Array.getElem?_eq_getElem hiG, Option.getD_some], (hrep (j + 1) i).1] at hv
      exact congrArg toColV12 hv)
    (fun j hj k _ => by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact hgen_mem j hj g)
    (fun j hj k hk k' hk' e => by
      have hk1 : k < L[j]!.paths.size := by rw [(hspec j hj).2.2, Array.size_map] at hk; exact hk
      have hk1' : k' < L[j]!.paths.size := by
        rw [(hspec j hj).2.2, Array.size_map] at hk'; exact hk'
      have hpt : ∀ k (hk : k < L[j]!.paths.size), toVecD 12 L[j]!.pts[k]! =
          ofColV12 (tr j k • base j) := by
        intro k hk
        rw [(hspec j hj).2.2, getElem!_pos _ k (by rw [Array.size_map]; exact hk),
          Array.getElem_map, ptOf12_spec (hrep j) _ (fun g hg => by
            rw [← hgsz j hj]; exact hpathv j hj k g (by rwa [getElem!_pos _ k hk])),
          ← getElem!_pos L[j]!.paths k hk]
      have hv : toVecD 12 L[j]!.pts[k]! = toVecD 12 L[j]!.pts[k']! := by
        rw [hpt k hk1, hpt k' hk1', e]
      have hlt : ∀ i < L[j]!.pts.size, L[j]!.pts[i]! < 2 ^ 12 := fun i hi => by
        rw [getElem!_pos _ i hi]; exact (hparts j hj).2.2.2.1 i hi
      have heq := toVecD_injective (hlt k hk) (hlt k' hk') hv
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt' | hlt'
      · exact (hparts j hj).2.2.2.2.1 k' hk' k hlt' heq.symm
      · exact (hparts j hj).2.2.2.2.1 k hk k' hlt' heq)
  have hg0 : gens 0 = {g | ∃ i < xs.size, gs i = g} := by
    have h1 : L[0]!.gens = xs := by
      rw [(hspec 0 (Nat.succ_pos _)).1]
      cases ws <;> rfl
    have h2 : sgl 0 = gs := by
      show (levelGensGL12 gs ws).getD 0 _ = gs
      cases ws <;> rfl
    ext g
    show (∃ i < L[0]!.gens.size, sgl 0 i = g) ↔ _
    rw [h1, h2]
    rfl
  rw [← hg0]
  refine le_trans (le_of_eq ?_) key
  rw [orbitSizes12, prod_map_toList12, hm]

end CFSG.Quasithin.H13.J4
