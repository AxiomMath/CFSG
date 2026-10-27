module

public import CFSG.Quasithin.Recognition.J2RecDefs
public import CFSG.Timmesfeld.Moufang.J2Mat

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge.J2 (wfM mulL idL toM unitL lwordL wfM_idL toM_idL
  val_wordProd_of_lwordL nativeEquiv seedGroup)
open CFSG.Timmesfeld.Moufang.J2 (genL)

private theorem genL_wf_fin : ∀ i : Fin 7, wfM (genL i.val) = true := by decide +kernel

private theorem genL_sq_fin : ∀ i : Fin 7, mulL (genL i.val) (genL i.val) = idL := by
  decide +kernel

private theorem mulL_idL_idL' : mulL idL idL = idL := by decide +kernel

theorem genL_wf_all (i : ℕ) : wfM (genL i) = true := by
  by_cases hi : i < 7
  · exact genL_wf_fin ⟨i, hi⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 7 := ⟨i - 7, by omega⟩
    exact wfM_idL

theorem genL_sq_all (i : ℕ) : mulL (genL i) (genL i) = idL := by
  by_cases hi : i < 7
  · exact genL_sq_fin ⟨i, hi⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 7 := ⟨i - 7, by omega⟩
    exact mulL_idL_idL'

@[expose] noncomputable def j2Gen (i : ℕ) : GL (Fin 14) (ZMod 5) :=
  unitL (genL i) (genL i) (genL_wf_all i) (genL_wf_all i) (genL_sq_all i) (genL_sq_all i)

theorem j2Gen_val (i : ℕ) : (j2Gen i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (genL i) := rfl

theorem j2Gen_inv_val (i : ℕ) :
    (((j2Gen i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (genL i) := rfl

@[expose] def lineGen7 {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) (i : ℕ) : H :=
  if i = 0 then d else if i = 1 then c else if h : i - 2 < 5 then x ⟨i - 2, h⟩ else 1

theorem lineGen7_zero {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) : lineGen7 d c x 0 = d := by
  simp [lineGen7]

theorem lineGen7_two_add {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) (j : Fin 5) :
    lineGen7 d c x (j.val + 2) = x j := by
  simp [lineGen7]

theorem lineGen7_mem {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) (K : Subgroup H)
    (hd : d ∈ K) (hc : c ∈ K) (hx : ∀ i, x i ∈ K) (i : ℕ) : lineGen7 d c x i ∈ K := by
  unfold lineGen7
  split_ifs
  · exact hd
  · exact hc
  · exact hx _
  · exact K.one_mem

theorem lineGen7_mem_closure {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) (i : ℕ) :
    lineGen7 d c x i ∈ Subgroup.closure (insert d (insert c (Set.range x))) :=
  lineGen7_mem d c x _ (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (fun i => Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_range_self i)))) i

@[expose] def posWord (u : List ℕ) : List (ℕ × Bool) := u.map fun i => (i, true)

theorem wordProd_posWord {H : Type*} [Group H] (g : ℕ → H) (u : List ℕ) :
    CFSG.Sporadic.Bridge.wordProd g (posWord u) = (u.map g).prod := by
  simp [CFSG.Sporadic.Bridge.wordProd, posWord, List.map_map, Function.comp_def]

theorem j2Gen_matrix_prod (u : List ℕ) :
    (((u.map j2Gen).prod : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (lwordL genL genL (posWord u) idL) := by
  rw [← wordProd_posWord]
  exact val_wordProd_of_lwordL genL_wf_all genL_wf_all j2Gen_val j2Gen_inv_val rfl

theorem j2Gen_prod_eq {u v : List ℕ}
    (hm : lwordL genL genL (posWord u) idL = lwordL genL genL (posWord v) idL) :
    (u.map j2Gen).prod = (v.map j2Gen).prod := by
  apply Units.ext
  rw [j2Gen_matrix_prod, j2Gen_matrix_prod, hm]

theorem j2Gen_prod_ne_one {u : List ℕ} (hm : toM (lwordL genL genL (posWord u) idL) ≠ 1) :
    (u.map j2Gen).prod ≠ 1 := by
  intro h
  apply hm
  rw [← j2Gen_matrix_prod, h]
  rfl

private theorem k_d_sq : lwordL genL genL (posWord [0, 0]) idL = idL := by decide +kernel

private theorem k_c_sq : lwordL genL genL (posWord [1, 1]) idL = idL := by decide +kernel

private theorem k_x_sq : ∀ i : Fin 5, lwordL genL genL (posWord [i.val + 2, i.val + 2]) idL =
    idL := by decide +kernel

private theorem k_d_comm : ∀ i : Fin 5, lwordL genL genL (posWord [0, i.val + 2]) idL =
    lwordL genL genL (posWord [i.val + 2, 0]) idL := by decide +kernel

private theorem k_sq_eq : ∀ i j : Fin 5, i ≠ j →
    lwordL genL genL (posWord [i.val + 2, j.val + 2, i.val + 2, j.val + 2]) idL =
      lwordL genL genL (posWord [0]) idL := by decide +kernel

private theorem k_prod : lwordL genL genL (posWord [2, 3, 4, 5, 6]) idL = idL := by
  decide +kernel

private theorem k_dc_pow : lwordL genL genL (posWord [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) idL =
    idL := by decide +kernel

private theorem k_dc_ne : toM (lwordL genL genL (posWord [0, 1]) idL) ≠ 1 := by decide +kernel

private theorem k_cx_pow : ∀ i : Fin 5,
    lwordL genL genL (posWord [1, i.val + 2, 1, i.val + 2, 1, i.val + 2]) idL = idL := by
  decide +kernel

private theorem k_cdx_pow : ∀ i : Fin 5,
    lwordL genL genL (posWord [1, 0, i.val + 2, 1, 0, i.val + 2, 1, 0, i.val + 2, 1, 0, i.val + 2,
      1, 0, i.val + 2]) idL = idL := by
  decide +kernel

theorem j2Gen_fiveLines : J2FiveLines (j2Gen 0) (fun i : Fin 5 => j2Gen (i.val + 2)) where
  d_sq := by
    simpa using j2Gen_prod_eq (u := [0, 0]) (v := []) (by rw [k_d_sq]; rfl)
  x_sq i := by
    simpa using j2Gen_prod_eq (u := [i.val + 2, i.val + 2]) (v := []) (by rw [k_x_sq i]; rfl)
  d_comm i := by
    have := j2Gen_prod_eq (u := [0, i.val + 2]) (v := [i.val + 2, 0]) (k_d_comm i)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this
  sq_eq i j hij := by
    have := j2Gen_prod_eq (u := [i.val + 2, j.val + 2, i.val + 2, j.val + 2]) (v := [0])
      (k_sq_eq i j hij)
    rw [pow_two]
    simpa [mul_assoc] using this
  prod_eq := by
    have := j2Gen_prod_eq (u := [2, 3, 4, 5, 6]) (v := []) (by rw [k_prod]; rfl)
    simpa [mul_assoc] using this

theorem j2Gen_closingRels :
    J2ClosingRels (j2Gen 0) (j2Gen 1) (fun i : Fin 5 => j2Gen (i.val + 2)) where
  c_sq := by
    simpa using j2Gen_prod_eq (u := [1, 1]) (v := []) (by rw [k_c_sq]; rfl)
  dc_pow := by
    have := j2Gen_prod_eq (u := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) (v := [])
      (by rw [k_dc_pow]; rfl)
    simpa [pow_succ, mul_assoc] using this
  dc_ne := by
    have := j2Gen_prod_ne_one (u := [0, 1]) k_dc_ne
    simpa using this
  cx_pow i := by
    have := j2Gen_prod_eq (u := [1, i.val + 2, 1, i.val + 2, 1, i.val + 2]) (v := [])
      (by rw [k_cx_pow i]; rfl)
    simpa [pow_succ, mul_assoc] using this
  cdx_pow i := by
    have := j2Gen_prod_eq (u := [1, 0, i.val + 2, 1, 0, i.val + 2, 1, 0, i.val + 2, 1, 0, i.val + 2,
      1, 0, i.val + 2]) (v := []) (by rw [k_cdx_pow i]; rfl)
    simpa [pow_succ, mul_assoc] using this

@[expose] def J2LineEndgame : Prop :=
  ∀ (H : Type) [Group H] (d c : H) (x : Fin 5 → H), J2FiveLines d x → J2ClosingRels d c x →
    Nonempty (↥(Subgroup.closure (insert d (insert c (Set.range x)))) ≃*
      CFSG.Blueprint.NativeSporadic.J2)

theorem J2FiveLines.prodMk {G G' : Type*} [Group G] [Group G'] {d : G} {x : Fin 5 → G} {d' : G'}
    {x' : Fin 5 → G'} (h : J2FiveLines d x) (h' : J2FiveLines d' x') :
    J2FiveLines (d, d') (fun i => (x i, x' i)) where
  d_sq := Prod.ext h.d_sq h'.d_sq
  x_sq i := Prod.ext (h.x_sq i) (h'.x_sq i)
  d_comm i := Prod.ext (h.d_comm i).eq (h'.d_comm i).eq
  sq_eq i j hij := Prod.ext (h.sq_eq i j hij) (h'.sq_eq i j hij)
  prod_eq := Prod.ext h.prod_eq h'.prod_eq

theorem J2ClosingRels.prodMk {G G' : Type*} [Group G] [Group G'] {d c : G} {x : Fin 5 → G}
    {d' c' : G'} {x' : Fin 5 → G'} (h : J2ClosingRels d c x) (h' : J2ClosingRels d' c' x') :
    J2ClosingRels (d, d') (c, c') (fun i => (x i, x' i)) where
  c_sq := Prod.ext h.c_sq h'.c_sq
  dc_pow := Prod.ext h.dc_pow h'.dc_pow
  dc_ne := fun h1 => h.dc_ne (congrArg Prod.fst h1)
  cx_pow i := Prod.ext (h.cx_pow i) (h'.cx_pow i)
  cdx_pow i := Prod.ext (h.cdx_pow i) (h'.cdx_pow i)

theorem j2Gen_eq_one_of_seven_le {i : ℕ} (hi : 7 ≤ i) : j2Gen i = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 7 := ⟨i - 7, by omega⟩
  apply Units.ext
  rw [j2Gen_val, show genL (k + 7) = idL from rfl, toM_idL]
  rfl

@[expose] noncomputable def lineGenP {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) (i : ℕ) :
    H × GL (Fin 14) (ZMod 5) := (lineGen7 d c x i, j2Gen i)

@[expose] noncomputable def diagGroup {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) :
    Subgroup (H × GL (Fin 14) (ZMod 5)) :=
  Subgroup.closure (insert (d, j2Gen 0) (insert (c, j2Gen 1)
    (Set.range fun i : Fin 5 => (x i, j2Gen (i.val + 2)))))

theorem lineGenP_mem {H : Type*} [Group H] (d c : H) (x : Fin 5 → H) (i : ℕ) :
    lineGenP d c x i ∈ diagGroup d c x := by
  unfold diagGroup
  by_cases h0 : i = 0
  · subst h0
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  by_cases h1 : i = 1
  · subst h1
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  by_cases h7 : i < 7
  · have hj : i - 2 < 5 := by omega
    refine Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      ⟨⟨i - 2, hj⟩, ?_⟩))
    have : (⟨i - 2, hj⟩ : Fin 5).val + 2 = i := by simp; omega
    simp only [lineGenP, this]
    congr 1
    simp [lineGen7, h0, h1, hj]
  · have h7' : 7 ≤ i := by omega
    have h1' : lineGenP d c x i = 1 := by
      simp only [lineGenP, j2Gen_eq_one_of_seven_le h7']
      have : lineGen7 d c x i = 1 := by simp [lineGen7, h0, h1]; omega
      rw [this]; rfl
    rw [h1']
    exact (diagGroup d c x).one_mem

private theorem injOn_of_card_le {P Q : Type*} [Group P] [Group Q] (D : Subgroup P) (f : P →* Q)
    [Finite D] (hcard : Nat.card D ≤ Nat.card (D.map f)) :
    ∀ a ∈ D, ∀ b ∈ D, f a = f b → a = b := by
  intro a ha b hb hab
  have hbij : Function.Bijective (f.subgroupMap D) :=
    (f.subgroupMap_surjective D).bijective_of_nat_card_le hcard
  have h : f.subgroupMap D ⟨a, ha⟩ = f.subgroupMap D ⟨b, hb⟩ := Subtype.ext hab
  exact congrArg Subtype.val (hbij.1 h)

namespace J2LineEndgame

variable {H : Type} [Group H] {d c : H} {x : Fin 5 → H}

theorem diag_inj (hE : J2LineEndgame) (h1 : J2FiveLines d x) (h2 : J2ClosingRels d c x) :
    (∀ a ∈ diagGroup d c x, ∀ b ∈ diagGroup d c x, a.1 = b.1 → a = b) ∧
      ∀ a ∈ diagGroup d c x, ∀ b ∈ diagGroup d c x, a.2 = b.2 → a = b := by
  obtain ⟨eK⟩ := hE H d c x h1 h2
  obtain ⟨eM⟩ := hE (GL (Fin 14) (ZMod 5)) (j2Gen 0) (j2Gen 1)
    (fun i : Fin 5 => j2Gen (i.val + 2)) j2Gen_fiveLines j2Gen_closingRels
  obtain ⟨eD⟩ := hE (H × GL (Fin 14) (ZMod 5)) (d, j2Gen 0) (c, j2Gen 1)
    (fun i => (x i, j2Gen (i.val + 2))) (h1.prodMk j2Gen_fiveLines) (h2.prodMk j2Gen_closingRels)
  have hfinN : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Finite.of_equiv ↥seedGroup nativeEquiv.symm.toEquiv
  have hfinD : Finite ↥(diagGroup d c x) := Finite.of_equiv _ eD.symm.toEquiv
  have hD : Nat.card ↥(diagGroup d c x) = Nat.card CFSG.Blueprint.NativeSporadic.J2 :=
    Nat.card_congr eD.toEquiv
  have hK : Nat.card ↥(Subgroup.closure (insert d (insert c (Set.range x)))) =
      Nat.card CFSG.Blueprint.NativeSporadic.J2 := Nat.card_congr eK.toEquiv
  have hM : Nat.card ↥(Subgroup.closure (insert (j2Gen 0) (insert (j2Gen 1)
      (Set.range fun i : Fin 5 => j2Gen (i.val + 2))))) =
      Nat.card CFSG.Blueprint.NativeSporadic.J2 := Nat.card_congr eM.toEquiv
  have hmapfst : (diagGroup d c x).map (MonoidHom.fst H (GL (Fin 14) (ZMod 5))) =
      Subgroup.closure (insert d (insert c (Set.range x))) := by
    simp [diagGroup, MonoidHom.map_closure, Set.image_insert_eq, ← Set.range_comp,
      Function.comp_def]
  have hmapsnd : (diagGroup d c x).map (MonoidHom.snd H (GL (Fin 14) (ZMod 5))) =
      Subgroup.closure (insert (j2Gen 0) (insert (j2Gen 1)
        (Set.range fun i : Fin 5 => j2Gen (i.val + 2)))) := by
    simp [diagGroup, MonoidHom.map_closure, Set.image_insert_eq, ← Set.range_comp,
      Function.comp_def]
  refine ⟨injOn_of_card_le _ (MonoidHom.fst H (GL (Fin 14) (ZMod 5))) ?_,
    injOn_of_card_le _ (MonoidHom.snd H (GL (Fin 14) (ZMod 5))) ?_⟩
  · rw [hmapfst, hD, hK]
  · rw [hmapsnd, hD, hM]

theorem eval_eq (hE : J2LineEndgame) (h1 : J2FiveLines d x) (h2 : J2ClosingRels d c x)
    {u v : List ℕ}
    (hm : lwordL genL genL (posWord u) idL = lwordL genL genL (posWord v) idL) :
    (u.map (lineGen7 d c x)).prod = (v.map (lineGen7 d c x)).prod := by
  obtain ⟨-, hsnd⟩ := diag_inj hE h1 h2
  have hprod : ∀ w : List ℕ, (w.map (lineGenP d c x)).prod ∈ diagGroup d c x := fun w =>
    Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      exact lineGenP_mem d c x i
  have hs : ∀ w : List ℕ, ((w.map (lineGenP d c x)).prod).2 = (w.map j2Gen).prod := by
    intro w
    have := map_list_prod (MonoidHom.snd H (GL (Fin 14) (ZMod 5))) (w.map (lineGenP d c x))
    simpa [List.map_map, Function.comp_def, lineGenP] using this
  have hf : ∀ w : List ℕ, ((w.map (lineGenP d c x)).prod).1 = (w.map (lineGen7 d c x)).prod := by
    intro w
    have := map_list_prod (MonoidHom.fst H (GL (Fin 14) (ZMod 5))) (w.map (lineGenP d c x))
    simpa [List.map_map, Function.comp_def, lineGenP] using this
  have h3 := hsnd _ (hprod u) _ (hprod v) (by rw [hs, hs]; exact j2Gen_prod_eq hm)
  rw [← hf, ← hf, h3]

theorem eval_ne_one (hE : J2LineEndgame) (h1 : J2FiveLines d x) (h2 : J2ClosingRels d c x)
    {u : List ℕ} (hm : toM (lwordL genL genL (posWord u) idL) ≠ 1) :
    (u.map (lineGen7 d c x)).prod ≠ 1 := by
  obtain ⟨hfst, -⟩ := diag_inj hE h1 h2
  intro h
  have hprod : (u.map (lineGenP d c x)).prod ∈ diagGroup d c x :=
    Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      exact lineGenP_mem d c x i
  have hs : ((u.map (lineGenP d c x)).prod).2 = (u.map j2Gen).prod := by
    have := map_list_prod (MonoidHom.snd H (GL (Fin 14) (ZMod 5))) (u.map (lineGenP d c x))
    simpa [List.map_map, Function.comp_def, lineGenP] using this
  have hf : ((u.map (lineGenP d c x)).prod).1 = (u.map (lineGen7 d c x)).prod := by
    have := map_list_prod (MonoidHom.fst H (GL (Fin 14) (ZMod 5))) (u.map (lineGenP d c x))
    simpa [List.map_map, Function.comp_def, lineGenP] using this
  have h3 : (u.map (lineGenP d c x)).prod = 1 :=
    hfst _ hprod 1 (diagGroup d c x).one_mem (by rw [hf, h]; rfl)
  apply j2Gen_prod_ne_one hm
  rw [← hs, h3]
  rfl

end J2LineEndgame

end CFSG.Quasithin
