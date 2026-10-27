module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.DichotomyLetters
public import Certificates.Certificate272039

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal.J2Model

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th CFSG.Sporadic.J2
open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition (j3WordsRest)

noncomputable def gL (l : ℤ) : J :=
  if l = 1 then a else if l = -1 then a⁻¹ else if l = 2 then b else b⁻¹

noncomputable def uN2 (k : ℕ) : J := wordG gL (uWord2 k)

noncomputable def uJ2 : Fin 7 → J := fun i => uN2 i

noncomputable def letG (z : ℤ) : J :=
  if 0 < z then uN2 (z - 1).toNat else (uN2 (-z - 1).toNat)⁻¹

theorem uWord2_letters : ∀ k, ∀ l ∈ uWord2 k, l = 1 ∨ l = 2 := by
  intro k
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide +kernel | simp [uWord2]

theorem encodeWord_letters' (r : List (Fin 7 × Bool)) :
    ∀ l ∈ encodeWord r, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7 := by
  intro l hl
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hl
  obtain ⟨i, s⟩ := x
  have := i.isLt
  cases s <;> simp <;> omega

theorem wa7_letters : ∀ l ∈ wa7, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7 := by decide +kernel

theorem wb7_letters : ∀ l ∈ wb7, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7 := by decide +kernel

section Check

theorem rep_gen {z : ℤ} (hz : z = 1 ∨ z = 2) : Rep 315 (CFSG.Sporadic.J1.Native.genTables orb z) (gL z) := by
  rcases hz with rfl | rfl
  · simpa [CFSG.Sporadic.J1.Native.genTables, gL] using rep_alpha
  · simpa [CFSG.Sporadic.J1.Native.genTables, gL] using rep_beta

theorem hn : (315 : ℕ) < 2 ^ 32 := by norm_num

theorem rep_uN2 (k : ℕ) :
    Rep 315 (uTab2 315 (CFSG.Sporadic.J1.Native.genTables orb) k) (uN2 k) :=
  Rep.wordT hn (uWord2 k) fun l hl => rep_gen (uWord2_letters k l hl)

theorem ap_idT {i : ℕ} (hi : i < 315) : ap (idT 315) i = i := by
  have := Rep.idT hn (G := J) i hi
  rwa [idx_one] at this

theorem eq_one_of_rep_id {g : J} (h : Rep 315 (idT 315) g) : g = 1 := by
  apply sep
  intro t ht
  have hq := chainQ_lt (t := t) (by rw [chainQ_size] at ht; exact ht)
  have h1 := h _ hq
  rw [ap_idT hq] at h1
  exact h1.symm

theorem eq_of_rep {T : Table} {g h : J} (hg : Rep 315 T g) (hh : Rep 315 T h) : g = h := by
  have : g⁻¹ * h = 1 := by
    apply sep
    intro t ht
    have hq := chainQ_lt (t := t) (by rw [chainQ_size] at ht; exact ht)
    have e : idx 315 g Native.chainQ[t]! = idx 315 h Native.chainQ[t]! :=
      (hg _ hq).symm.trans (hh _ hq)
    rw [idx_mul, ← e, idx_inv_idx]
  exact inv_mul_eq_one.mp this

theorem ne_of_rep_differ {T U : Table} {g h : J} (hg : Rep 315 T g) (hh : Rep 315 U h)
    (hd : differSome 315 T U = true) : g ≠ h := by
  rintro rfl
  unfold differSome at hd
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hd
  obtain ⟨i, hi, hne⟩ := hd
  exact hne ((hg i hi).trans (hh i hi).symm)

theorem ne_one_of_moves {T : Table} {g : J} (hg : Rep 315 T g) (hd : movesSome 315 T = true) :
    g ≠ 1 := by
  rintro rfl
  unfold movesSome at hd
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hd
  obtain ⟨i, hi, hne⟩ := hd
  exact hne ((hg i hi).trans (idx_one i))

end Check

section Lift

variable {X : Type*} [Group X]

theorem lift_mk_prod (g : Fin 7 → X) (r : List (Fin 7 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk r) = (r.map fun x => if x.2 then g x.1 else (g x.1)⁻¹).prod :=
  CFSG.Quasithin.Kleidman.ThreeLocal.lift_mk_prod g r

end Lift

theorem lift_letter (i : Fin 7) (s : Bool) :
    FreeGroup.lift uJ2 (FreeGroup.mk [(i, s)]) =
      letG (if s then (i.val : ℤ) + 1 else -((i.val : ℤ) + 1)) := by
  cases s
  · simp [letG, uJ2]
  · simp [letG, uJ2]

theorem lift_eq (r : List (Fin 7 × Bool)) :
    FreeGroup.lift uJ2 (FreeGroup.mk r) = wordG letG (encodeWord r) := by
  induction r with
  | nil => simp [wordG, encodeWord]
  | cons x r ih =>
    obtain ⟨i, s⟩ := x
    have e1 : (i, s) :: r = [(i, s)] ++ r := rfl
    rw [e1, ← FreeGroup.mul_mk, map_mul, ih]
    have e2 : wordG letG (encodeWord ([(i, s)] ++ r)) =
        letG (if s then (i.val : ℤ) + 1 else -((i.val : ℤ) + 1)) * wordG letG (encodeWord r) := by
      simp only [wordG, encodeWord, List.cons_append, List.nil_append, List.map_cons,
        List.prod_cons]
    rw [e2, lift_letter]

section Parts

theorem modelCheckAt_parts (gen : ℤ → Table) (hc : modelCheckAt 315 gen = true) :
    (∀ k < 7, invOK 315 (uTab2 315 gen k) (invT 315 (uTab2 315 gen k)) = true) ∧
    (∀ r ∈ j2Rels, wordT 315 (letTab (modelTu 315 gen) (modelTui 315 gen)) (encodeWord r) = idT 315) ∧
    wordT 315 (letTab (modelTu 315 gen) (modelTui 315 gen)) wa7 = gen 1 ∧
    wordT 315 (letTab (modelTu 315 gen) (modelTui 315 gen)) wb7 = gen 2 ∧
    (let L := letTab (modelTu 315 gen) (modelTui 315 gen)
     let tf := wordT 315 L (encodeWord fWord)
     let tt := wordT 315 L (encodeWord tauWord)
     let tt' := wordT 315 L (encodeWord tau2Word)
     compT 315 tt tt = idT 315 ∧ compT 315 tt' tt' = idT 315 ∧ compT 315 tt tt' = compT 315 tt' tt ∧
     movesSome 315 tt = true ∧ movesSome 315 tt' = true ∧ differSome 315 tt tt' = true ∧
     powT 315 5 tf = idT 315 ∧ movesSome 315 tf = true ∧
     compT 315 tf tt = compT 315 tt tf ∧ compT 315 tf tt' = compT 315 tt' tf) := by
  unfold modelCheckAt at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := hc
  refine ⟨fun k hk => ?_, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have := h1 k hk
  simpa [modelTu, modelTui, hk] using this

end Parts

section Main

noncomputable abbrev gen : ℤ → Table := CFSG.Sporadic.J1.Native.genTables orb

theorem check_holds : modelCheckAt 315 gen = true := by
  have h := Certificates.certificate272039
  unfold j2ModelCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem modelTu_get {k : ℕ} (hk : k < 7) : (modelTu 315 gen)[k]! = uTab2 315 gen k := by
  simp [modelTu, hk]

theorem modelTui_get {k : ℕ} (hk : k < 7) :
    (modelTui 315 gen)[k]! = invT 315 (uTab2 315 gen k) := by
  simp [modelTui, modelTu, hk]

theorem rep_letTab {z : ℤ} (hz : 1 ≤ z.natAbs ∧ z.natAbs ≤ 7) :
    Rep 315 (letTab (modelTu 315 gen) (modelTui 315 gen) z) (letG z) := by
  obtain ⟨hinv, -⟩ := modelCheckAt_parts gen check_holds
  unfold letTab letG
  split_ifs with h
  · have hk : (z - 1).toNat < 7 := by omega
    rw [modelTu_get hk]
    exact rep_uN2 _
  · have hk : (-z - 1).toNat < 7 := by omega
    rw [modelTui_get hk]
    exact Rep.inv_of_invOK (rep_uN2 _) (hinv _ hk)

theorem rep_word {w : List ℤ} (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7) :
    Rep 315 (wordT 315 (letTab (modelTu 315 gen) (modelTui 315 gen)) w) (wordG letG w) :=
  Rep.wordT hn w fun l hl => rep_letTab (hw l hl)

theorem rep_lift (r : List (Fin 7 × Bool)) :
    Rep 315 (wordT 315 (letTab (modelTu 315 gen) (modelTui 315 gen)) (encodeWord r))
      (FreeGroup.lift uJ2 (FreeGroup.mk r)) := by
  rw [lift_eq]
  exact rep_word (encodeWord_letters' r)

theorem uJ2_rels : ∀ r ∈ j2Rels, FreeGroup.lift uJ2 (FreeGroup.mk r) = 1 := by
  intro r hr
  obtain ⟨-, h2, -⟩ := modelCheckAt_parts gen check_holds
  have h := rep_lift r
  rw [h2 r hr] at h
  exact eq_one_of_rep_id h

theorem letG_mem {z : ℤ} (hz : 1 ≤ z.natAbs ∧ z.natAbs ≤ 7) :
    letG z ∈ Subgroup.closure (Set.range uJ2) := by
  unfold letG
  split_ifs with h
  · have hk : (z - 1).toNat < 7 := by omega
    exact Subgroup.subset_closure ⟨⟨(z - 1).toNat, hk⟩, rfl⟩
  · have hk : (-z - 1).toNat < 7 := by omega
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨(-z - 1).toNat, hk⟩, rfl⟩)

theorem wordG_mem {w : List ℤ} (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7) :
    wordG letG w ∈ Subgroup.closure (Set.range uJ2) := by
  unfold wordG
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  exact letG_mem (hw l hl)

theorem closure_uJ2 : Subgroup.closure (Set.range uJ2) = ⊤ := by
  obtain ⟨-, -, h3, h4, -⟩ := modelCheckAt_parts gen check_holds
  have ha : a = wordG letG wa7 := by
    refine eq_of_rep ?_ (rep_word wa7_letters)
    rw [h3]
    exact rep_gen (Or.inl rfl)
  have hb : b = wordG letG wb7 := by
    refine eq_of_rep ?_ (rep_word wb7_letters)
    rw [h4]
    exact rep_gen (Or.inr rfl)
  have haM : a ∈ Subgroup.closure (Set.range uJ2) := by
    rw [ha]; exact wordG_mem wa7_letters
  have hbM : b ∈ Subgroup.closure (Set.range uJ2) := by
    rw [hb]; exact wordG_mem wb7_letters
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact haM
  · exact hbM

noncomputable def fJ : J := FreeGroup.lift uJ2 (FreeGroup.mk fWord)
noncomputable def tauJ : J := FreeGroup.lift uJ2 (FreeGroup.mk tauWord)
noncomputable def tau2J : J := FreeGroup.lift uJ2 (FreeGroup.mk tau2Word)

theorem j2_five_klein_J :
    tauJ * tauJ = 1 ∧ tau2J * tau2J = 1 ∧ tauJ * tau2J = tau2J * tauJ ∧ tauJ ≠ 1 ∧ tau2J ≠ 1 ∧
      tauJ ≠ tau2J ∧ fJ ^ 5 = 1 ∧ fJ ≠ 1 ∧ fJ * tauJ = tauJ * fJ ∧ fJ * tau2J = tau2J * fJ := by
  obtain ⟨-, -, -, -, hfacts⟩ := modelCheckAt_parts gen check_holds
  obtain ⟨c1, c2, c3, m1, m2, d12, p5, mf, k1, k2⟩ := hfacts
  have rF := rep_lift fWord
  have rT := rep_lift tauWord
  have rT2 := rep_lift tau2Word
  have e1 := Rep.compT rT rT
  have e2 := Rep.compT rT2 rT2
  have e3 := Rep.compT rT rT2
  have e3' := Rep.compT rT2 rT
  have e4 := Rep.powT hn rF 5
  have e5 := Rep.compT rF rT
  have e5' := Rep.compT rT rF
  have e6 := Rep.compT rF rT2
  have e6' := Rep.compT rT2 rF
  rw [c1] at e1
  rw [c2] at e2
  rw [c3] at e3
  rw [p5] at e4
  rw [k1] at e5
  rw [k2] at e6
  exact ⟨eq_one_of_rep_id e1, eq_one_of_rep_id e2, eq_of_rep e3 e3', ne_one_of_moves rT m1,
    ne_one_of_moves rT2 m2, ne_of_rep_differ rT rT2 d12, eq_one_of_rep_id e4,
    ne_one_of_moves rF mf, eq_of_rep e5 e5', eq_of_rep e6 e6'⟩

noncomputable def j2Tuple : Fin 7 → CFSG.Blueprint.NativeSporadic.J2 := fun i =>
  nativeEquiv.symm (uJ2 i)

theorem lift_j2Tuple (r : List (Fin 7 × Bool)) :
    FreeGroup.lift j2Tuple (FreeGroup.mk r) = nativeEquiv.symm (FreeGroup.lift uJ2 (FreeGroup.mk r)) := by
  rw [lift_mk_prod, lift_mk_prod, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  obtain ⟨i, s⟩ := x
  cases s <;> simp [j2Tuple]

theorem wRelator_four_zero : wRelator 4 0 = wFour := by
  simp [wRelator, powWord, yInvPow, wWord, wFour, List.replicate]

theorem j2Tuple_rels : ∀ r ∈ j3WordsRest ++ [wRelator 4 0],
    FreeGroup.lift j2Tuple (FreeGroup.mk r) = 1 := by
  intro r hr
  rw [wRelator_four_zero] at hr
  rw [lift_j2Tuple, uJ2_rels r hr, map_one]

theorem closure_j2Tuple : Subgroup.closure (Set.range j2Tuple) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : nativeEquiv g ∈ Subgroup.closure (Set.range uJ2) := by
    rw [closure_uJ2]; exact Subgroup.mem_top _
  have key : ∀ x ∈ Subgroup.closure (Set.range uJ2),
      nativeEquiv.symm x ∈ Subgroup.closure (Set.range j2Tuple) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i, rfl⟩
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  simpa using key _ hg

noncomputable def j2F : CFSG.Blueprint.NativeSporadic.J2 := FreeGroup.lift j2Tuple (FreeGroup.mk fWord)
noncomputable def j2Tau : CFSG.Blueprint.NativeSporadic.J2 := FreeGroup.lift j2Tuple (FreeGroup.mk tauWord)
noncomputable def j2Tau2 : CFSG.Blueprint.NativeSporadic.J2 := FreeGroup.lift j2Tuple (FreeGroup.mk tau2Word)

theorem j2F_eq : j2F = FreeGroup.lift j2Tuple (FreeGroup.mk fWord) := by rw [j2F]

theorem j2Tau_eq : j2Tau = FreeGroup.lift j2Tuple (FreeGroup.mk tauWord) := by rw [j2Tau]

theorem j2Tau2_eq : j2Tau2 = FreeGroup.lift j2Tuple (FreeGroup.mk tau2Word) := by
  rw [j2Tau2]

theorem j2_five_klein :
    j2Tau * j2Tau = 1 ∧ j2Tau2 * j2Tau2 = 1 ∧ j2Tau * j2Tau2 = j2Tau2 * j2Tau ∧ j2Tau ≠ 1 ∧
      j2Tau2 ≠ 1 ∧ j2Tau ≠ j2Tau2 ∧ j2F ^ 5 = 1 ∧ j2F ≠ 1 ∧ j2F * j2Tau = j2Tau * j2F ∧
      j2F * j2Tau2 = j2Tau2 * j2F := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := j2_five_klein_J
  have e : ∀ x y : J, nativeEquiv.symm x = nativeEquiv.symm y ↔ x = y := fun x y =>
    nativeEquiv.symm.injective.eq_iff
  have hF : j2F = nativeEquiv.symm fJ := lift_j2Tuple _
  have hT : j2Tau = nativeEquiv.symm tauJ := lift_j2Tuple _
  have hT2 : j2Tau2 = nativeEquiv.symm tau2J := lift_j2Tuple _
  rw [hF, hT, hT2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h1, map_one]
  · rw [← map_mul, h2, map_one]
  · rw [← map_mul, ← map_mul, h3]
  · intro h; apply h4; rw [← map_one nativeEquiv.symm] at h; exact nativeEquiv.symm.injective h
  · intro h; apply h5; rw [← map_one nativeEquiv.symm] at h; exact nativeEquiv.symm.injective h
  · intro h; exact h6 (nativeEquiv.symm.injective h)
  · rw [← map_pow, h7, map_one]
  · intro h; apply h8; rw [← map_one nativeEquiv.symm] at h; exact nativeEquiv.symm.injective h
  · rw [← map_mul, ← map_mul, h9]
  · rw [← map_mul, ← map_mul, h10]

end Main

end CFSG.Quasithin.Kleidman.ThreeLocal.J2Model
