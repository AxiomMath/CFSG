module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoPackedFull

open CFSG.StandardType GGResQTwoPacked

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev PkTabF (n tab : ℕ) (T : Fin (n + 1) → Vector (ZMod 3) (n + 2)) : Prop :=
  ∀ (j : Fin (n + 1)) (l : Fin (n + 2)), l.val < n + 1 →
    (T j).get l = ((pkLane tab (j.val * (n + 1) + l.val) : ℕ) : ZMod 3)

theorem pkF_two : (2 : ZMod 3) = -1 := by decide

theorem pkF_sum_fin_ite {L n : ℕ} (hn : n ≤ L) (g : ℕ → ZMod 3) :
    (∑ l : Fin L, if l.val < n then g l.val else 0) = ∑ i ∈ Finset.range n, g i := by
  have h1 := Fin.sum_univ_eq_sum_range (fun i => if i < n then g i else 0) L
  rw [h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

theorem pkF_ggFDot {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTabF n tab T)
    (j : Fin (n + 1)) {x : ℕ} {z : Vector (ZMod 3) (n + 2)}
    (hz : PkRep (n + 1) x z) : ggFDot (T j) z = ((pkDotR tab (n + 1) j.val x : ℕ) : ZMod 3) := by
  rw [pkDotR_eq, Nat.cast_sum, ← pkF_sum_fin_ite (L := n + 1 + 1) (by omega)]
  unfold ggFDot
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hz l]
  split_ifs with hl
  · rw [hT j l hl, Nat.cast_mul]
  · simp

theorem pkF_ggFDualAt {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    (hT : PkTabF n tab T) (j : Fin (n + 1)) {c : ℕ} {w : Vector (ZMod 3) (n + 1)}
    (hw : PkRep (n + 1) c w) :
    ggFDualAt T w j = ((pkDotC tab (n + 1) j.val c : ℕ) : ZMod 3) := by
  rw [pkDotC_eq, Nat.cast_sum, ← pkF_sum_fin_ite (L := n + 1) le_rfl]
  unfold ggFDualAt
  refine Finset.sum_congr rfl fun o _ => ?_
  have hj' : (j.castSucc : Fin (n + 2)).val < n + 1 := by rw [Fin.coe_castSucc]; exact j.isLt
  rw [hw o]
  split_ifs with ho
  · rw [hT o j.castSucc hj', Fin.coe_castSucc, Nat.cast_mul]
  · simp

theorem pkFRep_refl {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTabF n tab T)
    (j : Fin (n + 1)) {x : ℕ} {z : Vector (ZMod 3) (n + 2)}
    (hz : PkRep (n + 1) x z) : PkRep (n + 1) (pkRefl tab (n + 1) j.val x) (ggFRefl T j z) := by
  intro l
  have hd := pkF_ggFDot hT j hz
  have hlt : (pkLane x j.val + 2 * pkDotR tab (n + 1) j.val x) % 3 < 4 := by omega
  rw [ggFRefl, Vector.get_ofFn, pkRefl_eq, pkLane_pkSet _ _ _ _ hlt]
  by_cases hl : l = j.castSucc
  · have hv : l.val = j.val := by rw [hl, Fin.coe_castSucc]
    have hln : l.val < n + 1 := by omega
    have hzl : z.get l = ((pkLane x l.val : ℕ) : ZMod 3) := (hz l).trans (if_pos hln)
    rw [if_pos hl, if_pos hv, if_pos hln, hzl, hd, ZMod.natCast_mod, hv]
    push_cast
    rw [pkF_two]
    ring
  · have hv : l.val ≠ j.val := fun h => hl (Fin.ext (by rw [h, Fin.coe_castSucc]))
    rw [if_neg hl, if_neg hv, hz l]

theorem pkFRep_drefl {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    (hT : PkTabF n tab T) (j : Fin (n + 1)) {c : ℕ} {w : Vector (ZMod 3) (n + 1)}
    (hw : PkRep (n + 1) c w) :
    PkRep (n + 1) (pkDRefl tab (n + 1) j.val c) (ggFDRefl T j w) := by
  intro o
  have hd := pkF_ggFDualAt hT j hw
  have hlt : (pkLane c j.val + 2 * pkDotC tab (n + 1) j.val c) % 3 < 4 := by omega
  rw [ggFDRefl, Vector.get_ofFn, pkDRefl_eq, pkLane_pkSet _ _ _ _ hlt]
  by_cases ho : o = j
  · have hv : o.val = j.val := by rw [ho]
    have hon : o.val < n + 1 := o.isLt
    have hwo : w.get o = ((pkLane c o.val : ℕ) : ZMod 3) := (hw o).trans (if_pos hon)
    rw [if_pos ho, if_pos hv, if_pos hon, hwo, hd, ZMod.natCast_mod, hv]
    push_cast
    rw [pkF_two]
    ring
  · have hv : o.val ≠ j.val := fun h => ho (Fin.ext h)
    rw [if_neg ho, if_neg hv, hw o]

theorem pkFRep_unitH {n : ℕ} (k : Fin (n + 1)) :
    PkRep (n + 1) (pkUnit k.val) (ggFUnit (R := ZMod 3) (N := n + 1) k.castSucc) := by
  intro l
  rw [ggFUnit, Vector.get_ofFn, pkUnit, pkLane_pkSet _ _ _ _ (by norm_num)]
  by_cases hl : l = k.castSucc
  · have hv : l.val = k.val := by rw [hl, Fin.coe_castSucc]
    have hln : l.val < n + 1 := by omega
    rw [if_pos hl, if_pos hv, if_pos hln]
    simp
  · have hv : l.val ≠ k.val := fun h => hl (Fin.ext (by rw [h, Fin.coe_castSucc]))
    rw [if_neg hl, if_neg hv, pkLane_zero]
    simp

theorem pkFRep_unitC {n : ℕ} (k : Fin (n + 1)) :
    PkRep (n + 1) (pkUnit k.val) (ggFDUnit (R := ZMod 3) (N := n + 1) k) := by
  intro o
  rw [ggFDUnit, Vector.get_ofFn, pkUnit, pkLane_pkSet _ _ _ _ (by norm_num)]
  by_cases ho : o = k
  · have hv : o.val = k.val := by rw [ho]
    rw [if_pos ho, if_pos hv, if_pos o.isLt]
    simp
  · have hv : o.val ≠ k.val := fun h => ho (Fin.ext h)
    rw [if_neg ho, if_neg hv, pkLane_zero]
    simp

theorem pkFRep_ggFH {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTabF n tab T)
    (k : Fin (n + 1)) :
    ∀ ws : List (Fin (n + 1)), PkRep (n + 1) (pkWordH tab (n + 1) ws (pkUnit k.val)) (ggFH T (k, ws))
  | [] => pkFRep_unitH k
  | j :: ws => by
    rw [ggFH_cons]
    exact pkFRep_refl hT j (pkFRep_ggFH hT k ws)

theorem pkFRep_ggFC {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTabF n tab T)
    (k : Fin (n + 1)) :
    ∀ ws : List (Fin (n + 1)), PkRep (n + 1) (pkWordC tab (n + 1) ws (pkUnit k.val)) (ggFC T (k, ws))
  | [] => pkFRep_unitC k
  | j :: ws => by
    rw [ggFC_cons]
    exact pkFRep_drefl hT j (pkFRep_ggFC hT k ws)

theorem pkF_refMat_eq {n : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    {t t' : Fin (n + 1) × List (Fin (n + 1))} {c h c' h' : ℕ}
    (hc : PkRep (n + 1) c (ggFC T t)) (hh : PkRep (n + 1) h (ggFH T t))
    (hc' : PkRep (n + 1) c' (ggFC T t')) (hh' : PkRep (n + 1) h' (ggFH T t'))
    (hm : (c' = c ∧ h' = h) ∨ (c' = pkNeg (n + 1) c ∧ h' = pkNeg (n + 1) h)) :
    ggFRefMat T t' = ggFRefMat T t := by
  apply ggFRefMat_eq_of_raw_factors
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    exact ⟨fun m => by rw [hh' m.castSucc, hh m.castSucc], fun o => by rw [hc' o, hc o]⟩
  · right
    exact ⟨fun m => pkRep_neg hh hh' m.castSucc, fun o => pkRep_neg hc hc' o⟩

theorem pkF_getD_finRange {α : Type} {N : ℕ} (f : Fin N → α) (d : α) {l : ℕ}
    (hl : l < N) : ((List.finRange N).map f).getD l d = f ⟨l, hl⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp

theorem pkFBlkM_refMat {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    (hT : PkTabF n tab T) {t : Fin (n + 1) × List (Fin (n + 1))} {c h : ℕ}
    (hc : PkRep (n + 1) c (ggFC T t)) (hh : PkRep (n + 1) h (ggFH T t)) :
    pkBlkM (n + 1) (ggFRefMat T t) = pkBlk tab (n + 1) c h := by
  apply pkDSum_congr
  intro l m hl hm
  have hD := pkF_ggFDualAt hT ⟨l, hl⟩ hc
  have hH : (ggFH T t).get (⟨m, hm⟩ : Fin (n + 1)).castSucc = ((pkLane h m : ℕ) : ZMod 3) :=
    (hh _).trans (if_pos hm)
  have hif : (if (⟨l, hl⟩ : Fin (n + 1)) = ⟨m, hm⟩ then (1 : ZMod 3) else 0) =
      ((pkDelta l m : ℕ) : ZMod 3) := by
    rw [pkDelta_eq]
    by_cases hlm : l = m
    · subst hlm
      simp
    · rw [if_neg (fun e => hlm (Fin.mk.inj e)), if_neg hlm]
      simp
  have e : ((ggFRefMat T t).getD l []).getD m 0 =
      ((pkDelta l m + 2 * (pkDotC tab (n + 1) l c * pkLane h m) : ℕ) : ZMod 3) := by
    simp only [ggFRefMat_eq_map, pkF_getD_finRange _ _ hl, pkF_getD_finRange _ _ hm]
    rw [hif, hD, hH]
    push_cast
    rw [pkF_two]
    ring
  beta_reduce
  rw [e, ZMod.val_natCast]
  rfl

theorem pkSharedF_sound {n tab : ℕ} {side : List (Fin (n + 1))}
    {R : List (Fin (n + 1) × List (Fin (n + 1)))} {D : List (ℕ × ℕ × ℕ)}
    (hchk : pkSharedOK tab (n + 1) side R D = true)
    {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTabF n tab T)
    (h2 : ∀ k, (T k).get k.castSucc = 2) (hx : ∀ k, (T k).get (Fin.last (n + 1)) = 0) :
    GGResQTwoListOK T side R ∧ ∀ r ∈ R, ∃ d ∈ D, pkBlkM (n + 1) (ggFRefMat T r) = d.2.2 := by
  obtain ⟨-, h1⟩ := pkAnd_sound hchk
  obtain ⟨hw, h1⟩ := pkAnd_sound h1
  obtain ⟨hseed, hcl⟩ := pkAnd_sound h1
  have hin : ∀ i : Fin (n + 1),
      pkAnyL (fun s : Fin (n + 1) => Nat.beq s.val i.val) side = true → i ∈ side := by
    intro i hi
    obtain ⟨s, hs', he⟩ := pkAnyL_sound hi
    rw [← Fin.ext (pk_beq he)]
    exact hs'
  have hF := pkWalk_sound R D hw
  have hkey : ∀ r d, pkEntry tab (n + 1) side r d = true →
      PkRep (n + 1) d.1 (ggFC T r) ∧ PkRep (n + 1) d.2.1 (ggFH T r) ∧
        (r.1 ∈ side ∧ ∀ i ∈ r.2, i ∈ side) ∧ pkBlk tab (n + 1) d.1 d.2.1 = d.2.2 := by
    rintro ⟨k, ws⟩ d he
    obtain ⟨e1, he⟩ := pkAnd_sound he
    obtain ⟨e2, he⟩ := pkAnd_sound he
    obtain ⟨e3, he⟩ := pkAnd_sound he
    obtain ⟨e4, e5⟩ := pkAnd_sound he
    refine ⟨?_, ?_, ⟨hin k e1, fun i hi => hin i (pkAllL_sound e2 i hi)⟩, pk_beq e5⟩
    · rw [← pk_beq e3]
      exact pkFRep_ggFC hT k ws
    · rw [← pk_beq e4]
      exact pkFRep_ggFH hT k ws
  have hD : ∀ d ∈ D, ∃ r ∈ R, PkRep (n + 1) d.1 (ggFC T r) ∧ PkRep (n + 1) d.2.1 (ggFH T r) := by
    intro d hd
    obtain ⟨r, hr, he⟩ := pk_forall₂_right hF d hd
    exact ⟨r, hr, (hkey r d he).1, (hkey r d he).2.1⟩
  have hmem : ∀ t : Fin (n + 1) × List (Fin (n + 1)), ∀ c h : ℕ,
      PkRep (n + 1) c (ggFC T t) → PkRep (n + 1) h (ggFH T t) → pkMemPM (n + 1) c h D = true →
      ∃ r ∈ R, ggFMat T (ggConjWord r) = ggFRefMat T t := by
    intro t c h hc hh hm
    obtain ⟨d, hd, hm⟩ := pkAnyL_sound hm
    beta_reduce at hm
    obtain ⟨r, hr, hc', hh'⟩ := hD d hd
    refine ⟨r, hr, ?_⟩
    rw [ggFMat_conjWord_eq_ggFRefMat h2 hx r]
    apply pkF_refMat_eq hc hh hc' hh'
    cases ha : pkAnd (Nat.beq d.1 c) (Nat.beq d.2.1 h)
    · rw [ha] at hm
      obtain ⟨f1, f2⟩ := pkAnd_sound hm
      exact Or.inr ⟨pk_beq f1, pk_beq f2⟩
    · obtain ⟨f1, f2⟩ := pkAnd_sound ha
      exact Or.inl ⟨pk_beq f1, pk_beq f2⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨r, hr, he⟩ := hmem (j, []) _ _ (pkFRep_ggFC hT j []) (pkFRep_ggFH hT j [])
      (pkAllL_sound hseed j hj)
    refine ⟨r, hr, ?_⟩
    rw [he]
    exact (ggFMat_conjWord_eq_ggFRefMat h2 hx (j, [])).symm
  · intro j hj r hr
    obtain ⟨d, hd, he⟩ := pk_forall₂_left hF r hr
    obtain ⟨hc, hh, -, -⟩ := hkey r d he
    obtain ⟨k, ws⟩ := r
    have hc2 : PkRep (n + 1) (pkDRefl tab (n + 1) j.val d.1) (ggFC T (k, j :: ws)) := by
      rw [ggFC_cons]
      exact pkFRep_drefl hT j hc
    have hh2 : PkRep (n + 1) (pkRefl tab (n + 1) j.val d.2.1) (ggFH T (k, j :: ws)) := by
      rw [ggFH_cons]
      exact pkFRep_refl hT j hh
    obtain ⟨r', hr', he'⟩ :=
      hmem (k, j :: ws) _ _ hc2 hh2 (pkAllL_sound (pkAllL_sound hcl j hj) d hd)
    refine ⟨r', hr', ?_⟩
    rw [he', ggConjWord_cons (k, ws) j]
    exact (ggFMat_conjWord_eq_ggFRefMat h2 hx (k, j :: ws)).symm
  · intro r hr
    obtain ⟨d, -, he⟩ := pk_forall₂_left hF r hr
    exact (hkey r d he).2.2.1
  · intro r hr
    obtain ⟨d, hd, he⟩ := pk_forall₂_left hF r hr
    obtain ⟨hc, hh, -, hb⟩ := hkey r d he
    exact ⟨d, hd, by rw [pkFBlkM_refMat hT hc hh, hb]⟩

theorem pkTabF_std {n tab : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {u v : ZMod 3}
    (hC : ∀ j l : Fin (n + 1), ggStdEntryI (Int.cast) C ib ic e₁ e₂ u v j l.castSucc =
      ((pkLane tab (j.val * (n + 1) + l.val) : ℕ) : ZMod 3)) :
    PkTabF n tab (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) := by
  intro j l hl
  simp only [ggStdTableI, Vector.get_ofFn]
  exact hC j ⟨l.val, hl⟩

theorem pkListF_std {n tab : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {u v : ZMod 3} {side : List (Fin (n + 1))} {R : List (Fin (n + 1) × List (Fin (n + 1)))}
    {D : List (ℕ × ℕ × ℕ)}
    (hC : ∀ j l : Fin (n + 1), ggStdEntryI (Int.cast) C ib ic e₁ e₂ u v j l.castSucc =
      ((pkLane tab (j.val * (n + 1) + l.val) : ℕ) : ZMod 3))
    (hchk : pkSharedOK tab (n + 1) side R D = true)
    (h2 : ∀ k, (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v k).get (Fin.last (n + 1)) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) side R ∧
      ∀ r ∈ R, ∃ d ∈ D,
        pkBlkM (n + 1) (ggFRefMat (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) r) = d.2.2 :=
  pkSharedF_sound hchk (pkTabF_std hC) h2 hx

theorem GGResQTwoNormOKK_of_pkF {n : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    {side : List (Fin (n + 1))} {R : List (Fin (n + 1) × List (Fin (n + 1)))}
    {x₀ : List ℕ} {τ : List (Fin (n + 1))} {k : Fin (n + 1)} {D : List (ℕ × ℕ × ℕ)}
    (h2 : ∀ k, (T k).get k.castSucc = 2) (hx : ∀ k, (T k).get (Fin.last (n + 1)) = 0)
    (hS : (∀ k, (T k).get k.castSucc = 2) → (∀ k, (T k).get (Fin.last (n + 1)) = 0) →
      GGResQTwoListOK T side R ∧ ∀ r ∈ R, ∃ d ∈ D, pkBlkM (n + 1) (ggFRefMat T r) = d.2.2)
    (hk : k ∈ side)
    (hrest : ggResQTwoVecNeZero (p := 3) (n := n) x₀ ∧ x₀.getD (n + 1) 0 = 0 ∧
      (∀ i ∈ side, ggFDot (T i) (ggFVec x₀) = 0) ∧
      ggResQTwoVecEqV (ggFWord T τ (ggFVec x₀)) (ggFVec x₀))
    (hnot : pkNotMem (pkBlkM (n + 1) (ggFRefMat T (k, τ))) D = true) :
    GGResQTwoNormOKK T side R x₀ τ k := by
  obtain ⟨hL, hB⟩ := hS h2 hx
  refine ⟨hk, hL, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2, ?_⟩
  intro r hr heq
  rw [ggFMat_conjWord_eq_ggFRefMat h2 hx, ggFMat_conjWord_eq_ggFRefMat h2 hx] at heq
  obtain ⟨d, hd, hb⟩ := hB r hr
  have hs : ∀ (x : ℕ) (k : ℕ → Bool), pkStrict x k = k x := by
    intro x k
    cases x <;> rfl
  rw [pkNotMem, hs] at hnot
  have hn := pkAllL_sound hnot d hd
  beta_reduce at hn
  rw [heq, hb, Nat.beq_refl] at hn
  exact Bool.false_ne_true hn

end CFSG.StandardType.GGResQTwoPackedFull
