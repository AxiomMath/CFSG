module

public import CFSG.GH74.QTGen4.Recog.G23.NativeFacts
public import CFSG.GH74.QTGen4.Recog.G23.NativeFactsB
public import CFSG.GH74.QTGen4.Recog.G23.NativeLetters
public import Certificates.Certificate687002
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Recognition.PresentedWordsClosure

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th Native Max3
open CFSG.Sporadic.Recognition.PresentedWords

section Basic

theorem imgGL_mem_J {k : ℕ} (hk : k < 8) : Bridge.Th.imgGL k ∈ J := by
  have hJ : J ≤ Bridge.Th.φ.range := Bridge.Th.J_le_range
  have hcard : Nat.card Bridge.Th.φ.range ≤ Nat.card J := by
    have hfinP : Finite Bridge.Th.pres.Group := by
      change Finite TauCeti.SporadicName.Th.Group
      exact CFSG.Sporadic.Presentation.Th.finite_card_le.1
    letI := hfinP
    have h1 : Nat.card Bridge.Th.φ.range ≤ Nat.card Bridge.Th.pres.Group :=
      Nat.card_le_card_of_surjective Bridge.Th.φ.rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    have h2 : Nat.card Bridge.Th.pres.Group ≤ 90745943887872000 := by
      change Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000
      exact CFSG.Sporadic.Presentation.Th.finite_card_le.2
    exact h1.trans (h2.trans Bridge.Th.card_J.symm.le)
  have heq : J = Bridge.Th.φ.range := Subgroup.eq_of_le_of_card_ge hJ hcard
  rw [heq]
  exact Bridge.Th.imgGL_mem_range k

noncomputable def gJ (i : Fin 8) : J :=
  ⟨Bridge.Th.imgGL i.val, imgGL_mem_J i.2⟩

noncomputable def cJ : J := wprod gJ cWord

noncomputable def hswJ (i : Fin 8) : J := cJ * gJ i * cJ⁻¹

theorem imgGL_mem_J_all (i : ℕ) : Bridge.Th.imgGL i ∈ J := by
  by_cases hi : i < 8
  · exact imgGL_mem_J hi
  · rw [Bridge.Th.imgGL, dite_eq_right hi]
    exact J.one_mem

noncomputable def imgWordJ (w : List (Fin 8 × Bool)) : J :=
  ⟨wprod (fun i : Fin 8 => Bridge.Th.imgGL i) w, by
    rw [← wordProd_map_fin (fun i : Fin 8 => Bridge.Th.imgGL i) w]
    have hfun : (fun i : ℕ => if h : i < 8 then Bridge.Th.imgGL i else 1) =
        Bridge.Th.imgGL := by
      funext i
      by_cases hi : i < 8
      · rw [dif_pos hi]
      · rw [dif_neg hi, Bridge.Th.imgGL, dif_neg hi]
    rw [hfun]
    exact Bridge.wordProd_mem imgGL_mem_J_all (w.map fun l => (l.1.val, l.2))⟩

theorem imgWordJ_nil : imgWordJ [] = 1 := Subtype.ext rfl

theorem imgWordJ_cons (l : Fin 8 × Bool) (w : List (Fin 8 × Bool)) :
    imgWordJ (l :: w) = (if l.2 then gJ l.1 else (gJ l.1)⁻¹) * imgWordJ w := by
  apply Subtype.ext
  show wprod (fun i : Fin 8 => Bridge.Th.imgGL i) (l :: w) =
    (if l.2 then (gJ l.1 : J) else (gJ l.1)⁻¹) * (imgWordJ w : J)
  rw [wprod_cons]
  cases hl : l.2
  · simp [gJ, hl]
    rfl
  · simp [gJ, hl]
    rfl

theorem wprod_hswJ (w : List (Fin 8 × Bool)) :
    wprod hswJ w = cJ * imgWordJ w * cJ⁻¹ := by
  induction w with
  | nil => rw [wprod_nil, imgWordJ_nil]; group
  | cons l w ih =>
    rw [wprod_cons, ih, imgWordJ_cons]
    cases hl : l.2
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, hswJ, gJ]
      group
    · simp only [hl, ↓reduceIte, hswJ, gJ]
      group

theorem hswJ_rel : ∀ w : List (Fin 8 × Bool),
    w ∈ (TauCeti.Sporadic.Thompson.presentation.relators :
      List (List (Fin 8 × Bool))) → wprod hswJ w = 1 := by
  intro w hw
  rw [wprod_hswJ]
  have hfun : (fun i : ℕ => if h : i < 8 then Bridge.Th.imgGL i else 1) =
      Bridge.Th.imgGL := by
    funext i
    by_cases hi : i < 8
    · rw [dif_pos hi]
    · rw [dif_neg hi, Bridge.Th.imgGL, dif_neg hi]
  have h1 : wprod (fun i : Fin 8 => Bridge.Th.imgGL i) w = 1 := by
    refine (th_relatorLetters_iff (fun i : Fin 8 => Bridge.Th.imgGL i)).1 ?_ w hw
    have h := Bridge.Th.hrel
    rw [hfun]
    exact h
  have h2 : imgWordJ w = 1 := Subtype.ext h1
  rw [h2]
  group

theorem wprod_hswWord (i : Fin 8) : wprod gJ (hswWord i) = hswJ i := by
  unfold hswWord hswJ cJ
  rw [wprod_append, wprod_append, wprod_cons, wprod_nil, mul_one, wprod_invRev]
  change (wprod gJ cWord * gJ i) * (wprod gJ cWord)⁻¹ =
    wprod gJ cWord * gJ i * (wprod gJ cWord)⁻¹
  group

theorem wprod_hswWordInv (i : Fin 8) : wprod gJ (hswWordInv i) = (hswJ i)⁻¹ := by
  unfold hswWordInv hswJ cJ
  rw [wprod_append, wprod_append, wprod_cons, wprod_nil, mul_one, wprod_invRev]
  change (wprod gJ cWord * (gJ i)⁻¹) * (wprod gJ cWord)⁻¹ =
    (wprod gJ cWord * gJ i * (wprod gJ cWord)⁻¹)⁻¹
  group

theorem rowsMatrix_rowsG (i : Fin 8) : rowsMatrix (rowsG i) = toMat (gJ i) := by
  simpa [rowsG, gJ, toMat] using Bridge.Th.imgMats_spec i.val

theorem rowsMatrix_rowsGInv (i : Fin 8) : rowsMatrix (rowsGInv i) = toMat ((gJ i)⁻¹) := by
  simpa [rowsGInv, gJ, toMat] using Bridge.Th.imgInvs_spec i.val

theorem rowsMatrix_rowsHsw (i : Fin 8) :
    rowsMatrix (rowsHsw i) = toMat (hswJ i) := by
  unfold rowsHsw
  rw [rowsMatrix_wRows (g := gJ) (rs := rowsG) (rsi := rowsGInv) (w := hswWord i)]
  · rw [wprod_hswWord]
  · exact rowsMatrix_rowsG
  · exact rowsMatrix_rowsGInv

theorem rowsMatrix_rowsHswInv (i : Fin 8) :
    rowsMatrix (rowsHswInv i) = toMat ((hswJ i)⁻¹) := by
  unfold rowsHswInv
  rw [rowsMatrix_wRows (g := gJ) (rs := rowsG) (rsi := rowsGInv) (w := hswWordInv i)]
  · rw [wprod_hswWordInv]
  · exact rowsMatrix_rowsG
  · exact rowsMatrix_rowsGInv

theorem rowsMatrix_rowsA : rowsMatrix rowsA = toMat (a : J) := isRows_a.eq

theorem hswJ_zero : hswJ 0 = (a : J) := by
  apply toMat_injective
  rw [← rowsMatrix_rowsHsw 0, ← rowsMatrix_rowsA]
  exact rowsMatrix_eq_of_eqRows Certificates.certificate687002.1

theorem hswJ_ne : hswJ 0 ≠ hswJ 1 := by
  intro h
  apply Certificates.certificate687002.2.1
  calc
    rowsMatrix (rowsHsw 1) = toMat (hswJ 1) := rowsMatrix_rowsHsw 1
    _ = toMat (hswJ 0) := congrArg toMat h.symm
    _ = toMat (a : J) := by rw [hswJ_zero]
    _ = rowsMatrix rowsA := rowsMatrix_rowsA.symm

noncomputable def lJ (i : Fin 6) : J := wprod hswJ (lWord i)

theorem rowsMatrix_rowsL (i : Fin 6) : rowsMatrix (rowsL i) = toMat (lJ i) := by
  unfold rowsL lJ
  apply rowsMatrix_wRowsArr
  · intro j
    rw [rowsHswArr_get]
    exact rowsMatrix_rowsHsw j
  · intro j
    rw [rowsHswInvArr_get]
    exact rowsMatrix_rowsHswInv j

theorem rowsMatrix_rowsLInv (i : Fin 6) : rowsMatrix (rowsLInv i) = toMat ((lJ i)⁻¹) := by
  unfold rowsLInv lJ
  rw [rowsMatrix_wRowsArr (g := hswJ)]
  · rw [wprod_invRev]
  · intro j
    rw [rowsHswArr_get]
    exact rowsMatrix_rowsHsw j
  · intro j
    rw [rowsHswInvArr_get]
    exact rowsMatrix_rowsHswInv j

theorem rowsMatrix_rowsWJ (i : Fin 8) :
    rowsMatrix (rowsWJ i) = toMat (Max3.wordProd (wJ i) * (a : J) ^ εJ i) := by
  unfold rowsWJ
  rw [rowsMatrix_mulRows, (Max3.IsRows.word Max3.isRows_x Max3.isRows_y (wJ i)).eq,
    (Max3.IsRows.pow Max3.isRows_a (εJ i)).eq, toMat_mul]

private theorem hswJ_eq_wordProd_of_eqRows {i : Fin 8}
    (h : eqRows (rowsHsw i) (rowsWJ i) = true) :
    hswJ i = Max3.wordProd (wJ i) * (a : J) ^ εJ i := by
  apply toMat_injective
  rw [← rowsMatrix_rowsHsw i, ← rowsMatrix_rowsWJ i]
  exact rowsMatrix_eq_of_eqRows h

theorem hswJ_eq_wordProd (i : Fin 8) (hi : i ≠ 1) :
    hswJ i = Max3.wordProd (wJ i) * (a : J) ^ εJ i := by
  obtain ⟨-, -, -, -, -, -, h2, h3, h4, h5, h6, h7⟩ := Certificates.certificate687002
  fin_cases i
  · change hswJ 0 = Max3.wordProd (wJ 0) * (a : J) ^ εJ 0
    rw [hswJ_zero]
    simp [wJ, εJ, Max3.wordProd]
  · exact absurd rfl hi
  · exact hswJ_eq_wordProd_of_eqRows h2
  · exact hswJ_eq_wordProd_of_eqRows h3
  · exact hswJ_eq_wordProd_of_eqRows h4
  · exact hswJ_eq_wordProd_of_eqRows h5
  · exact hswJ_eq_wordProd_of_eqRows h6
  · exact hswJ_eq_wordProd_of_eqRows h7

theorem hswJ_mem_M (i : Fin 8) (hi : i ≠ 1) : hswJ i ∈ Max3.M := by
  rw [← CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M CFSG.Sporadic.Th.th_kernel_facts]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : hswJ 0 * hswJ i = hswJ i * hswJ 0 := by
    apply toMat_injective
    rw [toMat_mul, toMat_mul, ← rowsMatrix_rowsHsw 0, ← rowsMatrix_rowsHsw i,
      ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
    exact rowsMatrix_eq_of_eqRows
      (Certificates.certificate687002.2.2.1 i hi)
  rw [hswJ_zero] at hcomm
  exact hcomm.symm

theorem kap_hswJ (i : Fin 8) (hi : i ≠ 1) :
    (Max3.InvRep.kap ⟨hswJ i, hswJ_mem_M i hi⟩ : Equiv.Perm (Fin 9)) =
      ((wJ i).map (Max3.Gen.eval Max3.aPerm Max3.bPerm)).prod := by
  have haM : (a : J) ∈ Max3.M := Max3.z_eq_a ▸ Max3.z_mem_M
  have hM : (⟨hswJ i, hswJ_mem_M i hi⟩ : ↥Max3.M) =
      Max3.InvRep.wordM (wJ i) * ⟨(a : J) ^ εJ i, Subgroup.pow_mem _ haM _⟩ := by
    apply Subtype.ext
    change hswJ i = Max3.wordProd (wJ i) * (a : J) ^ εJ i
    exact hswJ_eq_wordProd i hi
  have h1 : Max3.InvRep.kap (⟨hswJ i, hswJ_mem_M i hi⟩ : ↥Max3.M) =
      Max3.InvRep.kap (Max3.InvRep.wordM (wJ i)) *
        Max3.InvRep.kap ⟨(a : J) ^ εJ i, Subgroup.pow_mem _ haM _⟩ := by
    rw [hM, map_mul]
  rw [h1, Subgroup.coe_mul, Max3.InvRep.kap_wordM]
  have h2 : Max3.InvRep.kap (⟨(a : J) ^ εJ i,
      Subgroup.pow_mem _ haM _⟩ : ↥Max3.M) = 1 := by
    rw [Max3.InvRep.kap_eq_one_iff]
    exact Subgroup.pow_mem _ (Max3.z_eq_a ▸ Max3.z_mem_Q) _
  rw [h2, Subgroup.coe_one, mul_one]

theorem lJ_sat : CFSG.GH74.QTGen4.Recog.G23.SatisfiesG23Words lJ := by
  intro r hr
  rw [lift_mk]
  have h := List.all_eq_true.1 Certificates.certificate687002.2.2.2.1 r hr
  have hL : ∀ i, rowsMatrix (((rowsLArr ())[i.val]?).getD idRows) = toMat (lJ i) := by
    intro i
    rw [rowsLArr_get]
    exact rowsMatrix_rowsL i
  have hLI : ∀ i, rowsMatrix (((rowsLInvArr ())[i.val]?).getD idRows) =
      toMat ((lJ i)⁻¹) := by
    intro i
    rw [rowsLInvArr_get]
    exact rowsMatrix_rowsLInv i
  have hm := rowsMatrix_wRowsArr (rs := rowsLArr ()) (rsi := rowsLInvArr ())
    (g := lJ) hL hLI r
  have he := rowsMatrix_eq_of_eqRows h
  rw [hm, rowsMatrix_idRows] at he
  exact toMat_injective (by rw [he, toMat_one])

theorem lJ_comm_t (i : Fin 6) : Commute (lJ i) (hswJ 6) := by
  apply toMat_injective
  rw [toMat_mul, toMat_mul, ← rowsMatrix_rowsL i, ← rowsMatrix_rowsHsw 6,
    ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
  exact rowsMatrix_eq_of_eqRows
    (Certificates.certificate687002.2.2.2.2.1 i)

theorem lJ_ne_one : ∃ i, lJ i ≠ 1 := by
  refine ⟨0, ?_⟩
  intro h
  apply Certificates.certificate687002.2.2.2.2.2.1
  calc
    rowsMatrix (rowsL 0) = toMat (lJ 0) := rowsMatrix_rowsL 0
    _ = toMat (1 : J) := by rw [h]
    _ = 1 := toMat_one
    _ = rowsMatrix idRows := rowsMatrix_idRows.symm

end Basic

section Ghat

theorem nonempty_K₀_ghat :
    Nonempty (↥(Subgroup.closure (Set.range lJ)) ≃* CFSG.GH74.QTGen4.Recog.G23.Ghat) := by
  obtain ⟨u, hu, hugen⟩ := CFSG.GH74.QTGen4.Recog.G23.exists_letters_native
  exact CFSG.GH74.QTGen4.Recog.G23.nonempty_mulEquiv_native_of_letters
    CFSG.GH74.QTGen4.Recog.G23.ghat_simple CFSG.GH74.QTGen4.Recog.G23.ghat_card
    u hu hugen lJ lJ_sat lJ_ne_one

end Ghat

end CFSG.Sporadic.Th.Recog
