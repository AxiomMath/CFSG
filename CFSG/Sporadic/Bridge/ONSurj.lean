
module

public import CFSG.Sporadic.Bridge.ONSurjBase1
import all CFSG.Sporadic.Bridge.ONSurjBase
import all CFSG.Sporadic.Bridge.ONSurjBase1

public import CFSG.Sporadic.ON.Simple
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.ONan
public import Certificates.Data.CFSGNative.Bridge.ONGPL
public meta import Certificates.Data.CFSGNative.Bridge.ONGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.ONanInputs
public import Certificates.Certificate9217
public import Certificates.Data.CFSGNative.ON.Certificate
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Bridge.ON

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.Sporadic.Bridge.ONGPL.Native TauCeti

@[expose] noncomputable def img
    (k : ℕ) : J := wordG genG imgWords[k]!

theorem rep_img
    {k : ℕ} (hk : k < 7) : Rep nPts imgT[k]! (img k) := by
  rw [imgT_getElem hk]
  exact Rep.wordT nPts_lt _ fun l _ => rep_genT l

theorem rep_img_inv
    {k : ℕ} (hk : k < 7) : Rep nPts imgTv[k]! (img k)⁻¹ := by
  have hk' : k < imgT.size := by rw [Array.size_map, bridge_facts.sizeImg]; exact hk
  have e : imgTv[k]! = invT nPts imgT[k]! := by
    rw [getElem!_pos imgTv k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
      getElem!_pos imgT k hk']
  rw [e]
  exact Rep.inv_of_invOK (rep_img hk) (by rw [← e]; exact bridge_facts.inv k hk)

@[expose] noncomputable def imgG (z : ℤ) : J :=
  if 0 < z then img (z - 1).toNat else (img (-z - 1).toNat)⁻¹

theorem rep_imgLetter
    {z : ℤ} (hz : z.natAbs ≤ 7) :
    Rep nPts (imgLetter imgT imgTv z) (imgG z) := by
  unfold imgLetter imgG
  split_ifs with h
  · exact rep_img (by omega)
  · exact rep_img_inv (by omega)

theorem wordG_map_letterOf (v : List (ℕ × Bool)) :
    wordG imgG (v.map letterOf) = wordProd img v := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    simp only [wordProd, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [letterOf, imgG]

theorem eq_of_tupleEq
    {g h : J} {X Y : Table} (hX : Rep nPts X g) (hY : Rep nPts Y h)
    (e : tupleEq (apT X chainQ) (apT Y chainQ) = true) : g = h := by
  have : h⁻¹ * g = 1 := by
    apply sep
    intro t ht
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size] at e
    have := (allIn_eq_true.1 e.2) t (Nat.zero_le _) ht
    simp only [beq_iff_eq] at this
    rw [apT_get _ _ ht, apT_get _ _ ht, hX _ (chainQ_lt ht), hY _ (chainQ_lt ht)] at this
    rw [idx_mul, this, idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem relators_eval :
    ∀ v ∈ Sporadic.onanPresentation.relatorLetters, wordProd img v = 1 := by
  rw [relatorLetters_eq]
  intro v hv
  have hlt : ∀ l ∈ v, l.1 < 7 := by
    revert v; unfold rels; decide
  have hrep : Rep nPts (wordT nPts (imgLetter imgT imgTv) (v.map letterOf))
      (wordG imgG (v.map letterOf)) := by
    apply Rep.wordT nPts_lt
    intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    exact rep_imgLetter (by rw [letterOf_natAbs]; exact hlt l hl)
  rw [← wordG_map_letterOf]
  exact eq_one_of_tupleEq hrep (bridge_facts.rels v hv)

@[expose] noncomputable def toJ :
    Sporadic.onanPresentation.Group →* J :=
  presHom Sporadic.onanPresentation img relators_eval

theorem toJ_presLetter
    {z : ℤ} (hz : z.natAbs ≤ 7) :
    toJ (presLetter z) = imgG z := by
  unfold presLetter imgG toJ
  split_ifs with h
  · exact presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega)
  · rw [map_inv, presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega)]

theorem wordG_imgG_mem
    {w : List ℤ} (hw : ∀ z ∈ w, z.natAbs ≤ 7) :
    wordG imgG w ∈ toJ.range := by
  refine ⟨wordG presLetter w, ?_⟩
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact toJ_presLetter (hw z hz)

theorem rep_surjWord
    {i : ℕ} (hi : i < 2) :
    Rep nPts (wordT nPts (imgLetter imgT imgTv) surjWords[i]!) (wordG imgG surjWords[i]!) :=
  Rep.wordT nPts_lt _ fun z hz => rep_imgLetter (bridge_facts.letters _ (surjWords_mem hi) z hz).2

theorem ga_mem_range :
    ga ∈ toJ.range := by
  rw [← eq_of_tupleEq (rep_surjWord (by decide)) rep_ga bridge_facts.surjA]
  exact wordG_imgG_mem fun z hz => (bridge_facts.letters _ (surjWords_mem (by decide)) z hz).2

theorem gb_mem_range :
    gb ∈ toJ.range := by
  rw [← eq_of_tupleEq (rep_surjWord (by decide)) rep_gb bridge_facts.surjB]
  exact wordG_imgG_mem fun z hz => (bridge_facts.letters _ (surjWords_mem (by decide)) z hz).2

theorem toJ_surjective :
    Function.Surjective toJ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_gab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ga_mem_range
  · exact gb_mem_range

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.ONan.Group)
    (hcard : Nat.card SporadicName.ONan.Group ≤ 460815505920) :
    Nonempty (Blueprint.NativeSporadic.ON ≃* SporadicName.ONan.Group) := by
  revert hfin hcard
  show Finite SporadicName.ONan.presentation.Group →
    Nat.card SporadicName.ONan.presentation.Group ≤ 460815505920 →
    Nonempty (Blueprint.NativeSporadic.ON ≃* SporadicName.ONan.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective toJ toJ_surjective hcard (by rw [card_J])
  exact ⟨onEquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.ON ≃* SporadicName.ONan.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.ONan.finite_card_le.1
    Presentation.ONan.finite_card_le.2

end CFSG.Sporadic.Bridge.ON
