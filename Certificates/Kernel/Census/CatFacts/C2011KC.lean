module

public import Certificates.Kernel.Census.CatFacts.C2011K
public import Certificates.Kernel.Census.CatFacts.C2011KS
public import CFSG.Certificates.Kernel.SporSch.ChainKClasses
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.Census.CatFacts.SylowClass
public import CFSG.Certificates.SchreierChainOrder
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Mathlib.Tactic.IntervalCases

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CodesImg
  CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CFSG.Certificates
  CertificateChecks.KernelCatFacts.C2011KP CertificateChecks.KernelCatFacts.C2011KS

theorem evalCodes_append11 (S : List (Equiv.Perm (Fin 42))) (a b : List ℤ) :
    evalCodes S (a ++ b) = evalCodes S a * evalCodes S b := by
  induction a with
  | nil => simp [evalCodes]
  | cons z a ih => simp only [List.cons_append, evalCodes, ih, mul_assoc]

theorem evalCodes_inv11 (S : List (Equiv.Perm (Fin 42))) :
    ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0) → evalCodes S (w.map Neg.neg).reverse = (evalCodes S w)⁻¹
  | [], _ => by simp [evalCodes]
  | z :: w, h => by
    have hz : z ≠ 0 := h z List.mem_cons_self
    have ih := evalCodes_inv11 S w fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, List.reverse_cons, evalCodes_append11, ih, evalCodes, evalCodes, mul_one,
      evalCodes, mul_inv_rev]
    congr 1
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have h1 : 0 < -z := by omega
      have h2 : ¬ 0 < z := by omega
      simp only [h1, h2, ite_true, ite_false, inv_inv, neg_neg]
    · have h1 : ¬ 0 < -z := by omega
      simp only [h1, hgt, ite_true, ite_false, neg_neg]

theorem evalCodes_mem11 (T : List (Equiv.Perm (Fin 42))) :
    ∀ wd : List Int, evalCodes T wd ∈ Subgroup.closure {x | x ∈ T}
  | [] => Subgroup.one_mem _
  | z :: wd => by
    rw [evalCodes]
    refine Subgroup.mul_mem _ ?_ (evalCodes_mem11 T wd)
    have hg : ∀ i, T.getD i 1 ∈ Subgroup.closure {x | x ∈ T} := fun i => by
      by_cases hi : i < T.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact Subgroup.subset_closure (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Subgroup.one_mem _
    split
    · exact hg _
    · exact Subgroup.inv_mem _ (hg _)

theorem xl_2011K : conjWords.map (fun wd => wordK 42 6 (mask 6) (pidn 42 6) QC11.S QC11.SI
    (wd ++ [2] ++ (wd.map Neg.neg).reverse)) = XL11 := by
  decide +kernel

theorem nd_2011K : XL11.Nodup ∧ XL11.all (fun X => Nat.beq (X >>> (42 * 6)) 0) = true := by
  constructor <;> decide +kernel

theorem let_2011K : conjWords.all (fun wd => lettersK 3 (wd ++ [2] ++ (wd.map Neg.neg).reverse) &&
    wd.all (fun z => z != 0)) = true := by
  decide +kernel

theorem inv_2011K : (List.range 64).all (fun j =>
    !((List.range 42).all fun i => Nat.beq (pg 6 (mask 6) (pcomp 42 6 (mask 6)
      (elemK 42 6 (mask 6) (42 * 6) (pidn 42 6) QP11.LR QP11.TR 2 j)
      (elemK 42 6 (mask 6) (42 * 6) (pidn 42 6) QP11.LR QP11.TR 2 j)) i) i) ||
    Nat.beq (elemK 42 6 (mask 6) (42 * 6) (pidn 42 6) QP11.LR QP11.TR 2 j) (pidn 42 6) ||
    XL11.contains (elemK 42 6 (mask 6) (42 * 6) (pidn 42 6) QP11.LR QP11.TR 2 j)) = true := by
  decide +kernel

theorem gen_2011K : (List.range 18).all (fun j => lettersK 3 (wP11.getD j []) &&
    Nat.beq (wordK 42 6 (mask 6) (pidn 42 6) QC11.S QC11.SI (wP11.getD j [])) (QP11.S j) &&
    Nat.beq (pcomp 42 6 (mask 6) (QP11.S j) (QC11.S 1)) (pcomp 42 6 (mask 6) (QC11.S 1) (QP11.S j)))
    = true := by
  decide +kernel

theorem img_2011K {wd : List Int} (h : lettersK 3 wd = true) :
    imageList (evalCodes [tab g₁, tab g₂, tab g₃] wd) =
      (unpack 42 6 (wordK 42 6 (mask 6) (pidn 42 6) QC11.S QC11.SI wd)).toList := by
  have hp : ∀ j < [tab g₁, tab g₂, tab g₃].length,
      permOK 42 6 (mask 6) (42 * 6) (QC11.S j) (QC11.SI j) = true := by
    intro j hj
    have hj' : j < 3 := by simpa using hj
    interval_cases j <;> decide +kernel
  have hid : imageList (1 : Equiv.Perm (Fin 42)) = (unpack 42 6 (pidn 42 6)).toList := by
    decide +kernel
  exact evalCodes_img (by decide +kernel) chainQS11.2.2.2.1 hp hid h

@[expose] def gP11 : List (Equiv.Perm (Fin 42)) := wP11.map (evalCodes [tab g₁, tab g₂, tab g₃])

theorem gP11_getD (j : Nat) : gP11.getD j 1 = evalCodes [tab g₁, tab g₂, tab g₃] (wP11.getD j []) := by
  have h := List.getD_map (l := wP11) (n := j) (d := ([] : List Int))
    (evalCodes [tab g₁, tab g₂, tab g₃])
  exact h

theorem gP11_length : gP11.length = 18 := by
  simp [gP11, wP11]

theorem gen11 {j : Nat} (hj : j < 18) : lettersK 3 (wP11.getD j []) = true ∧
    wordK 42 6 (mask 6) (pidn 42 6) QC11.S QC11.SI (wP11.getD j []) = QP11.S j ∧
    pcomp 42 6 (mask 6) (QP11.S j) (QC11.S 1) = pcomp 42 6 (mask 6) (QC11.S 1) (QP11.S j) := by
  have h := List.all_eq_true.1 gen_2011K j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem chainP11 : ChainK 42 6 gP11 wNil11 (#v[0, 1] : Vector (Fin 42) 2)
    QP11.S QP11.SI QP11.LR QP11.TR QP11.TRI 18 QP11.BP 3 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QP11.head, QP11.hl,
    by norm_num, .inl QP11.hs⟩
  rw [gP11_length] at hj
  obtain ⟨hl, he, -⟩ := gen11 hj
  rw [gP11_getD, ← he]
  exact img_2011K hl

theorem prep11 {wd : List Int} (h : lettersK 3 wd = true) :
    PRep 42 6 (wordK 42 6 (mask 6) (pidn 42 6) QC11.S QC11.SI wd)
      (evalCodes [tab g₁, tab g₂, tab g₃] wd) :=
  prep_of_imageList (img_2011K h)

theorem g2_11 : PRep 42 6 (QC11.S 1) g₂ := by
  have h := prep_of_imageList (chainQS11.2.2.2.1 1 (by decide))
  simpa only [List.getD_cons_succ, List.getD_cons_zero, tab_eq] using h

theorem prep_eq11 {P : Nat} {g h : Equiv.Perm (Fin 42)} (hg : PRep 42 6 P g) (hh : PRep 42 6 P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem conj11 {wd : List Int} (hwd : wd ∈ conjWords) :
    PRep 42 6 (wordK 42 6 (mask 6) (pidn 42 6) QC11.S QC11.SI (wd ++ [2] ++ (wd.map Neg.neg).reverse))
      (evalCodes [tab g₁, tab g₂, tab g₃] wd * g₂ * (evalCodes [tab g₁, tab g₂, tab g₃] wd)⁻¹) := by
  have h := List.all_eq_true.1 let_2011K wd hwd
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  have e : evalCodes [tab g₁, tab g₂, tab g₃] (wd ++ [2] ++ (wd.map Neg.neg).reverse) =
      evalCodes [tab g₁, tab g₂, tab g₃] wd * g₂ * (evalCodes [tab g₁, tab g₂, tab g₃] wd)⁻¹ := by
    rw [evalCodes_append11, evalCodes_append11, evalCodes_inv11 _ _ h.2]
    simp [evalCodes, tab_eq]
  rw [← e]
  exact prep11 h.1

theorem mem11 (wd : List Int) : evalCodes [tab g₁, tab g₂, tab g₃] wd ∈ QS.originalSubgroup := by
  rw [QS, certificate_originalSubgroup]
  exact evalCodes_mem11 _ wd

theorem conjugators_eq11 : conjugators = conjWords.map (evalCodes [tab g₁, tab g₂, tab g₃]) := by
  simp only [conjugators, tab_eq]

theorem memC11 : ∀ c ∈ conjugators, c ∈ QS.originalSubgroup := by
  intro c hc
  rw [conjugators_eq11] at hc
  obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hc
  exact mem11 wd

theorem g2_mem11 : g₂ ∈ QS.originalSubgroup := by
  have h := mem11 [2]
  simpa [evalCodes, tab_eq] using h

theorem nodup11 : (conjugators.map fun c => c * g₂ * c⁻¹).Nodup := by
  rw [conjugators_eq11, List.map_map]
  have h2 := nd_2011K.1
  have hs := List.all_eq_true.1 nd_2011K.2
  rw [← xl_2011K] at h2 hs
  rw [List.Nodup, List.pairwise_map] at h2 ⊢
  refine h2.imp_of_mem fun {a b} ha hb hne heq => hne ?_
  have sa := Nat.eq_of_beq_eq_true (hs _ (List.mem_map_of_mem ha))
  have sb := Nat.eq_of_beq_eq_true (hs _ (List.mem_map_of_mem hb))
  have pb := conj11 hb
  simp only [Function.comp_apply] at heq
  rw [← heq] at pb
  exact CFSG.KS.PF.eq_of_fields (by norm_num) sa sb fun i hi =>
    ((conj11 ha) ⟨i, hi⟩).trans (pb ⟨i, hi⟩).symm

@[expose] def P11 : Subgroup (Equiv.Perm (Fin 42)) :=
  (certificate (by decide) gP11 wNil11 (#v[0, 1] : Vector (Fin 42) 2) (by decide)).originalSubgroup

theorem ordP11 : ordK QP11.LR 2 = 64 := Nat.eq_of_beq_eq_true (by decide +kernel)

theorem P11_card : Nat.card P11 = 2 ^ 6 := by
  rw [P11, card_group chainP11 (by decide) (by decide), ordP11]
  norm_num

theorem P11_le : P11 ≤ QS.originalSubgroup := by
  rw [P11, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq, gP11] at hg
  obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
  exact mem11 wd

theorem P11_comm : ∀ y ∈ P11, y * g₂ = g₂ * y := by
  have hc : P11 ≤ Subgroup.centralizer {g₂} := by
    rw [P11, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < 18 := by rwa [gP11_length] at hj
    obtain ⟨hl, he, hcm⟩ := gen11 hj'
    have hy : PRep 42 6 (QP11.S j) gP11[j] := by
      have e : gP11[j] = gP11.getD j 1 := (List.getD_eq_getElem _ _ hj).symm
      rw [e, gP11_getD, ← he]
      exact prep11 hl
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have a := prep_pcomp (by norm_num) hy g2_11
    have b := prep_pcomp (by norm_num) g2_11 hy
    rw [hcm] at a
    exact Equiv.ext fun x => Fin.ext ((b x).symm.trans (a x))
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hc hy)) g₂ rfl).symm

theorem P11_cls : ∀ y ∈ P11, y ^ 2 = 1 → y ≠ 1 → ∃ c ∈ conjugators, c * g₂ * c⁻¹ = y := by
  intro y hy hy2 hy1
  obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainP11 (by decide) (by decide) y).1 hy
  rw [ordP11] at hj
  have hE := prep_elemK chainP11 j
  have hc := List.all_eq_true.1 inv_2011K j (List.mem_range.2 hj)
  have hsq : ((List.range 42).all fun i => Nat.beq (pg 6 (mask 6) (pcomp 42 6 (mask 6)
      (elemK 42 6 (mask 6) (42 * 6) (pidn 42 6) QP11.LR QP11.TR 2 j)
      (elemK 42 6 (mask 6) (42 * 6) (pidn 42 6) QP11.LR QP11.TR 2 j)) i) i) = true := by
    rw [List.all_eq_true]
    intro i hi
    have h1 := prep_pcomp (by norm_num) hE hE
    rw [← pow_two, hy2] at h1
    have h2 := h1 ⟨i, List.mem_range.1 hi⟩
    rw [h2]
    exact Nat.beq_refl i
  rw [hsq] at hc
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc
  rcases hc with h | h
  · rw [Nat.eq_of_beq_eq_true h] at hE
    exact absurd (prep_eq11 hE (prep_pidn (by norm_num) (by norm_num))) hy1
  · rw [List.contains_iff_mem, ← xl_2011K] at h
    obtain ⟨wd, hwd, hw⟩ := List.mem_map.1 h
    refine ⟨evalCodes [tab g₁, tab g₂, tab g₃] wd, ?_, ?_⟩
    · rw [conjugators_eq11]
      exact List.mem_map_of_mem hwd
    · have h3 := conj11 hwd
      rw [hw] at h3
      exact prep_eq11 h3 hE

theorem class_2011K : classCheck (elemsV QS) g₂ conjugators = true := by
  classical
  have hV : ValidSchreier QS := chainK_valid chainQS11 (by decide) (by decide)
  have hcard : Nat.card QS.originalSubgroup = 2 ^ 6 * 315 :=
    (RawSchreierDatum.orderCertificate_eq_card QS hV).symm.trans qs_2011K.2
  have hPc : Nat.card (P11.subgroupOf QS.originalSubgroup) = 2 ^ 6 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe P11_le).toEquiv).trans P11_card
  have hmapv : ((conjugators.pmap (fun c hc => (⟨c, hc⟩ : QS.originalSubgroup)) memC11).map
      fun c => c * ⟨g₂, g2_mem11⟩ * c⁻¹).map Subtype.val =
      conjugators.map fun c => c * g₂ * c⁻¹ := by
    rw [List.map_map, List.map_pmap]
    exact List.pmap_eq_map (f := fun c => c * g₂ * c⁻¹) memC11
  have hnd : ((conjugators.pmap (fun c hc => (⟨c, hc⟩ : QS.originalSubgroup)) memC11).map
      fun c => c * ⟨g₂, g2_mem11⟩ * c⁻¹).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [hmapv]
    exact nodup11
  have hlen : (conjugators.pmap (fun c hc => (⟨c, hc⟩ : QS.originalSubgroup)) memC11).length =
      315 := by
    rw [List.length_pmap, conjugators, List.length_map]
    rfl
  have key := CFSG.Certificates.Kernel.SylowClass.mem_conj_list_of_sylow (p := 2)
    (P11.subgroupOf QS.originalSubgroup) hcard hPc (by decide) ⟨g₂, g2_mem11⟩
    (fun y hy => Subtype.ext (P11_comm _ (Subgroup.mem_subgroupOf.1 hy)))
    (fun y hy hy2 hy1 => by
      obtain ⟨c, hc, hcy⟩ := P11_cls (y : Equiv.Perm (Fin 42)) (Subgroup.mem_subgroupOf.1 hy)
        (by simpa using congrArg Subtype.val hy2) (fun h => hy1 (Subtype.ext h))
      exact ⟨⟨c, memC11 c hc⟩, Subtype.ext hcy⟩)
    _ hnd hlen
  unfold classCheck
  rw [List.all_eq_true]
  intro x hx
  have hxH : x ∈ QS.originalSubgroup := (mem_elemsT QS hV x).1 (by rw [elemsT_eq_elemsV]; exact hx)
  by_cases h1 : x * x = 1
  · by_cases h2 : x = 1
    · simp [h2]
    · obtain ⟨c, hc, hcx⟩ := key ⟨x, hxH⟩ (Subtype.ext (by simpa [pow_two] using h1))
        (fun h => h2 (congrArg Subtype.val h))
      obtain ⟨c0, hc0, rfl⟩ := List.mem_pmap.1 hc
      have h3 : c0 * g₂ * c0⁻¹ = x := congrArg Subtype.val hcx
      simp only [h1, h2, decide_true, decide_false, Bool.not_true, Bool.false_or,
        List.any_eq_true, decide_eq_true_eq]
      exact ⟨c0, hc0, h3⟩
  · simp [h1]

end CertificateChecks.KernelCatFacts
