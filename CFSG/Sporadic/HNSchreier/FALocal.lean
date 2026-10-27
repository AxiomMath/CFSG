module

public import CFSG.Sporadic.HNSchreier.Involution
public import CFSG.Sporadic.HNSchreier.FALocalCheck
public import Certificates.Certificate16041
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HN.Local Equiv

theorem hJ_mem (j : ℕ) : hJ j ∈ HJ := by
  refine gStrong_mem _ _ HJ ?_ j
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h1J_mem
  · exact h2J_mem

theorem hWordJ_mem (w : List ℤ) : hWordJ w ∈ HJ := by
  refine HJ.list_prod_mem fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
  split_ifs
  · exact hJ_mem _
  · exact inv_mem (hJ_mem _)

@[expose] def hWordH (w : List ℤ) : HJ := ⟨hWordJ w, hWordJ_mem w⟩

@[expose] def natWord (w : List ℤ) : Perm (Fin 12) :=
  (w.map fun l => if 0 < l then natImg (l.natAbs - 1) else (natImg (l.natAbs - 1))⁻¹).prod

@[expose] def thetaHom :
    HJ →* Perm (Fin 12) :=
  MonoidHom.comp (alternatingGroup (Fin 12)).subtype (thetaJ : HJ →* alternatingGroup (Fin 12))

theorem thetaHom_apply
    (h : HJ) : thetaHom h = (thetaJ h : Perm (Fin 12)) := rfl

theorem hJ_eq_gStrong (j : ℕ) :
    (⟨hJ j, hJ_mem j⟩ : HJ) = gStrong [⟨h1J, h1J_mem⟩, ⟨h2J, h2J_mem⟩] LocalData.strongWords j := by
  apply Subtype.ext
  show hJ j = HJ.subtype (gStrong [⟨h1J, h1J_mem⟩, ⟨h2J, h2J_mem⟩] LocalData.strongWords j)
  rw [map_gStrong]
  rfl

theorem thetaJ_hJ
    (j : ℕ) : (thetaJ ⟨hJ j, hJ_mem j⟩ : Perm (Fin 12)) = natImg j := by
  have e := map_gStrong thetaHom [⟨h1J, h1J_mem⟩, ⟨h2J, h2J_mem⟩] LocalData.strongWords j
  rw [← hJ_eq_gStrong, thetaHom_apply, List.map_cons, List.map_cons, List.map_nil,
    thetaHom_apply, thetaHom_apply, thetaJ_h1, thetaJ_h2] at e
  exact e

theorem hWordH_cons (l : ℤ) (w : List ℤ) :
    hWordH (l :: w) = (if 0 < l then ⟨hJ (l.natAbs - 1), hJ_mem _⟩ else
      (⟨hJ (l.natAbs - 1), hJ_mem _⟩ : HJ)⁻¹) * hWordH w := by
  apply Subtype.ext
  show hWordJ (l :: w) = _
  rw [hWordJ_cons]
  split_ifs <;> rfl

theorem natWord_cons (l : ℤ) (w : List ℤ) :
    natWord (l :: w) = (if 0 < l then natImg (l.natAbs - 1) else (natImg (l.natAbs - 1))⁻¹) *
      natWord w := by
  simp only [natWord, List.map_cons, List.prod_cons]

theorem thetaJ_hWord
    (w : List ℤ) : (thetaJ (hWordH w) : Perm (Fin 12)) = natWord w := by
  induction w with
  | nil =>
    rw [show hWordH [] = 1 from Subtype.ext rfl, map_one]
    rfl
  | cons l w ih =>
    have hX : (thetaJ (if 0 < l then ⟨hJ (l.natAbs - 1), hJ_mem _⟩ else
        (⟨hJ (l.natAbs - 1), hJ_mem _⟩ : HJ)⁻¹) : Perm (Fin 12)) =
        if 0 < l then natImg (l.natAbs - 1) else (natImg (l.natAbs - 1))⁻¹ := by
      by_cases hl : 0 < l
      · rw [ite_eq_left hl, ite_eq_left hl]
        exact thetaJ_hJ _
      · rw [ite_eq_right hl, ite_eq_right hl, map_inv, Subgroup.coe_inv, thetaJ_hJ]
    rw [hWordH_cons, natWord_cons, ← ih, map_mul, Subgroup.coe_mul, hX]

theorem natWord_eq_evalWord {j : ℕ} (w : List ℤ) (hw : plettersOK j w = true) :
    Quiver.SchreierGraph.evalWord (fun h : Fin j => natImg h) (ptoLetters j w) = natWord w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have hcons : ptoLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters j w := by
      simp [ptoLetters, hl0, hlj]
    rw [hcons, natWord, List.map_cons, List.prod_cons, ← natWord, ← ih hw']
    by_cases hpos : 0 < l
    · rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, ite_eq_left hpos]
    · rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false, ite_eq_right hpos]

theorem natStrongInv_rep :
    ∀ h < 17, PRep 12 (pinvs 12 natStrongArr)[h]! (natImg h)⁻¹ := by
  intro h hh
  refine prep_inv_of_pisInv (natStrong_rep h hh) ?_
  have h2 := local_parts.2.1
  unfold strongOK at h2
  simp only [Bool.and_eq_true] at h2
  exact allBelowN_spec h2.1.2 (show h < natStrongArr.size by
    have := (prep_of_strongOK local_parts.2.1 prep_natPerm1 prep_natPerm2).1
    rw [this, strongWords_size]; exact hh)

theorem prep_natWord {w : List ℤ} (hw : plettersOK 17 w = true) :
    PRep 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) w) (natWord w) := by
  rw [← natWord_eq_evalWord w hw]
  exact prep_pword (fun h hh => natStrong_rep h hh) (fun h hh => natStrongInv_rep h hh) w hw

@[expose] def tri (a b c : Fin 12) : Perm (Fin 12) := swap a c * swap a b

@[expose] def tripleNat : ℕ → Perm (Fin 12)
  | 0 => 1
  | m + 1 => tripleNat m * tri ⟨(3 * m) % 12, Nat.mod_lt _ (by norm_num)⟩
      ⟨(3 * m + 1) % 12, Nat.mod_lt _ (by norm_num)⟩ ⟨(3 * m + 2) % 12, Nat.mod_lt _ (by norm_num)⟩

@[expose] def fiveNat : Perm (Fin 12) := swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1

theorem prep_tripleArr : ∀ m : Fin 4, PRep 12 (tripleArr (m.val + 1)) (tripleNat (m.val + 1)) := by
  unfold PRep tripleArr tripleNat tri
  decide

theorem prep_fiveArr : PRep 12 fiveArr fiveNat := by
  unfold PRep fiveArr fiveNat
  decide

theorem fa_nat_parts : FAData.sWords.size = 4 ∧
    (∀ k < 4, plettersOK 17 FAData.sWords[k]! = true ∧
      peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) FAData.sWords[k]!)
        (tripleArr (k + 1)) = true) ∧
    plettersOK 17 FAData.fWord = true ∧
    peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) FAData.fWord) fiveArr = true ∧
    FAData.aWords.size = 5 ∧
    (∀ j < 5, plettersOK 17 FAData.aWords[j]! = true ∧
      ∀ i < 5, (pword 12 natStrongArr (pinvs 12 natStrongArr) FAData.aWords[j]!)[i]! = i) := by
  have h := fa_nat_cert
  unfold faNatChecks at h
  rw [← natStrongArr_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun k hk => ?_, h3, h4, h5, fun j hj => ?_⟩
  · have := allBelowN_spec h2 hk
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allBelowN_spec h6 hj
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, fun i hi => ?_⟩
    have := allBelowN_spec this.2 hi
    simpa using this

@[expose] def sJ (k : ℕ) : JH := hWordJ FAData.sWords[k]!

@[expose] def fJ : JH := hWordJ FAData.fWord

@[expose] def g3J : JH := seedWordJ FAData.g3Root * hWordJ FAData.g3H

@[expose] def g5J : JH := seedWordJ FAData.g5Root

@[expose] def c1J (j : ℕ) : JH := hWordJ FAData.c1Words[j]!

@[expose] def c3J (j : ℕ) : JH := if j < 6 then hWordJ FAData.c3Words[j]! else g3J

@[expose] def pGenJ (j : ℕ) : JH :=
  if j < 5 then (FAData.pLift[j]!.map fun l => c3J (l - 1)).prod else hWordJ FAData.pKernel

@[expose] def PJ : Subgroup JH := Subgroup.closure (Set.range fun j : Fin 6 => pGenJ j)

@[expose] def aGenJ (j : ℕ) : JH := hWordJ FAData.aWords[j]!

@[expose] def alt5 : Subgroup (alternatingGroup (Fin 12)) :=
  (fixingSubgroup (Perm (Fin 12)) {i : Fin 12 | i.val < 5}).comap
    (alternatingGroup (Fin 12)).subtype

theorem mem_alt5 (σ : alternatingGroup (Fin 12)) :
    σ ∈ alt5 ↔ ∀ i : Fin 12, i.val < 5 → (σ : Perm (Fin 12)) i = i := by
  rw [alt5, Subgroup.mem_comap, mem_fixingSubgroup_iff]
  exact ⟨fun h i hi => h i hi, fun h i hi => h i hi⟩

@[expose] def AH :
    Subgroup HJ := alt5.comap (thetaJ : HJ →* alternatingGroup (Fin 12))

@[expose] def commJ : JH :=
  (aGenJ FAData.iCommIdx)⁻¹ * g5J⁻¹ * aGenJ FAData.iCommIdx * g5J

@[expose] def IJ :
    Subgroup JH := Subgroup.closure ((AH.map HJ.subtype : Set JH) ∪ {commJ})

theorem sJ_mem (k : ℕ) : sJ k ∈ HJ := hWordJ_mem _

theorem fJ_mem : fJ ∈ HJ := hWordJ_mem _

theorem aGenJ_mem (j : ℕ) : aGenJ j ∈ HJ := hWordJ_mem _

theorem thetaJ_sJ
    {k : ℕ} (hk : k < 4) :
    (thetaJ ⟨sJ k, sJ_mem k⟩ : Perm (Fin 12)) = tripleNat (k + 1) := by
  obtain ⟨-, h2, -⟩ := fa_nat_parts
  obtain ⟨hlet, hpeq⟩ := h2 k hk
  have e := thetaJ_hWord FAData.sWords[k]!
  refine e.trans (eq_of_peq (prep_natWord hlet) ?_ hpeq)
  exact prep_tripleArr ⟨k, hk⟩

theorem thetaJ_fJ :
    (thetaJ ⟨fJ, fJ_mem⟩ : Perm (Fin 12)) = fiveNat := by
  obtain ⟨-, -, hlet, hpeq, -⟩ := fa_nat_parts
  exact (thetaJ_hWord FAData.fWord).trans (eq_of_peq (prep_natWord hlet) prep_fiveArr hpeq)

theorem aGenJ_mem_AH
    {j : ℕ} (hj : j < 5) : (⟨aGenJ j, aGenJ_mem j⟩ : HJ) ∈ AH := by
  obtain ⟨-, -, -, -, -, h6⟩ := fa_nat_parts
  obtain ⟨hlet, hfix⟩ := h6 j hj
  show thetaJ ⟨aGenJ j, aGenJ_mem j⟩ ∈ alt5
  rw [mem_alt5]
  intro i hi
  have hrep := prep_natWord hlet i
  rw [hfix i hi] at hrep
  have e : (thetaJ ⟨aGenJ j, aGenJ_mem j⟩ : Perm (Fin 12)) = natWord FAData.aWords[j]! :=
    thetaJ_hWord _
  show (thetaJ ⟨aGenJ j, aGenJ_mem j⟩ : Perm (Fin 12)) i = i
  rw [e]
  exact Fin.ext hrep.symm

theorem fa_data_sizes :
    (∀ k < 4, (FAData.sFixed[k]!).length = [645, 645, 60, 645][k]!) ∧
    FAData.c1Words.size = 8 ∧ FAData.c3Words.size = 6 ∧ FAData.pLift.size = 5 ∧
    FAData.pParents.size = 729 ∧ FAData.pLeft.size = 6 ∧ (∀ j < 6, FAData.pLeft[j]!.size = 729) ∧
    FAData.wRep.size = 48 ∧ FAData.fFixed.length = 50 ∧ FAData.iParents.size = 50 ∧
    FAData.iSchreier.size = 50 ∧ (∀ i < 50, FAData.iSchreier[i]!.size = 6) ∧
    FAData.gamma.size = 50 :=
  Certificates.certificate16041

theorem ctuc_hn_full_automorphism_local_data :
    (∀ k < 4, sJ k ∈ HJ ∧ (thetaJ ⟨sJ k, sJ_mem k⟩ : Perm (Fin 12)) = tripleNat (k + 1)) ∧
    fJ ∈ HJ ∧ (thetaJ ⟨fJ, fJ_mem⟩ : Perm (Fin 12)) = fiveNat ∧
    g3J = seedWordJ FAData.g3Root * hWordJ FAData.g3H ∧ g5J = seedWordJ FAData.g5Root ∧
    PJ = Subgroup.closure (Set.range fun j : Fin 6 => pGenJ j) ∧
    (∀ j < 5, aGenJ j ∈ HJ ∧ (⟨aGenJ j, aGenJ_mem j⟩ : HJ) ∈ AH) ∧
    AH = alt5.comap (thetaJ : HJ →* alternatingGroup (Fin 12)) ∧
    IJ = Subgroup.closure ((AH.map HJ.subtype : Set JH) ∪ {commJ}) ∧
    commJ = (aGenJ 0)⁻¹ * g5J⁻¹ * aGenJ 0 * g5J ∧
    (∀ k < 4, (FAData.sFixed[k]!).length = [645, 645, 60, 645][k]!) ∧
    FAData.c1Words.size = 8 ∧ FAData.c3Words.size = 6 ∧ FAData.pLift.size = 5 ∧
    FAData.pParents.size = 729 ∧ FAData.pLeft.size = 6 ∧ (∀ j < 6, FAData.pLeft[j]!.size = 729) ∧
    FAData.wRep.size = 48 ∧ FAData.fFixed.length = 50 ∧ FAData.iParents.size = 50 ∧
    FAData.iSchreier.size = 50 ∧ (∀ i < 50, FAData.iSchreier[i]!.size = 6) ∧
    FAData.gamma.size = 50 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := fa_data_sizes
  exact ⟨fun k hk => ⟨sJ_mem k, thetaJ_sJ hk⟩, fJ_mem, thetaJ_fJ, rfl, rfl, rfl,
    fun j hj => ⟨aGenJ_mem j, aGenJ_mem_AH hj⟩, rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13⟩

end CFSG.Sporadic.HNSchreier
