module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.MinusFacts
public import Certificates.Certificate1383012
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameCheck
public import CFSG.Timmesfeld.Bridge.Asc72ZAlt
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartThree.MinusFrame
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

private theorem frameCheck_parts (h : frameCheck () = true) :
    t0Check (t0Cert ()) = true ∧
      t0SubCheck (minusEnum ()) = true ∧
      frameMemCheck (t0Cert ()) = true ∧
      frameCommuteCheck () = true ∧
      centCheck () = true ∧
      l0Check () = true ∧
      aCheck () = true ∧
      stabCheck (minusEnum ()) = true ∧
      cardCentralCheck (minusEnum ()) = true ∧
      notMemCheck () = true ∧
      notMulCheck () = true ∧
      conjCommuteCheck (minusEnum ()) = true := by
  simp only [frameCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2,
    h.1.1.2, h.1.2, h.2⟩

private theorem fc : frameCheck () = true := Certificates.certificate1383012

private theorem t0Check_true : t0Check (t0Cert ()) = true := (frameCheck_parts fc).1

private theorem t0SubCheck_true : t0SubCheck (minusEnum ()) = true :=
  (frameCheck_parts fc).2.1

private theorem frameMemCheck_true : frameMemCheck (t0Cert ()) = true :=
  (frameCheck_parts fc).2.2.1

private theorem frameCommuteCheck_true : frameCommuteCheck () = true :=
  (frameCheck_parts fc).2.2.2.1

private theorem centCheck_true : centCheck () = true :=
  (frameCheck_parts fc).2.2.2.2.1

private theorem l0Check_true : l0Check () = true :=
  (frameCheck_parts fc).2.2.2.2.2.1

private theorem aCheck_true : aCheck () = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.1

private theorem stabCheck_true : stabCheck (minusEnum ()) = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.2.1

private theorem cardCentralCheck_true : cardCentralCheck (minusEnum ()) = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.2.2.1

private theorem notMemCheck_true : notMemCheck () = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.2.2.2.1

private theorem notMulCheck_true : notMulCheck () = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.2.2.2.2.1

private theorem conjCommuteCheck_true : conjCommuteCheck (minusEnum ()) = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.2.2.2.2.2

private theorem minusBase_lt : ∀ p ∈ minusBase, p < 65 := by decide

private theorem t0EnumOK : enumOK 65 t0Gens minusBase (t0Cert ()) = true := by
  have h := t0Check_true
  simp only [t0Check, Bool.and_eq_true] at h
  exact h.1

private def frameIdx (i : Fin 3) : Fin 65 :=
  ⟨frameArr[(i : ℕ)]!, by fin_cases i <;> decide⟩

private theorem frameIdx_val (i : Fin 3) : (frameIdx i : ℕ) = frameArr[(i : ℕ)]! := rfl

private theorem frameIdx_injective : Function.Injective frameIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [frameIdx, frameArr]

private theorem isFrame_iff (k : ℕ) : isFrame k = true ↔ ∃ i : Fin 3, (frameIdx i : ℕ) = k := by
  constructor
  · intro h
    simp only [isFrame, List.any_eq_true, List.mem_finRange] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, by rw [frameIdx_val, beq_iff_eq.mp hi]⟩
  · rintro ⟨i, rfl⟩
    simp only [isFrame, List.any_eq_true, List.mem_finRange]
    exact ⟨i, by simp, by simp [frameIdx_val]⟩

private noncomputable def T0sub : Subgroup (Equiv.Perm (Fin 65)) :=
  Subgroup.closure (permsA 65 t0Gens)

private theorem T0sub_card : Nat.card T0sub = 16 := by
  have h := t0Check_true
  simp only [t0Check, Bool.and_eq_true] at h
  obtain ⟨hok, hsz⟩ := h
  obtain ⟨-, hcard, -⟩ := enumOK_spec (n := 65) (gs := t0Gens) (ps := minusBase)
    (c := t0Cert ()) minusBase_lt hok
  unfold T0sub
  rw [hcard, beq_iff_eq.mp hsz]

private theorem T0sub_le : T0sub ≤ minusPerm := by
  rw [T0sub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hany : (minusEnum ()).pts.toList.any (eqA 65 t0Gens[k]!) = true :=
    List.all_eq_true.mp t0SubCheck_true k (List.mem_range.mpr hk)
  rw [List.any_eq_true] at hany
  obtain ⟨a, ha, heq⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (minusEnum ()).pts.size := by simpa using hi
  have hvalid : validA 65 (minusEnum ()).pts[i]! = true := minusEnum_spec.2.2 i hi'
  have hgvalid : validA 65 t0Gens[k]! = true := enumOK_gens_valid t0EnumOK hk
  have heq2 : eqA 65 t0Gens[k]! (minusEnum ()).pts[i]! = true := by
    rw [getElem!_pos (minusEnum ()).pts i hi']
    simpa [Array.getElem_toList] using heq
  have heq' : permOfArr 65 (minusEnum ()).pts[i]! = permOfArr 65 t0Gens[k]! :=
    ((eqA_iff (rep_of_validA hgvalid) (rep_of_validA hvalid)).mp heq2).symm
  exact (minusEnum_spec.1 (permOfArr 65 t0Gens[k]!)).mpr ⟨i, hi', heq'⟩

private theorem factorization_15600_two : 2 ^ (15600).factorization 2 = 16 := by
  have h : (15600).factorization 2 = 4 := by
    have h2 : 15600 = 2 ^ 4 * 975 := by norm_num
    rw [h2, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 975)]
  rw [h]
  norm_num

private noncomputable def T0 : Sylow 2 minusPerm :=
  Sylow.ofCard (T0sub.subgroupOf minusPerm) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0sub_le).toEquiv, T0sub_card,
      card_minusPerm]
    exact factorization_15600_two.symm)

private noncomputable def frameR (i : Fin 3) : minusPerm :=
  ⟨minusRefl (frameIdx i), minusRefl_mem _⟩

private theorem frameR_injective : Function.Injective frameR := by
  intro i j h
  exact frameIdx_injective (minusRefl_injective (Subtype.ext_iff.mp h))

private theorem rep_minusTable (i : Fin 65) : Rep 65 minusTable[(i : ℕ)]! (minusRefl i) :=
  fun x => (minusRefl_apply i x).symm

private theorem mem_T0sub_iff (k : ℕ) (hk : k < 65) :
    minusRefl ⟨k, hk⟩ ∈ T0sub ↔ isFrame k = true := by
  have hck : ((t0Cert ()).pts.toList.any (eqA 65 minusTable[k]!)) = isFrame k := by
    have h := List.all_eq_true.mp frameMemCheck_true k (List.mem_range.mpr hk)
    simpa using (beq_iff_eq.mp h :
      (t0Cert ()).pts.toList.any (eqA 65 minusTable[k]!) = isFrame k)
  have hspec := enumOK_spec (n := 65) (gs := t0Gens) (ps := minusBase)
    (c := t0Cert ()) minusBase_lt t0EnumOK
  have hany : ((t0Cert ()).pts.toList.any (eqA 65 minusTable[k]!)) = true ↔
      minusRefl ⟨k, hk⟩ ∈ T0sub := by
    constructor
    · intro h
      exact enumOK_mem_of_any (n := 65) (gs := t0Gens) (ps := minusBase) (c := t0Cert ())
        minusBase_lt t0EnumOK (rep_minusTable ⟨k, hk⟩) h
    · intro hmem
      obtain ⟨i, hi, hik⟩ := (hspec.1 (minusRefl ⟨k, hk⟩)).1 hmem
      have hval := hspec.2.2 i hi
      rw [List.any_eq_true]
      exact ⟨(t0Cert ()).pts[i]!,
        by rw [getElem!_pos (t0Cert ()).pts i hi]; exact Array.getElem_mem_toList hi,
        (eqA_iff (rep_minusTable ⟨k, hk⟩) (rep_of_validA hval)).mpr hik.symm⟩
  rw [← hany, hck]

private theorem frameR_inter : (T0 : Set minusPerm) ∩ minusClass = Set.range frameR := by
  ext x
  constructor
  · rintro ⟨hT0, hclass⟩
    obtain ⟨k, hk⟩ := hclass
    have hT0' : (x : Equiv.Perm (Fin 65)) ∈ T0sub := hT0
    rw [hk] at hT0'
    obtain ⟨i, hi⟩ := (isFrame_iff (k : ℕ)).mp ((mem_T0sub_iff (k : ℕ) k.2).mp hT0')
    exact ⟨i, Subtype.ext (by
      rw [hk]
      change minusRefl (frameIdx i) = minusRefl k
      exact congrArg minusRefl (Fin.ext hi))⟩
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ⟨frameIdx i, rfl⟩⟩
    change minusRefl (frameIdx i) ∈ T0sub
    exact (mem_T0sub_iff (frameIdx i : ℕ) (frameIdx i).2).mpr ((isFrame_iff _).mpr ⟨i, rfl⟩)

private theorem frameR_commute : ∀ i j, Commute (frameR i) (frameR j) := by
  intro i j
  have hrow := List.all_eq_true.mp frameCommuteCheck_true i (List.mem_finRange i)
  have hrow2 := List.all_eq_true.mp hrow j (List.mem_finRange j)
  have hval : (minusTable[(frameIdx i : ℕ)]!)[(frameIdx j : ℕ)]! = (frameIdx j : ℕ) := by
    rw [frameIdx_val i, frameIdx_val j]
    exact beq_iff_eq.mp hrow2
  have hfix : minusRefl (frameIdx i) (frameIdx j) = frameIdx j := by
    apply Fin.ext
    rw [minusRefl_apply, hval]
  apply Subtype.ext
  exact (commute_minusRefl_iff (frameIdx i) (frameIdx j)).mpr hfix

private noncomputable def t : minusPerm := frameR 0 * frameR 1 * frameR 2

private theorem rep_t : Rep 65 (tArr ()) (t : Equiv.Perm (Fin 65)) := by
  have h0 : Rep 65 minusTable[(frameIdx (0 : Fin 3) : ℕ)]! (minusRefl (frameIdx 0)) :=
    rep_minusTable _
  have h1 : Rep 65 minusTable[(frameIdx (1 : Fin 3) : ℕ)]! (minusRefl (frameIdx 1)) :=
    rep_minusTable _
  have h2 : Rep 65 minusTable[(frameIdx (2 : Fin 3) : ℕ)]! (minusRefl (frameIdx 2)) :=
    rep_minusTable _
  have hprod : Rep 65 (compA 65 (compA 65 minusTable[(frameIdx (0 : Fin 3) : ℕ)]!
      minusTable[(frameIdx (1 : Fin 3) : ℕ)]!) minusTable[(frameIdx (2 : Fin 3) : ℕ)]!)
      (minusRefl (frameIdx 0) * minusRefl (frameIdx 1) * minusRefl (frameIdx 2)) :=
    rep_compA (rep_compA h0 h1) h2
  simpa [tArr, t, frameR, frameIdx_val, Subgroup.coe_mul] using hprod

private theorem commute_iff_commutesA {a b : Array ℕ} {A B : Equiv.Perm (Fin 65)}
    (ha : Rep 65 a A) (hb : Rep 65 b B) : commutesA a b = true ↔ Commute A B := by
  rw [commutesA, eqA_iff (rep_compA ha hb) (rep_compA hb ha)]
  exact (commute_iff_eq A B).symm

private theorem commute_subtype_iff {x y : minusPerm} :
    Commute x y ↔ Commute (x : Equiv.Perm (Fin 65)) (y : Equiv.Perm (Fin 65)) :=
  ⟨fun h => h.map minusPerm.subtype, fun h => Subtype.ext h⟩

private theorem centArr_size : centArr.size = 15 := by decide

private theorem l0Gens_size : l0Gens.size = 15 := by
  rw [l0Gens, Array.size_map]; exact centArr_size

private def centIdx (k : Fin 15) : Fin 65 :=
  ⟨centArr[(k : ℕ)]!, by fin_cases k <;> decide⟩

private theorem centIdx_val (k : Fin 15) : (centIdx k : ℕ) = centArr[(k : ℕ)]! := rfl

private theorem commutesA_cent (i : ℕ) (hi : i < 65) :
    commutesA (tArr ()) (minusTable[i]!) = (centArr.toList.any (fun j => j == i)) := by
  have h := List.all_eq_true.mp centCheck_true i (List.mem_range.mpr hi)
  simpa [centCheck] using h

private theorem mem_centArr_iff {i : ℕ} (hi : i < 65) :
    (centArr.toList.any (fun j => j == i)) = true ↔ ∃ k : Fin 15, (centIdx k : ℕ) = i := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hje⟩
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hj
    have hk15 : k < 15 := by simpa [centArr_size] using hk
    refine ⟨⟨k, hk15⟩, ?_⟩
    rw [centIdx_val]
    rw [getElem!_pos centArr k (by rw [centArr_size]; exact hk15)]
    rw [← Array.getElem_toList (xs := centArr) (i := k)
      (by simpa [centArr_size] using hk15)]
    exact hke.trans (beq_iff_eq.mp hje)
  · rintro ⟨k, rfl⟩
    refine ⟨(centIdx k : ℕ), ?_, by simp⟩
    rw [centIdx_val]
    rw [getElem!_pos centArr (k : ℕ) (by rw [centArr_size]; exact k.isLt)]
    exact Array.getElem_mem_toList (by rw [centArr_size]; exact k.isLt)

private theorem mem_centSet_iff {x : minusPerm} :
    x ∈ centSet minusClass t ↔ ∃ k : Fin 15, x = ⟨minusRefl (centIdx k), minusRefl_mem _⟩ := by
  constructor
  · rintro ⟨hclass, hcomm⟩
    obtain ⟨i, hi⟩ := hclass
    have hcomm' : Commute (⟨minusRefl i, minusRefl_mem i⟩ : minusPerm) t := by
      have hx : x = ⟨minusRefl i, minusRefl_mem i⟩ := Subtype.ext hi
      rw [hx] at hcomm
      exact hcomm
    have hcommA : commutesA (tArr ()) (minusTable[(i : ℕ)]!) = true := by
      refine (commute_iff_commutesA rep_t (rep_minusTable i)).mpr ?_
      exact (hcomm'.map minusPerm.subtype).symm
    have hcent : (centArr.toList.any (fun j => j == (i : ℕ))) = true := by
      rw [← commutesA_cent (i : ℕ) i.isLt, hcommA]
    obtain ⟨k, hk⟩ := (mem_centArr_iff i.isLt).mp hcent
    have hik : i = centIdx k := Fin.ext hk.symm
    have hx : x = ⟨minusRefl i, minusRefl_mem i⟩ := Subtype.ext hi
    exact ⟨k, by rw [hx, hik]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨centIdx k, rfl⟩, ?_⟩
    have hcent : (centArr.toList.any (fun j => j == (centIdx k : ℕ))) = true :=
      (mem_centArr_iff (centIdx k).isLt).mpr ⟨k, rfl⟩
    have hA : commutesA (tArr ()) (minusTable[(centIdx k : ℕ)]!) = true := by
      rw [commutesA_cent (centIdx k : ℕ) (centIdx k).isLt]
      exact hcent
    have hcomm := (commute_iff_commutesA rep_t (rep_minusTable (centIdx k))).mp hA
    exact commute_subtype_iff.mpr hcomm.symm

private noncomputable def L0sub : Subgroup (Equiv.Perm (Fin 65)) :=
  Subgroup.closure (permsA 65 l0Gens)

private theorem l0Gens_get (k : Fin 15) : l0Gens[(k : ℕ)]! = minusTable[(centIdx k : ℕ)]! := by
  rw [l0Gens, getElem!_pos _ _ (by rw [Array.size_map, centArr_size]; exact k.isLt)]
  rw [Array.getElem_map]
  rw [centIdx_val, getElem!_pos centArr (k : ℕ) (by rw [centArr_size]; exact k.isLt)]

private theorem L0sub_le : L0sub ≤ minusPerm := by
  rw [L0sub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk15 : k < 15 := by simpa [l0Gens_size] using hk
  change permOfArr 65 l0Gens[k]! ∈ (minusPerm : Set (Equiv.Perm (Fin 65)))
  have hgen : permOfArr 65 l0Gens[k]! = minusRefl (centIdx ⟨k, hk15⟩) := by
    rw [l0Gens_get ⟨k, hk15⟩]
    rfl
  rw [hgen]
  exact minusRefl_mem _

private theorem localGroup_eq : localGroup minusClass t = L0sub.subgroupOf minusPerm := by
  apply le_antisymm
  · rw [localGroup, Subgroup.closure_le]
    rintro x hx
    change (x : Equiv.Perm (Fin 65)) ∈ L0sub
    obtain ⟨k, rfl⟩ := mem_centSet_iff.mp hx
    rw [L0sub]
    have hmem : minusRefl (centIdx k) ∈ permsA 65 l0Gens := by
      rw [show minusRefl (centIdx k) = permOfArr 65 l0Gens[(k : ℕ)]! from by
        rw [l0Gens_get k]; rfl]
      exact mem_permsA (by rw [l0Gens_size]; exact k.isLt)
    exact Subgroup.subset_closure hmem
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hle : L0sub ≤ (localGroup minusClass t).map minusPerm.subtype := by
      rw [L0sub, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      have hk15 : k < 15 := by simpa [l0Gens_size] using hk
      change permOfArr 65 l0Gens[k]! ∈ (localGroup minusClass t).map minusPerm.subtype
      have hgen : permOfArr 65 l0Gens[k]! = minusRefl (centIdx ⟨k, hk15⟩) := by
        rw [l0Gens_get ⟨k, hk15⟩]
        rfl
      rw [hgen]
      exact Subgroup.mem_map_of_mem minusPerm.subtype
        (Subgroup.subset_closure (mem_centSet_iff.mpr ⟨⟨k, hk15⟩, rfl⟩))
    have hmem := hle hx
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy

private theorem L0sub_card : Nat.card L0sub = 120 := by
  have h := l0Check_true
  simp only [l0Check, Bool.and_eq_true] at h
  obtain ⟨⟨hok, hsz⟩, -⟩ := h
  have hcard := (enumOK_spec (n := 65) (gs := l0Gens) (ps := minusBase)
    (c := l0Cert ()) minusBase_lt hok).2.1
  rw [L0sub, hcard, beq_iff_eq.mp hsz]

private theorem frameR_not_mem : t ∉ minusClass := by
  rintro ⟨i, hi⟩
  have h := List.all_eq_true.mp notMemCheck_true (i : ℕ) (List.mem_range.mpr i.isLt)
  have hne : eqA 65 (tArr ()) minusTable[(i : ℕ)]! = false := by
    simpa [notMemCheck] using h
  have heq : eqA 65 (tArr ()) minusTable[(i : ℕ)]! = true :=
    (eqA_iff rep_t (rep_minusTable i)).mpr (by simpa using hi)
  rw [heq] at hne
  exact Bool.noConfusion hne

private theorem frameR_not_mul :
    ∀ a ∈ centSet minusClass t, ∀ b ∈ centSet minusClass t, a * b ≠ t := by
  intro a ha b hb hab
  obtain ⟨ka, rfl⟩ := mem_centSet_iff.mp ha
  obtain ⟨kb, rfl⟩ := mem_centSet_iff.mp hb
  have h := List.all_eq_true.mp (List.all_eq_true.mp notMulCheck_true ka (List.mem_finRange ka))
    kb (List.mem_finRange kb)
  have hne : eqA 65 (compA 65 minusTable[(centIdx ka : ℕ)]! minusTable[(centIdx kb : ℕ)]!)
      (tArr ()) = false := by
    simpa [notMulCheck, centIdx_val] using h
  have hrep : Rep 65 (compA 65 minusTable[(centIdx ka : ℕ)]! minusTable[(centIdx kb : ℕ)]!)
      (minusRefl (centIdx ka) * minusRefl (centIdx kb)) :=
    rep_compA (rep_minusTable _) (rep_minusTable _)
  have heq : eqA 65 (compA 65 minusTable[(centIdx ka : ℕ)]! minusTable[(centIdx kb : ℕ)]!)
      (tArr ()) = true := by
    refine (eqA_iff hrep rep_t).mpr ?_
    have hcoe : ((⟨minusRefl (centIdx ka), minusRefl_mem _⟩ *
        ⟨minusRefl (centIdx kb), minusRefl_mem _⟩ : minusPerm) : Equiv.Perm (Fin 65)) =
        minusRefl (centIdx ka) * minusRefl (centIdx kb) := rfl
    rw [← hcoe, hab]
  rw [heq] at hne
  exact Bool.noConfusion hne

private theorem frameR_conj_commute :
    ∃ x : minusPerm, x * t * x⁻¹ ≠ t ∧ Commute t (x * t * x⁻¹) := by
  have hvalid : validA 65 xArr = true := by
    have h := conjCommuteCheck_true
    simp only [conjCommuteCheck, Bool.and_eq_true] at h
    exact h.1.1.1
  have hne : eqA 65 (compA 65 (compA 65 xArr (tArr ())) (invCand 65 xArr)) (tArr ()) = false := by
    have h := conjCommuteCheck_true
    simp only [conjCommuteCheck, Bool.and_eq_true] at h
    simpa using h.1.1.2
  have hcomm : commutesA (tArr ())
      (compA 65 (compA 65 xArr (tArr ())) (invCand 65 xArr)) = true := by
    have h := conjCommuteCheck_true
    simp only [conjCommuteCheck, Bool.and_eq_true] at h
    exact h.1.2
  have hmem : (minusEnum ()).pts.toList.any (eqA 65 xArr) = true := by
    have h := conjCommuteCheck_true
    simp only [conjCommuteCheck, Bool.and_eq_true] at h
    exact h.2
  have hmem' : permOfArr 65 xArr ∈ minusPerm := by
    rw [minusEnum_spec.1]
    rw [List.any_eq_true] at hmem
    obtain ⟨a, ha, heq⟩ := hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hi' : i < (minusEnum ()).pts.size := by simpa using hi
    have hval : validA 65 (minusEnum ()).pts[i]! = true := minusEnum_spec.2.2 i hi'
    refine ⟨i, hi', ?_⟩
    have heq' : eqA 65 xArr ((minusEnum ()).pts[i]!) = true := by
      rw [getElem!_pos (minusEnum ()).pts i hi']
      simpa [Array.getElem_toList] using heq
    exact ((eqA_iff (rep_of_validA hvalid) (rep_of_validA hval)).mp heq').symm
  let x : minusPerm := ⟨permOfArr 65 xArr, hmem'⟩
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hrep : Rep 65 (compA 65 (compA 65 xArr (tArr ())) (invCand 65 xArr))
        ((x : Equiv.Perm (Fin 65)) * (t : Equiv.Perm (Fin 65)) * (x : Equiv.Perm (Fin 65))⁻¹) := by
      exact rep_compA (rep_compA (rep_of_validA hvalid) rep_t) (rep_inv_of_validA hvalid)
    have heq : eqA 65 (compA 65 (compA 65 xArr (tArr ())) (invCand 65 xArr)) (tArr ()) = true :=
      (eqA_iff hrep rep_t).mpr (by
        have := congrArg Subtype.val hx
        simpa [x, Subgroup.coe_mul, Subgroup.coe_inv] using this)
    rw [heq] at hne
    exact Bool.noConfusion hne
  · exact commute_subtype_iff.mpr ((commute_iff_commutesA rep_t
      (rep_compA (rep_compA (rep_of_validA hvalid) rep_t) (rep_inv_of_validA hvalid))).mp hcomm)

private theorem conj_subtype_minusRefl (g : minusPerm) (k : Fin 65) :
    g * ⟨minusRefl k, minusRefl_mem k⟩ * g⁻¹ =
      ⟨minusRefl ((g : Equiv.Perm (Fin 65)) k), minusRefl_mem _⟩ := by
  apply Subtype.ext
  change (g : Equiv.Perm (Fin 65)) * minusRefl k * (g : Equiv.Perm (Fin 65))⁻¹ =
    minusRefl ((g : Equiv.Perm (Fin 65)) k)
  exact conj_minusRefl g.2 k

private theorem mem_localGroup_of_mem_L0sub {g : Equiv.Perm (Fin 65)} (hg : g ∈ L0sub) :
    (⟨g, L0sub_le hg⟩ : minusPerm) ∈ localGroup minusClass t := by
  rw [localGroup_eq]
  exact hg

private theorem frameR_centralizer :
    ∀ x : minusPerm, (∀ y ∈ centSet minusClass t, Commute x y) → x = 1 ∨ x = t := by
  intro x hx
  have hfix : ∀ k : Fin 15, (x : Equiv.Perm (Fin 65)) (centIdx k) = centIdx k := by
    intro k
    have hmem : (⟨minusRefl (centIdx k), minusRefl_mem _⟩ : minusPerm) ∈ centSet minusClass t :=
      mem_centSet_iff.mpr ⟨k, rfl⟩
    have hc : Commute (x : Equiv.Perm (Fin 65)) (minusRefl (centIdx k)) :=
      commute_subtype_iff.mp
        (hx (⟨minusRefl (centIdx k), minusRefl_mem (centIdx k)⟩ : minusPerm) hmem)
    have h1 : (x : Equiv.Perm (Fin 65)) * minusRefl (centIdx k) *
        (x : Equiv.Perm (Fin 65))⁻¹ = minusRefl (centIdx k) := by
      rw [commute_iff_eq] at hc
      rw [hc]
      group
    have h2 := conj_minusRefl x.2 (centIdx k)
    rw [h2] at h1
    exact minusRefl_injective h1
  obtain ⟨i, hi, hxi⟩ := (minusEnum_spec.1 x).1 x.2
  have hfixi : (List.finRange 15).all
      (fun k => ((minusEnum ()).pts[i]!)[centArr[(k : ℕ)]!]! == centArr[(k : ℕ)]!) = true := by
    rw [List.all_eq_true]
    intro k _
    have hxk : (permOfArr 65 ((minusEnum ()).pts[i]!)) (centIdx k) = centIdx k := by
      rw [hxi]; exact hfix k
    have hval := rep_of_validA (minusEnum_spec.2.2 i hi) (centIdx k)
    rw [hxk] at hval
    rw [centIdx_val] at hval
    exact beq_iff_eq.mpr hval
  have hstab := allLt_spec stabCheck_true hi
  simp only [MinusFrame.stabCheck] at hstab
  rw [hfixi] at hstab
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hstab
  rcases hstab with h1 | ht
  · left
    apply Subtype.ext
    rw [← hxi]
    exact (eqA_iff (rep_of_validA (minusEnum_spec.2.2 i hi)) rep_idA).mp h1
  · right
    apply Subtype.ext
    rw [← hxi]
    exact (eqA_iff (rep_of_validA (minusEnum_spec.2.2 i hi)) rep_t).mp ht

private theorem frameR_transitive :
    ∀ x ∈ centSet minusClass t, ∀ y ∈ centSet minusClass t,
      ∃ g ∈ localGroup minusClass t, g * x * g⁻¹ = y := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_centSet_iff.mp hx
  obtain ⟨b, rfl⟩ := mem_centSet_iff.mp hy
  have htrans := l0Check_true
  simp only [l0Check, Bool.and_eq_true] at htrans
  obtain ⟨⟨hok, _⟩, htrans'⟩ := htrans
  have hany := List.all_eq_true.mp
    (List.all_eq_true.mp htrans' a (List.mem_finRange a)) b (List.mem_finRange b)
  rw [List.any_eq_true] at hany
  obtain ⟨garr, hgmem, hgeq⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgmem
  have hi' : i < (l0Cert ()).pts.size := by simpa using hi
  have hvalid : validA 65 (l0Cert ()).pts[i]! = true :=
    (enumOK_spec (n := 65) (gs := l0Gens) (ps := minusBase) (c := l0Cert ())
      minusBase_lt hok).2.2 i hi'
  have hgL : permOfArr 65 ((l0Cert ()).pts[i]!) ∈ L0sub :=
    enumOK_mem (n := 65) (gs := l0Gens) (ps := minusBase) (c := l0Cert ())
      minusBase_lt hok hi' (rep_of_validA hvalid)
  have hgeq' : ((l0Cert ()).pts[i]!)[centArr[(a : ℕ)]!]! = centArr[(b : ℕ)]! := by
    rw [getElem!_pos (l0Cert ()).pts i hi']
    rw [← Array.getElem_toList (xs := (l0Cert ()).pts) (i := i) (by simpa using hi')]
    exact beq_iff_eq.mp hgeq
  refine ⟨⟨permOfArr 65 ((l0Cert ()).pts[i]!), L0sub_le hgL⟩,
    mem_localGroup_of_mem_L0sub hgL, ?_⟩
  rw [conj_subtype_minusRefl]
  apply Subtype.ext
  rw [minusRefl_injective.eq_iff]
  apply Fin.ext
  rw [← rep_of_validA hvalid (centIdx a)]
  rw [centIdx_val a, centIdx_val b]
  exact hgeq'

private theorem card_filter_fin_eq_length_filter {α : Type} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin l.length => p (l.get i))).card = (l.filter p).length := by
  rw [← List.countP_eq_length_filter]
  induction l with
  | nil =>
      rw [List.countP_nil]
      refine Nat.eq_zero_of_le_zero ?_
      calc (Finset.univ.filter (fun i : Fin 0 => p (([].get i)))).card
          ≤ (Finset.univ : Finset (Fin 0)).card := Finset.card_filter_le _ _
        _ = 0 := by simp
  | cons a l ih =>
      rw [List.countP_cons]
      rw [show (Finset.univ.filter (fun i : Fin (a :: l).length => p ((a :: l).get i))).card =
          ∑ i : Fin (a :: l).length, ite (p ((a :: l).get i)) 1 0 from Finset.card_filter _ _]
      rw [show (∑ i : Fin (a :: l).length, ite (p ((a :: l).get i)) 1 0) =
          ∑ i : Fin (l.length + 1), ite (p ((a :: l).get i)) 1 0 from rfl]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero]
      rw [show (∑ i : Fin l.length, ite (p ((a :: l).get i.succ)) 1 0) =
          ∑ i : Fin l.length, ite (p (l.get i)) 1 0 from
        Finset.sum_congr rfl fun i _ => by rw [List.get_cons_succ']]
      rw [← Finset.card_filter (fun i : Fin l.length => p (l.get i)) Finset.univ]
      rw [ih]
      by_cases h : p a = true <;> simp [h, Nat.add_comm]

private theorem card_filter_array_eq_length_filter {α : Type} [Inhabited α]
    (a : Array α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin a.size => p a[i]!)).card = (a.toList.filter p).length := by
  rw [← card_filter_fin_eq_length_filter a.toList p]
  apply Finset.card_bij (fun i _ => Fin.cast (Array.length_toList (xs := a)).symm i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h1 : a[i]! = a.toList.get (Fin.cast (Array.length_toList (xs := a)).symm i) := by
      rw [List.get_eq_getElem, Array.getElem_toList, getElem!_pos a i i.isLt]
      rfl
    rwa [← h1]
  · intro i _ j _ hij
    exact Fin.cast_injective _ hij
  · intro j hj
    refine ⟨Fin.cast (Array.length_toList (xs := a)) j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have h1 : a[Fin.cast (Array.length_toList (xs := a)) j]! =
          a.toList.get (Fin.cast (Array.length_toList (xs := a)).symm
            (Fin.cast (Array.length_toList (xs := a)) j)) := by
        rw [List.get_eq_getElem, Array.getElem_toList, getElem!_pos a _ (Fin.cast _ j).isLt]
        congr 1
      rw [h1]
      convert hj using 2
      simp
    · simp

private noncomputable def enumPerm (i : Fin (minusEnum ()).pts.size) : minusPerm :=
  ⟨permOfArr 65 ((minusEnum ()).pts[i]!), (minusEnum_spec.1 _).2 ⟨i, i.2, rfl⟩⟩

private theorem enumPerm_surjective : Function.Surjective enumPerm := by
  intro x
  obtain ⟨i, hi, hix⟩ := (minusEnum_spec.1 x).1 x.2
  exact ⟨⟨i, hi⟩, Subtype.ext hix⟩

private noncomputable def enumEquiv : Fin (minusEnum ()).pts.size ≃ minusPerm :=
  Equiv.ofBijective enumPerm (by
    haveI : Fintype minusPerm := Fintype.ofFinite _
    rw [Fintype.bijective_iff_surjective_and_card]
    exact ⟨enumPerm_surjective, by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_minusPerm, minusEnum_spec.2.1]⟩)

private theorem frameR_card_centralizer :
    Nat.card (Subgroup.centralizer ({t} : Set minusPerm)) = 240 := by
  classical
  haveI : Fintype minusPerm := Fintype.ofFinite _
  haveI : Fintype (Subgroup.centralizer ({t} : Set minusPerm)) := Fintype.ofFinite _
  have hcount := cardCentralCheck_true
  simp only [cardCentralCheck, Bool.and_eq_true, beq_iff_eq] at hcount
  rw [← hcount]
  rw [Nat.card_eq_fintype_card]
  haveI : Fintype {i : Fin (minusEnum ()).pts.size //
      enumPerm i ∈ Subgroup.centralizer ({t} : Set minusPerm)} := Fintype.ofFinite _
  rw [show Fintype.card (Subgroup.centralizer ({t} : Set minusPerm)) =
      Fintype.card {i : Fin (minusEnum ()).pts.size //
        enumPerm i ∈ Subgroup.centralizer ({t} : Set minusPerm)} from
    Fintype.card_congr (enumEquiv.subtypeEquiv (fun i => Iff.rfl)).symm]
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter (fun i : Fin (minusEnum ()).pts.size =>
      enumPerm i ∈ Subgroup.centralizer ({t} : Set minusPerm))) =
      (Finset.univ.filter (fun i : Fin (minusEnum ()).pts.size =>
        commutesA ((minusEnum ()).pts[i]!) (tArr ()))) from by
    congr 1
    ext i
    rw [Subgroup.mem_centralizer_singleton_iff]
    change Commute (enumPerm i) t ↔ commutesA ((minusEnum ()).pts[i]!) (tArr ()) = true
    rw [commute_subtype_iff]
    exact (commute_iff_commutesA (rep_of_validA (minusEnum_spec.2.2 i i.2)) rep_t).symm]
  exact card_filter_array_eq_length_filter (minusEnum ()).pts (fun g => commutesA g (tArr ()))

private theorem l0Check_parts :
    enumOK 65 l0Gens minusBase (l0Cert ()) = true ∧ (l0Cert ()).pts.size = 120 ∧
      ((List.finRange 15).all fun a => (List.finRange 15).all fun b =>
        (l0Cert ()).pts.toList.any fun g =>
          g[centArr[(a : ℕ)]!]! == centArr[(b : ℕ)]!) = true := by
  have h := l0Check_true
  simp only [l0Check, Bool.and_eq_true] at h
  exact ⟨h.1.1, beq_iff_eq.mp h.1.2, h.2⟩

private theorem aCheck_parts :
    enumOK 65 aGens minusBase (aCert ()) = true ∧ (aCert ()).pts.size = 60 ∧
      (aCert ()).pts.toList.all (fun g => !(eqA 65 g (tArr ()))) = true ∧
      aGens.toList.all (fun a => (l0Cert ()).pts.toList.any (eqA 65 a)) = true ∧
      conjSimpleOK 65 minusBase (aCert ()) = true := by
  have h := aCheck_true
  simp only [aCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, beq_iff_eq.mp h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private noncomputable def Asubperm : Subgroup (Equiv.Perm (Fin 65)) :=
  Subgroup.closure (permsA 65 aGens)

private theorem Asubperm_card : Nat.card Asubperm = 60 := by
  obtain ⟨hok, hsz, -, -, -⟩ := aCheck_parts
  have hcard := (enumOK_spec (n := 65) (gs := aGens) (ps := minusBase) (c := aCert ())
    minusBase_lt hok).2.1
  rw [Asubperm, hcard, hsz]

private theorem Asubperm_simple : IsSimpleGroup Asubperm := by
  obtain ⟨hok, hsz, -, -, hsimple⟩ := aCheck_parts
  refine isSimpleGroup_of_conjSimpleOK (n := 65) (gs := aGens) (ps := minusBase)
    (c := aCert ()) minusBase_lt hok ?_ hsimple
  rw [hsz]; norm_num

private theorem Asubperm_le : Asubperm ≤ L0sub := by
  obtain ⟨-, -, -, hsub, -⟩ := aCheck_parts
  obtain ⟨hok_l0, -, -⟩ := l0Check_parts
  rw [Asubperm, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hgvalid : validA 65 aGens[k]! = true := enumOK_gens_valid aCheck_parts.1 hk
  have hmem : aGens[k]! ∈ aGens.toList := by
    rw [getElem!_pos aGens k hk]; exact Array.getElem_mem_toList hk
  have hany : (l0Cert ()).pts.toList.any (eqA 65 aGens[k]!) = true :=
    List.all_eq_true.mp hsub _ hmem
  exact enumOK_mem_of_any (n := 65) (gs := l0Gens) (ps := minusBase) (c := l0Cert ())
    minusBase_lt hok_l0 (rep_of_validA hgvalid) hany

private theorem Asubperm_not_t : ((t : minusPerm) : Equiv.Perm (Fin 65)) ∉ Asubperm := by
  obtain ⟨hok, -, hnotT, -, -⟩ := aCheck_parts
  intro hmem
  obtain ⟨i, hi, hix⟩ := (enumOK_spec (n := 65) (gs := aGens) (ps := minusBase) (c := aCert ())
    minusBase_lt hok).1 _ |>.1 hmem
  have hval : (aCert ()).pts[i]! ∈ (aCert ()).pts.toList := by
    rw [getElem!_pos (aCert ()).pts i hi]; exact Array.getElem_mem_toList hi
  have hfalse : eqA 65 ((aCert ()).pts[i]!) (tArr ()) = false := by
    have h := List.all_eq_true.mp hnotT _ hval
    simpa using h
  have htrue : eqA 65 ((aCert ()).pts[i]!) (tArr ()) = true :=
    (eqA_iff (rep_of_validA ((enumOK_spec (n := 65) (gs := aGens) (ps := minusBase)
      (c := aCert ()) minusBase_lt hok).2.2 i hi)) rep_t).mpr hix
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

private theorem mem_frameR_centSet (i : Fin 3) :
    frameR i ∈ centSet minusClass t := by
  refine ⟨⟨frameIdx i, rfl⟩, ?_⟩
  unfold t
  exact (frameR_commute i 0).mul_right
    ((frameR_commute i 1).mul_right (frameR_commute i 2))

private theorem t_mem_localGroup : t ∈ localGroup minusClass t := by
  rw [localGroup]
  change frameR 0 * frameR 1 * frameR 2 ∈ Subgroup.closure (centSet minusClass t)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.subset_closure (mem_frameR_centSet 0))
    (Subgroup.subset_closure (mem_frameR_centSet 1)))
    (Subgroup.subset_closure (mem_frameR_centSet 2))

private theorem tL_mem_center :
    (⟨t, t_mem_localGroup⟩ : localGroup minusClass t) ∈
      Subgroup.center (localGroup minusClass t) := by
  have hmain : ∀ z ∈ Subgroup.closure (centSet minusClass t), Commute t z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem w hw => exact hw.2.symm
    | one => exact Commute.one_right t
    | mul a b _ _ iha ihb => exact iha.mul_right ihb
    | inv a _ iha => exact iha.inv_right
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (hmain (y : minusPerm) y.2).symm

private theorem mem_center_localGroup_iff {x : localGroup minusClass t} :
    x ∈ Subgroup.center (localGroup minusClass t) ↔
      (x : minusPerm) = 1 ∨ (x : minusPerm) = t := by
  constructor
  · intro hx
    exact frameR_centralizer (x : minusPerm) (fun y hy => by
      have := Subgroup.mem_center_iff.mp hx
        (⟨y, Subgroup.subset_closure hy⟩ : localGroup minusClass t)
      exact (congrArg Subtype.val this).symm)
  · rintro (h1 | ht)
    · have hx1 : x = 1 := Subtype.ext h1
      rw [hx1]; exact Subgroup.one_mem _
    · have hx1 : x = ⟨t, t_mem_localGroup⟩ := Subtype.ext ht
      rw [hx1]; exact tL_mem_center

private theorem center_localGroup_eq :
    Subgroup.center (localGroup minusClass t) =
      Subgroup.zpowers (⟨t, t_mem_localGroup⟩ : localGroup minusClass t) := by
  apply le_antisymm
  · intro x hx
    rcases (mem_center_localGroup_iff.mp hx) with h1 | ht
    · have hx1 : x = 1 := Subtype.ext h1
      rw [hx1]; exact Subgroup.one_mem _
    · have hx1 : x = ⟨t, t_mem_localGroup⟩ := Subtype.ext ht
      rw [hx1]; exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr tL_mem_center

private theorem orderOf_t : orderOf t = 2 := by
  apply orderOf_eq_prime
  · have h0 : frameR 0 ^ 2 = 1 := Subtype.ext (minusRefl_mul_self (frameIdx 0))
    have h1 : frameR 1 ^ 2 = 1 := Subtype.ext (minusRefl_mul_self (frameIdx 1))
    have h2 : frameR 2 ^ 2 = 1 := Subtype.ext (minusRefl_mul_self (frameIdx 2))
    have habc : Commute (frameR 0) (frameR 1 * frameR 2) :=
      (frameR_commute 0 1).mul_right (frameR_commute 0 2)
    have hbc : Commute (frameR 1) (frameR 2) := frameR_commute 1 2
    unfold t
    rw [show frameR 0 * frameR 1 * frameR 2 = frameR 0 * (frameR 1 * frameR 2) from
      mul_assoc _ _ _]
    rw [habc.mul_pow, hbc.mul_pow, h0, h1, h2, mul_one, one_mul]
  · intro h
    exact Asubperm_not_t (by rw [h]; exact Asubperm.one_mem)

private theorem orderOf_tL :
    orderOf (⟨t, t_mem_localGroup⟩ : localGroup minusClass t) = 2 := by
  apply orderOf_eq_prime
  · have h2 : t ^ 2 = 1 := by
      rw [← orderOf_t]; exact pow_orderOf_eq_one t
    apply Subtype.ext
    show t ^ 2 = (1 : minusPerm)
    exact h2
  · intro h
    have ht1 : (t : Equiv.Perm (Fin 65)) = 1 := by
      have h1 := congrArg (fun x : localGroup minusClass t => (x : minusPerm)) h
      exact congrArg (fun x : minusPerm => (x : Equiv.Perm (Fin 65))) h1
    exact Asubperm_not_t (by rw [ht1]; exact Asubperm.one_mem)

private theorem card_center_localGroup :
    Nat.card (Subgroup.center (localGroup minusClass t)) = 2 := by
  rw [center_localGroup_eq, Nat.card_zpowers, orderOf_tL]

private theorem card_localGroup : Nat.card (localGroup minusClass t) = 120 := by
  rw [localGroup_eq]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe L0sub_le).toEquiv]
  exact L0sub_card

private noncomputable def AsubToL : Asubperm →* localGroup minusClass t where
  toFun a := ⟨⟨(a : Equiv.Perm (Fin 65)), L0sub_le (Asubperm_le a.2)⟩,
    by rw [localGroup_eq]; exact Asubperm_le a.2⟩
  map_one' := rfl
  map_mul' := fun x y => rfl

private noncomputable def phi : Asubperm →* (localGroup minusClass t ⧸
    Subgroup.center (localGroup minusClass t)) :=
  (QuotientGroup.mk' (Subgroup.center (localGroup minusClass t))).comp AsubToL

private theorem phi_injective : Function.Injective phi := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have hmem : AsubToL a ∈ Subgroup.center (localGroup minusClass t) := by
    rw [← QuotientGroup.eq_one_iff]
    exact ha
  rcases (mem_center_localGroup_iff.mp hmem) with h1 | ht
  · apply Subtype.ext
    change (a : Equiv.Perm (Fin 65)) = (1 : Equiv.Perm (Fin 65))
    exact congrArg (fun x : minusPerm => (x : Equiv.Perm (Fin 65))) h1
  · exfalso
    exact Asubperm_not_t (by rw [← ht]; exact a.2)

private theorem card_quotient :
    Nat.card (localGroup minusClass t ⧸ Subgroup.center (localGroup minusClass t)) = 60 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (localGroup minusClass t))
  rw [card_localGroup, card_center_localGroup] at h
  omega

private theorem phi_bijective : Function.Bijective phi := by
  haveI : Fintype Asubperm := Fintype.ofFinite _
  haveI : Fintype (localGroup minusClass t ⧸ Subgroup.center (localGroup minusClass t)) :=
    Fintype.ofFinite _
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨phi_injective, by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Asubperm_card, card_quotient]⟩

private noncomputable def AsubEquivQuotient :
    Asubperm ≃* (localGroup minusClass t ⧸
      Subgroup.center (localGroup minusClass t)) :=
  MulEquiv.ofBijective phi phi_bijective

private theorem frameR_bender :
    Nonempty (localGroup minusClass t ⧸
      Subgroup.center (localGroup minusClass t) ≃* CFSG.Theory.Comparator.PSL2Model 2) := by
  haveI : IsSimpleGroup Asubperm := Asubperm_simple
  obtain ⟨eA⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := Asubperm) Asubperm_card
  haveI : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model 2) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup
      (CFSG.BenderSuzuki.IsBenderGroup.isPSL2 2 (by norm_num) (MulEquiv.refl _))
  obtain ⟨eP⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := CFSG.Theory.Comparator.PSL2Model 2) (by
      rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (m := 2) (by norm_num)]
      norm_num)
  exact ⟨AsubEquivQuotient.symm.trans (eA.trans eP.symm)⟩

private theorem frame_T0 : O4MinusFrame minusClass (T0 : Subgroup minusPerm) frameR := by
  exact ⟨frameR_injective, frameR_inter, frameR_commute, frameR_transitive,
    frameR_bender, frameR_centralizer, frameR_card_centralizer, frameR_not_mem,
    frameR_not_mul, frameR_conj_commute⟩

private theorem conj_mem_minusClass (g : minusPerm) {x : minusPerm} (hx : x ∈ minusClass) :
    MulAut.conj g x ∈ minusClass := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨(g : Equiv.Perm (Fin 65)) k, ?_⟩
  rw [MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hk]
  exact conj_minusRefl g.2 k

private theorem conj_image_minusClass (g : minusPerm) :
    (MulAut.conj g) '' minusClass = minusClass := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact conj_mem_minusClass g hx
  · intro hy
    exact ⟨MulAut.conj g⁻¹ y, conj_mem_minusClass g⁻¹ hy, by
      simp only [MulAut.conj_apply]
      group⟩

theorem minusPerm_frame : ∀ T : Sylow 2 minusPerm, ∃ r : Fin 3 → minusPerm,
    O4MinusFrame minusClass (T : Subgroup minusPerm) r := by
  intro T
  haveI : Finite (Sylow 2 minusPerm) := inferInstance
  haveI := Sylow.isPretransitive_of_finite (p := 2) (G := minusPerm)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq minusPerm T0 T
  refine ⟨fun i => MulAut.conj g (frameR i), ?_⟩
  have hmap := O4MinusFrame.map (MulAut.conj g) (conj_image_minusClass g) frame_T0
  have hT : (T : Subgroup minusPerm) =
      (T0 : Subgroup minusPerm).map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 minusPerm => (P : Subgroup minusPerm)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    rw [← h1]
    rfl
  simpa [hT] using hmap

end CFSG.OddTranspositions.PartThree
