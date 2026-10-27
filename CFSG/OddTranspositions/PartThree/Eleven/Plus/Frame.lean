module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Perm
public import CFSG.OddTranspositions.PartThree.Eleven.PlusFacts
public import Certificates.Certificate1383004

import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.OddTranspositions.PartThree.PlusFrame

private theorem frameCheck_parts (h : frameCheck () = true) :
    t0Check (t0Cert ()) = true ∧ t0SubCheck (plusEnum ()) = true ∧
      frameMemCheck (t0Cert ()) = true ∧
      frameProdCheck () = true ∧ cardCheck () = true ∧
      evenCheck (plusEnum ()) = true ∧ alternatingCheck (plusEnum ()) = true ∧
      autCheck () = true ∧ derivValidCheck () = true := by
  simp only [frameCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem fc : frameCheck () = true := Certificates.certificate1383004

private theorem t0Check_true : t0Check (t0Cert ()) = true := (frameCheck_parts fc).1

private theorem t0SubCheck_true : t0SubCheck (plusEnum ()) = true := (frameCheck_parts fc).2.1

private theorem frameMemCheck_true : frameMemCheck (t0Cert ()) = true :=
  (frameCheck_parts fc).2.2.1

private theorem frameProdCheck_true : frameProdCheck () = true := (frameCheck_parts fc).2.2.2.1

private theorem cardCheck_true : cardCheck () = true := (frameCheck_parts fc).2.2.2.2.1

private theorem evenCheck_true : evenCheck (plusEnum ()) = true :=
  (frameCheck_parts fc).2.2.2.2.2.1

private theorem alternatingCheck_true : alternatingCheck (plusEnum ()) = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.1

private theorem autCheck_true : autCheck () = true := (frameCheck_parts fc).2.2.2.2.2.2.2.1

private theorem derivValidCheck_true : derivValidCheck () = true :=
  (frameCheck_parts fc).2.2.2.2.2.2.2.2

private theorem t0EnumOK_true : enumOK 60 t0Gens plusBase (t0Cert ()) = true := by
  have h := t0Check_true
  simp only [t0Check, Bool.and_eq_true] at h
  exact h.1

private theorem plusBase_lt : ∀ p ∈ plusBase, p < 60 := by decide

private def frameIdx (i : Fin 4) : Fin 60 :=
  ⟨frameArr[(i : ℕ)]!, by fin_cases i <;> decide⟩

private theorem frameIdx_val (i : Fin 4) : (frameIdx i : ℕ) = frameArr[(i : ℕ)]! := rfl

private theorem frameIdx_injective : Function.Injective frameIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [frameIdx, frameArr]

private theorem isFrame_iff (k : ℕ) : isFrame k = true ↔ ∃ i : Fin 4, (frameIdx i : ℕ) = k := by
  constructor
  · intro h
    simp only [isFrame, List.any_eq_true, List.mem_finRange] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, by rw [frameIdx_val, beq_iff_eq.mp hi]⟩
  · rintro ⟨i, rfl⟩
    simp only [isFrame, List.any_eq_true, List.mem_finRange]
    exact ⟨i, by simp, by simp [frameIdx_val]⟩

private noncomputable def T0sub : Subgroup (Equiv.Perm (Fin 60)) :=
  Subgroup.closure (permsA 60 t0Gens)

private theorem T0sub_card : Nat.card T0sub = 32 := by
  have h := (frameCheck_parts (Certificates.certificate1383004)).1
  simp only [t0Check, Bool.and_eq_true] at h
  obtain ⟨hok, hsz⟩ := h
  obtain ⟨-, hcard, -⟩ := enumOK_spec (n := 60) (gs := t0Gens) (ps := plusBase)
    (c := t0Cert ()) plusBase_lt hok
  unfold T0sub
  rw [hcard, beq_iff_eq.mp hsz]

private theorem T0sub_le : T0sub ≤ plusPerm := by
  rw [T0sub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hany : (plusEnum ()).pts.toList.any (eqA 60 t0Gens[k]!) = true :=
    List.all_eq_true.mp t0SubCheck_true k (List.mem_range.mpr hk)
  rw [List.any_eq_true] at hany
  obtain ⟨a, ha, heq⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (plusEnum ()).pts.size := by simpa using hi
  have hvalid : validA 60 (plusEnum ()).pts[i]! = true := plusEnum_spec.2.2 i hi'
  have hgvalid : validA 60 t0Gens[k]! = true := enumOK_gens_valid t0EnumOK_true hk
  have heq2 : eqA 60 t0Gens[k]! (plusEnum ()).pts[i]! = true := by
    rw [getElem!_pos (plusEnum ()).pts i hi']
    simpa [Array.getElem_toList] using heq
  have heq' : permOfArr 60 (plusEnum ()).pts[i]! = permOfArr 60 t0Gens[k]! :=
    ((eqA_iff (rep_of_validA hgvalid) (rep_of_validA hvalid)).mp heq2).symm
  exact (plusEnum_spec.1 (permOfArr 60 t0Gens[k]!)).mpr ⟨i, hi', heq'⟩

private theorem factorization_7200_two : 2 ^ (7200).factorization 2 = 32 := by
  have h : (7200).factorization 2 = 5 := by
    have h2 : 7200 = 2 ^ 5 * 225 := by norm_num
    rw [h2, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 225)]
  rw [h]
  norm_num

private noncomputable def T0 : Sylow 2 plusPerm :=
  Sylow.ofCard (T0sub.subgroupOf plusPerm) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0sub_le).toEquiv, T0sub_card,
      card_plusPerm]
    exact factorization_7200_two.symm)

private noncomputable def frameR (i : Fin 4) : plusPerm :=
  ⟨plusRefl (frameIdx i), plusRefl_mem _⟩

private theorem frameR_injective : Function.Injective frameR := by
  intro i j h
  exact frameIdx_injective (plusRefl_injective (Subtype.ext_iff.mp h))

private theorem rep_plusTable (i : Fin 60) : Rep 60 plusTable[(i : ℕ)]! (plusRefl i) :=
  fun x => (plusRefl_apply i x).symm

private theorem frameR_zero : frameR 0 = ⟨plusRefl 18, plusRefl_mem 18⟩ := rfl

private theorem frameR_one : frameR 1 = ⟨plusRefl 31, plusRefl_mem 31⟩ := rfl

private theorem frameR_two : frameR 2 = ⟨plusRefl 36, plusRefl_mem 36⟩ := rfl

private theorem frameR_three : frameR 3 = ⟨plusRefl 41, plusRefl_mem 41⟩ := rfl

private theorem frameR_prod : frameR 0 * frameR 1 * frameR 2 * frameR 3 = 1 := by
  rw [frameR_zero, frameR_one, frameR_two, frameR_three]
  apply Subtype.ext
  have h3 : Rep 60 (compA 60 (compA 60 (compA 60 plusTable[18]! plusTable[31]!) plusTable[36]!)
      plusTable[41]!) (((plusRefl 18 * plusRefl 31) * plusRefl 36) * plusRefl 41) :=
    rep_compA (rep_compA (rep_compA (rep_plusTable 18) (rep_plusTable 31)) (rep_plusTable 36))
      (rep_plusTable 41)
  have heq := (eqA_iff h3 rep_idA).mp (by simpa [frameProdCheck] using frameProdCheck_true)
  simpa [Subgroup.coe_mul, mul_assoc] using heq

private theorem matchesPerm_eq (a : Array ℕ) (σ : Fin 4 → Fin 4) :
    matchesPerm a σ = true ↔
      ∀ i : Fin 4, a[frameArr[(i : ℕ)]!]! = frameArr[((σ i : Fin 4) : ℕ)]! := by
  simp [matchesPerm, List.all_eq_true, List.mem_finRange, beq_iff_eq]

private theorem mapsFrame_eq (a : Array ℕ) :
    mapsFrame a = true ↔
      ∀ i : Fin 4, ∃ j : Fin 4, a[frameArr[(i : ℕ)]!]! = frameArr[(j : ℕ)]! := by
  simp [mapsFrame, List.all_eq_true, List.any_eq_true, List.mem_finRange, beq_iff_eq]

private theorem frameR_conj_apply (g : plusPerm) (i : Fin 4) :
    ((g * frameR i * g⁻¹ : plusPerm) : Equiv.Perm (Fin 60)) =
      plusRefl ((g : Equiv.Perm (Fin 60)) (frameIdx i)) := by
  show ((g : Equiv.Perm (Fin 60)) * (plusRefl (frameIdx i)) *
    (g : Equiv.Perm (Fin 60))⁻¹ : Equiv.Perm (Fin 60)) = _
  exact conj_plusRefl g.2 (frameIdx i)

private theorem frameR_conj_iff (g : plusPerm) (σ : Equiv.Perm (Fin 4)) :
    (∀ i, g * frameR i * g⁻¹ = frameR (σ i)) ↔
      ∀ i, (g : Equiv.Perm (Fin 60)) (frameIdx i) = frameIdx (σ i) := by
  constructor
  · intro h i
    have h1 := congrArg (fun x : plusPerm => (x : Equiv.Perm (Fin 60))) (h i)
    rw [frameR_conj_apply] at h1
    have h2 : (frameR (σ i) : Equiv.Perm (Fin 60)) = plusRefl (frameIdx (σ i)) := rfl
    rw [h2] at h1
    exact plusRefl_injective h1
  · intro h i
    apply Subtype.ext
    rw [frameR_conj_apply, h i]
    rfl

private def funSign (f : Fin 4 → Fin 4) : ℤˣ :=
  ∏ j : Fin 4, ∏ i ∈ Finset.Iio j, (if f i < f j then 1 else -1)

private theorem funSign_inj_even : ∀ f : Fin 4 → Fin 4, Function.Injective f →
    (funSign f = 1 ↔ f ∈ evenPerms) := by decide +kernel

private theorem funSign_inj_cases : ∀ f : Fin 4 → Fin 4, Function.Injective f →
    f ∈ evenPerms ∨ f ∈ oddPerms := by decide +kernel

private theorem sign_eq_funSign (σ : Equiv.Perm (Fin 4)) : σ.sign = funSign (⇑σ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  rfl

private theorem evenPerms_complete :
    ∀ σ : Equiv.Perm (Fin 4), σ ∈ alternatingGroup (Fin 4) →
      ∃ τ ∈ evenPerms, ∀ i, τ i = σ i := by
  intro σ hσ
  have hsign : σ.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp hσ
  have hfun : funSign (⇑σ) = 1 := by rw [← sign_eq_funSign]; exact hsign
  exact ⟨⇑σ, (funSign_inj_even (⇑σ) σ.injective).mp hfun, fun i => rfl⟩

private theorem oddPerms_complete :
    ∀ σ : Equiv.Perm (Fin 4), σ ∉ alternatingGroup (Fin 4) →
      ∃ τ ∈ oddPerms, ∀ i, τ i = σ i := by
  intro σ hσ
  have hsign : σ.sign ≠ 1 := fun h => hσ (Equiv.Perm.mem_alternatingGroup.mpr h)
  rcases funSign_inj_cases (⇑σ) σ.injective with he | ho
  · exact absurd (by rw [sign_eq_funSign]; exact (funSign_inj_even (⇑σ) σ.injective).mpr he)
      hsign
  · exact ⟨⇑σ, ho, fun i => rfl⟩

private theorem frameR_even : ∀ (g : plusPerm) (σ : Equiv.Perm (Fin 4)),
    (∀ i, g * frameR i * g⁻¹ = frameR (σ i)) → σ ∈ alternatingGroup (Fin 4) := by
  intro g σ hσ
  by_contra hnot
  obtain ⟨τ, hτmem, hτeq⟩ := oddPerms_complete σ hnot
  obtain ⟨k, hk, hak⟩ := (plusEnum_spec.1 g).mp g.2
  have hvalid : validA 60 (plusEnum ()).pts[k]! = true := plusEnum_spec.2.2 k hk
  have hframe : ∀ i, (g : Equiv.Perm (Fin 60)) (frameIdx i) = frameIdx (σ i) :=
    (frameR_conj_iff g σ).mp hσ
  have hmap : mapsFrame ((plusEnum ()).pts[k]!) = true := by
    rw [mapsFrame_eq]
    intro i
    refine ⟨σ i, ?_⟩
    rw [← frameIdx_val, ← frameIdx_val]
    rw [(rep_of_validA hvalid).apply (frameIdx i).2, hak]
    exact congrArg Fin.val (hframe i)
  have hkprop : (let a := (plusEnum ()).pts[k]!;
      !(mapsFrame a) || (oddPerms.all fun σ => !(matchesPerm a σ))) = true :=
    allLt_spec evenCheck_true hk
  simp only [evenCheck] at hkprop
  rw [hmap] at hkprop
  simp only [Bool.not_true, Bool.false_or] at hkprop
  have hτfalse : matchesPerm ((plusEnum ()).pts[k]!) τ = false := by
    have := List.all_eq_true.mp hkprop τ hτmem
    simpa using this
  have hσtrue : matchesPerm ((plusEnum ()).pts[k]!) σ = true := by
    rw [matchesPerm_eq]
    intro i
    rw [← frameIdx_val, ← frameIdx_val]
    rw [(rep_of_validA hvalid).apply (frameIdx i).2, hak]
    exact congrArg Fin.val (hframe i)
  rw [show τ = (fun i => σ i) from funext hτeq] at hτfalse
  rw [hσtrue] at hτfalse
  exact Bool.noConfusion hτfalse

private theorem frameR_alternating : ∀ σ ∈ alternatingGroup (Fin 4),
    ∃ g : plusPerm, ∀ i, g * frameR i * g⁻¹ = frameR (σ i) := by
  intro σ hσ
  obtain ⟨τ, hτmem, hτeq⟩ := evenPerms_complete σ hσ
  have hany := List.all_eq_true.mp alternatingCheck_true τ hτmem
  rw [List.any_eq_true] at hany
  obtain ⟨a, ha, hmat⟩ := hany
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk' : k < (plusEnum ()).pts.size := by simpa using hk
  have hvalid : validA 60 (plusEnum ()).pts[k]! = true := plusEnum_spec.2.2 k hk'
  have hmat' : matchesPerm ((plusEnum ()).pts[k]!) τ = true := by
    rw [getElem!_pos (plusEnum ()).pts k hk']
    exact hmat
  refine ⟨⟨permOfArr 60 ((plusEnum ()).pts[k]!),
    (plusEnum_spec.1 _).mpr ⟨k, hk', rfl⟩⟩, ?_⟩
  rw [frameR_conj_iff]
  intro i
  apply Fin.ext
  have hm := (matchesPerm_eq _ τ).mp hmat' i
  rw [← frameIdx_val i] at hm
  rw [← (rep_of_validA hvalid).apply (frameIdx i).2, hm, hτeq i, frameIdx_val]

private theorem mem_T0sub_iff (k : ℕ) (hk : k < 60) :
    plusRefl ⟨k, hk⟩ ∈ T0sub ↔ isFrame k = true := by
  have hck : ((t0Cert ()).pts.toList.any (eqA 60 plusTable[k]!)) = isFrame k := by
    have h := List.all_eq_true.mp frameMemCheck_true k (List.mem_range.mpr hk)
    simpa using (beq_iff_eq.mp h : (t0Cert ()).pts.toList.any (eqA 60 plusTable[k]!) = isFrame k)
  have hspec := enumOK_spec (n := 60) (gs := t0Gens) (ps := plusBase)
    (c := t0Cert ()) plusBase_lt t0EnumOK_true
  have hany : ((t0Cert ()).pts.toList.any (eqA 60 plusTable[k]!)) = true ↔
      plusRefl ⟨k, hk⟩ ∈ T0sub := by
    constructor
    · intro h
      exact enumOK_mem_of_any (n := 60) (gs := t0Gens) (ps := plusBase) (c := t0Cert ())
        plusBase_lt t0EnumOK_true (rep_plusTable ⟨k, hk⟩) h
    · intro hmem
      obtain ⟨i, hi, hik⟩ := (hspec.1 (plusRefl ⟨k, hk⟩)).1 hmem
      have hval := hspec.2.2 i hi
      rw [List.any_eq_true]
      exact ⟨(t0Cert ()).pts[i]!,
        by rw [getElem!_pos (t0Cert ()).pts i hi]; exact Array.getElem_mem_toList hi,
        (eqA_iff (rep_plusTable ⟨k, hk⟩) (rep_of_validA hval)).mpr hik.symm⟩
  rw [← hany, hck]

private theorem frameR_inter : (T0 : Set plusPerm) ∩ plusClass = Set.range frameR := by
  ext x
  constructor
  · rintro ⟨hT0, hclass⟩
    obtain ⟨k, hk⟩ := hclass
    have hT0' : (x : Equiv.Perm (Fin 60)) ∈ T0sub := hT0
    rw [hk] at hT0'
    obtain ⟨i, hi⟩ := (isFrame_iff (k : ℕ)).mp ((mem_T0sub_iff (k : ℕ) k.2).mp hT0')
    exact ⟨i, Subtype.ext (by
      rw [hk]
      change plusRefl (frameIdx i) = plusRefl k
      exact congrArg plusRefl (Fin.ext hi))⟩
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ⟨frameIdx i, rfl⟩⟩
    change plusRefl (frameIdx i) ∈ T0sub
    exact (mem_T0sub_iff (frameIdx i : ℕ) (frameIdx i).2).mpr ((isFrame_iff _).mpr ⟨i, rfl⟩)

private theorem mem_otherRows (i : Fin 4) (a : Array ℕ) :
    a ∈ (otherRows i).toList ↔
      ∃ j : Fin 4, j ≠ i ∧ a = plusTable[frameArr[(j : ℕ)]!]! := by
  rw [otherRows, List.toList_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨j, -, hj⟩
    by_cases hji : j = i
    · simp [hji] at hj
    · exact ⟨j, hji, by simpa [hji] using hj.symm⟩
  · rintro ⟨j, hji, rfl⟩
    exact ⟨j, List.mem_finRange j, by simp [hji]⟩

private theorem mem_permsA_iff {gs : Array (Array ℕ)} {x : Equiv.Perm (Fin 60)} :
    x ∈ permsA 60 gs ↔ ∃ a ∈ gs.toList, x = permOfArr 60 a := by
  rw [permsA]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨gs[k]!, by rw [getElem!_pos gs k hk]; exact Array.getElem_mem_toList hk, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    refine ⟨k, by simpa using hk, ?_⟩
    change permOfArr 60 gs[k]! = permOfArr 60 gs.toList[k]
    rw [getElem!_pos gs k (by simpa using hk)]
    rfl

private theorem permsA_otherRows (i : Fin 4) :
    permsA 60 (otherRows i) =
      {x | ∃ j : Fin 4, j ≠ i ∧ x = plusRefl (frameIdx j)} := by
  ext x
  rw [mem_permsA_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hji, rfl⟩ := (mem_otherRows i a).mp ha
    exact ⟨j, hji, rfl⟩
  · rintro ⟨j, hji, rfl⟩
    exact ⟨plusTable[frameArr[(j : ℕ)]!]!, (mem_otherRows i _).mpr ⟨j, hji, rfl⟩, rfl⟩

private theorem subtype_image_frameR (i : Fin 4) :
    plusPerm.subtype '' (Set.range frameR \ {frameR i}) =
      {x | ∃ j : Fin 4, j ≠ i ∧ x = plusRefl (frameIdx j)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨hy_range, hy_ne⟩
    obtain ⟨j, rfl⟩ := hy_range
    exact ⟨j, fun h => hy_ne (by simp [h]), rfl⟩
  · rintro ⟨j, hji, rfl⟩
    exact ⟨frameR j, ⟨⟨j, rfl⟩, fun h => hji (frameR_injective h)⟩, rfl⟩

private theorem cardCheck_other (i : Fin 4) :
    Nat.card (Subgroup.closure (permsA 60 (otherRows i))) = 8 := by
  have hcheck : (enumOK 60 (otherRows i) plusBase (enumBfs 60 (otherRows i) plusBase 16) &&
      ((enumBfs 60 (otherRows i) plusBase 16).pts.size == 8)) = true :=
    List.all_eq_true.mp cardCheck_true i (List.mem_finRange i)
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨hok, hsize⟩ := hcheck
  have hcard := (enumOK_spec (n := 60) (gs := otherRows i) (ps := plusBase)
    (c := enumBfs 60 (otherRows i) plusBase 16) plusBase_lt hok).2.1
  rw [hcard, beq_iff_eq.mp hsize]

private theorem frameR_card_closure :
    ∀ i, Nat.card (Subgroup.closure (Set.range frameR \ {frameR i})) = 8 := by
  intro i
  have hmap : (Subgroup.closure (Set.range frameR \ {frameR i})).map plusPerm.subtype =
      Subgroup.closure (permsA 60 (otherRows i)) := by
    rw [MonoidHom.map_closure, subtype_image_frameR i, permsA_otherRows i]
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective plusPerm), hmap,
    cardCheck_other i]

private theorem derivOrder_lt {k : ℕ} (hk : k < 60) : derivOrder[k]! < 60 := by
  have h := derivValidCheck_true
  simp only [derivValidCheck, Bool.and_eq_true] at h
  exact decide_eq_true_eq.mp (List.all_eq_true.mp h.1.1.1 k (List.mem_range.mpr hk))

private theorem derivOrder_covers {p : ℕ} (hp : p < 60) : ∃ j < 60, derivOrder[j]! = p := by
  have h := derivValidCheck_true
  simp only [derivValidCheck, Bool.and_eq_true] at h
  have h2 := List.all_eq_true.mp h.1.1.2 p (List.mem_range.mpr hp)
  rw [List.any_eq_true] at h2
  obtain ⟨j, hj, hje⟩ := h2
  exact ⟨j, List.mem_range.mp hj, by simpa using hje⟩

private theorem derivOrder_ne {j k : ℕ} (hj : j < k) (hk : k < 60) :
    derivOrder[j]! ≠ derivOrder[k]! := by
  have h := derivValidCheck_true
  simp only [derivValidCheck, Bool.and_eq_true] at h
  have h3 := List.all_eq_true.mp h.1.2 k (List.mem_range.mpr hk)
  intro hjk
  have := List.all_eq_true.mp h3 j (List.mem_range.mpr hj)
  simp [hjk] at this

private theorem occursBefore_spec {p k : ℕ} (h : occursBefore p k = true) :
    ∃ j < k, derivOrder[j]! = p := by
  rw [occursBefore, List.any_eq_true] at h
  obtain ⟨j, hj, hje⟩ := h
  exact ⟨j, List.mem_range.mp hj, beq_iff_eq.mp hje⟩

private theorem derivStep_spec {k : ℕ} (hk : k < 60) :
    (let p := derivOrder[k]!
     let s := derivSrc[k]!
     if s = 0 then (isFrame p || p = 0 || p = 1)
     else
       let x := (s - 1) / 60
       let y := (s - 1) % 60
       (x < 60) && (y < 60) && ((plusTable[x]!)[y]! == p) && occursBefore x k &&
         occursBefore y k) = true := by
  have h := derivValidCheck_true
  simp only [derivValidCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 k (List.mem_range.mpr hk)

private theorem initArr_size (a b : ℕ) : (initArr a b).size = 60 := by simp [initArr]

private theorem deriveFun_size (f : Array ℕ) (a b : ℕ) (k : ℕ) :
    (deriveFun a b f k).size = f.size := by
  induction k with
  | zero => rfl
  | succ k ih => rw [deriveFun, Array.size_set!, ih]

private theorem deriveFun_succ (f : Array ℕ) (a b k : ℕ) :
    deriveFun a b f (k + 1) =
      (deriveFun a b f k).set! (derivOrder[k]!) (stepVal a b (deriveFun a b f k) k) := rfl

private theorem initFun_eq_of_step (f : ℕ → ℕ) (a b p : ℕ)
    (hfix : ∀ i : Fin 4, f (frameIdx i : ℕ) = (frameIdx i : ℕ))
    (h0 : f 0 = a) (h1 : f 1 = b)
    (h : (isFrame p || p = 0 || p = 1) = true) : initFun a b p = f p := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (hf | hz) | ho
  · obtain ⟨i, hi⟩ := (isFrame_iff _).mp hf
    rw [show p = (frameIdx i : ℕ) from hi.symm, hfix i]
    simp [initFun, (isFrame_iff _).mpr ⟨i, rfl⟩]
  · rw [hz, h0]; simp [initFun, show isFrame 0 = false by decide]
  · rw [ho, h1]; simp [initFun, show isFrame 1 = false by decide]

private theorem deriveFun_spec (f : ℕ → ℕ) (a b : ℕ)
    (hfix : ∀ i : Fin 4, f (frameIdx i : ℕ) = (frameIdx i : ℕ))
    (h0 : f 0 = a) (h1 : f 1 = b)
    (hhom : ∀ i j : Fin 60, f ((plusTable[(i : ℕ)]!)[(j : ℕ)]!) = (plusTable[f i]!)[f j]!) :
    ∀ k, k ≤ 60 → ∀ j, j < k →
      (deriveFun a b (initArr a b) k)[derivOrder[j]!]! = f (derivOrder[j]!) := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
      intro hk j hj
      have hk60 : k < 60 := by omega
      rw [deriveFun_succ]
      by_cases hjk : j = k
      · rw [hjk]
        rw [Array.getElem!_set!_self _ _ _
          (by rw [deriveFun_size, initArr_size]; exact derivOrder_lt hk60)]
        have hspec := derivStep_spec hk60
        dsimp only at hspec
        rw [stepVal]
        split_ifs with hs
        · rw [if_pos hs] at hspec
          exact initFun_eq_of_step f a b _ hfix h0 h1 hspec
        · rw [if_neg hs] at hspec
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hspec
          obtain ⟨⟨⟨⟨hx60, hy60⟩, hxy⟩, hox⟩, hoy⟩ := hspec
          have hx60' : (derivSrc[k]! - 1) / 60 < 60 := decide_eq_true_eq.mp hx60
          have hy60' : (derivSrc[k]! - 1) % 60 < 60 := decide_eq_true_eq.mp hy60
          obtain ⟨jx, hjx, hxjx⟩ := occursBefore_spec hox
          obtain ⟨jy, hjy, hyjy⟩ := occursBefore_spec hoy
          have hDx : (deriveFun a b (initArr a b) k)[(derivSrc[k]! - 1) / 60]! =
              f ((derivSrc[k]! - 1) / 60) := by
            rw [← hxjx]; exact ih (by omega) jx hjx
          have hDy : (deriveFun a b (initArr a b) k)[(derivSrc[k]! - 1) % 60]! =
              f ((derivSrc[k]! - 1) % 60) := by
            rw [← hyjy]; exact ih (by omega) jy hjy
          dsimp only
          rw [hDx, hDy, ← beq_iff_eq.mp hxy]
          exact (hhom ⟨_, hx60'⟩ ⟨_, hy60'⟩).symm
      · have hjk' : j < k := by omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm (derivOrder_ne hjk' hk60))]
        exact ih (by omega) j hjk'

private theorem rep_dImageList (S : List (Fin 4)) :
    Rep 60 (dImageList S) (((S.map frameR).prod : plusPerm) : Equiv.Perm (Fin 60)) := by
  induction S with
  | nil => simpa [dImageList] using (rep_idA (n := 60))
  | cons i S ih =>
      have h : dImageList (i :: S) = compA 60 (plusTable[(frameIdx i : ℕ)]!) (dImageList S) := by
        simp [dImageList, frameIdx_val]
      simpa only [h, List.map_cons, List.prod_cons, Subgroup.coe_mul, frameR] using
        rep_compA (rep_plusTable (frameIdx i)) ih

private theorem closure_plusRefl_eq_top :
    Subgroup.closure (Set.range (fun k : Fin 60 => (⟨plusRefl k, plusRefl_mem k⟩ : plusPerm))) =
      ⊤ := by
  have hmap : (Subgroup.closure (Set.range (fun k : Fin 60 =>
      (⟨plusRefl k, plusRefl_mem k⟩ : plusPerm)))).map plusPerm.subtype = plusPerm := by
    rw [MonoidHom.map_closure]
    have himg : plusPerm.subtype '' Set.range (fun k : Fin 60 =>
        (⟨plusRefl k, plusRefl_mem k⟩ : plusPerm)) = Set.range plusRefl := by
      ext x
      constructor
      · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨⟨plusRefl k, plusRefl_mem k⟩, ⟨k, rfl⟩, rfl⟩
    rw [himg]
    rfl
  rw [eq_top_iff]
  intro x _
  have hx : (x : Equiv.Perm (Fin 60)) ∈
      (Subgroup.closure (Set.range (fun k : Fin 60 =>
        (⟨plusRefl k, plusRefl_mem k⟩ : plusPerm)))).map plusPerm.subtype := by
    rw [hmap]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rw [hyx'] at hy
  exact hy

private theorem plusTable_lt (i j : Fin 60) : (plusTable[(i : ℕ)]!)[(j : ℕ)]! < 60 := by
  rw [← plusRefl_apply i j]
  exact (plusRefl i j).2

private theorem prod_frameR_mem (S : List (Fin 4)) :
    (S.map frameR).prod ∈ Subgroup.closure (Set.range frameR) := by
  induction S with
  | nil => exact Subgroup.one_mem _
  | cons i S ih =>
      rw [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) ih

private theorem frameR_aut : ∀ φ : plusPerm ≃* plusPerm, φ '' plusClass = plusClass →
    (∀ i, φ (frameR i) = frameR i) →
      ∃ d ∈ Subgroup.closure (Set.range frameR), ∀ x, φ x = d * x * d⁻¹ := by
  intro φ hφ hfix
  have hψ_exists : ∀ k : Fin 60, ∃ k' : Fin 60,
      φ ⟨plusRefl k, plusRefl_mem k⟩ = ⟨plusRefl k', plusRefl_mem k'⟩ := by
    intro k
    have h : φ ⟨plusRefl k, plusRefl_mem k⟩ ∈ plusClass := by
      rw [← hφ]
      exact ⟨⟨plusRefl k, plusRefl_mem k⟩, ⟨k, rfl⟩, rfl⟩
    obtain ⟨k', hk'⟩ := h
    exact ⟨k', Subtype.ext hk'⟩
  let ψ : Fin 60 → Fin 60 := fun k => Classical.choose (hψ_exists k)
  have hψ : ∀ k, φ ⟨plusRefl k, plusRefl_mem k⟩ = ⟨plusRefl (ψ k), plusRefl_mem (ψ k)⟩ :=
    fun k => Classical.choose_spec (hψ_exists k)
  have hψ_frame : ∀ i : Fin 4, ψ (frameIdx i) = frameIdx i := by
    intro i
    have h1 := hψ (frameIdx i)
    have h3 : (⟨plusRefl (ψ (frameIdx i)), plusRefl_mem _⟩ : plusPerm) = frameR i :=
      h1.symm.trans (hfix i)
    exact plusRefl_injective (Subtype.ext_iff.mp h3)
  have hψ_hom : ∀ i j : Fin 60,
      ψ ⟨(plusTable[(i : ℕ)]!)[(j : ℕ)]!, plusTable_lt i j⟩ =
        ⟨(plusTable[(ψ i : ℕ)]!)[(ψ j : ℕ)]!, plusTable_lt (ψ i) (ψ j)⟩ := by
    intro i j
    have hconj : (⟨plusRefl ⟨(plusTable[(i : ℕ)]!)[(j : ℕ)]!, plusTable_lt i j⟩,
        plusRefl_mem _⟩ : plusPerm) =
        ⟨plusRefl i, plusRefl_mem i⟩ * ⟨plusRefl j, plusRefl_mem j⟩ *
          ⟨plusRefl i, plusRefl_mem i⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [plusRefl_conj,
        show plusRefl i j = ⟨(plusTable[(i : ℕ)]!)[(j : ℕ)]!, plusTable_lt i j⟩ from
          Fin.ext (plusRefl_apply i j)]
    have h1 := hψ ⟨(plusTable[(i : ℕ)]!)[(j : ℕ)]!, plusTable_lt i j⟩
    rw [hconj] at h1
    rw [map_mul, map_mul, map_inv, hψ i, hψ j] at h1
    have h2 : (⟨plusRefl (ψ i), plusRefl_mem (ψ i)⟩ * ⟨plusRefl (ψ j), plusRefl_mem (ψ j)⟩ *
        ⟨plusRefl (ψ i), plusRefl_mem (ψ i)⟩⁻¹ : plusPerm) =
        ⟨plusRefl ⟨(plusTable[(ψ i : ℕ)]!)[(ψ j : ℕ)]!, plusTable_lt (ψ i) (ψ j)⟩,
          plusRefl_mem _⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [plusRefl_conj,
        show plusRefl (ψ i) (ψ j) = ⟨(plusTable[(ψ i : ℕ)]!)[(ψ j : ℕ)]!,
          plusTable_lt (ψ i) (ψ j)⟩ from Fin.ext (plusRefl_apply (ψ i) (ψ j))]
    rw [h2] at h1
    exact (plusRefl_injective (Subtype.ext_iff.mp h1)).symm
  let a : ℕ := (ψ 0 : ℕ)
  let b : ℕ := (ψ 1 : ℕ)
  let f : ℕ → ℕ := fun p => if h : p < 60 then (ψ ⟨p, h⟩ : ℕ) else 0
  have hf_apply : ∀ (p : ℕ) (hp : p < 60), f p = (ψ ⟨p, hp⟩ : ℕ) := by
    intro p hp; simp [f, hp]
  have hf0 : f 0 = a := by simp [f, a]
  have hf1 : f 1 = b := by simp [f, b]
  have hfframe : ∀ i : Fin 4, f (frameIdx i : ℕ) = (frameIdx i : ℕ) := by
    intro i; rw [hf_apply _ (frameIdx i).2, hψ_frame i]
  have hfhom : ∀ i j : Fin 60, f ((plusTable[(i : ℕ)]!)[(j : ℕ)]!) = (plusTable[f i]!)[f j]! := by
    intro i j
    rw [hf_apply _ (plusTable_lt i j), hf_apply _ i.2, hf_apply _ j.2]
    exact congrArg Fin.val (hψ_hom i j)
  have hderive : ∀ (p : ℕ) (hp : p < 60), (deriveArr a b)[p]! = (ψ ⟨p, hp⟩ : ℕ) := by
    intro p hp
    obtain ⟨j, hj, hjval⟩ := derivOrder_covers hp
    have hspec := deriveFun_spec f a b hfframe hf0 hf1 hfhom 60 (le_refl 60) j hj
    rw [hjval] at hspec
    change (deriveFun a b (initArr a b) 60)[p]! = (ψ ⟨p, hp⟩ : ℕ)
    rw [hspec, hf_apply p hp]
  have hhomArr : isTableHomArr (deriveArr a b) = true := by
    rw [isTableHomArr, List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    rw [beq_iff_eq]
    have hi' : i < 60 := List.mem_range.mp hi
    have hj' : j < 60 := List.mem_range.mp hj
    rw [hderive _ (plusTable_lt ⟨i, hi'⟩ ⟨j, hj'⟩), hderive i hi', hderive j hj']
    exact congrArg Fin.val (hψ_hom ⟨i, hi'⟩ ⟨j, hj'⟩)
  have haut : (dActions ()).any (fun g => matchesArr (deriveArr a b) g) = true := by
    have h1 := List.all_eq_true.mp (by simpa only [autCheck] using autCheck_true) (ψ 0 : ℕ)
      (List.mem_range.mpr (ψ 0).2)
    have h2 := List.all_eq_true.mp h1 (ψ 1 : ℕ) (List.mem_range.mpr (ψ 1).2)
    rw [hhomArr] at h2
    simpa using h2
  rw [List.any_eq_true] at haut
  obtain ⟨g, hgmem, hgmatch⟩ := haut
  rw [dActions, List.mem_map] at hgmem
  obtain ⟨S, -, hSeq⟩ := hgmem
  have hrep := rep_dImageList S
  have hd1 : ((S.map frameR).prod : Equiv.Perm (Fin 60)) = permOfArr 60 (dImageList S) :=
    (permOfArr_eq_of_rep hrep).symm
  have hrep' : Rep 60 (dImageList S) (permOfArr 60 (dImageList S)) := by
    rw [← hd1]; exact hrep
  have hd_apply : ∀ k : Fin 60, ((S.map frameR).prod : Equiv.Perm (Fin 60)) k = ψ k := by
    intro k
    apply Fin.ext
    rw [hd1]
    change ((permOfArr 60 (dImageList S)) k : ℕ) = (ψ k : ℕ)
    have hgall : (List.range 60).all
        (fun p => (deriveArr a b)[p]! == (dImageList S)[p]!) = true := by
      change matchesArr (deriveArr a b) (dImageList S) = true
      rw [hSeq]
      exact hgmatch
    have hm : (deriveArr a b)[(k : ℕ)]! = (dImageList S)[(k : ℕ)]! :=
      beq_iff_eq.mp (List.all_eq_true.mp hgall (k : ℕ) (List.mem_range.mpr k.2))
    rw [← hrep'.apply k.2, ← hm, hderive (k : ℕ) k.2]
  have hgen : ∀ k : Fin 60, φ ⟨plusRefl k, plusRefl_mem k⟩ =
      (S.map frameR).prod * ⟨plusRefl k, plusRefl_mem k⟩ * ((S.map frameR).prod)⁻¹ := by
    intro k
    rw [hψ k]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      conj_plusRefl ((S.map frameR).prod).2 k]
    exact congrArg plusRefl (hd_apply k).symm
  refine ⟨(S.map frameR).prod, prod_frameR_mem S, ?_⟩
  intro x
  have heq : φ.toMonoidHom = (MulAut.conj ((S.map frameR).prod)).toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense closure_plusRefl_eq_top (fun y hy => by
      rcases hy with ⟨k, rfl⟩
      exact hgen k)
  have := congrFun (congrArg DFunLike.coe heq) x
  simpa [MulAut.conj_apply] using this

private theorem frame_T0 : O4PlusFrame plusClass (T0 : Subgroup plusPerm) frameR :=
  ⟨frameR_injective, frameR_inter, frameR_prod, frameR_card_closure, frameR_even,
    frameR_alternating, frameR_aut⟩

private theorem conj_mem_plusClass (g : plusPerm) {x : plusPerm} (hx : x ∈ plusClass) :
    MulAut.conj g x ∈ plusClass := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨(g : Equiv.Perm (Fin 60)) k, ?_⟩
  rw [MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hk]
  exact conj_plusRefl g.2 k

private theorem conj_image_plusClass (g : plusPerm) :
    (MulAut.conj g) '' plusClass = plusClass := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact conj_mem_plusClass g hx
  · intro hy
    exact ⟨MulAut.conj g⁻¹ y, conj_mem_plusClass g⁻¹ hy, by
      simp only [MulAut.conj_apply]
      group⟩

theorem exists_plusFrame : ∀ T : Sylow 2 plusPerm,
    ∃ r : Fin 4 → plusPerm, O4PlusFrame plusClass (T : Subgroup plusPerm) r := by
  intro T
  haveI : Finite (Sylow 2 plusPerm) := inferInstance
  haveI := Sylow.isPretransitive_of_finite (p := 2) (G := plusPerm)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq plusPerm T0 T
  refine ⟨fun i => MulAut.conj g (frameR i), ?_⟩
  have hmap := O4PlusFrame.map (MulAut.conj g) (conj_image_plusClass g) frame_T0
  have hT : (T : Subgroup plusPerm) =
      (T0 : Subgroup plusPerm).map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 plusPerm => (P : Subgroup plusPerm)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    rw [← h1]
    rfl
  simpa [hT] using hmap

end CFSG.OddTranspositions.PartThree
