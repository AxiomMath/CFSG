module

public import CFSG.Sporadic.FischerOddCore.Fi22CTICheck
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrder
public import CFSG.Sporadic.FischerOddCore.ClosureSpec
public import CFSG.LocalAnalysis.ComponentInitial.SylowLocalTransfer

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native

abbrev ctiR : Array (Array ℕ) × Array ℕ × Array ℕ × Array ℕ := closureSearch 3510 ctiQArr 1100

abbrev ctiCD : Array ℕ × Array ℕ × Array ℕ := ctiCosets ctiR.1 ctiZ

abbrev ctiPis : Array (Array ℕ) :=
  (List.range 9).toArray.map fun k => ctiPi ctiR.1 ctiCD.1 ctiCD.2.1 (ctiG k) (ctiGi k)

abbrev ctiR5 : Array (Array ℕ) × Array ℕ × Array ℕ × Array ℕ := closureSearch 512 ctiPis 60000

theorem cti_parts :
    ctiQOK ctiR.1 ctiR.2.1 ctiR.2.2.1 ctiR.2.2.2 ctiCD.1 ctiCD.2.1 ctiCD.2.2 ctiPis = true ∧
      ctiImageOK ctiPis ctiR5.1 ctiR5.2.1 ctiR5.2.2.1 ctiR5.2.2.2 = true := by
  have h := cti_check
  unfold ctiChecks at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem cti_Q_parts :
    closureOK 3510 ctiQArr ctiR.1 ctiR.2.1 ctiR.2.2.1 ctiR.2.2.2 = true ∧ ctiR.1.size = 1024 ∧
      keysOK 3510 [0, 1, 2, 3, 6, 4] ctiR.1 = true ∧
      (∀ j < 10, siftA 3510 (rawLevels 3510 (fi22CentStrong 1) #[0, 1, 2, 3, 6, 4])
        #[0, 1, 2, 3, 6, 4] 0 ctiQArr[j]! = true) ∧
      (∀ k < 9, ∀ j < 10, ctiMem ctiR.1 (conjArr 3510 (ctiG k) (ctiGi k) ctiQArr[j]!) = true) ∧
      eqA 3510 ctiZ (idA 3510) = false ∧ eqA 3510 (compA 3510 ctiZ ctiZ) (idA 3510) = true ∧
      (∀ k < 9, eqA 3510 (compA 3510 (ctiG k) ctiZ) (compA 3510 ctiZ (ctiG k)) = true) ∧
      ctiCD.2.1.size = 512 ∧ ctiPis.size = 9 ∧
      (∀ c < 512, ctiCD.2.1[c]! < 1024 ∧ ctiCD.1[ctiCD.2.1[c]!]! = c) ∧
      (∀ i < 1024, ctiCD.1[i]! < 512 ∧ ctiCD.2.2[i]! < 1024 ∧
        eqA 3510 ctiR.1[ctiCD.2.2[i]!]! (compA 3510 ctiR.1[i]! ctiZ) = true ∧
        ctiCD.1[ctiCD.2.2[i]!]! = ctiCD.1[i]! ∧
        ctiInCoset ctiR.1 ctiZ ctiR.1[i]! ctiCD.2.1[ctiCD.1[i]!]! = true) ∧
      (∀ j < 10, ∀ c < 512,
        (eqA 3510 (compA 3510 ctiQArr[j]! ctiR.1[ctiCD.2.1[c]!]!)
          (compA 3510 ctiR.1[ctiCD.2.1[c]!]! ctiQArr[j]!) ||
        eqA 3510 (compA 3510 ctiQArr[j]! ctiR.1[ctiCD.2.1[c]!]!)
          (compA 3510 (compA 3510 ctiR.1[ctiCD.2.1[c]!]! ctiZ) ctiQArr[j]!)) = true) ∧
      (∀ k < 9, ctiPis[k]!.size = 512 ∧ ∀ c < 512, (ctiPis[k]!)[c]! < 512 ∧
        ctiInCoset ctiR.1 ctiZ (conjArr 3510 (ctiG k) (ctiGi k) ctiR.1[ctiCD.2.1[c]!]!)
          ctiCD.2.1[(ctiPis[k]!)[c]!]! = true) ∧
      ∀ j < 10, isInvA 3510 ctiQArr[j]! (invCand 3510 ctiQArr[j]!) = true := by
  have h := cti_parts.1
  unfold ctiQOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩ := h
  refine ⟨h1, h2, h3, fun j hj => allLt_spec h4 hj, fun k hk j hj => allLt_spec
    (allLt_spec h5 hk) hj, h6, h7, fun k hk => allLt_spec h8 hk, h9, h10, fun c hc => ?_,
    fun i hi => ?_, fun j hj c hc => allLt_spec (allLt_spec h13 hj) hc, fun k hk => ?_,
    fun j hj => allLt_spec h15 hj⟩
  · have := allLt_spec h11 hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · have := allLt_spec h12 hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := this
    exact ⟨a, b, c, d, e⟩
  · have := allLt_spec h14 hk
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    refine ⟨this.1, fun c hc => ?_⟩
    have := allLt_spec this.2 hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

theorem cti_image_parts :
    closureOK 512 ctiPis ctiR5.1 ctiR5.2.1 ctiR5.2.2.1 ctiR5.2.2.2 = true ∧
      ctiR5.1.size = 51840 ∧ keysOK 512 [18, 32, 2] ctiR5.1 = true := by
  have h := cti_parts.2
  unfold ctiImageOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] def ctiGP (k : ℕ) : Equiv.Perm (Fin 3510) := fi22CentPerm (19 + k)

theorem rep_ctiG
    {k : ℕ} (hk : k < 9) : Rep 3510 (ctiG k) (ctiGP k) :=
  rep_fi22CentPerm (by omega)

theorem rep_ctiGi
    {k : ℕ} (hk : k < 9) : Rep 3510 (ctiGi k) (ctiGP k)⁻¹ :=
  rep_fi22CentPerm_inv (by omega)

@[expose] def ctiQP (j : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 ctiQArr[j]!

theorem rep_ctiQ
    {j : ℕ} (hj : j < 10) : Rep 3510 ctiQArr[j]! (ctiQP j) :=
  (rep_permOfArr (cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj)).1

theorem rep_ctiQ_inv {j : ℕ} (hj : j < 10) :
    Rep 3510 (invCand 3510 ctiQArr[j]!) (ctiQP j)⁻¹ :=
  (rep_permOfArr (cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj)).2

theorem ctiQArr_size : ctiQArr.size = 10 := Array.size_ofFn

theorem rep_ctiQArr :
    ∀ k < ctiQArr.size, Rep 3510 ctiQArr[k]! (ctiQP k) :=
  fun _ hk => rep_ctiQ hk

@[expose] def ctiQSub : Subgroup (Equiv.Perm (Fin 3510)) := gensClosure ctiQArr ctiQP

theorem ctiQP_mem {j : ℕ} (hj : j < 10) : ctiQP j ∈ ctiQSub :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

@[expose] def ctiZP : Equiv.Perm (Fin 3510) := ctiQP 6 * ctiQP 2 * (ctiQP 6)⁻¹ * (ctiQP 2)⁻¹

theorem rep_ctiZ : Rep 3510 ctiZ ctiZP := by
  have h := rep_compA (rep_ctiQ (j := 6) (by norm_num)) (rep_compA (rep_ctiQ (j := 2)
    (by norm_num)) (rep_compA (rep_ctiQ_inv (j := 6) (by norm_num))
      (rep_ctiQ_inv (j := 2) (by norm_num))))
  rwa [← mul_assoc, ← mul_assoc] at h

theorem ctiZP_mem : ctiZP ∈ ctiQSub := by
  have h2 := ctiQP_mem (j := 2) (by norm_num)
  have h6 := ctiQP_mem (j := 6) (by norm_num)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h6 h2)
    (Subgroup.inv_mem _ h6)) (Subgroup.inv_mem _ h2)

theorem ctiZP_ne_one : ctiZP ≠ 1 := fun h => by
  have := cti_Q_parts.2.2.2.2.2.1
  rw [(eqA_iff rep_ctiZ rep_idA).2 h] at this
  exact Bool.noConfusion this

theorem ctiZP_mul_self : ctiZP * ctiZP = 1 :=
  eq_of_eqA (rep_compA rep_ctiZ rep_ctiZ) rep_idA cti_Q_parts.2.2.2.2.2.2.1

theorem fi22H_one_eq :
    fi22H 1 = Subgroup.closure {g | ∃ k < 9, ctiGP k = g} := by
  rw [fi22H_eq_closure (c := 1) (by norm_num)]
  rfl

theorem ctiGP_mem {k : ℕ} (hk : k < 9) : ctiGP k ∈ fi22H 1 := by
  rw [fi22H_one_eq]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem ctiQSub_le :
    ctiQSub ≤ fi22H 1 := by
  rw [ctiQSub, gensClosure, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact (siftA_iff_mem_fi22H (c := 1) (by norm_num) (rep_ctiQ hj)).1
    (cti_Q_parts.2.2.2.1 j hj)

theorem card_ctiQSub : Nat.card ctiQSub = 1024 := by
  rw [ctiQSub, card_closure_of_keysOK rep_ctiQArr cti_Q_parts.1 (by decide) cti_Q_parts.2.2.1,
    cti_Q_parts.2.1]

theorem mem_ctiQSub_of_ctiMem
    {x : Array ℕ} {X : Equiv.Perm (Fin 3510)} (hX : Rep 3510 x X)
    (h : ctiMem ctiR.1 x = true) : X ∈ ctiQSub := by
  unfold ctiMem at h
  obtain ⟨i, hi, hix⟩ := Array.any_eq_true.1 h
  obtain ⟨g, hg, hgi⟩ := exists_rep_mem_closure rep_ctiQArr cti_Q_parts.1 i hi
  rw [getElem!_pos _ i hi] at hgi
  rw [← eq_of_eqA hgi hX hix]
  exact hg

theorem exists_ctiE {X : Equiv.Perm (Fin 3510)} (hX : X ∈ ctiQSub) :
    ∃ i < 1024, Rep 3510 ctiR.1[i]! X := by
  obtain ⟨i, hi, h⟩ := exists_rep_of_mem_closure rep_ctiQArr cti_Q_parts.1 hX
  exact ⟨i, cti_Q_parts.2.1 ▸ hi, h⟩

theorem map_conj_ctiQSub_le
    {k : ℕ} (hk : k < 9) :
    ctiQSub.map (MulAut.conj (ctiGP k)).toMonoidHom ≤ ctiQSub := by
  rw [ctiQSub, gensClosure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  exact mem_ctiQSub_of_ctiMem (rep_conjArr (rep_ctiG hk) (rep_ctiGi hk) (rep_ctiQ hj))
    (cti_Q_parts.2.2.2.2.1 k hk j hj)

theorem ctiGP_mem_normalizer
    {k : ℕ} (hk : k < 9) :
    ctiGP k ∈ Subgroup.normalizer (ctiQSub : Set (Equiv.Perm (Fin 3510))) := by
  have hle := map_conj_ctiQSub_le hk
  have heq : ctiQSub.map (MulAut.conj (ctiGP k)).toMonoidHom = ctiQSub :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Nat.card_congr
      (ctiQSub.equivMapOfInjective _ (MulAut.conj (ctiGP k)).injective).toEquiv))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      change ctiGP k * y * (ctiGP k)⁻¹ = ctiGP k * h * (ctiGP k)⁻¹ at hyh
      simpa using hyh
    rwa [← this]

theorem fi22H_one_le_normalizer :
    fi22H 1 ≤ Subgroup.normalizer (ctiQSub : Set (Equiv.Perm (Fin 3510))) := by
  rw [fi22H_one_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact ctiGP_mem_normalizer hk

theorem ctiQSub_normal :
    (ctiQSub.subgroupOf (fi22H 1)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer ctiQSub_le).2 fi22H_one_le_normalizer

theorem conj_mem_ctiQSub
    {h : Equiv.Perm (Fin 3510)} (hh : h ∈ fi22H 1) {x : Equiv.Perm (Fin 3510)}
    (hx : x ∈ ctiQSub) : h * x * h⁻¹ ∈ ctiQSub :=
  (Subgroup.mem_normalizer_iff.1 (fi22H_one_le_normalizer hh) x).1 hx

theorem ctiZP_commute
    {h : Equiv.Perm (Fin 3510)} (hh : h ∈ fi22H 1) : h * ctiZP = ctiZP * h := by
  have hle : fi22H 1 ≤ Subgroup.centralizer {ctiZP} := by
    rw [fi22H_one_eq, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact eq_of_eqA (rep_compA (rep_ctiG hk) rep_ctiZ) (rep_compA rep_ctiZ (rep_ctiG hk))
      (cti_Q_parts.2.2.2.2.2.2.2.1 k hk)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

abbrev CtiX : Type := {S : Set (Equiv.Perm (Fin 3510)) // ∃ q ∈ ctiQSub, S = {q, q * ctiZP}}

theorem conj_image_pair
    {h q : Equiv.Perm (Fin 3510)} (hh : h ∈ fi22H 1) :
    (fun x => h * x * h⁻¹) '' {q, q * ctiZP} = {h * q * h⁻¹, h * q * h⁻¹ * ctiZP} := by
  have hz : h * ctiZP * h⁻¹ = ctiZP := by rw [ctiZP_commute hh, mul_inv_cancel_right]
  rw [Set.image_pair]
  congr 2
  calc h * (q * ctiZP) * h⁻¹ = h * q * h⁻¹ * (h * ctiZP * h⁻¹) := by group
    _ = h * q * h⁻¹ * ctiZP := by rw [hz]

@[expose] def ctiSmul
    (h : ↥(fi22H 1)) (S : CtiX) : CtiX :=
  ⟨(fun x => (h : Equiv.Perm (Fin 3510)) * x * (h : Equiv.Perm (Fin 3510))⁻¹) '' S.1, by
    obtain ⟨q, hq, hS⟩ := S.2
    refine ⟨(h : Equiv.Perm (Fin 3510)) * q * (h : Equiv.Perm (Fin 3510))⁻¹,
      conj_mem_ctiQSub h.2 hq, ?_⟩
    rw [hS, conj_image_pair h.2]⟩

theorem ctiSmul_val
    (h : ↥(fi22H 1)) (S : CtiX) :
    (ctiSmul h S).1 =
      (fun x => (h : Equiv.Perm (Fin 3510)) * x * (h : Equiv.Perm (Fin 3510))⁻¹) '' S.1 :=
  rfl

theorem ctiSmul_one
    (S : CtiX) : ctiSmul 1 S = S := by
  apply Subtype.ext
  rw [ctiSmul_val]
  simp

theorem ctiSmul_mul
    (h k : ↥(fi22H 1)) (S : CtiX) :
    ctiSmul (h * k) S = ctiSmul h (ctiSmul k S) := by
  apply Subtype.ext
  rw [ctiSmul_val, ctiSmul_val, ctiSmul_val, Set.image_image]
  simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]

instance ctiAct :
    MulAction ↥(fi22H 1) CtiX where
  smul := ctiSmul
  one_smul := ctiSmul_one
  mul_smul := ctiSmul_mul

theorem ctiAct_val
    (h : ↥(fi22H 1)) (S : CtiX) :
    (h • S).1 = (fun x => (h : Equiv.Perm (Fin 3510)) * x * (h : Equiv.Perm (Fin 3510))⁻¹) '' S.1 :=
  rfl

@[expose] def ctiElt (i : ℕ) : Equiv.Perm (Fin 3510) :=
  if h : i < ctiR.1.size then (exists_rep_mem_closure rep_ctiQArr cti_Q_parts.1 i h).choose
  else 1

theorem ctiElt_spec {i : ℕ} (hi : i < 1024) :
    ctiElt i ∈ ctiQSub ∧ Rep 3510 ctiR.1[i]! (ctiElt i) := by
  have hi' : i < ctiR.1.size := cti_Q_parts.2.1 ▸ hi
  rw [ctiElt, dite_eq_left hi']
  exact (exists_rep_mem_closure rep_ctiQArr cti_Q_parts.1 i hi').choose_spec

theorem ctiE_inj
    {i j : ℕ} (hi : i < 1024) (hj : j < 1024) {X : Equiv.Perm (Fin 3510)}
    (hXi : Rep 3510 ctiR.1[i]! X) (hXj : Rep 3510 ctiR.1[j]! X) : i = j := by
  have hkeys := cti_Q_parts.2.2.1
  have hsz := cti_Q_parts.2.1
  have hnd : (ctiR.1.toList.map (keyAt 3510 [0, 1, 2, 3, 6, 4])).Nodup := by
    have hs := CFSG.Certificates.strictIncr_pairwise hkeys
    exact ((List.mergeSort_perm _ _).nodup_iff).1 (hs.imp ne_of_lt)
  have hk := keyAt_eq (n := 3510) (b := [0, 1, 2, 3, 6, 4]) (by decide) hXi hXj
  have key : ∀ {α β : Type} [Inhabited α] (R : Array α) (f : α → β) {i j : ℕ} (hi : i < R.size)
      (hj : j < R.size), (R.toList.map f).Nodup → f R[i]! = f R[j]! → i = j := by
    intro α β _ R f i j hi hj hnd hk
    rw [getElem!_pos R i hi, getElem!_pos R j hj] at hk
    exact (hnd.getElem_inj_iff (i := i) (j := j) (hi := by simpa using hi)
      (hj := by simpa using hj)).1 (by
        simp only [List.getElem_map, Array.getElem_toList]
        exact hk)
  exact key ctiR.1 _ (hsz ▸ hi) (hsz ▸ hj) hnd hk

abbrev ctiCid (i : ℕ) : ℕ := ctiCD.1[i]!

abbrev ctiRep (c : ℕ) : ℕ := ctiCD.2.1[c]!

abbrev ctiRepElt (c : ℕ) : Equiv.Perm (Fin 3510) := ctiElt (ctiRep c)

theorem ctiRep_lt {c : ℕ} (hc : c < 512) : ctiRep c < 1024 :=
  (cti_Q_parts.2.2.2.2.2.2.2.2.2.2.1 c hc).1

theorem ctiCid_ctiRep
    {c : ℕ} (hc : c < 512) : ctiCid (ctiRep c) = c :=
  (cti_Q_parts.2.2.2.2.2.2.2.2.2.2.1 c hc).2

theorem ctiInCoset_spec
    {x : Array ℕ} {X : Equiv.Perm (Fin 3510)} (hX : Rep 3510 x X) {c : ℕ}
    (hc : c < 512) (h : ctiInCoset ctiR.1 ctiZ x (ctiRep c) = true) :
    X = ctiRepElt c ∨ X = ctiRepElt c * ctiZP := by
  have hr := (ctiElt_spec (ctiRep_lt hc)).2
  unfold ctiInCoset at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl (eq_of_eqA hX hr h)
  · exact Or.inr (eq_of_eqA hX (rep_compA hr rep_ctiZ) h)

theorem pair_eq_of_mem
    {x y : Equiv.Perm (Fin 3510)} (h : y = x ∨ y = x * ctiZP) :
    ({y, y * ctiZP} : Set (Equiv.Perm (Fin 3510))) = {x, x * ctiZP} := by
  rcases h with rfl | rfl
  · rfl
  · rw [mul_assoc, ctiZP_mul_self, mul_one, Set.pair_comm]

@[expose] def ctiE (c : Fin 512) : CtiX :=
  ⟨{ctiRepElt c, ctiRepElt c * ctiZP}, ctiRepElt c, (ctiElt_spec (ctiRep_lt c.2)).1, rfl⟩

theorem mem_ctiE_coset {i : ℕ} (hi : i < 1024) :
    ctiElt i = ctiRepElt (ctiCid i) ∨ ctiElt i = ctiRepElt (ctiCid i) * ctiZP := by
  obtain ⟨hlt, -, -, -, hin⟩ := cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.1 i hi
  exact ctiInCoset_spec (ctiElt_spec hi).2 hlt hin

theorem ctiCid_mul_z {i : ℕ} (hi : i < 1024) {j : ℕ} (hj : j < 1024)
    (h : ctiElt j = ctiElt i * ctiZP) : ctiCid j = ctiCid i := by
  obtain ⟨-, hzi, hzeq, hcz, -⟩ := cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.1 i hi
  have hr := rep_of_eqA (rep_compA (ctiElt_spec hi).2 rep_ctiZ) hzeq
  have hji : j = ctiCD.2.2[i]! :=
    ctiE_inj hj hzi (by rw [← h]; exact (ctiElt_spec hj).2) hr
  rw [hji]
  exact hcz

theorem ctiE_injective : Function.Injective ctiE := by
  intro c c' h
  have hS := congrArg Subtype.val h
  have hmem : ctiRepElt c ∈ ({ctiRepElt c', ctiRepElt c' * ctiZP} : Set _) := by
    change ctiRepElt c ∈ (ctiE c').1
    rw [← hS]
    exact Set.mem_insert _ _
  have hr := ctiRep_lt c.2
  have hr' := ctiRep_lt c'.2
  have key : ctiCid (ctiRep c) = ctiCid (ctiRep c') := by
    rcases hmem with h1 | h1
    · have h1' : Rep 3510 ctiR.1[ctiRep c']! (ctiRepElt c) := by
        rw [h1]; exact (ctiElt_spec hr').2
      rw [ctiE_inj hr hr' (ctiElt_spec hr).2 h1']
    · exact ctiCid_mul_z hr' hr h1
  rw [ctiCid_ctiRep c.2, ctiCid_ctiRep c'.2] at key
  exact Fin.ext key

theorem ctiE_surjective : Function.Surjective ctiE := by
  rintro ⟨S, q, hq, rfl⟩
  obtain ⟨i, hi, hrep⟩ := exists_ctiE hq
  have hqi : q = ctiElt i := eq_of_eqA hrep (ctiElt_spec hi).2 (by simp [eqA_iff hrep hrep])
  have hlt := (cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.1 i hi).1
  refine ⟨⟨ctiCid i, hlt⟩, Subtype.ext ?_⟩
  change ({ctiRepElt (ctiCid i), ctiRepElt (ctiCid i) * ctiZP} : Set _) = {q, q * ctiZP}
  rw [hqi, pair_eq_of_mem (mem_ctiE_coset hi)]

@[expose] def ctiEquiv : Fin 512 ≃ CtiX :=
  Equiv.ofBijective ctiE ⟨ctiE_injective, ctiE_surjective⟩

abbrev ctiPhi :
    ↥(fi22H 1) →* Equiv.Perm CtiX := MulAction.toPermHom ↥(fi22H 1) CtiX

@[expose] def permConj {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toFun σ := (e.symm.trans σ).trans e
  invFun τ := (e.trans τ).trans e.symm
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp
  map_mul' σ τ := by ext x; simp

theorem permConj_apply {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (b : β) :
    permConj e σ b = e (σ (e.symm b)) := rfl

abbrev ctiPsi :
    ↥(fi22H 1) →* Equiv.Perm (Fin 512) :=
  (permConj ctiEquiv.symm).toMonoidHom.comp ctiPhi

theorem ctiPsi_apply
    (h : ↥(fi22H 1)) (c : Fin 512) :
    ctiEquiv (ctiPsi h c) = h • ctiEquiv c := by
  change ctiEquiv (ctiEquiv.symm (h • ctiEquiv.symm.symm c)) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_symm]

theorem rep_ctiPis
    {k : ℕ} (hk : k < 9) :
    Rep 512 ctiPis[k]! (ctiPsi ⟨ctiGP k, ctiGP_mem hk⟩) := by
  intro c
  obtain ⟨-, hπ⟩ := cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk
  obtain ⟨hlt, hin⟩ := hπ c c.2
  have hr := ctiRep_lt c.2
  have hconj := ctiInCoset_spec (rep_conjArr (rep_ctiG hk) (rep_ctiGi hk) (ctiElt_spec hr).2)
    hlt hin
  suffices key : ctiPsi ⟨ctiGP k, ctiGP_mem hk⟩ c = ⟨(ctiPis[k]!)[(c : ℕ)]!, hlt⟩ from
    (congrArg Fin.val key).symm
  apply ctiEquiv.injective
  rw [ctiPsi_apply]
  apply Subtype.ext
  rw [ctiAct_val]
  change (fun x => ctiGP k * x * (ctiGP k)⁻¹) '' {ctiRepElt c, ctiRepElt c * ctiZP} =
    ({ctiRepElt ((ctiPis[k]!)[(c : ℕ)]!), ctiRepElt ((ctiPis[k]!)[(c : ℕ)]!) * ctiZP} : Set _)
  rw [conj_image_pair (ctiGP_mem hk), pair_eq_of_mem hconj]

theorem ctiPsi_ctiQP
    {j : ℕ} (hj : j < 10) :
    ctiPsi ⟨ctiQP j, ctiQSub_le (ctiQP_mem hj)⟩ = 1 := by
  refine Equiv.ext fun c => ?_
  rw [Equiv.Perm.one_apply]
  apply ctiEquiv.injective
  rw [ctiPsi_apply]
  apply Subtype.ext
  have hr := ctiRep_lt c.2
  have hrep := (ctiElt_spec hr).2
  have h := cti_Q_parts.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj c c.2
  have hconj : ctiQP j * ctiRepElt c * (ctiQP j)⁻¹ = ctiRepElt c ∨
      ctiQP j * ctiRepElt c * (ctiQP j)⁻¹ = ctiRepElt c * ctiZP := by
    rcases Bool.or_eq_true_iff.1 h with h | h
    · left
      have := eq_of_eqA (rep_compA (rep_ctiQ hj) hrep) (rep_compA hrep (rep_ctiQ hj)) h
      rw [this, mul_inv_cancel_right]
    · right
      have := eq_of_eqA (rep_compA (rep_ctiQ hj) hrep)
        (rep_compA (rep_compA hrep rep_ctiZ) (rep_ctiQ hj)) h
      rw [this, mul_inv_cancel_right]
  rw [ctiAct_val]
  change (fun x => ctiQP j * x * (ctiQP j)⁻¹) '' {ctiRepElt c, ctiRepElt c * ctiZP} =
    {ctiRepElt c, ctiRepElt c * ctiZP}
  rw [conj_image_pair (ctiQSub_le (ctiQP_mem hj)), pair_eq_of_mem hconj]

@[expose] def ctiPiP
    (k : ℕ) : Equiv.Perm (Fin 512) :=
  if hk : k < 9 then ctiPsi ⟨ctiGP k, ctiGP_mem hk⟩ else 1

theorem ctiPis_size :
    ctiPis.size = 9 := cti_Q_parts.2.2.2.2.2.2.2.2.2.1

theorem rep_ctiPiP :
    ∀ k < ctiPis.size, Rep 512 ctiPis[k]! (ctiPiP k) := by
  intro k hk
  rw [ctiPis_size] at hk
  rw [ctiPiP, dite_eq_left hk]
  exact rep_ctiPis hk

theorem range_ctiPsi :
    ctiPsi.range = gensClosure ctiPis ctiPiP := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx' : x ∈ Subgroup.closure {g | ∃ k < 9, ctiGP k = g} := fi22H_one_eq ▸ hx
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      apply Subgroup.subset_closure
      refine ⟨k, by rw [ctiPis_size]; exact hk, ?_⟩
      rw [ctiPiP, dite_eq_left hk]
    | one => exact (map_one ctiPsi) ▸ Subgroup.one_mem _
    | mul y w hy hw ihy ihw =>
      have e : (⟨y * w, hx⟩ : ↥(fi22H 1)) = ⟨y, fi22H_one_eq ▸ hy⟩ * ⟨w, fi22H_one_eq ▸ hw⟩ :=
        rfl
      rw [e, map_mul]
      exact Subgroup.mul_mem _ (ihy _) (ihw _)
    | inv y hy ihy =>
      have e : (⟨y⁻¹, hx⟩ : ↥(fi22H 1)) = (⟨y, fi22H_one_eq ▸ hy⟩ : ↥(fi22H 1))⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ (ihy _)
  · rw [gensClosure, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [ctiPis_size] at hk
    rw [ctiPiP, dite_eq_left hk]
    exact ⟨_, rfl⟩

theorem card_range_ctiPsi :
    Nat.card ctiPsi.range = 51840 := by
  rw [range_ctiPsi, card_closure_of_keysOK rep_ctiPiP cti_image_parts.1 (by decide)
    cti_image_parts.2.2, cti_image_parts.2.1]

theorem card_fi22H_one : Nat.card (fi22H 1) = 53084160 :=
  card_fi22H (c := 1) (by norm_num)

theorem card_ker_ctiPsi :
    Nat.card ctiPsi.ker = 1024 := by
  have h := ctiPsi.ker.card_mul_index
  rw [Subgroup.index_ker, card_range_ctiPsi, card_fi22H_one] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 51840) (h.trans (by norm_num))

theorem ctiQSub_le_ker :
    ctiQSub.subgroupOf (fi22H 1) ≤ ctiPsi.ker := by
  rintro ⟨x, hxH⟩ hx
  rw [Subgroup.mem_subgroupOf] at hx
  change x ∈ Subgroup.closure _ at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    exact ctiPsi_ctiQP hj
  | one => exact Subgroup.one_mem _
  | mul y w hy hw ihy ihw =>
    have e : (⟨y * w, hxH⟩ : ↥(fi22H 1)) =
        ⟨y, ctiQSub_le hy⟩ * ⟨w, ctiQSub_le hw⟩ := rfl
    rw [e]
    exact Subgroup.mul_mem _ (ihy _) (ihw _)
  | inv y hy ihy =>
    have e : (⟨y⁻¹, hxH⟩ : ↥(fi22H 1)) = (⟨y, ctiQSub_le hy⟩ : ↥(fi22H 1))⁻¹ := rfl
    rw [e]
    exact Subgroup.inv_mem _ (ihy _)

theorem ker_ctiPsi :
    ctiPsi.ker = ctiQSub.subgroupOf (fi22H 1) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge ctiQSub_le_ker
  rw [card_ker_ctiPsi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctiQSub_le).toEquiv,
    card_ctiQSub]

theorem fi22H_one_inf_centralizer_le :
    fi22H 1 ⊓ Subgroup.centralizer (ctiQSub : Set (Equiv.Perm (Fin 3510))) ≤ ctiQSub := by
  intro x hx
  obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.1 hx
  have hk : (⟨x, hxH⟩ : ↥(fi22H 1)) ∈ ctiPsi.ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun c => ?_
    rw [Equiv.Perm.one_apply]
    apply ctiEquiv.injective
    rw [ctiPsi_apply]
    apply Subtype.ext
    have hq := (ctiElt_spec (ctiRep_lt c.2)).1
    have h1 : x * ctiRepElt c * x⁻¹ = ctiRepElt c := by
      rw [← Subgroup.mem_centralizer_iff.1 hxc _ hq, mul_inv_cancel_right]
    rw [ctiAct_val]
    change (fun y => x * y * x⁻¹) '' {ctiRepElt c, ctiRepElt c * ctiZP} =
      {ctiRepElt c, ctiRepElt c * ctiZP}
    rw [conj_image_pair hxH, h1]
  rw [ker_ctiPsi, Subgroup.mem_subgroupOf] at hk
  exact hk

theorem CTI_Fi22_second_involution_centralizer_normal_two_subgroup :
    (∃ Q : Subgroup (Equiv.Perm (Fin 3510)), Q ≤ fi22H 1 ∧ (Q.subgroupOf (fi22H 1)).Normal ∧
      Nat.card Q = 1024 ∧
      fi22H 1 ⊓ Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 3510))) ≤ Q) ∧
    (∀ B : Subgroup ↥(fi22H 1), ¬ CFSG.IsComponent B) ∧
    ∀ B : Subgroup (Equiv.Perm (Fin 3510)), ¬ CFSG.Assembly.IsComponentOf B (fi22H 1) := by
  have h2 : IsPGroup 2 ctiQSub := IsPGroup.of_card (n := 10) (by rw [card_ctiQSub]; norm_num)
  have hno : ∀ B : Subgroup (Equiv.Perm (Fin 3510)),
      ¬ CFSG.Assembly.IsComponentOf B (fi22H 1) := fun B hB =>
    CFSG.LocalAnalysis.ComponentInitial.not_isComponentOf_of_selfCentralizing ctiQSub_le
      ctiQSub_normal h2 fi22H_one_inf_centralizer_le hB
  refine ⟨⟨ctiQSub, ctiQSub_le, ctiQSub_normal, card_ctiQSub, fi22H_one_inf_centralizer_le⟩,
    fun B hB => hno (B.map (fi22H 1).subtype) ?_, hno⟩
  have e : (B.map (fi22H 1).subtype).subgroupOf (fi22H 1) = B :=
    Subgroup.comap_map_eq_self_of_injective (fi22H 1).subtype_injective B
  rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (Subgroup.map_subtype_le B), e]
  exact hB

end CFSG.Sporadic.FischerOddCore
