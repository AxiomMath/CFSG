module

public import CFSG.CGT.M24S.NonsplitCoord
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.GroupTheory.PCore.Construction
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S
open scoped Pointwise

abbrev Mt : Type := Matrix (Fin 5) (Fin 5) (ZMod 2)

abbrev Hc : Type := ↥tCent

abbrev cm (x : Hc) : Mt := (x.1 : Matrix (Fin 5) (Fin 5) (ZMod 2))

abbrev tt : Mt := 1 + Matrix.single 0 4 1

theorem coe_tt :
    ((CFSG.Quasithin.H13.transvection15 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Mt) = tt :=
  rfl

theorem cm_comm (x : Hc) : cm x * tt = tt * cm x := by
  have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
  have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) => (g : Mt)) h
  simpa [coe_tt] using h2

theorem cm_mul (x y : Hc) : cm (x * y) = cm x * cm y := rfl

theorem cm_one : cm (1 : Hc) = 1 := rfl

theorem cm_inv_mul (x : Hc) : cm x⁻¹ * cm x = 1 := by
  have h : cm (x⁻¹ * x) = cm 1 := congrArg cm (inv_mul_cancel x)
  rwa [cm_mul, cm_one] at h

theorem cm_mul_inv (x : Hc) : cm x * cm x⁻¹ = 1 := by
  have h : cm (x * x⁻¹) = cm 1 := congrArg cm (mul_inv_cancel x)
  rwa [cm_mul, cm_one] at h

theorem mul_tt_apply (M : Mt) (a b : Fin 5) :
    (M * tt) a b = M a b + if b = 4 then M a 0 else 0 := by
  by_cases hb : b = 4
  · subst hb
    simp [tt, Matrix.mul_add]
  · simp [tt, Matrix.mul_add, hb, Matrix.mul_single_apply_of_ne]

theorem tt_mul_apply (M : Mt) (a b : Fin 5) :
    (tt * M) a b = M a b + if a = 0 then M 4 b else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [tt, Matrix.add_mul]
  · simp [tt, Matrix.add_mul, ha, Matrix.single_mul_apply_of_ne]

theorem cm_entries (x : Hc) :
    (∀ i : Fin 5, cm x i 0 = (1 : Mt) i 0) ∧ (∀ j : Fin 5, cm x 4 j = (1 : Mt) 4 j) := by
  have hc : ∀ a b : Fin 5,
      (if b = 4 then cm x a 0 else 0) = (if a = 0 then cm x 4 b else 0) := by
    intro a b
    have h := congrFun (congrFun (cm_comm x) a) b
    rw [mul_tt_apply, tt_mul_apply] at h
    exact add_left_cancel h
  have h44 : cm x 4 4 = 1 := by
    by_contra hne
    have hsub : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
    have hrow : ∀ j : Fin 5, cm x 4 j = 0 := by
      intro j
      by_cases hj : j = 4
      · subst hj
        exact hsub _ hne
      · have h := hc 0 j
        rw [if_neg hj, if_pos rfl] at h
        exact h.symm
    have hdet : (cm x).det = 1 := x.1.2
    have h0 : (cm x).det = 0 := Matrix.det_eq_zero_of_row_eq_zero 4 hrow
    exact one_ne_zero (hdet.symm.trans h0)
  have h00 : cm x 0 0 = 1 := by
    have h := hc 0 4
    simpa [h44] using h
  have hcol : ∀ a : Fin 5, cm x a 0 = (1 : Mt) a 0 := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [Matrix.one_apply_eq, h00]
    · rw [Matrix.one_apply_ne ha]
      have h := hc a 4
      simpa [ha, h44] using h
  have hrow4 : ∀ j : Fin 5, cm x 4 j = (1 : Mt) 4 j := by
    intro j
    by_cases hj : j = 4
    · subst hj
      rw [Matrix.one_apply_eq, h44]
    · rw [Matrix.one_apply_ne (Ne.symm hj)]
      have h := hc 0 j
      rw [if_neg hj, if_pos rfl] at h
      exact h.symm
  exact ⟨hcol, hrow4⟩

theorem cm_col0 (x : Hc) (i : Fin 5) : cm x i 0 = (1 : Mt) i 0 := (cm_entries x).1 i

theorem cm_row4 (x : Hc) (j : Fin 5) : cm x 4 j = (1 : Mt) 4 j := (cm_entries x).2 j

theorem cm_00 (x : Hc) : cm x 0 0 = 1 := by
  have := cm_col0 x 0
  rwa [Matrix.one_apply_eq] at this

theorem cm_44 (x : Hc) : cm x 4 4 = 1 := by
  have := cm_row4 x 4
  rwa [Matrix.one_apply_eq] at this

theorem det_one_add_of_upper (N : Mt) (hup : ∀ i j : Fin 5, j ≤ i → N i j = 0) :
    (1 + N).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [hup i i le_rfl]
  · intro i j hij
    have hji : j ≤ i := le_of_lt hij
    have hne : i ≠ j := ne_of_gt hij
    simp [Matrix.one_apply, hne, hup i j hji]

theorem tt_comm_of (M : Mt) (hc : ∀ i : Fin 5, M i 0 = (1 : Mt) i 0)
    (hr : ∀ j : Fin 5, M 4 j = (1 : Mt) 4 j) : M * tt = tt * M := by
  ext a b
  rw [mul_tt_apply, tt_mul_apply, hc a, hr b]
  congr 1
  by_cases ha : a = 0 <;> by_cases hb : b = 4
  · subst ha
    subst hb
    simp
  · subst ha
    simp [hb, Matrix.one_apply, Ne.symm hb]
  · subst hb
    simp [ha, Matrix.one_apply]
  · simp [ha, hb, Matrix.one_apply]

@[expose] def unipH (N : Mt) (hup : ∀ i j : Fin 5, j ≤ i → N i j = 0) (hc0 : ∀ i : Fin 5, N i 0 = 0)
    (hr4 : ∀ j : Fin 5, N 4 j = 0) : Hc :=
  ⟨⟨1 + N, det_one_add_of_upper N hup⟩, by
    refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
    show (1 + N) * tt = tt * (1 + N)
    exact tt_comm_of (1 + N) (fun i => by simp [hc0 i]) (fun j => by simp [hr4 j])⟩

theorem cm_unipH (N : Mt) (hup : ∀ i j : Fin 5, j ≤ i → N i j = 0)
    (hc0 : ∀ i : Fin 5, N i 0 = 0) (hr4 : ∀ j : Fin 5, N 4 j = 0) :
    cm (unipH N hup hc0 hr4) = 1 + N := rfl

theorem not_lt_zero' : ∀ i : Fin 5, ¬ i < 0 := by decide

theorem not_gt_four : ∀ j : Fin 5, ¬ 4 < j := by decide

theorem lt_four_of_ne : ∀ i : Fin 5, i ≠ 4 → i < 4 := by decide

@[expose] def unipS (i j : Fin 5) (hij : i < j) (c : ZMod 2) : Hc :=
  unipH (Matrix.single i j c)
    (fun a b hba => by
      rw [Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd hba (not_le.mpr hij)
      · rfl)
    (fun a => by
      rw [Matrix.single_apply]
      split_ifs with h
      · obtain ⟨_, rfl⟩ := h
        exact absurd hij (not_lt_zero' i)
      · rfl)
    (fun b => by
      rw [Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, _⟩ := h
        exact absurd hij (not_gt_four j)
      · rfl)

theorem cm_unipS (i j : Fin 5) (hij : i < j) (c : ZMod 2) :
    cm (unipS i j hij c) = 1 + Matrix.single i j c := rfl

abbrev SuppIn (S : Fin 5 → Fin 5 → Prop) (M : Mt) : Prop := ∀ i j, ¬ S i j → M i j = 0

theorem suppIn_mul_eq_zero {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    {A B : Mt} (hA : SuppIn S A) (hB : SuppIn S B) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : S i k
  · rw [hB k j (fun h' => hS i k j h h'), mul_zero]
  · rw [hA i k h, zero_mul]

theorem mat_add_self (N : Mt) : N + N = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem sq_one_of_supp {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False) {x : Hc}
    (hx : SuppIn S (cm x - 1)) : cm x * cm x = 1 := by
  have hN := suppIn_mul_eq_zero hS hx hx
  have e : cm x * cm x = 1 + ((cm x - 1) + (cm x - 1) + (cm x - 1) * (cm x - 1)) := by
    noncomm_ring
  rw [e, hN, add_zero, mat_add_self, add_zero]

@[expose] def patSub (S : Fin 5 → Fin 5 → Prop) (hS : ∀ i k j, S i k → S k j → False) :
    Subgroup Hc where
  carrier := {x | SuppIn S (cm x - 1)}
  mul_mem' := fun {x y} hx hy => by
    show SuppIn S (cm (x * y) - 1)
    have hz := suppIn_mul_eq_zero hS hx hy
    have e : cm (x * y) - 1 = (cm x - 1) + (cm y - 1) + (cm x - 1) * (cm y - 1) := by
      rw [cm_mul]
      noncomm_ring
    intro i j hij
    rw [e]
    simp [hz, hx i j hij, hy i j hij]
  one_mem' := by
    show SuppIn S (cm 1 - 1)
    rw [cm_one, sub_self]
    intro i j _
    simp
  inv_mem' := fun {x} hx => by
    have hxx : cm x * cm x = 1 := sq_one_of_supp hS hx
    have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Subtype.ext (Subtype.ext hxx))
    show SuppIn S (cm x⁻¹ - 1)
    rw [hinv]
    exact hx

theorem mem_patSub {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False) {x : Hc} :
    x ∈ patSub S hS ↔ SuppIn S (cm x - 1) := Iff.rfl

theorem patSub_comm {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False) {x y : Hc}
    (hx : x ∈ patSub S hS) (hy : y ∈ patSub S hS) : x * y = y * x := by
  rw [mem_patSub] at hx hy
  have h1 := suppIn_mul_eq_zero hS hx hy
  have h2 := suppIn_mul_eq_zero hS hy hx
  have e1 : cm x * cm y = 1 + ((cm x - 1) + (cm y - 1) + (cm x - 1) * (cm y - 1)) := by
    noncomm_ring
  have e2 : cm y * cm x = 1 + ((cm y - 1) + (cm x - 1) + (cm y - 1) * (cm x - 1)) := by
    noncomm_ring
  apply Subtype.ext
  apply Subtype.ext
  show cm x * cm y = cm y * cm x
  rw [e1, e2, h1, h2]
  abel

theorem isElemAbelian_patSub {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False) :
    CFSG.Open.IsElemAbelian 2 (patSub S hS) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (patSub_comm hS a.2 b.2)⟩⟩, fun x hx => ?_⟩
  rw [sq]
  rw [mem_patSub] at hx
  exact Subtype.ext (Subtype.ext (sq_one_of_supp hS hx))

theorem unipS_mem_patSub {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    {i j : Fin 5} (hij : i < j) (c : ZMod 2) (h : S i j) : unipS i j hij c ∈ patSub S hS := by
  refine (mem_patSub hS).2 ?_
  have e : cm (unipS i j hij c) - 1 = Matrix.single i j c := by
    rw [cm_unipS]
    abel
  rw [e]
  intro a b hab
  rw [Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h hab
  · rfl

abbrev S1 (i j : Fin 5) : Prop := i = 0 ∧ j ≠ 0

abbrev S2 (i j : Fin 5) : Prop := j = 4 ∧ i ≠ 4

abbrev SA (i j : Fin 5) : Prop := i.val ≤ 1 ∧ 2 ≤ j.val

theorem hS1 : ∀ i k j, S1 i k → S1 k j → False := fun _ _ _ h1 h2 => h1.2 h2.1

theorem hS2 : ∀ i k j, S2 i k → S2 k j → False := fun _ _ _ h1 h2 => h2.2 h1.1

theorem hSA : ∀ i k j, SA i k → SA k j → False := by
  intro i k j h1 h2
  have := h1.2
  have := h2.1
  omega

@[expose] def U1 : Subgroup Hc := patSub S1 hS1

@[expose] def U2 : Subgroup Hc := patSub S2 hS2

@[expose] def A1 : Subgroup Hc := patSub SA hSA

theorem isElemAbelian_U1 : CFSG.Open.IsElemAbelian 2 U1 := isElemAbelian_patSub hS1
theorem isElemAbelian_A1 : CFSG.Open.IsElemAbelian 2 A1 := isElemAbelian_patSub hSA

theorem row_of_comm (x : Hc) {j : Fin 5} (hj : j ≠ 0)
    (h : (1 + Matrix.single 0 j 1 : Mt) * cm x = cm x * (1 + Matrix.single 0 j 1)) (b : Fin 5) :
    cm x j b = (1 : Mt) j b := by
  have h' := congrFun (congrFun h 0) b
  have hl : (cm x * (1 + Matrix.single 0 j 1 : Mt)) 0 b =
      cm x 0 b + if b = j then cm x 0 0 else 0 := by
    by_cases hb : b = j
    · subst hb
      simp [Matrix.mul_add, Matrix.mul_single_apply_same]
    · simp [Matrix.mul_add, hb, Matrix.mul_single_apply_of_ne]
  have hr : ((1 + Matrix.single 0 j 1 : Mt) * cm x) 0 b = cm x 0 b + cm x j b := by
    simp [Matrix.add_mul, Matrix.single_mul_apply_same]
  rw [hr, hl, cm_00, add_right_inj] at h'
  by_cases hb : b = j
  · subst hb
    simpa using h'
  · rw [if_neg hb] at h'
    rw [Matrix.one_apply, if_neg (Ne.symm hb)]
    exact h'

theorem col_of_comm (x : Hc) {i : Fin 5} (hi : i ≠ 4)
    (h : (1 + Matrix.single i 4 1 : Mt) * cm x = cm x * (1 + Matrix.single i 4 1)) (a : Fin 5) :
    cm x a i = (1 : Mt) a i := by
  have h' := congrFun (congrFun h a) 4
  have hl : (cm x * (1 + Matrix.single i 4 1 : Mt)) a 4 = cm x a 4 + cm x a i := by
    simp [Matrix.mul_add, Matrix.mul_single_apply_same]
  have hr : ((1 + Matrix.single i 4 1 : Mt) * cm x) a 4 =
      cm x a 4 + if a = i then cm x 4 4 else 0 := by
    by_cases ha : a = i
    · subst ha
      simp [Matrix.add_mul, Matrix.single_mul_apply_same]
    · simp [Matrix.add_mul, ha, Matrix.single_mul_apply_of_ne]
  rw [hr, hl, cm_44, add_right_inj] at h'
  by_cases ha : a = i
  · subst ha
    simpa using h'.symm
  · rw [if_neg ha] at h'
    rw [Matrix.one_apply, if_neg ha]
    exact h'.symm

theorem centralizer_U1 : Subgroup.centralizer (U1 : Set Hc) = U1 := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hrow : ∀ j : Fin 5, j ≠ 0 → ∀ b : Fin 5, cm x j b = (1 : Mt) j b := by
      intro j hj b
      have hmem : unipS 0 j (Fin.pos_iff_ne_zero.2 hj) 1 ∈ U1 :=
        unipS_mem_patSub hS1 _ 1 ⟨rfl, hj⟩
      have h := congrArg cm (hx _ hmem)
      rw [cm_mul, cm_mul, cm_unipS] at h
      exact row_of_comm x hj h b
    refine (mem_patSub hS1).2 ?_
    intro i j hij
    by_cases hi : i = 0
    · have hj : j = 0 := by
        by_contra hj
        exact hij ⟨hi, hj⟩
      subst hi
      subst hj
      rw [Matrix.sub_apply, cm_00, Matrix.one_apply_eq, sub_self]
    · rw [Matrix.sub_apply, hrow i hi j, sub_self]
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact patSub_comm hS1 hh hu

theorem centralizer_U2 : Subgroup.centralizer (U2 : Set Hc) = U2 := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hcol : ∀ i : Fin 5, i ≠ 4 → ∀ a : Fin 5, cm x a i = (1 : Mt) a i := by
      intro i hi a
      have hmem : unipS i 4 (lt_four_of_ne i hi) 1 ∈ U2 :=
        unipS_mem_patSub hS2 _ 1 ⟨rfl, hi⟩
      have h := congrArg cm (hx _ hmem)
      rw [cm_mul, cm_mul, cm_unipS] at h
      exact col_of_comm x hi h a
    refine (mem_patSub hS2).2 ?_
    intro i j hij
    by_cases hj : j = 4
    · have hi : i = 4 := by
        by_contra hi
        exact hij ⟨hj, hi⟩
      subst hi
      subst hj
      rw [Matrix.sub_apply, cm_44, Matrix.one_apply_eq, sub_self]
    · rw [Matrix.sub_apply, hcol j hj i, sub_self]
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact patSub_comm hS2 hh hu

theorem mul_add_single_apply (M : Mt) (i j a b : Fin 5) (c : ZMod 2) :
    (M * (1 + Matrix.single i j c)) a b = M a b + if b = j then M a i * c else 0 := by
  by_cases hb : b = j
  · subst hb
    simp [Matrix.mul_add, Matrix.mul_single_apply_same]
  · simp [Matrix.mul_add, hb, Matrix.mul_single_apply_of_ne]

theorem add_single_mul_apply (M : Mt) (i j a b : Fin 5) (c : ZMod 2) :
    ((1 + Matrix.single i j c) * M) a b = M a b + if a = i then c * M j b else 0 := by
  by_cases ha : a = i
  · subst ha
    simp [Matrix.add_mul, Matrix.single_mul_apply_same]
  · simp [Matrix.add_mul, ha, Matrix.single_mul_apply_of_ne]

theorem comm_of_isElemAbelian {E : Subgroup Hc} (hab : CFSG.Open.IsElemAbelian 2 E) {y z : Hc}
    (hy : y ∈ E) (hz : z ∈ E) : y * z = z * y :=
  congrArg Subtype.val (hab.1.is_comm.comm (⟨y, hy⟩ : E) ⟨z, hz⟩)

theorem e02_mem : unipS 0 2 (by decide) 1 ∈ A1 ⊓ U1 :=
  Subgroup.mem_inf.2 ⟨unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩,
    unipS_mem_patSub hS1 _ 1 ⟨rfl, by decide⟩⟩

theorem e03_mem : unipS 0 3 (by decide) 1 ∈ A1 ⊓ U1 :=
  Subgroup.mem_inf.2 ⟨unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩,
    unipS_mem_patSub hS1 _ 1 ⟨rfl, by decide⟩⟩

theorem rows_of_centralizer {x : Hc}
    (hx : x ∈ Subgroup.centralizer ((A1 ⊓ U1 : Subgroup Hc) : Set Hc)) :
    (∀ b : Fin 5, cm x 2 b = (1 : Mt) 2 b) ∧ (∀ b : Fin 5, cm x 3 b = (1 : Mt) 3 b) := by
  rw [Subgroup.mem_centralizer_iff] at hx
  have h2 := congrArg cm (hx _ e02_mem)
  have h3 := congrArg cm (hx _ e03_mem)
  rw [cm_mul, cm_mul, cm_unipS] at h2 h3
  exact ⟨row_of_comm x (by decide) h2, row_of_comm x (by decide) h3⟩

theorem cm_entry_11 {x : Hc} (h2 : ∀ b : Fin 5, cm x 2 b = (1 : Mt) 2 b)
    (h3 : ∀ b : Fin 5, cm x 3 b = (1 : Mt) 3 b) : cm x 1 1 = 1 := by
  have hlow : ∀ i j : Fin 5, j < i → cm x i j = 0 := by
    intro i j hji
    have hcases : ∀ i j : Fin 5, j < i → (i = 1 ∧ j = 0) ∨ (i = 2 ∧ (j = 0 ∨ j = 1)) ∨
        (i = 3 ∧ (j = 0 ∨ j = 1 ∨ j = 2)) ∨ i = 4 := by decide
    rcases hcases i j hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | rfl <;>
      simp [h2, h3, cm_col0, cm_row4, Matrix.one_apply, ne_of_gt hji]
  have hdet : (cm x).det = 1 := x.1.2
  have hup : (cm x).IsUpperTriangular := by
    intro i j hji
    exact hlow i j hji
  rw [Matrix.det_of_isUpperTriangular hup, Fin.prod_univ_five] at hdet
  rw [cm_00, cm_44, h2 2, h3 3] at hdet
  simpa using hdet

@[expose] def Nfun (x : Hc) : Mt :=
  Matrix.of fun i j => if i.val ≤ 1 ∧ 2 ≤ j.val then cm x i j else 0

theorem Nfun_up (x : Hc) : ∀ i j : Fin 5, j ≤ i → Nfun x i j = 0 := by
  intro i j hji
  simp only [Nfun, Matrix.of_apply]
  split_ifs with h
  · exfalso
    have h1 : j.val ≤ i.val := hji
    have := h.1
    have := h.2
    omega
  · rfl

theorem Nfun_c0 (x : Hc) : ∀ i : Fin 5, Nfun x i 0 = 0 := by
  intro i
  simp [Nfun]

theorem Nfun_r4 (x : Hc) : ∀ j : Fin 5, Nfun x 4 j = 0 := by
  intro j
  simp [Nfun]

theorem Nfun_supp (x : Hc) : SuppIn SA (Nfun x) := by
  intro i j hij
  simp only [Nfun, Matrix.of_apply]
  rw [if_neg hij]

theorem mem_A1_mul_U1_of_centralizer {x : Hc}
    (hx : x ∈ Subgroup.centralizer ((A1 ⊓ U1 : Subgroup Hc) : Set Hc)) :
    x ∈ (A1 : Set Hc) * (U1 : Set Hc) := by
  obtain ⟨h2, h3⟩ := rows_of_centralizer hx
  have h11 := cm_entry_11 h2 h3
  have hz : Nfun x * Matrix.single 0 1 (cm x 0 1) = 0 := by
    ext i j
    by_cases hj : j = 1
    · subst hj
      simp [Matrix.mul_single_apply_same, Nfun_c0]
    · simp [Matrix.mul_single_apply_of_ne, hj]
  have key : 1 + Nfun x + Matrix.single 0 1 (cm x 0 1) = cm x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nfun, Matrix.single_apply, Matrix.one_apply, h2, h3, h11, cm_00, cm_col0, cm_row4]
  have ha : unipH (Nfun x) (Nfun_up x) (Nfun_c0 x) (Nfun_r4 x) ∈ A1 := by
    refine (mem_patSub hSA).2 ?_
    have e : (1 + Nfun x - 1 : Mt) = Nfun x := by abel
    rw [cm_unipH, e]
    exact Nfun_supp x
  have hu : unipS 0 1 (by decide) (cm x 0 1) ∈ U1 :=
    unipS_mem_patSub hS1 _ _ ⟨rfl, by decide⟩
  have hxau : unipH (Nfun x) (Nfun_up x) (Nfun_c0 x) (Nfun_r4 x) * unipS 0 1 (by decide) (cm x 0 1)
      = x := by
    apply Subtype.ext
    apply Subtype.ext
    show cm (unipH (Nfun x) (Nfun_up x) (Nfun_c0 x) (Nfun_r4 x) * unipS 0 1 (by decide) (cm x 0 1))
      = cm x
    rw [cm_mul, cm_unipH, cm_unipS]
    calc (1 + Nfun x) * (1 + Matrix.single 0 1 (cm x 0 1))
        = 1 + Nfun x + Matrix.single 0 1 (cm x 0 1) + Nfun x * Matrix.single 0 1 (cm x 0 1) := by
          noncomm_ring
      _ = 1 + Nfun x + Matrix.single 0 1 (cm x 0 1) := by rw [hz, add_zero]
      _ = cm x := key
  exact Set.mem_mul.2 ⟨_, ha, _, hu, hxau⟩

theorem mul_mem_centralizer {a u : Hc} (ha : a ∈ A1) (hu : u ∈ U1) :
    a * u ∈ Subgroup.centralizer ((A1 ⊓ U1 : Subgroup Hc) : Set Hc) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨hbA, hbU⟩ := Subgroup.mem_inf.1 hb
  have h1 : b * a = a * b := patSub_comm hSA hbA ha
  have h2 : b * u = u * b := patSub_comm hS1 hbU hu
  calc b * (a * u) = (b * a) * u := (mul_assoc _ _ _).symm
    _ = (a * b) * u := by rw [h1]
    _ = a * (b * u) := mul_assoc _ _ _
    _ = a * (u * b) := by rw [h2]
    _ = (a * u) * b := (mul_assoc _ _ _).symm

theorem centralizer_B_eq :
    (Subgroup.centralizer ((A1 ⊓ U1 : Subgroup Hc) : Set Hc) : Set Hc) =
      (A1 : Set Hc) * (U1 : Set Hc) := by
  ext x
  constructor
  · intro hx
    exact mem_A1_mul_U1_of_centralizer hx
  · intro hx
    obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.1 hx
    exact mul_mem_centralizer ha hu

theorem fin5_le_zero : ∀ j : Fin 5, j ≤ 0 → j = 0 := by decide

theorem fin5_four_le : ∀ i : Fin 5, 4 ≤ i → i = 4 := by decide

theorem fin5_A_up : ∀ i j : Fin 5, j ≤ i → ¬ (i.val ≤ 1 ∧ 2 ≤ j.val) := by decide

theorem fin5_A_zero : ∀ i : Fin 5, ¬ (i.val ≤ 1 ∧ 2 ≤ (0 : Fin 5).val) := by decide

theorem fin5_A_four : ∀ j : Fin 5, ¬ ((4 : Fin 5).val ≤ 1 ∧ 2 ≤ j.val) := by decide

@[expose] def unipOfS1 (N : Mt) (hN : SuppIn S1 N) : Hc :=
  unipH N (fun i j hji => hN i j (fun h => h.2 (fin5_le_zero j (h.1 ▸ hji))))
    (fun i => hN i 0 (fun h => h.2 rfl))
    (fun j => hN 4 j (fun h => absurd h.1 (by decide)))

@[expose] def unipOfS2 (N : Mt) (hN : SuppIn S2 N) : Hc :=
  unipH N (fun i j hji => hN i j (fun h => h.2 (fin5_four_le i (h.1 ▸ hji))))
    (fun i => hN i 0 (fun h => absurd h.1 (by decide)))
    (fun j => hN 4 j (fun h => h.2 rfl))

@[expose] def unipOfSA (N : Mt) (hN : SuppIn SA N) : Hc :=
  unipH N (fun i j hji => hN i j (fin5_A_up i j hji))
    (fun i => hN i 0 (fin5_A_zero i))
    (fun j => hN 4 j (fin5_A_four j))

theorem cm_unipOfS1 (N : Mt) (hN : SuppIn S1 N) : cm (unipOfS1 N hN) = 1 + N := rfl

theorem cm_unipOfS2 (N : Mt) (hN : SuppIn S2 N) : cm (unipOfS2 N hN) = 1 + N := rfl

theorem unipOfS1_mem (N : Mt) (hN : SuppIn S1 N) : unipOfS1 N hN ∈ U1 := by
  refine (mem_patSub hS1).2 ?_
  have e : (1 + N - 1 : Mt) = N := by abel
  rw [cm_unipOfS1, e]
  exact hN

theorem unipOfS2_mem (N : Mt) (hN : SuppIn S2 N) : unipOfS2 N hN ∈ U2 := by
  refine (mem_patSub hS2).2 ?_
  have e : (1 + N - 1 : Mt) = N := by abel
  rw [cm_unipOfS2, e]
  exact hN

theorem supp_conj_S1 {A B N : Mt} (hA : ∀ i, A i 0 = (1 : Mt) i 0)
    (hB : ∀ i, B i 0 = (1 : Mt) i 0) (hN : SuppIn S1 N) : SuppIn S1 (A * N * B) := by
  have hNl : ∀ l k, l ≠ 0 → N l k = 0 := fun l k hl => hN l k (fun h => hl h.1)
  have hAN : ∀ i k, (A * N) i k = A i 0 * N 0 k := by
    intro i k
    rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin 5)]
    · intro l _ hl
      rw [hNl l k hl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro i j hij
  rw [Matrix.mul_apply]
  by_cases hi : i = 0
  · subst hi
    have hj : j = 0 := by
      by_contra hj
      exact hij ⟨rfl, hj⟩
    subst hj
    rw [Finset.sum_eq_single (0 : Fin 5)]
    · rw [hAN 0 0, hN 0 0 (fun h => h.2 rfl), mul_zero, zero_mul]
    · intro k _ hk
      rw [hB k, Matrix.one_apply_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · apply Finset.sum_eq_zero
    intro k _
    rw [hAN i k, hA i, Matrix.one_apply_ne hi, zero_mul, zero_mul]

theorem supp_conj_S2 {A B N : Mt} (hA : ∀ k, A 4 k = (1 : Mt) 4 k)
    (hB : ∀ k, B 4 k = (1 : Mt) 4 k) (hN : SuppIn S2 N) : SuppIn S2 (A * N * B) := by
  have hNl : ∀ k l, l ≠ 4 → N k l = 0 := fun k l hl => hN k l (fun h => hl h.1)
  have hAN : ∀ i k, k ≠ 4 → (A * N) i k = 0 := by
    intro i k hk
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rw [hNl l k hk, mul_zero]
  have hANB : ∀ i j, (A * N * B) i j = (A * N) i 4 * B 4 j := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (4 : Fin 5)]
    · intro k _ hk
      rw [hAN i k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro i j hij
  rw [hANB]
  by_cases hj : j = 4
  · subst hj
    have hi : i = 4 := by
      by_contra hi
      exact hij ⟨rfl, hi⟩
    subst hi
    have h44 : (A * N) 4 4 = 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (4 : Fin 5)]
      · rw [hN 4 4 (fun h => h.2 rfl), mul_zero]
      · intro l _ hl
        rw [hA l, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [h44, zero_mul]
  · rw [hB j, Matrix.one_apply_ne (Ne.symm hj), mul_zero]

theorem U1_normal_conj (h : Hc) {x : Hc} (hx : x ∈ U1) : h * x * h⁻¹ ∈ U1 := by
  have hx' : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 hx
  refine (mem_patSub hS1).2 ?_
  have e : cm (h * x * h⁻¹) - 1 = cm h * (cm x - 1) * cm h⁻¹ := by
    rw [cm_mul, cm_mul]
    calc cm h * cm x * cm h⁻¹ - 1 = cm h * cm x * cm h⁻¹ - cm h * cm h⁻¹ := by
          rw [cm_mul_inv]
      _ = cm h * (cm x - 1) * cm h⁻¹ := by noncomm_ring
  rw [e]
  exact supp_conj_S1 (fun i => cm_col0 h i) (fun i => cm_col0 h⁻¹ i) hx'

theorem U2_normal_conj (h : Hc) {x : Hc} (hx : x ∈ U2) : h * x * h⁻¹ ∈ U2 := by
  have hx' : SuppIn S2 (cm x - 1) := (mem_patSub hS2).1 hx
  refine (mem_patSub hS2).2 ?_
  have e : cm (h * x * h⁻¹) - 1 = cm h * (cm x - 1) * cm h⁻¹ := by
    rw [cm_mul, cm_mul]
    calc cm h * cm x * cm h⁻¹ - 1 = cm h * cm x * cm h⁻¹ - cm h * cm h⁻¹ := by
          rw [cm_mul_inv]
      _ = cm h * (cm x - 1) * cm h⁻¹ := by noncomm_ring
  rw [e]
  exact supp_conj_S2 (fun k => cm_row4 h k) (fun k => cm_row4 h⁻¹ k) hx'

instance normal_U1 : U1.Normal := ⟨fun _ hn g => U1_normal_conj g hn⟩

instance normal_U2 : U2.Normal := ⟨fun _ hn g => U2_normal_conj g hn⟩

@[expose] def paramN1 (v : Fin 4 → ZMod 2) : Mt :=
  Matrix.single 0 1 (v 0) + Matrix.single 0 2 (v 1) + Matrix.single 0 3 (v 2) +
    Matrix.single 0 4 (v 3)

theorem paramN1_supp (v : Fin 4 → ZMod 2) : SuppIn S1 (paramN1 v) := by
  intro i j hij
  by_cases hi : i = 0
  · subst hi
    have hj : j = 0 := by
      by_contra hj
      exact hij ⟨rfl, hj⟩
    subst hj
    simp [paramN1, Matrix.single_apply]
  · simp [paramN1, Matrix.single_apply, Ne.symm hi]

@[expose] def idx4 : Fin 4 → Fin 5 := ![1, 2, 3, 4]

theorem paramN1_entry (v : Fin 4 → ZMod 2) (k : Fin 4) : paramN1 v 0 (idx4 k) = v k := by
  fin_cases k <;> simp [paramN1, idx4]

theorem card_U1 : Nat.card U1 = 16 := by
  let f : (Fin 4 → ZMod 2) → U1 := fun v => ⟨unipOfS1 (paramN1 v) (paramN1_supp v),
    unipOfS1_mem _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      have hvw' := congrArg Subtype.val hvw
      have h1 : (1 + paramN1 v : Mt) = 1 + paramN1 w := by
        rw [← cm_unipOfS1 (paramN1 v) (paramN1_supp v),
          ← cm_unipOfS1 (paramN1 w) (paramN1_supp w)]
        exact congrArg cm hvw'
      have h2 := add_left_cancel h1
      funext k
      have := congrFun (congrFun h2 0) (idx4 k)
      rwa [paramN1_entry, paramN1_entry] at this
    · rintro ⟨x, hx⟩
      refine ⟨fun k => cm x 0 (idx4 k), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have hxS : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 hx
      have hxrow : ∀ i j, i ≠ 0 → cm x i j = (1 : Mt) i j := by
        intro i j hi
        have := hxS i j (fun h => hi h.1)
        rw [Matrix.sub_apply] at this
        exact sub_eq_zero.1 this
      show (1 + paramN1 _ : Mt) = cm x
      ext i j
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          simp [paramN1, cm_00 x]
        · have hj4 : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
            revert hj
            revert j
            decide
          rcases hj4 with rfl | rfl | rfl | rfl <;>
            simp [paramN1, Matrix.single_apply, idx4]
      · rw [hxrow i j hi]
        simp [paramN1, Matrix.single_apply, Ne.symm hi]
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_eq_fintype_card]

@[expose] def zt : Hc :=
  ⟨CFSG.Quasithin.H13.transvection15, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem cm_zt : cm zt = tt := rfl

theorem zt_eq_unipS : zt = unipS 0 4 (by decide) 1 := rfl

theorem zt_mem_inf : zt ∈ U1 ⊓ U2 := by
  rw [zt_eq_unipS]
  exact Subgroup.mem_inf.2 ⟨unipS_mem_patSub hS1 _ 1 ⟨rfl, by decide⟩,
    unipS_mem_patSub hS2 _ 1 ⟨rfl, by decide⟩⟩

theorem U1_inf_U2 : U1 ⊓ U2 = Subgroup.zpowers zt := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hS1x : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 h1
    have hS2x : SuppIn S2 (cm x - 1) := (mem_patSub hS2).1 h2
    have hoff : ∀ i j, ¬ (i = 0 ∧ j = 4) → cm x i j = (1 : Mt) i j := by
      intro i j hij
      by_cases a1 : S1 i j
      · have a2 : ¬ S2 i j := fun a2 => hij ⟨a1.1, a2.1⟩
        have h := hS2x i j a2
        rw [Matrix.sub_apply] at h
        exact sub_eq_zero.1 h
      · have h := hS1x i j a1
        rw [Matrix.sub_apply] at h
        exact sub_eq_zero.1 h
    have hform : cm x = 1 + Matrix.single 0 4 (cm x 0 4) := by
      ext i j
      by_cases hij : i = 0 ∧ j = 4
      · obtain ⟨rfl, rfl⟩ := hij
        rw [Matrix.add_apply, Matrix.one_apply_ne (by decide : (0 : Fin 5) ≠ 4), zero_add,
          Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
      · rw [hoff i j hij, Matrix.add_apply, Matrix.single_apply,
          if_neg (fun h => hij ⟨h.1.symm, h.2.symm⟩), add_zero]
    have hc : cm x 0 4 = 0 ∨ cm x 0 4 = 1 := by
      have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact hz _
    rcases hc with hc | hc
    · have hx1 : x = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        show cm x = 1
        rw [hform, hc, Matrix.single_zero, add_zero]
      rw [hx1]
      exact Subgroup.one_mem _
    · have hxz : x = zt := by
        apply Subtype.ext
        apply Subtype.ext
        show cm x = cm zt
        rw [cm_zt, hform, hc]
      rw [hxz]
      exact Subgroup.mem_zpowers zt
  · rw [Subgroup.zpowers_le]
    exact zt_mem_inf

theorem mul_row0 (A B : Mt) (hA : ∀ k, A 0 k = (1 : Mt) 0 k) (j : Fin 5) :
    (A * B) 0 j = B 0 j := by
  have h : (A * B) 0 j = (1 * B) 0 j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [hA k])
  rw [h, Matrix.one_mul]

@[expose] def K1 : Subgroup Hc where
  carrier := {x | ∀ j : Fin 5, cm x 0 j = (1 : Mt) 0 j}
  mul_mem' := fun {x y} hx hy j => by
    have hx' : ∀ j : Fin 5, cm x 0 j = (1 : Mt) 0 j := hx
    have hy' : ∀ j : Fin 5, cm y 0 j = (1 : Mt) 0 j := hy
    show cm (x * y) 0 j = (1 : Mt) 0 j
    rw [cm_mul, mul_row0 _ _ hx' j, hy' j]
  one_mem' := fun j => by
    show cm 1 0 j = (1 : Mt) 0 j
    rw [cm_one]
  inv_mem' := fun {x} hx j => by
    have hx' : ∀ j : Fin 5, cm x 0 j = (1 : Mt) 0 j := hx
    show cm x⁻¹ 0 j = (1 : Mt) 0 j
    have h := mul_row0 (cm x) (cm x⁻¹) hx' j
    rw [cm_mul_inv] at h
    exact h.symm

theorem K1_inf_U1 : K1 ⊓ U1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hK, hU⟩ := Subgroup.mem_inf.1 hx
  have hK' : ∀ j : Fin 5, cm x 0 j = (1 : Mt) 0 j := hK
  have hU' : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 hU
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  show cm x = 1
  ext i j
  by_cases hi : i = 0
  · subst hi
    exact hK' j
  · have h := hU' i j (fun h => hi h.1)
    rw [Matrix.sub_apply] at h
    exact sub_eq_zero.1 h

theorem zmod2_aux (a b : ZMod 2) : a + (a - b) = b := by
  revert a b
  decide

@[expose] def sK1 (x : Hc) : Fin 5 → ZMod 2 := fun j => cm x 0 j - (1 : Mt) 0 j

@[expose] def phiK1 (x : Hc) : Fin 5 → ZMod 2 := Matrix.vecMul (sK1 x) (cm x⁻¹)

theorem phiK1_zero (x : Hc) : phiK1 x 0 = 0 := by
  show ∑ i, sK1 x i * cm x⁻¹ i 0 = 0
  rw [Finset.sum_eq_single (0 : Fin 5)]
  · rw [cm_col0 x⁻¹ 0, Matrix.one_apply_eq, mul_one]
    show cm x 0 0 - (1 : Mt) 0 0 = 0
    rw [cm_00, Matrix.one_apply_eq, sub_self]
  · intro i _ hi
    rw [cm_col0 x⁻¹ i, Matrix.one_apply_ne hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem phiK1_vecMul (x : Hc) : Matrix.vecMul (phiK1 x) (cm x) = sK1 x := by
  show Matrix.vecMul (Matrix.vecMul (sK1 x) (cm x⁻¹)) (cm x) = sK1 x
  rw [Matrix.vecMul_vecMul, cm_inv_mul, Matrix.vecMul_one]

@[expose] def NK1 (x : Hc) : Mt :=
  Matrix.of fun i j => if i = 0 ∧ j ≠ 0 then phiK1 x j else 0

theorem NK1_supp (x : Hc) : SuppIn S1 (NK1 x) := by
  intro i j hij
  show (if i = 0 ∧ j ≠ 0 then phiK1 x j else 0) = 0
  rw [if_neg hij]

theorem NK1_row0 (x : Hc) (m : Fin 5) : NK1 x 0 m = phiK1 x m := by
  show (if (0 : Fin 5) = 0 ∧ m ≠ 0 then phiK1 x m else 0) = phiK1 x m
  by_cases hm : m = 0
  · subst hm
    rw [if_neg (fun h => h.2 rfl), phiK1_zero]
  · rw [if_pos ⟨rfl, hm⟩]

theorem K1_decomp (x : Hc) : ∃ u ∈ U1, ∃ k ∈ K1, x = u * k := by
  refine ⟨unipOfS1 (NK1 x) (NK1_supp x), unipOfS1_mem _ _,
    unipOfS1 (NK1 x) (NK1_supp x) * x, ?_, ?_⟩
  · intro j
    show cm (unipOfS1 (NK1 x) (NK1_supp x) * x) 0 j = (1 : Mt) 0 j
    rw [cm_mul, cm_unipOfS1, Matrix.add_mul, Matrix.add_apply, Matrix.one_mul]
    have hsum1 : (NK1 x * cm x) 0 j = ∑ m, phiK1 x m * cm x m j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun m _ => by rw [NK1_row0])
    have hsum2 : ∑ m, phiK1 x m * cm x m j = sK1 x j := congrFun (phiK1_vecMul x) j
    rw [hsum1, hsum2]
    show cm x 0 j + (cm x 0 j - (1 : Mt) 0 j) = (1 : Mt) 0 j
    exact zmod2_aux _ _
  · have hu2 : unipOfS1 (NK1 x) (NK1_supp x) ^ 2 = 1 :=
      isElemAbelian_U1.2 _ (unipOfS1_mem _ _)
    rw [← mul_assoc, ← sq, hu2, one_mul]

theorem K1_sup_U1 : K1 ⊔ U1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, hu, k, hk, rfl⟩ := K1_decomp x
  exact mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hk)

abbrev inB (i : Fin 5) : Prop := 1 ≤ i.val ∧ i.val ≤ 3

@[expose] def idx3 : Fin 3 → Fin 5 := ![1, 2, 3]

@[expose] def idxB : Fin 5 → Fin 3 := ![0, 0, 1, 2, 0]

theorem idx3_ne0 : ∀ i : Fin 3, idx3 i ≠ 0 := by decide

theorem idx3_ne4 : ∀ i : Fin 3, idx3 i ≠ 4 := by decide

theorem idx3_inj : ∀ i j : Fin 3, idx3 i = idx3 j → i = j := by decide

theorem inB_idx3 : ∀ i : Fin 3, inB (idx3 i) := by decide

theorem idx3_idxB : ∀ i : Fin 5, inB i → idx3 (idxB i) = i := by decide

theorem idxB_idx3 : ∀ i : Fin 3, idxB (idx3 i) = i := by decide

theorem idxB_inj : ∀ i j : Fin 5, inB i → inB j → idxB i = idxB j → i = j := by decide

@[expose] def blk (M : Mt) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => M (idx3 i) (idx3 j)

theorem blk_apply (M : Mt) (i j : Fin 3) : blk M i j = M (idx3 i) (idx3 j) := rfl

theorem blk_one : blk (1 : Mt) = 1 := by
  ext i j
  rw [blk_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hij, if_neg (fun h => hij (idx3_inj i j h))]

theorem blk_mul (M N : Mt) (hM : ∀ i, M (idx3 i) 0 = 0) (hN : ∀ j, N 4 (idx3 j) = 0) :
    blk (M * N) = blk M * blk N := by
  ext i j
  rw [blk_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three]
  simp only [blk_apply]
  rw [hM i, hN j]
  simp only [zero_mul, mul_zero, zero_add, add_zero]
  rfl

theorem cm_hM (x : Hc) : ∀ i : Fin 3, cm x (idx3 i) 0 = 0 := fun i => by
  rw [cm_col0, Matrix.one_apply_ne (idx3_ne0 i)]

theorem cm_hN (x : Hc) : ∀ j : Fin 3, cm x 4 (idx3 j) = 0 := fun j => by
  rw [cm_row4, Matrix.one_apply_ne (Ne.symm (idx3_ne4 j))]

@[expose] def piUnit (x : Hc) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  Units.mk (blk (cm x)) (blk (cm x⁻¹))
    (by rw [← blk_mul _ _ (cm_hM x) (cm_hN x⁻¹), cm_mul_inv, blk_one])
    (by rw [← blk_mul _ _ (cm_hM x⁻¹) (cm_hN x), cm_inv_mul, blk_one])

theorem piUnit_val (x : Hc) : (piUnit x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = blk (cm x) := rfl

@[expose] def piHom : Hc →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) where
  toFun := piUnit
  map_one' := Units.ext (by
    rw [piUnit_val, cm_one, blk_one, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, piUnit_val, piUnit_val, piUnit_val, cm_mul, blk_mul _ _ (cm_hM x) (cm_hN y)])

abbrev SQ (i j : Fin 5) : Prop := (i = 0 ∧ j ≠ 0) ∨ (j = 4 ∧ inB i)

theorem hSQ3 : ∀ i k l j : Fin 5, SQ i k → SQ k l → SQ l j → False := by decide

@[expose] def Qh : Subgroup Hc := piHom.ker

theorem mem_Qh_iff (x : Hc) : x ∈ Qh ↔ SuppIn SQ (cm x - 1) := by
  constructor
  · intro hx
    have hb : blk (cm x) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hx)
    intro i j hij
    rw [Matrix.sub_apply]
    have hfin : ∀ i : Fin 5, i = 0 ∨ i = 4 ∨ inB i := by decide
    rcases hfin i with rfl | rfl | hi
    · have hj : j = 0 := by
        by_contra hj
        exact hij (Or.inl ⟨rfl, hj⟩)
      subst hj
      rw [cm_00, Matrix.one_apply_eq, sub_self]
    · rw [cm_row4, sub_self]
    · have hfin2 : ∀ j : Fin 5, j = 0 ∨ j = 4 ∨ inB j := by decide
      rcases hfin2 j with rfl | rfl | hj
      · have hi0 : i ≠ 0 := by
          rintro rfl
          exact absurd hi (by decide)
        rw [cm_col0, Matrix.one_apply_ne hi0, sub_self]
      · exact absurd (Or.inr ⟨rfl, hi⟩) hij
      · have h1 := congrFun (congrFun hb (idxB i)) (idxB j)
        rw [blk_apply, idx3_idxB i hi, idx3_idxB j hj, Matrix.one_apply] at h1
        rw [Matrix.one_apply, sub_eq_zero, h1]
        by_cases hij' : i = j
        · subst hij'
          rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hij', if_neg (fun h => hij' (idxB_inj i j hi hj h))]
  · intro h
    apply MonoidHom.mem_ker.2
    apply Units.ext
    show blk (cm x) = 1
    ext i j
    rw [blk_apply, Matrix.one_apply]
    have hns : ¬ SQ (idx3 i) (idx3 j) := fun hh =>
      hh.elim (fun h' => idx3_ne0 i h'.1) (fun h' => idx3_ne4 j h'.1)
    have h1 := h (idx3 i) (idx3 j) hns
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at h1
    rw [h1]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hij (idx3_inj i j h)), if_neg hij]

instance isSimpleGroup_GL3 : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (by norm_num)

@[expose] def emb (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Mt :=
  Matrix.of fun i j => if inB i ∧ inB j then A (idxB i) (idxB j) else if i = j then 1 else 0

theorem emb_blk (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : blk (emb A) = A := by
  ext i j
  rw [blk_apply]
  show (if inB (idx3 i) ∧ inB (idx3 j) then A (idxB (idx3 i)) (idxB (idx3 j)) else
    if idx3 i = idx3 j then 1 else 0) = A i j
  rw [if_pos ⟨inB_idx3 i, inB_idx3 j⟩, idxB_idx3, idxB_idx3]

theorem emb_col0 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i : Fin 5) : emb A i 0 = (1 : Mt) i 0 := by
  show (if inB i ∧ inB 0 then A (idxB i) (idxB 0) else if i = 0 then 1 else 0) = (1 : Mt) i 0
  rw [if_neg (fun h => absurd h.2 (by decide)), Matrix.one_apply]

theorem emb_row4 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (j : Fin 5) : emb A 4 j = (1 : Mt) 4 j := by
  show (if inB 4 ∧ inB j then A (idxB 4) (idxB j) else if 4 = j then 1 else 0) = (1 : Mt) 4 j
  rw [if_neg (fun h => absurd h.1 (by decide)), Matrix.one_apply]

theorem emb_one : emb 1 = 1 := by
  ext i j
  show (if inB i ∧ inB j then (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) (idxB i) (idxB j)
    else if i = j then 1 else 0) = (1 : Mt) i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : inB i
    · rw [if_pos ⟨hi, hi⟩, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [if_neg (fun h => hi h.1), if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg hij, Matrix.one_apply_ne hij]
    by_cases hi : inB i ∧ inB j
    · rw [if_pos hi, Matrix.one_apply_ne (fun h => hij (idxB_inj i j hi.1 hi.2 h))]
    · rw [if_neg hi]

theorem emb_mul (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : emb (A * B) = emb A * emb B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, inB, idxB]

theorem det_emb (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
    (emb (A : Matrix (Fin 3) (Fin 3) (ZMod 2))).det = 1 := by
  have h1 : emb (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * emb ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← emb_mul, Units.mul_inv, emb_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  have hz : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide
  exact hz _ _ h2

@[expose] def leviSL (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Hc :=
  ⟨⟨emb (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), det_emb A⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (tt_comm_of _ (emb_col0 _) (emb_row4 _)))⟩

theorem cm_leviSL (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
    cm (leviSL A) = emb (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

theorem piHom_leviSL (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : piHom (leviSL A) = A := by
  apply Units.ext
  show blk (cm (leviSL A)) = (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [cm_leviSL, emb_blk]

theorem piHom_surjective : Function.Surjective piHom := fun A => ⟨leviSL A, piHom_leviSL A⟩

theorem card_GL3 : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 :=
  CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two

theorem suppIn_mul3_eq_zero {S : Fin 5 → Fin 5 → Prop}
    (hS : ∀ i k l j, S i k → S k l → S l j → False) {A B C : Mt} (hA : SuppIn S A)
    (hB : SuppIn S B) (hC : SuppIn S C) : A * B * C = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  by_cases h1 : S i l
  · by_cases h2 : S l k
    · by_cases h3 : S k j
      · exact (hS i l k j h1 h2 h3).elim
      · rw [hC k j h3, mul_zero]
    · rw [hB l k h2, mul_zero, zero_mul]
  · rw [hA i l h1, zero_mul, zero_mul]

theorem Qh_pow_four {x : Hc} (hx : x ∈ Qh) : x ^ 4 = 1 := by
  have hN : SuppIn SQ (cm x - 1) := (mem_Qh_iff x).1 hx
  have hN3 : (cm x - 1) * (cm x - 1) * (cm x - 1) = 0 :=
    suppIn_mul3_eq_zero hSQ3 hN hN hN
  have hMM : cm x * cm x = 1 + (cm x - 1) * (cm x - 1) := by
    have e : cm x * cm x = 1 + ((cm x - 1) + (cm x - 1) + (cm x - 1) * (cm x - 1)) := by
      noncomm_ring
    rw [e, mat_add_self, zero_add]
  have hNNNN : (cm x - 1) * (cm x - 1) * ((cm x - 1) * (cm x - 1)) = 0 := by
    rw [← mul_assoc, hN3, zero_mul]
  have hpow : cm (x ^ 4) = 1 := by
    have e4 : x ^ 4 = (x * x) * (x * x) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [e4, cm_mul, cm_mul, hMM]
    have e2 : (1 + (cm x - 1) * (cm x - 1)) * (1 + (cm x - 1) * (cm x - 1)) =
        1 + ((cm x - 1) * (cm x - 1) + (cm x - 1) * (cm x - 1) +
          (cm x - 1) * (cm x - 1) * ((cm x - 1) * (cm x - 1))) := by
      noncomm_ring
    rw [e2, mat_add_self, zero_add, hNNNN, add_zero]
  exact Subtype.ext (Subtype.ext hpow)

theorem isPGroup_Qh : IsPGroup 2 Qh := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  show (g : Hc) ^ 2 ^ 2 = 1
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  exact Qh_pow_four g.2

theorem pCore_eq_Qh : CFSG.pCore 2 Hc = Qh := by
  haveI : Qh.Normal := MonoidHom.normal_ker piHom
  apply le_antisymm
  · apply sSup_le
    rintro K ⟨hKn, hKp⟩
    haveI : (K.map piHom).Normal := hKn.map piHom piHom_surjective
    have hKmp : IsPGroup 2 (K.map piHom) := hKp.map piHom
    rcases Subgroup.Normal.eq_bot_or_eq_top (K.map piHom) with hbot | htop
    · intro k hk
      have hmem : piHom k ∈ K.map piHom := Subgroup.mem_map_of_mem piHom hk
      rw [hbot, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.2 hmem
    · exfalso
      have hcard : Nat.card (K.map piHom) = 168 := by
        rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, card_GL3]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hKmp
      rw [hcard] at hn
      have hlt : n < 8 := by
        by_contra hc
        have hc' : 8 ≤ n := by omega
        have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc'
        omega
      interval_cases n <;> norm_num at hn
  · exact le_sSup ⟨inferInstance, isPGroup_Qh⟩

abbrev Tri : Type := ZMod 2 × ZMod 2 × ZMod 2

@[expose] def tstar (p q : Tri) : Tri :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.2.1 * q.1)

@[expose] def tabR (k : ZMod 4) : Tri :=
  if k = 0 then (0, 0, 0) else if k = 1 then (1, 1, 0) else if k = 2 then (0, 0, 1) else (1, 1, 1)

@[expose] def tabS (k : ZMod 4) : Tri :=
  if k = 0 then (1, 0, 0) else if k = 1 then (0, 1, 0) else if k = 2 then (1, 0, 1) else (0, 1, 1)

@[expose] def Tab : DihedralGroup 4 → Tri
  | .r k => tabR k
  | .sr k => tabS k

theorem Tab_mul : ∀ g h : DihedralGroup 4, Tab (g * h) = tstar (Tab g) (Tab h) := by decide

theorem Tab_inj : ∀ g h : DihedralGroup 4, Tab g = Tab h → g = h := by decide

theorem Tab_one : Tab 1 = (0, 0, 0) := by decide

theorem Tab_surj : ∀ p : Tri, ∃ g : DihedralGroup 4, Tab g = p := by decide

@[expose] def Dmat (i : Fin 5) (p : Tri) : Mt :=
  Matrix.single i 4 p.1 + Matrix.single 0 i p.2.1 + Matrix.single 0 4 p.2.2

abbrev SDi (i a b : Fin 5) : Prop := (a = i ∧ b = 4) ∨ (a = 0 ∧ b = i) ∨ (a = 0 ∧ b = 4)

theorem SDi_lt : ∀ i a b : Fin 5, inB i → SDi i a b → a < b := by decide

theorem SDi_sub_SQ : ∀ i a b : Fin 5, inB i → SDi i a b → SQ a b := by decide

theorem S1_sub_SQ : ∀ a b : Fin 5, S1 a b → SQ a b := by decide

theorem S2_sub_SQ : ∀ a b : Fin 5, S2 a b → SQ a b := by decide

theorem Dmat_supp (i : Fin 5) (hi : inB i) (p : Tri) : SuppIn (SDi i) (Dmat i p) := by
  intro a b hab
  have h1 : ¬ (i = a ∧ (4 : Fin 5) = b) := fun h => hab (Or.inl ⟨h.1.symm, h.2.symm⟩)
  have h2 : ¬ ((0 : Fin 5) = a ∧ i = b) := fun h => hab (Or.inr (Or.inl ⟨h.1.symm, h.2.symm⟩))
  have h3 : ¬ ((0 : Fin 5) = a ∧ (4 : Fin 5) = b) :=
    fun h => hab (Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩))
  unfold Dmat
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg h1, if_neg h2, if_neg h3]
  simp

theorem inB_ne0 (i : Fin 5) (hi : inB i) : i ≠ 0 := by
  rintro rfl
  exact absurd hi (by decide)

theorem inB_ne4 (i : Fin 5) (hi : inB i) : i ≠ 4 := by
  rintro rfl
  exact absurd hi (by decide)

theorem Dmat_i4 (i : Fin 5) (hi : inB i) (p : Tri) : Dmat i p i 4 = p.1 := by
  have hi0 := inB_ne0 i hi
  unfold Dmat
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
    Matrix.single_apply, if_pos ⟨rfl, rfl⟩, if_neg (fun h => hi0 h.1.symm),
    if_neg (fun h => hi0 h.1.symm)]
  simp

theorem Dmat_0i (i : Fin 5) (hi : inB i) (p : Tri) : Dmat i p 0 i = p.2.1 := by
  have hi0 := inB_ne0 i hi
  have hi4 := inB_ne4 i hi
  unfold Dmat
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg (fun h => hi0 h.1), if_pos ⟨rfl, rfl⟩,
    if_neg (fun h => hi4 h.2.symm)]
  simp

theorem Dmat_04 (i : Fin 5) (hi : inB i) (p : Tri) : Dmat i p 0 4 = p.2.2 := by
  have hi0 := inB_ne0 i hi
  have hi4 := inB_ne4 i hi
  unfold Dmat
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg (fun h => hi0 h.1), if_neg (fun h => hi4 h.2),
    if_pos ⟨rfl, rfl⟩]
  simp

theorem Dmat_zero (i : Fin 5) : Dmat i (0, 0, 0) = 0 := by
  unfold Dmat
  simp

theorem Dmat_zero_iff (i : Fin 5) (hi : inB i) (p : Tri) (h : Dmat i p = 0) : p = 0 := by
  have h1 := congrFun (congrFun h i) 4
  have h2 := congrFun (congrFun h 0) i
  have h3 := congrFun (congrFun h 0) 4
  rw [Dmat_i4 i hi, Matrix.zero_apply] at h1
  rw [Dmat_0i i hi, Matrix.zero_apply] at h2
  rw [Dmat_04 i hi, Matrix.zero_apply] at h3
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem Dmat_add (i : Fin 5) (p q : Tri) :
    Dmat i p + Dmat i q + Matrix.single 0 4 (p.2.1 * q.1) = Dmat i (tstar p q) := by
  unfold Dmat tstar
  simp only [Matrix.single_add]
  abel

theorem inB_cases : ∀ i : Fin 5, inB i → i = 1 ∨ i = 2 ∨ i = 3 := by decide

theorem Dmat_mul_self (i : Fin 5) (hi : inB i) (p q : Tri) :
    Dmat i p * Dmat i q = Matrix.single 0 4 (p.2.1 * q.1) := by
  rcases inB_cases i hi with rfl | rfl | rfl <;> ext a b <;> unfold Dmat <;>
    simp only [add_mul, mul_add, Matrix.mul_apply, Fin.sum_univ_five, Matrix.add_apply,
      Matrix.single_apply] <;>
    fin_cases a <;> fin_cases b <;> simp

theorem Dmat_mul_ne (i j : Fin 5) (hi : inB i) (hj : inB j) (hij : i ≠ j) (p q : Tri) :
    Dmat i p * Dmat j q = 0 := by
  rcases inB_cases i hi with rfl | rfl | rfl <;> rcases inB_cases j hj with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hij
    | (ext a b <;> unfold Dmat <;>
        simp only [add_mul, mul_add, Matrix.mul_apply, Fin.sum_univ_five, Matrix.add_apply,
          Matrix.single_apply] <;>
        fin_cases a <;> fin_cases b <;> simp)

@[expose] def unipD (i : Fin 5) (hi : inB i) (N : Mt) (hN : SuppIn (SDi i) N) : Hc :=
  unipH N (fun a b hba => hN a b (fun h => absurd (SDi_lt i a b hi h) (not_lt.2 hba)))
    (fun a => hN a 0 (fun h => absurd (SDi_lt i a 0 hi h) (not_lt_zero' a)))
    (fun b => hN 4 b (fun h => absurd (SDi_lt i 4 b hi h) (not_gt_four b)))

@[expose] def Dele (i : Fin 5) (hi : inB i) (p : Tri) : Hc :=
  unipD i hi (Dmat i p) (Dmat_supp i hi p)

theorem cm_Dele (i : Fin 5) (hi : inB i) (p : Tri) : cm (Dele i hi p) = 1 + Dmat i p := rfl

theorem Dele_mul (i : Fin 5) (hi : inB i) (p q : Tri) :
    cm (Dele i hi p) * cm (Dele i hi q) = 1 + Dmat i (tstar p q) := by
  rw [cm_Dele, cm_Dele]
  calc (1 + Dmat i p) * (1 + Dmat i q)
      = 1 + (Dmat i p + Dmat i q + Dmat i p * Dmat i q) := by noncomm_ring
    _ = 1 + (Dmat i p + Dmat i q + Matrix.single 0 4 (p.2.1 * q.1)) := by
        rw [Dmat_mul_self i hi p q]
    _ = 1 + Dmat i (tstar p q) := by rw [Dmat_add]

@[expose] def Psi (i : Fin 5) (hi : inB i) : DihedralGroup 4 →* Hc where
  toFun g := Dele i hi (Tab g)
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    show 1 + Dmat i (Tab 1) = 1
    rw [Tab_one, Dmat_zero, add_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    show cm (Dele i hi (Tab (g * h))) = cm (Dele i hi (Tab g) * Dele i hi (Tab h))
    rw [Tab_mul, cm_mul, Dele_mul, cm_Dele]

theorem Psi_inj (i : Fin 5) (hi : inB i) : Function.Injective (Psi i hi) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : cm (Psi i hi g) = 1 := congrArg cm hg
  have h2 : 1 + Dmat i (Tab g) = 1 := h1
  have h3 : Dmat i (Tab g) = 0 := add_eq_left.1 h2
  have h4 : Tab g = (0, 0, 0) := Dmat_zero_iff i hi _ h3
  exact Tab_inj g 1 (h4.trans Tab_one.symm)

@[expose] def Dsub (i : Fin 5) (hi : inB i) : Subgroup Hc := (Psi i hi).range

theorem mem_Dsub (i : Fin 5) (hi : inB i) (x : Hc) :
    x ∈ Dsub i hi ↔ ∃ p : Tri, cm x = 1 + Dmat i p := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Tab g, rfl⟩
  · rintro ⟨p, hp⟩
    obtain ⟨g, hg⟩ := Tab_surj p
    refine ⟨g, Subtype.ext (Subtype.ext ?_)⟩
    show cm (Dele i hi (Tab g)) = cm x
    rw [cm_Dele, hg, hp]

theorem Dsub_mulEquiv (i : Fin 5) (hi : inB i) : Nonempty (Dsub i hi ≃* DihedralGroup 4) :=
  ⟨(MonoidHom.ofInjective (Psi_inj i hi)).symm⟩

theorem Dsub_le_Qh (i : Fin 5) (hi : inB i) : Dsub i hi ≤ Qh := by
  intro x hx
  obtain ⟨p, hp⟩ := (mem_Dsub i hi x).1 hx
  rw [mem_Qh_iff]
  intro a b hab
  have := Dmat_supp i hi p a b (fun h => hab (SDi_sub_SQ i a b hi h))
  have e : cm x - 1 = Dmat i p := by
    rw [hp]
    abel
  rw [e]
  exact this

theorem Dsub_comm (i j : Fin 5) (hi : inB i) (hj : inB j) (hij : i ≠ j) {x y : Hc}
    (hx : x ∈ Dsub i hi) (hy : y ∈ Dsub j hj) : x * y = y * x := by
  obtain ⟨p, hp⟩ := (mem_Dsub i hi x).1 hx
  obtain ⟨q, hq⟩ := (mem_Dsub j hj y).1 hy
  apply Subtype.ext
  apply Subtype.ext
  show cm x * cm y = cm y * cm x
  rw [hp, hq]
  have h1 := Dmat_mul_ne i j hi hj hij p q
  have h2 := Dmat_mul_ne j i hj hi (Ne.symm hij) q p
  have e1 : (1 + Dmat i p) * (1 + Dmat j q) = 1 + (Dmat i p + Dmat j q) := by
    have := (show (1 + Dmat i p) * (1 + Dmat j q) =
      1 + (Dmat i p + Dmat j q + Dmat i p * Dmat j q) by noncomm_ring)
    rw [this, h1, add_zero]
  have e2 : (1 + Dmat j q) * (1 + Dmat i p) = 1 + (Dmat j q + Dmat i p) := by
    have := (show (1 + Dmat j q) * (1 + Dmat i p) =
      1 + (Dmat j q + Dmat i p + Dmat j q * Dmat i p) by noncomm_ring)
    rw [this, h2, add_zero]
  rw [e1, e2]
  abel

theorem zmod2_sub_zero : ∀ a : ZMod 2, a - 0 = a := by decide

theorem Dmat_row0 (i : Fin 5) (hi : inB i) (p : Tri) (b : Fin 5) :
    Dmat i p 0 b = (if i = b then p.2.1 else 0) + (if 4 = b then p.2.2 else 0) := by
  have hi0 := inB_ne0 i hi
  unfold Dmat
  simp [Matrix.add_apply, Matrix.single_apply, hi0]

theorem Dmat_col4 (i : Fin 5) (hi : inB i) (p : Tri) (a : Fin 5) :
    Dmat i p a 4 = (if i = a then p.1 else 0) + (if 0 = a then p.2.2 else 0) := by
  have hi4 := inB_ne4 i hi
  unfold Dmat
  simp [Matrix.add_apply, Matrix.single_apply, hi4]

theorem Dmat_only04 (i : Fin 5) (p : Tri) (h1 : p.1 = 0) (h2 : p.2.1 = 0) :
    Dmat i p = Matrix.single 0 4 p.2.2 := by
  unfold Dmat
  rw [h1, h2]
  simp

theorem eq_one_or_zt (x : Hc) (c : ZMod 2) (h : cm x = 1 + Matrix.single 0 4 c) :
    x = 1 ∨ x = zt := by
  have hc : c = 0 ∨ c = 1 := by
    have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact hz c
  rcases hc with rfl | rfl
  · left
    apply Subtype.ext
    apply Subtype.ext
    show cm x = 1
    rw [h, Matrix.single_zero, add_zero]
  · right
    apply Subtype.ext
    apply Subtype.ext
    show cm x = cm zt
    rw [h, cm_zt]

theorem zt_mem_Dsub (i : Fin 5) (hi : inB i) : zt ∈ Dsub i hi :=
  (mem_Dsub i hi zt).2 ⟨(0, 0, 1), by
    rw [cm_zt]
    simp [tt, Dmat]⟩

theorem zt_mem_U1 : zt ∈ U1 := (zt_mem_inf).1

theorem zt_sq : zt ^ 2 = 1 := isElemAbelian_U1.2 zt zt_mem_U1

theorem zt_ne_one : zt ≠ 1 := by
  intro h
  have h1 : cm zt = 1 := by rw [h, cm_one]
  have h2 : tt 0 4 = (1 : Mt) 0 4 := congrFun (congrFun h1 0) 4
  have h3 : (1 : Mt) 0 4 = 0 := Matrix.one_apply_ne (by decide)
  have h4 : tt 0 4 = 1 := by
    show (1 + Matrix.single 0 4 1 : Mt) 0 4 = 1
    rw [Matrix.add_apply, h3, Matrix.single_apply, if_pos ⟨rfl, rfl⟩, zero_add]
  rw [h4, h3] at h2
  exact one_ne_zero h2

theorem zt_order : orderOf zt = 2 :=
  orderOf_eq_prime zt_sq zt_ne_one

theorem zt_central : zt ∈ Subgroup.center Hc := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subtype.ext (cm_comm g))

theorem Dsub_inf (i j : Fin 5) (hi : inB i) (hj : inB j) (hij : i ≠ j) :
    Dsub i hi ⊓ Dsub j hj = Subgroup.zpowers zt := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨p, hp⟩ := (mem_Dsub i hi x).1 h1
    obtain ⟨q, hq⟩ := (mem_Dsub j hj x).1 h2
    have hDD : Dmat i p = Dmat j q := add_left_cancel (hp.symm.trans hq)
    have hp1 : p.1 = 0 := by
      rw [← Dmat_i4 i hi p, hDD, Dmat_col4 j hj q i]
      simp [Ne.symm hij, Ne.symm (inB_ne0 i hi)]
    have hp2 : p.2.1 = 0 := by
      rw [← Dmat_0i i hi p, hDD, Dmat_row0 j hj q i]
      simp [Ne.symm hij, Ne.symm (inB_ne4 i hi)]
    have hcx : cm x = 1 + Matrix.single 0 4 p.2.2 := by
      rw [hp, Dmat_only04 i p hp1 hp2]
    rcases eq_one_or_zt x _ hcx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers zt
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨zt_mem_Dsub i hi, zt_mem_Dsub j hj⟩

@[expose] def coefQ (x : Hc) (k : Fin 3) : Tri :=
  (cm x (idx3 k) 4, cm x 0 (idx3 k), if k = 0 then cm x 0 4 else 0)

theorem Qh_sum (x : Hc) (hx : x ∈ Qh) :
    Dmat (idx3 0) (coefQ x 0) + Dmat (idx3 1) (coefQ x 1) + Dmat (idx3 2) (coefQ x 2) =
      cm x - 1 := by
  have hS := (mem_Qh_iff x).1 hx
  ext a b
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.sub_apply]
  by_cases h : SQ a b
  · rcases h with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
        revert hb
        revert b
        decide
      rcases hb' with rfl | rfl | rfl | rfl <;>
        simp [Dmat_row0 1 (by decide), Dmat_row0 2 (by decide), Dmat_row0 3 (by decide), coefQ,
          idx3, zmod2_sub_zero]
    · have ha' := inB_cases a ha
      rcases ha' with rfl | rfl | rfl <;>
        simp [Dmat_col4 1 (by decide), Dmat_col4 2 (by decide), Dmat_col4 3 (by decide), coefQ,
          idx3, zmod2_sub_zero]
  · have h0 : ∀ k : Fin 3, Dmat (idx3 k) (coefQ x k) a b = 0 := fun k =>
      Dmat_supp (idx3 k) (inB_idx3 k) _ a b (fun hh => h (SDi_sub_SQ _ a b (inB_idx3 k) hh))
    rw [h0 0, h0 1, h0 2, add_zero, add_zero]
    have := hS a b h
    rw [Matrix.sub_apply] at this
    exact this.symm

theorem Qh_le_iSup (x : Hc) (hx : x ∈ Qh) :
    x ∈ ⨆ k : Fin 3, Dsub (idx3 k) (inB_idx3 k) := by
  have hdk : ∀ k : Fin 3, Dele (idx3 k) (inB_idx3 k) (coefQ x k) ∈
      Dsub (idx3 k) (inB_idx3 k) := fun k => (mem_Dsub _ _ _).2 ⟨coefQ x k, rfl⟩
  have h01 : Dmat (idx3 0) (coefQ x 0) * Dmat (idx3 1) (coefQ x 1) = 0 :=
    Dmat_mul_ne _ _ (inB_idx3 0) (inB_idx3 1) (fun h => by
      have := idx3_inj 0 1 h
      exact absurd this (by decide)) _ _
  have h02 : Dmat (idx3 0) (coefQ x 0) * Dmat (idx3 2) (coefQ x 2) = 0 :=
    Dmat_mul_ne _ _ (inB_idx3 0) (inB_idx3 2) (fun h => by
      have := idx3_inj 0 2 h
      exact absurd this (by decide)) _ _
  have h12 : Dmat (idx3 1) (coefQ x 1) * Dmat (idx3 2) (coefQ x 2) = 0 :=
    Dmat_mul_ne _ _ (inB_idx3 1) (inB_idx3 2) (fun h => by
      have := idx3_inj 1 2 h
      exact absurd this (by decide)) _ _
  have hprod : x = Dele (idx3 0) (inB_idx3 0) (coefQ x 0) * Dele (idx3 1) (inB_idx3 1) (coefQ x 1) *
      Dele (idx3 2) (inB_idx3 2) (coefQ x 2) := by
    apply Subtype.ext
    apply Subtype.ext
    show cm x = cm (Dele (idx3 0) (inB_idx3 0) (coefQ x 0) * Dele (idx3 1) (inB_idx3 1) (coefQ x 1) *
      Dele (idx3 2) (inB_idx3 2) (coefQ x 2))
    rw [cm_mul, cm_mul, cm_Dele, cm_Dele, cm_Dele]
    have e : (1 + Dmat (idx3 0) (coefQ x 0)) * (1 + Dmat (idx3 1) (coefQ x 1)) *
        (1 + Dmat (idx3 2) (coefQ x 2)) =
        1 + (Dmat (idx3 0) (coefQ x 0) + Dmat (idx3 1) (coefQ x 1) + Dmat (idx3 2) (coefQ x 2)) +
          (Dmat (idx3 0) (coefQ x 0) * Dmat (idx3 1) (coefQ x 1) +
            Dmat (idx3 0) (coefQ x 0) * Dmat (idx3 2) (coefQ x 2) +
            Dmat (idx3 1) (coefQ x 1) * Dmat (idx3 2) (coefQ x 2)) +
          Dmat (idx3 0) (coefQ x 0) * Dmat (idx3 1) (coefQ x 1) * Dmat (idx3 2) (coefQ x 2) := by
      noncomm_ring
    rw [e, h01, h02, h12, Qh_sum x hx, zero_mul, add_zero, add_zero, add_zero]
    abel
  rw [hprod]
  exact mul_mem (mul_mem (Subgroup.mem_iSup_of_mem 0 (hdk 0)) (Subgroup.mem_iSup_of_mem 1 (hdk 1)))
    (Subgroup.mem_iSup_of_mem 2 (hdk 2))

theorem isD8CentralCube_Qh : ∃ (D : Fin 3 → Subgroup Hc) (z : Hc), orderOf z = 2 ∧
    z ∈ Subgroup.center Hc ∧ (∀ i, D i ≤ Qh) ∧ (∀ i, Nonempty (↥(D i) ≃* DihedralGroup 4)) ∧
    (∀ i, z ∈ D i) ∧ (∀ i j, i ≠ j → ∀ x ∈ D i, ∀ y ∈ D j, x * y = y * x) ∧
    (∀ i j, i ≠ j → D i ⊓ D j = Subgroup.zpowers z) ∧ (⨆ i, D i) = Qh := by
  refine ⟨fun k => Dsub (idx3 k) (inB_idx3 k), zt, zt_order, zt_central,
    fun k => Dsub_le_Qh _ _, fun k => Dsub_mulEquiv _ _, fun k => zt_mem_Dsub _ _,
    fun i j hij x hx y hy => Dsub_comm _ _ _ _ (fun h => hij (idx3_inj i j h)) hx hy,
    fun i j hij => Dsub_inf _ _ _ _ (fun h => hij (idx3_inj i j h)), ?_⟩
  exact le_antisymm (iSup_le fun k => Dsub_le_Qh _ _) (fun x hx => Qh_le_iSup x hx)

theorem U1_le_Qh : U1 ≤ Qh := by
  intro x hx
  have hx' : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 hx
  exact (mem_Qh_iff x).2 (fun a b hab => hx' a b (fun h => hab (S1_sub_SQ a b h)))

theorem U2_le_Qh : U2 ≤ Qh := by
  intro x hx
  have hx' : SuppIn S2 (cm x - 1) := (mem_patSub hS2).1 hx
  exact (mem_Qh_iff x).2 (fun a b hab => hx' a b (fun h => hab (S2_sub_SQ a b h)))

@[expose] def Nu (x : Hc) : Mt :=
  Matrix.single 0 1 (cm x 0 1) + Matrix.single 0 2 (cm x 0 2) + Matrix.single 0 3 (cm x 0 3) +
    Matrix.single 0 4 (cm x 0 4 + (cm x 1 4 * cm x 0 1 + cm x 2 4 * cm x 0 2 + cm x 3 4 * cm x 0 3))

@[expose] def Nt (x : Hc) : Mt :=
  Matrix.single 1 4 (cm x 1 4) + Matrix.single 2 4 (cm x 2 4) + Matrix.single 3 4 (cm x 3 4)

theorem zmod2_add_add_self : ∀ a b : ZMod 2, a + b + b = a := by decide

theorem Nu_supp (x : Hc) : SuppIn S1 (Nu x) := by
  intro a b hab
  by_cases ha : a = 0
  · subst ha
    have hb : b = 0 := by
      by_contra hb
      exact hab ⟨rfl, hb⟩
    subst hb
    simp [Nu]
  · simp [Nu, Matrix.single_apply, Ne.symm ha]

theorem Nt_supp (x : Hc) : SuppIn S2 (Nt x) := by
  intro a b hab
  by_cases hb : b = 4
  · subst hb
    have ha : a = 4 := by
      by_contra ha
      exact hab ⟨rfl, ha⟩
    subst ha
    simp [Nt]
  · simp [Nt, Matrix.single_apply, hb, Ne.symm hb]

theorem Nu_Nt_sum (x : Hc) (hx : x ∈ Qh) :
    Nu x + Nt x + Matrix.single 0 4 (cm x 1 4 * cm x 0 1 + cm x 2 4 * cm x 0 2 + cm x 3 4 * cm x 0 3)
      = cm x - 1 := by
  have hS := (mem_Qh_iff x).1 hx
  ext a b
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.sub_apply]
  by_cases h : SQ a b
  · rcases h with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
        revert hb
        revert b
        decide
      rcases hb' with rfl | rfl | rfl | rfl <;>
        simp [Nu, Nt, Matrix.single_apply, zmod2_sub_zero, zmod2_add_add_self]
    · have ha' := inB_cases a ha
      rcases ha' with rfl | rfl | rfl <;>
        simp [Nu, Nt, Matrix.single_apply, zmod2_sub_zero, zmod2_add_add_self]
  · have h1 : Nu x a b = 0 := Nu_supp x a b (fun hh => h (S1_sub_SQ a b hh))
    have h2 : Nt x a b = 0 := Nt_supp x a b (fun hh => h (S2_sub_SQ a b hh))
    have h3 : Matrix.single 0 4 (cm x 1 4 * cm x 0 1 + cm x 2 4 * cm x 0 2 + cm x 3 4 * cm x 0 3)
        a b = 0 := by
      rw [Matrix.single_apply, if_neg (fun hh => h (Or.inl ⟨hh.1.symm, by
        rw [← hh.2]; decide⟩))]
    rw [h1, h2, h3, zero_add, zero_add]
    have := hS a b h
    rw [Matrix.sub_apply] at this
    exact this.symm

theorem Nu_mul_Nt (x : Hc) :
    Nu x * Nt x = Matrix.single 0 4 (cm x 1 4 * cm x 0 1 + cm x 2 4 * cm x 0 2 + cm x 3 4 * cm x 0 3) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Nu, Nt, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply] <;> ring

theorem Qh_mul_eq (x : Hc) (hx : x ∈ Qh) : (1 + Nu x) * (1 + Nt x) = cm x := by
  have e : (1 + Nu x) * (1 + Nt x) = 1 + (Nu x + Nt x + Matrix.single 0 4
      (cm x 1 4 * cm x 0 1 + cm x 2 4 * cm x 0 2 + cm x 3 4 * cm x 0 3)) := by
    rw [show (1 + Nu x) * (1 + Nt x) = 1 + (Nu x + Nt x) + Nu x * Nt x by noncomm_ring,
      Nu_mul_Nt]
    abel
  rw [e, Nu_Nt_sum x hx]
  abel

theorem Qh_eq_U1_mul_U2 : (Qh : Set Hc) = (U1 : Set Hc) * (U2 : Set Hc) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ Qh := hx
    refine Set.mem_mul.2 ⟨_, unipOfS1_mem (Nu x) (Nu_supp x), _, unipOfS2_mem (Nt x) (Nt_supp x), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show cm (unipOfS1 (Nu x) (Nu_supp x) * unipOfS2 (Nt x) (Nt_supp x)) = cm x
    rw [cm_mul, cm_unipOfS1, cm_unipOfS2]
    exact Qh_mul_eq x hx'
  · intro hx
    obtain ⟨u, hu, t, ht, rfl⟩ := Set.mem_mul.1 hx
    exact mul_mem (U1_le_Qh hu) (U2_le_Qh ht)

abbrev QPar : Type := (Fin 3 → ZMod 2) × ZMod 2 × (Fin 3 → ZMod 2)

@[expose] def NuP (f : Fin 3 → ZMod 2) (a : ZMod 2) (w : Fin 3 → ZMod 2) : Mt :=
  Matrix.single 0 1 (f 0) + Matrix.single 0 2 (f 1) + Matrix.single 0 3 (f 2) +
    Matrix.single 0 4 (a + (w 0 * f 0 + w 1 * f 1 + w 2 * f 2))

@[expose] def NtP (w : Fin 3 → ZMod 2) : Mt :=
  Matrix.single 1 4 (w 0) + Matrix.single 2 4 (w 1) + Matrix.single 3 4 (w 2)

theorem NuP_supp (f : Fin 3 → ZMod 2) (a : ZMod 2) (w : Fin 3 → ZMod 2) :
    SuppIn S1 (NuP f a w) := by
  intro i j hij
  by_cases hi : i = 0
  · subst hi
    have hj : j = 0 := by
      by_contra hj
      exact hij ⟨rfl, hj⟩
    subst hj
    simp [NuP]
  · simp [NuP, Matrix.single_apply, Ne.symm hi]

theorem NtP_supp (w : Fin 3 → ZMod 2) : SuppIn S2 (NtP w) := by
  intro a b hab
  by_cases hb : b = 4
  · subst hb
    have ha : a = 4 := by
      by_contra ha
      exact hab ⟨rfl, ha⟩
    subst ha
    simp [NtP]
  · simp [NtP, Matrix.single_apply, hb, Ne.symm hb]

@[expose] def phiQ (p : QPar) : Hc :=
  unipOfS1 (NuP p.1 p.2.1 p.2.2) (NuP_supp _ _ _) * unipOfS2 (NtP p.2.2) (NtP_supp _)

theorem cm_phiQ (p : QPar) : cm (phiQ p) = (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) := by
  rw [phiQ, cm_mul, cm_unipOfS1, cm_unipOfS2]

theorem phiQ_mem (p : QPar) : phiQ p ∈ Qh :=
  mul_mem (U1_le_Qh (unipOfS1_mem _ _)) (U2_le_Qh (unipOfS2_mem _ _))

theorem NuP_mul_NtP (f : Fin 3 → ZMod 2) (a : ZMod 2) (w : Fin 3 → ZMod 2) :
    NuP f a w * NtP w = Matrix.single 0 4 (w 0 * f 0 + w 1 * f 1 + w 2 * f 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NuP, NtP, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply] <;> ring

theorem cm_phiQ_expand (p : QPar) :
    cm (phiQ p) = 1 + NuP p.1 p.2.1 p.2.2 + NtP p.2.2 +
      Matrix.single 0 4 (p.2.2 0 * p.1 0 + p.2.2 1 * p.1 1 + p.2.2 2 * p.1 2) := by
  rw [cm_phiQ]
  have e : (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) =
      1 + NuP p.1 p.2.1 p.2.2 + NtP p.2.2 + NuP p.1 p.2.1 p.2.2 * NtP p.2.2 := by
    noncomm_ring
  rw [e, NuP_mul_NtP]

theorem phiQ_inj : Function.Injective phiQ := by
  rintro ⟨f, a, w⟩ ⟨f', a', w'⟩ h
  have hc : cm (phiQ (f, a, w)) = cm (phiQ (f', a', w')) := congrArg cm h
  rw [cm_phiQ_expand, cm_phiQ_expand] at hc
  have e01 := congrFun (congrFun hc 0) 1
  have e02 := congrFun (congrFun hc 0) 2
  have e03 := congrFun (congrFun hc 0) 3
  have e04 := congrFun (congrFun hc 0) 4
  have e14 := congrFun (congrFun hc 1) 4
  have e24 := congrFun (congrFun hc 2) 4
  have e34 := congrFun (congrFun hc 3) 4
  simp [NuP, NtP, Matrix.add_apply, Matrix.single_apply] at e01 e02 e03 e04 e14 e24 e34
  have hf : f = f' := funext fun k => by
    fin_cases k
    exacts [e01, e02, e03]
  have hw : w = w' := funext fun k => by
    fin_cases k
    exacts [e14, e24, e34]
  subst hf
  subst hw
  have ha : a = a' := by
    have h4 := e04
    rw [zmod2_add_add_self, zmod2_add_add_self] at h4
    exact h4
  subst ha
  rfl

@[expose] def Fq (p : QPar) : ↥Qh := ⟨phiQ p, phiQ_mem p⟩

theorem Fq_bij : Function.Bijective Fq := by
  constructor
  · intro p p' h
    exact phiQ_inj (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    refine ⟨((fun k => cm x 0 (idx3 k)), cm x 0 4, (fun k => cm x (idx3 k) 4)), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    show cm (phiQ _) = cm x
    rw [cm_phiQ]
    exact Qh_mul_eq x hx

theorem card_Qh : Nat.card Qh = 128 := by
  rw [← Nat.card_congr (Equiv.ofBijective Fq Fq_bij)]
  simp [QPar, Nat.card_eq_fintype_card]

end CFSG.Quasithin.A94.L52
