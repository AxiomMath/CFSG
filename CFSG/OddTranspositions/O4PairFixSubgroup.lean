module

public import CFSG.OddTranspositions.O4PairTenInvolutions
public import CFSG.OddTranspositions.F25tPSL2Reps
public import CFSG.OddTranspositions.O4PairTransport
public import CFSG.OddTranspositions.O4PairCard65
public import CFSG.Adapters.Certificate43Check
public import CFSG.Dihedral.Glauberman.DicksonMaxTraceField
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.O4CloseReduction
public import CFSG.OddTranspositions.O4PairCentralizer
public import CFSG.OddTranspositions.SixEight
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F25t

@[expose] def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

instance (priority := 2000) f25tDecEqInst : DecidableEq F25t := f25tDecEq

@[expose] def sl2DecEq (M N : SL2) : Decidable (M = N) := by
  letI : DecidableEq F25t := f25tDecEq
  by_cases h00 : (M : Matrix (Fin 2) (Fin 2) F25t) 0 0 =
      (N : Matrix (Fin 2) (Fin 2) F25t) 0 0
  · by_cases h01 : (M : Matrix (Fin 2) (Fin 2) F25t) 0 1 =
        (N : Matrix (Fin 2) (Fin 2) F25t) 0 1
    · by_cases h10 : (M : Matrix (Fin 2) (Fin 2) F25t) 1 0 =
          (N : Matrix (Fin 2) (Fin 2) F25t) 1 0
      · by_cases h11 : (M : Matrix (Fin 2) (Fin 2) F25t) 1 1 =
            (N : Matrix (Fin 2) (Fin 2) F25t) 1 1
        · exact isTrue (Subtype.ext (Matrix.ext (by
            intro i j
            fin_cases i <;> fin_cases j <;> assumption)))
        · exact isFalse fun h => h11 (by rw [h])
      · exact isFalse fun h => h10 (by rw [h])
    · exact isFalse fun h => h01 (by rw [h])
  · exact isFalse fun h => h00 (by rw [h])

instance (priority := 2000) sl2DecEqInst : DecidableEq SL2 := sl2DecEq

@[expose] def FixG : Subgroup (PSL2 F25t) where
  carrier := {q | psl2FieldAut F25t frob25t q = q}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def H : Subgroup (PSL2 F25t) :=
  Subgroup.closure (Set.range x)

@[expose] def genA : SL2 := X 0

@[expose] def genB : SL2 := X 1 * X 2 * X 3

@[expose] def pslGenA : PSL2 F25t := x 0

@[expose] def pslGenB : PSL2 F25t := x 1 * x 2 * x 3

@[simp] theorem pslGenA_eq_mk : pslGenA = mk genA := rfl

@[simp] theorem pslGenB_eq_mk : pslGenB = mk genB := by
  simp [pslGenB, genB, x]

@[expose] def closeStep (S : Finset SL2) : Finset SL2 :=
  S ∪ S.image (fun y => canonSL (y * genA)) ∪ S.image (fun y => canonSL (y * genB))

@[expose] def closeIter : ℕ → Finset SL2
  | 0 => {1}
  | n + 1 => closeStep (closeIter n)

@[expose] def N : ℕ := 10

theorem closeIter_zero : closeIter 0 = ({1} : Finset SL2) := rfl

theorem closeIter_succ (n : ℕ) : closeIter (n + 1) = closeStep (closeIter n) := rfl

theorem closeIter_subset_succ (n : ℕ) : closeIter n ⊆ closeIter (n + 1) := by
  intro y hy
  rw [closeIter_succ]
  simp only [closeStep]
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hy)))

theorem closeIter_mono : Monotone closeIter :=
  monotone_nat_of_le_succ closeIter_subset_succ

theorem canonSL_one : canonSL (1 : SL2) = 1 := by
  unfold canonSL
  rw [if_pos (by decide +kernel)]

theorem one_mem_closeIter : (1 : SL2) ∈ closeIter N :=
  closeIter_mono (Nat.zero_le N) (Finset.mem_singleton_self 1)

theorem closeIter_canon : ∀ (n : ℕ) (y : SL2), y ∈ closeIter n → canonSL y = y := by
  intro n
  induction n with
  | zero =>
      intro y hy
      rw [closeIter_zero, Finset.mem_singleton] at hy
      subst y
      exact canonSL_one
  | succ n ih =>
      intro y hy
      rw [closeIter_succ] at hy
      simp only [closeStep, Finset.mem_union, Finset.mem_image] at hy
      rcases hy with (hy | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
      · exact ih y hy
      · exact canonSL_idem (z * genA)
      · exact canonSL_idem (z * genB)

theorem mk_inj_on_closeIter :
    Set.InjOn (CFSG.PSL2Table.mk) (↑(closeIter N) : Set SL2) := by
  intro y hy z hz h
  exact mk_inj_on_reps (mem_psl2Reps.mpr (closeIter_canon N y hy))
    (mem_psl2Reps.mpr (closeIter_canon N z hz)) h

theorem mk_genA_mem_closure :
    mk genA ∈ Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t)) := by
  have h : pslGenA ∈ ({pslGenA, pslGenB} : Set (PSL2 F25t)) := by simp
  simpa [pslGenA_eq_mk] using Subgroup.subset_closure h

theorem mk_genB_mem_closure :
    mk genB ∈ Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t)) := by
  have h : pslGenB ∈ ({pslGenA, pslGenB} : Set (PSL2 F25t)) := by simp
  simpa [pslGenB_eq_mk] using Subgroup.subset_closure h

theorem closeIter_subset_closure :
    ∀ y ∈ closeIter N, mk y ∈ Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t)) := by
  have h : ∀ (n : ℕ) (y : SL2), y ∈ closeIter n →
      mk y ∈ Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t)) := by
    intro n
    induction n with
    | zero =>
        intro y hy
        rw [closeIter_zero, Finset.mem_singleton] at hy
        subst y
        simp
    | succ n ih =>
        intro y hy
        rw [closeIter_succ] at hy
        simp only [closeStep, Finset.mem_union, Finset.mem_image] at hy
        rcases hy with (hy | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
        · exact ih y hy
        · rw [canonSL_mk, map_mul]
          exact Subgroup.mul_mem _ (ih z hz) mk_genA_mem_closure
        · rw [canonSL_mk, map_mul]
          exact Subgroup.mul_mem _ (ih z hz) mk_genB_mem_closure
  exact h N

theorem closeStep_closeIter_eq : closeStep (closeIter N) = closeIter N := by
  decide +kernel

theorem closeIter_closed :
    ∀ y ∈ closeIter N,
      canonSL (y * genA) ∈ closeIter N ∧ canonSL (y * genB) ∈ closeIter N := by
  intro y hy
  constructor
  · have himage : canonSL (y * genA) ∈
        (closeIter N).image (fun y => canonSL (y * genA)) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have hstep : canonSL (y * genA) ∈ closeStep (closeIter N) := by
      simp only [closeStep]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr himage)))
    rwa [closeStep_closeIter_eq] at hstep
  · have himage : canonSL (y * genB) ∈
        (closeIter N).image (fun y => canonSL (y * genB)) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have hstep : canonSL (y * genB) ∈ closeStep (closeIter N) := by
      simp only [closeStep]
      exact Finset.mem_union.mpr (Or.inr himage)
    rwa [closeStep_closeIter_eq] at hstep

theorem closure_le_image_closeIter :
    Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t)) ≤
      ((closeIter N).image CFSG.PSL2Table.mk : Set (PSL2 F25t)) := by
  let T : Set (PSL2 F25t) := ((closeIter N).image CFSG.PSL2Table.mk : Set (PSL2 F25t))
  intro h hh
  change h ∈ T
  have hTfin : T.Finite := Finset.finite_toSet ((closeIter N).image CFSG.PSL2Table.mk)
  have h1 : (1 : PSL2 F25t) ∈ T :=
    Finset.mem_image.mpr ⟨1, one_mem_closeIter, by rw [map_one]⟩
  have hA : ∀ q ∈ T, q * pslGenA ∈ T := by
    intro q hq
    change q ∈ (closeIter N).image CFSG.PSL2Table.mk at hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨canonSL (y * genA), (closeIter_closed y hy).1, by
      rw [canonSL_mk, map_mul, pslGenA_eq_mk]⟩
  have hB : ∀ q ∈ T, q * pslGenB ∈ T := by
    intro q hq
    change q ∈ (closeIter N).image CFSG.PSL2Table.mk at hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨canonSL (y * genB), (closeIter_closed y hy).2, by
      rw [canonSL_mk, map_mul, pslGenB_eq_mk]⟩
  have hinv : ∀ y ∈ ({pslGenA, pslGenB} : Set (PSL2 F25t)), ∀ q ∈ T, q * y⁻¹ ∈ T := by
    intro y hy q hq
    have hmaps : Set.MapsTo (fun r : PSL2 F25t => r * y) T T := by
      intro r hr
      rcases hy with rfl | rfl
      · exact hA r hr
      · exact hB r hr
    have hbij : Set.BijOn (fun r : PSL2 F25t => r * y) T T :=
      (hTfin.injOn_iff_bijOn_of_mapsTo hmaps).mp (fun a _ b _ h => mul_right_cancel h)
    obtain ⟨z, hzT, hzq⟩ := hbij.surjOn hq
    have hz : q * y⁻¹ = z := by
      rw [← hzq, mul_assoc, mul_inv_cancel, mul_one]
    rwa [hz]
  refine Subgroup.closure_induction_right (p := fun q _ => q ∈ T) h1 ?_ ?_ hh
  · intro x _ y hy hxT
    rcases hy with rfl | rfl
    · exact hA x hxT
    · exact hB x hxT
  · intro x _ y hy hxT
    exact hinv y hy x hxT

theorem closeIter_card : (closeIter N).card = 120 := by
  decide +kernel

theorem card_closure_gens :
    Nat.card (Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t))) = 120 := by
  let K := Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t))
  change Nat.card K = 120
  have hKT : (K : Set (PSL2 F25t)) = ((closeIter N).image CFSG.PSL2Table.mk :
      Set (PSL2 F25t)) := by
    apply Set.Subset.antisymm
    · intro q hq
      exact closure_le_image_closeIter hq
    · intro q hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      exact closeIter_subset_closure y hy
  have hcard_image : ((closeIter N).image CFSG.PSL2Table.mk).card = 120 := by
    rw [Finset.card_image_of_injOn mk_inj_on_closeIter, closeIter_card]
  calc
    Nat.card K = (K : Set (PSL2 F25t)).ncard := rfl
    _ = ((closeIter N).image CFSG.PSL2Table.mk : Set (PSL2 F25t)).ncard := by rw [hKT]
    _ = ((closeIter N).image CFSG.PSL2Table.mk).card := Set.ncard_coe_finset _
    _ = 120 := hcard_image

theorem closure_gens_le_H :
    Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t)) ≤ H := by
  rw [Subgroup.closure_le]
  intro q hq
  rcases hq with rfl | rfl
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · have h1 : x 1 ∈ H := Subgroup.subset_closure ⟨1, rfl⟩
    have h2 : x 2 ∈ H := Subgroup.subset_closure ⟨2, rfl⟩
    have h3 : x 3 ∈ H := Subgroup.subset_closure ⟨3, rfl⟩
    simpa [pslGenB] using mul_mem (mul_mem h1 h2) h3

theorem H_le_FixG : H ≤ FixG := by
  rw [H, Subgroup.closure_le]
  rintro q ⟨i, rfl⟩
  simpa [FixG] using x_fixed i

theorem pslEquiv_aut_apply (q : PSL2 F25t) :
    pslEquiv (psl2FieldAut F25t frob25t q) =
      psl2FieldAut K25 frob25 (pslEquiv q) := by
  have h := congrArg (fun e : PSL2 F25t ≃* PSL2 K25 => e q) (pslEquiv_compat frob25t)
  simpa [MulEquiv.trans_apply, ringAutConjMulEquiv_frob25t] using h

noncomputable def fixEquiv :
    {q : PSL2 F25t // psl2FieldAut F25t frob25t q = q} ≃
      {q : PSL2 K25 // q = psl2FieldAut K25 frob25 q} :=
  Equiv.subtypeEquiv pslEquiv.toEquiv (fun q => by
    constructor
    · intro hq
      have h := congrArg pslEquiv hq
      rw [pslEquiv_aut_apply] at h
      exact h.symm
    · intro hq
      apply pslEquiv.injective
      rw [pslEquiv_aut_apply]
      exact hq.symm)

theorem card_FixG : Nat.card FixG = 120 := by
  calc
    Nat.card FixG = Nat.card {q : PSL2 F25t // psl2FieldAut F25t frob25t q = q} := rfl
    _ = Nat.card {q : PSL2 K25 // q = psl2FieldAut K25 frob25 q} :=
      Nat.card_congr fixEquiv
    _ = 120 := @card_fix_psl2_frob25

theorem H_eq_FixG : H = FixG := by
  apply Subgroup.eq_of_le_of_card_ge H_le_FixG
  have hle : Nat.card (Subgroup.closure ({pslGenA, pslGenB} : Set (PSL2 F25t))) ≤
      Nat.card H := Subgroup.card_le_of_le closure_gens_le_H
  rw [card_closure_gens] at hle
  rw [card_FixG]
  exact hle

end CFSG.OddTranspositions.QZ
