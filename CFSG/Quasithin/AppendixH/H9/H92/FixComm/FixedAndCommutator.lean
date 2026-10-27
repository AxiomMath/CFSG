module

public import CFSG.Quasithin.AppendixH.H9.H92.FixComm.SplitSubgroup
public import CFSG.Quasithin.AppendixH.H9.H92.FixComm.RadSubspace
public import CFSG.Quasithin.AppendixH.H9.H92.FixComm.ActionFormula

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

section Generic

variable {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
  {A : Subgroup (MulAut (PairN n))} {A' : Subgroup (GL (Fin n) (ZMod 2))}
  {𝒜 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))}

theorem pairVec_mem_fixV_iff (hA' : A' ≤ RadMat n D)
    (hAmem : ∀ g : MulAut (PairN n), g ∈ A ↔ ∃ B ∈ A', pairActN n B = g)
    (h𝒜 : ∀ N, N ∈ 𝒜 ↔ ∃ B ∈ A', (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = N)
    (a b : Fin n → ZMod 2) :
    pairVec a b ∈ fixV A ↔ ∀ N ∈ 𝒜, N *ᵥ a = 0 ∧ Nᵀ *ᵥ b = 0 := by
  constructor
  · intro h N hN
    obtain ⟨B, hB, rfl⟩ := (h𝒜 N).1 hN
    have hfix : pairActN n B (pairVec a b) = pairVec a b :=
      (mem_fixV.1 h) _ ((hAmem _).2 ⟨B, hB, rfl⟩)
    rw [pairActN_pairVec_of_mem_radMat (hA' hB)] at hfix
    obtain ⟨h1, h2⟩ := pairVec_inj.1 hfix
    exact ⟨add_eq_left.1 h1, add_eq_left.1 h2⟩
  · intro h
    refine mem_fixV.2 fun g hg => ?_
    obtain ⟨B, hB, rfl⟩ := (hAmem g).1 hg
    obtain ⟨h1, h2⟩ := h _ ((h𝒜 _).2 ⟨B, hB, rfl⟩)
    show pairActN n B (pairVec a b) = pairVec a b
    rw [pairActN_pairVec_of_mem_radMat (hA' hB), h1, h2, add_zero, add_zero]

theorem pairVec_mulVec_mem_commV (hA' : A' ≤ RadMat n D)
    (hAmem : ∀ g : MulAut (PairN n), g ∈ A ↔ ∃ B ∈ A', pairActN n B = g)
    (h𝒜 : ∀ N, N ∈ 𝒜 ↔ ∃ B ∈ A', (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = N)
    {N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N ∈ 𝒜) (a b : Fin n → ZMod 2) :
    pairVec (N *ᵥ a) (Nᵀ *ᵥ b) ∈ commV A := by
  obtain ⟨B, hB, rfl⟩ := (h𝒜 N).1 hN
  have hmem : pairActN n B ∈ A := (hAmem _).2 ⟨B, hB, rfl⟩
  have key := pairActN_mul_inv_pairVec_of_mem_radMat (hA' hB) a b
  exact Subgroup.subset_closure ⟨pairActN n B, hmem, pairVec a b, key⟩

theorem commV_le_splitSub (hA' : A' ≤ RadMat n D)
    (hAmem : ∀ g : MulAut (PairN n), g ∈ A ↔ ∃ B ∈ A', pairActN n B = g) :
    commV A ≤ splitSub n D (dotPerp n D) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro w ⟨x, hx, v, rfl⟩
  obtain ⟨B, hB, rfl⟩ := (hAmem x).1 hx
  obtain ⟨a, b, rfl⟩ := pairVec_surj v
  have key := pairActN_mul_inv_pairVec_of_mem_radMat (hA' hB) a b
  have hN := (mem_radMat_iff_sub_mem_radNil B).1 (hA' hB)
  have hNt := transpose_mem_radNil n D _ hN
  have hmem : pairVec (((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a)
      (((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b) ∈ splitSub n D (dotPerp n D) :=
    pairVec_mem_splitSub.2 ⟨hN.1 a, hNt.1 b⟩
  exact Eq.mpr (congrArg (fun w => w ∈ splitSub n D (dotPerp n D)) key) hmem

private def v2SpaceOf (K : Subgroup (PairN n)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {b | pairVec 0 b ∈ K}
  add_mem' := fun {a b} ha hb => by
    have h := K.mul_mem ha hb
    rw [pairVec_mul, add_zero] at h
    exact h
  zero_mem' := by
    show pairVec 0 0 ∈ K
    rw [← pairVec_one]
    exact K.one_mem
  smul_mem' := fun c a ha => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · show pairVec 0 ((0 : ZMod 2) • a) ∈ K
      rw [zero_smul, ← pairVec_one]
      exact K.one_mem
    · simpa using ha

theorem splitSub_le_commV (hA' : A' ≤ RadMat n D)
    (hAmem : ∀ g : MulAut (PairN n), g ∈ A ↔ ∃ B ∈ A', pairActN n B = g)
    (h𝒜 : ∀ N, N ∈ 𝒜 ↔ ∃ B ∈ A', (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = N)
    (hspan : Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ a : Fin n → ZMod 2, y = N *ᵥ a} = D)
    (hspanT : Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ b : Fin n → ZMod 2, y = Nᵀ *ᵥ b} =
      dotPerp n D) :
    splitSub n D (dotPerp n D) ≤ commV A := by
  have h1 : D ≤ v1Space n (commV A) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro y ⟨N, hN, a, rfl⟩
    have h := pairVec_mulVec_mem_commV hA' hAmem h𝒜 hN a 0
    rw [Matrix.mulVec_zero] at h
    exact h
  have h2 : dotPerp n D ≤ v2SpaceOf (commV A) := by
    rw [← hspanT]
    refine Submodule.span_le.2 ?_
    rintro y ⟨N, hN, b, rfl⟩
    have h := pairVec_mulVec_mem_commV hA' hAmem h𝒜 hN 0 b
    rw [Matrix.mulVec_zero] at h
    exact h
  rintro x ⟨a, ha, b, hb, rfl⟩
  have e : pairVec a b = pairVec a 0 * pairVec 0 b := by
    rw [pairVec_mul, add_zero, zero_add]
  rw [e]
  exact Subgroup.mul_mem _ (h1 ha) (h2 hb)

end Generic

theorem fixV_commV_eq_splitSub {U : Subgroup (PairN 5)}
    (hD : Module.finrank (ZMod 2) (v1Space 5 U) = 3)
    {A : Subgroup (MulAut (PairN 5))} (hA : A ≤ RadV1 5 U) (hcard : 32 ≤ Nat.card A) :
    fixV A = splitSub 5 (v1Space 5 U) (dotPerp 5 (v1Space 5 U)) ∧
      commV A = splitSub 5 (v1Space 5 U) (dotPerp 5 (v1Space 5 U)) := by
  have hLg : A ≤ Lg 5 := hA.trans (RadV1_le_Lg 5 U)
  have hA' := comap_pairActN_le_radMat hA
  have hAmem := mem_iff_exists_comap_pairActN hLg
  obtain ⟨𝒜, h𝒜, h𝒜le, h𝒜card⟩ := exists_radDiffSpace _ hA'
  have h5 : 5 ≤ Module.finrank (ZMod 2) 𝒜 := by
    refine five_le_finrank_of_le_card 𝒜 ?_
    rw [h𝒜card, card_comap_pairActN hLg]
    exact hcard
  obtain ⟨hker, hkerT, hspan, hspanT, -⟩ :=
    radNil_large_subspace_facts (v1Space 5 U) hD 𝒜 h𝒜le h5
  refine ⟨?_, le_antisymm (commV_le_splitSub hA' hAmem)
    (splitSub_le_commV hA' hAmem h𝒜 hspan hspanT)⟩
  ext x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  refine (pairVec_mem_fixV_iff hA' hAmem h𝒜 a b).trans (Iff.trans ?_ pairVec_mem_splitSub.symm)
  constructor
  · intro h
    exact ⟨(hker a).1 fun N hN => (h N hN).1, (hkerT b).1 fun N hN => (h N hN).2⟩
  · rintro ⟨ha, hb⟩ N hN
    exact ⟨(hker a).2 ha N hN, (hkerT b).2 hb N hN⟩

end CFSG.ASVolI.ChH
