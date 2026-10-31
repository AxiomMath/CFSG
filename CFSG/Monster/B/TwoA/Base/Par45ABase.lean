
module

public import CFSG.Monster.B.TwoA.Base.RankThreeBase
public import CFSG.Monster.B.TwoA.Base.Space34ABase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem PairSpace.qV_eq_zero
    {U : Submodule (ZMod 2) (Wv v0)}
    {A : Finset (Set.powersetCard (Fin 24) 2)} (hU : PairSpace U A) : ∀ x ∈ U, qV x = 0 := by
  intro x hx
  rcases (hU.mem_iff x).1 hx with rfl | rfl | ⟨y, z, h, -, b, rfl⟩
  · exact QuadraticMap.map_zero _
  · exact qV_wFr
  · exact qV_pairW h b

theorem EU_span_le
    {n : ℕ} {g : Fin n → Wv v0} {H : Subgroup Dfull} (hx : xhat ∈ H)
    (hg : ∀ i, ∃ e : Ehat, psiW e = g i ∧ (e : Dfull) ∈ H) :
    EU (Submodule.span (ZMod 2) (Set.range g)) ≤ H := by
  have key : ∀ x ∈ Submodule.span (ZMod 2) (Set.range g),
      ∃ e : Ehat, psiW e = x ∧ (e : Dfull) ∈ H := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hg i
    | zero => exact ⟨1, psiW_one, H.one_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨e, rfl, he⟩ := hx
      obtain ⟨e', rfl, he'⟩ := hy
      exact ⟨e * e', psiW_mul e e', H.mul_mem he he'⟩
    | smul t x _ hx =>
      obtain ⟨e, rfl, he⟩ := hx
      rcases zmod2_cases t with rfl | rfl
      · exact ⟨1, by rw [psiW_one, zero_smul], H.one_mem⟩
      · exact ⟨e, by rw [one_smul], he⟩
  intro d hd
  obtain ⟨hd', hdU⟩ := mem_EU.1 hd
  obtain ⟨e, he, heH⟩ := key _ hdU
  rcases fiber_cases (a := ⟨d, hd'⟩) (b := e) he.symm with h | h
  · rw [show d = (e : Dfull) from h]
    exact heH
  · rw [show d = (e : Dfull) * xhat from h]
    exact H.mul_mem heH hx

def E4 : Subgroup Dfull := Subgroup.closure (insert (dhat 4 5) (E3 : Set Dfull))

def E5 : Subgroup Dfull := Subgroup.closure (insert (dhat 8 9) (E4 : Set Dfull))

theorem psiW_d45 :

    psiW (dhatE 4 5) = pairW 4 5 offPair45 0 := psiW_dhat (by decide) offPair45

theorem psiW_d89 :

    psiW (dhatE 8 9) = pairW 8 9 offPair89 0 := psiW_dhat (by decide) offPair89

theorem yhat_mem_E3 : yhat ∈ E3 := Subgroup.subset_closure (by simp)

theorem zhat_mem_E3 : zhat ∈ E3 := Subgroup.subset_closure (by simp)

theorem E3_le_E4 : E3 ≤ E4 := fun _ h => Subgroup.subset_closure (Set.mem_insert_of_mem _ h)

theorem E4_le_E5 : E4 ≤ E5 := fun _ h => Subgroup.subset_closure (Set.mem_insert_of_mem _ h)

theorem d45_mem_E4 : dhat 4 5 ∈ E4 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem d89_mem_E5 : dhat 8 9 ∈ E5 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem xhat_mem_E4 : xhat ∈ E4 := E3_le_E4 xhat_mem_E3

theorem xhat_mem_E5 : xhat ∈ E5 := E4_le_E5 xhat_mem_E4

theorem U3_le_U4 :
    U3 ≤ U4 := by
  rw [U3, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : gen3 i = gen4 i.castSucc := by fin_cases i <;> rfl
  rw [h]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem tauhat_mem_normalizer_E4 : tauhat ∈ Subgroup.normalizer (E4 : Set Dfull) := by
  refine mem_normalizer_of_closure ?_
  rintro _ (rfl | h)
  · rw [tauhat_mul_dhat, mul_inv_cancel_right]
    exact d45_mem_E4
  · exact E3_le_E4 (conj_mem_of_normalizer tauhat_mem_normalizer_E3 h)

theorem tauhat_mem_normalizer_E5 : tauhat ∈ Subgroup.normalizer (E5 : Set Dfull) := by
  refine mem_normalizer_of_closure ?_
  rintro _ (rfl | h)
  · rw [tauhat_mul_dhat, mul_inv_cancel_right]
    exact d89_mem_E5
  · exact E4_le_E5 (conj_mem_of_normalizer tauhat_mem_normalizer_E4 h)

def H4 : Subgroup Dfull := Jhat ⊓ Subgroup.normalizer (E4 : Set Dfull)

abbrev K4 : Subgroup Dfull := Subgroup.normalizer (E4 : Set Dfull)

def Z4 : Subgroup Dfull := Subgroup.centralizer (E4 : Set Dfull)

def H5 : Subgroup Dfull := Jhat ⊓ Subgroup.normalizer (E5 : Set Dfull)

abbrev K5 : Subgroup Dfull := Subgroup.normalizer (E5 : Set Dfull)

def Z5 : Subgroup Dfull := Subgroup.centralizer (E5 : Set Dfull)

theorem Z4_le_K4 : Z4 ≤ K4 := Subgroup.centralizer_le_normalizer _

theorem Z5_le_K5 : Z5 ≤ K5 := Subgroup.centralizer_le_normalizer _

end CFSG.Monster.B.TwoA
