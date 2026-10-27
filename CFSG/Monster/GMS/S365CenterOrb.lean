module

public import CFSG.Monster.GMS.S365CosetSpec
public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365CentPathSpec
public import CFSG.Monster.GMS.S365CenterOrbInputs
public import Certificates.Certificate10041
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Monster.GMS.S365CosetSpec

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative

theorem canon4_zero (v : ℕ) : canon4 0 0 v = v := by
  unfold canon4
  simp

theorem orbitCheck3_ok : orbitCheck3 = true :=
  Certificates.certificate10041

theorem tree_orbit {L par lab : Array ℕ} (h : treeCheckK cosetRowsT 0 0 L par lab = true)
    {gl : ℕ → Co1}
    (hf : ∀ l < cosetRowsT.size, ∀ u, gl l • toVecD 24 u = toVecD 24 (vecMulN 24 cosetRowsT[l]! u))
    (hstab : ∀ l < cosetRowsT.size, gl l • toVecD 24 2 = toVecD 24 2 ∧
      gl l • toVecD 24 4 = toVecD 24 4) :
    ∀ k < L.size, ∃ g : Co1, g • toVecD 24 2 = toVecD 24 2 ∧ g • toVecD 24 4 = toVecD 24 4 ∧
      g • toVecD 24 L[0]! = toVecD 24 L[k]! := by
  obtain ⟨hLpos, hL⟩ := treeCheckK_spec h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases hL k hk with h0 | ⟨hp, hl, he⟩
    · subst h0
      exact ⟨1, one_smul _ _, one_smul _ _, one_smul _ _⟩
    · obtain ⟨g', hg'2, hg'4, hg'⟩ := ih _ hp (lt_trans hp hk)
      refine ⟨gl lab[k]! * g', ?_, ?_, ?_⟩
      · rw [mul_smul, hg'2, (hstab _ hl).1]
      · rw [mul_smul, hg'4, (hstab _ hl).2]
      · rw [mul_smul, hg', hf _ hl, he, canon4_zero]

theorem orbit3_ncard :
    397 ≤ (MulAction.orbit (↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4)))
      (toVecD 24 28)).ncard := by
  have hc := orbitCheck3_ok
  unfold orbitCheck3 at hc
  generalize cosetBFS cosetRowsT 0 0 28 400 = T at hc
  unfold orbitCheck3Of at hc
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨htree, h0⟩, hsize⟩, hlt⟩, hnd⟩ := hc
  obtain ⟨gl, hgl⟩ := exists_cosetElems
  have hstab := cosetElems_fix hgl
  have hreach := tree_orbit htree hgl hstab
  let f : ℕ → Fin 24 → ZMod 2 := fun k => toVecD 24 T.1[k]!
  have hlt' : ∀ k < T.1.size, T.1[k]! < 2 ^ 24 := by
    intro k hk
    have := Array.all_eq_true.1 hlt k hk
    simp only [decide_eq_true_eq] at this
    rwa [getElem!_pos T.1 k hk]
  have hinj : Set.InjOn f (Set.Iio 397) := by
    intro k₁ hk₁ k₂ hk₂ hkk
    have hk₁' : k₁ < T.1.size := lt_of_lt_of_le hk₁ hsize
    have hk₂' : k₂ < T.1.size := lt_of_lt_of_le hk₂ hsize
    have heq := toVecD_injective (hlt' k₁ hk₁') (hlt' k₂ hk₂') hkk
    rw [getElem!_pos T.1 k₁ hk₁', getElem!_pos T.1 k₂ hk₂'] at heq
    have hl1 : k₁ < T.1.toList.length := by simpa using hk₁'
    have hl2 : k₂ < T.1.toList.length := by simpa using hk₂'
    exact (hnd.getElem_inj_iff (hi := hl1) (hj := hl2)).1 (by simpa using heq)
  have hsub : f '' Set.Iio 397 ⊆ MulAction.orbit (↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4)))
      (toVecD 24 28) := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < T.1.size := lt_of_lt_of_le hk hsize
    obtain ⟨g, hg2, hg4, hg⟩ := hreach k hk'
    rw [h0] at hg
    refine ⟨⟨g, Subgroup.mem_inf.2 ⟨hg2, hg4⟩⟩, ?_⟩
    exact hg
  calc 397 = (f '' Set.Iio 397).ncard := by
        rw [hinj.ncard_image, Set.ncard_Iio_nat]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end S365

end CFSG.Monster.GMS
