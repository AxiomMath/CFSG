module

public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Vol2.Ch11SecBNPE114

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def TypeLie (n : ℕ) (Y : Type) [Group Y] : Prop :=
  IsPSL 2 2 n Y ∨ IsSz n Y ∨ IsPSU 3 2 n Y ∨ IsPSL 3 2 n Y ∨ IsPSp4 2 n Y ∨
    (n = 1 ∧ IsAlt 6 Y)

theorem TypeLie.of_mulEquiv {n : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeLie n Y') : TypeLie n Y := by
  rcases h with h | h | h | h | h | ⟨hn, h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))))
  · obtain ⟨e'⟩ : Nonempty (Y' ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, ⟨e.trans e'⟩⟩))))

theorem TypeLie.isSimpleGroup {n : ℕ} {Y : Type} [Group Y] (h : TypeLie n Y) :
    IsSimpleGroup Y := by
  rcases h with h | h | h | h | h | ⟨-, h⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity Y 2 n h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 n h).2
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y 2 2 n h
  · obtain ⟨e⟩ : Nonempty (Y ≃* alternatingGroup (Fin 6)) := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup

theorem nParam_sup_eq_of_typeLie (h1114 : ASInputs.AS_E_1_14) {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hSQ : SQTKGroup X) (hT : TypeLie n X) {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) = n := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hIn : I.Normal := normal_range_conj X
  have hSQI : SQTKGroup ↥I :=
    sqtkGroup_of_mulEquiv (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm hSQ
  have hSQZ : SQTKGroup ↥Z := InternalSec.sqtkGroup_of_two_pow le_sup_left
    (fun y _ k hk => hIn.conj_mem k hk y) (pow_mem_of_mem_sup hB) hSQI
  set e := generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFT : TypeLie n (ASInputs.FStar ↥Z) := TypeLie.of_mulEquiv e hT
  obtain ⟨h1, -⟩ := h1114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
    (generalizedFitting_sup_sup hnab B)
  have key : E1.nParam (⊤ : Subgroup ↥Z) = n := by
    refine h1 n hn ?_
    rcases hFT with h | h | h | h | h | ⟨hn1, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨hn1, h⟩)))))
  rw [E1.nParam_subgroupOf, key]

end CFSG.Quasithin.Vol2.Ch11.SecB
