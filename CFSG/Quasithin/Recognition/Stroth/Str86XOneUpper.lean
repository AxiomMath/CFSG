module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem u3Z1_le_u3Y {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (h1 : VU3Big L1) (hB2 : VBig L2)
    (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S ≤ u3Y L1 L2 S := by
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.1
  exact le_inf hZ1Z2 (omegaOneCenterOf_le (Q1 L1 L2 S))

theorem u3_commutator_q1_z2_le_u3Y {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    ⁅Q1 L1 L2 S, Z2 L1 L2 S⁆ ≤ u3Y L1 L2 S := by
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW))
  have hleft : ⁅Q1 L1 L2 S, Z2 L1 L2 S⁆ ≤ Q1 L1 L2 S :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (hZ2S.trans (le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S)))
  have hright : ⁅Q1 L1 L2 S, Z2 L1 L2 S⁆ ≤ Z2 L1 L2 S :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp
      (hQ1S.trans (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S)))
  rw [u3Y]
  exact le_inf hright hleft

theorem u3_commutator_u3X1_z2_le_u3Y {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    ⁅u3X1 L1 L2 S, Z2 L1 L2 S⁆ ≤ u3Y L1 L2 S :=
  (Subgroup.commutator_mono (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)) le_rfl).trans
    (u3_commutator_q1_z2_le_u3Y hF)

theorem u3_commutator_u3X1_conj_z2_le_u3Y
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {l : G} (hl : l ∈ L1) :
    ⁅u3X1 L1 L2 S, conjSub l (Z2 L1 L2 S)⁆ ≤ conjSub l (u3Y L1 L2 S) := by
  have hXeq : conjSub l (u3X1 L1 L2 S) = u3X1 L1 L2 S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_u3X1_left (L1 := L1) (L2 := L2) (S := S) hl)
  calc ⁅u3X1 L1 L2 S, conjSub l (Z2 L1 L2 S)⁆
      = ⁅conjSub l (u3X1 L1 L2 S), conjSub l (Z2 L1 L2 S)⁆ := by rw [hXeq]
    _ = conjSub l ⁅u3X1 L1 L2 S, Z2 L1 L2 S⁆ := by
        simp only [conjSub, ← Subgroup.map_commutator]
    _ ≤ conjSub l (u3Y L1 L2 S) :=
        conjSub_mono l (u3_commutator_u3X1_z2_le_u3Y hF)

theorem u3L1_inf_normalizer_eq_borelOf {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    L1 ⊓ Subgroup.normalizer (S : Set G) = borelOf L1 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL1, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxP : x ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hxL1
    have hxbig : x ∈ bigB L1 L2 S :=
      str86_p1_inf_normalizer_le_bigB hF.toW hSB (Subgroup.mem_inf.mpr ⟨hxP, hxN⟩)
    rw [← F1.inf_bigB_eq_borelOf hR]
    exact Subgroup.mem_inf.mpr ⟨hxL1, hxbig⟩
  · intro x hx
    rw [← F1.inf_bigB_eq_borelOf hR] at hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hSB (Subgroup.mem_inf.mp hx).2⟩

theorem u3_exists_mem_L1_not_normalizer {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    ∃ g ∈ L1, g ∉ Subgroup.normalizer (S : Set G) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨g, hgL1, hgb⟩ := SetLike.exists_of_lt (F1.lt_borelOf hR)
  refine ⟨g, hgL1, fun hgN => hgb ?_⟩
  rw [← u3L1_inf_normalizer_eq_borelOf hF hSB]
  exact Subgroup.mem_inf.mpr ⟨hgL1, hgN⟩

end CFSG.Quasithin.Stroth
