module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSz2
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem sz_vertex {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S ∧ Q1 L1 L2 S ≤ S ∧ L1 ⊔ S = L1 ⊔ Q1 L1 L2 S ∧
      ∃ e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K,
        (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K := by
  classical
  obtain ⟨eSz⟩ := hSz
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF hS1
  let e0 : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K :=
    (CFSG.Quasithin.H13.oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF).trans (eSz.trans (suzukiGroupEquivSz a K hK).symm))
  have hSylTop : IsSylowTwoOf (S.subgroupOf (L1 ⊔ S)) ⊤ :=
    CFSG.Quasithin.H13.NQCat.A314D.isSylowTwoOf_top_subgroupOf hSyl1
  have hP : IsSylowTwoOf ((szSbar L1 L2 S).map e0.toMonoidHom) ⊤ := by
    have h := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hSylTop
      (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) (QuotientGroup.mk'_surjective _)
    exact CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective h e0.toMonoidHom e0.surjective
  have hU : IsSylowTwoOf (suzukiU a K) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hP hU
  refine ⟨hpCore1, hQ1S, hsup1, e0.trans (MulAut.conj g), ?_⟩
  have hmap : (szSbar L1 L2 S).map (e0.trans (MulAut.conj g)).toMonoidHom =
      ((szSbar L1 L2 S).map e0.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [show (e0.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e0.toMonoidHom from rfl, ← Subgroup.map_map]
  rw [hmap, hg]
  rfl

end CFSG.Quasithin.Stroth.G5F

end
