module

public import CFSG.Quasithin.Vol2.Ch3E213MP5C
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open CFSG.QuasithinUnique

section Transport

variable {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')

theorem isSylowTwoOf_map_equiv {S X : Subgroup Y} (h : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  show ¬ 2 ∣ (S.map e.toMonoidHom).relIndex (X.map e.toMonoidHom)
  rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  exact h.2.2

theorem map_inf_normalizer (L S : Subgroup Y) :
    (L ⊓ Subgroup.normalizer (S : Set Y)).map e.toMonoidHom =
      L.map e.toMonoidHom ⊓ Subgroup.normalizer (S.map e.toMonoidHom : Set Y') := by
  rw [Subgroup.map_inf _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq]

theorem isParabolic2_map_equiv {L P : Subgroup Y} (h : IsParabolic2 L P) :
    IsParabolic2 (L.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hPL, S, hS, hLS⟩ := h
  refine ⟨Subgroup.map_mono hPL, S.map e.toMonoidHom, isSylowTwoOf_map_equiv e hS, ?_⟩
  rw [← map_inf_normalizer]
  exact Subgroup.map_mono hLS

theorem isMaxParabolic2_map_equiv {L P : Subgroup Y} (h : IsMaxParabolic2 L P) :
    IsMaxParabolic2 (L.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hP, hne, hmax⟩ := h
  refine ⟨isParabolic2_map_equiv e hP, fun h' => hne (Subgroup.map_injective e.injective h'),
    fun Q hQ hQne hPQ => ?_⟩
  have hQ' := isParabolic2_map_equiv e.symm hQ
  rw [map_symm_map] at hQ'
  have h1 := hmax (Q.map e.symm.toMonoidHom) hQ'
    (fun h'' => hQne (by rw [← h'', map_map_symm]))
    (fun x hx => ⟨e x, hPQ ⟨x, hx, rfl⟩, by simp⟩)
  rw [← h1, map_map_symm]

theorem map_le_normalizer {X P : Subgroup Y} (h : X ≤ Subgroup.normalizer (P : Set Y)) :
    X.map e.toMonoidHom ≤ Subgroup.normalizer (P.map e.toMonoidHom : Set Y') := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono h

end Transport

section Sylow

variable {Y : Type} [Group Y]

theorem isSylowTwoOf_subgroupOf_top {S K : Subgroup Y} (h : IsSylowTwoOf S K) :
    IsSylowTwoOf (S.subgroupOf K) (⊤ : Subgroup K) := by
  refine ⟨le_top, h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm, ?_⟩
  show ¬ 2 ∣ (S.subgroupOf K).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact h.2.2

variable [Finite Y]

theorem le_of_le_normalizer {A C Q : Subgroup Y} (hA : IsSylowTwoOf A C) (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ C) (hQA : Q ≤ Subgroup.normalizer (A : Set Y)) : Q ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : IsPGroup 2 ↥(Q ⊔ A) := hQ.to_sup_of_normal_right' hA.2.1 hQA
  exact le_sup_left.trans (E2P.eq_of_isSylowTwoOf_le hA hR le_sup_right (sup_le hQC hA.1)).le

theorem inf_normalizer_eq_of_borel {K S B S₀ : Subgroup Y} (hS : IsSylowTwoOf (S ⊓ K) K)
    (hS₀ : IsSylowTwoOf S₀ K) (hB : B ⊓ K = K ⊓ Subgroup.normalizer (S₀ : Set Y))
    (hSB : S ⊓ K ≤ B ⊓ K) : B ⊓ K = K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup Y) : Set Y) := by
  have hle : S ⊓ K ≤ S₀ :=
    le_of_le_normalizer hS₀ hS.2.1 inf_le_right ((hSB.trans hB.le).trans inf_le_right)
  rw [hB, E2P.eq_of_isSylowTwoOf_le hS hS₀.2.1 hle hS₀.1]

end Sylow

end CFSG.Quasithin.Ch3E213M.P5
