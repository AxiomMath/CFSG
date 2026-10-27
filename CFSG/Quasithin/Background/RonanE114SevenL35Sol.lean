module

public import CFSG.Quasithin.Background.RonanE114SevenL35Norm
public import CFSG.Quasithin.Background.RonanE114SevenL35Cent

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open scoped MatrixGroups
open CFSG.Wreathed CFSG.Wreathed.BrauerWong

theorem isSolvable_sup_of_le_normalizer' {Γ : Type*} [Group Γ] {T D : Subgroup Γ}
    (hD : D ≤ Subgroup.normalizer (T : Set Γ)) (hT : Group.IsSolvable T)
    (hD' : Group.IsSolvable D) : Group.IsSolvable ↥(D ⊔ T) := by
  have hnorm : (T.subgroupOf (D ⊔ T)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hD
  have hnormD : (T.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hD
  have hker : (QuotientGroup.mk' (T.subgroupOf (D ⊔ T))).ker ≤
      (T.subgroupOf (D ⊔ T)).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  let e₁ := Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ D ⊔ T)
  have h1 : Group.IsSolvable ↥(T.subgroupOf (D ⊔ T)) :=
    Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  let e₂ := QuotientGroup.quotientInfEquivProdNormalizerQuotient D T hD
  have h2 : Group.IsSolvable (↥(D ⊔ T) ⧸ T.subgroupOf (D ⊔ T)) := by
    have : Group.IsSolvable (↥D ⧸ T.subgroupOf D) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact Group.isSolvable_of_surjective (f := e₂.toMonoidHom) e₂.surjective
  exact Group.isSolvable_of_ker_le_range _ _ hker

theorem centralizer_modelV35_comm {g h : SL(3, ZMod 5)}
    (hg : g ∈ Subgroup.centralizer (modelV sylowS35 e35 : Set SL(3, ZMod 5)))
    (hh : h ∈ Subgroup.centralizer (modelV sylowS35 e35 : Set SL(3, ZMod 5))) :
    g * h = h * g := by
  have hmem : ∀ x ∈ ({u35 * v35, u35 ^ 2, s35} : Set SL(3, ZMod 5)),
      x ∈ (modelV sylowS35 e35 : Subgroup SL(3, ZMod 5)) := by
    intro x hx
    rw [modelV_eq35]
    exact Subgroup.subset_closure hx
  have key : ∀ k ∈ Subgroup.centralizer (modelV sylowS35 e35 : Set SL(3, ZMod 5)),
      k * (u35 * v35) = (u35 * v35) * k ∧ k * u35 ^ 2 = u35 ^ 2 * k := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff] at hk
    exact ⟨(hk _ (hmem _ (by simp))).symm, (hk _ (hmem _ (by simp))).symm⟩
  obtain ⟨hg₁, hg₂⟩ := key g hg
  obtain ⟨hh₁, hh₂⟩ := key h hh
  exact comm_of_commutes_gens35 hg₁ hg₂ hh₁ hh₂

theorem isSolvable_normalizer_modelV35 :
    Group.IsSolvable ↥(Subgroup.normalizer
      (modelV sylowS35 e35 : Set SL(3, ZMod 5))) := by
  set V := modelV sylowS35 e35 with hV
  set N := Subgroup.normalizer (V : Set SL(3, ZMod 5)) with hN
  set C := Subgroup.centralizer (V : Set SL(3, ZMod 5)) with hC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥C :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (centralizer_modelV35_comm a.2 b.2)
  have hVp : IsPGroup 2 ↥V :=
    (sylowS35.isPGroup').to_le (modelV_le_sylow sylowS35 e35)
  haveI : Group.IsNilpotent ↥V := hVp.isNilpotent
  haveI : Group.IsSolvable ↥V := inferInstance
  have hCV : C ≤ Subgroup.normalizer (V : Set SL(3, ZMod 5)) :=
    Subgroup.centralizer_le_normalizer _
  haveI : Group.IsSolvable ↥(C ⊔ V) := isSolvable_sup_of_le_normalizer' hCV inferInstance inferInstance
  have hVCN : V ⊔ C ≤ N := sup_le Subgroup.le_normalizer hCV
  haveI : Group.IsSolvable ↥(V ⊔ C) := by rw [sup_comm]; infer_instance
  haveI : Group.IsSolvable ↥(modelVInnerCentralizer sylowS35 e35) := by
    rw [modelVInnerCentralizer_eq]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hVCN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hVCN).injective
  haveI : Group.IsSolvable (↥N ⧸ modelVInnerCentralizer sylowS35 e35) := by
    rcases modelVNormalizerQuotient_alternatives 2 le_rfl sylowS35 e35 with h2 | h6
    · have hp : IsPGroup 2 (↥N ⧸ modelVInnerCentralizer sylowS35 e35) :=
        IsPGroup.of_card (n := 1) (by rw [h2]; norm_num)
      haveI : Group.IsNilpotent (↥N ⧸ modelVInnerCentralizer sylowS35 e35) := hp.isNilpotent
      infer_instance
    · obtain ⟨f⟩ := h6
      haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
      exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  exact Group.isSolvable_of_subgroup_quotient (modelVInnerCentralizer sylowS35 e35)

end CFSG.Quasithin.RonanE114.Seven.L35
