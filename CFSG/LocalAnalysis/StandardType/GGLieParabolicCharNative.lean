module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharBorel

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace RootWeightDatum


variable {K : Type} [Field K]

theorem borel_le_normalizer_unipotent (D : RootWeightDatum K) :
    D.borel ≤ Subgroup.normalizer (D.unipotent : Set (ModGL D.tag K)) := by
  cases D with
  | ordinary τ =>
    exact (le_of_eq (borel_self_normalizers τ K).1.symm).trans inf_le_right
  | fixed t σ hσ =>
    exact graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent
      (t := t) (K := K) (σ := σ.toRingHom)

private theorem top_map_subtype_eq {α : Type*} [Group α] (G : Subgroup α) :
    (⊤ : Subgroup G).map G.subtype = G := by
  ext x
  exact ⟨fun hx => Subgroup.map_subtype_le ⊤ hx,
    fun hx => Subgroup.mem_map.2 ⟨⟨x, hx⟩, trivial, rfl⟩⟩

theorem isCharacteristicP_of_normalizer_sylow_le [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : RootWeightDatum K) {S X : Subgroup D.group} (hS : IsPGroup p S) (hSi : ¬ p ∣ S.index)
    (hNX : Subgroup.normalizer (S : Set D.group) ≤ X) (hX : X ≠ ⊤) :
    CFSG.IsCharacteristicP p ↥X := by
  haveI : Finite (ModGL D.tag K) := finite_modGL (τ := D.tag) (K := K)
  let S₀ : Sylow p D.group := hS.toSylow hSi
  obtain ⟨P₀, hP₀⟩ := D.exists_sylow_eq_unipotent p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.group S₀ P₀
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hS₀coe : (S₀ : Subgroup D.group) = S := IsPGroup.toSylow_coe hS hSi
  have hmap : S.map (MulAut.conj g).toMonoidHom = D.unipotent.subgroupOf D.group := by
    rw [← hS₀coe, ← coe_smul_sylow_eq_map g S₀, hg, hP₀]
  have hnormalizer_le : Subgroup.normalizer (D.unipotent.subgroupOf D.group) ≤
      X.map (MulAut.conj g).toMonoidHom := by
    rw [← hmap, ← Subgroup.map_equiv_normalizer_eq S (MulAut.conj g)]
    exact Subgroup.map_mono hNX
  have hborel_sub : D.borel.subgroupOf D.group ≤
      Subgroup.normalizer (D.unipotent.subgroupOf D.group) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    rw [Subgroup.mem_set_normalizer_iff]
    intro u
    show (u : ModGL D.tag K) ∈ D.unipotent ↔
      ((b * u * b⁻¹ : D.group) : ModGL D.tag K) ∈ D.unipotent
    exact Subgroup.mem_set_normalizer_iff.1 (borel_le_normalizer_unipotent D hb)
      (u : ModGL D.tag K)
  let A : Subgroup (ModGL D.tag K) := (X.map (MulAut.conj g).toMonoidHom).map D.group.subtype
  have hBA : D.borel ≤ A := by
    intro x hx
    have hxg : x ∈ D.group := D.borel_le_group hx
    have hxX : (⟨x, hxg⟩ : D.group) ∈ X.map (MulAut.conj g).toMonoidHom :=
      hnormalizer_le (hborel_sub (Subgroup.mem_subgroupOf.2 hx))
    exact Subgroup.mem_map.2 ⟨⟨x, hxg⟩, hxX, rfl⟩
  have hAG : A ≤ D.group := Subgroup.map_subtype_le (X.map (MulAut.conj g).toMonoidHom)
  have hAne : A ≠ D.group := by
    intro hAeq
    apply hX
    have hmapeq : X.map (MulAut.conj g).toMonoidHom = ⊤ :=
      Subgroup.map_injective D.group.subtype_injective
        (hAeq.trans (top_map_subtype_eq D.group).symm)
    have hXeq : X = ⊤ := by
      have h := (Subgroup.comap_map_eq_self_of_injective
        (f := (MulAut.conj g).toMonoidHom) hinj X).symm
      rw [h, hmapeq]
      exact Subgroup.comap_top (MulAut.conj g).toMonoidHom
    exact hXeq
  have hAchar : CFSG.IsCharacteristicP p ↥A :=
    isCharacteristicP_of_borel_le p D hBA hAG hAne
  exact CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    ((Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom hinj).trans
      (Subgroup.equivMapOfInjective (X.map (MulAut.conj g).toMonoidHom) D.group.subtype
        D.group.subtype_injective)).symm hAchar

end RootWeightDatum

end CFSG.LieType.Chevalley
