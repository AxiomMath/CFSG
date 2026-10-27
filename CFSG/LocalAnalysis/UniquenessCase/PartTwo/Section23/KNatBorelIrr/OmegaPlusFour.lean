module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaPlusFourModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.ProdBorelOvergroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open Matrix
open CFSG.Quasithin.S151S4 (SL2 Bsub Usub dD)

section

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem dD_mem_Bsub_L27 (d : K) (hd : d ≠ 0) : dD d hd ∈ Bsub K := by
  rw [CFSG.Quasithin.S151S4.mem_Bsub]
  simp [dD]

theorem normalizer_map_prod_Usub_omegaPlusFour (hK : 4 ≤ Nat.card K) :
    Subgroup.normalizer ((((Usub K).prod (Usub K)).map (omegaPlusFourEquiv hK).toMonoidHom :
        Subgroup ↥(StatedOmega (StatedQuadPlus 2 K))) :
          Set ↥(StatedOmega (StatedQuadPlus 2 K))) =
      ((Bsub K).prod (Bsub K)).map (omegaPlusFourEquiv hK).toMonoidHom := by
  rw [← Subgroup.map_equiv_normalizer_eq ((Usub K).prod (Usub K)) (omegaPlusFourEquiv hK)]
  rw [normalizer_prod_Usub_eq (K := K)]

theorem map_prod_top_bot_le_or_omegaPlusFour (hK : 4 ≤ Nat.card K)
    {P : Subgroup ↥(StatedOmega (StatedQuadPlus 2 K))}
    (hP : ((Bsub K).prod (Bsub K)).map (omegaPlusFourEquiv hK).toMonoidHom ≤ P)
    (hPl : ¬ P ≤ KTabD.lineStab (StatedOmega (StatedQuadPlus 2 K)) (KTabC.e1P K)) :
    ((⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K))).map
        (omegaPlusFourEquiv hK).toMonoidHom ≤ P ∨
      ((⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K))).map
        (omegaPlusFourEquiv hK).toMonoidHom ≤ P := by
  let Φ := (omegaPlusFourEquiv hK).toMonoidHom
  have hPB : (Bsub K).prod (Bsub K) ≤ P.comap Φ :=
    Subgroup.map_le_iff_le_comap.mp hP
  have hne : ¬ P.comap Φ ≤ (Bsub K).prod (Bsub K) := by
    intro hle
    apply hPl
    have hPmap : (P.comap Φ).map Φ = P :=
      Subgroup.map_comap_eq_self_of_surjective
        (f := (omegaPlusFourEquiv hK).toMonoidHom) (omegaPlusFourEquiv hK).surjective P
    rw [← hPmap]
    exact (Subgroup.map_mono (f := Φ) hle).trans
      (map_prod_Bsub_le_lineStab_omegaPlusFour hK)
  rcases prod_top_bot_le_or_of_prod_Bsub_le hK (P := P.comap Φ) hPB hne with h | h
  · exact Or.inl (Subgroup.map_le_iff_le_comap.mpr h)
  · exact Or.inr (Subgroup.map_le_iff_le_comap.mpr h)

theorem exists_mem_map_top_bot_mulVec_e1P_omegaPlusFour (hK : 4 ≤ Nat.card K) {d : K}
    (hd : d ≠ 0) :
    ∃ t ∈ ((⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K))).map
          (omegaPlusFourEquiv hK).toMonoidHom ⊓
        ((Bsub K).prod (Bsub K)).map (omegaPlusFourEquiv hK).toMonoidHom,
      ((t : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ KTabC.e1P K =
        d • KTabC.e1P K := by
  refine ⟨omegaPlusFourEquiv hK (dD d hd, 1), ?_,
    omegaPlusFourEquiv_dD_one_mulVec_e1P hK hd⟩
  rw [Subgroup.mem_inf]
  exact ⟨Subgroup.mem_map_of_mem (omegaPlusFourEquiv hK).toMonoidHom
      (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩),
    Subgroup.mem_map_of_mem (omegaPlusFourEquiv hK).toMonoidHom
      (Subgroup.mem_prod.mpr ⟨dD_mem_Bsub_L27 d hd, Subgroup.one_mem _⟩)⟩

theorem exists_mem_map_bot_top_mulVec_e1P_omegaPlusFour (hK : 4 ≤ Nat.card K) {d : K}
    (hd : d ≠ 0) :
    ∃ t ∈ ((⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K))).map
          (omegaPlusFourEquiv hK).toMonoidHom ⊓
        ((Bsub K).prod (Bsub K)).map (omegaPlusFourEquiv hK).toMonoidHom,
      ((t : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ KTabC.e1P K =
        d • KTabC.e1P K := by
  refine ⟨omegaPlusFourEquiv hK (1, dD d hd), ?_,
    omegaPlusFourEquiv_one_dD_mulVec_e1P hK hd⟩
  rw [Subgroup.mem_inf]
  exact ⟨Subgroup.mem_map_of_mem (omegaPlusFourEquiv hK).toMonoidHom
      (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩),
    Subgroup.mem_map_of_mem (omegaPlusFourEquiv hK).toMonoidHom
      (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, dD_mem_Bsub_L27 d hd⟩)⟩

theorem borelScalars_omegaPlusFour (hK : 4 ≤ Nat.card K) :
    BorelScalars (StatedOmega (StatedQuadPlus 2 K))
      (((Usub K).prod (Usub K)).map (omegaPlusFourEquiv hK).toMonoidHom) (KTabC.e1P K) := by
  let Φ := (omegaPlusFourEquiv hK).toMonoidHom
  let X₁ : Subgroup ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    ((⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K))).map Φ
  let X₂ : Subgroup ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    ((⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K))).map Φ
  refine borelScalars_of_roots
    ({X₁, X₂} : Set (Subgroup ↥(StatedOmega (StatedQuadPlus 2 K)))) ?_ ?_ ?_
  · intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl
    · rw [← Subgroup.map_commutator (f := Φ)
          (H₁ := (⊤ : Subgroup (SL2 K)).prod ⊥) (H₂ := (⊤ : Subgroup (SL2 K)).prod ⊥),
        commutator_prod_top_bot_SL2 hK]
    · rw [← Subgroup.map_commutator (f := Φ)
          (H₁ := (⊥ : Subgroup (SL2 K)).prod ⊤) (H₂ := (⊥ : Subgroup (SL2 K)).prod ⊤),
        commutator_prod_bot_top_SL2 hK]
  · intro P hNP hnot
    rw [normalizer_map_prod_Usub_omegaPlusFour hK] at hNP
    rcases map_prod_top_bot_le_or_omegaPlusFour hK hNP hnot with h | h
    · exact ⟨X₁, Set.mem_insert _ _, h⟩
    · exact ⟨X₂, Set.mem_insert_of_mem _ (Set.mem_singleton _), h⟩
  · intro X hX c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl
    · obtain ⟨t, ht, htval⟩ := exists_mem_map_top_bot_mulVec_e1P_omegaPlusFour hK hc
      refine ⟨t, ?_, htval⟩
      rw [Subgroup.mem_inf] at ht ⊢
      exact ⟨ht.1, (normalizer_map_prod_Usub_omegaPlusFour hK).ge ht.2⟩
    · obtain ⟨t, ht, htval⟩ := exists_mem_map_bot_top_mulVec_e1P_omegaPlusFour hK hc
      refine ⟨t, ?_, htval⟩
      rw [Subgroup.mem_inf] at ht ⊢
      exact ⟨ht.1, (normalizer_map_prod_Usub_omegaPlusFour hK).ge ht.2⟩

end

theorem hasBorelScalars_omegaPlusFour {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    HasBorelScalars (StatedOmega (StatedQuadPlus 2 K)) (KTabC.e1P K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_sylow_eq_prod_Usub (K := K) hK
  refine ⟨Sylow.mapSurjective (p := 2) (f := (omegaPlusFourEquiv hK).toMonoidHom)
    (omegaPlusFourEquiv hK).surjective T, ?_, ?_⟩
  · change (T : Subgroup (SL2 K × SL2 K)).map (omegaPlusFourEquiv hK).toMonoidHom ≤
      KTabD.lineStab (StatedOmega (StatedQuadPlus 2 K)) (KTabC.e1P K)
    rw [hT]
    exact (Subgroup.map_mono (f := (omegaPlusFourEquiv hK).toMonoidHom)
      prod_Usub_le_prod_Bsub).trans (map_prod_Bsub_le_lineStab_omegaPlusFour hK)
  · change BorelScalars (StatedOmega (StatedQuadPlus 2 K))
      ((T : Subgroup (SL2 K × SL2 K)).map (omegaPlusFourEquiv hK).toMonoidHom) (KTabC.e1P K)
    rw [hT]
    exact borelScalars_omegaPlusFour hK

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
