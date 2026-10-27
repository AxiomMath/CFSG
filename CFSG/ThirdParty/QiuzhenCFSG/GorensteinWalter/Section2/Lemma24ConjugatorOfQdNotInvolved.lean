module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.AmbientSylowZJNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma24PCoreCenter
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB

namespace CFSG
end CFSG
open CFSG

/-!
# The Glauberman conjugator for Gorenstein--Walter Lemma 2.4

This module carries out the complete Theorem-A/Theorem-B argument once
`Qd(p)` is known not to be involved in the ambient group.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

open Glauberman

universe u

/-- If `Qd(p)` is not involved in `G`, the two maximal subgroups in Lemma
2.4 are conjugate by an element of `A`. -/
public theorem lemma24_glauberman_conjugator_of_not_involved
    {G : Type u} [Group G] [Finite G]
    {A M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hsimple : IsSimpleGroup G)
    (hA : IsCoatom A) (hM : IsCoatom M)
    (hAM : NormalizerControlledBy A M)
    (hp : p.Prime) (hodd : Odd p)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf A))
    (hMp : IsPGroup p (generalizedFittingSubgroupOf M))
    (hInvG : ¬ Involved (Qd p) G) :
    ∃ g : G, conjugateSubgroup A g = M ∧ g ∈ A := by
  classical
  have hpodd : p ≠ 2 := by
    rcases hodd with ⟨k, hk⟩
    omega
  let Wint : Subgroup (↥A) := centerIn (G := ↥A) (pCore p (↥A))
  let W : Subgroup G := section8SubgroupInAmbient Wint
  obtain ⟨hWne, hNW, hWM, hWp⟩ :=
    lemma24_pCoreCenter_data hsimple hA hAM hp hAp
  have hWleA : W ≤ A := by
    rw [← hNW]
    exact Subgroup.le_normalizer

  let WA : Subgroup (↥A) := W.subgroupOf A
  have hWAp : IsPGroup p WA :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWleA).symm
  have hWAne : WA ≠ ⊥ := by
    intro hbot
    apply hWne
    calc
      W = WA.map A.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWleA).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  obtain ⟨PA, hWAlePA⟩ := IsPGroup.exists_le_sylow hWAp
  have hPAne : (PA : Subgroup (↥A)) ≠ ⊥ := by
    intro hbot
    apply hWAne
    apply le_bot_iff.mp
    simpa [hbot] using hWAlePA

  let WM : Subgroup (↥M) := W.subgroupOf M
  have hWMp : IsPGroup p WM :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  have hWMne : WM ≠ ⊥ := by
    intro hbot
    apply hWne
    calc
      W = WM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWM).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  obtain ⟨PM, hWMlePM⟩ := IsPGroup.exists_le_sylow hWMp
  have hPMne : (PM : Subgroup (↥M)) ≠ ⊥ := by
    intro hbot
    apply hWMne
    apply le_bot_iff.mp
    simpa [hbot] using hWMlePM

  obtain ⟨PAG, hPAG, hNZA⟩ :=
    exists_ambient_sylow_with_zj_normalizer_eq_of_fstar_pgroup
      hpodd hsimple hInvG A hA hAp PA hPAne
  obtain ⟨PMG, hPMG, hNZM⟩ :=
    exists_ambient_sylow_with_zj_normalizer_eq_of_fstar_pgroup
      hpodd hsimple hInvG M hM hMp PM hPMne
  obtain ⟨g, hgSyl⟩ : ∃ g : G, g • PAG = PMG :=
    MulAction.exists_smul_eq G PAG PMG
  have hPmap :
      (PAG : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (PMG : Subgroup G) := by
    rw [← sylow_smul_subgroup_eq_map_conj g PAG, hgSyl]
  have hZmap :
      (ZJ (G := G) (PAG : Subgroup G)).map (MulAut.conj g).toMonoidHom =
        ZJ (G := G) (PMG : Subgroup G) := by
    have hK := (zjCharacteristicFunctor p).K_conj (PAG : Subgroup G) g
    rw [hPmap] at hK
    simpa [zjCharacteristicFunctor, zjFunctor, ZJ] using hK.symm
  have hgAM : conjugateSubgroup A g = M := by
    calc
      conjugateSubgroup A g =
          (Subgroup.normalizer
            ((ZJ (G := G) (PAG : Subgroup G) : Subgroup G) : Set G)).map
              (MulAut.conj g).toMonoidHom := by rw [hNZA]; rfl
      _ = Subgroup.normalizer
          (((ZJ (G := G) (PAG : Subgroup G) : Subgroup G)).map
            (MulAut.conj g).toMonoidHom : Set G) :=
        Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective
      _ = Subgroup.normalizer
          ((ZJ (G := G) (PMG : Subgroup G) : Subgroup G) : Set G) := by
        rw [hZmap]
      _ = M := hNZM

  have hconjM : conjSubgroup g M = A := by
    rw [← hgAM]
    unfold conjSubgroup conjugateSubgroup
    rw [Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hWgA : conjSubgroup g W ≤ A := by
    calc
      conjSubgroup g W ≤ conjSubgroup g M :=
        Subgroup.map_mono hWM
      _ = A := hconjM
  have hWgp : IsPGroup p (conjSubgroup g W) :=
    hWp.map (MulAut.conj g⁻¹).toMonoidHom
  have hWgne : conjSubgroup g W ≠ ⊥ := by
    intro hbot
    apply hWne
    calc
      W = conjSubgroup g⁻¹ (conjSubgroup g W) := by
        rw [conjSubgroup_comp]
        ext x
        simp [conjSubgroup]
      _ = ⊥ := by rw [hbot]; simp [conjSubgroup]
  let V : Subgroup (↥A) := (conjSubgroup g W).subgroupOf A
  have hVp : IsPGroup p V :=
    hWgp.of_equiv (Subgroup.subgroupOfEquivOfLe hWgA).symm
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hWgne
    calc
      conjSubgroup g W = V.map A.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWgA).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  obtain ⟨P, hVleP⟩ := IsPGroup.exists_le_sylow hVp
  have hPne : (P : Subgroup (↥A)) ≠ ⊥ := by
    intro hbot
    apply hVne
    apply le_bot_iff.mp
    simpa [hbot] using hVleP
  obtain ⟨PG, hPG, hNZP⟩ :=
    exists_ambient_sylow_with_zj_normalizer_eq_of_fstar_pgroup
      hpodd hsimple hInvG A hA hAp P hPne

  have hWlePG : (W : Set G) ⊆ (PG : Subgroup G) := by
    intro w hw
    rw [hPG]
    rcases Subgroup.mem_map.mp hw with ⟨wA, hwW, rfl⟩
    refine Subgroup.mem_map.mpr ⟨wA, ?_, rfl⟩
    exact (pCore_le_sylow (G := ↥A) P) hwW.1
  have hWgLePG : conjSubset g (W : Set G) ⊆ (PG : Subgroup G) := by
    rw [conjSubset_eq_conjSubgroup]
    intro w hw
    rw [hPG]
    have hwA : w ∈ A := hWgA hw
    refine Subgroup.mem_map.mpr ⟨⟨w, hwA⟩, ?_, rfl⟩
    exact hVleP hw
  obtain ⟨c, n, hcW, hnZ, hcn⟩ :=
    Glauberman.theoremB hpodd PG hInvG (W : Set G)
      ⟨1, W.one_mem⟩ hWlePG g hWgLePG
  have hcA : c ∈ A := by
    have hcN : c ∈ Subgroup.normalizer (W : Set G) :=
      (Subgroup.centralizer_le_normalizer (W : Set G)) hcW
    rwa [hNW] at hcN
  have hnA : n ∈ A := by
    rwa [hNZP] at hnZ
  have hgA : g ∈ A := by
    rw [hcn]
    exact A.mul_mem hcA hnA
  exact ⟨g, hgAM, hgA⟩

end CFSG.GorensteinWalter
