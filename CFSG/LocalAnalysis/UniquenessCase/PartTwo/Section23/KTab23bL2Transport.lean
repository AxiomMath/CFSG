module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2Parabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.Quasithin.Background.HLUBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped commutatorElement

theorem l2ParabolicLeStabilizerTransport_holds :
    L2ParabolicLeStabilizerTransport := by
  intro W V _ _ _ _ H H' n e hH' hV
  intro hL2 hBin
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  let eH : ↥H ≃* ↥H' :=
    ((MulAut.congr e).subgroupMap H).trans (MulEquiv.subgroupCongr hH'.symm)
  let S' : Sylow 2 ↥H' := S.mapSurjective (f := eH.toMonoidHom) eH.surjective
  have hL2' : IsL2 ↥H' n := CFSG.Blueprint.LieModel.of_mulEquiv eH hL2
  have hBin' : CFSG.Quasithin.BinaryNaturalSL H' ⊤ ⊥ 2 n := by
    obtain ⟨K, hF, hFin, hK, hR⟩ := hBin
    exact ⟨K, hF, hFin, hK, by
      rw [hH']
      exact CFSG.Quasithin.H.LU.realizes_map
        (CFSG.Quasithin.FFModel.nat (CFSG.Open.StatedSL 2 K)) e hR⟩
  letI : MulDistribMulAction ↥H' V := MulDistribMulAction.compHom V H'.subtype
  letI : MulAction ↥H' V := MulAction.compHom V H'.subtype
  letI : MulAction ↥H' (Set V) := Set.mulActionSet
  have hV' := hV hL2' hBin'
  letI : MulDistribMulAction ↥S' V :=
    MulDistribMulAction.compHom V (H'.subtype.comp (S' : Subgroup ↥H').subtype)
  let ℓ' : Subgroup V := fixedPointSubgroup ↥S' V
  let Pℓ' : Subgroup ↥H' := MulAction.stabilizer ↥H' (ℓ' : Set V)
  intro Pstar hpar hSP hne
  let Pstar' : Subgroup ↥H' := Pstar.map eH.toMonoidHom
  have hpar' : IsParabolicTwo ↥H' Pstar' :=
    IsParabolicTwo.map hpar eH.toMonoidHom eH.surjective
  have hSP' : S' ≤ Pstar' := by
    change (S : Subgroup ↥H).map eH.toMonoidHom ≤ Pstar.map eH.toMonoidHom
    exact Subgroup.map_mono hSP
  have hne' : Pstar' ≠ ⊤ := by
    intro htop
    apply hne
    have htop' : Pstar.map eH.toMonoidHom = (⊤ : Subgroup ↥H).map eH.toMonoidHom := by
      have h := htop
      change Pstar.map eH.toMonoidHom = ⊤ at h
      rw [h, Subgroup.map_top_of_surjective _ eH.surjective]
    exact (Subgroup.map_injective eH.injective).eq_iff.mp htop'
  have hle' : Pstar' ≤ Pℓ' := hV' S' Pstar' hpar' hSP' hne'
  have hℓ : ℓ = CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) := by
    ext w
    constructor
    · intro hw x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hw ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut W) w = w at h
      exact h
    · intro hw s
      have h := hw (s : MulAut W) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut W) w = w
      exact h
  have hℓ' : ℓ' = CFSG.Quasithin.fixV ((S' : Subgroup ↥H').map H'.subtype) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hv ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut V) v = v at h
      exact h
    · intro hv s
      have h := hv (s : MulAut V) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut V) v = v
      exact h
  have hS'coe : (S' : Subgroup ↥H') = (S : Subgroup ↥H).map eH.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hA : ((S : Subgroup ↥H).map eH.toMonoidHom).map H'.subtype =
      ((S : Subgroup ↥H).map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have heHcoe : ∀ g : ↥H, (eH g : MulAut V) = MulAut.congr e (g : MulAut W) := by
    intro g
    change ((MulEquiv.subgroupMap (MulAut.congr e) H g : MulAut V)) =
      MulAut.congr e (g : MulAut W)
    rw [MulEquiv.coe_subgroupMap_apply]
  have hfix : ℓ' = ℓ.map e.toMonoidHom := by
    rw [hℓ', hS'coe, hA, hℓ, CFSG.Quasithin.H.fixV_map_congrHom e]
  have hstab : Pℓ' = Pℓ.map eH.toMonoidHom := by
    have hfixset : Equiv.setCongr e.toEquiv (ℓ : Set W) = (ℓ' : Set V) := by
      rw [hfix]
      rfl
    have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
      eH (Equiv.setCongr e.toEquiv) ?_ (ℓ : Set W)
    · rw [hfixset] at h
      exact h.symm
    · intro g z
      change Equiv.setCongr e.toEquiv ((g : MulAut W) '' z) =
        (eH g : MulAut V) '' (Equiv.setCongr e.toEquiv z)
      rw [heHcoe g]
      ext y
      simp [Equiv.setCongr, MulAut.congr_apply, Set.image_image]
  rw [hstab] at hle'
  exact (Subgroup.map_le_map_iff_of_injective eH.injective).mp hle'

theorem l2ParabolicLeStabilizer_holds :
    ∀ (W) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      L2ParabolicLeStabilizer W H n :=
  l2ParabolicLeStabilizer_of_transport l2ParabolicLeStabilizerTransport_holds

theorem kTab23b_L2_line_uncond (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hL2line : IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) n :=
  kTab23b_L2_line W H n hnat hperf hL2line (l2ParabolicLeStabilizer_holds W H n)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
