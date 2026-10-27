module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal.Symplectic CFSG.SeitzReduction.F4Pilot
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

private theorem irgSp_two_smul_not_mem {n : ℕ} {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    2 • γ ∉ roots (isFiniteType_cartanC n) ∅ := by
  intro h2
  obtain ⟨r, hr⟩ :=
    CFSG.LieType.Universal.Symplectic.SpExtras.exists_stdVec_of_mem_roots hγ
  obtain ⟨r', hr'⟩ :=
    CFSG.LieType.Universal.Symplectic.SpExtras.exists_stdVec_of_mem_roots h2
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.toStd_nsmul', ← hr] at hr'
  have h1 := CFSG.LieType.Universal.Symplectic.SpExtras.dot_stdVec r
  have h2' := CFSG.LieType.Universal.Symplectic.SpExtras.dot_stdVec r'
  rw [hr', smul_dotProduct, dotProduct_smul, smul_smul, nsmul_eq_mul] at h2'
  push_cast at h2'
  omega

private theorem irgSp_exists_map_tauSp_rootGroup_two
    {K : Type} [Field K] [CharP K 2] [Finite K]
    {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    ∃ w ∈ roots (isFiniteType_cartanC 2) ∅,
      (CFSG.LieType.Universal.Symplectic.rootGroup 2 K v).map
          (tauSp : CFSG.Open.StatedSp 2 K →* CFSG.Open.StatedSp 2 K) =
        CFSG.LieType.Universal.Symplectic.rootGroup 2 K w ∧
      (CFSG.LieType.Universal.Symplectic.rootGroup 2 K (-v)).map
          (tauSp : CFSG.Open.StatedSp 2 K →* CFSG.Open.StatedSp 2 K) =
        CFSG.LieType.Universal.Symplectic.rootGroup 2 K (-w) := by
  obtain ⟨r, hr⟩ :=
    CFSG.LieType.Universal.Symplectic.SpExtras.exists_stdVec_of_mem_roots hv
  obtain ⟨w, hw, hwr⟩ := CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec (tauIdx r)
  refine ⟨w, hw, ?_, ?_⟩
  · exact map_rootGroup_of_elt _
      (pow_tauExp_surjective r) (tauSp_elt r) hr hwr.symm
  · have hr' : stdVec (negIdx r) = toStd 2 (-v) := by
      rw [stdVec_negIdx, hr, CFSG.LieType.Universal.Symplectic.SpExtras.toStd_neg']
    have hw' : stdVec (tauIdx (negIdx r)) = toStd 2 (-w) := by
      rw [← negIdx_tauIdx, stdVec_negIdx,
        CFSG.LieType.Universal.Symplectic.SpExtras.toStd_neg', hwr]
    exact map_rootGroup_of_elt _
      (pow_tauExp_surjective (negIdx r)) (tauSp_elt (negIdx r)) hr' hw'

theorem irgRootPairAut_PSp_two
    {g : ℕ} (hadm : StatedLieAdmissible .PSp 2 2 g) : IRGRootPairAut .PSp 2 g := by
  intro θ β' hβ' hlong u'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (GaloisField 2 g) 2 := inferInstance
  haveI : Finite (GaloisField 2 g) := inferInstance
  have hZ : Subgroup.center (ggU .PSp 2 g).K = ⊥ := by
    change Subgroup.center (CFSG.Open.StatedSp 2 (GaloisField 2 g)) = ⊥
    exact CFSG.SeitzReduction.F4Pilot.center_statedSp_eq_bot_of_charTwo
      (K := GaloisField 2 g) (n := 2)
  obtain ⟨α, hα⟩ := irg_exists_aut_of_center_eq_bot hZ θ
  obtain ⟨s, σ, hαs | hαs⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp_tauSp
      (K := GaloisField 2 g) α
  · let sG : (ggU .PSp 2 g).K := s
    have hhom : α.toMonoidHom =
        (MulAut.conj s).toMonoidHom.comp
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 2
            (GaloisField 2 g) σ).toMonoidHom :=
      MonoidHom.ext hαs
    have hmap : ((ggU .PSp 2 g).D.rootGroup β').map α.toMonoidHom =
        ((ggU .PSp 2 g).D.rootGroup β').map (MulAut.conj sG).toMonoidHom := by
      change (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) β').map
          α.toMonoidHom =
        (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) β').map
          (MulAut.conj s).toMonoidHom
      rw [hhom]
      erw [← Subgroup.map_map]
      erw [CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup]
      rfl
    have hmapneg : ((ggU .PSp 2 g).D.rootGroup (-β')).map α.toMonoidHom =
        ((ggU .PSp 2 g).D.rootGroup (-β')).map (MulAut.conj sG).toMonoidHom := by
      change (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) (-β')).map
          α.toMonoidHom =
        (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) (-β')).map
          (MulAut.conj s).toMonoidHom
      rw [hhom]
      erw [← Subgroup.map_map]
      erw [CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup]
      rfl
    refine ⟨β', ⟨hβ', Or.inl hlong⟩, α u' * sG, ?_, ?_⟩
    · simpa only [ggRootSub] using
        (irg_map_conj_subgroup_mulAut
          (QuotientGroup.mk' (Subgroup.center (ggU .PSp 2 g).K)) θ α hα
          (A := (ggU .PSp 2 g).D.rootGroup β') (B := (ggU .PSp 2 g).D.rootGroup β')
          (t := sG) (u := u') hmap)
    · simpa only [ggRootSub] using
        (irg_map_conj_subgroup_mulAut
          (QuotientGroup.mk' (Subgroup.center (ggU .PSp 2 g).K)) θ α hα
          (A := (ggU .PSp 2 g).D.rootGroup (-β')) (B := (ggU .PSp 2 g).D.rootGroup (-β'))
          (t := sG) (u := u') hmapneg)
  · have hβ'roots : β' ∈ roots (isFiniteType_cartanC 2) ∅ := hβ'
    obtain ⟨w, hw, hτ, hτneg⟩ :=
      irgSp_exists_map_tauSp_rootGroup_two (K := GaloisField 2 g) hβ'roots
    let sG : (ggU .PSp 2 g).K := s
    have hhom : α.toMonoidHom =
        (MulAut.conj s).toMonoidHom.comp
          ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 2
              (GaloisField 2 g) σ).toMonoidHom.comp
            (tauSp : CFSG.Open.StatedSp 2 (GaloisField 2 g) →*
              CFSG.Open.StatedSp 2 (GaloisField 2 g))) :=
      MonoidHom.ext hαs
    have hmap : ((ggU .PSp 2 g).D.rootGroup β').map α.toMonoidHom =
        ((ggU .PSp 2 g).D.rootGroup w).map (MulAut.conj sG).toMonoidHom := by
      change (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) β').map
          α.toMonoidHom =
        (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) w).map
          (MulAut.conj s).toMonoidHom
      rw [hhom]
      erw [← Subgroup.map_map]
      erw [← Subgroup.map_map]
      erw [hτ]
      erw [CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup]
      rfl
    have hmapneg : ((ggU .PSp 2 g).D.rootGroup (-β')).map α.toMonoidHom =
        ((ggU .PSp 2 g).D.rootGroup (-w)).map (MulAut.conj sG).toMonoidHom := by
      change (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) (-β')).map
          α.toMonoidHom =
        (CFSG.LieType.Universal.Symplectic.rootGroup 2 (GaloisField 2 g) (-w)).map
          (MulAut.conj s).toMonoidHom
      rw [hhom]
      erw [← Subgroup.map_map]
      erw [← Subgroup.map_map]
      erw [hτneg]
      erw [CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup]
      rfl
    refine ⟨w, ⟨hw, Or.inr ⟨Or.inl ⟨rfl, rfl⟩, irgSp_two_smul_not_mem hw⟩⟩,
      α u' * sG, ?_, ?_⟩
    · exact irg_map_conj_subgroup_mulAut
          (QuotientGroup.mk' (Subgroup.center (ggU .PSp 2 g).K)) θ α hα
          (A := (ggU .PSp 2 g).D.rootGroup β') (B := (ggU .PSp 2 g).D.rootGroup w)
          (t := sG) (u := u') hmap
    · exact irg_map_conj_subgroup_mulAut
          (QuotientGroup.mk' (Subgroup.center (ggU .PSp 2 g).K)) θ α hα
          (A := (ggU .PSp 2 g).D.rootGroup (-β')) (B := (ggU .PSp 2 g).D.rootGroup (-w))
          (t := sG) (u := u') hmapneg

theorem irgRootPairAut_PSp
    {n g : ℕ} (hn : 3 ≤ n) (hadm : StatedLieAdmissible .PSp n 2 g) :
    IRGRootPairAut .PSp n g := by
  intro θ β' hβ' hlong u'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (GaloisField 2 g) 2 := inferInstance
  haveI : Finite (GaloisField 2 g) := inferInstance
  haveI : NeZero n := ⟨by omega⟩
  have hZ : Subgroup.center (ggU .PSp n g).K = ⊥ := by
    change Subgroup.center (CFSG.Open.StatedSp n (GaloisField 2 g)) = ⊥
    exact CFSG.SeitzReduction.F4Pilot.center_statedSp_eq_bot_of_charTwo
      (K := GaloisField 2 g) (n := n)
  obtain ⟨α, hα⟩ := irg_exists_aut_of_center_eq_bot hZ θ
  obtain ⟨s, σ, hαs⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp
      (K := GaloisField 2 g) hn α
  let sG : (ggU .PSp n g).K := s
  have hhom : α.toMonoidHom =
      (MulAut.conj s).toMonoidHom.comp
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n
          (GaloisField 2 g) σ).toMonoidHom :=
    MonoidHom.ext hαs
  have hmap : ((ggU .PSp n g).D.rootGroup β').map α.toMonoidHom =
      ((ggU .PSp n g).D.rootGroup β').map (MulAut.conj sG).toMonoidHom := by
    change (CFSG.LieType.Universal.Symplectic.rootGroup n (GaloisField 2 g) β').map
        α.toMonoidHom =
      (CFSG.LieType.Universal.Symplectic.rootGroup n (GaloisField 2 g) β').map
        (MulAut.conj s).toMonoidHom
    rw [hhom]
    erw [← Subgroup.map_map]
    erw [CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup]
    rfl
  have hmapneg : ((ggU .PSp n g).D.rootGroup (-β')).map α.toMonoidHom =
      ((ggU .PSp n g).D.rootGroup (-β')).map (MulAut.conj sG).toMonoidHom := by
    change (CFSG.LieType.Universal.Symplectic.rootGroup n (GaloisField 2 g) (-β')).map
        α.toMonoidHom =
      (CFSG.LieType.Universal.Symplectic.rootGroup n (GaloisField 2 g) (-β')).map
        (MulAut.conj s).toMonoidHom
    rw [hhom]
    erw [← Subgroup.map_map]
    erw [CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup]
    rfl
  refine ⟨β', ⟨hβ', Or.inl hlong⟩, α u' * sG, ?_, ?_⟩
  · simpa only [ggRootSub] using
      (irg_map_conj_subgroup_mulAut
        (QuotientGroup.mk' (Subgroup.center (ggU .PSp n g).K)) θ α hα
        (A := (ggU .PSp n g).D.rootGroup β') (B := (ggU .PSp n g).D.rootGroup β')
        (t := sG) (u := u') hmap)
  · simpa only [ggRootSub] using
      (irg_map_conj_subgroup_mulAut
        (QuotientGroup.mk' (Subgroup.center (ggU .PSp n g).K)) θ α hα
        (A := (ggU .PSp n g).D.rootGroup (-β')) (B := (ggU .PSp n g).D.rootGroup (-β'))
        (t := sG) (u := u') hmapneg)

end CFSG.StandardType.RCKRP
