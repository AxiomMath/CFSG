module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockOmega
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockExt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlus
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedOmega)
open scoped commutatorElement

section Genuine


private theorem rckPOmegaPlus_blockTransport {k f : ℕ}
    {s : (ggU .POmegaPlus (k + 3) f).K}
    {ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJ' : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
          {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
          {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    ∃ (ι : (ggU .POmegaPlus (k + 3) f).K ≃*
        ↥(StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (ΦB : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
          {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K) ≃*
        ↥(glBlockCentralizer (StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f))).subtype
          {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε)),
      Subgroup.map ι.toMonoidHom
          (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
            {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
            Subgroup (ggU .POmegaPlus (k + 3) f).K) =
        glBlockCentralizer (StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f))).subtype
          {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε ∧
      IsComponentOf (J'.map ι.toMonoidHom)
        ⁅glBlockCentralizer (StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f))).subtype
            {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε,
          glBlockCentralizer (StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f))).subtype
            {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε⁆ ∧
      J' ≤ (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K) ∧
      ⁅J', J'⁆ = J' := by
  classical
  let F := GaloisField 2 f
  let j : (ggU .POmegaPlus (k + 3) f).K →* GL (Fin (k + 3) ⊕ Fin (k + 3)) F :=
    Spin.spinMatrix (Spin.quadPlus (k + 3) F)
  have hkerj : j.ker = ⊥ :=
    Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)
  have hrangej : j.range = StatedOmega ⇑(Spin.quadPlus (k + 3) F) :=
    CFSG.StandardType.AutOm.range_spinMatrix_plus (K := F) (n := k + 3) (by omega)
  let ι : (ggU .POmegaPlus (k + 3) f).K ≃*
      ↥(StatedOmega ⇑(Spin.quadPlus (k + 3) F)) :=
    CFSG.SectionRank.EvenCover.spinMatrixEquiv hkerj hrangej
  let B : Subgroup (ggU .POmegaPlus (k + 3) f).K := glBlockCentralizer j {j s} ε
  let BΩ : Subgroup ↥(StatedOmega ⇑(Spin.quadPlus (k + 3) F)) :=
    glBlockCentralizer (StatedOmega ⇑(Spin.quadPlus (k + 3) F)).subtype {j s} ε
  have hBmap :
      Subgroup.map ι.toMonoidHom
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) F))
          {Spin.spinMatrix (Spin.quadPlus (k + 3) F) s} ε) =
      glBlockCentralizer (StatedOmega ⇑(Spin.quadPlus (k + 3) F)).subtype
        {Spin.spinMatrix (Spin.quadPlus (k + 3) F) s} ε := by
    change Subgroup.map ι.toMonoidHom B = BΩ
    have hBeq : B = BΩ.comap ι.toMonoidHom := by
      simp only [B, BΩ, glBlockCentralizer, Subgroup.comap_comap]
      congr 1
    rw [hBeq]
    exact Subgroup.map_comap_eq_self_of_surjective ι.surjective BΩ
  have hJ'G : J' ≤ B := hJ'.1.trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂))
  have hJ'Ω : IsComponentOf (J'.map ι.toMonoidHom) ⁅BΩ, BΩ⁆ := by
    have h := CFSG.isComponentOf_map_mulEquiv ι
      ((CFSG.Assembly.isComponentOf_iff_open).1 hJ')
    rw [Subgroup.map_commutator, hBmap] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).2 h
  have hperf : ⁅J', J'⁆ = J' := LayerFacts.ggCommutator_eq_of_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'.2.2)
  exact ⟨ι, (Subgroup.equivMapOfInjective B ι.toMonoidHom ι.injective).trans
    (MulEquiv.subgroupCongr hBmap), hBmap, hJ'Ω, hJ'G, hperf⟩

theorem rckClassicalModelID_POmegaPlus {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 4 ≤ n)
    (hf : 1 ≤ f) {ψ : (ggU .POmegaPlus n f).K →* X} {G₀ : Subgroup X} (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B₁ D J K : Subgroup X} {d e : X} (hB₁ : IsElemAbelian p B₁) (hDB₁ : D ≤ B₁)
    (hDcard : Nat.card D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hp4 : p ^ 4 ≤ Nat.card B₁) (hB₁N : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hID : ∀ b ∈ B₁, GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ b) (heD : e ∈ D)
    (hK : IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e})) (hJK : J ≤ K) (hKJ : K ≠ J)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X)) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    RCKClassicalModelID K B₁ := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have heB₁ : e ∈ B₁ := hDB₁ heD
  have hep : e ^ p = 1 := hB₁.2 e heB₁
  have hB₁e : ∀ b ∈ B₁, Commute b e := fun b hb =>
    congrArg Subtype.val (hB₁.1.is_comm.comm (⟨b, hb⟩ : B₁) (⟨e, heB₁⟩ : B₁))
  have hKq : IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hK.2.2
  obtain ⟨s, hslift, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaPlus hp hp2 hep hf ψ hrange hker (hID e heB₁) hK
  obtain ⟨ι, ΦB, hBmap, hJ'Ω, hJ'G, hperf⟩ :=
    rckPOmegaPlus_blockTransport hJ'comp
  have hb : Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s ∈
      StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f)) := by
    rw [Spin.coe_quadPlus,
      ← Spin.range_spinMatrix_quadPlus (K := GaloisField 2 f) (n := k + 3) (by omega)]
    exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have h8 : 8 ≤ Fintype.card (Fin (k + 3) ⊕ Fin (k + 3)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  rcases rckBlockModel_Omega hf (Spin.quadPlus (k + 3) (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) h8 hb hsodd hε
      hJ'Ω with
    ⟨t, m, g, κ, ht, hg, hκ⟩ | ⟨m, Q, E, hEf, hEfin, hEch, hm, -, ⟨ΦΩ⟩⟩
  · refine rckClassicalModelID_of_blockExt hker ι.injective ?_ hκ ht hg hJ'map ?_
    · rw [← hBmap]; exact Subgroup.map_mono hJ'G
    · intro b hb₁
      obtain ⟨s₁, hs₁B, hs₁N, hs₁conj⟩ :=
        rckLiftToBlock_POmegaPlus (by omega) hker hslift hε hJ'G hperf
          (hp.odd_of_ne_two hp2) (hB₁.2 b hb₁) (hrange ▸ hB₁N hb₁) (hID b hb₁)
          (hB₁e b hb₁) (hJ'map ▸ hB₁K hb₁)
      let s₁' : (ggU .POmegaPlus (k + 3) f).K := s₁
      have hs₁B' : s₁' ∈ glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
          {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε := hs₁B
      have hs₁N' : s₁' ∈ Subgroup.normalizer (J' : Set (ggU .POmegaPlus (k + 3) f).K) := hs₁N
      have hs₁conj' : ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁' * y * s₁'⁻¹) :=
        fun y hy => hs₁conj y hy
      refine ⟨ι s₁', ?_, ?_, ?_⟩
      · rw [← hBmap]; exact Subgroup.mem_map.mpr ⟨s₁', hs₁B', rfl⟩
      · have hNmap : (Subgroup.normalizer (J' : Set (ggU .POmegaPlus (k + 3) f).K)).map
            ι.toMonoidHom = Subgroup.normalizer
              (J'.map ι.toMonoidHom :
                Subgroup ↥(StatedOmega ⇑(Spin.quadPlus (k + 3) (GaloisField 2 f)))) :=
          Subgroup.map_normalizer_eq_of_bijective J' ⟨ι.injective, ι.surjective⟩
        rw [← hNmap]; exact Subgroup.mem_map.mpr ⟨s₁', hs₁N', rfl⟩
      · intro y hy y' _ hconj
        have hyy' : y' = s₁' * y * s₁'⁻¹ := by
          apply ι.injective
          rw [map_mul, map_mul, map_inv]
          exact hconj
        rw [hyy']; exact hs₁conj' y hy
  · letI : Field E := hEf; letI : Finite E := hEfin; letI : CharP E 2 := hEch
    refine absurd (rckEq_of_block_unitarySmall_POmegaPlus (E := E) (m := m) (Q := Q)
      (by omega) hp hp2 hB₁ hDcard hB₁J hp4 hJK hKq hdD hJ hker hslift hε hJ'G hJ'map
      (hrange ▸ hB₁N) (fun b hb => hID b hb) hB₁e hm ?_) hKJ
    exact ΦB.trans ΦΩ

theorem rckClassicalCompModelAt_POmegaPlus : RCKClassicalCompModelAt .POmegaPlus := by
  intro X _ _ n f ψ p G₀ A B₁ D J L K e h hKJ hID
  unfold RCKCompConfig at h
  rcases h with
    ⟨hGG, -, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, -, hB1J, hB1Jc, hp4, -, -, -, -, -,
      hJcompD, -, -, -, -, -, -, heD, he1, hKcomp, hJK, -⟩
  obtain ⟨hB₁K, d, hdD, -, hJd⟩ := le_normalizer_and_exists_isComponentOf_of_plane hp hAel
    hB1A hDB1 hDcard hAnorm hB1J hJcompD heD he1 hKcomp hJK
  exact rckClassicalModelID_POmegaPlus hGG.1.1.2.2 hGG.1.1.2.1 hGG.2.1.1 hGG.2.1.2 hp hp2
    (hAel.mono hB1A) hDB1 hDcard hB1Jc hp4 (hB1A.trans hAnorm) (fun b hb => hID b (hB1A hb))
    heD hKcomp hJK hKJ hB₁K hdD hJd

end Genuine

end CFSG.StandardType.RCKRP
