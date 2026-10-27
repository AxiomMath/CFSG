module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftsPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockExt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.TableCRes
open CFSG.Open (StatedLieTag)

section Genuine


theorem rckClassicalModelID_PSU {X : Type} [Group X] [Finite X] {n g : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {p : ℕ} {A B₁ D J K : Subgroup X} {d e : X}
    (hH : PSULiftHyp n g ψ p A) (hB₁A : B₁ ≤ A) (hDB₁ : D ≤ B₁) (hDcard : Nat.card D = p ^ 2)
    (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hp4 : p ^ 4 ≤ Nat.card B₁) (heD : e ∈ D)
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {e})) (hJK : J ≤ K) (hKJ : K ≠ J)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X)) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    RCKClassicalModelID K B₁ := by
  classical
  have heA : e ∈ A := hB₁A (hDB₁ heD)
  have hKq : IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hK.2.2
  obtain ⟨s, hsU', hslift, hodd, ε, hε, ⟨e', he', he'ε, hdich⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSU hH.prime hH.ne_two (hH.pow_eq_one heA) hH.three_le ψ rfl hH.ker
      (hH.norm heA) (hH.diag e heA) hK
  have hsU : s ∈ GUsub (PSUσ g) n := mem_GUsub_iff.mpr hsU'
  have hJ'G : J' ≤ glBlockCentralizer (PSUj n g) {s} ε := by
    refine hJ'comp.1.trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  have hperf : ⁅J', J'⁆ = J' := LayerFacts.ggCommutator_eq_of_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'comp.2.2)
  have hJ'Gt : J'.map (PSUj n g) ≤
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
        GUsub (PSUσ g) n :=
    (Subgroup.map_mono hJ'G).trans (rckPSU_blockGroup_map_normal s ε).1
  rcases rckBlockModel_PSU hsU hodd hε he' he'ε hdich hJ'comp with
    ⟨t, m, g', κ, ht, hg, hκ⟩ | ⟨m, Q, E, _, _, _, hm, hE, ⟨Φ⟩⟩
  · refine rckClassicalModelID_of_blockExt hH.ker (Subgroup.subtype_injective _) hJ'Gt hκ
      ht hg hJ'map ?_
    intro b hb
    obtain ⟨tb, htbU, htb⟩ := hH.exists_lift (hB₁A hb)
    have hts : Commute tb s := hH.commute_lifts (hB₁A hb) heA htb hslift
    exact rckLiftToBlock_PSU hH.ker hε hJ'G hperf htbU htb hts (hJ'map ▸ hB₁K hb)
  · exact absurd (rckEq_of_block_unitarySmall_PSU hH hB₁A hDcard hB₁J hp4 hJK hKq hdD hJ heA
      hslift hε hJ'G hJ'map hm hE Φ) hKJ

theorem rckClassicalCompModelAt_PSU : RCKClassicalCompModelAt .PSU := by
  intro X _ _ n f ψ p G₀ A B₁ D J L K e h hKJ hID
  have hf : 1 ≤ f := h.1.1.1.2.1
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hH : PSULiftHyp n g ψ p A := rckPSULiftHyp_of_compConfig h hID
  unfold RCKCompConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, heD, he1, hKcomp, hJK, hOddK⟩
  obtain ⟨hB₁K, d, hdD, -, hJd⟩ := le_normalizer_and_exists_isComponentOf_of_plane hp hAel hB1A
    hDB1 hDcard hAnorm hB1J hJcomp heD he1 hKcomp hJK
  have hrange : ψ.range = G₀ := hGG.2.1.1
  rw [← hrange] at hKcomp
  exact rckClassicalModelID_PSU hH hB1A hDB1 hDcard hB1Jc hp4 heD hKcomp hJK hKJ hB₁K
    hdD hJd

end Genuine

end CFSG.StandardType.RCKRP
