module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs

import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRoot
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentCorank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTorus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin

private theorem exists_lift_mem_ggTorus {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {G : Type} [Group G] {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) {Bs : Subgroup G} (hstd : GGKGPosStdPos (plusDatum n K hn) ψ Bs)
    (hID : ∀ b ∈ Bs, GGPsiInnerDiag (plusDatum n K hn) ψ b) {b : G} (hb : b ∈ Bs) :
    ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, b * ψ u * b⁻¹ = ψ (s * u * s⁻¹) := by
  have hker : ψ.ker ≤ Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  obtain ⟨s, hs⟩ := ClassicalPosition.exists_conj_eq_POmegaPlus n K hn ψ hker (hID b hb)
  refine jcore_inner_torus _ hψ hstd hb ⟨ψ s, ⟨s, rfl⟩, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun _ ⟨u, hu⟩ => ?_
  rw [← hu]
  have e := hs u
  rw [map_mul, map_mul, map_inv] at e
  calc ψ u * (b * ψ s) = b * (b⁻¹ * ψ u * b) * ψ s := by group
    _ = b * ψ s * ψ u := by rw [e]; group

private theorem conj_eq_self_POmegaPlus
    {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {Bs D J : Subgroup G} {n f : ℕ} (hn4 : 4 ≤ n)
    {ψ : (ggU .POmegaPlus n f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    (hstd : GGKGPosStdPos (ggU .POmegaPlus n f).D ψ Bs)
    (hID : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ b) (hDBs : D ≤ Bs)
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hKC1 : ∀ β ∈ ggKGCentRoots (ggU .POmegaPlus n f).D ψ D,
      ((ggU .POmegaPlus n f).D.rootGroup β).map ψ ≤ J)
    (hKC2 : ∃ β ∈ ggKGCentRoots (ggU .POmegaPlus n f).D ψ D,
      ∃ β' ∈ ggKGCentRoots (ggU .POmegaPlus n f).D ψ D, β + β' ∈ (ggU .POmegaPlus n f).D.roots)
    (hKC2' : ¬ p ∣ Nat.card (Subgroup.center (ggU .POmegaPlus n f).K) →
      Set.ncard {h : (ggU .POmegaPlus n f).K | h ∈ ggTorus (ggU .POmegaPlus n f).D ∧ h ^ p = 1 ∧
        ∀ β ∈ ggKGCentRoots (ggU .POmegaPlus n f).D ψ D, ∀ z ∈ (ggU .POmegaPlus n f).D.rootGroup β,
          Commute h z} ≤ p)
    {t : G} (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1) (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) (htJ : t ∈ Subgroup.centralizer (J : Set G)) :
    ∀ k, t * ψ k * t⁻¹ = ψ k := by
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hstd hID hKC1 hKC2 hKC2' htN
  have hcen := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := GaloisField 2 f) hn
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcen.le
  exact conj_eq_self_of_kgc hn hn4 hp hψ (fun d hd => hBp d (hDBs hd))
    (fun d hd => exists_lift_mem_ggTorus hn hψ hstd hID (hDBs hd))
    (fun β hβ hβC => hKC1 β ⟨hβ, hβC⟩) hKC2
    (hKC2' (by rw [hcen, Subgroup.card_bot]; exact hp.not_dvd_one)) ht2 htN htD htJ

end CFSG.StandardType.KGCentOm

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.StandardType.KGCentOm

theorem ggKGCentTagStmt_POmegaPlus
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput) : GGKGCentTagStmt .POmegaPlus := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ hr X hX n f ψ hloc hstd t ht htN htD htJ
  obtain ⟨r, hrA, hrefl⟩ := hr
  have hrange : ψ.range = X := hloc.2.1.2.1
  have key := conj_eq_self_POmegaPlus hloc.1.1 hloc.1.2.2.1.2.2 hloc.2.1.1 hstd hloc.2.2.2.1
    (hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1) hloc.2.2.1.1.2
    (fun β hβ => ggKGCent_rootGroup_le ha₀ hL hcfg hrA hrefl hX hloc hstd hβ)
    (ggKGCent_exists_root_add ha₀ hL hcfg hrA hrefl hX hloc hstd)
    (ggKGCent_card_torus_le ha₀ hL hcfg hrA hrefl hX hloc hstd) ht (hrange ▸ htN) htD htJ
  intro g hg h _
  obtain ⟨k, rfl⟩ : g ∈ ψ.range := hrange ▸ hg
  rw [key k, mul_inv_cancel]
  exact Commute.one_left h

end CFSG.StandardType

end
