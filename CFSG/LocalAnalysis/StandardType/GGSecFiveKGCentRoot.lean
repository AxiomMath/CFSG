module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRootJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentSeed
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentSpan
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentCoroot
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRootComm
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPerf
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPosDef
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.Timmesfeld.ARS

private theorem ggKGCent_rootGroup_le_core {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hext : SteinbergExtras Δ nn H) (hBU : BruhatExtras Δ H) (hdiv : Δ.divisible = ∅)
    (hpd : (Δ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {F : Type*} [Field F] [CharP F 2]
    {xp : (Fin Δ.rank → ℤ) → F → K} {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hE : ChevalleyExtras Δ F xp C O) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs D J : Subgroup G} (hstd : GGKGPosStdPos Δ ψ Bs) (hDB : D ≤ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (hNJ : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hJR : J ≤ (ggKGCentRootSpan Δ ψ D).map ψ)
    {s₀ : Fˣ} (hs₀ : orderOf s₀ = p)
    (htr : ∀ γ ∈ Δ.roots, ∀ y ∈ Δ.rootGroup γ, ψ y ∈ J → ψ y ≠ 1 → (Δ.rootGroup γ).map ψ ≤ J)
    {β₀ : Fin Δ.rank → ℤ} (hβ₀ : β₀ ∈ ggKGCentRoots Δ ψ D) (hβ₀J : (Δ.rootGroup β₀).map ψ ≤ J)
    {β : Fin Δ.rank → ℤ} (hβ : β ∈ ggKGCentRoots Δ ψ D) : (Δ.rootGroup β).map ψ ≤ J := by
  have hsymm := cartan_symm_of_posDef hpd
  have hs₂ : s₀ ^ (2 : ℤ) ≠ 1 := ggKGCent_zpow_ne_one hp hp2 hs₀ two_ne_zero (by norm_num) le_rfl
  have hneg := fun δ (hδ : δ ∈ ggKGCentRoots Δ ψ D) (hδJ : (Δ.rootGroup δ).map ψ ≤ J) =>
    ggKGCent_neg_mem hct hE hdiv ψ hker hstd hDB hNJ hδ hδJ
  have horth : ∀ δ ∈ ggKGCentRoots Δ ψ D, (Δ.rootGroup δ).map ψ ≤ J →
      ∀ γ ∈ ggKGCentRoots Δ ψ D, ¬(Δ.rootGroup γ).map ψ ≤ J → cartanPair Δ.cartan δ γ = 0 := by
    intro δ hδ hδJ γ hγ hγJ
    by_contra h0
    obtain ⟨h1, h2⟩ := ggKGCent_cartanPair_bound hdiv hpd hδ.1 hγ.1
    exact hγJ (ggKGCent_join hct hE hdiv hsymm ψ hker hNJ hs₂ htr hδ.1 hδJ (hneg δ hδ hδJ).2 hγ
      (ggKGCent_zpow_ne_one hp hp2 hs₀ h0 h1 h2))
  by_contra hβJ
  set A : Subgroup K := ⨆ (δ) (_ : δ ∈ ggKGCentRoots Δ ψ D ∧ (Δ.rootGroup δ).map ψ ≤ J),
    Δ.rootGroup δ
  have hXA : ∀ δ, δ ∈ ggKGCentRoots Δ ψ D ∧ (Δ.rootGroup δ).map ψ ≤ J → Δ.rootGroup δ ≤ A :=
    fun δ hδ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ ggKGCentRoots Δ ψ D ∧
      (Δ.rootGroup δ).map ψ ≤ J) => Δ.rootGroup δ) δ hδ le_rfl
  have hAJ : A.map ψ ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun δ hδ => Subgroup.map_le_iff_le_comap.mp hδ.2)
  have hRN : ggKGCentRootSpan Δ ψ D ≤ Subgroup.normalizer (A : Set K) := by
    refine iSup₂_le fun γ hγ => ?_
    by_cases hγJ : (Δ.rootGroup γ).map ψ ≤ J
    · exact (hXA γ ⟨hγ, hγJ⟩).trans Subgroup.le_normalizer
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    exact ((ggKGCent_rootGroup_commute hext hdiv hpd hδ.1.1 hγ.1
      (horth δ hδ.1 hδ.2 γ hγ hγJ)).1 a ha b hb).symm
  obtain ⟨a, ha, a', ha', hne⟩ := ggKGCent_exists_not_commute hct hdiv hE ψ hker hβ₀.1
  have hJA : J ≤ A.map ψ := ggKGCent_le_of_le_normalizer hJ hAJ
    (hJR.trans ((Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map ψ)))
    (Subgroup.mem_map_of_mem ψ (hXA β₀ ⟨hβ₀, hβ₀J⟩ ha))
    (Subgroup.mem_map_of_mem ψ (hXA (-β₀) (hneg β₀ hβ₀ hβ₀J) ha')) hne
  obtain ⟨t, htT, -, hact⟩ := ggKGCent_exists_coroot hct hE hdiv hsymm hβ.1
  have htA : A ≤ Subgroup.centralizer {t s₀} := by
    refine iSup₂_le fun δ hδ z hz => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have e := (hact s₀ δ hδ.1.1 z hz).1 (by
      rw [cartanPair_comm hsymm, horth δ hδ.1 hδ.2 β hβ hβJ, zpow_zero])
    calc z * t s₀ = t s₀ * z * (t s₀)⁻¹ * t s₀ := by rw [e]
      _ = t s₀ * z := by group
  have hgJ : ψ (t s₀) ∈ Subgroup.centralizer (J : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    obtain ⟨a, haA, rfl⟩ := hJA hj
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (htA haA)]
  have hgp : ψ (t s₀) ^ p = 1 := by
    rw [← map_pow, ← map_pow, ← hs₀, pow_orderOf_eq_one, map_one, map_one]
  have hgD : ψ (t s₀) ∈ D := hBJ (Subgroup.mem_inf.mpr ⟨hC3 _ (ggStdPos_psi_mem_centralizer hct
    hext hBU hE ψ hker hstd _ (htT s₀)) hgp, hgJ⟩)
  have hpar := hE.param β hβ.1
  have hz : xp β 1 ∈ Δ.rootGroup β := (hpar.1 _).mpr ⟨1, rfl⟩
  have hz1 : xp β 1 ≠ 1 := by
    have h0 := hpar.2.1 0 0
    rw [add_zero] at h0
    exact fun h => one_ne_zero (hpar.2.2 (h.trans (left_eq_mul.mp h0).symm))
  have htN : t s₀ ∈ Subgroup.normalizer (Δ.rootGroup β : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (htT s₀) β) hβ.1
  have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (hβ.2 hz)) _ hgD
  have hy := ggKGCent_eq_one_of_psi hct hE hdiv hsymm ψ hker hs₂ hβ.1
    (mul_mem ((Subgroup.mem_normalizer_iff.mp htN _).mp hz) (inv_mem hz)) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group)
  have hββ : cartanPair Δ.cartan β β = 2 :=
    cartanForm_eq_two Δ.isFiniteType hsymm (show β ∈ roots Δ.isFiniteType ∅ from hdiv ▸ hβ.1)
  rcases (hact s₀ β hβ.1 _ hz).2 (mul_inv_eq_one.mp hy) with h | h
  · exact hs₂ (hββ ▸ h)
  · exact hz1 h

theorem ggKGCent_rootGroup_le
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs)
    {β : Fin (ggU tg n f).D.rank → ℤ} (hβ : β ∈ ggKGCentRoots (ggU tg n f).D ψ D) :
    ((ggU tg n f).D.rootGroup β).map ψ ≤ J := by
  obtain ⟨⟨hp, hp2, hadm, hrank⟩, ⟨hker, -, ht, hpf⟩, ⟨hab, -, hC3⟩, -, -⟩ := id hloc
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, xp, C, O, hE⟩ := ggStdPos_bruhatData (f := f) hrank ht
  have hpre := hcfg.1.1.2.2.1
  have hBB : Bs = B := ggKGCent_bstar_eq hcfg.1.1 hloc hstd
  have hNJ := SecFiveL1Odd.centralizer_le_normalizer_J ha₀ hcfg
  have hDB := SecFiveL1Odd.le_bstar hcfg
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, GaloisField.card 2 f (by have := hadm.2.1; omega)]
  obtain ⟨s₀, hs₀⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p (hcard ▸ hpf)
  obtain ⟨β₀, hβ₀, hβ₀J⟩ := ggKGCent_exists_rootGroup_le ha₀ hL hcfg hr hrefl hX hloc hstd
  exact ggKGCent_rootGroup_le_core hct hext hBU hdiv (ggU_cartan_posDef hrank ht) hE ψ hker
    hp hp2 hstd hDB hC3 (by rw [hpre.2.2.2.2.2.2, hBB]) hNJ hpre.2.2.2.2.2.1.2.2
    (ggKGCent_le_rootSpan ha₀ hL hcfg (ggKGCent_exists_conj_ne ha₀ hcfg hp hp2 hab.2 hr hrefl).1
      hX hloc hstd) hs₀
    (fun γ hγ y hy hyJ hy1 => ggKGCent_rootGroup_le_of_mem hct hext hBU hE hdiv ψ hker hstd hDB
      hNJ hγ hy hyJ hy1) hβ₀ hβ₀J hβ

end CFSG.StandardType

end
