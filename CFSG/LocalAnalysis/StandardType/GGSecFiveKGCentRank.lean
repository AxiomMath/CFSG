module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPosDef
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRootComm
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPerf
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentSpan
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRoot
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
import CFSG.LocalAnalysis.StandardType.GGRankOneTags
import CFSG.LocalAnalysis.StandardType.GGStdPosRankCard
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS

private theorem exists_root_add_core {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hext : SteinbergExtras Δ nn H) (hdiv : Δ.divisible = ∅)
    (hpd : (Δ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {F : Type*} [Field F] [CharP F 2]
    {xp : (Fin Δ.rank → ℤ) → F → K} {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hE : ChevalleyExtras Δ F xp C O)
    (hlin : ∀ h ∈ ggTorus Δ, ∀ i : Fin Δ.rank, ∃ χ : F, ∀ c : F,
      h * xp (Pi.single i 1) c * h⁻¹ = xp (Pi.single i 1) (χ * c))
    {G : Type*} [Group G] [Finite G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : p.Prime) {Bs D J : Subgroup G} (hstd : GGKGPosStdPos Δ ψ Bs)
    (hpow : ∀ b ∈ Bs, b ^ p = 1) (hDB : D ≤ Bs)
    (hBJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hcard : p * Nat.card D < Nat.card Bs)
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hJR : J ≤ (ggKGCentRootSpan Δ ψ D).map ψ)
    (hKC1 : ∀ β ∈ ggKGCentRoots Δ ψ D, (Δ.rootGroup β).map ψ ≤ J) :
    ∃ β ∈ ggKGCentRoots Δ ψ D, ∃ β' ∈ ggKGCentRoots Δ ψ D, β + β' ∈ Δ.roots := by
  by_contra hno
  have hR : ∀ v, v ∈ roots Δ.isFiniteType ∅ → v ∈ Δ.roots := fun v hv => by
    show v ∈ roots Δ.isFiniteType Δ.divisible
    rw [hdiv]
    exact hv
  obtain ⟨β, hβ⟩ : (ggKGCentRoots Δ ψ D).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    have hbot : ggKGCentRootSpan Δ ψ D = ⊥ := by simp [ggKGCentRootSpan, h0]
    rw [hbot, Subgroup.map_bot, le_bot_iff] at hJR
    rw [hJR, Subgroup.card_bot] at hpJ
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpJ)
  have hneg : ∀ γ ∈ ggKGCentRoots Δ ψ D, -γ ∈ ggKGCentRoots Δ ψ D := by
    rintro γ ⟨hγr, hγc⟩
    refine ⟨OfCartan.neg_mem_roots Δ.isFiniteType hγr, fun z hz => ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : ∀ z' ∈ Δ.rootGroup γ, d * ψ z' * d⁻¹ = ψ z' := fun z' hz' => by
      rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (hγc hz')) d hd,
        mul_inv_cancel_right]
    have e := ggKGCent_fix_neg hct hdiv hE ψ hker hstd hγr (hDB hd) h1 z hz
    calc d * ψ z = d * ψ z * d⁻¹ * d := by group
      _ = ψ z * d := by rw [e]
  obtain ⟨w, i, hβw⟩ : ∃ (w : (coxeterMatrix Δ.isFiniteType).Group) (i : Fin Δ.rank),
      β = weylAction Δ.isFiniteType w (Pi.single i 1) := by
    rcases (show β ∈ roots Δ.isFiniteType ∅ from hdiv ▸ hβ.1) with ⟨w, i, h⟩ | ⟨w, i, hi, -⟩
    · exact ⟨w, i, h⟩
    · simp at hi
  have horth : ∀ γ ∈ ggKGCentRoots Δ ψ D, γ ≠ β → γ ≠ -β → cartanPair Δ.cartan β γ = 0 := by
    intro γ hγ h1 h2
    have hγ' : γ ∈ roots Δ.isFiniteType ∅ := hdiv ▸ hγ.1
    rcases ggKGCent_root_trichotomy Δ.isFiniteType hpd w i hγ' (by rwa [← hβw])
      (by rwa [← hβw]) with h | h | h
    · rw [← hβw] at h
      exact (hno ⟨β, hβ, γ, hγ, hR _ h⟩).elim
    · rw [← hβw, sub_eq_add_neg] at h
      exact (hno ⟨β, hβ, -γ, hneg γ hγ, hR _ h⟩).elim
    · rwa [← hβw] at h
  set T : Subgroup K := Δ.rootGroup β ⊔ Δ.rootGroup (-β) with hT
  have hRT : ggKGCentRootSpan Δ ψ D ≤ Subgroup.normalizer (T : Set K) := by
    refine iSup₂_le fun γ hγ => ?_
    by_cases h1 : γ = β
    · rw [h1]
      exact le_sup_left.trans Subgroup.le_normalizer
    by_cases h2 : γ = -β
    · rw [h2]
      exact le_sup_right.trans Subgroup.le_normalizer
    obtain ⟨hc1, hc2⟩ := ggKGCent_rootGroup_commute hext hdiv hpd hβ.1 hγ.1 (horth γ hγ h1 h2)
    refine le_trans (fun z hz => ?_) (Subgroup.centralizer_le_normalizer _)
    have hTz : T ≤ Subgroup.centralizer {z} := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hc1 a ha z hz))
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hc2 a ha z hz))
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
  have hJN : J ≤ Subgroup.normalizer ((T.map ψ : Subgroup G) : Set G) :=
    hJR.trans ((Subgroup.map_mono hRT).trans (Subgroup.le_normalizer_map ψ))
  have hTJ : T.map ψ ≤ J := by
    rw [hT, Subgroup.map_sup]
    exact sup_le (hKC1 β hβ) (hKC1 (-β) (hneg β hβ))
  obtain ⟨a, ha, a', ha', hne⟩ := ggKGCent_exists_not_commute hct hdiv hE ψ hker hβ.1
  have hJT : J ≤ T.map ψ := ggKGCent_le_of_le_normalizer hJ hTJ hJN
    (Subgroup.mem_map_of_mem ψ (Subgroup.mem_sup_left ha))
    (Subgroup.mem_map_of_mem ψ (Subgroup.mem_sup_right ha')) hne
  have hle : Bs ⊓ Subgroup.centralizer ((Δ.rootGroup β).map ψ : Set G) ≤ D := by
    intro b hb
    obtain ⟨hbB, hbc⟩ := Subgroup.mem_inf.mp hb
    have h1 : ∀ z ∈ Δ.rootGroup β, b * ψ z * b⁻¹ = ψ z := fun z hz => by
      rw [← Subgroup.mem_centralizer_iff.mp hbc (ψ z) (Subgroup.mem_map_of_mem ψ hz),
        mul_inv_cancel_right]
    have h2 := ggKGCent_fix_neg hct hdiv hE ψ hker hstd hβ.1 hbB h1
    have hTc : T.map ψ ≤ Subgroup.centralizer {b} := by
      rw [hT, Subgroup.map_sup]
      refine sup_le ?_ ?_ <;> rintro _ ⟨z, hz, rfl⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
      · calc ψ z * b = b * ψ z * b⁻¹ * b := by rw [h1 z hz]
          _ = b * ψ z := by group
      · calc ψ z * b = b * ψ z * b⁻¹ * b := by rw [h2 z hz]
          _ = b * ψ z := by group
    refine hBJ (Subgroup.mem_inf.mpr ⟨hbB, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTc (hJT hj))
  have h3 := (ggKGCent_card_le_mul hct hdiv hE hlin ψ hker hp.ne_zero hstd hpow hβ.1).trans
    (Nat.mul_le_mul_left p (Subgroup.card_le_of_le hle))
  exact absurd hcard (not_lt.mpr h3)

theorem ggKGCent_exists_root_add
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs) :
    ∃ β ∈ ggKGCentRoots (ggU tg n f).D ψ D, ∃ β' ∈ ggKGCentRoots (ggU tg n f).D ψ D,
      β + β' ∈ (ggU tg n f).D.roots := by
  obtain ⟨hp, -, hadm, hrank⟩ := hloc.1
  obtain ⟨hker, -, ht, -⟩ := hloc.2.1
  obtain ⟨hdiv, ⟨nn, H, hct, hext, -⟩, -⟩ := ggStdPos_bruhatData (f := f) hrank ht
  obtain ⟨xp, C, O, hE, hlin⟩ := ggRankOneModel_of_tag ht hadm hrank
  have hBB : Bs = B := ggKGCent_bstar_eq hcfg.1.1 hloc hstd
  have hpJ := SecFiveL1Odd.p_dvd_card_J ha₀ hcfg hr hrefl
  have hpre := hcfg.1.1.2.2.1
  have hBm : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.1.1.2.2.2.2.2.2.1.1.2.1
  have h4 := Nat.pow_le_pow_right hp.pos (ggKGPos_prime_rank_ge_four hcfg).2.2
  refine exists_root_add_core hct hext hdiv (ggU_cartan_posDef (f := f) hrank ht) hE hlin ψ hker hp
    hstd hloc.2.2.1.1.2 (SecFiveL1Odd.le_bstar hcfg) ?_ ?_ hpre.2.2.2.2.2.1.2.2 hpJ
    (ggKGCent_le_rootSpan ha₀ hL hcfg hpJ hX hloc hstd)
    fun β hβ => ggKGCent_rootGroup_le ha₀ hL hcfg hr hrefl hX hloc hstd hβ
  · rw [hpre.2.2.2.2.2.2, hBB]
  · rw [hpre.2.2.1, hBB, hBm]
    calc p * p ^ 2 = p ^ 3 := by ring
      _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      _ ≤ _ := h4

end CFSG.StandardType

end
