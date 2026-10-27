module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPerf
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentSpan
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import CFSG.LocalAnalysis.StandardType.GGStdPosRankCard
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

private theorem ncard_le_card_inf {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hext : SteinbergExtras Δ nn H) (hBU : BruhatExtras Δ H) {F : Type*} [Field F] [CharP F 2]
    {xp : (Fin Δ.rank → ℤ) → F → K} {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hE : ChevalleyExtras Δ F xp C O) {G : Type*} [Group G] [Finite G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {Bs D J : Subgroup G} (hstd : GGKGPosStdPos Δ ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJR : J ≤ (ggKGCentRootSpan Δ ψ D).map ψ) :
    Set.ncard {h : K | h ∈ ggTorus Δ ∧ h ^ p = 1 ∧
      ∀ β ∈ ggKGCentRoots Δ ψ D, ∀ z ∈ Δ.rootGroup β, Commute h z} ≤
      Nat.card ↥(D ⊓ ψ.range) := by
  have hmaps : ∀ h ∈ {h : K | h ∈ ggTorus Δ ∧ h ^ p = 1 ∧
      ∀ β ∈ ggKGCentRoots Δ ψ D, ∀ z ∈ Δ.rootGroup β, Commute h z},
      ψ h ∈ ((D ⊓ ψ.range : Subgroup G) : Set G) := by
    intro h hh
    have hRh : ggKGCentRootSpan Δ ψ D ≤ Subgroup.centralizer {h} := iSup₂_le fun β hβ z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hh.2.2 β hβ z hz).symm.eq
    have hJc : ψ h ∈ Subgroup.centralizer (J : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp (hJR hj)
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hRh hr)]
    have hBs : ψ h ∈ Bs := hC3 _ (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hstd h hh.1)
      (by rw [← map_pow, hh.2.1, map_one])
    exact Subgroup.mem_inf.mpr ⟨hBJ (Subgroup.mem_inf.mpr ⟨hBs, hJc⟩), ⟨h, rfl⟩⟩
  have hinj : Set.InjOn ψ {h : K | h ∈ ggTorus Δ ∧ h ^ p = 1 ∧
      ∀ β ∈ ggKGCentRoots Δ ψ D, ∀ z ∈ Δ.rootGroup β, Commute h z} := by
    intro h₁ hh₁ h₂ hh₂ heq
    have hc : h₁⁻¹ * h₂ ∈ Subgroup.center K :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel])
    have hcp : (h₁⁻¹ * h₂) ^ p = 1 := by
      have hcomm : Commute h₁ (h₁⁻¹ * h₂) := Subgroup.mem_center_iff.mp hc h₁
      have e := hcomm.mul_pow p
      rw [mul_inv_cancel_left, hh₂.2.1, hh₁.2.1, one_mul] at e
      exact e.symm
    have hZc : (h₁⁻¹ * h₂) ^ Nat.card (Subgroup.center K) = 1 := by
      have e := congrArg Subtype.val (pow_card_eq_one' (G := Subgroup.center K) (x := ⟨_, hc⟩))
      simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using e
    have h1 := pow_gcd_eq_one.mpr ⟨hcp, hZc⟩
    rw [((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ).gcd_eq_one, pow_one] at h1
    exact inv_mul_eq_one.mp h1
  exact (Set.ncard_le_ncard_of_injOn ψ hmaps hinj (Set.toFinite _)).trans_eq
    (by rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq])

theorem ggKGCent_card_torus_le
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (ggU tg n f).K)) :
    Set.ncard {h : (ggU tg n f).K | h ∈ ggTorus (ggU tg n f).D ∧ h ^ p = 1 ∧
      ∀ β ∈ ggKGCentRoots (ggU tg n f).D ψ D, ∀ z ∈ (ggU tg n f).D.rootGroup β,
        Commute h z} ≤ p := by
  obtain ⟨hp, -, hadm, hrank⟩ := hloc.1
  obtain ⟨hker, hrange, ht, hpq⟩ := hloc.2.1
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, xp, C, O, hE⟩ := ggStdPos_bruhatData (f := f) hrank ht
  have hBB : Bs = B := ggKGCent_bstar_eq hcfg.1.1 hloc hstd
  have hpre := hcfg.1.1.2.2.1
  have hpJ := SecFiveL1Odd.p_dvd_card_J ha₀ hcfg hr hrefl
  have hBJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by rw [hpre.2.2.2.2.2.2, hBB]
  refine (ncard_le_card_inf hct hext hBU hE ψ hker hp hZ hstd hloc.2.2.1.2.2 hBJ
    (ggKGCent_le_rootSpan ha₀ hL hcfg hpJ hX hloc hstd)).trans ?_
  rw [hrange]
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).mp
    (show Nat.card ↥(D ⊓ X) ∣ p ^ 2 by
      rw [← hpre.2.2.1]
      exact Subgroup.card_dvd_of_le inf_le_left)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · rw [hkc]
    exact (Nat.pow_le_pow_right hp.pos (by omega : k ≤ 1)).trans_eq (pow_one p)
  exfalso
  have hDX : D ≤ X := inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
    (by rw [hkc, hpre.2.2.1]; exact Nat.pow_le_pow_right hp.pos hk2))
  obtain ⟨y, hyB, hy1, hyp, hXy, -⟩ := ggKGPos_exists_central_elt hcfg hX
  have hJX := SecFiveL1Odd.J_le hL hcfg hpJ hX
  have hyD : y ∈ D := by
    rw [hpre.2.2.2.2.2.2]
    exact Subgroup.mem_inf.mpr ⟨hyB, Subgroup.mem_centralizer_iff.mpr fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXy (hJX hj))⟩
  have hf : 2 ≤ f := by
    by_contra hf
    have hf1 : f = 1 := by have := hadm.2.1; omega
    rw [hf1] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpq))
  have hcard : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a, ha, hasq⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card _ hcard
  have hK := ggKGCent_commutator_eq_top hct hdiv hE ha hasq
  refine hy1 (ggKGCent_eq_one_of_mem_center hK ψ hker hp hZ (by rw [hrange]; exact hDX hyD)
    (fun g hg => ?_) hyp)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hXy (by rw [← hrange]; exact hg))

end CFSG.StandardType

end
