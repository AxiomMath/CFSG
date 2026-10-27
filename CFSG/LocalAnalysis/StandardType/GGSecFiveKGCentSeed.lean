module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentSpan
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
import CFSG.LocalAnalysis.StandardType.GGStdPosTrans
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

theorem ggKGCent_exists_conj_ne (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ b ∈ Bs, b ^ p = 1) {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs)
    (hrefl : GGIsReflection p r) :
    p ∣ Nat.card J ∧ ∃ e ∈ J ⊓ Bs, ∃ j ∈ J, j * e * j⁻¹ ≠ e := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgJ, -, hrg⟩ := mem_ggAutomizer_iff.mp hr
  obtain ⟨hr2, hcard⟩ := hrefl
  have hrr : ∀ b : ↥Bs, r (r b) = b := fun b => by
    rw [← MulAut.mul_apply, ← pow_two, hr2, MulAut.one_apply]
  obtain ⟨b, hb⟩ : ∃ b : ↥Bs, r b ≠ b := by
    by_contra! h
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv h)] at hcard
    exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans (mul_one _).symm))
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    (SecFiveL1Odd.bstar_le_centralizer hcfg).trans
      (SecFiveL1Odd.centralizer_le_normalizer_J ha₀ hcfg)
  set e : ↥Bs := r b * b⁻¹ with he_def
  have heJ : (e : G) ∈ J := by
    have e1 : (e : G) = g * ((b : G) * g⁻¹ * (b : G)⁻¹) := by
      rw [he_def, Subgroup.coe_mul, Subgroup.coe_inv, hrg b]
      group
    rw [e1]
    exact J.mul_mem hgJ ((Subgroup.mem_normalizer_iff.mp (hBsJ b.2) _).mp (J.inv_mem hgJ))
  have hre : r e = e⁻¹ := by
    rw [he_def, map_mul, map_inv, hrr, mul_inv_rev, inv_inv]
  have hconj : g * (e : G) * g⁻¹ = (e : G)⁻¹ := by
    rw [← hrg e, hre]
    rfl
  have he1 : (e : G) ≠ 1 := fun h => hb (mul_inv_eq_one.mp (Subtype.ext h))
  have hep : (e : G) ^ p = 1 := hexp _ e.2
  refine ⟨?_, (e : G), Subgroup.mem_inf.mpr ⟨heJ, e.2⟩, g, hgJ, fun h => he1 ?_⟩
  · have hdvd := orderOf_dvd_natCard (⟨(e : G), heJ⟩ : ↥J)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hep he1] at hdvd
  ·
    have h2 : (e : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hconj.symm.trans h]
      exact inv_mul_cancel _
    have hg := pow_gcd_eq_one.mpr ⟨h2, hep⟩
    rwa [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one, pow_one] at hg

theorem ggKGCent_rootGroup_le_of_mem {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K} {F : Type*} [Field F] [Finite F]
    [CharP F 2] {xp : (Fin Δ.rank → ℤ) → F → K}
    {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hext : SteinbergExtras Δ nn H) (hBU : BruhatExtras Δ H) (hE : ChevalleyExtras Δ F xp C O)
    (hdiv : Δ.divisible = ∅) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {Bs D J : Subgroup G} (hstd : GGKGPosStdPos Δ ψ Bs)
    (hDB : D ≤ Bs) (hNJ : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (J : Set G))
    {β : Fin Δ.rank → ℤ} (hβ : β ∈ Δ.roots) {y : K} (hy : y ∈ Δ.rootGroup β) (hyJ : ψ y ∈ J)
    (hy1 : ψ y ≠ 1) : (Δ.rootGroup β).map ψ ≤ J := by
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
  rintro _ ⟨z, hz, rfl⟩
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
    exact J.one_mem
  obtain ⟨t, ht, rfl⟩ :=
    ggStdPos_transitive_of_chevalleyExtras hct hE hdiv β hβ y hy z hz hy1' hz1
  have hψt : ψ t ∈ Subgroup.normalizer (J : Set G) :=
    hNJ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hDB)
      (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hstd t ht))
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp hψt _).mp hyJ

theorem ggKGCent_exists_rootGroup_le
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs) :
    ∃ β ∈ ggKGCentRoots (ggU tg n f).D ψ D, ((ggU tg n f).D.rootGroup β).map ψ ≤ J := by
  obtain ⟨⟨hp, hp2, -, hrank⟩, ⟨hker, -, ht, -⟩, ⟨hab, -, -⟩, -, -⟩ := id hloc
  obtain ⟨hpJ, e, ⟨heJ, heB⟩, j, hjJ, hje⟩ := ggKGCent_exists_conj_ne ha₀ hcfg hp hp2 hab.2 hr hrefl
  have hJR := ggKGCent_le_rootSpan ha₀ hL hcfg hpJ hX hloc hstd
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, xp, C, O, hE⟩ := ggStdPos_bruhatData hrank ht
  have hNJ := SecFiveL1Odd.centralizer_le_normalizer_J ha₀ hcfg
  obtain ⟨γ, hγ, z, hz, hez⟩ : ∃ γ ∈ ggKGCentRoots (ggU tg n f).D ψ D,
      ∃ z ∈ (ggU tg n f).D.rootGroup γ, e * ψ z * e⁻¹ ≠ ψ z := by
    by_contra! hcon
    have hle : (ggKGCentRootSpan (ggU tg n f).D ψ D).map ψ ≤ Subgroup.centralizer {e} := by
      rw [Subgroup.map_le_iff_le_comap]
      refine iSup₂_le fun γ hγ z hz => ?_
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      calc ψ z * e = e * ψ z * e⁻¹ * e := by rw [hcon γ hγ z hz]
        _ = e * ψ z := by group
    apply hje
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hle (hJR hjJ)), mul_assoc, mul_inv_cancel,
      mul_one]
  obtain ⟨h, hh, hhz⟩ := hstd e heB γ hγ.1
  have hhN : h ∈ Subgroup.normalizer ((ggU tg n f).D.rootGroup γ : Set (ggU tg n f).K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ.1
  have hψy : ψ (h * z * h⁻¹ * z⁻¹) = e * ψ z * e⁻¹ * (ψ z)⁻¹ := by
    rw [map_mul, map_inv, ← hhz z hz]
  refine ⟨γ, hγ, ggKGCent_rootGroup_le_of_mem hct hext hBU hE hdiv ψ hker hstd
    (SecFiveL1Odd.le_bstar hcfg) hNJ hγ.1
    (mul_mem ((Subgroup.mem_normalizer_iff.mp hhN z).mp hz) (inv_mem hz)) ?_ ?_⟩
  · have e3 : e * ψ z * e⁻¹ * (ψ z)⁻¹ = e * (ψ z * e⁻¹ * (ψ z)⁻¹) := by group
    rw [hψy, e3]
    exact J.mul_mem heJ ((Subgroup.mem_normalizer_iff.mp (hNJ (hγ.2 hz)) _).mp (J.inv_mem heJ))
  · rw [hψy]
    exact fun h1 => hez (mul_inv_eq_one.mp h1)

end CFSG.StandardType

end
