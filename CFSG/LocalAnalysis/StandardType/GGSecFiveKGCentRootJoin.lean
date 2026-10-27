module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
public import CFSG.Timmesfeld.ARS.CaseEWeight
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentCoroot
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentConj
import CFSG.LieType.Steinberg.OfCartan
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.Timmesfeld.ARS

theorem ggKGCent_zpow_ne_one {M : Type*} [Group M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : M} (hs : orderOf s = p) {m : ℤ} (hm0 : m ≠ 0) (hm1 : -2 ≤ m)
    (hm2 : m ≤ 2) : s ^ m ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [hs] at hc
  have h3 : (3 : ℤ) ≤ p := by
    have := hp.two_le
    have : p ≠ 2 := hp2
    omega
  rcases lt_trichotomy c 0 with hc0 | rfl | hc0
  · nlinarith
  · exact hm0 (by rw [hc, mul_zero])
  · nlinarith

theorem ggKGCent_eq_one_of_psi {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K} {F : Type*} [Field F]
    {xp : (Fin Δ.rank → ℤ) → F → K} {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hE : ChevalleyExtras Δ F xp C O) (hdiv : Δ.divisible = ∅)
    (hsymm : ∀ i j, Δ.cartan i j = Δ.cartan j i) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {s₀ : Fˣ} (hs₀ : s₀ ^ (2 : ℤ) ≠ 1)
    {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ Δ.roots) {y : K} (hy : y ∈ Δ.rootGroup γ) (hψ : ψ y = 1) :
    y = 1 := by
  obtain ⟨t, -, -, hact⟩ := ggKGCent_exists_coroot hct hE hdiv hsymm hγ
  have hyc := Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hψ)) (t s₀)
  have hfix : t s₀ * y * (t s₀)⁻¹ = y := by rw [hyc, mul_inv_cancel_right]
  have hγγ : cartanPair Δ.cartan γ γ = 2 :=
    cartanForm_eq_two Δ.isFiniteType hsymm (hdiv ▸ hγ)
  rcases (hact s₀ γ hγ y hy).2 hfix with h | h
  · exact absurd (hγγ ▸ h) hs₀
  · exact h

theorem ggKGCent_neg_mem {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {xp : (Fin Δ.rank → ℤ) → F → K} {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hE : ChevalleyExtras Δ F xp C O) (hdiv : Δ.divisible = ∅) {G : Type*} [Group G]
    (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs D J : Subgroup G}
    (hstd : GGKGPosStdPos Δ ψ Bs) (hDB : D ≤ Bs)
    (hNJ : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (J : Set G))
    {δ : Fin Δ.rank → ℤ} (hδ : δ ∈ ggKGCentRoots Δ ψ D) (hδJ : (Δ.rootGroup δ).map ψ ≤ J) :
    -δ ∈ ggKGCentRoots Δ ψ D ∧ (Δ.rootGroup (-δ)).map ψ ≤ J := by
  have hneg : Δ.rootGroup (-δ) ≤ (Subgroup.centralizer (D : Set G)).comap ψ := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : ∀ z ∈ Δ.rootGroup δ, d * ψ z * d⁻¹ = ψ z := fun z hz => by
      rw [Subgroup.mem_centralizer_iff.mp (hδ.2 hz) d hd, mul_inv_cancel_right]
    have h2 := ggKGCent_fix_neg hct hdiv hE ψ hker hstd hδ.1 (hDB hd) h1 z hz
    calc d * ψ z = d * ψ z * d⁻¹ * d := by group
      _ = ψ z * d := by rw [h2]
  refine ⟨⟨OfCartan.neg_mem_roots Δ.isFiniteType hδ.1, hneg⟩, ?_⟩
  obtain ⟨N, hN, hNz⟩ := ggKGCent_exists_weyl hct hdiv hδ.1
  have hψN : (ψ N)⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
    inv_mem (hNJ (sup_le hδ.2 hneg hN))
  rintro _ ⟨z, hz, rfl⟩
  have e : ψ z = (ψ N)⁻¹ * ψ (N * z * N⁻¹) * (ψ N)⁻¹⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hψN _).mp (hδJ ⟨_, hNz z hz, rfl⟩)

theorem ggKGCent_join {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K} {F : Type*} [Field F]
    {xp : (Fin Δ.rank → ℤ) → F → K} {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hE : ChevalleyExtras Δ F xp C O) (hdiv : Δ.divisible = ∅)
    (hsymm : ∀ i j, Δ.cartan i j = Δ.cartan j i) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {D J : Subgroup G}
    (hNJ : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (J : Set G))
    {s₀ : Fˣ} (hs₀ : s₀ ^ (2 : ℤ) ≠ 1)
    (htr : ∀ γ ∈ Δ.roots, ∀ y ∈ Δ.rootGroup γ, ψ y ∈ J → ψ y ≠ 1 → (Δ.rootGroup γ).map ψ ≤ J)
    {δ : Fin Δ.rank → ℤ} (hδ : δ ∈ Δ.roots) (hδJ : (Δ.rootGroup δ).map ψ ≤ J)
    (hδJ' : (Δ.rootGroup (-δ)).map ψ ≤ J) {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ ggKGCentRoots Δ ψ D)
    (hpair : s₀ ^ cartanPair Δ.cartan δ γ ≠ 1) : (Δ.rootGroup γ).map ψ ≤ J := by
  obtain ⟨t, htT, htR, hact⟩ := ggKGCent_exists_coroot hct hE hdiv hsymm hδ
  have htJ : ψ (t s₀) ∈ J := by
    have hle : (Δ.rootGroup δ ⊔ Δ.rootGroup (-δ)).map ψ ≤ J := by
      rw [Subgroup.map_sup]
      exact sup_le hδJ hδJ'
    exact hle (Subgroup.mem_map_of_mem ψ (htR s₀))
  have hpar := hE.param γ hγ.1
  have hz : xp γ 1 ∈ Δ.rootGroup γ := (hpar.1 _).mpr ⟨1, rfl⟩
  have hz1 : xp γ 1 ≠ 1 := by
    have h0 := hpar.2.1 0 0
    rw [add_zero] at h0
    exact fun h => one_ne_zero (hpar.2.2 (h.trans (left_eq_mul.mp h0).symm))
  have htN : t s₀ ∈ Subgroup.normalizer (Δ.rootGroup γ : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (htT s₀) γ) hγ.1
  have hy : t s₀ * xp γ 1 * (t s₀)⁻¹ * (xp γ 1)⁻¹ ∈ Δ.rootGroup γ :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp htN _).mp hz) (inv_mem hz)
  have hy1 : t s₀ * xp γ 1 * (t s₀)⁻¹ * (xp γ 1)⁻¹ ≠ 1 := fun h =>
    ((hact s₀ γ hγ.1 _ hz).2 (mul_inv_eq_one.mp h)).elim hpair hz1
  refine htr γ hγ.1 _ hy ?_ fun h => hy1 (ggKGCent_eq_one_of_psi hct hE hdiv hsymm ψ hker hs₀
    hγ.1 hy h)
  have e : ψ (t s₀ * xp γ 1 * (t s₀)⁻¹ * (xp γ 1)⁻¹) =
      ψ (t s₀) * (ψ (xp γ 1) * (ψ (t s₀))⁻¹ * (ψ (xp γ 1))⁻¹) := by
    simp only [map_mul, map_inv]
    group
  rw [e]
  exact J.mul_mem htJ ((Subgroup.mem_normalizer_iff.mp (hNJ (hγ.2 hz)) _).mp (J.inv_mem htJ))

end CFSG.StandardType

end
