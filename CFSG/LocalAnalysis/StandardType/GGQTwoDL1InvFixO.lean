module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.LieType.ChevTwo
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def QTwoDL1OrthModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G)
    (Φ : OrthTorus.OrthFrameCore p Bs X), Nat.card Φ.F = 2 → 5 ≤ Φ.r →
      Subgroup.center ↥X = ⊥ →
        ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Q₀ : (ι → ZMod 2) → ZMod 2)
          (_ : ↥X ≃* ↥(StatedOmega Q₀)),
          GoodQ Q₀ ∧ OmegaTwoAutInduced Q₀ ∧ Fintype.card ι = 2 * Φ.r

private theorem p9uFO_card_pi (p r : ℕ) :
    Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem p9uFO_isElemAbelian_tau {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
    (Δ : OrthTorus.TBJOmData Q p A r) : IsElemAbelian p A := by
  rw [← Δ.τ_range]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hf, ← hg]
    rw [← map_mul, ← map_mul]
    exact congrArg Δ.τ (mul_comm f g)
  · obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hx
    rw [← hf, ← map_pow]
    have hf' : f ^ p = 1 := by
      funext i
      apply Multiplicative.toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, ZMod.natCast_self,
        zero_mul]
    rw [hf', map_one]

private theorem p9uFO_card_A {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
    (Δ : OrthTorus.TBJOmData Q p A r) : Nat.card ↥A = p ^ r := by
  have h : Nat.card (Fin r → Multiplicative (ZMod p)) = Nat.card ↥Δ.τ.range :=
    Nat.card_congr (Equiv.ofInjective Δ.τ Δ.τ_inj)
  rw [← Δ.τ_range, ← h]
  exact p9uFO_card_pi p r

theorem qtwoDL1_invFix_orth (hmod : QTwoDL1OrthModel) {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {Bs X : Subgroup G} (Φ : OrthTorus.OrthFrameCore p Bs X)
    (hF : Nat.card Φ.F = 2) (h5 : 5 ≤ Φ.r)
    (hZ : Subgroup.center ↥X = ⊥) {t : G} (htC : t ∈ Subgroup.centralizer (Bs : Set G))
    (htN : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.centralizer (X : Set G) := by
  classical
  obtain ⟨ι, instFι, instDι, Q₀, e, hQ, hind, hcardι⟩ := hmod G p Bs X Φ hF h5 hZ
  letI := instFι
  letI := instDι
  have hp3 : p = 3 := by
    have h : p ∣ 3 := by
      have := Φ.hpq
      rw [hF] at this
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  let E : Subgroup G := (Φ.A.subgroupOf (orthDerived Φ.Q)).map Φ.ψ
  have hEX : E ≤ X := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
    exact (le_of_eq Φ.hrange) (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hcardA : Nat.card ↥Φ.A = 3 ^ Φ.r := by
    rw [← hp3]
    exact p9uFO_card_A Φ.Δ
  have hcardE : Nat.card E = 3 ^ Φ.r := by
    rw [Subgroup.card_map_of_injective Φ.hinj]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Φ.hA).toEquiv]
    exact hcardA
  have hE3 : IsElemAbelian 3 E := by
    have hAe : IsElemAbelian p Φ.A := p9uFO_isElemAbelian_tau Φ.Δ
    have hA3 : IsElemAbelian 3 Φ.A := by
      refine ⟨hAe.1, fun x hx => ?_⟩
      rw [← hp3]
      exact hAe.2 x hx
    exact (hA3.subgroupOf (orthDerived Φ.Q)).map Φ.ψ
  have hev : Even (Fintype.card ι) := hcardι ▸ even_two_mul Φ.r
  have hdiv : Fintype.card ι / 2 = Φ.r :=
    hcardι ▸ (by omega : 2 * Φ.r / 2 = Φ.r)
  have hcard3 : 3 ^ (Fintype.card ι / 2) ≤ Nat.card E := by
    simp [hdiv, hcardE]
  let T : Subgroup G := Subgroup.zpowers t
  have hT2 : IsPGroup 2 T := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    change Nat.card ↥(Subgroup.zpowers t) ∣ 2 ^ 1
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr ht2
  have hTN : T ≤ Subgroup.normalizer (X : Set G) := by
    change Subgroup.zpowers t ≤ Subgroup.normalizer (X : Set G)
    exact Subgroup.zpowers_le.mpr htN
  have hET : E ≤ Subgroup.normalizer (T : Set G) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, hb⟩ := Φ.hβsurj _ (Subgroup.mem_subgroupOf.mp hx)
    have hb' : Φ.β b = x := Subtype.ext hb
    rw [← hb']
    have haX : Φ.ψ (Φ.β b) ∈ X :=
      (le_of_eq Φ.hrange) (MonoidHom.mem_range.mpr ⟨Φ.β b, rfl⟩)
    have hcX : t * Φ.ψ (Φ.β b) * t⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp htN _).mp haX
    have hconj : ∀ y ∈ X,
        t * Φ.ψ (Φ.β b) * t⁻¹ * y * (t * Φ.ψ (Φ.β b) * t⁻¹)⁻¹
          = Φ.ψ (Φ.β b) * y * (Φ.ψ (Φ.β b))⁻¹ := by
      intro y hy
      obtain ⟨y₀, rfl⟩ := MonoidHom.mem_range.mp ((le_of_eq Φ.hrange.symm) hy)
      let z : G := t⁻¹ * Φ.ψ y₀ * t
      have hzX : z ∈ X := by
        dsimp [z]
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) _).mp hy
      obtain ⟨y₁, hy₁⟩ := MonoidHom.mem_range.mp ((le_of_eq Φ.hrange.symm) hzX)
      have hb1 : t * (b : G) * t⁻¹ = (b : G) := by
        have h := Subgroup.mem_centralizer_iff.mp htC (b : G) b.2
        rw [← h]
        group
      have hmid : Φ.ψ (Φ.β b) * z * (Φ.ψ (Φ.β b))⁻¹
          = (b : G) * z * (b : G)⁻¹ := by
        rw [show z = Φ.ψ y₁ from hy₁.symm]
        simpa only [← map_mul, ← map_inv] using Φ.hcompat b y₁
      have hz1 : t * z * t⁻¹ = Φ.ψ y₀ := by
        dsimp [z]
        group
      have hkey : t * ((b : G) * z * (b : G)⁻¹) * t⁻¹
          = (b : G) * Φ.ψ y₀ * (b : G)⁻¹ := by
        calc t * ((b : G) * z * (b : G)⁻¹) * t⁻¹
            = (t * (b : G) * t⁻¹) * (t * z * t⁻¹) * (t * (b : G) * t⁻¹)⁻¹ := by
              group
          _ = (b : G) * Φ.ψ y₀ * (b : G)⁻¹ := by simp only [hb1, hz1]
      calc t * Φ.ψ (Φ.β b) * t⁻¹ * Φ.ψ y₀ * (t * Φ.ψ (Φ.β b) * t⁻¹)⁻¹
            = t * (Φ.ψ (Φ.β b) * z * (Φ.ψ (Φ.β b))⁻¹) * t⁻¹ := by
              dsimp [z]; group
        _ = t * ((b : G) * z * (b : G)⁻¹) * t⁻¹ := by rw [hmid]
        _ = (b : G) * Φ.ψ y₀ * (b : G)⁻¹ := hkey
        _ = Φ.ψ (Φ.β b) * Φ.ψ y₀ * (Φ.ψ (Φ.β b))⁻¹ := by
              simpa only [← map_mul, ← map_inv] using (Φ.hcompat b y₀).symm
    have hcent : t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹
        ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (Φ.ψ (Φ.β b))⁻¹ * y * Φ.ψ (Φ.β b) ∈ X :=
        X.mul_mem (X.mul_mem (X.inv_mem haX) hy) haX
      have h3 : (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) * y
          * (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹)⁻¹ = y := by
        rw [show (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) * y
              * (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹)⁻¹
            = t * Φ.ψ (Φ.β b) * t⁻¹ * ((Φ.ψ (Φ.β b))⁻¹ * y * Φ.ψ (Φ.β b))
              * (t * Φ.ψ (Φ.β b) * t⁻¹)⁻¹ by group]
        rw [hconj _ hy']
        group
      have h3' : (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) * y
          = y * (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) := by
        calc (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) * y
            = (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) * y
              * (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹)⁻¹
              * (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) := by group
          _ = y * (t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹) := by rw [h3]
      exact h3'.symm
    have hmemX : t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹ ∈ X :=
      X.mul_mem hcX (X.inv_mem haX)
    have hcenter : (⟨t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹, hmemX⟩ : ↥X)
        ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent (y : G) y.2)
    have h1 : (⟨t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹, hmemX⟩ : ↥X) = 1 := by
      have := hcenter
      rw [hZ] at this
      exact Subgroup.mem_bot.mp this
    have hca : t * Φ.ψ (Φ.β b) * t⁻¹ * (Φ.ψ (Φ.β b))⁻¹ = 1 :=
      congrArg Subtype.val h1
    have hct : t * Φ.ψ (Φ.β b) * t⁻¹ = Φ.ψ (Φ.β b) := by
      have := congrArg (· * Φ.ψ (Φ.β b)) hca
      simpa using this
    have hcomm : Commute (Φ.ψ (Φ.β b)) t := by
      show Φ.ψ (Φ.β b) * t = t * Φ.ψ (Φ.β b)
      have hta : t * Φ.ψ (Φ.β b) = Φ.ψ (Φ.β b) * t := by
        calc t * Φ.ψ (Φ.β b)
            = (t * Φ.ψ (Φ.β b) * t⁻¹) * t := by group
          _ = Φ.ψ (Φ.β b) * t := by rw [hct]
      exact hta.symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : Φ.ψ (Φ.β b) * t ^ k * (Φ.ψ (Φ.β b))⁻¹ = t ^ k := by
        rw [(hcomm.zpow_right k).eq]
        group
      rw [hk]
      exact Subgroup.zpow_mem (Subgroup.zpowers t) (Subgroup.mem_zpowers t) k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hy' : y = (Φ.ψ (Φ.β b))⁻¹ * t ^ k * Φ.ψ (Φ.β b) := by
        rw [hk]
        group
      rw [hy']
      have hk' : (Φ.ψ (Φ.β b))⁻¹ * t ^ k * Φ.ψ (Φ.β b) = t ^ k := by
        rw [((Commute.inv_left_iff.mpr hcomm).zpow_right k).eq]
        group
      rw [hk']
      exact Subgroup.zpow_mem (Subgroup.zpowers t) (Subgroup.mem_zpowers t) k
  have hmain := CFSG.StandardType.FrameRoute.le_centralizer_of_goodQ (L := X) (E := E) (T := T)
    hQ hind hev e hZ hEX hE3 hcard3 hT2 hTN hET
  exact hmain (Subgroup.mem_zpowers t)

end CFSG.StandardType.QTwo

end
