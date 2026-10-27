module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56TorA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private def torusHom (K : Type) [Field K] : Kˣ × Kˣ →* (OmI → Kˣ) where
  toFun p := OmegaEig.torusVals p.1 p.2
  map_one' := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [OmegaEig.torusVals]
  map_mul' p q := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [OmegaEig.torusVals] <;> rw [mul_comm]

private theorem torusHom_injective (K : Type) [Field K] :
    Function.Injective (torusHom K) := by
  intro p q h
  have h0 := congrFun h (Sum.inl 0)
  have h1 := congrFun h (Sum.inl 1)
  simp [torusHom, OmegaEig.torusVals] at h0 h1
  exact Prod.ext h0 h1

private theorem diagGL_injective (K : Type) [Field K] :
    Function.Injective (OmegaEig.diagGL (K := K)) := by
  classical
  intro d d' h
  funext i
  apply Units.ext
  have h' := congrFun (congrArg (fun γ : GL OmI K =>
    ((γ : Matrix OmI OmI K) *ᵥ (Pi.single i 1 : OmI → K))) h) i
  simp only [OmegaEig.diagGL_mulVec] at h'
  simpa using h'

theorem exists_elemAbelian_of_diag {m : ℕ} (hSK : Nat.card S.K = 2 ^ m)
    (hq : (2 ^ m - 1).Prime) (l μ : S.Kˣ) (hlμ : l * μ ≠ 1) :
    ∃ E : Subgroup (MulAut W),
      S.actHom (OmegaEig.diagGL (OmegaEig.diagVals l μ)) ∈ E ∧
      E ≤ S.omega ⊔ Subgroup.zpowers (S.actHom (OmegaEig.diagGL (OmegaEig.diagVals l μ))) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ (2 ^ m - 1) = 1) ∧
      Nat.card E = (2 ^ m - 1) ^ 3 := by
  classical
  let q : ℕ := 2 ^ m - 1
  let d : OmI → S.Kˣ := OmegaEig.diagVals l μ
  let φ : (OmI → S.Kˣ) →* MulAut W := S.actHom.comp OmegaEig.diagGL
  let τ : S.Kˣ × S.Kˣ →* (OmI → S.Kˣ) := torusHom S.K
  let T : Subgroup (OmI → S.Kˣ) := τ.range
  let E₀ : Subgroup (OmI → S.Kˣ) := Subgroup.zpowers d ⊔ T
  let E : Subgroup (MulAut W) := E₀.map φ
  let D : MulAut W := S.actHom (OmegaEig.diagGL (OmegaEig.diagVals l μ))
  have hKq : Nat.card S.Kˣ = q := by
    rw [Nat.card_units, hSK]
  have hφinj : Function.Injective φ :=
    S.actHom_injective.comp (diagGL_injective S.K)
  have hd_ne_one : d ≠ 1 := by
    intro h
    apply hlμ
    have h0 := congrFun h (Sum.inr 0)
    simpa [d, OmegaEig.diagVals] using h0
  have hdq : d ^ q = 1 := by
    funext i
    show (d i) ^ q = 1
    rw [← hKq]
    exact pow_card_eq_one'
  have horderd : orderOf d = q := by
    have hdvd : orderOf d ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hdq
    rcases hq.eq_one_or_self_of_dvd (orderOf d) hdvd with h | h
    · exact absurd h (fun hh => hd_ne_one (orderOf_eq_one_iff.mp hh))
    · exact h
  have hcq : (l * μ) ^ q = 1 := by
    rw [← hKq]
    exact pow_card_eq_one'
  have horderc : orderOf (l * μ) = q := by
    have hdvd : orderOf (l * μ) ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hcq
    rcases hq.eq_one_or_self_of_dvd (orderOf (l * μ)) hdvd with h | h
    · exact absurd h (fun hh => hlμ (orderOf_eq_one_iff.mp hh))
    · exact h
  have hTcard : Nat.card T = q ^ 2 := by
    have hTmap : T = (⊤ : Subgroup (S.Kˣ × S.Kˣ)).map τ :=
      MonoidHom.range_eq_map τ
    rw [hTmap, Subgroup.card_map_of_injective (K := ⊤) (f := τ) (torusHom_injective S.K),
      Subgroup.card_top, Nat.card_prod, hKq]
    ring
  have hdisj : Disjoint (Subgroup.zpowers d) T := by
    rw [Subgroup.disjoint_def]
    intro x hxd hxT
    obtain ⟨n, hn, hdn⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hxd)
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hxT
    have hp' : τ p = d ^ n := hp.trans hdn.symm
    have hα : p.1 = 1 := by
      have h0 := congrFun hp' (Sum.inl 0)
      simpa [τ, torusHom, OmegaEig.torusVals, d, OmegaEig.diagVals] using h0
    have hcn : (l * μ) ^ n = 1 := by
      have h0 := congrFun hp' (Sum.inr 0)
      have h1 : τ p (Sum.inr 0) = 1 := by
        simp [τ, torusHom, OmegaEig.torusVals, hα]
      have h2 : (d ^ n) (Sum.inr 0) = (l * μ) ^ n := by
        simp [d, OmegaEig.diagVals]
      rw [h1, h2] at h0
      exact h0.symm
    have hnlt : n < q := by
      rw [← horderd]
      exact Finset.mem_range.mp hn
    have hdvd : q ∣ n := by
      rw [← horderc]
      exact orderOf_dvd_iff_pow_eq_one.mpr hcn
    have hn0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hnlt
    rw [← hdn, hn0, pow_zero]
  have hT_pow : ∀ y ∈ T, y ^ q = 1 := by
    intro y hy
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← map_pow]
    have hp : p ^ q = 1 := by
      rw [Prod.ext_iff]
      constructor
      · rw [Prod.pow_fst, ← hKq]
        exact pow_card_eq_one'
      · rw [Prod.pow_snd, ← hKq]
        exact pow_card_eq_one'
    rw [hp, map_one]
  have hE0_pow : ∀ y ∈ E₀, y ^ q = 1 := by
    change ∀ y ∈ Subgroup.zpowers d ⊔ T, y ^ q = 1
    rw [Subgroup.forall_mem_sup]
    intro y₁ hy₁ y₂ hy₂
    rw [mul_pow]
    have h1 : y₁ ^ q = 1 := by
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hy₁)
      rw [← pow_mul, mul_comm n q, pow_mul, hdq, one_pow]
    rw [h1, hT_pow y₂ hy₂, one_mul]
  have hcardE0 : Nat.card E₀ = q ^ 3 := by
    let f : Subgroup.zpowers d × T → E₀ := fun p =>
      ⟨(p.1 : OmI → S.Kˣ) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro p p' hp
        have h_eq : (p.1 : OmI → S.Kˣ) * p.2 = (p'.1 : OmI → S.Kˣ) * p'.2 :=
          Subtype.ext_iff.mp hp
        have hkey : (p.1 : OmI → S.Kˣ)⁻¹ * p'.1 =
            p.2 * (p'.2 : OmI → S.Kˣ)⁻¹ := by
          have h1 : (p.1 : OmI → S.Kˣ) * (p.2 * (p'.2 : OmI → S.Kˣ)⁻¹) = p'.1 := by
            rw [← mul_assoc, h_eq, mul_assoc, mul_inv_cancel, mul_one]
          rw [← h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have hmemz : (p.1 : OmI → S.Kˣ)⁻¹ * p'.1 ∈ Subgroup.zpowers d :=
          (Subgroup.zpowers d).mul_mem ((Subgroup.zpowers d).inv_mem p.1.2) p'.1.2
        have hmemT : (p.1 : OmI → S.Kˣ)⁻¹ * p'.1 ∈ T := by
          rw [hkey]
          exact T.mul_mem p.2.2 (T.inv_mem p'.2.2)
        have hone : (p.1 : OmI → S.Kˣ)⁻¹ * p'.1 = 1 :=
          Subgroup.disjoint_def.mp hdisj hmemz hmemT
        have hp1 : (p.1 : OmI → S.Kˣ) = p'.1 := by
          have h : (p.1 : OmI → S.Kˣ)⁻¹ * p'.1 = (p.1 : OmI → S.Kˣ)⁻¹ * p.1 := by
            rw [hone, inv_mul_cancel]
          exact (mul_left_cancel h).symm
        have hp2 : (p.2 : OmI → S.Kˣ) = p'.2 := by
          have h : (p.1 : OmI → S.Kˣ) * p.2 = (p.1 : OmI → S.Kˣ) * p'.2 := by
            rw [h_eq, hp1]
          exact mul_left_cancel h
        exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
      · intro x
        have hx : (x : OmI → S.Kˣ) ∈ Subgroup.zpowers d ⊔ T := x.2
        rw [Subgroup.mem_sup] at hx
        obtain ⟨y, hy, z, hz, hyz⟩ := hx
        exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), Subtype.ext hyz⟩
    have hcard : Nat.card E₀ = Nat.card (Subgroup.zpowers d × T) :=
      (Nat.card_congr (Equiv.ofBijective f hbij)).symm
    rw [hcard, Nat.card_prod, Nat.card_zpowers, horderd, hTcard]
    ring
  have hE0_le : E₀ ≤ (S.omega ⊔ Subgroup.zpowers D).comap φ := by
    intro y hy
    rw [Subgroup.mem_comap]
    have hy' : y ∈ Subgroup.zpowers d ⊔ T := hy
    rw [Subgroup.mem_sup] at hy'
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
    have h2 : φ y₂ ∈ S.omega := by
      obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hy₂
      exact actHom_torus_mem_omega S p.1 p.2
    have h1 : φ y₁ ∈ Subgroup.zpowers D := by
      have hmem : φ y₁ ∈ (Subgroup.zpowers d).map φ := Subgroup.mem_map.mpr ⟨y₁, hy₁, rfl⟩
      rwa [MonoidHom.map_zpowers φ d] at hmem
    rw [map_mul]
    have hcomm : φ y₁ * φ y₂ = φ y₂ * φ y₁ := by
      rw [← map_mul, ← map_mul, mul_comm y₁ y₂]
    rw [hcomm]
    exact Subgroup.mul_mem_sup h2 h1
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · change D ∈ E
    rw [Subgroup.mem_map]
    exact ⟨d, Subgroup.mem_sup_left (Subgroup.mem_zpowers d), rfl⟩
  · exact Subgroup.map_le_iff_le_comap.mpr hE0_le
  · intro x hx y hy
    rw [Subgroup.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm a b]
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    change (φ a) ^ q = 1
    rw [← map_pow, hE0_pow a ha, map_one]
  · change Nat.card E = q ^ 3
    rw [Subgroup.card_map_of_injective (K := E₀) (f := φ) hφinj, hcardE0]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
