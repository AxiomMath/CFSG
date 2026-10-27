module

public import CFSG.RankThree.GF2n.Smith81.S81LRoot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube
open scoped commutatorElement

section Model

variable {K : Type} [Field K]

theorem A5Cube.IsPure.smul' {ξ : Cube K} (h : IsPure K ξ) (s : K) : IsPure K (s • ξ) := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨Function.update v 0 (s • v 0), ?_⟩
  have h1 := (exteriorPower.ιMulti K 3).map_update_smul v 0 s (v 0)
  have h2 : Function.update v 0 (v 0) = v := Function.update_eq_self 0 v
  rw [h2] at h1
  exact h1.symm

end Model

section Points

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ψ : M₀.E ≃ₗ[K] Cube K} {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}

theorem exists_comm_eq_of_mem_Q (hg : GlobalModelData M Q Z γ M₀) {a : G} (haQ : a ∈ Q)
    (haZ : a ∉ Z) {z₀ : G} (hz₀ : z₀ ∈ Z) : ∃ q ∈ Q, ⁅q, a⁆ = z₀ := by
  have R := hg.reg
  have hπa : M₀.π a ≠ 0 := fun h0 => haZ ((M₀.π_ker a haQ).mp h0)
  obtain ⟨f, hf⟩ : ∃ f : M₀.E, M₀.B (M₀.π a) f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hπa (M₀.nondeg _ hcon)
  have hBf : M₀.B f (M₀.π a) ≠ 0 := by
    intro h
    apply hf
    rw [Tim79.QuadModel.B_comm (M₀.π a) f, h, neg_zero]
  obtain ⟨q, hqQ, hq⟩ := M₀.π_surj ((γ z₀ * (M₀.B f (M₀.π a))⁻¹) • f)
  have hcZ : ⁅q, a⁆ ∈ Z := M₀.comm_mem q hqQ a haQ
  have hγ : γ ⁅q, a⁆ = γ z₀ := by
    rw [M₀.comm_eq q hqQ a haQ, hq, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc,
      inv_mul_cancel₀ hBf, mul_one]
  have hγinv : γ z₀⁻¹ = - γ z₀ := by
    have := R.add z₀ hz₀ z₀⁻¹ (Z.inv_mem hz₀)
    rw [mul_inv_cancel, R.one] at this
    linear_combination -this
  have h0 : γ (⁅q, a⁆ * z₀⁻¹) = 0 := by
    rw [R.add _ hcZ _ (Z.inv_mem hz₀), hγinv, hγ, add_neg_cancel]
  exact ⟨q, hqQ, mul_inv_eq_one.mp (R.inj _ (Z.mul_mem hcZ (Z.inv_mem hz₀)) h0)⟩

theorem isConj_of_mem_conj (Hs : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {g a : G}
    (ha : a ∈ conjSubgroup g Z) (ha1 : a ≠ 1) : IsConj z a := by
  rw [mem_conjSubgroup] at ha
  have hy1 : g⁻¹ * a * g ≠ 1 := by
    intro h
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨m, -, hm⟩ := Z_isConj Hs hz hz1 ha hy1
  refine isConj_iff.mpr ⟨g * m, ?_⟩
  calc (g * m) * z * (g * m)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hm]
    _ = a := by group

theorem EGeom.EUniData.isPure_of_isConj (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (Hs : StrothHyp M Q Z) {z a : G} (hz : z ∈ Z) (hza : IsConj z a) (haQ : a ∈ Q)
    (haZ : a ∉ Z) : IsPure K (ψ (M₀.π a)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hza
  have haA : a ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, ← hg]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
    exact hz
  have hAZ : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  have hAQ : conjSubgroup g Z ≤ Q := by
    have := IsZConjugate.le_QB_of_mem Hs (IsZConjugate.self Z) hAZ ha1 haA
      (by rw [Hs.QB_Z]; exact haQ)
    rwa [Hs.QB_Z] at this
  have hAne : conjSubgroup g Z ≠ Z := fun e => haZ (e ▸ haA)
  obtain ⟨g₀, hg₀, himg, -⟩ := d.point _ hAZ hAQ hAne
  obtain ⟨h₀, -, rfl⟩ := Subgroup.mem_map.mp hg₀
  have hmem : ψ (M₀.π a) ∈ ((Submodule.span K {rhoEquiv K h₀ (p0 K)} : Submodule K (Cube K)) :
      Set (Cube K)) := by
    rw [← himg]
    exact ⟨a, haA, rfl⟩
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
  rw [← hs]
  have hp0 : IsPure K (p0 K) := ⟨_, p0_eq⟩
  have e : s • (rhoEquiv K h₀) (p0 K) = (rhoEquiv K h₀) (s • p0 K) := by simp
  rw [e]
  exact (hp0.smul' s).rho h₀

theorem EGeom.EUniData.isConj_of_isPure (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (Hs : StrothHyp M Q Z) (hg : GlobalModelData M Q Z γ M₀) {z a : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (haQ : a ∈ Q) (haZ : a ∉ Z) (hpure : IsPure K (ψ (M₀.π a))) : IsConj z a := by
  have hζ0 : ψ (M₀.π a) ≠ 0 := fun h => haZ ((M₀.π_ker a haQ).mp (ψ.map_eq_zero_iff.mp h))
  obtain ⟨A, hAZ, hAQ, -, a₁, ha₁A, hψa₁⟩ := d.exists_root_group Hs hpure hζ0
  have ha₁Q : a₁ ∈ Q := hAQ ha₁A
  have hπ : M₀.π a₁ = M₀.π a := ψ.injective hψa₁
  have hz₀ : a₁⁻¹ * a ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ ha₁Q haQ).mp hπ
  have ha₁Z : a₁ ∉ Z := fun h => haZ ((M₀.π_ker a haQ).mp (by rw [← hπ]; exact (M₀.π_ker a₁ ha₁Q).mpr h))
  have ha₁1 : a₁ ≠ 1 := fun h => ha₁Z (h ▸ Z.one_mem)
  obtain ⟨g₂, hg₂⟩ := hAZ
  have hconj₁ : IsConj z a₁ := isConj_of_mem_conj Hs hz hz1 (g := g₂) (hg₂ ▸ ha₁A) ha₁1
  obtain ⟨q, hqQ, hq⟩ := exists_comm_eq_of_mem_Q hg ha₁Q ha₁Z hz₀
  have hZcent : ∀ y ∈ Z, ∀ w ∈ Q, w * y = y * w := fun y hy w hw => by
    have hy' : y ∈ Subgroup.centralizer (Q : Set G) := by rw [Hs.centralizer_Q]; exact hy
    exact Subgroup.mem_centralizer_iff.mp hy' w hw
  have hqa : q * a₁ * q⁻¹ = a := by
    have h1 : q * a₁ * q⁻¹ * a₁⁻¹ = a₁⁻¹ * a := by rw [← hq, commutatorElement_def]
    have h2 : a₁ * (a₁⁻¹ * a) = (a₁⁻¹ * a) * a₁ := hZcent _ hz₀ a₁ ha₁Q
    calc q * a₁ * q⁻¹ = (q * a₁ * q⁻¹ * a₁⁻¹) * a₁ := by group
      _ = (a₁⁻¹ * a) * a₁ := by rw [h1]
      _ = a₁ * (a₁⁻¹ * a) := h2.symm
      _ = a := by group
  exact hconj₁.trans (isConj_iff.mpr ⟨q, hqa⟩)

end Points

end CFSG.RankThree.GF2n.Smith81
