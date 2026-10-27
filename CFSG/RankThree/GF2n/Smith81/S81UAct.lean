module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Smith81.S81BBridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
open scoped commutatorElement

section Action

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V]

@[expose] def ActsOnQtAsU (ψ : M₀.E ≃ₗ[K] V) (m : G) (T : V ≃ₗ[K] V) : Prop :=
  ∀ x ∈ Q, T (ψ (M₀.π x)) = ψ (M₀.π (m * x * m⁻¹))

theorem ActsOnQtAsU.one (ψ : M₀.E ≃ₗ[K] V) : ActsOnQtAsU ψ (1 : G) 1 := by
  intro x hx
  simp

theorem ActsOnQtAsU.mul (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] V} {m m' : G}
    {T T' : V ≃ₗ[K] V} (hm' : m' ∈ M) (h : ActsOnQtAsU ψ m T) (h' : ActsOnQtAsU ψ m' T') :
    ActsOnQtAsU ψ (m * m') (T * T') := by
  intro x hx
  have h1 := h' x hx
  have h2 := h (m' * x * m'⁻¹) (CFSG.RankThree.GF2n.Smith81.conj_mem_Q H hm' hx)
  calc (T * T') (ψ (M₀.π x)) = T (T' (ψ (M₀.π x))) := rfl
    _ = T (ψ (M₀.π (m' * x * m'⁻¹))) := by rw [h1]
    _ = ψ (M₀.π (m * (m' * x * m'⁻¹) * m⁻¹)) := h2
    _ = ψ (M₀.π (m * m' * x * (m * m')⁻¹)) := by
      rw [show m * (m' * x * m'⁻¹) * m⁻¹ = m * m' * x * (m * m')⁻¹ by group]

theorem ActsOnQtAsU.unique (ψ : M₀.E ≃ₗ[K] V) {m : G} {T T' : V ≃ₗ[K] V}
    (h : ActsOnQtAsU ψ m T) (h' : ActsOnQtAsU ψ m T') : T = T' := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, hx, hxv⟩ := M₀.π_surj (ψ.symm v)
  have hv : ψ (M₀.π x) = v := by rw [hxv]; simp
  rw [← hv, h x hx, h' x hx]

theorem ActsOnQtAsU.pow (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] V} {m : G}
    {T : V ≃ₗ[K] V} (hm : m ∈ M) (h : ActsOnQtAsU ψ m T) (j : ℕ) :
    ActsOnQtAsU ψ (m ^ j) (T ^ j) := by
  induction j with
  | zero => simpa using ActsOnQtAsU.one ψ
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul H hm h

theorem ActsOnQtAsU.pow_eq_one (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] V} {m : G}
    {T : V ≃ₗ[K] V} (hm : m ∈ M) (h : ActsOnQtAsU ψ m T) {n : ℕ} (hn : m ^ n = 1) :
    T ^ n = 1 := by
  have h1 := h.pow H hm n
  rw [hn] at h1
  exact h1.unique ψ (ActsOnQtAsU.one ψ)

theorem exists_actsOnQtAsU (hg : GlobalModelData M Q Z γ M₀) (ψ : M₀.E ≃ₗ[K] V) {m : G}
    (hm : m ∈ H0 M Z) : ∃ T : V ≃ₗ[K] V, ActsOnQtAsU ψ m T := by
  obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.mp hm
  have hc : ∀ z ∈ Z, m * z * m⁻¹ = z := fun z hz => by
    have h1 := Subgroup.mem_centralizer_iff.mp hmC z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  obtain ⟨T', hT', -⟩ := hg.linear_of_centralizes hmM hc
  refine ⟨ψ.symm.trans (T'.trans ψ), fun x hx => ?_⟩
  simp [LinearEquiv.trans_apply, hT' x hx]

theorem ActsOnQtAsU.mem_Q (H : StrothHyp M Q Z) {ψ : M₀.E ≃ₗ[K] V} {m : G} (hm : m ∈ M)
    (h : ActsOnQtAsU ψ m 1) : m ∈ Q := by
  refine H.centralizer_Qt m hm fun y hy => ?_
  have h1 := h y hy
  have hmy : m * y * m⁻¹ ∈ Q := CFSG.RankThree.GF2n.Smith81.conj_mem_Q H hm hy
  have hπ : M₀.π (m * y * m⁻¹) = M₀.π y := ψ.injective (by simpa using h1.symm)
  have e : ⁅m, y⁆ = (m * y * m⁻¹) * y⁻¹ := by
    simp only [commutatorElement_def]
  rw [e]
  refine (M₀.π_ker _ (Q.mul_mem hmy (Q.inv_mem hy))).mp ?_
  rw [M₀.π_mul _ hmy _ (Q.inv_mem hy), quadModel_pi_inv M₀ hy, hπ]
  abel

section Uniform

private theorem q_le_lgen (M Q B : Subgroup G) : Q ≤ Lgen M (LB M Q B) := by
  calc Q ≤ LB M Q B := le_sup_left
    _ = conjSubgroup 1 (LB M Q B) := (conjSubgroup_one _).symm
    _ ≤ Lgen M (LB M Q B) :=
        le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m (LB M Q B)) 1 M.one_mem

private theorem lgen_le_M (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ M := by
  refine iSup₂_le fun m hm => ?_
  calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.LB_le_M
    _ = M := hc.conj_M_eq hm

variable {ψ : M₀.E ≃ₗ[K] V} {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}
  {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem actsOnQtAsU_phi (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀)
    (s : Lgen M (LB M Q B)) : ActsOnQtAsU ψ (s : G) (φ s) :=
  fun x hx => (d.equivariant s x hx).symm

theorem ActsOnQtAsU.mem_Lgen (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {m : G} {T : V ≃ₗ[K] V}
    (hm : m ∈ M) (h : ActsOnQtAsU ψ m T) (hT : T ∈ Γ) : m ∈ Lgen M (LB M Q B) := by
  have hH := hc.hyp
  rw [← d.range] at hT
  obtain ⟨s, hs⟩ := hT
  have hsM : (s : G) ∈ M := lgen_le_M hc s.2
  have h1 : ActsOnQtAsU ψ ((s⁻¹ : Lgen M (LB M Q B)) : G) (φ s⁻¹) := actsOnQtAsU_phi d s⁻¹
  rw [map_inv, Subgroup.coe_inv] at h1
  have h2 := ActsOnQtAsU.mul hH hm h1 h
  rw [hs, inv_mul_cancel] at h2
  have hq : (s : G)⁻¹ * m ∈ Q := ActsOnQtAsU.mem_Q hH (M.mul_mem (M.inv_mem hsM) hm) h2
  have e : m = (s : G) * ((s : G)⁻¹ * m) := by group
  rw [e]
  exact mul_mem s.2 (q_le_lgen M Q B hq)

theorem ActsOnQtAsU.normalizesGamma (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {m : G} {T : V ≃ₗ[K] V}
    (hm : m ∈ M) (h : ActsOnQtAsU ψ m T) : ∀ g ∈ Γ, ∃ g' ∈ Γ, T * g = g' * T := by
  intro g hg
  have hH := hc.hyp
  rw [← d.range] at hg
  obtain ⟨s, hs⟩ := hg
  let s' : Lgen M (LB M Q B) :=
    ⟨m * (s : G) * m⁻¹,
      (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) hm) (s : G)).mp s.2⟩
  have hsM : (s : G) ∈ M := lgen_le_M hc s.2
  have h1 : ActsOnQtAsU ψ (m * (s : G)) (T * φ s) :=
    ActsOnQtAsU.mul hH hsM h (actsOnQtAsU_phi d s)
  have h2 : ActsOnQtAsU ψ ((s' : G) * m) (φ s' * T) :=
    ActsOnQtAsU.mul hH hm (actsOnQtAsU_phi d s') h
  have hmm : m * (s : G) = (s' : G) * m := by
    show m * (s : G) = m * (s : G) * m⁻¹ * m
    group
  rw [hmm] at h1
  have h3 : T * φ s = φ s' * T := h1.unique ψ h2
  refine ⟨φ s', ?_, ?_⟩
  · rw [← d.range]
    exact ⟨s', rfl⟩
  · rw [← hs]
    exact h3

end Uniform

end Action

end CFSG.RankThree.GF2n.Smith81
