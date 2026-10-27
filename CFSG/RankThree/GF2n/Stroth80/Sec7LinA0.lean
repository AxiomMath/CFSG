module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec37Commuting

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_A0 [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
      (_ : IsTensorSetup hc n M₀ ρ b) (ψ : M₀.E →ₗ[K] M₀.E),
      (∀ e, ψ e =
        (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M hs.toSec5.mem⟩ : ↥M))).toAdd e - e) ∧
      (∀ e, e ∈ LinearMap.range ψ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
      (∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0) ∧
      (∀ a a' : Mbar M Q, (∀ e, (ρ a).toAdd e = (ρ a').toAdd e) → a = a') ∧
      (∀ a ∈ bar M Q Z0, ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • ψ e) ∧
      (∀ c : K, ∃ a ∈ bar M Q Z0, ∀ e, (ρ a).toAdd e = e + c • ψ e) := by
  classical
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, -, hinj, ψ, hψ, hker, hA, -⟩ :=
    sec7_linModelData h34 h310chi hc hs hZ0
      (fun z hz w hw => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).2 w hw)
      (fun u hu huQ => hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ)
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  refine ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, ?_, ?_, hinj, hA, ?_⟩
  ·
    obtain ⟨hVeq, hWeq⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
    obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
    have htbH : (QuotientGroup.mk (⟨t, htM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
      Subgroup.mem_map.mpr ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr (hc.LB_le_H0 ht), rfl⟩
    let T : M₀.E ≃ₗ[K] M₀.E :=
      AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd (hS.lin _ htbH)
    have hψT : ψ = (T : M₀.E →ₗ[K] M₀.E) - 1 := LinearMap.ext fun e => by
      rw [hψ e]
      rfl
    intro e
    rw [hψT, hVeq]
    exact (mem_img_comm_zpowers_sup_iff M₀ hS.model.reg T htQ htQ'
      (fun x hx => hS.conj ⟨t, htM⟩ x hx) e).symm
  ·
    intro x hxQ
    obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
    obtain ⟨-, hWeq⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
    have key : ψ (M₀.π x) = 0 ↔ ⁅t, x⁆ ∈ Z := by
      rw [hψ, sub_eq_zero, ← hS.conj ⟨t, htM⟩ x hxQ]
      exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ (htQ x hxQ)).symm
    rw [key, hWeq, hc.mem_Q1_iff htM]
    exact ⟨fun h => h.2, fun h => ⟨hxQ, h⟩⟩
  · choose Λ hΛ using fun a : ↥(bar M Q Z0) => hA a a.2
    have hΛinj : Function.Injective Λ := by
      intro a a' h
      apply Subtype.ext
      apply hinj
      intro e
      rw [hΛ a e, hΛ a' e, h]
    have hcard : Nat.card ↥(bar M Q Z0) = Nat.card K := by
      have h1 := Tim37.card_bar_mul_card_of_le (M := M) hQZ0 hZ0M
      have h2 := hZcard G M Q Z B hc n t hs Z0 hZ0
      rw [h2] at h1
      have h3 : Nat.card ↥(bar M Q Z0) = Nat.card Z :=
        Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (by rw [mul_comm]; exact h1)
      rw [h3, hS.card]
    have hbij : Function.Bijective Λ :=
      hΛinj.bijective_of_nat_card_le (by rw [hcard])
    intro c
    obtain ⟨a, ha⟩ := hbij.2 c
    exact ⟨a, a.2, fun e => by rw [hΛ a e, ha]⟩

theorem sec7_comm_Z0_of_vanish [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {z : G} (hzH : z ∈ H0 M Z)
    (hzV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅z, v⁆ ∈ Z) : ∀ a ∈ Z0, ⁅z, a⁆ ∈ Q := by
  classical
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA, -⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  have hzM : z ∈ M := hzH.1
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQn : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  set ζ : Mbar M Q := QuotientGroup.mk (⟨z, hzM⟩ : ↥M) with hζ
  have hζH : ζ ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzH, rfl⟩
  have hlin := hS.lin ζ hζH
  have hiso := hS.iso ζ hζH
  have hfixV : ∀ e ∈ M₀.img (Vt M (LB M Q B) B Z t), (ρ ζ).toAdd e = e := by
    rintro _ ⟨v, hvV, hvQ, rfl⟩
    rw [hζ, ← hS.conj ⟨z, hzM⟩ v hvQ]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hvQ (hQn z hzM v hvQ)).mp (hzV v hvV)
  have h1 : ∀ e, (ρ ζ).toAdd (ψ e) = ψ e := fun e => hfixV _ ((hrange _).mp ⟨e, rfl⟩)
  have h2 : ∀ e, ψ ((ρ ζ).toAdd e - e) = 0 := by
    intro e
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj ((ρ ζ).toAdd e - e)
    rw [← hx]
    refine (hW x hxQ).mp ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hvQ : v ∈ Q := hVQ hv
    have hvfix := hfixV _ (M₀.pi_mem_img hv hvQ)
    refine ((M₀.comm_iff_B hS.model.reg hvQ hxQ).mpr ?_)
    rw [hx, map_sub]
    have e3 : M₀.B (M₀.π v) ((ρ ζ).toAdd e) = M₀.B (M₀.π v) e := by
      have := hiso (M₀.π v) e
      rw [hvfix] at this
      exact this
    rw [e3, sub_self]
  have hcomm : ∀ e, (ρ ζ).toAdd (ψ e) = ψ ((ρ ζ).toAdd e) := by
    intro e
    rw [h1]
    have h3 := h2 e
    rw [map_sub, sub_eq_zero] at h3
    exact h3.symm
  intro a ha
  obtain ⟨c, hc'⟩ := hA (QuotientGroup.mk (⟨a, hZ0M ha⟩ : ↥M))
    (Subgroup.mem_map.mpr ⟨⟨a, hZ0M ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
  have hcomm2 : ∀ e, (ρ ζ).toAdd ((ρ (QuotientGroup.mk (⟨a, hZ0M ha⟩ : ↥M))).toAdd e) =
      (ρ (QuotientGroup.mk (⟨a, hZ0M ha⟩ : ↥M))).toAdd ((ρ ζ).toAdd e) := by
    intro e
    rw [hc', hc', map_add, hlin c (ψ e), hcomm e]
  have hmk : ζ * QuotientGroup.mk (⟨a, hZ0M ha⟩ : ↥M) =
      QuotientGroup.mk (⟨a, hZ0M ha⟩ : ↥M) * ζ := by
    refine hinj _ _ fun e => ?_
    have h4 := hcomm2 e
    rw [act_mul_apply ρ, act_mul_apply ρ]
    exact h4
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hmk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmk
  have e : ⁅z, a⁆ = (z * a) * ((z * a)⁻¹ * (a * z))⁻¹ * (z * a)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hQn (z * a) (M.mul_mem hzM (hZ0M ha)) _ (Q.inv_mem hmk)

end CFSG.RankThree.GF2n.Stroth80
