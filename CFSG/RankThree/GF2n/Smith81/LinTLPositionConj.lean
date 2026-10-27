module

public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualField
public import CFSG.RankThree.GF2n.Smith81.LinSetup

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.conj_trichotomy (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A) :
    A ≤ V₁ ∨ A ≤ V₂ ∨ ((A ⊔ Z) ⊓ V₁ = Z ∧ (A ⊔ Z) ⊓ V₂ = Z) := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, -, -, hAline, -, -⟩ := hA.dictB h
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨F, hFfield, hFfin, hFcard, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φ, hΦ, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [h.card, hFcard]) Φ hΦ
  have hV1 : ∀ e, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0 := fun e => by
    rw [hCΦ]
    exact hΦ₁ e
  have hV2 : ∀ e, e ∈ M₀.img V₂ ↔ (C.Ψ e).1 = 0 := fun e => by
    rw [hCΦ]
    exact hΦ₂ e
  have hAZ : ∀ x ∈ A ⊔ Z, x ∈ Q ∧ M₀.π x ∈ M₀.img A := by
    intro x hx
    have hle : A ⊔ Z ≤ M₀.lift (M₀.img A) := by
      refine sup_le (fun u hu => ?_) (fun z hz => ?_)
      · exact (M₀.mem_lift).mpr ⟨hA.le hu, M₀.pi_mem_img hu (hA.le hu)⟩
      · refine (M₀.mem_lift).mpr ⟨h.reg.V_le hz, ?_⟩
        rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
        exact AddSubgroup.zero_mem _
    exact (M₀.mem_lift).mp (hle hx)
  by_cases h2 : (C.Ψ b).2 = 0
  ·
    left
    intro x hx
    have hxQ : x ∈ Q := hA.le hx
    obtain ⟨s, hs⟩ := (hAline _).mp (M₀.pi_mem_img hx hxQ)
    refine (M₀.mem_img_iff hZV₁ hxQ).mp ((hV1 _).mpr ?_)
    rw [hs, C.smul]
    show C.θ₂ s • (C.Ψ b).2 = 0
    rw [h2, smul_zero]
  by_cases h1 : (C.Ψ b).1 = 0
  ·
    right
    left
    intro x hx
    have hxQ : x ∈ Q := hA.le hx
    obtain ⟨s, hs⟩ := (hAline _).mp (M₀.pi_mem_img hx hxQ)
    refine (M₀.mem_img_iff hZV₂ hxQ).mp ((hV2 _).mpr ?_)
    rw [hs, C.smul]
    show C.θ₁ s • (C.Ψ b).1 = 0
    rw [h1, smul_zero]
  right
  right
  constructor
  · refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hZV₁)
    obtain ⟨hxAZ, hxV⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxQ, hπA⟩ := hAZ x hxAZ
    obtain ⟨s, hs⟩ := (hAline _).mp hπA
    have hv : C.θ₂ s • (C.Ψ b).2 = 0 := by
      have h0 := (hV1 _).mp (M₀.pi_mem_img hxV hxQ)
      rw [hs, C.smul] at h0
      exact h0
    rcases smul_eq_zero.mp hv with hθ | hp
    · have hs0 : s = 0 := C.θ₂.injective (hθ.trans (map_zero C.θ₂).symm)
      exact (M₀.π_ker x hxQ).mp (by rw [hs, hs0, zero_smul])
    · exact absurd hp h2
  · refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hZV₂)
    obtain ⟨hxAZ, hxV⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxQ, hπA⟩ := hAZ x hxAZ
    obtain ⟨s, hs⟩ := (hAline _).mp hπA
    have hv : C.θ₁ s • (C.Ψ b).1 = 0 := by
      have h0 := (hV2 _).mp (M₀.pi_mem_img hxV hxQ)
      rw [hs, C.smul] at h0
      exact h0
    rcases smul_eq_zero.mp hv with hθ | hp
    · have hs0 : s = 0 := C.θ₁.injective (hθ.trans (map_zero C.θ₁).symm)
      exact (M₀.π_ker x hxQ).mp (by rw [hs, hs0, zero_smul])
    · exact absurd hp h1

end CFSG.RankThree.GF2n.Smith81
