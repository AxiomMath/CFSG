module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L3Facts
import CFSG.GroupTheory.CentralizerMap
import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup

variable {X X' : Type*} [Group X] [Group X']

private theorem mulAut_congr_conj (e : X ≃* X') (g : X) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem derivedCent_map (e : X ≃* X') (t : X) :
    (derivedCent t).map e.toMonoidHom = derivedCent (e t) := by
  unfold derivedCent
  rw [Subgroup.map_commutator, CFSG.centralizer_singleton_map]

theorem L3OddPointed.of_mulEquiv {t₀ : X} (h : L3OddPointed X t₀) (e : X ≃* X') :
    L3OddPointed X' (e t₀) where
  orderOf_eq := by
    simpa using (MulEquiv.orderOf_eq e t₀).trans h.orderOf_eq
  conj := by
    intro t ht
    obtain ⟨g, hg⟩ := h.conj (e.symm t) (by
      simpa using (MulEquiv.orderOf_eq e.symm t).trans ht)
    refine ⟨e g, ?_⟩
    simpa using congrArg e hg
  inner := by
    intro B' hB'4 hB'2
    let ψ : MulAut X ≃* MulAut X' := MulAut.congr e
    let B : Subgroup (MulAut X) := B'.map ψ.symm.toMonoidHom
    have hBcard : Nat.card B = 4 := by
      change Nat.card (B'.map ψ.symm.toMonoidHom) = 4
      rw [Subgroup.card_map_of_injective ψ.symm.injective, hB'4]
    have hB2 : ∀ β ∈ B, β * β = 1 := by
      intro β hβ
      obtain ⟨β', hβ', rfl⟩ := Subgroup.mem_map.mp hβ
      rw [← map_mul, hB'2 β' hβ', map_one]
    obtain ⟨β, hβB, hβne, hβinner⟩ := h.inner B hBcard hB2
    obtain ⟨b', hb'B, hb'eq⟩ := Subgroup.mem_map.mp hβB
    have hb' : b' = ψ β := by
      rw [← hb'eq]
      simp
    refine ⟨b', hb'B, ?_, ?_⟩
    · intro h1
      apply hβne
      rw [← hb'eq, h1, map_one]
    · obtain ⟨g, hg⟩ := hβinner
      refine ⟨e g, ?_⟩
      rw [hb', ← hg]
      exact (mulAut_congr_conj e g).symm
  quasi := by
    let hiso : ↥(derivedCent t₀) ≃* ↥(derivedCent (e t₀)) :=
      (Subgroup.equivMapOfInjective (derivedCent t₀) e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (derivedCent_map e t₀))
    exact CFSG.Open.IsQuasisimple.of_mulEquiv hiso.symm h.quasi
  cent := by
    intro β' hβ'2 hβ't hβ'K
    let ψ : MulAut X ≃* MulAut X' := MulAut.congr e
    let β : MulAut X := ψ.symm β'
    have hβ2 : β * β = 1 := by
      dsimp only [β]
      rw [← map_mul, hβ'2, map_one]
    have hβt : β t₀ = t₀ := by
      dsimp only [β, ψ]
      rw [MulAut.congr_symm_apply]
      simp [MulEquiv.trans_apply, hβ't]
    have hβK : ∀ k ∈ derivedCent t₀, β k = k := by
      intro k hk
      have hk' : e k ∈ derivedCent (e t₀) := by
        rw [← derivedCent_map e t₀]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hk
      dsimp only [β, ψ]
      rw [MulAut.congr_symm_apply]
      simp [MulEquiv.trans_apply, hβ'K (e k) hk']
    have hβ'eq : β' = ψ β := (ψ.apply_symm_apply β').symm
    have hψconj : ψ (MulAut.conj t₀) = MulAut.conj (e t₀) := by
      dsimp only [ψ]
      exact mulAut_congr_conj e t₀
    rcases h.cent β hβ2 hβt hβK with h1 | h1
    · left
      rw [hβ'eq, h1, map_one]
    · right
      rw [hβ'eq, h1, hψconj]
  gen := by
    intro t ht hc hne
    have ht' : orderOf (e.symm t) = 2 := by
      simpa using (MulEquiv.orderOf_eq e.symm t).trans ht
    have hc' : t₀ * e.symm t = e.symm t * t₀ := by
      apply e.injective
      simpa using hc
    have hne' : t₀ ≠ e.symm t := by
      intro h1
      apply hne
      calc e t₀ = e (e.symm t) := by rw [h1]
        _ = t := e.apply_symm_apply t
    have hgen := h.gen (e.symm t) ht' hc' hne'
    calc derivedCent (e t₀) ⊔ derivedCent t
        = (derivedCent t₀).map e.toMonoidHom ⊔
            (derivedCent (e.symm t)).map e.toMonoidHom := by
          rw [derivedCent_map e t₀, derivedCent_map e (e.symm t), e.apply_symm_apply]
      _ = (derivedCent t₀ ⊔ derivedCent (e.symm t)).map e.toMonoidHom := by
          rw [Subgroup.map_sup]
      _ = ⊤ := by
          rw [hgen, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  four := by
    obtain ⟨g, hg⟩ := h.four
    refine ⟨e g, ?_⟩
    have h1 : orderOf (e (t₀ * (g * t₀ * g⁻¹))) = 4 := by
      rw [MulEquiv.orderOf_eq, hg]
    simpa using h1

theorem L3OddPointed.of_orderOf_eq_two {t₀ : X} (h : L3OddPointed X t₀) {t : X}
    (ht : orderOf t = 2) : L3OddPointed X t := by
  obtain ⟨g, hg⟩ := h.conj t ht
  have h' : L3OddPointed X ((MulAut.conj g) t₀) := h.of_mulEquiv (MulAut.conj g)
  rwa [MulAut.conj_apply, hg] at h'

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
