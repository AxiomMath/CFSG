module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

theorem noSignalizer_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {D : Subgroup X}
    (h : ∀ Q : Subgroup (MulAut X'), ¬ 3 ∣ Nat.card Q →
      (D.map e.toMonoidHom).map (MulAut.conj : X' →* MulAut X') ≤
        Subgroup.normalizer (Q : Set (MulAut X')) → Q = ⊥)
    (Q : Subgroup (MulAut X)) (hQ : ¬ 3 ∣ Nat.card Q)
    (hN : D.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Q : Set (MulAut X))) :
    Q = ⊥ := by
  set Ψ : MulAut X ≃* MulAut X' := MulAut.congr e with hΨ
  have hQ' : ¬ 3 ∣ Nat.card (Q.map Ψ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective Ψ.injective]
  have hN' : (D.map e.toMonoidHom).map (MulAut.conj : X' →* MulAut X') ≤
      Subgroup.normalizer ((Q.map Ψ.toMonoidHom : Subgroup (MulAut X')) : Set (MulAut X')) := by
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    have hdN := Subgroup.mem_normalizer_iff.mp (hN ⟨d, hd, rfl⟩) (Ψ.symm σ)
    have hconj : MulAut.conj (e d) = Ψ (MulAut.conj d) := by
      rw [hΨ, mulAut_congr_conj]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨MulAut.conj d * τ * (MulAut.conj d)⁻¹, ?_, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hdN
        exact hdN.mp hτ
      · change Ψ (MulAut.conj d * τ * (MulAut.conj d)⁻¹) = MulAut.conj (e d) * Ψ τ *
          (MulAut.conj (e d))⁻¹
        rw [hconj, map_mul, map_mul, map_inv]
    · rintro ⟨τ, hτ, hτe⟩
      refine ⟨Ψ.symm σ, ?_, Ψ.apply_symm_apply σ⟩
      refine hdN.mpr ?_
      have h1 : MulAut.conj d * Ψ.symm σ * (MulAut.conj d)⁻¹ = τ := by
        apply Ψ.injective
        rw [map_mul, map_mul, map_inv, ← hconj, Ψ.apply_symm_apply]
        exact hτe.symm
      rw [h1]
      exact hτ
  have h1 := h _ hQ' hN'
  exact (Subgroup.map_eq_bot_iff_of_injective _ Ψ.injective).mp h1

theorem alphaVanishes_of_noSignalizer_mulEquiv {X X' : Type} [Group X] [Finite X] [Group X']
    (hZ : Subgroup.center X = ⊥) (e : X ≃* X') {D : Subgroup X}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD : D ≠ ⊥)
    (h : ∀ Q : Subgroup (MulAut X'), ¬ 3 ∣ Nat.card Q →
      (D.map e.toMonoidHom).map (MulAut.conj : X' →* MulAut X') ≤
        Subgroup.normalizer (Q : Set (MulAut X')) → Q = ⊥) :
    AlphaVanishes X D :=
  alphaVanishes_of_noSignalizer hZ hDc hD (noSignalizer_of_mulEquiv e h)

theorem ne_bot_of_card_nine {G : Type*} [Group G] {D : Subgroup G} (hD9 : Nat.card D = 9) :
    D ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hD9
  norm_num at hD9

theorem comm_of_isElemAbelian {G : Type*} [Group G] {D : Subgroup G}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a :=
  fun _ ha _ hb => CFSG.Open.IsElemAbelian.comm hD ha hb

theorem isElemAbelian_map' {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem center_eq_bot_of_mulEquiv {X M : Type} [Group X] [Group M] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* M) : Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have h1 : e.symm c ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    have := hc (e g)
    apply e.injective
    simp [map_mul, this]
  rw [hZ, Subgroup.mem_bot] at h1
  have := congrArg e h1
  simpa using this

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
