module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Abs5
import CFSG.LocalAnalysis.WeakClosure81.W183Abs3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem br1_false_closing {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
    {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}
    (h : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hS : T ⊓ L₁ ∈ Γ) (hSr : mRank (T ⊓ L₁) ≤ m - i₀ - 1)
    (hmem : ∀ D ∈ Γ, 2 < Nat.card D → D ≤ L₁ ∨ D ≤ L₂) : False := by
  haveI hsimple₁ : IsSimpleGroup ↥L₁ := htwo.simple₁
  have hL12 : L₁ ⊓ L₂ = ⊥ :=
    w183_inf_eq_bot_of_commute (L₁ := L₁) (L₂ := L₂) htwo.nonab₁ htwo.comm
  have hSne : T ⊓ L₁ ≠ ⊥ := h.h131.ne_bot (T ⊓ L₁) hS
  have hTYne : T ≠ Y := by
    intro hTY
    have hL1T : L₁ ≤ T := hTY ▸ htwo.le₁
    have hSeq : T ⊓ L₁ = L₁ := inf_eq_right.mpr hL1T
    have hL1Γ : L₁ ∈ Γ := by rw [← hSeq]; exact hS
    obtain ⟨a, ha, b, hb, hab⟩ := htwo.nonab₁
    exact hab (CFSG.Open.IsElemAbelian.comm (h.h131.isElemAb L₁ hL1Γ) ha hb)
  have hgen : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (T ⊓ L₁ : Set (LGL 2 V)) := by
    intro B hB
    obtain ⟨hBT, D, hD, hBD, _⟩ := h.gens B hB
    intro b hbB
    by_cases hb1 : b = 1
    · rw [hb1]; exact Subgroup.one_mem _
    have hbD : b ∈ D := hBD hbB
    have hbT : b ∈ T := hBT hbB
    have hbY : b ∈ Y := h.sylow.1 hbT
    have hDne : D ≠ ⊥ := h.h131.ne_bot D hD
    have hD1 : 1 < Nat.card D := (Subgroup.one_lt_card_iff_ne_bot D).mpr hDne
    have hDcard : Nat.card D = 2 ∨ 2 < Nat.card D := by omega
    rcases hDcard with hD2 | hDgt
    · have hb2 : b * b = 1 :=
        CFSG.Open.IsElemAbelian.mul_self_eq_one (h.h131.isElemAb D hD) hbD
      have horder : orderOf b = 2 := by
        have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
        rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf b) hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hb1
        · exact h2
      have hzpowD : Subgroup.zpowers b = D := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbD) ?_
        rw [Nat.card_zpowers, horder, hD2]
      have hzpowΓ : Subgroup.zpowers b ∈ Γ := by rw [hzpowD]; exact hD
      have hσr : mRank (Subgroup.zpowers b) ≤ m - i₀ - 1 := by
        unfold mRank
        rw [Nat.card_zpowers, horder]
        have hlog : Nat.log 2 2 = 1 := by decide
        rw [hlog]
        exact h.h131.pos_i
      rcases htwo.perm b hbY with ⟨hp1, _hp2⟩ | ⟨hp1, _hp2⟩
      · have hcjS : cj b (T ⊓ L₁) = T ⊓ L₁ := by
          unfold cj
          rw [Subgroup.map_inf T L₁ (MulAut.conj b).toMonoidHom (MulAut.conj b).injective]
          rw [show T.map (MulAut.conj b).toMonoidHom = T from
                (Subgroup.mem_normalizer_iff_map_conj_eq (H := T) (g := b)).mp
                  (Subgroup.le_normalizer hbT),
              show L₁.map (MulAut.conj b).toMonoidHom = L₁ from by simpa [cj] using hp1]
        exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := T ⊓ L₁) (g := b)).mpr
          (by simpa [cj] using hcjS)
      · exfalso
        have hle' : cj b (T ⊓ L₁) ≤ L₂ := by
          calc cj b (T ⊓ L₁) = cj b T ⊓ cj b L₁ := by
                unfold cj
                rw [Subgroup.map_inf T L₁ (MulAut.conj b).toMonoidHom
                  (MulAut.conj b).injective]
            _ ≤ cj b L₁ := inf_le_right
            _ = L₂ := hp1
        have hne : cj b (T ⊓ L₁) ≠ T ⊓ L₁ := by
          intro heq
          have hle : T ⊓ L₁ ≤ L₂ := by rwa [heq] at hle'
          have hbot : T ⊓ L₁ ≤ (⊥ : Subgroup (LGL 2 V)) := by
            rw [← hL12]
            exact le_inf inf_le_right hle
          exact hSne (le_bot_iff.mp hbot)
        have hcomm : ∀ a ∈ T ⊓ L₁, ∀ b' ∈ cj b (T ⊓ L₁), a * b' = b' * a := by
          intro a ha b' hb'
          exact htwo.comm a (Subgroup.mem_inf.mp ha).2 b' (hle' hb')
        have hSsq : ∀ x ∈ T ⊓ L₁, x * x = 1 := fun x hx =>
          CFSG.Open.IsElemAbelian.mul_self_eq_one (h.h131.isElemAb (T ⊓ L₁) hS) hx
        have hnt : Nontrivial ↥(T ⊓ L₁) :=
          (Subgroup.nontrivial_iff_ne_bot (T ⊓ L₁)).mpr hSne
        obtain ⟨s, hs, hs1⟩ := (Subgroup.nontrivial_iff_exists_ne_one (T ⊓ L₁)).mp hnt
        exact Assumption131.false_of_sylow_and_reflection h.h131 hS hSr
          (h.vfix (T ⊓ L₁) hS) hSsq hbY hb2 hb1 hzpowΓ hσr hne hcomm hs hs1
    · rcases hmem D hD hDgt with hDL1 | hDL2
      · exact Subgroup.le_normalizer (show b ∈ T ⊓ L₁ from ⟨hbT, hDL1 hbD⟩)
      · have hbCent : b ∈ Subgroup.centralizer (T ⊓ L₁ : Set (LGL 2 V)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro s hs
          exact htwo.comm s (Subgroup.mem_inf.mp hs).2 b (hDL2 hbD)
        exact Subgroup.centralizer_le_normalizer _ hbCent
  have hTnorm : T ≤ Subgroup.normalizer (T ⊓ L₁ : Set (LGL 2 V)) :=
    h.weakClosure (T ⊓ L₁) hS inf_le_left hgen T h.sylow.1 le_rfl hTYne
  obtain ⟨x, hxT, hxL⟩ := htwo.swap
  have hxnorm : x ∈ Subgroup.normalizer (T ⊓ L₁ : Set (LGL 2 V)) := hTnorm hxT
  have hxS : cj x (T ⊓ L₁) = T ⊓ L₁ := by
    simpa [cj] using
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := T ⊓ L₁) (g := x)).mp hxnorm
  have hle : T ⊓ L₁ ≤ L₂ := by
    have hle' : cj x (T ⊓ L₁) ≤ L₂ := by
      calc cj x (T ⊓ L₁) = cj x T ⊓ cj x L₁ := by
            unfold cj
            rw [Subgroup.map_inf T L₁ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective]
        _ ≤ cj x L₁ := inf_le_right
        _ = L₂ := hxL
    rwa [hxS] at hle'
  have hbot : T ⊓ L₁ ≤ (⊥ : Subgroup (LGL 2 V)) := by
    rw [← hL12]
    exact le_inf inf_le_right hle
  exact hSne (le_bot_iff.mp hbot)

end CFSG.LocalAnalysis.WeakClosure81

end
