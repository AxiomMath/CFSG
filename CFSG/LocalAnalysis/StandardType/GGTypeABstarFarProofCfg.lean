module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueCtx

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix CFSG.Assembly

section Cfg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}

theorem ggFarCtx_of_cfg {B : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G}
    {K : Subgroup G} (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} (hL : φ₁.range = L)
    (hk₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hK : φ₂.range = K)
    (hk₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hc : φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
      φ₂.comp (slUpperBlockHom n (GaloisField 2 f)))
    (hdiag : ∀ c ∈ Bs, GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c) : GGFarCtx p Bs φ₁ φ₂ x y := by
  refine
    { prime := hN.prime
      odd := ?_
      two := ?_
      three_le := hN.three_le
      lifts := ⟨hk₁, hk₂, hc, fun c hc' => (hdiag c hc').1, fun c hc' => (hdiag c hc').2⟩
      exp := hN.exponent
      cent := hN.bs_centralizer
      x_mem := hN.x_mem
      y_mem := hN.y_mem
      y_ne := hN.y_ne_one
      x_comm := ?_
      x_ncomm := ?_
      y_comm := ?_
      inj := ?_ }
  ·
    intro hp
    have hf : 1 ≤ f := hN.one_le_f
    have h2 : 2 ∣ 2 ^ f - 1 := hp ▸ hN.dvd_two_pow_sub_one
    have heven : Even (2 ^ f) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hnot : ¬ Even (2 ^ f - 1) := by
      intro he
      exact Nat.not_even_one ((Nat.even_sub (Nat.one_le_two_pow (n := f))).mp he |>.mp heven)
    exact hnot (even_iff_two_dvd.mpr h2)
  ·
    simpa using CharP.cast_eq_zero (GaloisField 2 f) 2
  ·
    intro s
    exact hN.x_comm_of_mem_L (φ₁ s) (by rw [← hL]; exact ⟨s, rfl⟩)
  ·
    intro h
    apply hN.not_x_comm_K
    intro k hk
    rw [← hK] at hk
    obtain ⟨s, hs⟩ := hk
    rw [← hs]
    exact h s
  ·
    intro s
    exact hN.y_comm_of_mem_K (φ₂ s) (by rw [← hK]; exact ⟨s, rfl⟩)
  ·
    intro g hg h1 h2
    apply hN.eq_one_of_comm_L_K g hg
    · intro l hl
      rw [← hL] at hl
      obtain ⟨s, hs⟩ := hl
      rw [← hs]
      exact h1 s
    · intro k hk
      rw [← hK] at hk
      obtain ⟨s, hs⟩ := hk
      rw [← hs]
      exact h2 s

end Cfg

end CFSG.StandardType
