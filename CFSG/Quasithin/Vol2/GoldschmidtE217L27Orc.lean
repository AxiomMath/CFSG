module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Grp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinPGL

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter (PSL2)

namespace E217L27

theorem oddOracle_of_psl_seven
    {X : Type} [Group X] {K : Subgroup X} (hK : K.Normal)
    (hcent : Subgroup.centralizer (K : Set X) = ⊥) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 7) (e : ↥K ≃* PSL2 F) : OddOracle K := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro w hw hw2
  set α₀ : MulAut ↥K := MulAut.conjNormal w with hα₀
  set α : MulAut (PSL2 F) := MulAut.congr e α₀ with hα
  have hα2 : α * α = 1 := by
    have : α₀ * α₀ = 1 := by rw [← map_mul, hw2, map_one]
    rw [hα, ← map_mul, this, map_one]
  have hαapp : ∀ k : ↥K, α (e k) = e (α₀ k) := fun k => by simp [hα]
  have hαi : α ∉ CFSG.QuasithinUnique.innerAut (PSL2 F) := by
    rintro ⟨y, hy⟩
    have h1 : ∀ k : ↥K, α₀ k = e.symm y * k * (e.symm y)⁻¹ := by
      intro k
      have h2 : α (e k) = y * e k * y⁻¹ := by rw [← hy]; rfl
      apply e.injective
      rw [← hαapp, h2]
      simp
    have hk' : (e.symm y : X) ∈ K := (e.symm y).2
    have hc : ((e.symm y : X)⁻¹ * w) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h3 := congrArg Subtype.val (h1 ⟨h, hh⟩)
      simp only [hα₀, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
      calc h * ((e.symm y : X)⁻¹ * w) = (e.symm y : X)⁻¹ * ((e.symm y : X) * h *
            (e.symm y : X)⁻¹) * w := by group
        _ = (e.symm y : X)⁻¹ * (w * h * w⁻¹) * w := by rw [h3]
        _ = ((e.symm y : X)⁻¹ * w) * h := by group
    rw [hcent, Subgroup.mem_bot] at hc
    exact hw (by
      have : w = (e.symm y : X) := by
        calc w = (e.symm y : X) * ((e.symm y : X)⁻¹ * w) := by group
          _ = (e.symm y : X) := by rw [hc, mul_one]
      rw [this]
      exact hk')
  obtain ⟨N₀, hN₀1, hN₀odd, hN₀fix, hN₀norm⟩ :=
    CFSG.QuasithinUnique.Out21.oddNormalFix_of_outer_involution (le_refl 7) hF hα2 hαi
  have hfix : ∀ x : PSL2 F, x ∈ CFSG.QuasithinUnique.Out21.fixSub α ↔ α₀ (e.symm x) = e.symm x := by
    intro x
    rw [CFSG.QuasithinUnique.Out21.mem_fixSub]
    constructor
    · intro h
      apply e.injective
      rw [← hαapp, MulEquiv.apply_symm_apply]
      exact h
    · intro h
      have := hαapp (e.symm x)
      rw [MulEquiv.apply_symm_apply, h, MulEquiv.apply_symm_apply] at this
      exact this
  refine ⟨N₀.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hN₀1 ((Subgroup.map_eq_bot_iff_of_injective N₀ e.symm.injective).1 hbot)
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · rintro n ⟨x, hx, rfl⟩
    have h1 := (hfix x).1 (hN₀fix hx)
    have h2 := congrArg Subtype.val h1
    simp only [hα₀, MulAut.conjNormal_apply] at h2
    have h3 : w * (e.symm x : X) * w⁻¹ = (e.symm x : X) := h2
    calc w * ((e.symm.toMonoidHom x : ↥K) : X) = (w * (e.symm x : X) * w⁻¹) * w := by
          show w * (e.symm x : X) = _
          group
      _ = (e.symm.toMonoidHom x : ↥K) * w := by rw [h3]; rfl
  · intro k hk
    have h1 : α₀ k = k := by
      apply Subtype.ext
      simp only [hα₀, MulAut.conjNormal_apply]
      calc w * (k : X) * w⁻¹ = ((k : X) * w) * w⁻¹ := by rw [hk]
        _ = k := by group
    have h2 : e k ∈ CFSG.QuasithinUnique.Out21.fixSub α := by
      rw [hfix, MulEquiv.symm_apply_apply]
      exact h1
    have h3 := hN₀norm h2
    rw [Subgroup.mem_normalizer_iff] at h3 ⊢
    intro h
    have h4 := h3 (e h)
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_inv]
    exact h4

end E217L27

end CFSG.Quasithin
