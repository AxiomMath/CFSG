module

public import CFSG.Quasithin.MS93.S37Rho

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem card_ringHom_le {F : Type} [Field F] [Fintype F] [CharP F 2] {k : ℕ}
    (hF : Fintype.card F = 2 ^ k) : Nat.card (F →+* F) ≤ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let e : (F →ₐ[ZMod 2] F) ≃ (F →+* F) :=
    { toFun := fun f => f.toRingHom
      invFun := fun σ =>
        { σ with
          commutes' := fun r => by
            have := RingHom.ext_zmod (σ.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)
            exact congrArg (fun f => f r) this }
      left_inv := fun f => by ext; rfl
      right_inv := fun σ => by ext; rfl }
  rw [← Nat.card_congr e]
  have h1 := card_algHom_le_finrank (ZMod 2) F F
  have h2 : Module.finrank (ZMod 2) F = k := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF, ZMod.card] at this
    exact (Nat.pow_right_injective le_rfl this).symm
  omega

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem act_semi {x : G} (hx : x ∈ M) :
    ∃ σ : F →+* F, ∀ (c : F) (v : V4 F), C.act hx (c • v) = σ c • C.act hx v :=
  C.N.act_semilinear C.hMU C.hMA C.h.L_le C.h.le_normalizer hx

noncomputable def sig {x : G} (hx : x ∈ M) : F →+* F := Classical.choose (C.act_semi hx)

theorem sig_spec {x : G} (hx : x ∈ M) (c : F) (v : V4 F) :
    C.act hx (c • v) = C.sig hx c • C.act hx v :=
  Classical.choose_spec (C.act_semi hx) c v

theorem sig_unique {x : G} (hx : x ∈ M) {τ : F →+* F}
    (hτ : ∀ (c : F) (v : V4 F), C.act hx (c • v) = τ c • C.act hx v) : τ = C.sig hx := by
  ext c
  obtain ⟨v₀, hv₀⟩ := (C.N.act_bijective C.hMU C.hMA hx).2 (Pi.single (.inl 0) 1)
  have h1 := hτ c v₀
  rw [C.sig_spec, hv₀] at h1
  have h2 : (τ c - C.sig hx c) • (Pi.single (.inl 0) 1 : V4 F) = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd (congrFun h (.inl 0)) (by simp)

theorem sig_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    C.sig (M.mul_mem hx hy) = (C.sig hx).comp (C.sig hy) := by
  symm
  refine C.sig_unique _ fun c v => ?_
  have h1 := fun w => congrArg (fun f => f w) (C.N.act_mul C.hMU C.hMA hx hy)
  simp only [AddMonoidHom.comp_apply] at h1
  rw [show C.act (M.mul_mem hx hy) = C.N.act C.hMU C.hMA (M.mul_mem hx hy) from rfl, h1, h1,
    show C.N.act C.hMU C.hMA hy = C.act hy from rfl, C.sig_spec hy,
    show C.N.act C.hMU C.hMA hx = C.act hx from rfl, C.sig_spec hx]
  rfl

theorem linear_iff {x : G} (hx : x ∈ M) :
    (∀ (c : F) (v : V4 F), C.act hx (c • v) = c • C.act hx v) ↔ C.sig hx = RingHom.id F :=
  ⟨fun h => (C.sig_unique hx (τ := RingHom.id F) h).symm, fun h c v => by
    rw [C.sig_spec, h]
    rfl⟩

end Cfg

end CFSG.Quasithin.MS93.S37
