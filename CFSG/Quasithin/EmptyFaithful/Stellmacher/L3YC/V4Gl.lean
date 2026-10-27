module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.V4Aut

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

section Gl2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mat2_cube_mem : ∀ R A : Matrix (Fin 2) (Fin 2) (ZMod 2),
    R * R * R = 1 → R ≠ 1 → A * A * A = 1 → A = 1 ∨ A = R ∨ A = R * R := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mat2_comm_mem : ∀ R A A' : Matrix (Fin 2) (Fin 2) (ZMod 2),
    R * R * R = 1 → R ≠ 1 → A * A' = 1 → A * R = R * A → A = 1 ∨ A = R ∨ A = R * R := by
  decide +kernel

theorem gl2_cube_mem (ρ a : GL (Fin 2) (ZMod 2)) (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1) (ha : a ^ 3 = 1) :
    a = 1 ∨ a = ρ ∨ a = ρ ^ 2 := by
  have h1 : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) * ρ * ρ = 1 := by
    have := congrArg (fun u : GL (Fin 2) (ZMod 2) => (u : Matrix (Fin 2) (Fin 2) (ZMod 2))) hρ3
    simpa [pow_three', Units.val_mul] using this
  have h2 : (a : Matrix (Fin 2) (Fin 2) (ZMod 2)) * a * a = 1 := by
    have := congrArg (fun u : GL (Fin 2) (ZMod 2) => (u : Matrix (Fin 2) (Fin 2) (ZMod 2))) ha
    simpa [pow_three', Units.val_mul] using this
  have h3 : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1 := fun h => hρ1 (Units.ext h)
  rcases mat2_cube_mem _ _ h1 h3 h2 with h | h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Or.inl (Units.ext h))
  · exact Or.inr (Or.inr (Units.ext (by simpa [pow_two] using h)))

theorem gl2_comm_mem (ρ a : GL (Fin 2) (ZMod 2)) (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1)
    (ha : a * ρ = ρ * a) : a = 1 ∨ a = ρ ∨ a = ρ ^ 2 := by
  have h1 : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) * ρ * ρ = 1 := by
    have := congrArg (fun u : GL (Fin 2) (ZMod 2) => (u : Matrix (Fin 2) (Fin 2) (ZMod 2))) hρ3
    simpa [pow_three', Units.val_mul] using this
  have h3 : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1 := fun h => hρ1 (Units.ext h)
  have h4 : (a : Matrix (Fin 2) (Fin 2) (ZMod 2)) * (a⁻¹ : GL (Fin 2) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h5 : (a : Matrix (Fin 2) (Fin 2) (ZMod 2)) * ρ = ρ * a := by
    have := congrArg (fun u : GL (Fin 2) (ZMod 2) => (u : Matrix (Fin 2) (Fin 2) (ZMod 2))) ha
    simpa [Units.val_mul] using this
  rcases mat2_comm_mem _ _ _ h1 h3 h4 h5 with h | h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Or.inl (Units.ext h))
  · exact Or.inr (Or.inr (Units.ext (by simpa [pow_two] using h)))

end Gl2

theorem card_gl2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  have := CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 2
  rw [this]
  decide

section Action

variable {G : Type} [Group G] [Finite G]

theorem exists_gl_action {V : Subgroup G} (hV4 : Nat.card V = 4) (hsq : ∀ a ∈ V, a * a = 1) :
    ∃ Φ : ↥(Subgroup.normalizer (V : Set G)) →* GL (Fin 2) (ZMod 2),
      ∀ g : ↥(Subgroup.normalizer (V : Set G)),
        Φ g = 1 ↔ ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 2)
    (W := ↥V) (comm_of_sq_one hsq)
    (fun a => by rw [pow_two]; exact Subtype.ext (hsq _ a.2)) (by rw [hV4]; norm_num)
  refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp V.normalizerMonoidHom,
    fun g => ?_⟩
  show (CFSG.SectionRank.Ccomm.elemAutEquivGL e) (V.normalizerMonoidHom g) = 1 ↔ _
  rw [map_eq_one_iff _ (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective]
  exact actAut_eq_one_iff g.2

end Action

end Stellmacher.L3YC

end CFSG.Quasithin
