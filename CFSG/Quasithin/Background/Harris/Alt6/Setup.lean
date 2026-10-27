module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompActions
public import CFSG.Quasithin.H13.GoldschmidtKGAutA6Rank

public section

namespace CFSG.Quasithin.G11.Harris.Alt6

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem m_le_three [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m)
    (e : ↥L ≃* alternatingGroup (Fin 6)) : m ≤ 3 := by
  have : Finite (GLV V) :=
    Finite.of_injective (fun g : GLV V => (g : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have hnorm : ∀ g : GLV V, g ∈ Subgroup.normalizer ((⊥ : Subgroup (GLV V)) : Set (GLV V)) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl; simp
    · intro h1
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [this, h1]; simp
  have hAK : A ≤ Subgroup.normalizer (L : Set (GLV V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => hs.L_normal a (hs.A_le ha) l hl, fun h1 => ?_⟩
    have := hs.L_normal a⁻¹ (Γ.inv_mem (hs.A_le ha)) _ h1
    simpa [mul_assoc] using this
  have h8 := CFSG.Quasithin.H13.A6.factAutA6Rank (GLV V) L ⊥ A (fun g _ => hnorm g)
    (fun g _ => hnorm g) hAK ⟨e.toMonoidHom, e.surjective, fun k => by
      rw [MulEquiv.coe_toMonoidHom, ← e.map_one, e.injective.eq_iff, Subgroup.mem_bot,
        Subtype.ext_iff]
      rfl⟩
    (fun a ha hc => by
      rw [Subgroup.mem_bot]
      refine CFSG.Quasithin.Background.Harris.OrdinaryProofs.eq_one_of_mem_A_centralizes_L hs ha fun l hl => ?_
      have := hc l hl
      rw [Subgroup.mem_bot, mul_inv_eq_one] at this
      exact mul_inv_eq_iff_eq_mul.mp this)
    (fun a ha => by
      rw [Subgroup.mem_bot, ← sq]
      exact hs.A_elem.2 a ha)
  rw [bot_inf_eq, Subgroup.relIndex_bot_left, hs.A_card] at h8
  have : 2 ^ m ≤ 2 ^ 3 := by simpa using h8
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end CFSG.Quasithin.G11.Harris.Alt6
