module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G28
public import CFSG.Quasithin.Vol2.Ch10SecC9C3
public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecC9Diag

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem fsuUL_inf_centralizer_ne_bot (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1) (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) (hcv : fsuCVM T L I ≠ ⊥) :
    fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1C, hV2C, -⟩ := hdec t ht htn
  obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcv
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hcomm : ∀ a ∈ fsuUL T L I, ∀ b ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV (hV1V ha)
      (commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 ht).trans
        (SecA.fsuL0_le_normalizer_fsuVM T L I)) hb)
  have hcV : c ∈ fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := hVeq ▸ hc.1
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mul_of_mem_sup hcomm hcV
  have hcL0 : ∀ x ∈ fsuL0 T L, x * (v₁ * v₂) = v₁ * v₂ * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hc.2 x hx
  by_cases h1 : v₁ = 1
  ·
    subst h1
    rw [one_mul] at hc1' hcL0
    have hv₂' : t * v₂ * t⁻¹ ∈ fsuUL T L I := by
      rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L ht),
        SecA.mem_conjugate_iff] at hv₂
      exact hv₂
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨t * v₂ * t⁻¹, hv₂', ?_⟩, ?_⟩
    · show t * v₂ * t⁻¹ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlt : t⁻¹ * l * t ∈ fsuL0 T L := SecA.conjugate_le_fsuL0 ht (by
        rw [SecA.mem_conjugate_iff]; simpa [mul_assoc] using hl)
      have h2 := hcL0 _ hlt
      calc l * (t * v₂ * t⁻¹) = t * ((t⁻¹ * l * t) * v₂) * t⁻¹ := by group
        _ = t * (v₂ * (t⁻¹ * l * t)) * t⁻¹ := by rw [h2]
        _ = t * v₂ * t⁻¹ * l := by group
    · intro h
      apply hc1'
      have := congrArg Subtype.val h
      calc v₂ = t⁻¹ * (t * v₂ * t⁻¹) * t := by group
        _ = 1 := by rw [show t * v₂ * t⁻¹ = 1 from this]; group
  ·
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨v₁, hv₁, ?_⟩, fun h => h1
      (congrArg Subtype.val h)⟩
    show v₁ ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := hcL0 l (SecA.le_fsuL0 T L hl)
    have h3 : l * v₂ = v₂ * l := Subgroup.mem_centralizer_iff.mp (hV2C hv₂) l hl
    have h4 : l * v₁ * v₂ = v₁ * l * v₂ := by
      calc l * v₁ * v₂ = l * (v₁ * v₂) := by group
        _ = v₁ * v₂ * l := h2
        _ = v₁ * (v₂ * l) := by group
        _ = v₁ * (l * v₂) := by rw [h3]
        _ = v₁ * l * v₂ := by group
    exact mul_right_cancel h4

theorem Conf.exists_eA (c : Conf T L I t w J) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1026 : Stmt10_2_6) (h1028 : Stmt10_2_8) (hL : LBarL32 L) (hcv : fsuCVM T L I ≠ ⊥) :
    Nonempty (↥(autOn (fsuL0 T L ⊔ T) (fsuVM T L I) ⊓
        MulAction.stabilizer (MulAut ↥(fsuVM T L I)) (⟨w, c.w_mem_V⟩ : ↥(fsuVM T L I))) ≃*
      (A4 × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
  have hyp := c.hyp
  have h3 := case3_of hyp h1012 hL hcv
  have hne := fsuUL_inf_centralizer_ne_bot hyp h1011 c.ht c.htn hcv
  have hV1 : ⁅fsuVM T L I, L⁆ ≤ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 c.ht).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I))
  obtain ⟨U₁, hU₁⟩ := exists_isU hyp hV1
  obtain ⟨U₂, hU₂⟩ := exists_isU hyp hV2
  obtain ⟨R₁, hR₁⟩ := exists_isR (T := T) (I := I) L U₁
  obtain ⟨R₂, hR₂⟩ := exists_isR (T := T) (I := I) (CFSG.conjugate L t) U₂
  have hwU₂ : w ∈ U₂ := (hU₂.2 w c.claim.1).mpr (c.claim.2.2.2.2.2 h3)
  have hwL0 : w ∉ Subgroup.centralizer (fsuL0 T L : Set G) := fun h => c.claim.2.2.1
    (centralizer_le_of_mem_fsuCVM_case3 h1026 h1028 hyp hL hne ⟨c.w_mem_V, h⟩ c.w_ne_one)
  exact ((h1028 G T L I hyp hL hne).2.2.2.2 t c.ht c.htn U₁ U₂ R₁ R₂ hU₁ hU₂ hR₁ hR₂
    ⟨w, c.w_mem_V⟩ hwU₂ hwL0).1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
