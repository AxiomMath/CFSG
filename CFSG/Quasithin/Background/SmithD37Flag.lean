module

public import CFSG.Quasithin.Background.SmithD37Fac
public import CFSG.Quasithin.Background.SmithD37RowCls
public import CFSG.Quasithin.Background.SmithD37NB4
public import CFSG.Quasithin.Background.SmithD37Disp

public section

namespace CFSG.Quasithin.SmithD37

theorem isPSL_transfer {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : IsPSL n p f Y) : IsPSL n p f X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem natCard_natMod (F : Type) [Field F] [Fintype F] (d : ℕ) :
    Nat.card (natMod F d) = Nat.card F ^ d := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]

variable {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] [CharP F 2] {d : ℕ}

theorem card_mul_card_fixV_range_le
    (Mm : MatModel L₁ L₂ F d)
    (hd : 0 < d) (hs : IsSimpleGroup ↥L₁) (hnc : ∃ a b : ↥L₁, a * b ≠ b * a)
    (hSQ : SQTKGroup ↥L₁) {n : ℕ} (hL : IsPSL 2 2 n ↥L₁) {Y' Y : Submodule F (Fin d → F)}
    (D : FacStep Y' Y) {P : Subgroup (MulAut U)} (hP : P ≤ stabSub (rowSub Mm Y))
    (hP' : P ≤ stabSub (rowSub Mm Y')) (hE : IsElemAbelian2 P)
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) :
    Nat.card (facAct Mm D hP hP').range * Nat.card ↥(fixV (facAct Mm D hP hP').range) ≤
      Nat.card F ^ d := by
  have hB2 := isPGroup_range_facAct Mm D hP hP' hE.isPGroup
  have hBN := conj_mem_natSub_of_mem_range Mm D hP hP' hPN
  have hHyp := b4Hyp_natSub Mm hd hs hnc hSQ hB2 hBN
  have hQ : ∀ v : natMod F d, v ^ 2 = 1 := fun v => by
    apply Multiplicative.toAdd.injective
    ext i
    simp [pow_two, CharTwo.add_self_eq_zero]
  have hLn : IsPSL 2 2 n ↥(natSub Mm) := isPSL_transfer (natSubEquiv Mm).symm hL
  have h := card_mul_card_fixV_le_of_psl hQ hHyp hLn le_sup_right
    (isElemAbelian2_range_facAct Mm D hP hP' hE)
  rwa [natCard_natMod] at h

theorem card_fixV_flag
    (Mm : MatModel L₁ L₂ F d) (hd : 0 < d)
    (hs : IsSimpleGroup ↥L₁) (hnc : ∃ a b : ↥L₁, a * b ≠ b * a) (hSQ : SQTKGroup ↥L₁)
    {n : ℕ} (hL : IsPSL 2 2 n ↥L₁) {P : Subgroup (MulAut U)} (hE : IsElemAbelian2 P)
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) :
    ∀ (k : ℕ) (Y : Submodule F (Fin d → F)), Module.finrank F Y = k →
      IsInvBy P (rowSub Mm Y) →
      Nat.card ↥(rowSub Mm Y ⊓ fixV P) * Nat.card P ^ k ≤
        Nat.card F ^ (d * k) * Nat.card ↥(P ⊓ Subgroup.centralizer L₁) ^ k := by
  intro k
  induction k with
  | zero =>
    intro Y hY _
    rw [Submodule.finrank_eq_zero.mp hY, rowSub_bot, bot_inf_eq, Subgroup.card_bot]
    simp
  | succ k ih =>
    intro Y hY hinv
    have hY0 : Y ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hY
      omega
    obtain ⟨Y', hY'le, hrank, hinv'⟩ := exists_hyperplane_inv Mm hE.isPGroup hPN hinv hY0
    obtain ⟨D⟩ := exists_facStep hY'le hrank
    have hP := le_stabSub_of_isInvBy hinv
    have hP' := le_stabSub_of_isInvBy hinv'
    have h1 := card_fixV_le_facAct Mm D hP hP'
    have h2 := card_mul_card_fixV_range_le Mm hd hs hnc hSQ hL D hP hP' hE hPN
    have h3 := card_range_facAct_mul Mm D hP hP' hPN hE.isPGroup
    have h4 := ih Y' (by omega) hinv'
    set c := Nat.card ↥(P ⊓ Subgroup.centralizer L₁)
    set b := Nat.card (facAct Mm D hP hP').range
    set f := Nat.card ↥(fixV (facAct Mm D hP hP').range)
    calc Nat.card ↥(rowSub Mm Y ⊓ fixV P) * Nat.card P ^ (k + 1)
        = Nat.card ↥(rowSub Mm Y ⊓ fixV P) * Nat.card P ^ k * (b * c) := by
          rw [h3, pow_succ, mul_assoc]
      _ ≤ (Nat.card ↥(rowSub Mm Y' ⊓ fixV P) * f) * Nat.card P ^ k * (b * c) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ = (Nat.card ↥(rowSub Mm Y' ⊓ fixV P) * Nat.card P ^ k) * (b * f) * c := by ring
      _ ≤ (Nat.card F ^ (d * k) * c ^ k) * Nat.card F ^ d * c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul h4 h2)
      _ = Nat.card F ^ (d * (k + 1)) * c ^ (k + 1) := by ring

end CFSG.Quasithin.SmithD37
