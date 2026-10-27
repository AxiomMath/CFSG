module

public import CFSG.Quasithin.Vol2.Ch10SecKIVa
public import CFSG.Dihedral.Glauberman.DicksonMaxCases

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.BenderSuzuki.MatrixGroups

theorem eq_of_card_sup_eq_double {G : Type*} [Group G] [Finite G] {B₁ B₂ : Subgroup G}
    [IsSimpleGroup ↥B₁] {n : ℕ} (hn : 2 < n) (h₁ : Nat.card B₁ = n) (h₂ : Nat.card B₂ = n)
    (hs : Nat.card ↥(B₁ ⊔ B₂) = 2 * n) : B₁ = B₂ := by
  have hr : B₂.relIndex (B₁ ⊔ B₂) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := B₂) (K := B₁ ⊔ B₂)
    rw [inf_of_le_left le_sup_right, h₂, hs] at h
    have hn0 : 0 < n := by omega
    nlinarith
  have hle : B₂.relIndex B₁ ≤ 2 := hr ▸ Subgroup.relIndex_le_of_le_right le_sup_left (by omega)
  have hmul := Subgroup.relIndex_mul_card (H := B₂) (K := B₁)
  rw [h₁] at hmul
  have hidx : B₂.relIndex B₁ = 1 := by
    by_contra hne
    have h2 : (B₂.subgroupOf B₁).index = 2 := by
      have h0 : B₂.relIndex B₁ ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        omega
      change B₂.relIndex B₁ = 2
      omega
    have := Subgroup.normal_of_index_eq_two h2
    rcases Subgroup.Normal.eq_bot_or_eq_top (B₂.subgroupOf B₁) with h | h
    · rw [h, Subgroup.index_bot, h₁] at h2
      omega
    · rw [h, Subgroup.index_top] at h2
      omega
  have hB : B₁ ≤ B₂ := Subgroup.relIndex_eq_one.mp hidx
  exact Subgroup.eq_of_le_of_card_ge hB (by rw [h₁, h₂])


theorem dickson_25_cases {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5 ^ 2)
    (L : Subgroup (PSL2MatrixGroup F)) :
    Group.IsSolvable L ∨ L = ⊤ ∨ Nat.card L = 60 ∨ Nat.card L = 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF L with
    h1 | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, ⟨e⟩⟩
  · have := h1.toIsMulCommutative
    exact Or.inl inferInstance
  · exact Or.inl inferInstance
  · have := Dickson.isSolvable_dihedral z
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · exact Or.inr (Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans Dickson.card_alt_five)))
  · left
    have := hN
    have hcomm : commutator L ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    have hNs : Group.IsSolvable N := by
      have := hNel.toIsMulCommutative
      infer_instance
    have hQs : Group.IsSolvable (L ⧸ N) := by
      have : IsMulCommutative (L ⧸ N) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient N
  · have hm2 : m ≤ 2 := Nat.le_of_dvd two_pos hmf
    rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
    · refine Or.inr (Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans ?_)))
      rw [CFSG.Glauberman.Dickson.MaxCases.card_psl2_galoisField' (by norm_num) one_ne_zero]
      norm_num
    · refine Or.inr (Or.inl (Subgroup.eq_top_of_card_eq L ((Nat.card_congr e.toEquiv).trans ?_)))
      have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
        ⟨5, 2, by norm_num, by decide, by norm_num, hF⟩
      rw [CFSG.Glauberman.Dickson.MaxCases.card_psl2_galoisField' (by norm_num) two_ne_zero,
        CFSG.GorensteinWalter.psl2_card_formula F hodd, hF]
  · have hm1 : m = 1 := by
      have := Nat.le_of_dvd two_pos hmf
      omega
    subst hm1
    refine Or.inr (Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans ?_)))
    rw [CFSG.Glauberman.Dickson.MaxCases.card_pgl2_galoisField' one_ne_zero]
    norm_num

theorem sup_eq_top_psl2_25 {Y : Type} [Group Y] [Finite Y] (hY : IsPSL 2 5 2 Y)
    {B₁ B₂ : Subgroup Y} (h₁ : IsAlt 5 ↥B₁) (h₂ : IsAlt 5 ↥B₂) (hne : B₁ ≠ B₂) :
    B₁ ⊔ B₂ = ⊤ := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hY
  let e : Y ≃* PSL2MatrixGroup K :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have c₁ := card_eq_sixty h₁
  have c₂ := card_eq_sixty h₂
  have := isSimpleGroup_of_isAlt h₁
  have eH := (B₁ ⊔ B₂).equivMapOfInjective e.toMonoidHom e.injective
  rcases dickson_25_cases hK ((B₁ ⊔ B₂).map e.toMonoidHom) with hs | htop | h60 | h120
  · exfalso
    obtain ⟨a₁⟩ := h₁
    have : Group.IsSolvable ↥(B₁ ⊔ B₂) :=
      Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective
    have : Group.IsSolvable ↥B₁ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion le_sup_left)
        (Subgroup.inclusion_injective (le_sup_left : B₁ ≤ B₁ ⊔ B₂))
    exact Dickson.not_isSolvable_alt_five
      (Group.isSolvable_of_isSolvable_injective (f := a₁.symm.toMonoidHom) a₁.symm.injective)
  · exact eq_top_of_map_eq_top e htop
  · exfalso
    have hc : Nat.card ↥(B₁ ⊔ B₂) = 60 := (Nat.card_congr eH.toEquiv).trans h60
    exact hne (eq_of_card_sup_eq (hc.trans c₁.symm) (hc.trans c₂.symm))
  · exfalso
    have hc : Nat.card ↥(B₁ ⊔ B₂) = 2 * 60 := (Nat.card_congr eH.toEquiv).trans h120
    exact hne (eq_of_card_sup_eq_double (by norm_num) c₁ c₂ hc)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV
