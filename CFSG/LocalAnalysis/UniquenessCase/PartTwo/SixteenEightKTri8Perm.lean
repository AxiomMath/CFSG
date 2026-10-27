module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8PermB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V} {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
  {I₁ I₂ : Subgroup (Vtil V₀ V hV)}
  {π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L)}
  {π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)}

theorem s16k_tri8_perm (h : S16gRowCtx D V₀ V L hV)
    (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) {g : MulAut (Vtil V₀ V hV)}
    (hg : g ∈ Mbar D.M V₀ V hV) :
    (I₁.map g.toMonoidHom = I₁ ∧ I₂.map g.toMonoidHom = I₂) ∨
      (I₁.map g.toMonoidHom = I₂ ∧ I₂.map g.toMonoidHom = I₁) := by
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Z : Subgroup (Vtil V₀ V hV) := fixV (lBar V₀ V hV L)
  have hgN : g ∈ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))) :=
    h.mBar_le_normalizer hg
  have hZg : Z.map g.toMonoidHom = Z := s16k_tri8_map_fixV_eq hgN
  have hirr₁ : IsIrrOn H I₁ Z := s16k_tri8_isIrrOn_of_realizes hc.card₁ hc.real₁
  have hirr₂ : IsIrrOn H I₂ Z := s16k_tri8_isIrrOn_of_realizes hc.card₂ hc.real₂
  have hX₁ : IsIrrOn H (I₁.map g.toMonoidHom) Z := s16k_tri8_isIrrOn_map hgN hZg hirr₁
  have hX₂ : IsIrrOn H (I₂.map g.toMonoidHom) Z := s16k_tri8_isIrrOn_map hgN hZg hirr₂
  have hperm₁ : I₁.map g.toMonoidHom = I₁ ∨ I₁.map g.toMonoidHom = I₂ :=
    s16k_tri8_summands_of_irr hc hX₁.2.1 hX₁.1.le hX₁
  have hperm₂ : I₂.map g.toMonoidHom = I₁ ∨ I₂.map g.toMonoidHom = I₂ :=
    s16k_tri8_summands_of_irr hc hX₂.2.1 hX₂.1.le hX₂
  have hne : I₁ ≠ I₂ := by
    intro heq
    have hI₁Z : I₁ ≤ Z := by
      have h := hc.ind₂
      rw [← heq] at h
      rwa [inf_eq_left.mpr le_sup_right] at h
    exact hirr₁.1.ne (le_antisymm hI₁Z hirr₁.1.le).symm
  have hinj : ∀ {A B : Subgroup (Vtil V₀ V hV)},
      A.map g.toMonoidHom = B.map g.toMonoidHom → A = B := by
    intro A B hAB
    exact (MulEquiv.mapSubgroup g).injective (by simpa [MulEquiv.coe_mapSubgroup] using hAB)
  rcases hperm₁ with h₁ | h₁ <;> rcases hperm₂ with h₂ | h₂
  · exact absurd (hinj (h₁.trans h₂.symm)) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (hinj (h₁.trans h₂.symm)) hne

theorem s16k_tri8_fix_of_rk (h : S16gRowCtx D V₀ V L hV)
    (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) {t : MulAut (Vtil V₀ V hV)}
    (ht : t ∈ Mbar D.M V₀ V hV) (ht2 : t ^ 2 = 1)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) :
    I₁.map t.toMonoidHom = I₁ ∧ I₂.map t.toMonoidHom = I₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Z : Subgroup (Vtil V₀ V hV) := fixV (lBar V₀ V hV L)
  rcases s16k_tri8_perm h hc ht with hfix | hswap
  · exact hfix
  · exfalso
    obtain ⟨htI₁, htI₂⟩ := hswap
    have hI₁I₂ : I₁ ⊓ I₂ = Z := by
      refine le_antisymm ?_ (le_inf hc.le₁ hc.le₂)
      intro z hz
      exact hc.ind₁ ⟨hz.1, (le_sup_right : I₂ ≤ Z ⊔ I₂) hz.2⟩
    let φ : ↥I₁ →* Vtil V₀ V hV :=
      { toFun := fun x => (x : Vtil V₀ V hV) * t (x : Vtil V₀ V hV)
        map_one' := by simp
        map_mul' := fun x y => by
          simp only [Subgroup.coe_mul, map_mul]
          ac_rfl }
    have hx2 : ∀ x : Vtil V₀ V hV, x * x = 1 := fun x => by
      simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV x
    have hker_le : φ.ker ≤ Z.subgroupOf I₁ := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hx1 : (x : Vtil V₀ V hV) * t (x : Vtil V₀ V hV) = 1 := hx
      have htx : t (x : Vtil V₀ V hV) = (x : Vtil V₀ V hV) := by
        rw [eq_inv_of_mul_eq_one_right hx1]
        exact inv_eq_of_mul_eq_one_right (hx2 _)
      have hxI₂ : (x : Vtil V₀ V hV) ∈ I₂ := by
        have hmem : t (x : Vtil V₀ V hV) ∈ I₁.map t.toMonoidHom :=
          Subgroup.mem_map_of_mem t.toMonoidHom x.2
        rw [htI₁, htx] at hmem
        exact hmem
      exact hI₁I₂ ▸ ⟨x.2, hxI₂⟩
    have him : φ.range ≤ commSub ⊤ (Subgroup.zpowers t) := by
      rintro y ⟨x, rfl⟩
      change ((x : Vtil V₀ V hV) * t (x : Vtil V₀ V hV)) ∈
        commSub ⊤ (Subgroup.zpowers t)
      have hcomm : (x : Vtil V₀ V hV) * t (x : Vtil V₀ V hV) =
          t (x : Vtil V₀ V hV) * (x : Vtil V₀ V hV)⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right (hx2 (x : Vtil V₀ V hV))]
        exact mul_comm _ _
      rw [hcomm]
      exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, (x : Vtil V₀ V hV),
        Subgroup.mem_top _, rfl⟩
    obtain ⟨f₁, hf₁s, hf₁k, -⟩ := CFSG.Quasithin.FFC.exists_natMap
      (Γ := StatedOmega (StatedQuadPlus 4 K₁)) hc.real₁
    have hf₁ker : f₁.ker = Z.subgroupOf I₁ := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hf₁k u
    have hZidx : rkIdx (Z.subgroupOf I₁) = 8 := by
      unfold rkIdx
      rw [← hf₁ker, Subgroup.index_ker f₁]
      have htop : f₁.range = ⊤ := MonoidHom.range_eq_top.2 hf₁s
      rw [htop]
      have hcard : Nat.card (⊤ : Subgroup (Multiplicative (Fin 4 ⊕ Fin 4 → K₁))) = 2 ^ 8 := by
        rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
          Nat.card_fun (α := Fin 4 ⊕ Fin 4), hc.card₁, Nat.card_eq_fintype_card,
          Fintype.card_sum, Fintype.card_fin]
      rw [hcard]
      exact padicValNat.prime_pow 8
    have hZrk : rk ↥(Z.subgroupOf I₁) = rk ↥Z := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le₁).toEquiv]
    have hrange : rk ↥(φ.range) = rkIdx φ.ker := by
      unfold rk rkIdx
      rw [Subgroup.index_ker φ]
    have h1 : rk ↥(φ.ker) + rkIdx φ.ker = rk ↥I₁ := rk_add_rkIdx φ.ker
    have h2 : rk ↥(Z.subgroupOf I₁) + rkIdx (Z.subgroupOf I₁) = rk ↥I₁ :=
      rk_add_rkIdx (Z.subgroupOf I₁)
    have h3 : rk ↥(φ.ker) ≤ rk ↥Z := by
      have := rk_mono hker_le
      rw [hZrk] at this
      exact this
    have h8 : 8 ≤ rk ↥(φ.range) := by
      rw [hrange]
      omega
    exact absurd (le_trans h8 (rk_mono him)) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
