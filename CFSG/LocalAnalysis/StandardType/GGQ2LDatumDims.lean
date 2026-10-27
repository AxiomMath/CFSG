module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2LD_finrank_sup {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x)
    (hx : M.xV ∉ M.coSpan)
    (hsup : M.coSpan ⊔ Submodule.span (ZMod p) {M.xV} = ⊤) :
    Module.finrank (ZMod p) M.V = Module.finrank (ZMod p) M.coSpan + 1 := by
  have hfdH : FiniteDimensional (ZMod p) M.coSpan := by
    rw [GGQ2LDatum.coSpan]
    exact Module.Finite.span_of_finite (ZMod p) (Set.finite_range M.coroot)
  have hfdS : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) {M.xV}) :=
    Module.Finite.span_of_finite (ZMod p) (Set.finite_singleton M.xV)
  have hx0 : M.xV ≠ 0 := fun h => hx (h ▸ M.coSpan.zero_mem)
  have hdisj : M.coSpan ⊓ Submodule.span (ZMod p) {M.xV} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvH, hvS⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hvS
    rw [← hc] at hvH
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · exact absurd (by
        have hxx : M.xV = c⁻¹ • (c • M.xV) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hxx]
        exact Submodule.smul_mem _ _ hvH) hx
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq M.coSpan
    (Submodule.span (ZMod p) {M.xV})
  have hspan : Module.finrank (ZMod p) (Submodule.span (ZMod p) {M.xV}) = 1 :=
    finrank_span_singleton hx0
  rw [hsup, hdisj, finrank_top, finrank_bot, hspan, add_zero] at hfin
  exact hfin

theorem ggQ2LD_dim_nonheart {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x)
    (h : M.ShapeFull ∨ M.ShapeA ∨ M.ShapeC) :
    Module.finrank (ZMod p) M.V = Fintype.card M.Λ + 1 := by
  rcases h with hFull | hA | hC
  · obtain ⟨-, hLI, hxVn, hsup⟩ := hFull
    have hco : Module.finrank (ZMod p) M.coSpan = Fintype.card M.Λ :=
      finrank_span_eq_card hLI
    rw [ggQ2LD_finrank_sup M hxVn hsup, hco]
  · exact hA.2.2.2.1
  · exact hC.2.2.2.1

theorem ggQ2LD_dim_heart {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) (h : M.HeartShape) :
    Module.finrank (ZMod p) M.V = Fintype.card M.Λ := by
  rcases h with hB | hD
  · obtain ⟨-, hco1, hxVn, hsup⟩ := hB
    rw [ggQ2LD_finrank_sup M hxVn hsup]
    exact hco1
  · obtain ⟨-, hLI, htop⟩ := hD
    rw [← finrank_top (ZMod p) M.V, ← htop]
    exact finrank_span_eq_card hLI

theorem ggQ2LD_card_lie {lab : LargeEvenLabel} {ι : Type} [Fintype ι]
    {M : CoxeterMatrix ι} (h : GGQ2LabelWeyl lab M) (hlab : GGQ2TBLabel lab) :
    Fintype.card ι = GGQ2LieRank lab := by
  unfold GGQ2TBLabel at hlab
  rcases hlab with hA | hBC | hD | htwD | hF4 | htwE6 | hE7 | hE8
  · obtain ⟨htag, -⟩ := hA
    simp only [GGQ2LabelWeyl, htag] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htag]
  · obtain ⟨htag | htag, -⟩ := hBC
    · simp only [GGQ2LabelWeyl, htag] at h
      obtain ⟨e, -⟩ := h
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
      simp [GGQ2LieRank, htag]
    · simp only [GGQ2LabelWeyl, htag] at h
      obtain ⟨e, -⟩ := h
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
      simp [GGQ2LieRank, htag]
  · obtain ⟨htag, -⟩ := hD
    simp only [GGQ2LabelWeyl, htag] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htag]
  · obtain ⟨htag, -⟩ := htwD
    simp only [GGQ2LabelWeyl, htag] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htag]
  · simp only [GGQ2LabelWeyl, hF4] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, hF4]
  · simp only [GGQ2LabelWeyl, htwE6] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htwE6]
  · simp only [GGQ2LabelWeyl, hE7] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, hE7]
  · simp only [GGQ2LabelWeyl, hE8] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, hE8]

theorem ggQ2LD_finrank_le_card_succ {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) (hsh : M.Shape) :
    Module.finrank (ZMod p) M.V ≤ Fintype.card M.Λ + 1 := by
  rcases hsh with hF | hA | hB | hC | hD
  · rw [ggQ2LD_dim_nonheart M (Or.inl hF)]
  · rw [ggQ2LD_dim_nonheart M (Or.inr (Or.inl hA))]
  · rw [ggQ2LD_dim_heart M (Or.inl hB)]; omega
  · rw [ggQ2LD_dim_nonheart M (Or.inr (Or.inr hC))]
  · rw [ggQ2LD_dim_heart M (Or.inr hD)]; omega

end CFSG.StandardType

end
