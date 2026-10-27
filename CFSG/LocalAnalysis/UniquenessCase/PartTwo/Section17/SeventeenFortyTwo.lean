module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem Concl17_42.of_p1 {D : Data G} {L X : Subgroup G} {p : ℕ}
    (h : P17_42_1 D X) : Concl17_42 D L X p := Or.inl h

theorem Concl17_42.of_p4 {D : Data G} {L X : Subgroup G} {p : ℕ}
    (h : P17_42_4 D X p) : Concl17_42 D L X p := Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem Concl17_42.of_p5 {D : Data G} {L X : Subgroup G} {p : ℕ}
    (h : P17_42_5 D X p) : Concl17_42 D L X p := Or.inr (Or.inr (Or.inr (Or.inr h)))

private theorem exists_cosetReps {H K : Subgroup G} : ∃ Γ : Set G, CIsCosetReps H K Γ := by
  obtain ⟨T, hT, -⟩ := exists_isComplement_right (H.subgroupOf K) 1
  refine ⟨Subtype.val '' T, by rintro _ ⟨t, -, rfl⟩; exact t.2, fun k hk => ?_⟩
  obtain ⟨⟨⟨h, hh⟩, ⟨t, ht⟩⟩, hx, huniq⟩ := hT.existsUnique ⟨k, hk⟩
  refine ⟨t, ⟨⟨t, ht, rfl⟩, h, hh, congrArg Subtype.val hx.symm⟩, ?_⟩
  rintro _ ⟨⟨t', ht', rfl⟩, h', hh', rfl⟩
  have hh'K : h' ∈ K := by simpa using K.mul_mem hk (K.inv_mem t'.2)
  have := huniq ⟨⟨⟨h', hh'K⟩, hh'⟩, ⟨t', ht'⟩⟩ rfl
  simp_all

theorem exists_ctx17_42 {D : Data G} {V₀ V L X : Subgroup G} {p : ℕ}
    (hV : Hyp125 D V₀ V) (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hp : p ∈ D.sig) (hcounter : ¬ Concl17_42 D L X p)
    {n : ℕ} (hchev : CIsChevOver (BarInf L) n)
    {C : Subgroup G} (hcartan : CIsCartanOf D.T L C) :
    ∃ (l : ℕ) (Dc : Subgroup G) (Gamma : Set G), Ctx17_42 D V₀ V L X p n l C Dc Gamma := by
  obtain ⟨t, m, hadm, hmodel⟩ := hchev
  obtain ⟨Gamma, hreps⟩ := exists_cosetReps
    (H := (D.M ⊓ normalizer ((D.T ⊓ X : Set G))) ⊓ normalizer (L : Set G))
    (K := D.M ⊓ normalizer ((D.T ⊓ X : Set G)))
  exact ⟨CS17LieRank t m, ⨆ x ∈ Gamma, CFSG.Quasithin.conjSubgroup C x, Gamma,
    ⟨hV, hL, hX, hp, hcounter, ⟨t, m, hadm, hmodel⟩,
      ⟨t, m, hadm, hmodel, rfl⟩, hcartan, hreps, rfl⟩⟩

theorem Ctx17_42.L_le_M_of_ctx {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (hC : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    L ≤ D.M :=
  CFSG.Open.IsSubnormal.le hC.mem_calC.1

theorem Ctx17_42.C_le_M_of_ctx {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (hC : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    C ≤ D.M :=
  hC.cartan.1.trans hC.L_le_M_of_ctx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
