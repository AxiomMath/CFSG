module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem CFSG.LieType.Universal
  CFSG.LieType.Chevalley.CosetBuilding

@[expose] def PhanEClassifiedAt (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] {n : ℕ}
    (M : CoxeterMatrix (Fin n)) {C : Type} (δ : C → C → M.Group) (t : C → C) : Prop :=
  (∀ (J : Set (Fin n)) (x : C), J.ncard = 2 → ∃ code : PhanCode, code.rank = 2 ∧
    Nonempty (ChamberIso
      (inducedSystem M.toCoxeterSystem δ J (flipMaxSet M.toCoxeterSystem δ t J x))
      ((code.sys K).restrict (code.set K f)))) ∧
  (∀ (J : Set (Fin n)) (x : C), J.ncard = 3 → ∃ code : PhanCode, code.rank = 3 ∧
    Nonempty (ChamberIso
      (inducedSystem M.toCoxeterSystem δ J (flipMaxSet M.toCoxeterSystem δ t J x))
      ((code.sys K).restrict (code.set K f))))

@[expose] def PhanEConfig.Classified {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}
    {M : CoxeterMatrix (Fin n)} {G : Type} [Group G] (c : PhanEConfig K f M G) : Prop :=
  PhanEClassifiedAt K f M c.δ c.t

section Certified


@[expose] def PhanEClassified (cfg : PhanEConfigChoice) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f),
    (cfg K f hK hq).e6.Classified ∧ (cfg K f hK hq).e7.Classified ∧
      (cfg K f hK hq).e8.Classified

end Certified

@[expose] def PhanModelsRank2 (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] : Prop :=
  ∀ code : PhanCode, code.rank = 2 → ((code.sys K).restrict (code.set K f)).Connected

@[expose] def PhanModelsRank3 (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] : Prop :=
  ∀ code : PhanCode, code.rank = 3 →
    ((code.sys K).restrict (code.set K f)).Connected ∧
      ((code.sys K).restrict (code.set K f)).SimplyTwoConnected

@[expose] def PhanEModels : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2], Nat.card K = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f →
    PhanModelsRank2 K f ∧ PhanModelsRank3 K f

theorem PhanEConfig.localConnected_of_classified {K : Type} [Field K] [Finite K] {f : ℕ}
    [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)} {G : Type} [Group G]
    (c : PhanEConfig K f M G) (hc : c.Classified) (h2 : PhanModelsRank2 K f)
    (h3 : PhanModelsRank3 K f) : c.LocalConnected := by
  refine ⟨fun J x hJ => ?_, fun J x hJ => ?_⟩
  · obtain ⟨code, hr, ⟨iso⟩⟩ := hc.1 J x hJ
    exact iso.connected_iff.2 (h2 code hr)
  · obtain ⟨code, hr, ⟨iso⟩⟩ := hc.2 J x hJ
    obtain ⟨hconn, hsc⟩ := h3 code hr
    exact ⟨iso.connected_iff.2 hconn, iso.simplyTwoConnected_iff.2 hsc⟩

section Glue


theorem phanELocal_of_parts (cfg : PhanEConfigChoice) (h1 : PhanEClassified cfg)
    (h2 : PhanEModels) : PhanELocal cfg := by
  intro K _ _ f _ hK hq
  obtain ⟨c6, c7, c8⟩ := h1 K f hK hq
  obtain ⟨m2, m3⟩ := h2 K f hK hq
  exact ⟨PhanEConfig.localConnected_of_classified _ c6 m2 m3,
    PhanEConfig.localConnected_of_classified _ c7 m2 m3,
    PhanEConfig.localConnected_of_classified _ c8 m2 m3⟩

end Glue

end CFSG.ClassicalInvolution.Phan.PhanE

end
