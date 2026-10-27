module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Ctx

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique CFSG.Blueprint
  CFSG.Quasithin.H13.F431.SpModel

namespace F45

structure SpGeomFacts (F : Type) [Field F] [Finite F] [CharP F 2] {V : Type}
    [MulAction (antiSp F) V] (Γ : SimpleGraph V) (p l : V) : Prop where
  poly : IsGenPolygon Γ 4
  adj : Γ.Adj p l
  disj : ∀ y z : antiSp F, y • p ≠ z • l
  noadj_p : ∀ y z : antiSp F, ¬ Γ.Adj (y • p) (z • p)
  noadj_l : ∀ y z : antiSp F, ¬ Γ.Adj (y • l) (z • l)
  stab_p : ∀ y : antiSp F, y • p = p ↔ y ∈ Subgroup.normalizer (radA2 F : Set (antiSp F))
  stab_l : ∀ y : antiSp F, y • l = l ↔ y ∈ Subgroup.normalizer (radA1 F : Set (antiSp F))
  three_p : 3 ≤ Nat.card (Γ.neighborSet p)
  three_l : 3 ≤ Nat.card (Γ.neighborSet l)
  base_p : ModelBase Γ 4 p (radA2 F)
  base_l : ModelBase Γ 4 l (radA1 F)

@[expose] def SpGeomProp (F : Type) [Field F] [Finite F] [CharP F 2] : Prop :=
  ∃ (V : Type) (_ : MulAction (antiSp F) V) (Γ : SimpleGraph V) (_ : GraphAction (antiSp F) Γ)
    (p l : V), SpGeomFacts F Γ p l

open SpOut2 in
theorem facts45L_of_spGeom {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f)
    (A : LieAmalgamExt D) (hfin : Finite D)
    (hG : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], SpGeomProp F) :
    (A.setting hfin (polyNumber .PSp) (three_le_polyNumber .PSp)).Facts45L := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ψ, k₀, R, i, hP, hDd, hN, hRi, hψ, hΦr⟩ :=
    exists_f45Ctx hD A
  obtain ⟨V, hact, Γ, hgact, p, l, hF⟩ := hG F
  have hst_p : MulAction.stabilizer (antiSp F) p =
      Subgroup.normalizer (radA2 F : Set (antiSp F)) := by
    ext y
    rw [MulAction.mem_stabilizer_iff]
    exact hF.stab_p y
  have hst_l : MulAction.stabilizer (antiSp F) l =
      Subgroup.normalizer (radA1 F : Set (antiSp F)) := by
    ext y
    rw [MulAction.mem_stabilizer_iff]
    exact hF.stab_l y
  rcases hRi with ⟨hR, -⟩ | ⟨hR, -⟩
  · subst hR
    have hQ1 : pCoreOf 2 (MulAction.stabilizer (antiSp F) l) = radA1 F := by
      rw [hst_l]
      exact hDd.borel.core₁
    have hQ2 : pCoreOf 2 (MulAction.stabilizer (antiSp F) p) = radA2 F := by
      rw [hst_p]
      exact hDd.borel.core₂
    have X := xdatum_of_ctx A hfin (polyNumber .PSp) (three_le_polyNumber .PSp) Φ ψ k₀ (Rrad F)
      hP hN hψ hΦr Γ l p hF.stab_l hF.stab_p (fun y z => (hF.disj z y).symm) hF.noadj_l
      hF.noadj_p hF.adj.symm
    exact facts45L_of_model X hF.poly hF.three_l hF.three_p (radA1 F) (radA2 F) hQ1 hQ2
      hF.base_l hF.base_p
  · subst hR
    have hQ1 : pCoreOf 2 (MulAction.stabilizer (antiSp F) p) = radA2 F := by
      rw [hst_p]
      exact hDd.borel.core₁
    have hQ2 : pCoreOf 2 (MulAction.stabilizer (antiSp F) l) = radA1 F := by
      rw [hst_l]
      exact hDd.borel.core₂
    have X := xdatum_of_ctx A hfin (polyNumber .PSp) (three_le_polyNumber .PSp) Φ ψ k₀
      ![radA2 F, radA1 F] hP hN hψ hΦr Γ p l hF.stab_p hF.stab_l hF.disj hF.noadj_p hF.noadj_l
      hF.adj
    exact facts45L_of_model X hF.poly hF.three_p hF.three_l (radA2 F) (radA1 F) hQ1 hQ2
      hF.base_p hF.base_l

end F45

end CFSG.Quasithin.H13.F431
