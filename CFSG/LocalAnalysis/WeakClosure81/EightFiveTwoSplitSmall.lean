module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem isL2Gp_of_isSpGp_two {Y : Type} [Group Y] {n : ℕ} (h : IsSpGp Y 2 n) : IsL2Gp Y n := by
  obtain ⟨k, hk, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  obtain rfl : k = 1 := by omega
  let r := CFSG.RankThree.GF2n.Stroth80.reindexGL (K := F) CFSG.RankThree.GF2n.Stroth80.sumFinTwo
  let e₂ : ↥(StatedSp 1 F) ≃* ↥(StatedSL 2 F) :=
    (Subgroup.equivMapOfInjective (StatedSp 1 F) r.toMonoidHom r.injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.GF2n.Stroth80.map_reindexGL_statedSp_one)
  let e₃ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F).symm)
  exact ⟨F, hF, hFin, hcard, ⟨(e.trans e₂).trans e₃.symm⟩⟩

theorem isL2Gp_of_isL2WrSymGp_one {Y : Type} [Group Y] {n : ℕ} (h : IsL2WrSymGp Y n 1) :
    IsL2Gp Y n := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  let u : (Fin 1 → Matrix.SpecialLinearGroup (Fin 2) F) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    MulEquiv.funUnique (Fin 1) (Matrix.SpecialLinearGroup (Fin 2) F)
  let f : Matrix.SpecialLinearGroup (Fin 2) F →*
      WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) 1 :=
    SemidirectProduct.inl.comp u.symm.toMonoidHom
  have hf : Function.Bijective f := by
    refine ⟨SemidirectProduct.inl_injective.comp u.symm.injective, fun w => ?_⟩
    refine ⟨u w.left, ?_⟩
    apply SemidirectProduct.ext
    · simp [f]
    · exact Subsingleton.elim _ _
  exact ⟨F, hF, hFin, hcard, ⟨e.trans (MulEquiv.ofBijective f hf).symm⟩⟩

theorem subsingleton_of_isSpGp_zero {Y : Type} [Group Y] {n : ℕ} (h : IsSpGp Y 0 n) :
    Subsingleton Y := by
  obtain ⟨k, hk, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  obtain rfl : k = 0 := by omega
  haveI : Subsingleton (Matrix.GeneralLinearGroup (Fin 0 ⊕ Fin 0) F) :=
    ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  exact e.toEquiv.subsingleton

theorem subsingleton_of_isL2WrSymGp_zero {Y : Type} [Group Y] {n : ℕ} (h : IsL2WrSymGp Y n 0) :
    Subsingleton Y := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  haveI : Subsingleton (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) 0) := by
    refine ⟨fun a b => SemidirectProduct.ext ?_ ?_⟩
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  exact e.toEquiv.subsingleton

theorem one_le_of_isSpGp {Y : Type} [Group Y] {m n : ℕ} (h : IsSpGp Y m n) : 1 ≤ n := by
  obtain ⟨k, hk, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hcard] at h1
  exact Nat.one_le_iff_ne_zero.2 (Nat.one_lt_two_pow_iff.1 h1)

theorem three_le_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (h : IsPSUGp Y m n) :
    3 ≤ m ∧ 1 ≤ n := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  exact ⟨h1.2.2.1, h1.2.1⟩

theorem eq_bot_of_subsingleton_quot {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) (h : Subsingleton (X ⧸ Subgroup.center X)) : S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ∀ g : X, g ∈ Subgroup.center X := fun g =>
    (QuotientGroup.eq_one_iff g).1 (Subsingleton.elim _ _)
  haveI hnormS : S.Normal := ⟨fun n hn g => by
    have h1 := Subgroup.mem_center_iff.1 (hc g) n
    rwa [show g * n * g⁻¹ = n by rw [← h1]; group]⟩
  exact le_bot_iff.1 (hS.pCore_eq_bot ▸ CFSG.LieType.BorelTits.le_pCore 2 hnormS
    (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hS.elemAbelian))

end CFSG.LocalAnalysis.WeakClosure81

end
