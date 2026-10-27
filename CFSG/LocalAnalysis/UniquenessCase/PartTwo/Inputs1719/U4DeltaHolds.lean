module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4U5Delta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicTransport
public import CFSG.Quasithin.H13.U4ParPointStable
public import CFSG.Quasithin.H13.U4ParYAmalgam
public import CFSG.Quasithin.H13.U4ParTorusPrime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2TwoAutInnerHolds
public import CFSG.Quasithin.Background.E6Hyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.U4Par
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped Pointwise commutatorElement

private theorem map_aut_eq_of_map_eq {G Y : Type} [Group G] [Group Y] {φ : G ≃* Y}
    {r : MulAut Y} {X : Subgroup G} {T : Subgroup Y} (hφ : X.map φ.toMonoidHom = T)
    (hr : T.map r.toMonoidHom = T) :
    X.map ((φ.trans r).trans φ.symm).toMonoidHom = X := by
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  rw [Subgroup.map_map]
  have hcomp : φ.toMonoidHom.comp ((φ.trans r).trans φ.symm).toMonoidHom =
      r.toMonoidHom.comp φ.toMonoidHom := by
    ext x
    simp [MulEquiv.trans_apply]
  rw [hcomp, ← Subgroup.map_map, hφ, hr]

section Model

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

private theorem isSylowIn_hypUnitriangular :
    IsSylowIn 2 (hypUnitriangular h 2 0) ⊤ := by
  obtain ⟨P, hP⟩ :=
    (unitary_order_and_Sylow (r := 2) (ε := 0) h (by norm_num) (by norm_num)).2.1
  rw [← hP]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

private theorem isMaxParabolicOver_parP_map {Y : Type} [Group Y]
    (φ : hypSU h 2 0 ≃* Y) :
    IsMaxParabolicOver (⊤ : Subgroup Y) ((hypUnitriangular h 2 0).map φ.toMonoidHom)
      ((parP h).map φ.toMonoidHom) := by
  have hN : Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) ≤ parP h := by
    rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
    exact UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num)
  exact isMaxParabolicOver_top_map φ
    (isMaxParabolicOver_top_of_isCoatom (isCoatom_parP h) hN)

private theorem opp_parP_map {Y : Type} [Group Y] (hn : 2 ≤ n)
    (φ : hypSU h 2 0 ≃* Y) :
    Opp 2 ((parP h).map φ.toMonoidHom) = (perfectCore (parP h)).map φ.toMonoidHom := by
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hU : IsSylowIn 2 (hypUnitriangular h 2 0) ⊤ := isSylowIn_hypUnitriangular h
  have hUP : hypUnitriangular h 2 0 ≤ parP h :=
    (hypUnitriangular_le_perfectCore_parP h hn).trans (perfectCore_le _)
  have hS : IsSylowIn 2 (hypUnitriangular h 2 0) (parP h) :=
    CFSG.Quasithin.E6.isSylowIn_of_le hU hUP le_top
  have hOpp : Opp 2 (parP h) = perfectCore (parP h) :=
    S17.opp_eq_of_isSimpleGroup_bar2 (perfectCore_le _) (parP_le_normalizer_perfectCore h)
      hS (hypUnitriangular_le_perfectCore_parP h hn)
      (isSimpleGroup_modO2_perfectCore_parP h hn) (two_dvd_card_modO2_perfectCore_parP h hn)
  calc Opp 2 ((parP h).map φ.toMonoidHom)
      = (Opp 2 (parP h)).map φ.toMonoidHom := S17.opp_map φ 2 (parP h)
    _ = (perfectCore (parP h)).map φ.toMonoidHom := by rw [hOpp]

private theorem commutator_opp_parP_map {Y : Type} [Group Y] (hn : 2 ≤ n)
    (φ : hypSU h 2 0 ≃* Y) :
    ⁅Opp 2 ((parP h).map φ.toMonoidHom), Opp 2 ((parP h).map φ.toMonoidHom)⁆ =
      Opp 2 ((parP h).map φ.toMonoidHom) := by
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  calc ⁅Opp 2 ((parP h).map φ.toMonoidHom), Opp 2 ((parP h).map φ.toMonoidHom)⁆
      = ⁅(perfectCore (parP h)).map φ.toMonoidHom,
          (perfectCore (parP h)).map φ.toMonoidHom⁆ := by rw [opp_parP_map h hn φ]
    _ = (⁅perfectCore (parP h), perfectCore (parP h)⁆).map φ.toMonoidHom :=
        (Subgroup.map_commutator (H₁ := perfectCore (parP h)) (H₂ := perfectCore (parP h))
          (f := φ.toMonoidHom)).symm
    _ = (perfectCore (parP h)).map φ.toMonoidHom := by
        rw [CFSG.Quasithin.perfectCore_perfect]
    _ = Opp 2 ((parP h).map φ.toMonoidHom) := (opp_parP_map h hn φ).symm

private theorem isL2_bar2_opp_parP_map {Y : Type} [Group Y] (hn : 2 ≤ n)
    (φ : hypSU h 2 0 ≃* Y) :
    IsL2 (Bar2 (Opp 2 ((parP h).map φ.toMonoidHom))) n := by
  rw [opp_parP_map h hn φ]
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (S17.nonempty_bar2_map φ (perfectCore (parP h))).some.symm
    (lieModel_modO2_perfectCore_parP h hn)

private theorem card_zpowers_torElt_map {Y : Type} [Group Y] {p : ℕ}
    (φ : hypSU h 2 0 ≃* Y) {a : K} (ha : h.bar a * a = 1) (hap : orderOf a = p) :
    Nat.card ((Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom) = p := by
  rw [Subgroup.card_map_of_injective φ.injective, Nat.card_zpowers, orderOf_torElt h ha, hap]

private theorem zpowers_torElt_map_le_normalizer {Y : Type} [Group Y]
    (φ : hypSU h 2 0 ≃* Y) {S : Subgroup Y} {a : K} (ha : h.bar a * a = 1)
    (hφ : (hypUnitriangular h 2 0).map φ.toMonoidHom = S) :
    (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom ≤
      Subgroup.normalizer (S : Set Y) := by
  have hle : Subgroup.zpowers (torElt h ha) ≤
      Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) := by
    rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
    exact Subgroup.zpowers_le.mpr (torElt_mem_hypBorel h ha)
  calc (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom
      ≤ (Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0))).map
          φ.toMonoidHom := Subgroup.map_mono hle
    _ = Subgroup.normalizer ((hypUnitriangular h 2 0).map φ.toMonoidHom : Set Y) :=
        Subgroup.map_equiv_normalizer_eq _ φ
    _ = Subgroup.normalizer (S : Set Y) := by rw [hφ]

private theorem map_sup_zpowers_torElt_map {Y : Type} [Group Y] {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (φ : hypSU h 2 0 ≃* Y) {S : Subgroup Y}
    {a : K} (ha : h.bar a * a = 1) (hap : orderOf a = p)
    (hφ : (hypUnitriangular h 2 0).map φ.toMonoidHom = S) {r : MulAut Y}
    (hr : S.map r.toMonoidHom = S) :
    (S ⊔ (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom).map r.toMonoidHom =
      S ⊔ (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom := by
  have hθ : (hypUnitriangular h 2 0).map ((φ.trans r).trans φ.symm).toMonoidHom =
      hypUnitriangular h 2 0 := map_aut_eq_of_map_eq hφ hr
  have hθsup := map_sup_zpowers_torElt h hp hpq ha hap hθ
  have hSY : S ⊔ (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom =
      (hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom := by
    rw [Subgroup.map_sup, hφ]
  rw [hSY, S17.map_map_trans_symm, hθsup]

private theorem exists_elemAbelian_map {Y : Type} [Group Y] (hn : 2 ≤ n) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (φ : hypSU h 2 0 ≃* Y) {a : K}
    (ha : h.bar a * a = 1) (hap : orderOf a = p) :
    ∃ E : Subgroup Y,
      E ≤ Opp 2 ((parP h).map φ.toMonoidHom) ⊔
          (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom ∧
        IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨E₀, hE₀le, hE₀ea, hE₀card⟩ :=
    exists_isElemAbelian_le_perfectCore_parP_sup h hn hp hpq ha hap
  refine ⟨E₀.map φ.toMonoidHom, ?_, IsElemAbelian.map hE₀ea φ.toMonoidHom, ?_⟩
  · calc (E₀.map φ.toMonoidHom)
        ≤ ((perfectCore (parP h)) ⊔ Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom :=
          Subgroup.map_mono hE₀le
      _ = (perfectCore (parP h)).map φ.toMonoidHom ⊔
            (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom :=
          Subgroup.map_sup _ _ _
      _ = Opp 2 ((parP h).map φ.toMonoidHom) ⊔
            (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom := by
          rw [opp_parP_map h hn φ]
  · rw [Subgroup.card_map_of_injective φ.injective, hE₀card]

end Model

theorem kU4Delta_holds : KU4Delta := by
  classical
  intro Y _ _ n hn hY S R p hS _ hRS hp hpq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, instK, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY
  letI : Field K := instK
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hU : IsSylowIn 2 (hypUnitriangular h 2 0) ⊤ := isSylowIn_hypUnitriangular h
  obtain ⟨φ, hφ⟩ := S17.exists_mulEquiv_map_eq_of_isSylowIn e hU hS
  obtain ⟨a, ha, hap⟩ := exists_bar_mul_eq_one_orderOf_eq h hp hpq
  refine ⟨(parP h).map φ.toMonoidHom,
    (Subgroup.zpowers (torElt h ha)).map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hφ]
    exact isMaxParabolicOver_parP_map h φ
  · intro r hr
    have hθ : (hypUnitriangular h 2 0).map ((φ.trans r).trans φ.symm).toMonoidHom =
        hypUnitriangular h 2 0 := map_aut_eq_of_map_eq hφ (hRS r hr)
    calc ((parP h).map φ.toMonoidHom).map r.toMonoidHom
        = ((parP h).map ((φ.trans r).trans φ.symm).toMonoidHom).map φ.toMonoidHom :=
          S17.map_map_trans_symm φ r (parP h)
      _ = (parP h).map φ.toMonoidHom := by
          rw [map_parP_of_map_hypUnitriangular h hn hθ]
  · exact commutator_opp_parP_map h hn φ
  · exact isL2_bar2_opp_parP_map h hn φ
  · exact card_zpowers_torElt_map h φ ha hap
  · exact zpowers_torElt_map_le_normalizer h φ ha hφ
  · intro r hr
    exact map_sup_zpowers_torElt_map h hp hpq φ ha hap hφ (hRS r hr)
  · exact exists_elemAbelian_map h hn hp hpq φ ha hap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

