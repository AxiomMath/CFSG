module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Bar
public import CFSG.Quasithin.Vol2.Ch11SecBL2UCase
public import CFSG.Quasithin.Vol2.Ch11L2Q5cBadOrd
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi2
public import CFSG.Quasithin.Vol2.Ch11SecA11Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch11.SecB (A312Out L2BadType FactMathieuOrders)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem openQuasisimple_of {K : Subgroup G} (h : CFSG.IsQuasisimple (O2Q K)) :
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
  have e : O2Q K ≃* (↥K ⧸ CFSG.Open.pCore 2 ↥K) :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)
  obtain ⟨hp, hs, -⟩ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e h
  exact ⟨hp.commutator_eq_top, hs⟩

omit [Finite G] in
theorem isPGroup_openPCore (K : Subgroup G) : IsPGroup 2 (CFSG.Open.pCore 2 ↥K) := by
  exact CFSG.pCore_isPGroup

omit [Finite G] in
theorem isQuasisimple_o2q_of_simple {K : Subgroup G} [Group.IsPerfect ↥K]
    [IsSimpleGroup (O2Q K)] : CFSG.IsQuasisimple (O2Q K) := by
  have : Group.IsPerfect (O2Q K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
  exact isQuasisimple_of_isSimpleGroup_of_isPerfect

namespace EmbLoc

variable {S X K Kh : Subgroup G} {k : ℕ} (l : EmbLoc G S X K Kh)
include l

theorem false_of_not_a312Out (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (ψ : ↥K →* Y) (hψ : Function.Surjective ψ)
    (hQ : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) {m : ℕ} (hm : 2 ≤ m)
    (hbad : L2BadType m Y) (hout : ¬ A312Out Y) : False := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
  have hYab := Vol2.Ch11.SecB.nonabelian_of_perfect_surjective ψ hψ
  rcases l.cases h312 with hc | hnq
  · exact hout (Vol2.Ch11.SecB.a312Out_of_case hM hYab (isPGroup_openPCore K) hQ ψ hψ
      (barMap l.le_X) (barMap_surjective _) hc)
  · exact Vol2.Ch11.SecB.false_of_a312Nonquasi hm hbad hQ ψ hψ l.bar_lt.le
      (barMap l.le_X) (barMap_surjective _) hnq

theorem false_of_unitary (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (hk : 2 ≤ k)
    (hq : CFSG.IsQuasisimple (O2Q K))
    (hU : LieModel (O2Q K ⧸ Subgroup.center (O2Q K)) .PSU 3 2 k) : False := by
  have : IsSimpleGroup (O2Q K ⧸ Subgroup.center (O2Q K)) := hq.2.1
  have hY : IsPSU 3 2 k (O2Q K ⧸ Subgroup.center (O2Q K)) :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU
  exact l.false_of_not_a312Out hM h312
    ((QuotientGroup.mk' (Subgroup.center (O2Q K))).comp (QuotientGroup.mk' _))
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    (openQuasisimple_of hq) hk (Or.inr (Or.inl hY))
    (Vol2.Ch11.SecB.not_a312Out_of_isPSU3 hk hY)

theorem false_of_psl3 (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (hk : 3 ≤ k)
    (hL3 : LieModel (O2Q K) .PSL 3 2 k) : False := by
  have hY : IsPSL 3 2 k (O2Q K) :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL3
  have : IsSimpleGroup (O2Q K) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 k hY).2
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
  exact l.false_of_not_a312Out hM h312 (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (openQuasisimple_of isQuasisimple_o2q_of_simple) (by omega) (Or.inr (Or.inr (Or.inl hY)))
    (Vol2.Ch11.SecB.not_a312Out_of_isPSL3 hk hY)

theorem false_of_sl3 (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (hk : 3 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ k) (eF : O2Q K ≃* Matrix.SpecialLinearGroup (Fin 3) F) : False := by
  have hY : IsPSL 3 2 k (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    ⟨⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance,
      hF, ⟨projectiveSpecialLinearGroupEquivStatedProj 3 F⟩⟩
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 k hY).2
  have hq : CFSG.IsQuasisimple (O2Q K) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl)
  exact l.false_of_not_a312Out hM h312
    (((QuotientGroup.mk' _).comp eF.toMonoidHom).comp (QuotientGroup.mk' _))
    (((QuotientGroup.mk'_surjective _).comp eF.surjective).comp (QuotientGroup.mk'_surjective _))
    (openQuasisimple_of hq) (by omega) (Or.inr (Or.inr (Or.inl hY)))
    (Vol2.Ch11.SecB.not_a312Out_of_isPSL3 hk hY)

theorem false_of_psp4 (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (hk : 2 ≤ k)
    (hS : LieModel (O2Q K) .PSp 2 2 k) : False := by
  have hY : IsPSp4 2 k (O2Q K) :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hS
  have : IsSimpleGroup (O2Q K) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 k hY
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
  have hbad : L2BadType k (O2Q K) := by
    refine Or.inr (Or.inr (Or.inr ?_))
    unfold E2.IsSp4Prime
    simp only [show ¬ k = 1 by omega, ↓reduceIte]
    exact hY
  exact l.false_of_not_a312Out hM h312 (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (openQuasisimple_of isQuasisimple_o2q_of_simple) hk hbad
    (Vol2.Ch11.SecB.not_a312Out_of_isPSp4 hk hY)

theorem twoF4_of_suzuki (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (hS : SuzukiModel (O2Q K) 2 k) :
    Is2F4 k (O2Q Kh) := by
  have : IsSimpleGroup (O2Q K) := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 k hS).2
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
  have hq : CFSG.IsQuasisimple (O2Q K) := isQuasisimple_o2q_of_simple
  have hYab := Vol2.Ch11.SecB.nonabelian_of_perfect_surjective (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
  have hS' : IsSz k (O2Q K) := hS
  rcases l.cases h312 with hc | hnq
  · obtain ⟨f, hf, h2F4, -⟩ := Vol2.Ch11.SecB.a312C3_of_case_of_not_three hYab
      (isPGroup_openPCore K) (openQuasisimple_of hq) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (Vol2.Ch11.SecB.not_three_dvd_card_isSz hS')
      (Vol2.Ch11.SecB.lt_card_isSz hS') hM (barMap l.le_X) (barMap_surjective _) hc
    obtain ⟨eB⟩ := l.bar_equiv
    obtain ⟨eH⟩ := l.hat_equiv
    have hfk : f = k := by
      obtain ⟨-, hf3, hcf⟩ := Vol2.Ch11.SecB.card_isSz hf
      obtain ⟨-, hk3, hck⟩ := Vol2.Ch11.SecB.card_isSz hS'
      rw [← Nat.card_congr eB.toEquiv, hck] at hcf
      obtain ⟨r, hr, hr'⟩ := (CFSG.Timmesfeld.Orders.profile_ordSuzuki (f := k) (by omega)).two
      obtain ⟨s, hs, hs'⟩ := (CFSG.Timmesfeld.Orders.profile_ordSuzuki (f := f) (by omega)).two
      have h1 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hr'.symm.trans
        (hcf.trans hs'))
      omega
    subst hfk
    exact CFSG.SectionRank.reeTitsModel_of_mulEquiv eH h2F4
  · exact (Vol2.Ch11.SecB.false_of_a312Nonquasi (k := k)
      (by obtain ⟨-, hk3, -⟩ := Vol2.Ch11.SecB.card_isSz hS'; omega) (Or.inl hS')
      (openQuasisimple_of hq) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      l.bar_lt.le (barMap l.le_X) (barMap_surjective _) hnq).elim

end EmbLoc

namespace Emb512

variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem false_of_unitary (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (heq : K₁ = oTwoUpper H) (hk : 2 ≤ k)
    (hq : CFSG.IsQuasisimple (O2Q K₁))
    (hU : LieModel (O2Q K₁ ⧸ Subgroup.center (O2Q K₁)) .PSU 3 2 k) : False :=
  (e.toLoc heq).false_of_unitary hM h312 hk hq hU

theorem false_of_psl3 (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (heq : K₁ = oTwoUpper H) (hk : 3 ≤ k)
    (hL3 : LieModel (O2Q K₁) .PSL 3 2 k) : False :=
  (e.toLoc heq).false_of_psl3 hM h312 hk hL3

theorem false_of_sl3 (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (heq : K₁ = oTwoUpper H) (hk : 3 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ k) (eF : O2Q K₁ ≃* Matrix.SpecialLinearGroup (Fin 3) F) : False :=
  (e.toLoc heq).false_of_sl3 hM h312 hk hF eF

theorem false_of_psp4 (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (heq : K₁ = oTwoUpper H) (hk : 2 ≤ k)
    (hS : LieModel (O2Q K₁) .PSp 2 2 k) : False :=
  (e.toLoc heq).false_of_psp4 hM h312 hk hS

theorem twoF4_of_suzuki (hM : FactMathieuOrders)
    (h312 : A312ForSQTK) (heq : K₁ = oTwoUpper H) (hS : SuzukiModel (O2Q K₁) 2 k) :
    Is2F4 k (O2Q Kh₁) :=
  (e.toLoc heq).twoF4_of_suzuki hM h312 hS

end Emb512

theorem isRank2LieChar2_of_list11_1_1Two {Y : Type} [Group Y] {m : ℕ} (hm : 2 ≤ m)
    (h : Vol2.Ch11.List11_1_1Two Y m) : IsRank2LieChar2 Y := by
  rcases h with h | h | h | h | h | h | ⟨h3, h⟩
  · exact Or.inl ⟨m, Or.inr (Or.inl ⟨by omega, h⟩)⟩
  · exact Or.inl ⟨m, Or.inl ⟨by omega, h⟩⟩
  · exact Or.inl ⟨m, Or.inr (Or.inr (Or.inl ⟨hm, h⟩))⟩
  · exact Or.inl ⟨m, Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, h⟩)))⟩
  · obtain ⟨-, -, -, -, hodd, h3⟩ := h.1
    exact Or.inl ⟨m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, h3, h⟩))))⟩
  · exact Or.inl ⟨m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h⟩))))⟩
  · have : 1 ≤ m / 3 := by
      obtain ⟨c, hc⟩ := h3
      omega
    exact Or.inl ⟨m / 3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨this, h⟩))))⟩

theorem exists_sl2_equiv_of_lieModel {Y : Type} [Group Y] {m : ℕ}
    (h : LieModel Y .PSL 2 2 m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_two_equiv F)⟩⟩

namespace EmbLoc

variable {S X K Kh : Subgroup G} {k : ℕ} (l : EmbLoc G S X K Kh)
include l

theorem rank2_of_psl2 (hP : Vol2.Ch11.SecA.FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (hk : 3 ≤ k)
    (hL2 : LieModel (O2Q K) .PSL 2 2 k) : IsRank2LieChar2 (O2Q Kh) := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := exists_sl2_equiv_of_lieModel hL2
  obtain ⟨eB⟩ := l.bar_equiv
  obtain ⟨eH⟩ := l.hat_equiv
  have hD : Vol2.Ch11.SecA.BarData (modO2Image X K) k :=
    Vol2.Ch11.SecA.barData_of_quot_SL2 (by omega) hF (eB.symm.trans eF)
  have hconc : Vol2.Ch11.SecA.Concl1111 ↥(modO2Image X Kh) k := by
    rcases l.cases h312 with hc | hnq
    · exact Vol2.Ch11.SecA.concl_of_a312Case hP hD hc
    · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot l.qtke l.simple l.nonabelian l.pCoreX
      exact Vol2.Ch11.SecA.concl_of_nonquasi hD l.bar_lt.le (h36 _ hQ _ l.hatBar_cComp) hnq
  rcases Vol2.Ch11.SecA.Concl1111.of_mulEquiv eH.symm hconc with h2 | ⟨hk2, -⟩
  · exact isRank2LieChar2_of_list11_1_1Two (by omega) h2
  · omega

end EmbLoc

end CFSG.Quasithin.H13
