module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def NatShapeGood {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (I Z : Subgroup W) :
    Prop :=
  ∃ n : ℕ,
    (IsSLn ↥L n 1 ∧ 5 ≤ n ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L I Z 1) ∨
    (IsSpn ↥L n 1 ∧ 6 ≤ n ∧ SumOfNat (fun H U Z => NatSpn H U Z n 1) L I Z 1) ∨
    (IsOmegaPlus ↥L n 1 ∧ 6 ≤ n ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L I Z 1) ∨
    (IsOmegaMinus ↥L n 1 ∧ 8 ≤ n ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L I Z 1) ∨
    (UC22.IsAlt ↥L n ∧ 8 ≤ n ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z n) L I Z 1)

private theorem s16t3_nat_sq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (m : Multiplicative (ι → K)) : m * m ∈ (FFModel.nat Γ).ker := by
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  show m * m ∈ (⊥ : Subgroup (Multiplicative (ι → K)))
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  funext i
  exact CharTwo.add_self_eq_zero _

private theorem s16t3_nat_act_mem_ker {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (γ : ↥Γ) (m : Multiplicative (ι → K))
    (hx : (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
        (Multiplicative.toAdd m)) = Multiplicative.toAdd m) :
    natAct Γ γ m * m⁻¹ ∈ (FFModel.nat Γ).ker := by
  show natAct Γ γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (ι → K)))
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  have h1 : Multiplicative.toAdd (natAct Γ γ m) =
      (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
        (Multiplicative.toAdd m)) := by
    simp only [natAct, toAdd_ofAdd]
  rw [toAdd_mul, toAdd_inv, toAdd_one, h1, hx, add_neg_cancel]

private theorem s16t3_good_case_nat_sl {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {n : ℕ} (hn : 5 ≤ n)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hR : BinaryNaturalSL L I Z n 1) {w : W} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨K, hKf, hKfin, hcard, hreal⟩ := hR
  let : Field K := hKf
  let : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  refine s16t3_good_of_model hπ (FFModel.nat_faithful (StatedSL n K)) hZ ?_ ?_ hw
  · intro m _
    exact s16t3_nat_sq hK (StatedSL n K) m
  · intro m _
    obtain ⟨F, hFp, hFnc, hfix⟩ := s16t3_good_nat_sl hK hn (Multiplicative.toAdd m)
    exact ⟨F, hFp, hFnc, fun γ hγ => s16t3_nat_act_mem_ker γ m (hfix γ hγ)⟩

private theorem s16t3_good_case_nat_sp {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {n : ℕ} (hn : 6 ≤ n)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hR : NatSpn L I Z n 1) {w : W} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨-, K, hKf, hKfin, hcard, hreal⟩ := hR
  let : Field K := hKf
  let : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hm : 3 ≤ n / 2 := by omega
  refine s16t3_good_of_model hπ (FFModel.nat_faithful (StatedSp (n / 2) K)) hZ ?_ ?_ hw
  · intro m _
    exact s16t3_nat_sq hK (StatedSp (n / 2) K) m
  · intro m _
    obtain ⟨F, hFp, hFnc, hfix⟩ := s16t3_good_nat_sp hK hm (Multiplicative.toAdd m)
    exact ⟨F, hFp, hFnc, fun γ hγ => s16t3_nat_act_mem_ker γ m (hfix γ hγ)⟩

private theorem s16t3_good_case_nat_op {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {n : ℕ} (hn : 6 ≤ n)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hR : NatOmegaPlus L I Z n 1) {w : W} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨-, K, hKf, hKfin, hcard, hreal⟩ := hR
  let : Field K := hKf
  let : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hm : 3 ≤ n / 2 := by omega
  refine s16t3_good_of_model hπ (FFModel.nat_faithful (StatedOmega (StatedQuadPlus (n / 2) K)))
    hZ ?_ ?_ hw
  · intro m _
    exact s16t3_nat_sq hK (StatedOmega (StatedQuadPlus (n / 2) K)) m
  · intro m _
    obtain ⟨F, hFp, hFnc, hfix⟩ :=
      s16t3_good_nat_op hK hm (Multiplicative.toAdd m)
    exact ⟨F, hFp, hFnc, fun γ hγ => s16t3_nat_act_mem_ker γ m (hfix γ hγ)⟩

private theorem s16t3_good_case_nat_om {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {n : ℕ} (hn : 8 ≤ n)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hR : NatOmegaMinus L I Z n 1) {w : W} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hbc, hreal⟩ := hR
  let : Field K := hKf
  let : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hm : 4 ≤ n / 2 := by omega
  refine s16t3_good_of_model hπ
    (FFModel.nat_faithful (StatedOmega (StatedQuadMinus (n / 2) K b c))) hZ ?_ ?_ hw
  · intro m _
    exact s16t3_nat_sq hK (StatedOmega (StatedQuadMinus (n / 2) K b c)) m
  · intro m _
    obtain ⟨F, hFp, hFnc, hfix⟩ :=
      s16t3_good_nat_om hK hm hbc (Multiplicative.toAdd m)
    exact ⟨F, hFp, hFnc, fun γ hγ => s16t3_nat_act_mem_ker γ m (hfix γ hγ)⟩

private theorem s16t3_good_case_alt {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {n : ℕ} (hn : 8 ≤ n)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hR : AlternatingNatural L I Z n) {w : W} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨π, hπ⟩ := hR
  have hfaith : (FFModel.altDn n).Faithful :=
    CFSG.Quasithin.FFC.altDn_faithful (by omega)
  refine s16t3_good_of_model hπ hfaith hZ ?_ ?_ hw
  · intro m _
    let x : Multiplicative (Fin n → ZMod 2) := m
    have hsq : x * x = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      funext i
      exact CharTwo.add_self_eq_zero _
    rw [show m * m = 1 from hsq]
    exact Subgroup.one_mem _
  · intro m hm
    exact s16t3_good_alt_dn hn ⟨m, hm⟩

theorem NatShapeGood.exists_noncyclic_three {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I : Subgroup W} (hS : NatShapeGood L I (I ⊓ fixV L)) {w : W}
    (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨n, hcases⟩ := hS
  have hZ : ∀ l ∈ L, ∀ z ∈ I ⊓ fixV L, l z = z :=
    fun l hl z hz => (mem_fixV.mp hz.2) l hl
  rcases hcases with hc | hc | hc | hc | hc
  · exact s16t3_good_case_nat_sl hc.2.1 hZ (s16t3_sumOfNat_one hc.2.2) hw
  · exact s16t3_good_case_nat_sp hc.2.1 hZ (s16t3_sumOfNat_one hc.2.2) hw
  · exact s16t3_good_case_nat_op hc.2.1 hZ (s16t3_sumOfNat_one hc.2.2) hw
  · exact s16t3_good_case_nat_om hc.2.1 hZ (s16t3_sumOfNat_one hc.2.2) hw
  · exact s16t3_good_case_alt hc.2.1 hZ (s16t3_sumOfNat_one hc.2.2) hw

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_good_vec_sumOfNat {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hS : NatShapeGood L I (I ⊓ fixV L)) :
    SumOfNatShape L I (I ⊓ fixV L) 1 := by
  obtain ⟨n, hcases⟩ := hS
  rcases hcases with hc | hc | hc | hc | hc
  · exact ⟨n, Or.inl ⟨hc.1, hc.2.2⟩⟩
  · exact ⟨n, Or.inr (Or.inl ⟨hc.1, hc.2.2⟩)⟩
  · exact ⟨n, Or.inr (Or.inr (Or.inl ⟨hc.1, hc.2.2⟩))⟩
  · exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hc.1, hc.2.2⟩)))⟩
  · exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hc.1, hc.2.2⟩)))⟩

private theorem s16t3_good_vec_exists_fixed {I : Subgroup (Vtil V₀ V hV)}
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hS : NatShapeGood (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L)))
    (hTI : StableUnder (barSub V₀ V hV D.T) I) :
    ∃ w ∈ I, w ≠ 1 ∧ ∀ t : ↥(barSub V₀ V hV D.T),
      (t : MulAut (Vtil V₀ V hV)) w = w := by
  have hShape := s16t3_good_vec_sumOfNat hS
  have hTp : IsPGroup 2 (barSub V₀ V hV D.T) := by
    rw [barSub]
    exact (D.sylowM.isPGroup).comap_subtype.map (actTil V₀ V hV)
  exact exists_fixed_of_stable_subgroup hTI hShape hq
    (s15_Infra_vtil_sq_eq_one V₀ V hV) hTp

private theorem s16t3_good_vec_exists_three (hset : Setting16 D V₀ V L)
    {I : Subgroup (Vtil V₀ V hV)}
    (hS : NatShapeGood (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L)))
    {w : Vtil V₀ V hV} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut (Vtil V₀ V hV)), E ≤ Mbar D.M V₀ V hV ∧ IsPGroup 3 ↥E ∧
      ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  obtain ⟨E, hEL, hEp, hEc, hEfix⟩ := NatShapeGood.exists_noncyclic_three hS hw
  have hle : E ≤ Mbar D.M V₀ V hV :=
    hEL.trans (by simpa [lBar, Mbar] using barSub_mono V₀ V hV hset.hyp151.le)
  exact ⟨E, hle, hEp, hEc, hEfix⟩

theorem Setting16.exists_good_vector (hset : Setting16 D V₀ V L) (h61 : UC6.R6_1 D)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) (h3 : 3 ∈ D.sig) (hV₀ : V₀ = ⊥)
    {I : Subgroup (Vtil V₀ V hV)} (hTI : StableUnder (barSub V₀ V hV D.T) I)
    (hS : NatShapeGood (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L))) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  obtain ⟨w, hwI, hwv_ne, hwt⟩ := s16t3_good_vec_exists_fixed hq hS hTI
  obtain ⟨E, hle, hEp, hEc, hEfix⟩ := s16t3_good_vec_exists_three hset hS hwI
  exact hset.good_vector_of_fix h61 h3 hV₀ hwv_ne hwt hle hEp hEc hEfix

theorem Setting16.exists_good_vector_of_stronglyEmbedded (hset : Setting16 D V₀ V L)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hV₀ : V₀ = ⊥)
    {I : Subgroup (Vtil V₀ V hV)} (hTI : StableUnder (barSub V₀ V hV D.T) I)
    (hS : NatShapeGood (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L))) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  obtain ⟨w, hwI, hwv_ne, hwt⟩ := s16t3_good_vec_exists_fixed hq hS hTI
  obtain ⟨E, hle, hEp, hEc, hEfix⟩ := s16t3_good_vec_exists_three hset hS hwI
  exact hset.good_vector_of_fix_of_stronglyEmbedded h61 h63 hsp hV₀ hwv_ne hwt hle hEp hEc hEfix

theorem S16gRowCtx.exists_good_vector (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hV₀ : V₀ = ⊥) {I : Subgroup (Vtil V₀ V hV)} (hTI : StableUnder (barSub V₀ V hV D.T) I)
    (hS : NatShapeGood (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L))) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M :=
  h.setting.exists_good_vector h.std.h61 h.quasi h3 hV₀ hTI hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
