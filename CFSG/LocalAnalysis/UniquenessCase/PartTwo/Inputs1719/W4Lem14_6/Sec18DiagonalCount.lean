module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsXMod
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.F6CatSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem odd_card_irr_isoComp {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Γ : Type} [Group Γ] [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) :
    Odd (Nat.card {J : Subgroup Q // J ≤ SmithD39Two.isoComp ↥Λ I ∧ XMod.IsIrr ↥Λ J}) := by
  classical
  have hIne : I ≠ ⊥ := hI.2.1.ne'
  obtain ⟨c, hc⟩ := SmithD39Two.exists_rk_eq_mul (A := ↥Λ) hQ hI
    (SmithD39Two.isInv_isoComp (A := ↥Λ) I) le_rfl
  have hY : SmithD39Two.IsotypicOfLength ↥Λ (SmithD39Two.isoComp ↥Λ I) I c :=
    ⟨SmithD39Two.isInv_isoComp I, le_rfl, hc⟩
  have hIpos : 0 < rk ↥I := by
    rcases Nat.eq_zero_or_pos (rk ↥I) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hQ).mp h0) hIne
    · exact h0
  have hle : rk ↥I ≤ rk ↥(SmithD39Two.isoComp ↥Λ I) :=
    rk_mono (SmithD39Two.le_isoComp hI (XMod.Iso.refl I))
  rw [hc] at hle
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, zero_mul] at hle
      omega
    · exact h0
  have heven := SmithD321.even_card_end (Λ := Λ) hQ hI
  have hE := Nat.even_pow.2 ⟨heven, (by omega : c ≠ 0)⟩
  rw [← SmithD321.card_irr_mul_card_units (Λ := Λ) hQ hI hY, Nat.even_add_one,
    Nat.not_even_iff_odd] at hE
  exact (Nat.odd_mul.1 hE).1

theorem isIrr_iff_mem_irrSet {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (hfix : fixV X = ⊥) {J : Subgroup W} : XMod.IsIrr ↥X J ↔ J ∈ irrSet X := by
  constructor
  · intro hJ
    obtain ⟨hInv, hlt, hmax⟩ := hJ
    have hstab : ∀ x ∈ X, ∀ w ∈ J, x w ∈ J := (CFSG.Quasithin.isInv_iff X J).mp hInv
    have hcomm : commSub J X = J := by
      refine le_antisymm (commSub_le_of_invariant hstab) ?_
      rcases hmax (commSub J X) ((CFSG.Quasithin.isInv_iff X _).mpr (SmithD321.commSub_isInv J X))
        bot_le (commSub_le_of_invariant hstab) with h | h
      · exfalso
        have h1 : J ≤ fixV X := commSub_eq_bot_iff.mp h
        rw [hfix] at h1
        exact hlt.ne' (le_bot_iff.mp h1)
      · rw [h]
    have hInvZ : XMod.IsInv ↥X (J ⊓ fixV X) := by
      rw [CFSG.Quasithin.isInv_iff]
      intro x hx w hw
      obtain ⟨hwJ, hwFix⟩ := Subgroup.mem_inf.mp hw
      refine Subgroup.mem_inf.mpr ⟨hstab x hx w hwJ, ?_⟩
      rw [mem_fixV]
      intro y hy
      rw [mem_fixV.mp hwFix x hx]
      exact mem_fixV.mp hwFix y hy
    have hCZ : J ⊓ fixV X = ⊥ := by
      rcases hmax (J ⊓ fixV X) hInvZ bot_le inf_le_left with h | h
      · exact h
      · exfalso
        have h1 : J ≤ fixV X := h ▸ inf_le_right
        rw [hfix] at h1
        exact hlt.ne' (le_bot_iff.mp h1)
    refine ⟨hcomm, ?_, hstab, ?_, ?_⟩
    · rw [hCZ]; exact hlt
    · rw [hCZ]
      intro x _ u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · intro K hK _ hKJ
      rcases hmax K ((CFSG.Quasithin.isInv_iff X K).mpr hK) bot_le hKJ with h | h
      · left; rw [h, hCZ]
      · exact Or.inr h
  · rintro ⟨hcomm, hlt, hstab, -, hmin⟩
    have hCZ : J ⊓ fixV X = ⊥ := by rw [hfix, inf_bot_eq]
    refine ⟨(CFSG.Quasithin.isInv_iff X J).mpr hstab, ?_, ?_⟩
    · rwa [hCZ] at hlt
    · intro K hK hKbot hKJ
      rcases hmin K ((CFSG.Quasithin.isInv_iff X K).mp hK) (hCZ.symm ▸ hKbot) hKJ with h | h
      · left; rw [h, hCZ]
      · exact Or.inr h

theorem odd_card_irrSet_of_homog {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} (hfix : fixV X = ⊥)
    {I : Subgroup W} (hI : I ∈ irrSet X)
    (hhom : ∀ J ∈ irrSet X, SecIsoOn X I ⊥ J ⊥) :
    Odd (Nat.card ↥(irrSet X)) := by
  have hIirr : XMod.IsIrr ↥X I := (isIrr_iff_mem_irrSet hfix).mpr hI
  have hset : irrSet X =
      {J : Subgroup W | J ≤ SmithD39Two.isoComp ↥X I ∧ XMod.IsIrr ↥X J} := by
    ext J
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hJ
      have hJirr : XMod.IsIrr ↥X J := (isIrr_iff_mem_irrSet hfix).mpr hJ
      exact ⟨SmithD39Two.le_isoComp hJirr
        (XMod.Iso.symm hIirr.1 (iso_of_secIsoOn_bot (hhom J hJ))), hJirr⟩
    · rintro ⟨-, hJirr⟩
      exact (isIrr_iff_mem_irrSet hfix).mp hJirr
  rw [hset]
  exact odd_card_irr_isoComp hW hIirr

theorem exists_stable_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    {X A : Subgroup (MulAut W)} (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hA2 : IsPGroup 2 A) (hodd : Odd (Nat.card ↥(irrSet X))) :
    ∃ N ∈ irrSet X, StableUnder A N := by
  classical
  have hsmul : ∀ a : ↥A, ∀ I : ↥(irrSet X),
      ((a : MulAut W) • (I : Subgroup W)) ∈ irrSet X := by
    intro a I
    have h1 : ∀ x ∈ X, (a : MulAut W) * x * (a : MulAut W)⁻¹ ∈ X :=
      fun x hx => conj_mem_of_mem_normalizer (hAX a.2) hx
    have h2 : ∀ x ∈ X, (a : MulAut W)⁻¹ * x * (a : MulAut W) ∈ X :=
      fun x hx => inv_conj_mem_of_mem_normalizer (hAX a.2) hx
    have h := map_mem_irrSet (g := (a : MulAut W)) h1 h2 I.2
    rwa [Subgroup.pointwise_smul_def]
  letI : MulAction ↥A ↥(irrSet X) :=
    { smul := fun a I => ⟨(a : MulAut W) • (I : Subgroup W), hsmul a I⟩
      one_smul := fun I => by
        apply Subtype.ext
        show (((1 : ↥A) : MulAut W)) • (I : Subgroup W) = (I : Subgroup W)
        simp
      mul_smul := fun a b I => by
        apply Subtype.ext
        show (((a * b : ↥A) : MulAut W)) • (I : Subgroup W) =
          (a : MulAut W) • ((b : MulAut W) • (I : Subgroup W))
        rw [Subgroup.coe_mul, mul_smul] }
  have h2 : ¬ 2 ∣ Nat.card ↥(irrSet X) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hodd' : Nat.card ↥(irrSet X) % 2 = 1 := Nat.odd_iff.1 hodd
    omega
  obtain ⟨I, hIfix⟩ := hA2.nonempty_fixed_point_of_prime_not_dvd_card (↥(irrSet X)) h2
  refine ⟨(I : Subgroup W), I.2, ?_⟩
  intro a ha u hu
  have hfix : (⟨a, ha⟩ : ↥A) • I = I := (MulAction.mem_fixedPoints).1 hIfix ⟨a, ha⟩
  have hval : (a : MulAut W) • (I : Subgroup W) = (I : Subgroup W) :=
    congrArg Subtype.val hfix
  have hmem : a u ∈ (a : MulAut W) • (I : Subgroup W) :=
    Subgroup.smul_mem_pointwise_smul u a (I : Subgroup W) hu
  rwa [hval] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
