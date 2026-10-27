module

public import CFSG.Quasithin.EmptyFaithful.S152He4Core
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F420Ln2
public import CFSG.Quasithin.SteinbergBXPrimeThreeSylowCenters
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow

public section

namespace CFSG.Quasithin.He4

open CFSG.QuasithinUnique

theorem smallFacts_of_smallListFacts {Λ : Type} [Group Λ] [Finite Λ] (hF : SmallListFacts Λ)
    (hcard : ∃ m, Nat.card Λ = 16 * m ∧ Odd m) (hinv : NoInvCommNine Λ) : SmallFacts Λ := by
  refine ⟨hcard, ?_, ?_, hinv⟩
  · intro S hS
    obtain ⟨m, hm, hodd⟩ := hcard
    have hSyl : IsSylowTwoOf S ⊤ := by
      refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [hS]; norm_num), ?_⟩
      have h1 : Nat.card (S.subgroupOf ⊤) * (S.subgroupOf ⊤).index = Nat.card (⊤ : Subgroup Λ) :=
        Subgroup.card_mul_index _
      have h2 : Nat.card (S.subgroupOf ⊤) = 16 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, hS]
      rw [h2, Subgroup.card_top, hm] at h1
      have h3 : (S.subgroupOf ⊤).index = m := by omega
      rw [h3]
      exact fun h => by have := Nat.odd_iff.1 hodd; omega
    exact hF.sylow_normalizer S hSyl
  · intro F hF4 hexp
    have hFour : IsFourSubgroup F := by
      refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, hF4⟩
      · apply Subtype.ext
        show (a : Λ) * b = b * a
        have hab : (a : Λ) * b * ((a : Λ) * b) = 1 := hexp _ (F.mul_mem a.2 b.2)
        have ha : (a : Λ) * a = 1 := hexp _ a.2
        have hb : (b : Λ) * b = 1 := hexp _ b.2
        have ha' : (a : Λ)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
        have hb' : (b : Λ)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
        calc (a : Λ) * b = ((a : Λ) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
          _ = (b : Λ)⁻¹ * (a : Λ)⁻¹ := mul_inv_rev _ _
          _ = (b : Λ) * a := by rw [ha', hb']
      · rw [pow_two]
        exact hexp x hx
    obtain ⟨e⟩ := hF.four_normalizer F hFour
    have h24 : Nat.card (Subgroup.normalizer (F : Set Λ)) = 24 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [h24]
    norm_num


open CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_of_statedSL_three_three {X : Type} [Group X]
    (h : Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3)))) : StatedClassicalModel X .PSL 3 3 1 := by
  obtain ⟨e⟩ := h
  refine ⟨?_, ZMod 3, inferInstance, inferInstance, by simp, ⟨e.trans ?_⟩⟩
  · unfold StatedLieAdmissible
    exact ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  · exact ((QuotientGroup.quotientMulEquivOfEq
      CFSG.Quasithin.SteinbergBX.PrimeThreeSylow.statedScalars_subgroupOf_statedSL_three_three).trans
      QuotientGroup.quotientBot).symm

theorem smallFacts_l33
    {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3))))
    (hinv : NoInvCommNine X) : SmallFacts X := by
  have hmod : StatedClassicalModel X .PSL 3 3 1 :=
    h.elim id statedClassicalModel_of_statedSL_three_three
  refine smallFacts_of_smallListFacts (Unc25L33.l33_facts X hmod).1 ⟨351, ?_, by decide⟩ hinv
  rw [F420.card_of_l33 h]

theorem smallFacts_m11
    {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) (hinv : NoInvCommNine X) :
    SmallFacts X := by
  refine smallFacts_of_smallListFacts (Unc25M11.m11_facts X h).1 ⟨495, ?_, by decide⟩ hinv
  rw [F420.card_of_m11 h]

theorem card_mulAut_le_of_outer {P : Type*} [Group P] [Finite P] (hZ : Subgroup.center P = ⊥)
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer P) ∣ 2) :
    Nat.card (MulAut P) ≤ 2 * Nat.card P := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner P)
  have hinj : Function.Injective (MulAut.conj : P →* MulAut P) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : a ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := MulEquiv.ext_iff.1 ha g
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * a = a * g * a⁻¹ * a := by rw [this]
        _ = a * g := by group
    rw [hZ] at hc
    exact hc
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner P) = Nat.card P :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h2] at h1
  have h3 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer P) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hOut
  rw [h1]
  exact Nat.mul_le_mul_right _ h3

theorem lnTwo_facts {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel X .PSL n 2 1) :
    Subgroup.center X = ⊥ ∧ Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  have hZ := F420.center_eq_bot_of_statedPSL h
  refine ⟨hZ, ?_⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  let e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K := e.trans (K1.statedProjEquivProjectiveSL n K)
  have hOut := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
    (K := K) (ℓ := 2) (f := 1) Nat.prime_two le_rfl hn hK
  norm_num at hOut
  have hZP : Subgroup.center (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) = ⊥ :=
    F420.center_eq_bot_of_mulEquiv' e'.symm hZ
  have := card_mulAut_le_of_outer hZP hOut
  rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
  exact this

theorem nonempty_mulEquiv_psl_zmod_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) :
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Nat.card_zmod]
    norm_num
  exact ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin n)
      (FiniteField.ringEquivOfCardEq hcard)))⟩

end CFSG.Quasithin.He4
