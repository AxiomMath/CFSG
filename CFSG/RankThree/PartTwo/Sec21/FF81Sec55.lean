module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55F
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec526
public import CFSG.Quasithin.Recognition.M12AscGlobal
import CFSG.RankThree.PartTwo.Sec21.FF84S36Cp
import CFSG.RankThree.PartTwo.Sec21.FF84S36Ab
import CFSG.RankThree.PartTwo.Sec21.FF81Fusion
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Z
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
public import CFSG.CharacterTheory.Blocks.Defs
import CFSG.Fischer.Classification.Defs
import CFSG.GF2Type.Aschbacher1976
import CFSG.GF2Type.CenterFour.Setting
import CFSG.LargeExtraspecial.BridgeSetting
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S5Three
import CFSG.LargeExtraspecial.S6Four
import CFSG.LargeExtraspecial.S6SevenC
import CFSG.LargeExtraspecial.S8FusE
import CFSG.LargeExtraspecial.S8Lin
import CFSG.LargeExtraspecial.S9FourD
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
import CFSG.Quasithin.Recognition.M12AscConj
import CFSG.Sporadic.Th.F2Spec
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open S36 (hypF hypU hypA dot)
open CFSG.Quasithin (ExtraspecialAt)

variable {G : Type} [Group G] [Finite G]

namespace S55

theorem elemAb_comm {k : ℕ} {H : Subgroup G} (h : IsElemAb 2 k H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  haveI := h.1
  intro x hx y hy
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥H)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem elemAb_sq {k : ℕ} {H : Subgroup G} (h : IsElemAb 2 k H) : ∀ x ∈ H, x * x = 1 := by
  haveI := h.1
  intro x hx
  rw [← sq]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

theorem le_cenS_sup {A C D : Subgroup G} (h₁ : A ≤ CenS C) (h₂ : A ≤ CenS D) :
    A ≤ CenS (C ⊔ D) :=
  Subgroup.le_centralizer_iff.mpr
    (sup_le (Subgroup.le_centralizer_iff.mp h₁) (Subgroup.le_centralizer_iff.mp h₂))

theorem cenS_symm {A C : Subgroup G} (h : A ≤ CenS C) : C ≤ CenS A :=
  Subgroup.le_centralizer_iff.mp h

theorem comm_of_le_cenS {A C : Subgroup G} (h : A ≤ CenS C) : ∀ x ∈ A, ∀ y ∈ C, x * y = y * x :=
  fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (h hx) y hy).symm

theorem sup_comm_sq {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hA2 : ∀ x ∈ A, x * x = 1) (hB2 : ∀ x ∈ B, x * x = 1) :
    (∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x) ∧ ∀ x ∈ A ⊔ B, x * x = 1 := by
  have hdec : ∀ g ∈ A ⊔ B, ∃ x ∈ A, ∃ y ∈ B, g = x * y := by
    intro g hg
    have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2] at hg'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hg'
    exact ⟨x, hx, y, hy, hxy.symm⟩
  refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec g hg
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec g' hg'
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [hA a ha a' ha', hB b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hc a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec g hg
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hc a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hA2 a ha, hB2 b hb, one_mul]

theorem nor_sup {A B : Subgroup G} {a : G} (hA : a ∈ Nor A) (hB : a ∈ Nor B) : a ∈ Nor (A ⊔ B) := by
  have key : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj a).toMonoidHom := sup_le
    (fun x hx => by
      change a * x * a⁻¹ ∈ A ⊔ B
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA x).mp hx))
    (fun x hx => by
      change a * x * a⁻¹ ∈ A ⊔ B
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB x).mp hx))
  exact Subgroup.mem_normalizer_fintype fun y hy => key hy

end S55

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Big

variable (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include hKF h5

theorem FF81Sec5.conc5_5_of_big (hS : Nat.card (Op 2 (Cen s₀)) = 2 ^ 15)
    (hW1 : Nat.card (h5.W 1) = 2) (hW2 : IsElemAb 2 3 (h5.W 2)) (h72 : h5.W 7 ≤ CenS (h5.W 2))
    (h78 : h5.W 7 ≤ CenS (h5.W 8)) (hX : ExtraspecialAt (h5.W 8 ⊔ h5.W 7) s₀)
    {A : Subgroup G} (hAX : A ≤ h5.W 8 ⊔ h5.W 7) (hA : IsElemAb 2 3 A) (hsA : s₀ ∈ A) :
    FF81Conc5_5 s₀ ∧ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) = h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4 ∧
      Nat.card ↥(h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4) = 2 ^ 7 ∧
      (∀ x ∈ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4, ∀ y ∈ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4, x * y = y * x) ∧
      ∀ x ∈ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4, x * x = 1 := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  have hS2 : IsPGroup 2 (Op 2 (Cen s₀)) := op_two_isPGroup s₀
  have hs2 : s₀ * s₀ = 1 := by rw [← sq, ← h5.hs₀, pow_orderOf_eq_one]
  have hs₀1 : s₀ ≠ 1 := fun e => by
    have := h5.hs₀; rw [e, orderOf_one] at this; omega
  have hWS : ∀ i, h5.W i ≤ Op 2 (Cen s₀) := fun i => inf_le_left
  have T : ∀ (w : List (Fin 3)) {r₁ r₂ i j : Fin 13}, S55.Carries w r₁ i → S55.Carries w r₂ j →
      h5.W r₁ ≤ CenS (h5.W r₂) → h5.W i ≤ CenS (h5.W j) := fun w _ _ _ _ h₁ h₂ hc =>
    h5.W_le_cenS hgH hg h₁ h₂ hc
  have c27 : h5.W 2 ≤ CenS (h5.W 7) := S55.cenS_symm h72
  have c23 : h5.W 2 ≤ CenS (h5.W 3) := h5.W₂_le_cenS_W₃ hKF hW2 hW1
  have c24 : h5.W 2 ≤ CenS (h5.W 4) := T [0] (by decide) (by decide) c23
  have c34 : h5.W 3 ≤ CenS (h5.W 4) := T [2, 0] (by decide) (by decide) c23
  have c25 : h5.W 2 ≤ CenS (h5.W 5) := T [1] (by decide) (by decide) c27
  have c26 : h5.W 2 ≤ CenS (h5.W 6) := T [0, 1] (by decide) (by decide) c27
  have c28 : h5.W 2 ≤ CenS (h5.W 8) := T [1, 0, 1] (by decide) (by decide) c27
  have c35 : h5.W 3 ≤ CenS (h5.W 5) := T [2] (by decide) (by decide) c27
  have c36 : h5.W 3 ≤ CenS (h5.W 6) := T [2, 0, 1] (by decide) (by decide) c27
  have c37 : h5.W 3 ≤ CenS (h5.W 7) := T [1, 2] (by decide) (by decide) c27
  have c38 : h5.W 3 ≤ CenS (h5.W 8) := T [0, 1, 0, 2] (by decide) (by decide) c27
  have c45 : h5.W 4 ≤ CenS (h5.W 5) := T [0, 2, 0, 1] (by decide) (by decide) c27
  have c46 : h5.W 4 ≤ CenS (h5.W 6) := T [0, 2] (by decide) (by decide) c27
  have c47 : h5.W 4 ≤ CenS (h5.W 7) := T [0, 1, 2] (by decide) (by decide) c27
  have c48 : h5.W 4 ≤ CenS (h5.W 8) := T [1, 0, 2] (by decide) (by decide) c27
  have c57 : h5.W 5 ≤ CenS (h5.W 7) := T [0, 2, 0, 1] (by decide) (by decide) h78
  have c58 : h5.W 5 ≤ CenS (h5.W 8) := T [2] (by decide) (by decide) h78
  have c67 : h5.W 6 ≤ CenS (h5.W 7) := T [2, 0, 1] (by decide) (by decide) h78
  have c68 : h5.W 6 ≤ CenS (h5.W 8) := T [0, 2] (by decide) (by decide) h78
  have hW3 : IsElemAb 2 3 (h5.W 3) := by
    rw [← h5.conjBy_W hgH hg (r := 2) (w := [2]) (by decide)]; exact isElemAb_conjBy hW2 _
  have hW4 : IsElemAb 2 3 (h5.W 4) := by
    rw [← h5.conjBy_W hgH hg (r := 2) (w := [0, 2]) (by decide)]; exact isElemAb_conjBy hW2 _
  set Z := h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4 with hZ
  obtain ⟨h23c, h232⟩ := S55.sup_comm_sq (S55.comm_of_le_cenS c23) (S55.elemAb_comm hW2)
    (S55.elemAb_comm hW3) (S55.elemAb_sq hW2) (S55.elemAb_sq hW3)
  obtain ⟨hZc, hZ2⟩ := S55.sup_comm_sq (S55.comm_of_le_cenS (sup_le c24 c34)) h23c
    (S55.elemAb_comm hW4) h232 (S55.elemAb_sq hW4)
  have hZS : Z ≤ Op 2 (Cen s₀) := sup_le (sup_le (hWS 2) (hWS 3)) (hWS 4)
  have hs₀Z : s₀ ∈ Z := Subgroup.mem_sup_left (Subgroup.mem_sup_left (h5.s₀_mem_W 2) : s₀ ∈ h5.W 2 ⊔ h5.W 3)
  have hcZ : Nat.card Z = 2 ^ 7 := by
    have h23 : Nat.card ↥(h5.W 2 ⊔ h5.W 3) = 32 := by
      have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _
        (S55.comm_of_le_cenS c23)).1
      rw [card_eq_two_of_le h5.hs₀ (Subgroup.mem_inf.mpr ⟨h5.s₀_mem_W 2, h5.s₀_mem_W 3⟩)
        (fun y hy => h5.mem_W₂_inf_W₃ hKF hy), hW2.2, hW3.2] at this
      omega
    have hup : Nat.card Z * Nat.card ↥((h5.W 2 ⊔ h5.W 3) ⊓ h5.W 4) =
        Nat.card ↥(h5.W 2 ⊔ h5.W 3) * Nat.card (h5.W 4) :=
      (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _
        (S55.comm_of_le_cenS (sup_le c24 c34))).1
    rw [h23, hW4.2] at hup
    have hi := two_le_card_of_mem h5.hs₀ (Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_sup_left (h5.s₀_mem_W 2) : s₀ ∈ h5.W 2 ⊔ h5.W 3), h5.s₀_mem_W 4⟩)
    obtain ⟨hc, hs⟩ := S36.coprime_solvable_of_two (hS2.to_le hZS)
    have hnor : A₁sub b b₁ b₂ b₃ ≤ Nor Z := fun a ha =>
      S55.nor_sup (S55.nor_sup (h5.A₁_le_nor_W 2 ha) (h5.A₁_le_nor_W 3 ha)) (h5.A₁_le_nor_W 4 ha)
    have hw := S55.card_mul_pow_twelve h5.coordA hnor hc hs
    have hcen : Nat.card ↥(Z ⊓ CenS (A₁sub b b₁ b₂ b₃)) ≤ 2 := by
      rw [← h5.card_S_cenS_A₁ hKF]
      exact Subgroup.card_le_of_le (inf_le_inf_right _ hZS)
    have hlow : ∀ i : Fin 13, (![2, 2, 8, 8, 8, 2, 2, 2, 2, 2, 2, 2, 2] : Fin 13 → ℕ) i ≤
        Nat.card ↥(Z ⊓ CenS (S55.hyp h5.εA i)) := by
      intro i
      have h2 : 2 ≤ Nat.card ↥(Z ⊓ CenS (S55.hyp h5.εA i)) :=
        two_le_card_of_mem h5.hs₀ (Subgroup.mem_inf.mpr ⟨hs₀Z, (h5.s₀_mem_W i).2⟩)
      have h8 : ∀ j, h5.W j ≤ Z → h5.W j = Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA j) →
          8 ≤ Nat.card (h5.W j) → 8 ≤ Nat.card ↥(Z ⊓ CenS (S55.hyp h5.εA j)) :=
        fun j hj _ hc8 => hc8.trans (Subgroup.card_le_of_le (le_inf hj inf_le_right))
      fin_cases i
      · exact h2
      · exact h2
      · exact h8 2 (le_sup_left.trans le_sup_left) rfl hW2.2.ge
      · exact h8 3 (le_sup_right.trans le_sup_left) rfl hW3.2.ge
      · exact h8 4 le_sup_right rfl hW4.2.ge
      all_goals exact h2
    have hprod : (2 : ℕ) ^ 19 ≤ ∏ i : Fin 13, Nat.card ↥(Z ⊓ CenS (S55.hyp h5.εA i)) := by
      refine le_trans (le_of_eq ?_) (Finset.prod_le_prod (fun i _ => hlow i))
      decide
    have hpow : Nat.card ↥(Z ⊓ CenS (A₁sub b b₁ b₂ b₃)) ^ 12 ≤ 2 ^ 12 := Nat.pow_le_pow_left hcen 12
    have : 2 ^ 19 ≤ Nat.card Z * 2 ^ 12 :=
      hprod.trans (hw.symm.le.trans (Nat.mul_le_mul_left _ hpow))
    have := Nat.mul_le_mul_left (Nat.card Z) hi
    omega
  haveI : CFSG.IsElementaryAbelian 2 ↥Z := CFSG.IsElementaryAbelian.two_of_forall_mul_self hZc hZ2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 2 ↥Z (Subgroup.zpowers ⟨s₀, hs₀Z⟩)
  set S₀ := C.map Z.subtype with hS₀
  have hS₀Z : S₀ ≤ Z := Subgroup.map_subtype_le C
  have hcS₀ : Nat.card S₀ = 64 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers ⟨s₀, hs₀Z⟩) C
      fun x _ y _ => Subtype.ext (hZc _ x.2 _ y.2)).1
    rw [hC.sup_eq_top, hC.inf_eq_bot, Subgroup.card_top, Subgroup.card_bot, Nat.card_zpowers,
      Subgroup.orderOf_mk, h5.hs₀, hcZ, mul_one] at h
    rw [hS₀, Subgroup.card_map_of_injective Z.subtype_injective]
    omega
  have hs₀S₀ : s₀ ∉ S₀ := by
    rintro ⟨c, hc, hcs⟩
    have hc' : c = ⟨s₀, hs₀Z⟩ := Subtype.ext hcs
    have hmem : c ∈ Subgroup.zpowers ⟨s₀, hs₀Z⟩ ⊓ C := ⟨hc' ▸ Subgroup.mem_zpowers _, hc⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hs₀1 (by rw [← hcs, hmem]; rfl)
  set f := S55.wel g [1] with hf
  have hfs : f * s₀ * f⁻¹ = s₀ := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (S55.wel_cen hgH [1])), mul_inv_cancel_right]
  set X := h5.W 8 ⊔ h5.W 7 with hXdef
  set Y := h5.W 6 ⊔ h5.W 5 with hYdef
  have hYeq : conjBy f X = Y := by
    rw [hXdef, conjBy, Subgroup.map_sup, ← conjBy, ← conjBy,
      h5.conjBy_W hgH hg (w := [1]) (r := 8) (i := 6) (by decide),
      h5.conjBy_W hgH hg (w := [1]) (r := 7) (i := 5) (by decide)]
  have hY : ExtraspecialAt Y s₀ := by
    have := hX.conj f
    rw [hfs] at this
    rw [← hYeq]; exact this
  have hXY : X ≤ CenS Y :=
    sup_le (S55.le_cenS_sup (S55.cenS_symm c68) (S55.cenS_symm c58))
      (S55.le_cenS_sup (S55.cenS_symm c67) (S55.cenS_symm c57))
  have hXYc := S55.comm_of_le_cenS hXY
  set S₁ := X ⊔ Y with hS₁
  have hXS : X ≤ Op 2 (Cen s₀) := sup_le (hWS 8) (hWS 7)
  have hYS : Y ≤ Op 2 (Cen s₀) := sup_le (hWS 6) (hWS 5)
  have hS₁S : S₁ ≤ Op 2 (Cen s₀) := sup_le hXS hYS
  have hXYint : ∀ q ∈ X ⊓ Y, q = 1 ∨ q = s₀ := fun q hq =>
    hX.center_le q (Subgroup.mem_inf.mp hq).1 fun y hy =>
      (hXYc y hy q (Subgroup.mem_inf.mp hq).2).symm
  have hcXY : Nat.card ↥(X ⊓ Y) = 2 :=
    card_eq_two_of_le h5.hs₀ (Subgroup.mem_inf.mpr ⟨hX.mem, hY.mem⟩) hXYint
  have hcS₁ : Nat.card S₁ = 2 ^ 9 := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X Y hXYc).1
    rw [hcXY, hX.card_eq, hY.card_eq] at this
    rw [hS₁]; omega
  have hdecS₁ : ∀ q ∈ S₁, ∃ x ∈ X, ∃ y ∈ Y, q = x * y := by
    intro q hq
    have hq' : q ∈ ((X ⊔ Y : Subgroup G) : Set G) := hq
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X Y hXYc).2] at hq'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hq'
    exact ⟨x, hx, y, hy, hxy.symm⟩
  have hext : IsExtraspecialPGroup 2 ↥S₁ :=
    FF84.S3.S36_ext_central_product (hS2.to_le hS₁S) hX hY hXYc hdecS₁ le_sup_left le_sup_right
  have hA' : IsElemAb 2 3 (conjBy f A) := isElemAb_conjBy hA f
  have hA'Y : conjBy f A ≤ Y := hYeq ▸ Subgroup.map_mono hAX
  have hsA' : s₀ ∈ conjBy f A := by
    rw [mem_conjBy_iff, show f⁻¹ * s₀ * f = s₀ by
      calc f⁻¹ * s₀ * f = f⁻¹ * (f * s₀ * f⁻¹) * f := by rw [hfs]
        _ = s₀ := by group]
    exact hsA
  have hAA' : Nat.card ↥(A ⊓ conjBy f A) = 2 :=
    card_eq_two_of_le h5.hs₀ (Subgroup.mem_inf.mpr ⟨hsA, hsA'⟩) fun q hq =>
      hXYint q (Subgroup.mem_inf.mpr ⟨hAX (Subgroup.mem_inf.mp hq).1, hA'Y (Subgroup.mem_inf.mp hq).2⟩)
  have hE32 := FF84.S3.S36_elemAb_sup hA hA'
    (fun x hx y hy => hXYc x (hAX hx) y (hA'Y hy)) hAA'
  have hplus : IsExtraspecialPlus 4 S₁ :=
    ⟨hext, hcS₁, A ⊔ conjBy f A, sup_le_sup hAX hA'Y, hE32⟩
  have hZS₁ : Z ≤ CenS S₁ := by
    have hi : ∀ i : Fin 13, h5.W i ≤ CenS (h5.W 8) → h5.W i ≤ CenS (h5.W 7) →
        h5.W i ≤ CenS (h5.W 6) → h5.W i ≤ CenS (h5.W 5) → h5.W i ≤ CenS S₁ :=
      fun i h8 h7 h6 h5' =>
        S55.le_cenS_sup (S55.le_cenS_sup h8 h7) (S55.le_cenS_sup h6 h5')
    exact sup_le (sup_le (hi 2 c28 c27 c26 c25) (hi 3 c38 c37 c36 c35)) (hi 4 c48 c47 c46 c45)
  have hS₀S₁ : S₀ ≤ CenS S₁ := hS₀Z.trans hZS₁
  have hZ1 : ∀ q ∈ S₁, (∀ u ∈ S₁, q * u = u * q) → q = 1 ∨ q = s₀ := by
    intro q hq hcen
    obtain ⟨x, hx, y, hy, rfl⟩ := hdecS₁ _ hq
    have hxc : x = 1 ∨ x = s₀ := hX.center_le x hx fun u hu => by
      have e1 := hcen u (Subgroup.mem_sup_left hu)
      have e2 := hXYc u hu y hy
      calc x * u = x * y * u * y⁻¹ := by rw [mul_assoc x y u, ← e2]; group
        _ = u * (x * y) * y⁻¹ := by rw [e1]
        _ = u * x := by group
    have hyc : y = 1 ∨ y = s₀ := hY.center_le y hy fun u hu => by
      have e1 := hcen u (Subgroup.mem_sup_right hu)
      have e2 := hXYc x hx u hu
      calc y * u = x⁻¹ * (x * y * u) := by group
        _ = x⁻¹ * (u * (x * y)) := by rw [e1]
        _ = x⁻¹ * (u * x) * y := by group
        _ = u * y := by rw [← e2]; group
    rcases hxc with rfl | rfl <;> rcases hyc with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl hs2
  have hbot : S₀ ⊓ S₁ = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨hq0, hq1⟩ := Subgroup.mem_inf.mp hq
    rw [Subgroup.mem_bot]
    rcases hZ1 q hq1 fun u hu => (Subgroup.mem_centralizer_iff.mp (hS₀S₁ hq0) u hu).symm with
      h | h
    · exact h
    · exact absurd (h ▸ hq0) hs₀S₀
  have hsup : S₀ ⊔ S₁ = Op 2 (Cen s₀) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (hS₀Z.trans hZS) hS₁S) ?_
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S₀ S₁
      (S55.comm_of_le_cenS hS₀S₁)).1
    rw [hbot, Subgroup.card_bot, mul_one, hcS₀, hcS₁] at this
    rw [hS, this]; norm_num
  have hdecS : ∀ q ∈ Op 2 (Cen s₀), ∃ a ∈ S₀, ∃ t ∈ S₁, q = a * t := by
    intro q hq
    have hq' : q ∈ ((S₀ ⊔ S₁ : Subgroup G) : Set G) := by rw [hsup]; exact hq
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S₀ S₁
      (S55.comm_of_le_cenS hS₀S₁)).2] at hq'
    obtain ⟨a, ha, t, ht, hat⟩ := Set.mem_mul.1 hq'
    exact ⟨a, ha, t, ht, hat.symm⟩
  have hZcen : Z ≤ CenS (Op 2 (Cen s₀)) := by
    rw [← hsup]
    refine S55.le_cenS_sup (Subgroup.le_centralizer_iff.mpr fun a ha => ?_) hZS₁
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => hZc z hz a (hS₀Z ha)
  have hcenter : Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) = Z := by
    refine le_antisymm (fun q hq => ?_) (le_inf hZS hZcen)
    obtain ⟨hqS, hqc⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨a, ha, t, ht, rfl⟩ := hdecS q hqS
    have htc : ∀ y ∈ S₁, t * y = y * t := fun y hy => by
      have e1 : a * t * y = y * (a * t) :=
        (Subgroup.mem_centralizer_iff.mp hqc y (hS₁S hy)).symm
      have e2 : a * y = y * a := S55.comm_of_le_cenS hS₀S₁ a ha y hy
      calc t * y = a⁻¹ * (a * t * y) := by group
        _ = a⁻¹ * (y * (a * t)) := by rw [e1]
        _ = a⁻¹ * (y * a) * t := by group
        _ = y * t := by rw [← e2]; group
    rcases hZ1 t ht htc with rfl | rfl
    · rw [mul_one]; exact hS₀Z ha
    · exact Z.mul_mem (hS₀Z ha) hs₀Z
  refine ⟨⟨S₀, S₁, ⟨CFSG.IsElementaryAbelian.two_of_forall_mul_self
    (fun x hx y hy => hZc x (hS₀Z hx) y (hS₀Z hy)) (fun x hx => hZ2 x (hS₀Z hx)), hcS₀⟩,
    hplus, hsup, hbot, hS₀S₁⟩, hcenter, hcZ, hZc, hZ2⟩

end Big

structure FF81Sec5.Big (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) : Prop where
  cardS : Nat.card (Op 2 (Cen s₀)) = 2 ^ 15
  cardR : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen b) = 128
  cardW1 : Nat.card (h5.W 1) = 2
  elemW2 : IsElemAb 2 3 (h5.W 2)
  conc : FF81Conc5_5 s₀
  center_eq : Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) = h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4
  cardZ : Nat.card ↥(h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4) = 2 ^ 7
  Zcomm : ∀ x ∈ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4, ∀ y ∈ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4, x * y = y * x
  Zsq : ∀ x ∈ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4, x * x = 1

section Main

variable (hKF : KF_Sp6Levi) (hKS : KF_Sp6ShortRoot)
  (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include hKF hKS h5

theorem FF81Sec5.big : h5.Big := by
  have hB := h5.basis
  obtain ⟨⟨v, hv, hv4, hv1, hvs⟩, ⟨v', hv', hv'2, hv'c, hv'1, hv's⟩, hR⟩ :=
    hKS G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen hB.monoL_stab s₀
      h5.hs₀L h5.hs₀ h5.s₀_b₁ h5.s₀_u₃ h5.hs₀b
  obtain ⟨hRL, hRp, hRn, hRs⟩ := h5.R_hyp
  have hW := h5.card_S_mul hKF
  rw [h5.W₁_eq, h5.W₂_eq, h5.W₈_eq] at hW
  rcases hR _ hRL hRp hRn hRs with ⟨hc, hc1, hc2, hc3⟩ | ⟨hc, hc1, hc2, hc3, hQ⟩ |
    ⟨hc, hc1, hc2, hc3, hT⟩ |
    ⟨hc, hc1, hc2, hc3, hEA, h82, h72, h78, hX32, hXc, hXsq, hXcomm, A, hAX, hA, hsA⟩
  · rw [hc1, hc2, hc3] at hW
    exact (h5.card_S_ne_two hKF (by omega)).elim
  · rw [hc1, hc2, hc3] at hW
    exact (h5.not_case_eight hKF (by omega) hc hc2 hQ hv hv4 hv1 hvs).elim
  · rw [hc1, hc2, hc3] at hW
    exact (h5.not_case_thirtytwo hKF (by omega) hc hc1 hT hv' hv'2 hv'c hv'1 hv's).elim
  · rw [hc1, hc2, hc3] at hW
    rw [← h5.W₂_eq] at hEA h72
    rw [← h5.W₈_eq] at h78 hX32 hXc hXsq hXcomm hAX
    rw [← h5.W₇_eq] at h72 h78 hX32 hXc hXsq hXcomm hAX
    have hX : ExtraspecialAt (h5.W 8 ⊔ h5.W 7) s₀ :=
      { card_eq := hX32
        mem := Subgroup.mem_sup_left (h5.s₀_mem_W 8)
        ne_one := fun e => by have := h5.hs₀; rw [e, orderOf_one] at this; omega
        sq_eq := by rw [← sq, ← h5.hs₀, pow_orderOf_eq_one]
        central := fun q hq => Subgroup.mem_centralizer_singleton_iff.mp
          (op_two_le s₀ (sup_le (inf_le_left : h5.W 8 ≤ _) inf_le_left hq))
        center_le := hXc
        sq_mem := hXsq
        comm_mem := hXcomm }
    have hW1 : Nat.card (h5.W 1) = 2 := by rw [h5.W₁_eq]; exact hc3
    obtain ⟨hconc, hcen, hcZ, hZc, hZ2⟩ :=
      h5.conc5_5_of_big hKF (by omega) hW1 hEA h72 h78 hX hAX hA hsA
    exact ⟨by omega, hc, hW1, hEA, hconc, hcen, hcZ, hZc, hZ2⟩

theorem FF81Sec5.conc5_5 : FF81Conc5_5 s₀ := (h5.big hKF hKS).conc

end Main

theorem ff81_5_5 (hKF : KF_Sp6Levi) (hKS : KF_Sp6ShortRoot) :
    FF81_5_5 := fun _ _ _ _ _ _ _ _ _ _ _ h5 _ _ _ _ => h5.conc5_5 hKF hKS

end CFSG.RankThree.PartTwo.Sec21.FF81
