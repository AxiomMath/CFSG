module

public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecA1011E
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixHyp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

theorem isSimpleGroup_SL_two {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n)
    (by omega) (Or.inl hn)
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, eq_bot_iff]
    rintro A ⟨c, -, hA⟩
    have hc : c = 1 := Subsingleton.elim _ _
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [hA, hc]
    simp
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem card_SL_four_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_four]

theorem card_SL_five_two : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_five]

theorem not_surjective_statedSL {K : Type} [Group K] (hK : Nat.card K = 168) (n : ℕ)
    (hn : n = 4 ∨ n = 5) (π : ↥(StatedSL n (ZMod 2)) →* K) : ¬ Function.Surjective π := by
  intro hπ
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)
  set π' := π.comp e.toMonoidHom with hπ'def
  have hπ' : Function.Surjective π' := hπ.comp e.surjective
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    isSimpleGroup_SL_two (by omega)
  rcases hs.eq_bot_or_eq_top_of_normal π'.ker with h | h
  · have hinj : Function.Injective π' := (MonoidHom.ker_eq_bot_iff _).mp h
    have hc := Nat.card_eq_of_bijective π' ⟨hinj, hπ'⟩
    rcases hn with rfl | rfl
    · rw [card_SL_four_two, hK] at hc
      norm_num at hc
    · rw [card_SL_five_two, hK] at hc
      norm_num at hc
  · have hall : ∀ k : K, k = 1 := by
      intro k
      obtain ⟨x, rfl⟩ := hπ' k
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
    have h1 : Nat.card K = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

theorem isQuasisimple_of_simple' {X : Type} [Group X] [hs : IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  obtain ⟨h1, h2⟩ := isQuasisimple_of_simple hnc
  have hcen : Subgroup.center X = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  refine ⟨Group.isPerfect_def.mpr h1, h2, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hcen,
    Subgroup.mem_bot] at h
  exact inv_mul_eq_one.mp h

variable {G : Type} [Group G]

@[expose] noncomputable def autOnEquivQuotOf {L W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hC : L ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 L) :
    ↥(autOn L W) ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
  let ψ : ↥L →* ↥(autOn L W) :=
    ((conjAct W).comp (Subgroup.inclusion hLW)).codRestrict _
      fun l => ⟨Subgroup.inclusion hLW l, l.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ψ.ker = CFSG.pCore 2 ↥L := by
    rw [← subgroupOf_pCoreOf, ← hC]
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨l.2, A4.conjAct_eq_one_iff.mp (congrArg Subtype.val h)⟩
    · intro h
      exact Subtype.ext (A4.conjAct_eq_one_iff.mpr h.2)
  (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)

theorem le_normalizer_conjugate_of {L J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hLJ : L ≤ Subgroup.normalizer (J : Set G)) :
    L ≤ Subgroup.normalizer (CFSG.conjugate J g : Set G) := by
  intro l hl
  have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
  have hw : CFSG.conjugate J (g * l * g⁻¹) = J := conjugate_eq_self_iff.mpr (hLJ hgl)
  rw [← conjugate_eq_self_iff, conjugate_conjugate,
    show g * l = (g * l * g⁻¹) * g by group, ← conjugate_conjugate, hw]

variable [Finite G] {T L I : Subgroup G}

theorem facts_of_two
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (hyp : Ch10.Hyp10 G T L I) (hcard : Nat.card ↥I = 2 ^ 3)
    {s : G} (hU : fsuUL T L I = I ⊔ CFSG.conjugate I s) :
    L ≤ Subgroup.normalizer (I : Set G) ∧ ⁅I, L⁆ ≠ ⊥ ∧ autOn L I = ⊤ := by
  obtain ⟨hab, hel, -⟩ := hyp.three
  have hIU : I ≤ fsuUL T L I := hU ▸ le_sup_left
  obtain ⟨hLI, hcomm⟩ := le_normalizer_and_commutator_ne_bot h37 h38 hyp hIU
  have hC := inf_centralizer_le_pCoreOf h37 h38 hyp hLI hcomm
  have hIab : IsMulCommutative ↥I := isMulCommutative_of_le (le_fsuVM T L I)
  have h2 : ∀ w : ↥I, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hel.2 _ (le_fsuVM T L I w.2))
  have hAut : Nat.card (MulAut ↥I) = 168 := by
    rw [card_mulAut_of_sq_eq_one h2 hcard, card_GL_three_two]
  have hdvd1 := card_quot_dvd_card_autOn hLI hC
  have hdvd2 : Nat.card ↥(autOn L I) ∣ 168 := hAut ▸ Subgroup.card_subgroup_dvd_card _
  have hL32 : LBarL32 L :=
    lBarL32_of_shape_dvd (hshape G T L I hyp.fsu hyp.lt hyp.three) (hdvd1.trans hdvd2)
  have hLcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    obtain ⟨e⟩ := hL32
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three]
  refine ⟨hLI, hcomm, (Subgroup.card_eq_iff_eq_top _).mp ?_⟩
  rw [hAut]
  exact Nat.dvd_antisymm hdvd2 (hLcard ▸ hdvd1)

omit [Finite G] in
theorem irr_of_autOn_eq_top {L I : Subgroup G} [IsMulCommutative ↥I]
    (h2 : ∀ w : ↥I, w ^ 2 = 1) (hcard : Nat.card ↥I = 2 ^ 3) (htop : autOn L I = ⊤) :
    ∀ J : Subgroup G, J ≤ I → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = I := by
  have : Finite ↥I := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  intro J hJI hLJ
  obtain ⟨K, _, _, -, π, hreal⟩ := binaryNaturalSL_three_of_eq_top h2 hcard htop
  obtain ⟨-, -, hirr⟩ := B5.isIrr_of_realizes (by norm_num) hreal
  have hinv : XMod.IsInv ↥(autOn L I) (J.subgroupOf I) :=
    (isInv_iff _ _).mpr (InternalSec.autOn_inv_subgroupOf hLJ)
  rcases hirr _ hinv bot_le le_top with h | h
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le hJI, h, Subgroup.map_bot]
  · exact Or.inr (le_antisymm hJI (Subgroup.subgroupOf_eq_top.mp h))

end CFSG.Quasithin.Vol2.Ch10.SecA
