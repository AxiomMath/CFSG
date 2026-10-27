module

public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal
import CFSG.LieType.Chevalley.OddG2ToralInvolutionComponents
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog (map_eq_one_of_commutator_eq_top)
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.GroupTheory.SteinbergBM (center_eq_bot_of_isSimpleGroup
  isPerfect_of_isSimpleGroup_of_noncomm)

theorem not_le_of_isQuasisimple_of_center_ne_bot {X : Type*} [Group X] {S Q : Subgroup X}
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hq : CFSG.IsQuasisimple Q) (hz : center Q ≠ ⊥) : ¬ S ≤ Q := by
  intro hSQ
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
    (hSn.subgroupOf Q) with h | h
  ·
    have hQS : Q ≤ S := fun x hx => by
      have hx' : (⟨x, hx⟩ : Q) ∈ S.subgroupOf Q := h ▸ mem_top _
      exact hx'
    obtain ⟨z, hz1⟩ := (ne_bot_iff_exists_ne_one).mp hz
    have hzS : (⟨((z : Q) : X), hQS (z : Q).2⟩ : S) ∈ center S := by
      refine mem_center_iff.mpr fun s => Subtype.ext ?_
      have hc := mem_center_iff.mp z.2 ⟨s, hSQ s.2⟩
      have hc' : (s : X) * ((z : Q) : X) = ((z : Q) : X) * (s : X) := congrArg Subtype.val hc
      exact hc'
    rw [center_eq_bot_of_isSimpleGroup hSnab, mem_bot] at hzS
    apply hz1
    have h1 : ((z : Q) : X) = 1 := congrArg Subtype.val hzS
    exact Subtype.ext (Subtype.ext h1)
  ·
    obtain ⟨a, b, hab⟩ := hSnab
    apply hab
    have hb : (⟨b, hSQ b.2⟩ : Q) ∈ center Q := h (mem_subgroupOf.mpr b.2)
    have hab' : (a : X) * b = b * a := congrArg Subtype.val (mem_center_iff.mp hb ⟨a, hSQ a.2⟩)
    exact Subtype.ext hab'

theorem not_normal_simple_of_central_product {X : Type*} [Group X] {R Q₁ Q₂ : Subgroup X}
    [R.Normal] (hsolv : Group.IsSolvable (X ⧸ R)) (hR : R = Q₁ ⊔ Q₂) (hQ : ⁅Q₁, Q₂⁆ = ⊥)
    (hq₁ : CFSG.IsQuasisimple Q₁) (hq₂ : CFSG.IsQuasisimple Q₂) (hz₁ : center Q₁ ≠ ⊥)
    (hz₂ : center Q₂ ≠ ⊥) (S : Subgroup X) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) : False := by
  have : Group.IsPerfect S := isPerfect_of_isSimpleGroup_of_noncomm hSnab
  have hSR : S ≤ R := fun x hx => by
    have h := map_eq_one_of_commutator_eq_top
      Group.IsPerfect.commutator_eq_top ((QuotientGroup.mk' R).comp S.subtype) ⟨x, hx⟩
    rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have h21 : Q₂ ≤ centralizer (Q₁ : Set X) := by
    rw [commutator_comm] at hQ
    exact commutator_eq_bot_iff_le_centralizer.mp hQ
  have h12 : Q₁ ≤ centralizer (Q₂ : Set X) := commutator_eq_bot_iff_le_centralizer.mp hQ
  have hRN₁ : R ≤ normalizer (Q₁ : Set X) :=
    hR ▸ sup_le le_normalizer (h21.trans (centralizer_le_normalizer _))
  have hRN₂ : R ≤ normalizer (Q₂ : Set X) :=
    hR ▸ sup_le (h12.trans (centralizer_le_normalizer _)) le_normalizer
  have hcase : ∀ Q : Subgroup X, R ≤ normalizer (Q : Set X) → Q ≤ R →
      CFSG.IsQuasisimple Q → center Q ≠ ⊥ → ∀ s ∈ S, ∀ x ∈ Q, s * x = x * s := by
    intro Q hRN hQR hq hz s hs x hx
    have hN : (Q.subgroupOf S).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.mp (hRN (hSR g.2)) n).mp hn⟩
    rcases hN.eq_bot_or_eq_top with h | h
    ·
      have hc1 : s * x * s⁻¹ * x⁻¹ ∈ S := by
        rw [show s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) by group]
        exact mul_mem hs (hSn.conj_mem _ (inv_mem hs) x)
      have hc2 : s * x * s⁻¹ * x⁻¹ ∈ Q :=
        mul_mem ((mem_normalizer_iff.mp (hRN (hSR hs)) x).mp hx) (inv_mem hx)
      have hc : (⟨_, hc1⟩ : S) ∈ Q.subgroupOf S := mem_subgroupOf.mpr hc2
      rw [h, mem_bot] at hc
      have hc' : s * x * s⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hc
      calc s * x = s * x * s⁻¹ * x⁻¹ * (x * s) := by group
        _ = x * s := by rw [hc', one_mul]
    ·
      exfalso
      refine not_le_of_isQuasisimple_of_center_ne_bot hSn hSs hSnab hq hz fun y hy => ?_
      have hy' : (⟨y, hy⟩ : S) ∈ Q.subgroupOf S := h ▸ mem_top _
      exact hy'
  have hc₁ := hcase Q₁ hRN₁ (hR ▸ le_sup_left) hq₁ hz₁
  have hc₂ := hcase Q₂ hRN₂ (hR ▸ le_sup_right) hq₂ hz₂
  have hSC : R ≤ centralizer (S : Set X) := by
    rw [hR, sup_le_iff]
    exact ⟨fun x hx => mem_centralizer_iff.mpr fun s hs => hc₁ s hs x hx,
      fun x hx => mem_centralizer_iff.mpr fun s hs => hc₂ s hs x hx⟩
  obtain ⟨a, b, hab⟩ := hSnab
  exact hab (Subtype.ext (mem_centralizer_iff.mp (hSC (hSR b.2)) a a.2))

theorem center_SL_two_ne_bot {F : Type*} [Field F] (hF : ringChar F ≠ 2) :
    center (Matrix.SpecialLinearGroup (Fin 2) F) ≠ ⊥ := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_neg, Matrix.det_one]
    simp
  set z : Matrix.SpecialLinearGroup (Fin 2) F := ⟨-1, hdet⟩
  have hz : z ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    mem_center_iff.mpr fun A => Subtype.ext (by
      change (A : Matrix (Fin 2) (Fin 2) F) * -1 = -1 * (A : Matrix (Fin 2) (Fin 2) F)
      rw [mul_neg, mul_one, neg_mul, one_mul])
  have hz1 : z ≠ 1 := fun h => by
    have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [z, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact Ring.neg_one_ne_one_of_char_ne_two hF h00
  exact (ne_bot_iff_exists_ne_one).mpr ⟨⟨z, hz⟩, fun h => hz1 (congrArg Subtype.val h)⟩

theorem center_ne_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center A ≠ ⊥) : center B ≠ ⊥ := by
  obtain ⟨z, hz⟩ := (ne_bot_iff_exists_ne_one).mp h
  refine (ne_bot_iff_exists_ne_one).mpr ⟨⟨e z, mem_center_iff.mpr fun b => ?_⟩, fun h' => ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, mem_center_iff.mp z.2 a]
  · apply hz
    apply Subtype.ext
    apply e.injective
    have h1 : e (z : A) = 1 := congrArg Subtype.val h'
    rw [h1, Subgroup.coe_one, map_one]

theorem exists_finset_card_four_of_le {F : Type*} [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact ⟨t, ht⟩

theorem not_normal_simple_of_SL_two_pair {F : Type} [Field F] (hF2 : ringChar F ≠ 2)
    (h4 : ∃ s : Finset F, s.card = 4) {X Rs Qa Qb : Subgroup (ModGL .G2 F)}
    (hRs : Rs = Qa ⊔ Qb) (hcomm : ⁅Qa, Qb⁆ = ⊥) (ea : SL2 F ≃* Qa) (eb : SL2 F ≃* Qb)
    (hRX : Rs ≤ X) (hRn : (Rs.subgroupOf X).Normal)
    (hsolv : Group.IsSolvable (X ⧸ Rs.subgroupOf X)) (S : Subgroup X) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) : False := by
  have hQaX : Qa ≤ X := le_trans (hRs ▸ le_sup_left) hRX
  have hQbX : Qb ≤ X := le_trans (hRs ▸ le_sup_right) hRX
  have hR : Rs.subgroupOf X = Qa.subgroupOf X ⊔ Qb.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hQaX, map_subgroupOf_eq_of_le hQbX,
      map_subgroupOf_eq_of_le hRX, hRs]
  have hQ : ⁅Qa.subgroupOf X, Qb.subgroupOf X⁆ = ⊥ := by
    apply map_injective X.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hQaX, map_subgroupOf_eq_of_le hQbX, hcomm,
      Subgroup.map_bot]
  let ea' : SL2 F ≃* Qa.subgroupOf X := ea.trans (subgroupOfEquivOfLe hQaX).symm
  let eb' : SL2 F ≃* Qb.subgroupOf X := eb.trans (subgroupOfEquivOfLe hQbX).symm
  have hqSL := CFSG.RankThree.Classical.isQuasisimple_SL2 h4
  exact not_normal_simple_of_central_product hsolv hR hQ
    ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr ea').1 hqSL)
    ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eb').1 hqSL)
    (center_ne_bot_of_mulEquiv ea' (center_SL_two_ne_bot hF2))
    (center_ne_bot_of_mulEquiv eb' (center_SL_two_ne_bot hF2)) S hSn hSs hSnab

theorem not_normal_simple_toralCentralizer
    {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (b : Fin Tag.G2.rank → Fˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hb1 : b ≠ 1) (S : Subgroup (toralCentralizer .G2 F b)) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) : False := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hF) (Nat.even_iff.2 this)
  obtain ⟨-, -, hcases, hstruct, h3⟩ := odd_G2_toral_involution_fixed_p_components F hF b hb
  by_cases hF3 : Nat.card F = 3
  ·
    have := (h3 hF3 hb1).1
    obtain ⟨x, y, hxy⟩ := hSnab
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)
  have hF5 : 5 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    obtain ⟨k, hk⟩ := hF
    omega
  have h4 := exists_finset_card_four_of_le (F := F) (by omega)
  have key : ∀ α β : Fin Tag.G2.rank → ℤ,
      ((b = ![-1, 1] ∧ α = ![0, 1] ∧ β = ![2, 3]) ∨ (b = ![1, -1] ∧ α = ![1, 0] ∧ β = ![1, 2]) ∨
        (b = ![-1, -1] ∧ α = ![1, 1] ∧ β = ![1, 3])) → False := by
    intro α β hαβ
    obtain ⟨-, -, hRs, hcomm, -, ⟨ea⟩, ⟨eb⟩, hRX, hRn, hsolv, -⟩ := hstruct α β hαβ
    exact not_normal_simple_of_SL_two_pair hF2 h4 hRs hcomm ea eb hRX hRn hsolv S hSn hSs hSnab
  rcases hcases with h | h | h | h
  · exact hb1 h
  · exact key ![0, 1] ![2, 3] (Or.inl ⟨h, rfl, rfl⟩)
  · exact key ![1, 0] ![1, 2] (Or.inr (Or.inl ⟨h, rfl, rfl⟩))
  · exact key ![1, 1] ![1, 3] (Or.inr (Or.inr ⟨h, rfl, rfl⟩))

theorem exists_mulEquiv_toralCentralizer_of_inner
    {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup .G2 F)} {g : adjointGroup .G2 F}
    {a : Fin Tag.G2.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .G2 F, (α h : ModGL .G2 F) =
      (g : ModGL .G2 F) * rootDiagUnit .G2 a * h * (rootDiagUnit .G2 a)⁻¹ * (g : ModGL .G2 F)⁻¹)
    (hα : α ^ 2 = 1) (hα1 : α ≠ 1) :
    ∃ b : Fin Tag.G2.rank → Fˣ, (∀ i, b i = 1 ∨ b i = -1) ∧ b ≠ 1 ∧
      Nonempty (↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))) ≃*
        ↥(toralCentralizer .G2 F b)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set L := AlgebraicClosure F
  set ι := algebraMap F L with hι
  set p := ringChar F with hp_def
  have hpF : CharP F p := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : F, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set bL : Fin Tag.G2.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with hbL
  set x := baseChangeGL ι (g : ModGL .G2 F) * rootDiagUnit .G2 bL with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .G2 F hF L ι
  have hgG : baseChangeGL ι (g : ModGL .G2 F) ∈ adjointGroup .G2 L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup .G2 L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift .G2 L bL).1
  have hdb : baseChangeGL ι (rootDiagUnit .G2 a) = rootDiagUnit .G2 bL :=
    baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup .G2 F,
      x * baseChangeGL ι (h : ModGL .G2 F) * x⁻¹ = baseChangeGL ι (α h : ModGL .G2 F) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .G2 F hF L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit .G2 bL) = rootDiagUnit .G2 bL := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag bL) = rootDiag bL
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup .G2 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup .G2 F) => φ h) hα
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  obtain ⟨h, -, a', ha', hhx, -, hCh, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components .G2 F L (Or.inl rfl) hF Fr
      hFr hxR hx2
  let φ : adjointGroup .G2 F →* ModGL .G2 L := (baseChangeGL ι).comp (adjointGroup .G2 F).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))).map φ =
      (adjointGroup .G2 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL .G2 F) * x = x * baseChangeGL ι (c : ModGL .G2 F)
      calc baseChangeGL ι (c : ModGL .G2 F) * x =
          (x * baseChangeGL ι (c : ModGL .G2 F) * x⁻¹) * x := by rw [h1]
        _ = x * baseChangeGL ι (c : ModGL .G2 F) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * baseChangeGL ι c * x⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  let e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))) ≃*
      ↥((adjointGroup .G2 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x}) :=
    (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)
  let e1 : ↥((adjointGroup .G2 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x}) ≃*
      ↥((adjointGroup .G2 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {rootDiagUnit .G2 a'}) :=
    ((MulAut.conj h).subgroupMap _).trans (MulEquiv.subgroupCongr hCh)
  set b : Fin Tag.G2.rank → Fˣ := fun i => if a' i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a' i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map (algebraMap F L).toMonoidHom (b i)) = a' := by
    funext i
    by_cases h1 : a' i = 1
    · simp [hb_def, h1]
    · have h2 : a' i = -1 := (ha' i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK := map_baseChangeGL_toralCentralizer (algebraMap F L) b
  rw [hab] at hXK
  let e2 : ↥(toralCentralizer .G2 F b) ≃*
      ↥((adjointGroup .G2 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {rootDiagUnit .G2 a'}) :=
    (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (algebraMap F L))).trans
      (MulEquiv.subgroupCongr hXK)
  refine ⟨b, hb, fun hb1 => hα1 ?_, ⟨e.trans (e1.trans e2.symm)⟩⟩
  have ha'1 : a' = 1 := by
    rw [← hab, hb1]
    funext i
    simp
  rw [ha'1, rootDiagUnit_one] at hhx
  have hx1 : x = 1 := by
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [hhx]; group
  refine MulEquiv.ext fun u => Subtype.ext (hinj ?_)
  rw [MulAut.one_apply, ← hxconj u, hx1, one_mul, inv_one, mul_one]

theorem not_normal_simple_of_inner_diagonal
    {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup .G2 F)} {g : adjointGroup .G2 F}
    {a : Fin Tag.G2.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .G2 F, (α h : ModGL .G2 F) =
      (g : ModGL .G2 F) * rootDiagUnit .G2 a * h * (rootDiagUnit .G2 a)⁻¹ * (g : ModGL .G2 F)⁻¹)
    (hα : α ^ 2 = 1) (hα1 : α ≠ 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) : False := by
  obtain ⟨b, hb, hb1, ⟨e⟩⟩ := exists_mulEquiv_toralCentralizer_of_inner hF hαg hα hα1
  obtain ⟨S', hS'n, hS's, hS'nab, -⟩ := exists_normal_simple_of_mulEquiv e S hSn hSs hSnab
  exact not_normal_simple_toralCentralizer hF b hb hb1 S' hS'n hS's hS'nab

end CFSG.LocalAnalysis.SteinbergBM
