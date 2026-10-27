module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Griess
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

section Abstract

theorem comm_mul_central {R : Type} [Group R] {a b z w : R} (hz : ∀ x : R, z * x = x * z)
    (hw : ∀ x : R, w * x = x * w) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ x : R, z⁻¹ * x = x * z⁻¹ := fun x => by
    have := hz x⁻¹
    calc z⁻¹ * x = (x⁻¹ * z)⁻¹ := by group
      _ = (z * x⁻¹)⁻¹ := by rw [this]
      _ = x * z⁻¹ := by group
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * z * (b * w) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹)
      = a * (z * b) * w * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * (b * z) * w * (a⁻¹ * z⁻¹) * (w⁻¹ * b⁻¹) := by rw [hz b, hz' a⁻¹]
    _ = a * b * (z * w) * (a⁻¹ * z⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * b * (w * z) * (a⁻¹ * z⁻¹) * (w⁻¹ * b⁻¹) := by rw [hz w]
    _ = a * b * w * (z * a⁻¹) * z⁻¹ * (w⁻¹ * b⁻¹) := by group
    _ = a * b * w * (a⁻¹ * z) * z⁻¹ * (w⁻¹ * b⁻¹) := by rw [hz a⁻¹]
    _ = a * b * (w * a⁻¹) * (z * z⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * w) * (w⁻¹ * b⁻¹) := by rw [hw a⁻¹]; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem normal_of_central {R : Type} [Group R] {Z : Subgroup R}
    (hZ : ∀ z ∈ Z, ∀ x : R, z * x = x * z) : Z.Normal :=
  ⟨fun z hz g => by rw [← hZ z hz g, mul_inv_cancel_right]; exact hz⟩

theorem commutator_top_le_of_sup_central {R : Type} [Group R] {E Z : Subgroup R}
    (hZ : ∀ z ∈ Z, ∀ x : R, z * x = x * z) (hEZ : E ⊔ Z = ⊤) :
    ⁅(⊤ : Subgroup R), ⊤⁆ ≤ ⁅E, E⁆ := by
  haveI : Z.Normal := normal_of_central hZ
  rw [Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ E ⊔ Z := by rw [hEZ]; exact Subgroup.mem_top x
  have hy : y ∈ E ⊔ Z := by rw [hEZ]; exact Subgroup.mem_top y
  obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨b, hb, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  rw [comm_mul_central (hZ z hz) (hZ w hw)]
  exact Subgroup.commutator_mem_commutator ha hb

variable {G : Type} [Group G] [Finite G] {H : Type} [Group H]

theorem exists_split_complement {R Q N : Subgroup G} (hQN : Q ≤ N) (hNR : N ≤ R)
    (hQnorm : (Q.subgroupOf R).Normal) (hcen : ∀ s ∈ R, ∀ x ∈ N, ⁅s, x⁆ ∈ Q) (φ : ↥R →* H)
    (hker : φ.ker = N.subgroupOf R) (hperf : commutator ↥φ.range = ⊤)
    (hGr : ∀ (E : Type) [Group E] [Finite E] (Y : Subgroup E), Y ≤ Subgroup.center E →
      commutator E = ⊤ → ∀ π : E →* H, π.range = φ.range → π.ker = Y → Y = ⊥) :
    ∃ X : Subgroup G, Q ≤ X ∧ X ≤ R ∧ N ⊔ X = R ∧ N ⊓ X = Q ∧
      (X.subgroupOf R).map φ = φ.range := by
  classical
  have hQR : Q ≤ R := hQN.trans hNR
  let mk : ↥R →* ↥R ⧸ Q.subgroupOf R := QuotientGroup.mk' (Q.subgroupOf R)
  have hQker : Q.subgroupOf R ≤ φ.ker := by
    rw [hker]
    exact Subgroup.comap_mono hQN
  let φb : (↥R ⧸ Q.subgroupOf R) →* H := QuotientGroup.lift (Q.subgroupOf R) φ hQker
  have hφb : ∀ r : ↥R, φb (mk r) = φ r := fun r => rfl
  have hmk_surj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  let Nb : Subgroup (↥R ⧸ Q.subgroupOf R) := (N.subgroupOf R).map mk
  have hNb_cen : ∀ n ∈ Nb, ∀ x : ↥R ⧸ Q.subgroupOf R, n * x = x * n := by
    rintro n ⟨n', hn', rfl⟩ x
    obtain ⟨r, rfl⟩ := hmk_surj x
    show mk n' * mk r = mk r * mk n'
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have h := hcen ((r : G)⁻¹) (R.inv_mem r.2) ((n' : G)⁻¹) (N.inv_mem hn')
    have e : (((n' * r)⁻¹ * (r * n') : ↥R) : G) = ⁅(r : G)⁻¹, (n' : G)⁻¹⁆ := by
      simp only [commutatorElement_def]
      push_cast
      group
    rw [e]
    exact h
  have hφb_range : φb.range = φ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨r, rfl⟩ := hmk_surj x
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨mk r, rfl⟩
  have hφb_ker : φb.ker = Nb := by
    ext x
    obtain ⟨r, rfl⟩ := hmk_surj x
    constructor
    · intro h
      have h1 : r ∈ φ.ker := h
      rw [hker] at h1
      exact ⟨r, h1, rfl⟩
    · rintro ⟨n', hn', hnr⟩
      have h1 : n' ∈ φ.ker := by rw [hker]; exact hn'
      rw [MonoidHom.mem_ker] at h1 ⊢
      rw [← hnr, hφb]
      exact h1
  let E : Subgroup (↥R ⧸ Q.subgroupOf R) := commutator (↥R ⧸ Q.subgroupOf R)
  have hEmap : E.map φb = φ.range := by
    have h1 : E.map φb = ⁅φb.range, φb.range⁆ := map_commutator_eq (↥R ⧸ Q.subgroupOf R) φb
    have h2 : ⁅φ.range, φ.range⁆ = φ.range := by
      have := φ.range.map_subtype_commutator
      rw [hperf, Subgroup.map_top, Subgroup.range_subtype] at this
      exact this.symm
    rw [h1, hφb_range, h2]
  have hEN : E ⊔ Nb = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : φb x ∈ E.map φb := by
      rw [hEmap, ← hφb_range]
      exact ⟨x, rfl⟩
    obtain ⟨e, he, hex⟩ := hx
    have h1 : e⁻¹ * x ∈ φb.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hex, inv_mul_cancel]
    rw [hφb_ker] at h1
    have h2 : x = e * (e⁻¹ * x) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup he h1
  have hEcomm : ⁅E, E⁆ = E := by
    refine le_antisymm (Subgroup.commutator_le_self E) ?_
    have := commutator_top_le_of_sup_central hNb_cen hEN
    rw [← _root_.commutator_def] at this
    exact this
  have hEperf : commutator ↥E = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subtype_commutator, hEcomm, Subgroup.map_top, Subgroup.range_subtype]
  let Y : Subgroup ↥E := Nb.subgroupOf E
  let π : ↥E →* H := φb.comp E.subtype
  have hYc : Y ≤ Subgroup.center ↥E := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro e
    apply Subtype.ext
    exact (hNb_cen y hy e).symm
  have hπr : π.range = φ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hEmap]
  have hπk : π.ker = Y := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hφb_ker, MonoidHom.mem_ker]
    rfl
  have hY : Y = ⊥ := hGr ↥E Y hYc hEperf π hπr hπk
  let X : Subgroup G := (E.comap mk).map R.subtype
  have hmemX : ∀ x : G, x ∈ X ↔ ∃ h : x ∈ R, mk ⟨x, h⟩ ∈ E := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.2, hr⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have hXR : X ≤ R := fun x hx => ((hmemX x).mp hx).1
  have hQX : Q ≤ X := by
    intro q hq
    refine (hmemX q).mpr ⟨hQR hq, ?_⟩
    have : mk ⟨q, hQR hq⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hq)
    rw [this]
    exact E.one_mem
  refine ⟨X, hQX, hXR, ?_, ?_, ?_⟩
  · apply le_antisymm (sup_le hNR hXR)
    intro r hr
    have hmem : mk ⟨r, hr⟩ ∈ E ⊔ Nb := by rw [hEN]; exact Subgroup.mem_top _
    obtain ⟨e, he, n, hn, hen⟩ := Subgroup.mem_sup_of_normal_right (ht := normal_of_central hNb_cen)
      |>.mp hmem
    obtain ⟨r₁, rfl⟩ := hmk_surj e
    obtain ⟨n₁, hn₁, rfl⟩ := hn
    have hq : ((r₁ * n₁)⁻¹ * ⟨r, hr⟩ : ↥R) ∈ Q.subgroupOf R := by
      have h1 : mk (r₁ * n₁) = mk ⟨r, hr⟩ := by rw [map_mul]; exact hen
      exact QuotientGroup.eq.mp h1
    have hqQ : (((r₁ * n₁)⁻¹ * ⟨r, hr⟩ : ↥R) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have hr₁X : (r₁ : G) ∈ X := (hmemX r₁).mpr ⟨r₁.2, he⟩
    have hn₁N : (n₁ : G) ∈ N := Subgroup.mem_subgroupOf.mp hn₁
    have hr_eq : r = (r₁ : G) * ((n₁ : G) * (((r₁ * n₁)⁻¹ * ⟨r, hr⟩ : ↥R) : G)) := by
      push_cast
      group
    rw [hr_eq]
    exact (sup_comm X N ▸ Subgroup.mul_mem_sup hr₁X
      (N.mul_mem hn₁N (hQN hqQ)) : (r₁ : G) * ((n₁ : G) * _) ∈ N ⊔ X)
  · apply le_antisymm
    · rintro x ⟨hxN, hxX⟩
      obtain ⟨hxR, hxE⟩ := (hmemX x).mp hxX
      have hxNb : mk ⟨x, hxR⟩ ∈ Nb := ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩
      have h1 : (⟨mk ⟨x, hxR⟩, hxE⟩ : ↥E) ∈ Y := hxNb
      rw [hY, Subgroup.mem_bot] at h1
      have h2 : mk ⟨x, hxR⟩ = 1 := congrArg Subtype.val h1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    · exact le_inf hQN hQX
  · apply le_antisymm (Subgroup.map_le_range _ _)
    rintro y ⟨r, rfl⟩
    have h1 : φb (mk r) ∈ E.map φb := by
      rw [hEmap]
      exact ⟨r, rfl⟩
    obtain ⟨e, he, hee⟩ := h1
    obtain ⟨r₁, rfl⟩ := hmk_surj e
    exact ⟨r₁, Subgroup.mem_subgroupOf.mpr ((hmemX r₁).mpr ⟨r₁.2, he⟩), hee⟩

end Abstract

section Stroth

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth65XSplitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → n = 2 * m →
    (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) → ∃ X : Subgroup G,
      Q ≤ X ∧ X ≤ Rt M (LB M Q B) t ∧ hc.CN t ⊔ X = Rt M (LB M Q B) t ∧ hc.CN t ⊓ X = Q ∧
      (∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅a, x⁆ ∈ Q) ∧
      ((OmegaPlusNat hc t m ∧ QuotSat X Q (IsOmegaPlus m (Nat.card Z))) ∨
        (OmegaMinusNat hc t m ∧ QuotSat X Q (IsOmegaMinus m (Nat.card Z))))

theorem central_of_hypPlane (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Stroth6Hyp hc n t) (hnatSO : SpNat hc t ∨ OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ hc.CN t, ⁅s, x⁆ ∈ Q := by
  obtain ⟨-, hcard, hcent, hopp⟩ := h51 G M Q Z B hc n t hs.toSec5 hnatSO r hr hplane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
    rfl rfl rfl rfl rfl
  have heq : LB M Q B ⊓ LB M Q (conjSubgroup r B) = hc.CN t :=
    Subgroup.eq_of_le_of_card_ge (hopp.1.trans hopp.2.1) (by rw [hcard, hs.cardN])
  intro s hsR x hx
  exact hcent s hsR x (heq.symm ▸ hx)

theorem exists_hypPlane_omegaPlus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 3 ≤ m)
    (h : OmegaPlusNat hc t m) :
    (SpNat hc t ∨ OmegaNat hc t) ∧
      ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_orth h34 hRoot hs hnatSO hK
    (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus m K) h3
    (addCommutantScalar_statedOmegaPlus hm)
    (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm)) hnat
  exact ⟨hnatSO, r, hr, hplane⟩

theorem exists_hypPlane_omegaMinus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m)
    (h : OmegaMinusNat hc t m) :
    (SpNat hc t ∨ OmegaNat hc t) ∧
      ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]; omega
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_orth h34 hRoot hs hnatSO hK
    (ElemMatrixIso.minus hm hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
    (addCommutantScalar_statedOmegaMinus hm hirr)
    (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr)) hnat
  exact ⟨hnatSO, r, hr, hplane⟩

theorem exists_quotEquiv_of_split {H : Type} [Group H] {R Q N X : Subgroup G} (hXR : X ≤ R)
    (hQN : Q ≤ N) (φ : ↥R →* H) (hker : φ.ker = N.subgroupOf R) (hNX : N ⊓ X = Q)
    (hXφ : (X.subgroupOf R).map φ = φ.range) {S : Subgroup H} (hS : φ.range = S) :
    ∃ _ : (Q.subgroupOf X).Normal, Nonempty (↥X ⧸ Q.subgroupOf X ≃* ↥S) := by
  let ψ : ↥X →* H := φ.comp (Subgroup.inclusion hXR)
  have hψker : ψ.ker = Q.subgroupOf X := by
    ext x
    constructor
    · intro hx
      have h1 : Subgroup.inclusion hXR x ∈ φ.ker := hx
      rw [hker] at h1
      have h2 : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp h1
      have h3 : (x : G) ∈ N ⊓ X := ⟨h2, x.2⟩
      rw [hNX] at h3
      exact Subgroup.mem_subgroupOf.mpr h3
    · intro hx
      have h1 : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
      have h2 : Subgroup.inclusion hXR x ∈ φ.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr (hQN h1)
      exact h2
  have hψrange : ψ.range = S := by
    rw [← hS, ← hXφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  haveI hn : (Q.subgroupOf X).Normal := by
    rw [← hψker]
    exact ψ.normal_ker
  exact ⟨hn, ⟨((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hψrange)⟩⟩

theorem stroth65XSplit_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hG : GriessCoverStatement) : Stroth65XSplitStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hn hΩ
  have s5 := hs.toSec5
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN s5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQnorm : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRM.trans hc.hyp.Q_normal.2)
  have hq4 := hc.hyp.q4
  have hcom : ∀ (X : Subgroup G), X ≤ Rt M (LB M Q B) t →
      (∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ hc.CN t, ⁅s, x⁆ ∈ Q) →
      ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅a, x⁆ ∈ Q := fun X hXR hcen a ha x hx => by
    rw [← commutatorElement_inv x a]
    exact Q.inv_mem (hcen x (hXR hx) a ha)
  rcases hΩ with hP | hM
  · obtain ⟨hnatSO, r, hr, hplane⟩ := exists_hypPlane_omegaPlus h34 hRoot hc s5 hm hP
    have hcen := central_of_hypPlane h51 hc hs hnatSO hr hplane
    obtain ⟨K, fK, finK, hK, φ, hφr, hφk, hsec⟩ := hP
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    have hK4 : 4 ≤ Nat.card K := hK ▸ hq4
    have hperf : commutator ↥φ.range = ⊤ := by
      rw [hφr]
      exact Group.isPerfect_def.mp (statedOmega_plus_quasisimple_of_three_le K m hm).1
    obtain ⟨X, hQX, hXR, hNX, hNXQ, hXφ⟩ := exists_split_complement hQN hNR hQnorm hcen φ hφk
      hperf (fun E _ _ Y hY hEperf π hπr hπk => by
        rcases (hG K hK4 E Y hY hEperf).2.2.1 m (by omega) π (hπr.trans hφr) hπk with h | h
        · exact h
        · exfalso
          have h1 := h ⊥ (bot_inf_eq _) ⟨inferInstance, fun x hx => by
            rw [Subgroup.mem_bot] at hx; rw [hx, one_pow]⟩ (fun e _ => by
              rw [Subgroup.normalizer_eq_top]; trivial)
          have h2 : ¬ (Nat.card K = 4 ∧ m = 2) := fun h' => by omega
          rw [if_neg h2, Subgroup.card_bot] at h1
          omega)
    obtain ⟨hn', ⟨e⟩⟩ := exists_quotEquiv_of_split hXR hQN φ hφk hNXQ hXφ hφr
    exact ⟨X, hQX, hXR, hNX, hNXQ, hcom X hXR hcen, Or.inl ⟨⟨K, fK, finK, hK, φ, hφr, hφk, hsec⟩,
      hn', K, fK, finK, hK, ⟨e⟩⟩⟩
  · obtain ⟨hnatSO, r, hr, hplane⟩ :=
      exists_hypPlane_omegaMinus h34 hRoot hc s5 (m := m) (by omega) hM
    have hcen := central_of_hypPlane h51 hc hs hnatSO hr hplane
    obtain ⟨K, fK, finK, hK, b, c, hirr, φ, hφr, hφk, hsec⟩ := hM
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    have hK4 : 4 ≤ Nat.card K := hK ▸ hq4
    have hperf : commutator ↥φ.range = ⊤ := by
      rw [hφr]
      exact Group.isPerfect_def.mp (statedOmega_minus_quasisimple_of_two_le K (by omega) hirr).1
    obtain ⟨X, hQX, hXR, hNX, hNXQ, hXφ⟩ := exists_split_complement hQN hNR hQnorm hcen φ hφk
      hperf (fun E _ _ Y hY hEperf π hπr hπk =>
        (hG K hK4 E Y hY hEperf).2.2.2 m b c (by omega) hirr π (hπr.trans hφr) hπk)
    obtain ⟨hn', ⟨e⟩⟩ := exists_quotEquiv_of_split hXR hQN φ hφk hNXQ hXφ hφr
    exact ⟨X, hQX, hXR, hNX, hNXQ, hcom X hXR hcen, Or.inr ⟨⟨K, fK, finK, hK, b, c, hirr, φ, hφr,
      hφk, hsec⟩, hn', K, fK, finK, hK, b, c, hirr, ⟨e⟩⟩⟩

end Stroth

end HS6

end CFSG.RankThree.GF2n.Stroth80
