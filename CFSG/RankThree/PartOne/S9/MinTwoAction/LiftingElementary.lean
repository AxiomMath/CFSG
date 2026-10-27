module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingElementaryMain
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelectedBase
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.PartOne.Quotient36 SemidirectProduct
open scoped IsMulCommutative commutatorElement

namespace Lifting36

section Action

variable {G : Type*} [Group G] {R A D : Subgroup G}

theorem conj_compat (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (a : ↥A) (r : ↥R) :
    conjHom hAD a * conjHom hRD r * (conjHom hAD a)⁻¹ = conjHom hRD (conjHom hAR a r) :=
  (Compat.ofSubgroups hAR hRD hAD).compat a r

@[expose, instance_reducible] noncomputable def actRA
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) :
    MulDistribMulAction (↥R ⋊[conjHom hAR] ↥A) ↥D :=
  MulDistribMulAction.compHom ↥D
    (semidirectToAut (conjHom hAR) (conjHom hRD) (conjHom hAD) (conj_compat hAR hRD hAD))

theorem actRA_inl_coe (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (r : ↥R) (x : ↥D) :
    letI := actRA hAR hRD hAD
    (((inl r : ↥R ⋊[conjHom hAR] ↥A) • x : ↥D) : G) = (r : G) * (x : G) * (r : G)⁻¹ := by
  change ((semidirectToAut (conjHom hAR) (conjHom hRD) (conjHom hAD)
    (conj_compat hAR hRD hAD) (inl r) x : ↥D) : G) = _
  rw [semidirectToAut_inl]
  exact conjHom_apply_coe hRD r x

theorem actRA_inr_coe (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (a : ↥A) (x : ↥D) :
    letI := actRA hAR hRD hAD
    (((inr a : ↥R ⋊[conjHom hAR] ↥A) • x : ↥D) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
  change ((semidirectToAut (conjHom hAR) (conjHom hRD) (conjHom hAD)
    (conj_compat hAR hRD hAD) (inr a) x : ↥D) : G) = _
  rw [semidirectToAut_inr]
  exact conjHom_apply_coe hAD a x

theorem fixed_map_eq_ra (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (s : ↥R) :
    letI := actRA hAR hRD hAD
    (fixedPointSubgroup (Subgroup.zpowers (inl s : ↥R ⋊[conjHom hAR] ↥A)) ↥D).map D.subtype =
      D ⊓ Subgroup.centralizer ({(s : G)} : Set G) := by
  let _ := actRA hAR hRD hAD
  have hfix : ∀ x : ↥D, x ∈ fixedPointSubgroup
      (Subgroup.zpowers (inl s : ↥R ⋊[conjHom hAR] ↥A)) ↥D ↔ (s : G) * x = x * (s : G) := by
    intro x
    rw [mem_fixedPointSubgroup_zpowers_iff]
    constructor
    · intro h
      have h1 : (((inl s : ↥R ⋊[conjHom hAR] ↥A) • x : ↥D) : G) = (x : G) := congrArg Subtype.val h
      rw [actRA_inl_coe hAR hRD hAD] at h1
      calc (s : G) * x = ((s : G) * x * (s : G)⁻¹) * s := by group
        _ = x * s := by rw [h1]
    · intro h
      apply Subtype.ext
      rw [actRA_inl_coe hAR hRD hAD]
      calc (s : G) * x * (s : G)⁻¹ = (x * s) * (s : G)⁻¹ := by rw [h]
        _ = x := by group
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({(s : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hfix x).mp hx).symm
  · rintro ⟨hgD, hgC⟩
    refine ⟨⟨g, hgD⟩, (hfix ⟨g, hgD⟩).mpr ?_, rfl⟩
    have hgC' : g ∈ Subgroup.centralizer ({(s : G)} : Set G) := hgC
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC'
    exact hgC'.symm

theorem le_normalizer_inf_centralizer {X Y L : Subgroup G}
    (hX : L ≤ Subgroup.normalizer (X : Set G)) (hY : L ≤ Subgroup.normalizer (Y : Set G)) :
    L ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hX hc) x).mp hx.1,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (hY (L.inv_mem hc)) y).mp hy
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
  calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
    _ = (c * x * c⁻¹) * y := by group

theorem le_normalizer_commutator {H₁ H₂ L : Subgroup G}
    (h₁ : L ≤ Subgroup.normalizer (H₁ : Set G)) (h₂ : L ≤ Subgroup.normalizer (H₂ : Set G)) :
    L ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro g hg _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  rw [conjugate_commutatorElement]
  exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp (h₁ hg) g₁).mp hg₁)
    ((Subgroup.mem_normalizer_iff.mp (h₂ hg) g₂).mp hg₂)

end Action

section Invariant

variable {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S} {D : Type*} [Group D]
  [MulDistribMulAction (S ⋊[φ] A) D]

theorem invariant_of_inl_inr (Y : Subgroup D)
    (hl : ∀ s : S, ∀ y ∈ Y, (inl s : S ⋊[φ] A) • y ∈ Y)
    (hr : ∀ a : A, ∀ y ∈ Y, (inr a : S ⋊[φ] A) • y ∈ Y) :
    ∀ γ : S ⋊[φ] A, ∀ y ∈ Y, γ • y ∈ Y := by
  intro γ y hy
  rw [← inl_left_mul_inr_right γ, mul_smul]
  exact hl _ _ (hr _ _ hy)

end Invariant

end Lifting36

theorem elementarySmallActionWholeGroupLifting_of
    (hEFQKE : ElementaryFaithfulQuotientKernelElimination) :
    ElementarySmallActionWholeGroupLifting := by
  intro G _ _ p q d A D R hp hq hq2 hqp hpd hAel hAcard hAR hRel hRcard hB hirrAR hLD hDq hDexp
    hDcl hRD hrank
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian p ↥A := hAel
  have : IsElementaryAbelian 2 ↥R := hRel
  have hp3 : 3 < p := by rcases hpd with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hq1 : 1 < q := hq.one_lt
  have hRD' : R ≤ Subgroup.normalizer (D : Set G) := le_sup_left.trans hLD
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_sup_right.trans hLD
  have hK0 : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
    rcases hirrAR _ inf_le_left (Lifting36.le_normalizer_inf_centralizer hAR hAD) with h | h
    · exact h
    · exfalso
      apply hRD
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h.symm.le.trans inf_le_right
  let _ := Lifting36.actRA hAR hRD' hAD
  have hφ : Nat.card (conjHom hAR).range = p := by
    have h1 := Subgroup.card_ker_mul_card_range (conjHom hAR)
    have hker : (conjHom hAR).ker = (A ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A := by
      rw [ker_conjHom_eq]
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    have h2 : Nat.card (conjHom hAR).ker = p := by
      rw [hker, ← hB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h3 : p * Nat.card (conjHom hAR).range = p * p := by
      calc p * Nat.card (conjHom hAR).range = Nat.card (conjHom hAR).ker *
            Nat.card (conjHom hAR).range := by rw [h2]
        _ = Nat.card ↥A := h1
        _ = p ^ 2 := hAcard
        _ = p * p := by ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h3
  have hirr : ∀ U : Subgroup ↥R, (∀ a : ↥A, ∀ x ∈ U, conjHom hAR a x ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hYR : U.map R.subtype ≤ R := Subgroup.map_subtype_le U
    have hAY : A ≤ Subgroup.normalizer ((U.map R.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_of_conj_mem fun c hc y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hy
      exact ⟨conjHom hAR ⟨c, hc⟩ u, hU ⟨c, hc⟩ u hu, conjHom_apply_coe hAR ⟨c, hc⟩ u⟩
    rcases hirrAR _ hYR hAY with h | h
    · left
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      have : (u : G) ∈ U.map R.subtype := ⟨u, hu, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · right
      rw [Subgroup.eq_top_iff']
      intro u
      have : (u : G) ∈ U.map R.subtype := by rw [h]; exact u.2
      obtain ⟨u', hu', hu'u⟩ := this
      rw [← Subtype.ext hu'u]
      exact hu'
  have hDexp' : ∀ x : ↥D, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hDexp x x.2)
  have hDcl' : commutator ↥D ≤ Subgroup.center ↥D :=
    Lifting36.commutator_le_center_of_commutator_eq_bot D hDcl
  have hfaith : ∀ s : ↥R, (∀ x : ↥D, (inl s : ↥R ⋊[conjHom hAR] ↥A) • x = x) → s = 1 := by
    intro s hs
    have hc : (s : G) ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : (((inl s : ↥R ⋊[conjHom hAR] ↥A) • (⟨y, hy⟩ : ↥D) : ↥D) : G) = y :=
        congrArg Subtype.val (hs ⟨y, hy⟩)
      rw [Lifting36.actRA_inl_coe hAR hRD' hAD] at h1
      calc y * (s : G) = ((s : G) * y * (s : G)⁻¹) * s := by rw [h1]
        _ = s * y := by group
    have : (s : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := ⟨s.2, hc⟩
    rw [hK0, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hfixrank : ∀ s : ↥R, CFSG.pRank q ↥(fixedPointSubgroup
      (Subgroup.zpowers (inl s : ↥R ⋊[conjHom hAR] ↥A)) ↥D) =
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({(s : G)} : Set G)) := by
    intro s
    rw [← pRank_map_subtype hq1, Lifting36.fixed_map_eq_ra hAR hRD' hAD s]
  have hne1 : ∀ s : ↥R, s ≠ 1 → (s : G) ≠ 1 := fun s hs h => hs (Subtype.ext h)
  have hrank' : ∀ s : ↥R, s ≠ 1 → CFSG.pRank q ↥(fixedPointSubgroup
      (Subgroup.zpowers (inl s : ↥R ⋊[conjHom hAR] ↥A)) ↥D) ≤ 3 := fun s hs => by
    rw [hfixrank s]
    exact hrank s s.2 (hne1 s hs)
  obtain ⟨hEA, hcard, hirrD, h7, h5⟩ := Lifting36.whole_group_lifting_core (p := p) (q := q)
    (d := d) (S := ↥R) (A := ↥A) (φ := conjHom hAR) (D := ↥D) hp hq hq2 hqp.symm hpd hRcard hφ
    hirr hDq hDexp' hDcl' hfaith hrank'
  have hDRle : ⁅D, R⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_left.mp hRD'
  have hDR : ⁅D, R⁆ = D := by
    have hAcomm := Lifting36.le_normalizer_commutator hAD hAR
    have hY : ∀ γ : ↥R ⋊[conjHom hAR] ↥A, ∀ y ∈ (⁅D, R⁆).subgroupOf D,
        γ • y ∈ (⁅D, R⁆).subgroupOf D := by
      refine Lifting36.invariant_of_inl_inr _ ?_ ?_
      · intro s y hy
        have hy' : (y : G) ∈ ⁅D, R⁆ := Subgroup.mem_subgroupOf.mp hy
        refine Subgroup.mem_subgroupOf.mpr ?_
        rw [Lifting36.actRA_inl_coe hAR hRD' hAD]
        have h1 : ⁅(y : G), (s : G)⁆ ∈ ⁅D, R⁆ :=
          Subgroup.commutator_mem_commutator (hDRle hy') s.2
        have h2 : (s : G) * y * (s : G)⁻¹ = ⁅(y : G), (s : G)⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [h2]
        exact mul_mem (inv_mem h1) hy'
      · intro a y hy
        have hy' : (y : G) ∈ ⁅D, R⁆ := Subgroup.mem_subgroupOf.mp hy
        refine Subgroup.mem_subgroupOf.mpr ?_
        rw [Lifting36.actRA_inr_coe hAR hRD' hAD]
        exact (Subgroup.mem_normalizer_iff.mp (hAcomm a.2) y).mp hy'
    rcases hirrD _ hY with h | h
    · exfalso
      apply hRD
      rw [Subgroup.commutator_comm]
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      have : (⟨g, hDRle hg⟩ : ↥D) ∈ (⁅D, R⁆).subgroupOf D := Subgroup.mem_subgroupOf.mpr hg
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · refine le_antisymm hDRle fun g hg => ?_
      have : (⟨g, hg⟩ : ↥D) ∈ (⁅D, R⁆).subgroupOf D := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hDC : D ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
    have hAC := Lifting36.le_normalizer_inf_centralizer hAD hAR
    have hY : ∀ γ : ↥R ⋊[conjHom hAR] ↥A, ∀ y ∈ (D ⊓ Subgroup.centralizer (R : Set G)).subgroupOf D,
        γ • y ∈ (D ⊓ Subgroup.centralizer (R : Set G)).subgroupOf D := by
      refine Lifting36.invariant_of_inl_inr _ ?_ ?_
      · intro s y hy
        have hy' : (y : G) ∈ D ⊓ Subgroup.centralizer (R : Set G) := Subgroup.mem_subgroupOf.mp hy
        refine Subgroup.mem_subgroupOf.mpr ?_
        rw [Lifting36.actRA_inl_coe hAR hRD' hAD]
        have h1 : (s : G) * y = y * (s : G) := Subgroup.mem_centralizer_iff.mp hy'.2 s s.2
        have h2 : (s : G) * y * (s : G)⁻¹ = y := by rw [h1]; group
        rw [h2]
        exact hy'
      · intro a y hy
        have hy' : (y : G) ∈ D ⊓ Subgroup.centralizer (R : Set G) := Subgroup.mem_subgroupOf.mp hy
        refine Subgroup.mem_subgroupOf.mpr ?_
        rw [Lifting36.actRA_inr_coe hAR hRD' hAD]
        exact (Subgroup.mem_normalizer_iff.mp (hAC a.2) y).mp hy'
    rcases hirrD _ hY with h | h
    · rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      have : (⟨g, hg.1⟩ : ↥D) ∈ (D ⊓ Subgroup.centralizer (R : Set G)).subgroupOf D :=
        Subgroup.mem_subgroupOf.mpr hg
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hRD
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g hg
      have : (⟨g, hg⟩ : ↥D) ∈ (D ⊓ Subgroup.centralizer (R : Set G)).subgroupOf D := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
  have hΦ : inSubgroup frattini D = ⊥ := Lifting36.inSubgroup_frattini_eq_bot hq hEA
  have hFrat : IsFrattiniIrreducibleFor (R ⊔ A) D := by
    refine ⟨hLD, ?_, ?_⟩
    · rw [hΦ]
      refine bot_lt_iff_ne_bot.mpr fun hD => hRD ?_
      rw [hD]
      exact Subgroup.commutator_bot_right R
    · intro Y _ hYD hLY
      have hRY : R ≤ Subgroup.normalizer (Y : Set G) := le_sup_left.trans hLY
      have hAY : A ≤ Subgroup.normalizer (Y : Set G) := le_sup_right.trans hLY
      have hY : ∀ γ : ↥R ⋊[conjHom hAR] ↥A, ∀ y ∈ Y.subgroupOf D, γ • y ∈ Y.subgroupOf D := by
        refine Lifting36.invariant_of_inl_inr _ ?_ ?_
        · intro s y hy
          refine Subgroup.mem_subgroupOf.mpr ?_
          rw [Lifting36.actRA_inl_coe hAR hRD' hAD]
          exact (Subgroup.mem_normalizer_iff.mp (hRY s.2) y).mp (Subgroup.mem_subgroupOf.mp hy)
        · intro a y hy
          refine Subgroup.mem_subgroupOf.mpr ?_
          rw [Lifting36.actRA_inr_coe hAR hRD' hAD]
          exact (Subgroup.mem_normalizer_iff.mp (hAY a.2) y).mp (Subgroup.mem_subgroupOf.mp hy)
      rcases hirrD _ hY with h | h
      · left
        rw [hΦ, Subgroup.eq_bot_iff_forall]
        intro g hg
        have : (⟨g, hYD hg⟩ : ↥D) ∈ Y.subgroupOf D := Subgroup.mem_subgroupOf.mpr hg
        rw [h, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      · right
        refine le_antisymm hYD fun g hg => ?_
        have : (⟨g, hg⟩ : ↥D) ∈ Y.subgroupOf D := by rw [h]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
  have hRR : ⁅R, R⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥R) ⟨x, hx⟩)
  have hlast : ⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥ ∨ q % p = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hEFQKE G p q d A D R D hp hq hp3 hq2 hqp.symm hpd hAel
      hAcard (IsElementaryAbelian.isPGroup 2 ↥R) hAR hLD hDq hDexp hDcl hrank le_rfl hFrat
      (by rw [hRR]; exact bot_le)
      (fun r hr => by
        rw [elemPow_eq_one_of_isElementaryAbelian (A := R) r hr]
        exact Subgroup.one_mem _)
      (by rw [hK0, Subgroup.relIndex_bot_left]; exact hRcard)
      (fun Y _ hYR hAY => by rw [hK0]; exact hirrAR Y hYR hAY) hB
    exact h
  refine ⟨hK0, hEA, hcard, hDR, hDC, hFrat, ?_, ?_, hlast⟩
  · intro hp7 r hr hr1
    have := h7 hp7 ⟨r, hr⟩ (fun h => hr1 (congrArg Subtype.val h))
    rw [hfixrank] at this
    exact this
  · intro hp5
    obtain ⟨c1, c2⟩ := h5 hp5
    have hset : ∀ n : ℕ, {r : G | r ∈ R ∧ r ≠ 1 ∧
        CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = n} =
        Subtype.val '' {s : ↥R | s ≠ 1 ∧ CFSG.pRank q ↥(fixedPointSubgroup
          (Subgroup.zpowers (inl s : ↥R ⋊[conjHom hAR] ↥A)) ↥D) = n} := by
      intro n
      ext r
      constructor
      · rintro ⟨hr, hr1, hrn⟩
        refine ⟨⟨r, hr⟩, ⟨fun h => hr1 (congrArg Subtype.val h), ?_⟩, rfl⟩
        rw [hfixrank]
        exact hrn
      · rintro ⟨s, ⟨hs1, hsn⟩, rfl⟩
        refine ⟨s.2, fun h => hs1 (Subtype.ext h), ?_⟩
        rw [← hfixrank]
        exact hsn
    refine ⟨?_, ?_⟩
    · rw [hset 3, Set.ncard_image_of_injective _ Subtype.val_injective]
      exact c1
    · rw [hset 1, Set.ncard_image_of_injective _ Subtype.val_injective]
      exact c2

end CFSG.RankThree.PartOne
