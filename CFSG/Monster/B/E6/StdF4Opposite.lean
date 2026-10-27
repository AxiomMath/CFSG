module

public import CFSG.Monster.B.E6.StdF4LeviRoot

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.Classical
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical.UnitarySix (ProjSU IsoPt tPt isoGraph)

theorem card_eq_ncard_conjOrbit_mul {M : Type*} [Group M] [Finite M] (H : Subgroup M) (x : M) :
    Nat.card H = (conjOrbit H x).ncard * Nat.card ↥(H ⊓ Subgroup.centralizer {x}) := by
  let _ : MulAction H M := MulAction.compHom M ((MulAut.conj (G := M)).comp H.subtype)
  have hsmul : ∀ (h : H) (m : M), h • m = (h : M) * m * (h : M)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit H x = conjOrbit H x := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h x).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, hsmul _ x⟩
  have hstab : Nat.card (MulAction.stabilizer H x) =
      Nat.card ↥(H ⊓ Subgroup.centralizer {x}) := by
    have hc : ∀ h : MulAction.stabilizer H x, (h.1 : M) ∈ Subgroup.centralizer {x} := fun h =>
      Subgroup.mem_centralizer_singleton_iff.2
        (mul_inv_eq_iff_eq_mul.1 ((hsmul h.1 x).symm.trans h.2))
    have hs : ∀ h : ↥(H ⊓ Subgroup.centralizer {x}),
        (⟨h.1, (Subgroup.mem_inf.1 h.2).1⟩ : H) • x = x := fun h => by
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.2
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h.2).2)
    exact Nat.card_congr
      { toFun := fun h => ⟨h.1.1, Subgroup.mem_inf.2 ⟨h.1.2, hc h⟩⟩
        invFun := fun h => ⟨⟨h.1, (Subgroup.mem_inf.1 h.2).1⟩, hs h⟩
        left_inv := fun h => rfl
        right_inv := fun h => rfl }
  rw [← (MulAction.stabilizer H x).card_mul_index, MulAction.index_stabilizer, horb, hstab,
    mul_comm]

abbrev tMinus :
    stdGroup := repPoint 4

theorem coe_tMinus :
    (tMinus : ModGL Tag.E6 K) = pinnedX Tag.E6 K (-theta) 1 := by
  rw [coe_repPoint, repRootL_four]

theorem tMinus_mem_rootClass :
    tMinus ∈ rootClass :=
  (mem_rootClass_iff _).2 ⟨_, rfl⟩

theorem orderOf_rootInv_mul_tMinus :
    orderOf (rootInv * tMinus) = 3 :=
  orderOf_rootInv_mul_repPoint 4

theorem isRoot_neg_theta :
    IsRoot Tag.E6 (-theta) := repRootL_four ▸ isRoot_repRootL 4

theorem betaG_tMinus :
    betaG tMinus = tMinus := by
  apply Subtype.ext
  rw [coe_betaG_apply, coe_tMinus]
  exact Units.ext (by rw [betaGL_apply, entrywise_pinnedX, map_one])

theorem apply_tMinus
    (b : betaGroup) : (b : MulAut stdGroup) tMinus = tMinus := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [h]
    rfl
  · rw [h, betaG_tMinus]

theorem neg_theta_facts : ∀ i : Fin Tag.E6.rank, (i : ℕ) ≠ 1 →
    -theta ≠ Pi.single i 1 ∧ -theta ≠ -Pi.single i 1 ∧ -theta ≠ -(-Pi.single i 1) ∧
      E6Adjoint.cartanForm (-theta + Pi.single i 1) (-theta + Pi.single i 1) = 4 ∧
      E6Adjoint.cartanForm (-theta + -Pi.single i 1) (-theta + -Pi.single i 1) = 4 := by
  decide

theorem not_isRoot_of_cartanForm
    {v : Fin Tag.E6.rank → ℤ}
    (h : E6Adjoint.cartanForm v v = 4) : ¬IsRoot Tag.E6 v := fun hv => by
  rw [E6Adjoint.cartanForm_self_of_isRoot hv] at h
  exact absurd h (by decide)

theorem commute_tMinusM_pinnedX
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (hne : -theta ≠ β) (hne' : -theta ≠ -β) (hnot : ¬IsRoot Tag.E6 (-theta + β)) (c : K) :
    Commute (pinnedX Tag.E6 K (-theta) 1) (pinnedX Tag.E6 K β c) :=
  (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) isRoot_neg_theta hβ hne
    hne').2 hnot K _ (mem_rootSubgroup.2 ⟨1, rfl⟩) _ (mem_rootSubgroup.2 ⟨c, rfl⟩)

theorem ne_one_of_mem_setA {i : Fin Tag.E6.rank} (hi : i ∈ setA) : (i : ℕ) ≠ 1 := by
  rcases hi with h | h | h | h | h <;> rw [h] <;> decide

theorem groupA_le_centralizer_tMinus :
    groupA ≤ Subgroup.centralizer {(tMinus : ModGL Tag.E6 K)} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · obtain ⟨h1, h2, -, h4, -⟩ := neg_theta_facts i (ne_one_of_mem_setA hi)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, coe_tMinus, ← pinnedX_single]
    exact (commute_tMinusM_pinnedX (isRoot_single _ i) h1 h2 (not_isRoot_of_cartanForm h4)
      c).symm.eq
  · obtain ⟨-, h2, h3, -, h5⟩ := neg_theta_facts i (ne_one_of_mem_setA hi)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, coe_tMinus,
      ← pinnedX_neg_single]
    exact (commute_tMinusM_pinnedX (isRoot_neg_single _ i) h2 h3 (not_isRoot_of_cartanForm h5)
      c).symm.eq

theorem card_stdBorelG :
    Nat.card stdBorelG = 3 * 2 ^ 36 := by
  rw [← card_stdBorel]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe stdBorel_le_stdGroup).toEquiv

theorem card_stdLevi_subgroupOf :
    Nat.card ((stdLevi firstJ).subgroupOf stdGroup) = 9196830720 := by
  rw [← card_stdLevi_firstJ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe stdLevi_firstJ_le_stdGroup).toEquiv

theorem conjOrbit_PJ_tMinus :
    conjOrbit PJ tMinus = levPoints (repLevel 4) := by
  rw [tMinus, repPoint, conjOrbit_PJ_rootMap, lev_repPoint]

theorem stdLevi_subgroupOf_le :
    (stdLevi firstJ).subgroupOf stdGroup ≤
      Subgroup.centralizer {rootInv} ⊓ Subgroup.centralizer {tMinus} := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [centralizer_rootInv, Subgroup.mem_subgroupOf]
    exact stdLevi_le_nativeParabolic two_mem_firstJ hg
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1
      (groupA_le_centralizer_tMinus (stdLevi_firstJ_le_groupA hg)))

theorem centralizer_rootInv_tMinus :
    Subgroup.centralizer {rootInv} ⊓ Subgroup.centralizer {tMinus} =
      (stdLevi firstJ).subgroupOf stdGroup := by
  have hcard := card_eq_ncard_conjOrbit_mul PJ tMinus
  have h4 : repSize 4 = 2097152 := rfl
  rw [conjOrbit_PJ_tMinus, ncard_levPoints, card_PJ, card_stdBorelG, h4] at hcard
  have hPJ : PJ = Subgroup.centralizer {rootInv} := by rw [centralizer_rootInv]
  have hle : (stdLevi firstJ).subgroupOf stdGroup ≤ PJ ⊓ Subgroup.centralizer {tMinus} := by
    rw [hPJ]
    exact stdLevi_subgroupOf_le
  rw [← hPJ]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_stdLevi_subgroupOf]
  have e : (3 * 2 ^ 36 * 93555 : ℕ) = 2097152 * 9196830720 := by norm_num
  rw [e] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hcard).ge

theorem centralizer_rootStar_tMinus :
    Subgroup.centralizer ({rootStar, SemidirectProduct.inl tMinus} : Set GStar) = leviStar := by
  ext γ
  rw [Subgroup.mem_centralizer_iff, mem_leviStar]
  have key : (γ.left : ModGL Tag.E6 K) ∈ stdLevi firstJ ↔
      γ.left ∈ Subgroup.centralizer {rootInv} ⊓ Subgroup.centralizer {tMinus} := by
    rw [centralizer_rootInv_tMinus, Subgroup.mem_subgroupOf]
  rw [key, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have h1 : rootStar * γ = γ * rootStar ↔ γ.left * rootInv = rootInv * γ.left := by
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul, conj_rootStar,
      show rootStar = SemidirectProduct.inl rootInv from rfl,
      SemidirectProduct.inl_injective.eq_iff, mul_inv_eq_iff_eq_mul]
  have h2 : SemidirectProduct.inl tMinus * γ = γ * SemidirectProduct.inl tMinus ↔
      γ.left * tMinus = tMinus * γ.left := by
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul, conj_inl, apply_tMinus,
      SemidirectProduct.inl_injective.eq_iff, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    exact ⟨h1.1 (h _ (Set.mem_insert _ _)), h2.1 (h _ (Set.mem_insert_of_mem _ rfl))⟩
  · rintro ⟨ha, hb⟩ x hx
    rcases hx with rfl | rfl
    · exact h1.2 ha
    · exact h2.2 hb

@[expose] def commonNbrs
    (p q : stdGroup) : Set stdGroup :=
  {x | x ∈ rootClass ∧ x ≠ p ∧ Commute x p ∧ x ≠ q ∧ Commute x q}

theorem not_commute_rootInv_tMinus :
    ¬Commute rootInv tMinus := by
  intro h
  have h2 : (rootInv * tMinus) ^ 2 = 1 := by
    rw [h.mul_pow, pow_two, pow_two, rootInv_mul_self, one_mul]
    exact rootMap_mul_self _
  have := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_rootInv_mul_tMinus] at this
  exact absurd this (by decide)

theorem commonNbrs_eq :
    commonNbrs rootInv tMinus = rootLeviSet := by
  ext x
  constructor
  · rintro ⟨hx, -, h1, -, h2⟩
    refine ⟨hx, ?_⟩
    have hmem : x ∈ Subgroup.centralizer {rootInv} ⊓ Subgroup.centralizer {tMinus} :=
      ⟨Subgroup.mem_centralizer_singleton_iff.2 h1.eq,
        Subgroup.mem_centralizer_singleton_iff.2 h2.eq⟩
    rw [centralizer_rootInv_tMinus, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  · rintro ⟨hx, hL⟩
    obtain ⟨h1, h2⟩ := stdLevi_subgroupOf_le (Subgroup.mem_subgroupOf.2 hL)
    have c1 : Commute x rootInv := Subgroup.mem_centralizer_singleton_iff.1 h1
    have c2 : Commute x tMinus := Subgroup.mem_centralizer_singleton_iff.1 h2
    refine ⟨hx, ?_, c1, ?_, c2⟩
    · rintro rfl
      exact not_commute_rootInv_tMinus c2
    · rintro rfl
      exact not_commute_rootInv_tMinus c1.symm

theorem eq_one_of_forall_commonNbrs
    (γ : leviStar)
    (h : ∀ x ∈ commonNbrs rootInv tMinus,
      (γ : GStar) * SemidirectProduct.inl x * (γ : GStar)⁻¹ = SemidirectProduct.inl x) :
    γ = 1 := by
  have hfix : ∀ p : IsoPt, UnitarySix.extAct (leviStarEquiv γ) p = p := by
    intro p
    have hp := h (rootPt p) (by rw [commonNbrs_eq]; exact rootPt_mem_rootLeviSet p)
    rw [conj_rootPt] at hp
    exact rootPt_injective (SemidirectProduct.inl_injective hp)
  have h1 : UnitarySix.extAct (leviStarEquiv γ) = 1 := Equiv.ext hfix
  rw [← map_one UnitarySix.extAct] at h1
  have h2 := UnitarySix.extAct_injective h1
  rw [← map_one leviStarEquiv] at h2
  exact leviStarEquiv.injective h2

theorem repOrder_eq_three : ∀ i : Fin 5, repOrder i = 3 → i = 4 := by decide

theorem exists_conj_pair
    {p q : stdGroup} (hp : p ∈ rootClass) (hq : q ∈ rootClass)
    (hpq : orderOf (p * q) = 3) : ∃ g : stdGroup, g * rootInv * g⁻¹ = p ∧ g * tMinus * g⁻¹ = q := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hp
  set q' := c⁻¹ * q * c with hq'
  have hq'm : q' ∈ rootClass := hq.trans (isConj_iff.2 ⟨c⁻¹, by rw [hq', inv_inv]⟩)
  have hord : orderOf (rootInv * q') = 3 := by
    have e : rootInv * q' = MulAut.conj c⁻¹ (c * rootInv * c⁻¹ * q) := by
      rw [MulAut.conj_apply, hq']
      group
    rw [e, MulEquiv.orderOf_eq, hpq]
  obtain ⟨h, hh⟩ := (mem_rootClass_iff _).1 hq'm
  obtain ⟨i, hi⟩ := exists_repLevel h
  have hmem : q' ∈ levPoints (repLevel i) := by
    rw [← hh, ← hi]
    exact rootMap_mem_levPoints h
  have hi4 : i = 4 := repOrder_eq_three i
    (by rw [← orderOf_rootInv_mul_of_mem_levPoints hmem]; exact hord)
  rw [hi4, ← conjOrbit_PJ_tMinus] at hmem
  obtain ⟨u, hu, hu'⟩ := hmem
  have hut : u * rootInv * u⁻¹ = rootInv := by
    rw [mem_centralizer_rootInv_iff]
    exact hu
  refine ⟨c * u, ?_, ?_⟩
  · rw [mul_inv_rev, show c * u * rootInv * (u⁻¹ * c⁻¹) = c * (u * rootInv * u⁻¹) * c⁻¹ by group,
      hut]
  · rw [mul_inv_rev, show c * u * tMinus * (u⁻¹ * c⁻¹) = c * (u * tMinus * u⁻¹) * c⁻¹ by group,
      hu', hq']
    group

theorem commonNbrs_conj
    (g p q : stdGroup) :
    commonNbrs (g * p * g⁻¹) (g * q * g⁻¹) = (fun x => g * x * g⁻¹) '' commonNbrs p q := by
  have hcomm : ∀ a b : stdGroup, Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := by
    intro a b
    have e := (MulAut.conj g).injective.eq_iff (a := a * b) (b := b * a)
    simp only [map_mul, MulAut.conj_apply] at e
    exact e
  have hclass : ∀ x : stdGroup, g * x * g⁻¹ ∈ rootClass ↔ x ∈ rootClass := by
    intro x
    constructor
    · intro hx
      exact hx.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
    · intro hx
      exact hx.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hne : ∀ a b : stdGroup, g * a * g⁻¹ ≠ g * b * g⁻¹ ↔ a ≠ b := by
    intro a b
    exact not_congr (by constructor <;> intro h <;> simp_all)
  ext y
  constructor
  · rintro ⟨hy, h1, h2, h3, h4⟩
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e] at hy h1 h2 h3 h4
    exact ⟨(hclass _).1 hy, (hne _ _).1 h1, (hcomm _ _).1 h2, (hne _ _).1 h3, (hcomm _ _).1 h4⟩
  · rintro ⟨x, ⟨hx, h1, h2, h3, h4⟩, rfl⟩
    exact ⟨(hclass _).2 hx, (hne _ _).2 h1, (hcomm _ _).2 h2, (hne _ _).2 h3, (hcomm _ _).2 h4⟩

theorem centralizer_conj_pair
    (g : GStar) (a b : GStar) :
    Subgroup.centralizer ({g * a * g⁻¹, g * b * g⁻¹} : Set GStar) =
      (Subgroup.centralizer ({a, b} : Set GStar)).map (MulAut.conj g).toMonoidHom := by
  ext γ
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have key : ∀ x : GStar, (g * x * g⁻¹) * γ = γ * (g * x * g⁻¹) ↔
      x * ((MulAut.conj g).symm γ) = ((MulAut.conj g).symm γ) * x := by
    intro x
    rw [MulAut.conj_symm_apply]
    constructor
    · intro h
      calc x * (g⁻¹ * γ * g) = g⁻¹ * ((g * x * g⁻¹) * γ) * g := by group
        _ = g⁻¹ * (γ * (g * x * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * γ * g * x := by group
    · intro h
      calc (g * x * g⁻¹) * γ = g * (x * (g⁻¹ * γ * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * γ * g) * x) * g⁻¹ := by rw [h]
        _ = γ * (g * x * g⁻¹) := by group
  constructor
  · intro h x hx
    rcases hx with rfl | rfl
    · exact (key _).1 (h _ (Set.mem_insert _ _))
    · exact (key _).1 (h _ (Set.mem_insert_of_mem _ rfl))
  · intro h y hy
    rcases hy with rfl | rfl
    · exact (key a).2 (h _ (Set.mem_insert _ _))
    · exact (key b).2 (h _ (Set.mem_insert_of_mem _ rfl))

theorem inl_mem_leviStar_iff
    (g : stdGroup) :
    SemidirectProduct.inl g ∈ leviStar ↔ (g : ModGL Tag.E6 K) ∈ stdLevi firstJ :=
  Iff.rfl

theorem conj_mem_commonNbrs
    (γ : leviStar) {x : stdGroup} (hx : x ∈ commonNbrs rootInv tMinus) :
    ∃ y ∈ commonNbrs rootInv tMinus,
      (γ : GStar) * SemidirectProduct.inl x * (γ : GStar)⁻¹ = SemidirectProduct.inl y := by
  rw [commonNbrs_eq, rootLeviSet_eq_range] at hx ⊢
  obtain ⟨p, rfl⟩ := hx
  exact ⟨_, ⟨_, rfl⟩, conj_rootPt γ p⟩

theorem standard_F4_opposite_root_common_neighbor_geometry :
    (tMinus : ModGL Tag.E6 K) = pinnedX Tag.E6 K (-theta) 1 ∧ tMinus ∈ rootClass ∧
    orderOf (rootInv * tMinus) = 3 ∧
    Subgroup.centralizer ({rootStar, SemidirectProduct.inl tMinus} : Set GStar) = leviStar ∧
    (∀ g : stdGroup,
      SemidirectProduct.inl g ∈ leviStar ↔ (g : ModGL Tag.E6 K) ∈ stdLevi firstJ) ∧
    commonNbrs rootInv tMinus = rootLeviSet ∧
    commonNbrs rootInv tMinus = Set.range rootPt ∧ Function.Injective rootPt ∧
    Fintype.card IsoPt = 693 ∧ isoGraph.IsSRGWith 693 180 51 45 ∧
    (∀ p q : IsoPt, isoGraph.Adj p q ↔ p ≠ q ∧ Commute (rootPt p) (rootPt q)) ∧
    (∀ (γ : leviStar) (x : stdGroup), x ∈ commonNbrs rootInv tMinus →
      ∃ y ∈ commonNbrs rootInv tMinus,
        (γ : GStar) * SemidirectProduct.inl x * (γ : GStar)⁻¹ = SemidirectProduct.inl y) ∧
    (∀ (γ : leviStar) (p : IsoPt),
      (γ : GStar) * SemidirectProduct.inl (rootPt p) * (γ : GStar)⁻¹ =
        SemidirectProduct.inl (rootPt (UnitarySix.extAct (leviStarEquiv γ) p))) ∧
    Function.Injective UnitarySix.extAct ∧
    (∀ γ : leviStar, (∀ x ∈ commonNbrs rootInv tMinus,
      (γ : GStar) * SemidirectProduct.inl x * (γ : GStar)⁻¹ = SemidirectProduct.inl x) →
        γ = 1) ∧
    ∀ p q : stdGroup, p ∈ rootClass → q ∈ rootClass → orderOf (p * q) = 3 →
      ∃ g : stdGroup, g * rootInv * g⁻¹ = p ∧ g * tMinus * g⁻¹ = q ∧
        Subgroup.centralizer
            ({SemidirectProduct.inl p, SemidirectProduct.inl q} : Set GStar) =
          leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom ∧
        commonNbrs p q = (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus := by
  refine ⟨coe_tMinus, tMinus_mem_rootClass, orderOf_rootInv_mul_tMinus,
    centralizer_rootStar_tMinus, inl_mem_leviStar_iff, commonNbrs_eq,
    commonNbrs_eq.trans rootLeviSet_eq_range, rootPt_injective, UnitarySix.card_isoPt,
    UnitarySix.isSRGWith, adj_iff_commute_rootPt, fun γ _ hx => conj_mem_commonNbrs γ hx,
    conj_rootPt, UnitarySix.extAct_injective, eq_one_of_forall_commonNbrs,
    fun p q hp hq hpq => ?_⟩
  obtain ⟨g, hgt, hgq⟩ := exists_conj_pair hp hq hpq
  refine ⟨g, hgt, hgq, ?_, ?_⟩
  · have e1 : (SemidirectProduct.inl p : GStar) =
        SemidirectProduct.inl g * rootStar * (SemidirectProduct.inl g)⁻¹ := by
      rw [← hgt, map_mul, map_mul, map_inv]
      rfl
    have e2 : (SemidirectProduct.inl q : GStar) =
        SemidirectProduct.inl g * SemidirectProduct.inl tMinus * (SemidirectProduct.inl g)⁻¹ := by
      rw [← hgq, map_mul, map_mul, map_inv]
    rw [e1, e2, centralizer_conj_pair, centralizer_rootStar_tMinus]
  · rw [← hgt, ← hgq, commonNbrs_conj]

end CFSG.Monster.B.E6.StdF4
