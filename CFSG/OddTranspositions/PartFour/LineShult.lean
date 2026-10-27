module

public import CFSG.OddTranspositions.PartFour.LineStabilizer

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity MulAction

theorem four_le_natCard_of_mem {P : Type*} [Group P] [Finite P] {A : Subgroup P} {a b : P}
    (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a * b ≠ 1)
    (hb2 : b * b = 1) : 4 ≤ Nat.card A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let e0 : A := 1
  let e1 : A := ⟨a, ha⟩
  let e2 : A := ⟨b, hb⟩
  let e3 : A := ⟨a * b, A.mul_mem ha hb⟩
  have h01 : e0 ≠ e1 := fun h => ha1 (congrArg Subtype.val h).symm
  have h02 : e0 ≠ e2 := fun h => hb1 (congrArg Subtype.val h).symm
  have h03 : e0 ≠ e3 := fun h => hab1 (congrArg Subtype.val h).symm
  have h12 : e1 ≠ e2 := by
    intro h
    exact hab1 (by rw [show a = b from congrArg Subtype.val h, hb2])
  have h13 : e1 ≠ e3 := by
    intro h
    have h' : (1 : P) = b := by
      simpa [e1, e3] using congrArg (fun x : P => a⁻¹ * x) (congrArg Subtype.val h)
    exact hb1 h'.symm
  have h23 : e2 ≠ e3 := by
    intro h
    have h' : (1 : P) = a := by
      simpa [e2, e3, mul_assoc] using
        congrArg (fun x : P => x * b⁻¹) (congrArg Subtype.val h)
    exact ha1 h'.symm
  have hcard : ({e0, e1, e2, e3} : Finset A).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨e0, e1, e2, e3, h01, h02, h03, h12, h13, h23, rfl⟩
  have hle : 4 ≤ Fintype.card A := by
    have := Finset.card_le_card (Finset.subset_univ ({e0, e1, e2, e3} : Finset A))
    rwa [hcard] at this
  simpa [Nat.card_eq_fintype_card] using hle

theorem smul_rangeRestrict {X Ω : Type*} [Group X] [MulAction X Ω] (x : X) (ω : Ω) :
    (MulAction.toPermHom X Ω).rangeRestrict x • ω = x • ω := by
  rw [Subgroup.smul_def, Equiv.Perm.smul_def]
  exact MulAction.toPerm_apply x ω

theorem sq_rangeRestrict_eq_one {X Ω : Type*} [Group X] [MulAction X Ω] {A : Subgroup X}
    (hA2 : ∀ a ∈ A, ∀ ω : Ω, (a * a) • ω = ω) {a : X} (ha : a ∈ A) :
    (MulAction.toPermHom X Ω).rangeRestrict a * (MulAction.toPermHom X Ω).rangeRestrict a = 1 := by
  rw [← map_mul]
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro ω
  change ((MulAction.toPermHom X Ω).rangeRestrict (a * a) :
      (MulAction.toPermHom X Ω).range) • ω = (1 : (MulAction.toPermHom X Ω).range) • ω
  rw [smul_rangeRestrict, one_smul]
  exact hA2 a ha ω

theorem map_rangeRestrict_le_stabilizer {X Ω : Type*} [Group X] [MulAction X Ω] {α : Ω}
    {A : Subgroup X} (hAα : A ≤ MulAction.stabilizer X α) :
    A.map (MulAction.toPermHom X Ω).rangeRestrict ≤
      MulAction.stabilizer (MulAction.toPermHom X Ω).range α := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  rw [MulAction.mem_stabilizer_iff, smul_rangeRestrict]
  exact MulAction.mem_stabilizer_iff.mp (hAα ha)

theorem stabilizer_le_normalizer_map_rangeRestrict {X Ω : Type*} [Group X] [MulAction X Ω]
    {α : Ω} {A : Subgroup X}
    (hAN : MulAction.stabilizer X α ≤ Subgroup.normalizer (A : Set X)) :
    MulAction.stabilizer (MulAction.toPermHom X Ω).range α ≤
      Subgroup.normalizer (A.map (MulAction.toPermHom X Ω).rangeRestrict : Set _) := by
  rw [Subgroup.le_normalizer_iff]
  intro s hs a' ha'
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp s.2
  have hsx : (MulAction.toPermHom X Ω).rangeRestrict x = s := Subtype.ext hx
  have hxα : x ∈ MulAction.stabilizer X α := by
    rw [MulAction.mem_stabilizer_iff, ← smul_rangeRestrict x α, hsx]
    exact MulAction.mem_stabilizer_iff.mp hs
  have hxA : x * a * x⁻¹ ∈ A := (Subgroup.le_normalizer_iff.mp hAN) x hxα a ha
  refine Subgroup.mem_map.mpr ⟨x * a * x⁻¹, hxA, ?_⟩
  rw [map_mul, map_mul, map_inv, hsx]

theorem eq_one_of_map_rangeRestrict_semiregular {X Ω : Type*} [Group X] [MulAction X Ω]
    {α : Ω} {A : Subgroup X}
    (hsemi : ∀ a ∈ A, ∀ β : Ω, a • β = β → β ≠ α → ∀ ω : Ω, a • ω = ω) :
    ∀ a' ∈ A.map (MulAction.toPermHom X Ω).rangeRestrict, ∀ β : Ω, a' • β = β → β ≠ α →
      a' = 1 := by
  intro a' ha' β hβ hβne
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  have hβ' : a • β = β := by rw [← smul_rangeRestrict a β]; exact hβ
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro ω
  rw [← Equiv.Perm.smul_def, ← Subgroup.smul_def, smul_rangeRestrict]
  exact hsemi a ha β hβ' hβne ω

section Uncertified

variable {G : Type} [Group G] [Finite G] {D : Set G}

open scoped Pointwise

theorem conjAct_smul_set (g : G) (S : Set G) :
    ConjAct.toConjAct g • S = cimg g S := by
  rw [← Set.image_smul]
  simp only [ConjAct.toConjAct_smul]

theorem conjAct_smul_setSet (g : G) (L : Set (Set G)) :
    ConjAct.toConjAct g • L = (cimg g) '' L := by
  rw [← Set.image_smul]
  exact Set.image_congr fun S _ => conjAct_smul_set g S

theorem smul_stabilizer_coe {L : Set (Set G)} {x : G}
    (hx : ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct G) L) (S : ↥L) :
    (((⟨ConjAct.toConjAct x, hx⟩ : MulAction.stabilizer (ConjAct G) L) • S : ↥L) : Set G) =
      cimg x (S : Set G) := by
  rw [SMul.smul_stabilizer_def, conjAct_smul_set]

theorem mem_map_toConjAct_subgroupOf {N : Subgroup G} {X : Subgroup (ConjAct G)} {a : X} :
    a ∈ (N.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom).subgroupOf X ↔
      ∃ x ∈ N, ConjAct.toConjAct x = (a : ConjAct G) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  rfl

theorem cimg_image_blockLine_subset (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {x : G} (hx : x ∈ Malpha D hC.alpha) :
    (cimg x) '' blockLine D hC.alpha β ⊆ blockLine D hC.alpha β := by
  rintro S ⟨T, hT, rfl⟩
  exact cimg_mem_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ hT hx

theorem mem_stabilizer_blockLine_of_mem_Malpha (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {x : G} (hx : x ∈ Malpha D hC.alpha) :
    ConjAct.toConjAct x ∈
      MulAction.stabilizer (ConjAct G) (blockLine D hC.alpha β) := by
  rw [MulAction.mem_stabilizer_set_iff_smul_set_subset (Set.toFinite _), conjAct_smul_setSet]
  exact cimg_image_blockLine_subset h113 hC hrad hn3 hβ hx

theorem isPretransitive_stabilizer_blockLine (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    IsPretransitive (MulAction.stabilizer (ConjAct G) (blockLine D hC.alpha β))
      ↥(blockLine D hC.alpha β) := by
  rw [MulAction.isPretransitive_iff]
  intro δ ε
  obtain ⟨g, hg1, hg2⟩ :=
    exists_cimg_eq_of_mem_blockLine h89 h113 hC hrad hW hn3 hMZ hβ δ.2 ε.2
  refine ⟨⟨ConjAct.toConjAct g, ?_⟩, ?_⟩
  · rw [MulAction.mem_stabilizer_set_iff_smul_set_subset (Set.toFinite _), conjAct_smul_setSet,
      hg2]
  · apply Subtype.ext
    rw [SMul.smul_stabilizer_def, conjAct_smul_set, hg1]

abbrev blockLineStabilizer (hC : HypothesisC D) (β : Set G) : Subgroup (ConjAct G) :=
  MulAction.stabilizer (ConjAct G) (blockLine D hC.alpha β)

abbrev blockLineBase (hC : HypothesisC D) (β : Set G) :
    ↥(blockLine D hC.alpha β) :=
  ⟨hC.alpha, left_mem_blockLine hC.isBlock_alpha.subset⟩

abbrev mapToConjActStabilizer (hC : HypothesisC D) (N : Subgroup G) (β : Set G) :
    Subgroup (blockLineStabilizer hC β) :=
  (N.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom).subgroupOf
    (blockLineStabilizer hC β)

theorem map_toConjAct_subgroupOf_le_stabilizer_alpha (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {N : Subgroup G} (hNM : N ≤ Malpha D hC.alpha) :
    mapToConjActStabilizer hC N β ≤
      MulAction.stabilizer (blockLineStabilizer hC β) (blockLineBase hC β) := by
  intro a ha
  obtain ⟨z, hzN, hza⟩ := mem_map_toConjAct_subgroupOf.mp ha
  have hmemX : ConjAct.toConjAct z ∈ blockLineStabilizer hC β :=
    mem_stabilizer_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ (hNM hzN)
  have haeq : (a : blockLineStabilizer hC β) = ⟨ConjAct.toConjAct z, hmemX⟩ :=
    Subtype.ext hza.symm
  rw [MulAction.mem_stabilizer_iff, haeq]
  apply Subtype.ext
  rw [smul_stabilizer_coe hmemX]
  exact cimg_eq_self_of_mem_normalizer (Halpha_le_normalizer_block D hC.alpha
    (Subgroup.map_subtype_le (CFSG.solvableRadical (Halpha D hC.alpha)) (hNM hzN)))

theorem stabilizer_le_normalizer_map_toConjAct_subgroupOf (hC : HypothesisC D) {β : Set G}
    {N : Subgroup G}
    (hNN : ∀ g ∈ Subgroup.normalizer hC.alpha, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    MulAction.stabilizer (blockLineStabilizer hC β) (blockLineBase hC β) ≤
      Subgroup.normalizer (mapToConjActStabilizer hC N β : Set _) := by
  rw [Subgroup.le_normalizer_iff]
  intro s hs a ha
  obtain ⟨z, hzN, hza⟩ := mem_map_toConjAct_subgroupOf.mp ha
  have hsα : (s : ConjAct G) • hC.alpha = hC.alpha := by
    have h := MulAction.mem_stabilizer_iff.mp hs
    have h' := congrArg Subtype.val h
    rwa [SMul.smul_stabilizer_def] at h'
  set g : G := ConjAct.ofConjAct (s : ConjAct G) with hg
  have hsg : (s : ConjAct G) = ConjAct.toConjAct g := by
    rw [hg, ConjAct.toConjAct_ofConjAct]
  have hgα : g ∈ Subgroup.normalizer hC.alpha := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have h := hsα
    rw [hsg, conjAct_smul_set] at h
    rwa [show (⇑(MulAut.conj g) : G → G) = (fun y => g * y * g⁻¹) by
      funext y; rw [MulAut.conj_apply]]
  have hyN : g * z * g⁻¹ ∈ N := hNN g hgα z hzN
  refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨g * z * g⁻¹, hyN, ?_⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hsg, ← hza]
  change ConjAct.toConjAct (g * z * g⁻¹) =
    ConjAct.toConjAct g * ConjAct.toConjAct z * (ConjAct.toConjAct g)⁻¹
  rw [ConjAct.toConjAct_mul, ConjAct.toConjAct_mul, ConjAct.toConjAct_inv]

theorem map_toConjAct_subgroupOf_sq_smul (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {N : Subgroup G} (hNM : N ≤ Malpha D hC.alpha)
    (hexp : ∀ x ∈ N, ∀ ε ∈ blockLine D hC.alpha β, cimg (x * x) ε = ε) :
    ∀ a ∈ mapToConjActStabilizer hC N β, ∀ ω : ↥(blockLine D hC.alpha β),
      (a * a) • ω = ω := by
  intro a ha ω
  obtain ⟨z, hzN, hza⟩ := mem_map_toConjAct_subgroupOf.mp ha
  have hmemX : ConjAct.toConjAct z ∈ blockLineStabilizer hC β :=
    mem_stabilizer_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ (hNM hzN)
  have haeq : (a : blockLineStabilizer hC β) = ⟨ConjAct.toConjAct z, hmemX⟩ :=
    Subtype.ext hza.symm
  rw [haeq]
  apply Subtype.ext
  rw [mul_smul, smul_stabilizer_coe hmemX, smul_stabilizer_coe hmemX, ← cimg_mul]
  exact hexp z hzN (ω : Set G) ω.2

theorem map_toConjAct_subgroupOf_semiregular (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {N : Subgroup G} (hNM : N ≤ Malpha D hC.alpha)
    (hsemi : ∀ x ∈ N, ∀ δ ∈ blockLine D hC.alpha β, δ ≠ hC.alpha → cimg x δ = δ →
      ∀ ε ∈ blockLine D hC.alpha β, cimg x ε = ε) :
    ∀ a ∈ mapToConjActStabilizer hC N β, ∀ γ : ↥(blockLine D hC.alpha β),
      a • γ = γ → γ ≠ blockLineBase hC β →
        ∀ ω : ↥(blockLine D hC.alpha β), a • ω = ω := by
  intro a ha γ hγ hγne ω
  obtain ⟨z, hzN, hza⟩ := mem_map_toConjAct_subgroupOf.mp ha
  have hmemX : ConjAct.toConjAct z ∈ blockLineStabilizer hC β :=
    mem_stabilizer_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ (hNM hzN)
  have haeq : (a : blockLineStabilizer hC β) = ⟨ConjAct.toConjAct z, hmemX⟩ :=
    Subtype.ext hza.symm
  rw [haeq] at hγ ⊢
  have hfix : cimg z (γ : Set G) = (γ : Set G) := by
    have h := congrArg Subtype.val hγ
    rwa [smul_stabilizer_coe hmemX] at h
  have hne : (γ : Set G) ≠ hC.alpha := fun h => hγne (Subtype.ext h)
  apply Subtype.ext
  rw [smul_stabilizer_coe hmemX]
  exact hsemi z hzN (γ : Set G) γ.2 hne hfix (ω : Set G) ω.2

end Uncertified

end CFSG.OddTranspositions.PartFour
