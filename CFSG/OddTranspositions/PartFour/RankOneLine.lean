module

public import CFSG.OddTranspositions.PartFour.LineCount
public import CFSG.OddTranspositions.PartFour.LineShult
public import CFSG.OddTranspositions.PartFour.RankOneShult

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity MulAction

section Uncertified

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem map_pCore_two_le_Malpha (α : Set G) :
    (CFSG.pCore 2 (Halpha D α)).map (Halpha D α).subtype ≤ Malpha D α :=
  Subgroup.map_mono (CFSG.pCore_le_solvableRadical 2 _)

theorem conj_mem_map_pCore_two_of_mem_normalizer (hN : IsNormalSet D) {α : Set G} {g x : G}
    (hg : g ∈ Subgroup.normalizer α)
    (hx : x ∈ (CFSG.pCore 2 (Halpha D α)).map (Halpha D α).subtype) :
    g * x * g⁻¹ ∈ (CFSG.pCore 2 (Halpha D α)).map (Halpha D α).subtype := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hgH : g ∈ Subgroup.normalizer (Halpha D α : Set G) :=
    normalizer_le_normalizer_Halpha hN hg
  let φ : Halpha D α ≃* Halpha D α := (Halpha D α).normalizerMonoidHom ⟨g, hgH⟩
  have hfix : (CFSG.pCore 2 (Halpha D α)).map φ.toMonoidHom = CFSG.pCore 2 (Halpha D α) :=
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore 2 (Halpha D α)).Characteristic) φ
  refine Subgroup.mem_map.mpr ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · exact (Halpha D α).normalizerMonoidHom_apply_apply_coe ⟨g, hgH⟩ y

theorem isPGroup_mapToConjActStabilizer_pCore (hC : HypothesisC D) (β : Set G) :
    IsPGroup 2 (mapToConjActStabilizer hC
      ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) β) := by
  intro a
  obtain ⟨z, hz, hza⟩ := mem_map_toConjAct_subgroupOf.mp a.2
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha) ⟨y, hy⟩
  refine ⟨n, ?_⟩
  have h1 : ((a : blockLineStabilizer hC β) : ConjAct G) = ConjAct.toConjAct (y : G) := hza.symm
  have hord : orderOf a = orderOf (⟨y, hy⟩ : CFSG.pCore 2 (Halpha D hC.alpha)) := by
    calc orderOf a = orderOf (a : blockLineStabilizer hC β) := (Subgroup.orderOf_coe a).symm
      _ = orderOf ((a : blockLineStabilizer hC β) : ConjAct G) :=
        (Subgroup.orderOf_coe (a : blockLineStabilizer hC β)).symm
      _ = orderOf (ConjAct.toConjAct (y : G)) := by rw [h1]
      _ = orderOf (y : G) :=
        orderOf_injective (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
          (ConjAct.toConjAct : G ≃* ConjAct G).injective (y : G)
      _ = orderOf y := Subgroup.orderOf_coe y
      _ = orderOf (⟨y, hy⟩ : CFSG.pCore 2 (Halpha D hC.alpha)) :=
        Subgroup.orderOf_coe ⟨y, hy⟩
  rw [← orderOf_dvd_iff_pow_eq_one, hord]
  exact orderOf_dvd_of_pow_eq_one hn

section Pointwise

open scoped Pointwise

private theorem rankOneLine_smul_eq_base_and_right (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {a b : ↥(blockLine D hC.alpha β)} (hab : a ≠ b) :
    ∃ g : blockLineStabilizer hC β, g • a = blockLineBase hC β ∧
      g • b = (⟨β, right_mem_blockLine hβ.1 hβ.2.1⟩ : ↥(blockLine D hC.alpha β)) := by
  classical
  let ℓ : Set (Set G) := blockLine D hC.alpha β
  let pt : ↥ℓ := ⟨β, right_mem_blockLine hβ.1 hβ.2.1⟩
  haveI : Finite ↥ℓ := Set.Finite.to_subtype (Set.toFinite ℓ)
  have hpre : IsPretransitive (blockLineStabilizer hC β) ↥ℓ :=
    isPretransitive_stabilizer_blockLine h89 h113 hC hrad hW hn3 hMZ hβ
  obtain ⟨g₁, hg₁⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := blockLineStabilizer hC β) a (blockLineBase hC β)
  let b' : ↥ℓ := g₁ • b
  have hb'ne : b' ≠ blockLineBase hC β := by
    intro h
    have h1 : g₁ • b = g₁ • a := h.trans hg₁.symm
    exact hab (by simpa using (congrArg (fun x => g₁⁻¹ • x) h1).symm)
  have hb'α : (b' : Set G) ≠ hC.alpha := fun h => hb'ne (Subtype.ext h)
  obtain ⟨g₂, hg₂N, hg₂β, hg₂ℓ⟩ := exists_mem_normalizer_cimg_eq hC hβ b'.2 hb'α
  have hmem : ConjAct.toConjAct g₂ ∈ blockLineStabilizer hC β := by
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset (Set.toFinite _), conjAct_smul_setSet]
    show (cimg g₂) '' blockLine D hC.alpha β ⊆ blockLine D hC.alpha β
    rw [hg₂ℓ]
  let h₂ : blockLineStabilizer hC β := ⟨ConjAct.toConjAct g₂, hmem⟩
  have h2base : h₂ • blockLineBase hC β = blockLineBase hC β := by
    apply Subtype.ext
    rw [smul_stabilizer_coe hmem]
    exact cimg_eq_self_of_mem_normalizer hg₂N
  have h2pt : h₂ • pt = b' := by
    apply Subtype.ext
    rw [smul_stabilizer_coe hmem]
    exact hg₂β
  have h2inv_base : h₂⁻¹ • blockLineBase hC β = blockLineBase hC β := by
    simpa using (congrArg (fun x => h₂⁻¹ • x) h2base).symm
  have h2inv_pt : h₂⁻¹ • b' = pt := by
    simpa using (congrArg (fun x => h₂⁻¹ • x) h2pt).symm
  refine ⟨h₂⁻¹ * g₁, ?_, ?_⟩
  · rw [mul_smul, hg₁]
    exact h2inv_base
  · rw [mul_smul]
    exact h2inv_pt

end Pointwise

theorem exists_smul_eq_and_smul_eq_blockLine (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∀ a b c d : ↥(blockLine D hC.alpha β), a ≠ b → c ≠ d →
      ∃ g : blockLineStabilizer hC β, g • a = c ∧ g • b = d := by
  intro a b c d hab hcd
  obtain ⟨g₁, hg₁a, hg₁b⟩ :=
    rankOneLine_smul_eq_base_and_right h89 h113 hC hrad hW hn3 hMZ hβ hab
  obtain ⟨g₂, hg₂c, hg₂d⟩ :=
    rankOneLine_smul_eq_base_and_right h89 h113 hC hrad hW hn3 hMZ hβ hcd
  have hg₂c' : g₂⁻¹ • blockLineBase hC β = c := by
    simpa using (congrArg (fun x => g₂⁻¹ • x) hg₂c).symm
  have hg₂d' : g₂⁻¹ • (⟨β, right_mem_blockLine hβ.1 hβ.2.1⟩ :
      ↥(blockLine D hC.alpha β)) = d := by
    simpa using (congrArg (fun x => g₂⁻¹ • x) hg₂d).symm
  refine ⟨g₂⁻¹ * g₁, ?_, ?_⟩
  · rw [mul_smul, hg₁a]
    exact hg₂c'
  · rw [mul_smul, hg₁b]
    exact hg₂d'

private theorem rankOneLine_image_pCore_eq_image_Malpha (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {γ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) :
    (fun y => cimg y γ) ''
        (((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) : Set G) =
      (fun x => cimg x γ) '' (Malpha D hC.alpha : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, map_pCore_two_le_Malpha _ hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := exists_mem_pCore_cimg_eq h113 hC hrad hn3 hHns hγ hx
    exact ⟨(y : G), Subgroup.mem_map_of_mem _ hy, hye⟩

private theorem rankOneLine_image_orbit_pCore (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) (δ : ↥(blockLine D hC.alpha β)) :
    Subtype.val '' (orbit (mapToConjActStabilizer hC
        ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) β) δ :
        Set ↥(blockLine D hC.alpha β)) =
      (fun y => cimg y (δ : Set G)) ''
        (((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) : Set G) := by
  classical
  let ℓ : Set (Set G) := blockLine D hC.alpha β
  let Q : Subgroup G := (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  let P : Subgroup (blockLineStabilizer hC β) := mapToConjActStabilizer hC Q β
  have hzX : ∀ z ∈ Q, ConjAct.toConjAct z ∈ blockLineStabilizer hC β := fun z hz =>
    mem_stabilizer_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ
      (map_pCore_two_le_Malpha _ (by simpa [Q] using hz))
  ext S
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp hT
    obtain ⟨z, hzQ, hza⟩ := mem_map_toConjAct_subgroupOf.mp p.2
    refine ⟨z, hzQ, ?_⟩
    have haeq : (p : blockLineStabilizer hC β) = ⟨ConjAct.toConjAct z, hzX z hzQ⟩ :=
      Subtype.ext hza.symm
    calc cimg z (δ : Set G) = (((p : blockLineStabilizer hC β) • δ : ↥ℓ) : Set G) := by
          rw [haeq]
          exact (smul_stabilizer_coe (hzX z hzQ) δ).symm
      _ = ((p • δ : ↥ℓ) : Set G) := by rw [Subgroup.smul_def]
      _ = (T : Set G) := by rw [hp]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(⟨⟨ConjAct.toConjAct y, hzX y hy⟩,
      mem_map_toConjAct_subgroupOf.mpr ⟨y, hy, rfl⟩⟩ : P) • δ, ?_, ?_⟩
    · exact MulAction.mem_orbit_iff.mpr
        ⟨⟨_, mem_map_toConjAct_subgroupOf.mpr ⟨y, hy, rfl⟩⟩, rfl⟩
    · simpa using smul_stabilizer_coe (hzX y hy) δ

theorem ncard_orbit_map_pCore (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) (δ : ↥(blockLine D hC.alpha β))
    (hδ : δ ≠ blockLineBase hC β) :
    (orbit (mapToConjActStabilizer hC
      ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) β) δ).ncard =
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  classical
  let ℓ : Set (Set G) := blockLine D hC.alpha β
  let Q : Subgroup G := (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  let P : Subgroup (blockLineStabilizer hC β) := mapToConjActStabilizer hC Q β
  have hδne : (δ : Set G) ≠ hC.alpha := fun h => hδ (Subtype.ext h)
  have hδD : (δ : Set G) ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ δ.2 hδne
  have horbit : Subtype.val '' (orbit P δ : Set ↥ℓ) =
      (fun y => cimg y (δ : Set G)) '' (Q : Set G) :=
    rankOneLine_image_orbit_pCore h113 hC hrad hn3 hβ δ
  have hQM : (fun y => cimg y (δ : Set G)) '' (Q : Set G) =
      (fun x => cimg x (δ : Set G)) '' (Malpha D hC.alpha : Set G) :=
    rankOneLine_image_pCore_eq_image_Malpha h113 hC hrad hn3 hHns hδD
  calc (orbit P δ).ncard = (Subtype.val '' (orbit P δ : Set ↥ℓ)).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = ((fun y => cimg y (δ : Set G)) '' (Q : Set G)).ncard := by rw [horbit]
    _ = ((fun x => cimg x (δ : Set G)) '' (Malpha D hC.alpha : Set G)).ncard := by rw [hQM]
    _ = ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard :=
        ncard_orbit_Malpha_eq hC hβ hδD

theorem le_ncard_orbit_mapToConjActStabilizer (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {N : Subgroup G} (hNM : N ≤ Malpha D hC.alpha)
    (hcover : (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) ⊆
      (fun x => cimg x β) '' (N : Set G))
    {δ : ↥(blockLine D hC.alpha β)} (hδ : (δ : Set G) = β) :
    ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard ≤
      (orbit (mapToConjActStabilizer hC N β) δ).ncard := by
  classical
  let ℓ : Set (Set G) := blockLine D hC.alpha β
  let P : Subgroup (blockLineStabilizer hC β) := mapToConjActStabilizer hC N β
  have hzX : ∀ z ∈ N, ConjAct.toConjAct z ∈ blockLineStabilizer hC β := fun z hz =>
    mem_stabilizer_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ (hNM hz)
  have horbit : Subtype.val '' (orbit P δ : Set ↥ℓ) = (fun x => cimg x β) '' (N : Set G) := by
    ext S
    constructor
    · rintro ⟨T, hT, rfl⟩
      obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp hT
      obtain ⟨z, hzN, hza⟩ := mem_map_toConjAct_subgroupOf.mp p.2
      refine ⟨z, hzN, ?_⟩
      have haeq : (p : blockLineStabilizer hC β) = ⟨ConjAct.toConjAct z, hzX z hzN⟩ :=
        Subtype.ext hza.symm
      calc cimg z β = cimg z (δ : Set G) := by rw [hδ]
        _ = (((p : blockLineStabilizer hC β) • δ : ↥ℓ) : Set G) := by
            rw [haeq]
            exact (smul_stabilizer_coe (hzX z hzN) δ).symm
        _ = ((p • δ : ↥ℓ) : Set G) := by rw [Subgroup.smul_def]
        _ = (T : Set G) := by rw [hp]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(⟨⟨ConjAct.toConjAct y, hzX y hy⟩,
        mem_map_toConjAct_subgroupOf.mpr ⟨y, hy, rfl⟩⟩ : P) • δ, ?_, ?_⟩
      · exact MulAction.mem_orbit_iff.mpr
          ⟨⟨_, mem_map_toConjAct_subgroupOf.mpr ⟨y, hy, rfl⟩⟩, rfl⟩
      · simpa [hδ] using smul_stabilizer_coe (hzX y hy) δ
  calc ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard
      ≤ ((fun x => cimg x β) '' (N : Set G)).ncard := Set.ncard_le_ncard hcover
    _ = (Subtype.val '' (orbit P δ : Set ↥ℓ)).ncard := by rw [horbit]
    _ = (orbit P δ).ncard := Set.ncard_image_of_injective _ Subtype.val_injective

theorem ncard_blockLine_lt_sq_add_one (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    (hVlt : (Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)).ncard <
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard) :
    (blockLine D hC.alpha β).ncard <
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard ^ 2 + 1 := by
  classical
  let m : ℕ := ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard
  let Δ : Set (Set G) := blockLine D hC.alpha β \ {hC.alpha}
  let r : ℕ := (blockImage hC '' Δ).ncard
  have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hβpos : 0 < β.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨b, hb⟩
  have hVeq := ncard_Vmem_eq h89 h113 hC hrad hW hn3 hMZ hHns hβ hb
  have hrm : r * β.ncard < m := by
    rw [← hVeq]
    exact hVlt
  have h1 : r ≤ r * β.ncard := by
    have hβ1 : 1 ≤ β.ncard := by omega
    calc r = r * 1 := (Nat.mul_one r).symm
      _ ≤ r * β.ncard := Nat.mul_le_mul_left r hβ1
  have hrlt : r < m := by omega
  have hmpos : 0 < m := by omega
  have hΔ := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
  have hℓ : (blockLine D hC.alpha β).ncard = Δ.ncard + 1 :=
    (Set.ncard_diff_singleton_add_one hαℓ (Set.toFinite _)).symm
  have hmul : r * m < m * m := Nat.mul_lt_mul_of_pos_right hrlt hmpos
  calc (blockLine D hC.alpha β).ncard = Δ.ncard + 1 := hℓ
    _ = r * m + 1 := by rw [hΔ]
    _ < m * m + 1 := by omega
    _ = m ^ 2 + 1 := by ring

end Uncertified

section Certified


variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_ncard_blockLine_eq_two_pow_add_one_of_lt
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) (N : Subgroup G) (hNM : N ≤ Malpha D hC.alpha)
    (hexp : ∀ x ∈ N, ∀ ε ∈ blockLine D hC.alpha β, cimg (x * x) ε = ε)
    (hsemi : ∀ x ∈ N, ∀ δ ∈ blockLine D hC.alpha β, δ ≠ hC.alpha → cimg x δ = δ →
      ∀ ε ∈ blockLine D hC.alpha β, cimg x ε = ε)
    (hcover : (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) ⊆
      (fun x => cimg x β) '' (N : Set G))
    (hm4 : 4 ≤ ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard)
    {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    (hVlt : (Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)).ncard <
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard) :
    ∃ e : ℕ, (blockLine D hC.alpha β).ncard = 2 ^ e + 1 := by
  classical
  let ℓ : Set (Set G) := blockLine D hC.alpha β
  let X : Subgroup (ConjAct G) := blockLineStabilizer hC β
  let Q : Subgroup G := (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  let P : Subgroup X := mapToConjActStabilizer hC Q β
  let F : Subgroup X := mapToConjActStabilizer hC N β
  let m : ℕ := ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard
  let pt : ↥ℓ := ⟨β, right_mem_blockLine hβ.1 hβ.2.1⟩
  haveI : Finite ↥ℓ := Set.Finite.to_subtype (Set.toFinite ℓ)
  have h2 : ∀ a b c d : ↥ℓ, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d :=
    exists_smul_eq_and_smul_eq_blockLine h89 h113 hC hrad hW hn3 hMZ hβ
  have hPα : P ≤ MulAction.stabilizer X (blockLineBase hC β) :=
    map_toConjAct_subgroupOf_le_stabilizer_alpha h113 hC hrad hn3 hβ (map_pCore_two_le_Malpha _)
  have hPN : MulAction.stabilizer X (blockLineBase hC β) ≤
      Subgroup.normalizer (P : Set X) :=
    stabilizer_le_normalizer_map_toConjAct_subgroupOf hC fun g hg x hx =>
      conj_mem_map_pCore_two_of_mem_normalizer hC.setup.normal hg (by simpa [Q] using hx)
  have hP2 : IsPGroup 2 P := isPGroup_mapToConjActStabilizer_pCore hC β
  have horb : ∀ γ : ↥ℓ, γ ≠ blockLineBase hC β → m ≤ (orbit P γ).ncard := by
    intro γ hγ
    rw [ncard_orbit_map_pCore h113 hC hrad hn3 hHns hβ γ hγ]
  have hlt : Nat.card ↥ℓ < m ^ 2 + 1 := by
    rw [Nat.card_coe_set_eq]
    exact ncard_blockLine_lt_sq_add_one h89 h113 hC hrad hW hn3 hMZ hHns hβ hb hVlt
  have hFα : F ≤ MulAction.stabilizer X (blockLineBase hC β) :=
    map_toConjAct_subgroupOf_le_stabilizer_alpha h113 hC hrad hn3 hβ hNM
  have hF2 : ∀ f ∈ F, ∀ ω : ↥ℓ, (f * f) • ω = ω :=
    map_toConjAct_subgroupOf_sq_smul h113 hC hrad hn3 hβ hNM hexp
  have hF4 : ∃ γ : ↥ℓ, 4 ≤ (orbit F γ).ncard :=
    ⟨pt, le_trans hm4 (le_ncard_orbit_mapToConjActStabilizer h113 hC hrad hn3 hβ hNM hcover rfl)⟩
  have hFsemi : ∀ f ∈ F, ∀ γ : ↥ℓ, f • γ = γ → γ ≠ blockLineBase hC β →
      ∀ ω : ↥ℓ, f • ω = ω :=
    map_toConjAct_subgroupOf_semiregular h113 hC hrad hn3 hβ hNM hsemi
  obtain ⟨e, he⟩ := exists_card_eq_two_pow_add_one_of_lt_sq' (X := X) (Ω := ↥ℓ)
    h2 (α := blockLineBase hC β) (P := P) hPα hPN hP2 (m := m) horb hlt
    (F := F) hFα hF2 hF4 hFsemi
  exact ⟨e, by rwa [Nat.card_coe_set_eq] at he⟩

theorem ncard_blockImage_eq_one_of_lt
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hV : ∀ v ∈ imageClass hC, Odd (Vmem (imageClass hC) v).ncard)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) (N : Subgroup G) (hNM : N ≤ Malpha D hC.alpha)
    (hexp : ∀ x ∈ N, ∀ ε ∈ blockLine D hC.alpha β, cimg (x * x) ε = ε)
    (hsemi : ∀ x ∈ N, ∀ δ ∈ blockLine D hC.alpha β, δ ≠ hC.alpha → cimg x δ = δ →
      ∀ ε ∈ blockLine D hC.alpha β, cimg x ε = ε)
    (hcover : (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) ⊆
      (fun x => cimg x β) '' (N : Set G))
    (hm4 : 4 ≤ ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard)
    {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    (hVlt : (Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)).ncard <
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard) :
    (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1 := by
  obtain ⟨e, he⟩ := exists_ncard_blockLine_eq_two_pow_add_one_of_lt h89 h113 hC hrad hW
    hn3 hMZ hHns hβ N hNM hexp hsemi hcover hm4 hb hVlt
  exact ncard_blockImage_quotient_eq_one h89 h113 hC hrad hW hn3 hMZ hHns hV hβ hb he

end Certified

end CFSG.OddTranspositions.PartFour
