module

public import CFSG.RankThree.PartTwo.Sec21.Theorem236
public import CFSG.RankThree.PartTwo.Sec21.Implications

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def sixTwelveV (E U : Subgroup G) (c : G) : Subgroup G :=
  ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer ({c} : Set G),
    E ⊓ Subgroup.centralizer (U : Set G)⁆

@[expose] def Item612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ E ∈ collectionIn (partTwoE G) A, ∀ U ∈ fourGroups E,
      ∃ c ∈ E ⊓ Subgroup.centralizer (U : Set G), c ≠ 1 ∧ ∃ L ∈ lZeroStarAt A c,
        U ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, U⁆ = L ∧
        sixTwelveV E U c ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, sixTwelveV E U c⁆ = L

@[expose] def Item45 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → ∀ A : Subgroup X, IsPGroup 3 A →
    (CFSG.pCore 3 X ≠ ⊥ ∨ (CFSG.Assembly.IsElemAbelian 3 A ∧ 27 ∣ Nat.card A)) →
    ∀ L ∈ thetaComponents 3 X, A ≤ Subgroup.normalizer (L : Set X)

theorem sixTwelveV_le_lThreeV (E U : Subgroup G) (c : G) : sixTwelveV E U c ≤ lThreeV E U c := by
  apply Subgroup.commutator_mono _ le_rfl
  have hHU : Subgroup.centralizer ((U : Set G) ∪ {c}) ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.centralizer_le Set.subset_union_left
  have hHc : Subgroup.centralizer ((U : Set G) ∪ {c}) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le Set.subset_union_right
  set H := Subgroup.centralizer ((U : Set G) ∪ {c})
  set P := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G))
  have hQH : P ⊓ Subgroup.centralizer ({c} : Set G) ≤ H := by
    intro x hx
    have hxU : x ∈ Subgroup.centralizer (U : Set G) := Subgroup.map_subtype_le _ hx.1
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := hx.2
    rw [Subgroup.mem_centralizer_iff] at hxU hxc ⊢
    rintro y (hy | hy)
    · exact hxU y hy
    · exact hxc y hy
  set Q : Subgroup H := (P ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf H
  have hQ2 : IsPGroup 2 Q := by
    have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup.map _
    exact (hP2.to_le inf_le_left).comap_subtype
  have hQn : Q.Normal := by
    constructor
    intro x hx h
    have hx' := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hx'.1
      have hn : (CFSG.pCore 2 (Subgroup.centralizer (U : Set G))).Normal := CFSG.pCore_normal
      refine ⟨⟨(h : G), hHU h.2⟩ * y * ⟨(h : G), hHU h.2⟩⁻¹, hn.conj_mem y hy _, ?_⟩
      simpa using hyx
    · have hxc : (x : G) ∈ Subgroup.centralizer ({c} : Set G) := hx'.2
      have hhc : (h : G) ∈ Subgroup.centralizer ({c} : Set G) := hHc h.2
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhc hxc) (Subgroup.inv_mem _ hhc)
  have hQle : Q ≤ CFSG.pCore 2 H := le_sSup ⟨hQn, hQ2⟩
  intro x hx
  exact ⟨⟨x, hQH hx⟩, hQle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem mem_normalizer_of_map_conj_eq {L : Subgroup G} {g : G}
    (h : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := by
      simpa [MulAut.conj_apply] using hyx
    exact hyx' ▸ hy

theorem lThreeV_le_normalizer [Finite G] {A E U L : Subgroup G} {c : G} (hEA : E ≤ A)
    (hA : ∀ L' ∈ thetaComponentsAt 3 c, A ≤ Subgroup.normalizer (L' : Set G))
    (hL : L ∈ thetaComponentsAt 3 c) : lThreeV E U c ≤ Subgroup.normalizer (L : Set G) := by
  rw [lThreeV, Subgroup.commutator_le]
  intro v hv b hb
  have hvc : v ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le Set.subset_union_right (Subgroup.map_subtype_le _ hv)
  have hbA : b ∈ A := hEA hb.1
  have hcv : (MulAut.conj v⁻¹) c = c := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hvc
    rw [MulAut.conj_apply, inv_inv, mul_assoc, ← hvc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hL' : L.map (MulAut.conj v⁻¹).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have h := map_mem_thetaComponentsAt (MulAut.conj v⁻¹) hL
    rwa [hcv] at h
  have e1 : L.map (MulAut.conj b⁻¹).toMonoidHom = L :=
    map_conj_eq_of_mem_normalizer (hA L hL (A.inv_mem hbA))
  have e2 : (L.map (MulAut.conj v⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj v⁻¹).toMonoidHom :=
    map_conj_eq_of_mem_normalizer (hA _ hL' hbA)
  have e3 : (L.map (MulAut.conj v⁻¹).toMonoidHom).map (MulAut.conj v).toMonoidHom = L := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id L]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have e0 : L.map (MulAut.conj ⁅v, b⁆).toMonoidHom =
      (((L.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj v⁻¹).toMonoidHom).map
        (MulAut.conj b).toMonoidHom).map (MulAut.conj v).toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      commutatorElement_def]
    group
  apply mem_normalizer_of_map_conj_eq
  rw [e0, e1, e2, e3]

theorem mem_lThreeStarPairs_of_six_twelve [Finite G] {A E U L : Subgroup G} {c : G}
    (hEA : E ≤ A) (hA : ∀ L' ∈ thetaComponentsAt 3 c, A ≤ Subgroup.normalizer (L' : Set G))
    (hc : c ∈ E ⊓ Subgroup.centralizer (U : Set G)) (hc1 : c ≠ 1) (hL : L ∈ lZeroStarAt A c)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUcomm : ⁅L, U⁆ = L)
    (hV : ⁅L, sixTwelveV E U c⁆ = L) : (c, L) ∈ lThreeStarPairs A E U := by
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hL
  have hVN := lThreeV_le_normalizer (U := U) hEA hA hLc
  refine ⟨hc, hc1, hL, hUL, hVN, hUcomm, le_antisymm ?_ ?_⟩
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVN
  · calc L = ⁅L, sixTwelveV E U c⁆ := hV.symm
      _ ≤ ⁅L, lThreeV E U c⁆ := Subgroup.commutator_mono le_rfl (sixTwelveV_le_lThreeV E U c)

theorem le_normalizer_of_item45 [Finite G] (h45 : Item45) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hA3 : CFSG.Assembly.IsElemAbelian 3 A) {c : G} (hcA : c ∈ A)
    (hc1 : c ≠ 1) : ∀ L ∈ thetaComponentsAt 3 c, A ≤ Subgroup.normalizer (L : Set G) := by
  have := hG.isSimpleGroup
  set C := Subgroup.centralizer ({c} : Set G)
  have hAC : A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA3.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
  have hCtop : C ≠ ⊤ := by
    intro hC
    have hcz : c ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := hC ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [center_eq_bot_of_simple hG.nonabelian, Subgroup.mem_bot] at hcz
    exact hc1 hcz
  have hC4 : SectionFourHyp C := hG.sectionFourHyp hCtop
  have hA' : IsPGroup 3 (A.subgroupOf C) := by
    have hA3' : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3.2 g g.2)⟩
    exact hA3'.comap_subtype
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcore : CFSG.pCore 3 C ≠ ⊥ := by
    set c' : C := ⟨c, hcC⟩
    have hc'3 : orderOf c' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hA3.2 c hcA) hc1
    have hZn : (Subgroup.zpowers c').Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hgc : g * c' = c' * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have : g * c' ^ k * g⁻¹ = c' ^ k := by
        rw [(Commute.zpow_right hgc k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem_zpowers c' k
    have hZ3 : IsPGroup 3 (Subgroup.zpowers c') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
    have hZle : Subgroup.zpowers c' ≤ CFSG.pCore 3 C := le_sSup ⟨hZn, hZ3⟩
    intro hbot
    have hc'1 : c' = 1 := by
      have := hZle (Subgroup.mem_zpowers c')
      rwa [hbot, Subgroup.mem_bot] at this
    exact hc1 (congrArg Subtype.val hc'1)
  intro L hL
  obtain ⟨L', hL', rfl⟩ := hL
  have hN := h45 C hC4 (A.subgroupOf C) hA' (Or.inl hcore) L' hL'
  intro a ha
  have haN : (⟨a, hAC ha⟩ : C) ∈ Subgroup.normalizer (L' : Set C) :=
    hN (Subgroup.mem_subgroupOf.mpr ha)
  rw [Subgroup.mem_normalizer_iff] at haN ⊢
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨_, (haN x').mp hx', rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : G) = a * x * a⁻¹ := hyx
    have hxC : x ∈ C := by
      have hx' : x = a⁻¹ * (y : G) * a := by
        rw [hyx']
        group
      rw [hx']
      exact C.mul_mem (C.mul_mem (C.inv_mem (hAC ha)) y.2) (hAC ha)
    refine ⟨⟨x, hxC⟩, (haN ⟨x, hxC⟩).mpr ?_, rfl⟩
    have : (⟨a, hAC ha⟩ : C) * ⟨x, hxC⟩ * (⟨a, hAC ha⟩ : C)⁻¹ = y := Subtype.ext hyx'.symm
    rw [this]
    exact hy

theorem item612Sec21_of_items (h612 : Item612) (h45 : Item45) : Item612Sec21 := by
  intro G _ _ A hA E hE U hU
  obtain ⟨c, hc, hc1, L, hL, hUL, hUcomm, -, hV⟩ :=
    h612 G hA.standing A hA.mem_S E hE U hU
  have hcA : c ∈ A := hE.2 hc.1
  exact ⟨(c, L), mem_lThreeStarPairs_of_six_twelve hE.2
    (le_normalizer_of_item45 h45 hA.standing.toTheoremFourHyp hA.mem_S.1.1 hcA hc1)
    hc hc1 hL hUL hUcomm hV⟩

theorem item236_of_items_six_twelve (h64 : Item64One) (h612 : Item612) (h45 : Item45)
    (h233 : Item233) (h234 : Item234) (hHolt : HoltUniqueFixedPointSimple) : Item236 :=
  item236_of_items h64 (item612Sec21_of_items h612 h45) h233 h234 hHolt

end CFSG.RankThree.PartTwo.Sec21
