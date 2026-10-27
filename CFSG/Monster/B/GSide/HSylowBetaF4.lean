module

public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement Pointwise

section Center

variable {K : Type} [Field K]

theorem f4_coords_eq_zero_of_commute_rootElts
    [Finite K] [CharP K 2] (c : ℕ → K)
    (h : ∀ p, 24 ≤ p → p ≤ 47 → ⁅(f4PosList.map fun i => f4x K i (c i)).prod, f4x K p 1⁆ = 1) :
    ∀ i ∈ f4KillOrder, c i = 0 := by
  have hw : ∀ p, 24 ≤ p → p ≤ 47 → ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
      ([p].map fun q => f4x K q ((fun _ => (1 : K)) q)).prod⁆ = 1 := fun p hp hp' => by
    simpa using h p hp hp'
  have h24 := hw 24 (by norm_num) (by norm_num)
  have h25 := hw 25 (by norm_num) (by norm_num)
  have h27 := hw 27 (by norm_num) (by norm_num)
  have h33 := hw 33 (by norm_num) (by norm_num)
  have hD0 : ∀ j ∈ f4KillOrder.take 0, c j = 0 := by simp
  have k25 : c 25 = 0 := by
    simpa using f4_row_n c 0 hD0 (k := 26) (E := [(25, 1, 24, 1)]) (by decide +kernel) h24
  have hD1 := f4_take_succ hD0 k25
  have k27 : c 27 = 0 := by
    simpa using f4_row_n c 1 hD1 (k := 34) (E := [(27, 1, 33, 1)]) (by decide +kernel) h33
  have hD2 := f4_take_succ hD1 k27
  have k28 : c 28 = 0 := by
    simpa using f4_row_n c 2 hD2 (k := 35) (E := [(28, 1, 33, 1)]) (by decide +kernel) h33
  have hD3 := f4_take_succ hD2 k28
  have k30 : c 30 = 0 := by
    simpa using f4_row_n c 3 hD3 (k := 37) (E := [(30, 1, 33, 1)]) (by decide +kernel) h33
  have hD4 := f4_take_succ hD3 k30
  have k29 : c 29 = 0 := by
    simpa using f4_row_n c 4 hD4 (k := 36) (E := [(29, 1, 33, 1)]) (by decide +kernel) h33
  have hD5 := f4_take_succ hD4 k29
  have k35 : c 35 = 0 := by
    simpa using f4_row_n c 5 hD5 (k := 36) (E := [(35, 1, 24, 1)]) (by decide +kernel) h24
  have hD6 := f4_take_succ hD5 k35
  have k31 : c 31 = 0 := by
    simpa using f4_row_n c 6 hD6 (k := 38) (E := [(31, 1, 33, 1)]) (by decide +kernel) h33
  have hD7 := f4_take_succ hD6 k31
  have k37 : c 37 = 0 := by
    simpa using f4_row_n c 7 hD7 (k := 38) (E := [(37, 1, 24, 1)]) (by decide +kernel) h24
  have hD8 := f4_take_succ hD7 k37
  have k32 : c 32 = 0 := by
    simpa using f4_row_n c 8 hD8 (k := 39) (E := [(32, 1, 33, 1)]) (by decide +kernel) h33
  have hD9 := f4_take_succ hD8 k32
  have k40 : c 40 = 0 := by
    simpa using f4_row_n c 9 hD9 (k := 41) (E := [(40, 1, 24, 1)]) (by decide +kernel) h24
  have hD10 := f4_take_succ hD9 k40
  have k43 : c 43 = 0 := by
    simpa using f4_row_n c 10 hD10 (k := 44) (E := [(43, 1, 24, 1)]) (by decide +kernel) h24
  have hD11 := f4_take_succ hD10 k43
  have k46 : c 46 = 0 := by
    simpa using f4_row_n c 11 hD11 (k := 47) (E := [(46, 1, 33, 1)]) (by decide +kernel) h33
  have hD12 := f4_take_succ hD11 k46
  have k24 : c 24 = 0 := by
    simpa using f4_row_n c 12 hD12 (k := 26) (E := [(24, 1, 25, 1)]) (by decide +kernel) h25
  have hD13 := f4_take_succ hD12 k24
  have k33 : c 33 = 0 := by
    simpa using f4_row_n c 13 hD13 (k := 34) (E := [(33, 1, 27, 1)]) (by decide +kernel) h27
  have hD14 := f4_take_succ hD13 k33
  have k26 : c 26 = 0 := by
    simpa using f4_row_n c 14 hD14 (k := 29) (E := [(26, 1, 27, 1)]) (by decide +kernel) h27
  have hD15 := f4_take_succ hD14 k26
  have k34 : c 34 = 0 := by
    simpa using f4_row_n c 15 hD15 (k := 35) (E := [(34, 1, 25, 1)]) (by decide +kernel) h25
  have hD16 := f4_take_succ hD15 k34
  have k36 : c 36 = 0 := by
    simpa using f4_row_n c 16 hD16 (k := 38) (E := [(36, 1, 25, 1)]) (by decide +kernel) h25
  have hD17 := f4_take_succ hD16 k36
  have k38 : c 38 = 0 := by
    simpa using f4_row_n c 17 hD17 (k := 41) (E := [(38, 1, 27, 1)]) (by decide +kernel) h27
  have hD18 := f4_take_succ hD17 k38
  have k39 : c 39 = 0 := by
    simpa using f4_row_n c 18 hD18 (k := 42) (E := [(39, 1, 27, 1)]) (by decide +kernel) h27
  have hD19 := f4_take_succ hD18 k39
  have k41 : c 41 = 0 := by
    simpa using f4_row_n c 19 hD19 (k := 43) (E := [(41, 1, 25, 1)]) (by decide +kernel) h25
  have hD20 := f4_take_succ hD19 k41
  have k42 : c 42 = 0 := by
    simpa using f4_row_n c 20 hD20 (k := 44) (E := [(42, 1, 25, 1)]) (by decide +kernel) h25
  have hD21 := f4_take_succ hD20 k42
  have k45 : c 45 = 0 := by
    simpa using f4_row_n c 21 hD21 (k := 46) (E := [(45, 1, 27, 1)]) (by decide +kernel) h27
  have hD22 := f4_take_succ hD21 k45
  rw [show f4KillOrder.take 22 = f4KillOrder by decide] at hD22
  exact hD22

theorem f4_mem_of_commute_rootElts
    [Finite K] [CharP K 2] {z : ModGL .F4 K}
    (hz : z ∈ posUnipotent .F4 K) (h : ∀ p, 24 ≤ p → p ≤ 47 → ⁅z, f4x K p 1⁆ = 1) :
    ∃ c d : K, f4x K 44 c * f4x K 47 d = z := by
  obtain ⟨c, rfl⟩ := exists_f4_coords hz
  have h0 := f4_coords_eq_zero_of_commute_rootElts c h
  have hcover : ∀ i ∈ f4PosList, decide (i = 44 ∨ i = 47) = false → i ∈ f4KillOrder := by
    decide
  refine ⟨c 44, c 47, ?_⟩
  rw [← list_prod_map_filter_of_eq_one f4PosList (fun i => decide (i = 44 ∨ i = 47)) _
    (fun i hi hne => by rw [h0 i (hcover i hi hne), f4x_zero]),
    show f4PosList.filter (fun i => decide (i = 44 ∨ i = 47)) = [44, 47] by decide]
  simp

theorem exists_of_mem_center_posUnipotent_F4
    [Finite K] [CharP K 2] (z : posUnipotent .F4 K)
    (hz : z ∈ Subgroup.center (posUnipotent .F4 K)) :
    ∃ c d : K, f4x K 44 c * f4x K 47 d = z := by
  refine f4_mem_of_commute_rootElts z.2 fun p hp hp' => ?_
  have h := Subgroup.mem_center_iff.1 hz ⟨_, f4x_mem_posUnipotent (K := K) ⟨hp, hp'⟩ 1⟩
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (congrArg Subtype.val h).symm

theorem f4x_44_eq_commutator
    [CharP K 2] (c : K) : f4x K 44 c = ⁅f4x K 24 1, f4x K 43 c⁆ := by
  have h := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K 24 43 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 c
  have hl : (f4OddCommutatorFactors.lookup (24, 43)).getD [] = [(1, 1, 44)] := by decide +kernel
  rw [hl] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    one_mul, pow_one] at h
  exact h.symm

theorem f4x_47_eq_commutator
    [CharP K 2] (d : K) : f4x K 47 d = ⁅f4x K 33 1, f4x K 46 d⁆ := by
  have h := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K 33 46 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 d
  have hl : (f4OddCommutatorFactors.lookup (33, 46)).getD [] = [(1, 1, 47)] := by decide +kernel
  rw [hl] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    one_mul, pow_one] at h
  exact h.symm

theorem center_posUnipotent_F4_le_commutator
    [Finite K] [CharP K 2] :
    Subgroup.center (posUnipotent .F4 K) ≤ commutator (posUnipotent .F4 K) := by
  intro z hz
  obtain ⟨c, d, hcd⟩ := exists_of_mem_center_posUnipotent_F4 z hz
  have hmem : (z : ModGL .F4 K) ∈ ⁅posUnipotent .F4 K, posUnipotent .F4 K⁆ := by
    rw [← hcd, f4x_44_eq_commutator, f4x_47_eq_commutator]
    exact Subgroup.mul_mem _
      (Subgroup.commutator_mem_commutator (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)
        (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _))
      (Subgroup.commutator_mem_commutator (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _)
        (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ _))
  rw [← Subgroup.map_subtype_commutator] at hmem
  exact (Subgroup.mem_map_iff_mem (posUnipotent .F4 K).subtype_injective).1 hmem

end Center

section Two

theorem torusGroup_zmod_two
    (τ : Tag) : torusGroup τ (ZMod 2) = ⊥ := by
  rw [torusGroup, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨⟨i, t⟩, rfl⟩
  have ht : t = 1 := Units.ext (by
    have h := t.ne_zero
    revert h
    generalize (t : ZMod 2) = x
    revert x
    decide)
  subst ht
  show torusElt τ (ZMod 2) i 1 ∈ ({1} : Set (ModGL τ (ZMod 2)))
  rw [torusElt_one]
  exact Set.mem_singleton 1

theorem adjointGroup_inf_normalizer_posUnipotent_zmod_two
    (τ : Tag) :
    adjointGroup τ (ZMod 2) ⊓
        Subgroup.normalizer (posUnipotent τ (ZMod 2) : Set (ModGL τ (ZMod 2))) =
      posUnipotent τ (ZMod 2) := by
  rw [(borel_self_normalizers τ (ZMod 2)).1, borelGroup, torusGroup_zmod_two, bot_sup_eq]

theorem natCard_posUnipotent_F4_zmod_two :
    Nat.card (posUnipotent .F4 (ZMod 2)) = 2 ^ 24 := by
  rw [card_posUnipotent, Nat.card_zmod, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4]

theorem natCard_adjointGroup_F4_zmod_two :
    Nat.card (adjointGroup .F4 (ZMod 2)) = 2 ^ 24 * 197358525 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, Nat.card_zmod]
  norm_num [CFSG.Open.ordF4]

theorem natCard_center_posUnipotent_F4_zmod_two :
    Nat.card (Subgroup.center (posUnipotent .F4 (ZMod 2))) ≤ 4 := by
  have h : ∀ z : Subgroup.center (posUnipotent .F4 (ZMod 2)),
      ∃ p : ZMod 2 × ZMod 2, f4x (ZMod 2) 44 p.1 * f4x (ZMod 2) 47 p.2 = z := fun z => by
    obtain ⟨c, d, h⟩ := exists_of_mem_center_posUnipotent_F4 (z : posUnipotent .F4 (ZMod 2)) z.2
    exact ⟨(c, d), h⟩
  have hinj : Function.Injective fun z => (h z).choose := by
    intro z z' hzz'
    have e1 := (h z).choose_spec
    have e2 := (h z').choose_spec
    simp only at hzz'
    rw [hzz'] at e1
    exact Subtype.ext (Subtype.ext (e1.symm.trans e2))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_zmod] at this

end Two

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem center_le_commutator_of_mulEquiv (φ : G ≃* G')
    (h : Subgroup.center G' ≤ commutator G') : Subgroup.center G ≤ commutator G := by
  intro z hz
  have h1 : φ z ∈ Subgroup.center G' := by
    rw [← Subgroup.map_center_eq φ]
    exact ⟨z, hz, rfl⟩
  have h2 := h h1
  have hr : φ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 φ.surjective
  have h3 : (commutator G).map φ.toMonoidHom = commutator G' := by
    rw [map_commutator_eq, hr, ← _root_.commutator_def]
  rw [← h3] at h2
  exact (Subgroup.mem_map_iff_mem φ.injective).1 h2

end Transport

theorem sylow_facts_of_mulEquiv_F4
    {F : Type*} [Group F] [Finite F]
    (e : F ≃* adjointGroup .F4 (ZMod 2)) {P : Subgroup F} (hP : Nat.card P = 2 ^ 24) :
    Nat.card (Subgroup.center P) ≤ 4 ∧ Subgroup.center P ≤ commutator P ∧
      Subgroup.normalizer (P : Set F) = P ∧
      ∀ x ∈ P ⊓ Subgroup.centralizer (P : Set F), ∀ g : F,
        g * x * g⁻¹ ∈ P ⊓ Subgroup.centralizer (P : Set F) → g * x * g⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := adjointGroup .F4 (ZMod 2) with hA
  have : Finite A := Finite.of_equiv F e.toEquiv
  have hAcard : Nat.card A = 2 ^ 24 * 197358525 := natCard_adjointGroup_F4_zmod_two
  have hFcard : Nat.card F = 2 ^ 24 * 197358525 := (Nat.card_congr e.toEquiv).trans hAcard
  have hfac : ∀ n : ℕ, n = 2 ^ 24 * 197358525 → n.factorization 2 = 24 := by
    rintro n rfl
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  set Q₀ : Subgroup A := (posUnipotent .F4 (ZMod 2)).subgroupOf A with hQ₀
  have hQ₀card : Nat.card Q₀ = 2 ^ 24 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).toEquiv).trans
      natCard_posUnipotent_F4_zmod_two
  set Q : Subgroup A := P.map e.toMonoidHom with hQ
  have hQcard : Nat.card Q = 2 ^ 24 :=
    (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans hP
  set S₀ : Sylow 2 A := Sylow.ofCard Q₀ (by rw [hQ₀card, hfac _ hAcard]) with hS₀
  set S : Sylow 2 A := Sylow.ofCard Q (by rw [hQcard, hfac _ hAcard]) with hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S₀ S
  have hgQ : Q₀.map (MulAut.conj g).toMonoidHom = Q := by
    have h1 : ((g • S₀ : Sylow 2 A) : Subgroup A) = (S : Subgroup A) :=
      congrArg (fun T : Sylow 2 A => (T : Subgroup A)) hg
    rw [Sylow.coe_subgroup_smul] at h1
    have h2 : (S : Subgroup A) = Q := Sylow.coe_ofCard _ _
    have h3 : (S₀ : Subgroup A) = Q₀ := Sylow.coe_ofCard _ _
    rw [h2, h3] at h1
    exact (show Q₀.map (MulAut.conj g).toMonoidHom = MulAut.conj g • Q₀ from rfl).trans h1
  have eP : P ≃* posUnipotent .F4 (ZMod 2) :=
    ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hgQ.symm)).trans
      (((Q₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm).trans
        (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup))
  have hN₀ : Subgroup.normalizer (Q₀ : Set A) = Q₀ := by
    ext a
    rw [Subgroup.mem_normalizer_iff, hQ₀, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (a : ModGL .F4 (ZMod 2)) ∈ adjointGroup .F4 (ZMod 2) ⊓
          Subgroup.normalizer (posUnipotent .F4 (ZMod 2) : Set (ModGL .F4 (ZMod 2))) := by
        refine ⟨a.2, Subgroup.mem_normalizer_iff.2 fun x => ?_⟩
        constructor
        · intro hx
          have := (h ⟨x, posUnipotent_le_adjointGroup hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
          exact Subgroup.mem_subgroupOf.1 this
        · intro hx
          have hxA : x ∈ adjointGroup .F4 (ZMod 2) := by
            have h1 : (a : ModGL .F4 (ZMod 2)) * x * (a : ModGL .F4 (ZMod 2))⁻¹ ∈
                adjointGroup .F4 (ZMod 2) := posUnipotent_le_adjointGroup hx
            have h2 := (adjointGroup .F4 (ZMod 2)).mul_mem
              ((adjointGroup .F4 (ZMod 2)).mul_mem ((adjointGroup .F4 (ZMod 2)).inv_mem a.2) h1)
              a.2
            rwa [show (a : ModGL .F4 (ZMod 2))⁻¹ * ((a : ModGL .F4 (ZMod 2)) * x *
              (a : ModGL .F4 (ZMod 2))⁻¹) * a = x by group] at h2
          have := (h ⟨x, hxA⟩).2 (Subgroup.mem_subgroupOf.2 hx)
          exact Subgroup.mem_subgroupOf.1 this
      rw [adjointGroup_inf_normalizer_posUnipotent_zmod_two] at h'
      exact h'
    · intro ha x
      constructor
      · intro hx
        exact Subgroup.mem_subgroupOf.2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha
          (Subgroup.mem_subgroupOf.1 hx)) (Subgroup.inv_mem _ ha))
      · intro hx
        have h1 := Subgroup.mem_subgroupOf.1 hx
        have h2 := (posUnipotent .F4 (ZMod 2)).mul_mem
          ((posUnipotent .F4 (ZMod 2)).mul_mem ((posUnipotent .F4 (ZMod 2)).inv_mem ha) h1) ha
        rw [show (a : ModGL .F4 (ZMod 2))⁻¹ * (((a * x * a⁻¹ : A)) : ModGL .F4 (ZMod 2)) * a =
          (x : ModGL .F4 (ZMod 2)) by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group]
          at h2
        exact Subgroup.mem_subgroupOf.2 h2
  have hNQ : Subgroup.normalizer (Q : Set A) = Q := by
    rw [← hgQ, ← Subgroup.map_equiv_normalizer_eq Q₀ (MulAut.conj g), hN₀]
  have hNP : Subgroup.normalizer (P : Set F) = P := by
    have hN := Subgroup.map_equiv_normalizer_eq P e
    rw [← hQ, hNQ] at hN
    exact Subgroup.map_injective e.injective hN
  refine ⟨?_, center_le_commutator_of_mulEquiv eP center_posUnipotent_F4_le_commutator, hNP, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr eP).toEquiv]
    exact natCard_center_posUnipotent_F4_zmod_two
  ·
    intro x hx h hy
    set T : Sylow 2 F := Sylow.ofCard P (by rw [hP, hfac _ hFcard]) with hT
    have hx' : x ∈ Subgroup.centralizer (T : Set F) := hx.2
    have hy' : h⁻¹⁻¹ * x * h⁻¹ ∈ Subgroup.centralizer (T : Set F) := by
      rw [inv_inv]
      exact hy.2
    obtain ⟨n, hn, hn'⟩ := T.conj_eq_normalizer_conj_of_mem_centralizer x h⁻¹ hx' hy'
    rw [inv_inv] at hn'
    rw [hn']
    have hnP : n ∈ P := by
      have : n ∈ Subgroup.normalizer (P : Set F) := hn
      rwa [hNP] at this
    have hc := Subgroup.mem_centralizer_iff.1 hx.2 n⁻¹ (P.inv_mem hnP)
    rw [hc, inv_mul_cancel_right]

theorem center_facts_of_le_of_mulEquiv_F4
    {G : Type*} [Group G] [Finite G] {F P : Subgroup G}
    (e : F ≃* adjointGroup .F4 (ZMod 2)) (hPF : P ≤ F) (hP : Nat.card P = 2 ^ 24) :
    Nat.card ((Subgroup.center P).map P.subtype) ≤ 4 ∧
      (Subgroup.center P).map P.subtype ≤ ⁅P, P⁆ := by
  let φ : P.subgroupOf F ≃* P := Subgroup.subgroupOfEquivOfLe hPF
  have hP' : Nat.card (P.subgroupOf F) = 2 ^ 24 := (Nat.card_congr φ.toEquiv).trans hP
  obtain ⟨h1, h2, -, -⟩ := sylow_facts_of_mulEquiv_F4 e hP'
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective P.subtype_injective,
      ← Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
    exact h1
  · rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono (center_le_commutator_of_mulEquiv φ.symm h2)

end CFSG.Monster.B.GSide
