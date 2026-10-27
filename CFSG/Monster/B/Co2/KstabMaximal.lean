module

public import CFSG.Monster.B.Co2.Simple
public import CFSG.Monster.B.Co2.KstabMaximalCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GroupActions

section Generic

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem eq_or_eq_top_of_orbit_partition (a : Ω) (S : Subgroup G)
    (hS : S ≤ MulAction.stabilizer G a) {ι : Type*} [Fintype ι] (b : ι → Ω) (n : ι → ℕ) (i₀ : ι)
    (hb₀ : b i₀ = a) (hbmem : ∀ i, b i ∈ MulAction.orbit G a)
    (hn : ∀ i, (MulAction.orbit S (b i)).ncard = n i)
    (hne : ∀ i j, i ≠ j → MulAction.orbit S (b i) ≠ MulAction.orbit S (b j))
    (hfin : (MulAction.orbit G a).Finite)
    (hsumN : ∑ i, n i = (MulAction.orbit G a).ncard)
    (hsub : ∀ I : Finset ι, i₀ ∈ I → (∑ i ∈ I, n i) ∣ (MulAction.orbit G a).ncard →
      I = {i₀} ∨ I = Finset.univ)
    (X : Subgroup G) (hX : MulAction.stabilizer G a ≤ X) :
    X = MulAction.stabilizer G a ∨ X = ⊤ := by
  classical
  set H := MulAction.stabilizer G a with hH
  set O := MulAction.orbit G a with hO
  set T : ι → Set Ω := fun i => MulAction.orbit S (b i) with hT
  have hTO : ∀ i, T i ⊆ O := fun i => by
    refine (MulAction.orbit_subgroup_subset S (b i)).trans ?_
    rw [MulAction.orbit_eq_iff.2 (hbmem i)]
  have hTfin : ∀ i, (T i).Finite := fun i => hfin.subset (hTO i)
  have hdisj : Pairwise (Function.onFun Disjoint T) := fun i j hij => by
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    apply hne i j hij
    rw [← MulAction.orbit_eq_iff.2 hzi, ← MulAction.orbit_eq_iff.2 hzj]
  have hcov : (⋃ i, T i) = O := by
    apply Set.eq_of_subset_of_ncard_le (Set.iUnion_subset hTO) _ hfin
    rw [Set.ncard_iUnion_of_finite hTfin hdisj, finsum_eq_sum_of_fintype]
    simp only [hT, hn]
    exact hsumN.ge
  set Y : Set Ω := MulAction.orbit X a with hY
  have hYO : Y ⊆ O := MulAction.orbit_subgroup_subset X a
  have hSY : ∀ s ∈ S, ∀ y ∈ Y, s • y ∈ Y := by
    intro s hs y hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨⟨s * x, X.mul_mem (hX (hS hs)) x.2⟩, ?_⟩
    change (s * (x : G)) • a = s • (x : G) • a
    rw [mul_smul]
  set I : Finset ι := Finset.univ.filter fun i => b i ∈ Y with hI
  have hYI : Y = ⋃ i ∈ (I : Set ι), T i := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · intro hy
      have hyO := hYO hy
      rw [← hcov] at hyO
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyO
      refine ⟨i, ?_, hi⟩
      rw [hI, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨s, rfl⟩ := hi
      have := hSY ((s : G)⁻¹) (S.inv_mem s.2) _ hy
      simpa [Subgroup.smul_def] using this
    · rintro ⟨i, hi, hy⟩
      have hi' : b i ∈ Y := by simpa [hI] using hi
      obtain ⟨s, rfl⟩ := hy
      exact hSY s s.2 (b i) hi'
  have hYcard : Y.ncard = ∑ i ∈ I, n i := by
    rw [hYI, Set.Finite.ncard_biUnion I.finite_toSet (fun i _ => hTfin i)
      (hdisj.set_pairwise _), finsum_mem_coe_finset]
    exact Finset.sum_congr rfl fun i _ => hn i
  have hrel : H.relIndex X = Y.ncard := by
    rw [Subgroup.relIndex, hH, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  have hidx : Y.ncard * X.index = O.ncard := by
    rw [← hrel, ← MulAction.index_stabilizer G a, Subgroup.relIndex_mul_index hX]
  have hdvd : (∑ i ∈ I, n i) ∣ O.ncard := ⟨X.index, by rw [← hYcard, hidx]⟩
  have hi₀ : i₀ ∈ I := by
    rw [hI, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hb₀ ▸ MulAction.mem_orbit_self a⟩
  rcases hsub I hi₀ hdvd with hI1 | hI2
  · left
    have h1 : Y.ncard = 1 := by
      rw [hYcard, hI1, Finset.sum_singleton, ← hn, hb₀]
      have : MulAction.orbit S a = {a} := by
        ext y
        constructor
        · rintro ⟨s, rfl⟩
          exact hS s.2
        · rintro rfl
          exact MulAction.mem_orbit_self _
      rw [this, Set.ncard_singleton]
    exact le_antisymm (Subgroup.relIndex_eq_one.1 (hrel.trans h1)) hX
  · right
    have hpos : O.ncard ≠ 0 :=
      ((Set.ncard_pos hfin).2 ⟨a, MulAction.mem_orbit_self a⟩).ne'
    have h1 : Y.ncard = O.ncard := by
      rw [hYcard, hI2, hsumN]
    rw [h1] at hidx
    exact Subgroup.index_eq_one.1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos)
      (hidx.trans (mul_one _).symm))

end Generic

end CFSG.GroupActions

namespace CFSG.Monster.B.Co2.KstabMaximal

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.B.Short
  CFSG.Monster.Existence.CoPair.Native

@[expose, instance_reducible] def olqLeft : MulAction OLq L2 where
  smul k x := kOp k⁻¹ x
  one_smul x := by
    change kOp (1 : OLq)⁻¹ x = x
    rw [inv_one]
    exact LinearMap.congr_fun kOp_one x
  mul_smul k k' x := by
    change kOp (k * k')⁻¹ x = kOp k⁻¹ (kOp k'⁻¹ x)
    rw [mul_inv_rev, kOp_apply_mul]

attribute [local instance] olqLeft

theorem olqLeft_smul (k : OLq) (x : L2) : k • x = kOp k⁻¹ x := rfl

theorem stabilizer_olq (v : L2) : MulAction.stabilizer OLq v = Kstab v := by
  ext k
  rw [MulAction.mem_stabilizer_iff, olqLeft_smul]
  change kOp k⁻¹ v = v ↔ kOp k v = v
  constructor
  · intro h
    calc kOp k v = kOp k⁻¹⁻¹ (kOp k⁻¹ v) := by rw [inv_inv, h]
      _ = v := kOp_inv_apply k⁻¹ v
  · intro h
    calc kOp k⁻¹ v = kOp k⁻¹ (kOp k v) := by rw [h]
      _ = v := kOp_inv_apply k v

theorem orbit_olq_v0 :
    MulAction.orbit OLq v0 = shortSet := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective k⁻¹
    change k • v0 ∈ shortSet
    rw [olqLeft_smul, ← hg, kOp_mk]
    exact modTwoEnd_mem_shortSet g classOf_vMinus_mem_shortSet
  · intro hx
    obtain ⟨u, hu, hux⟩ := exists_Hvis_smul_eq_of_short classOf_vMinus_mem_shortSet hx
    obtain ⟨g, -, rfl⟩ := mem_Hvis.1 hu
    refine ⟨(QuotientGroup.mk g)⁻¹, ?_⟩
    change ((QuotientGroup.mk g)⁻¹ : OLq) • v0 = x
    rw [olqLeft_smul, inv_inv, kOp_mk]
    exact hux

theorem ncard_orbit_olq_v0 :
    (MulAction.orbit OLq v0).ncard = 98280 := by
  rw [orbit_olq_v0, ncard_shortSet]

theorem index_Kstab_v0 :
    (Kstab v0).index = 98280 := by
  rw [← stabilizer_olq, MulAction.index_stabilizer, ncard_orbit_olq_v0]

@[expose] def wordO (w : List ℕ) : OLq := (w.map alphaN).prod

theorem kOp_alphaN_dec
    {l : ℕ} (hl : l < 24) (v : ℕ) :
    kOp (alphaN l) (dec v) = dec (VisCert.Native.actRows (letterRows l) v) := by
  have h : alphaN l = alpha ⟨l, hl⟩ := by simp [alphaN, hl]
  rw [h, kOp_alpha_dec, VisCert.native_actRows_eq]
  rfl

theorem kOp_wordO_dec
    (w : List ℕ) (hw : ∀ l ∈ w, l < 24) (v : ℕ) :
    kOp (wordO w) (dec v) = dec (actLetters w v) := by
  induction w generalizing v with
  | nil =>
    rw [wordO, List.map_nil, List.prod_nil]
    exact LinearMap.congr_fun kOp_one (dec v)
  | cons l w ih =>
    have hl : l < 24 := hw l List.mem_cons_self
    have hcons : wordO (l :: w) = alphaN l * wordO w := by simp [wordO]
    rw [hcons, kOp_apply_mul, kOp_alphaN_dec hl,
      ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))]
    rfl

theorem wordO_mem_Kstab
    (w : List ℕ) : wordO w ∈ Kstab v0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact alphaN_mem l

theorem xWordN_lt : ∀ l ∈ xWordN, l < 24 := by decide

theorem yWordN_lt : ∀ l ∈ yWordN, l < 24 := by decide

@[expose] def Sgrp : Subgroup OLq := Subgroup.closure {(wordO xWordN)⁻¹, (wordO yWordN)⁻¹}

theorem Sgrp_le_Kstab :
    Sgrp ≤ Kstab v0 := by
  rw [Sgrp, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact inv_mem (wordO_mem_Kstab _)
  · exact inv_mem (wordO_mem_Kstab _)

theorem ncard_orbit_Sgrp_v0 :
    (MulAction.orbit Sgrp v0).ncard = 1 := by
  have : MulAction.orbit Sgrp v0 = {v0} := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      have hs : (s : OLq) ∈ MulAction.stabilizer OLq v0 := by
        rw [stabilizer_olq]
        exact Sgrp_le_Kstab s.2
      exact hs
    · rintro rfl
      exact MulAction.mem_orbit_self _
  rw [this, Set.ncard_singleton]

theorem genXY_zero (v : ℕ) : genXY 0 v = actLetters xWordN v := by
  simp [genXY, actXY]

theorem genXY_one (v : ℕ) : genXY 1 v = actLetters yWordN v := by
  simp [genXY, actXY]

theorem smul_dec_genXY_zero
    (v : ℕ) : (wordO xWordN)⁻¹ • dec v = dec (genXY 0 v) := by
  rw [olqLeft_smul, inv_inv, genXY_zero, kOp_wordO_dec _ xWordN_lt]

theorem smul_dec_genXY_one
    (v : ℕ) : (wordO yWordN)⁻¹ • dec v = dec (genXY 1 v) := by
  rw [olqLeft_smul, inv_inv, genXY_one, kOp_wordO_dec _ yWordN_lt]

theorem exists_smul_dec_genXY
    {g : ℕ} (hg : g < 2) (v : ℕ) :
    ∃ s : Sgrp, s • dec v = dec (genXY g v) := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact ⟨⟨(wordO xWordN)⁻¹, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
      smul_dec_genXY_zero v⟩
  · exact ⟨⟨(wordO yWordN)⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩,
      smul_dec_genXY_one v⟩

theorem orbPoint_spec {seed : ℕ} {lev par lab : ℕ → ℕ} {v : ℕ}
    (h : orbPoint seed lev par lab v = true) (hv : lev v ≠ 0) :
    (lev v = 1 → v = seed) ∧
    (lev v ≠ 1 → par v < 2 ^ 24 ∧ lab v < 2 ∧ lev (par v) + 1 = lev v ∧
      genXY (lab v) (par v) = v) ∧
    genXY 0 v < 2 ^ 24 ∧ lev (genXY 0 v) ≠ 0 ∧ genXY 1 v < 2 ^ 24 ∧ lev (genXY 1 v) ≠ 0 := by
  unfold orbPoint at h
  have h0 : (lev v == 0) = false := by simpa using hv
  simp only [h0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun hl => ?_, fun hl => ?_, h2, h3, h4, h5⟩
  · simpa [hl] using h1
  · have hl' : (lev v == 1) = false := by simpa using hl
    simp only [hl', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h1
    obtain ⟨⟨⟨hp, hg⟩, hlp⟩, hgp⟩ := h1
    exact ⟨hp, hg, hlp, hgp⟩

theorem ncard_orbit_Sgrp_of_orbCheck
    {seed N chunks : ℕ} {T : OrbTables} (hc : 0 < chunks)
    (h : orbCheck seed N T chunks = true) :
    (MulAction.orbit Sgrp (dec seed)).ncard = N := by
  simp only [orbCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hs, hlev⟩, hpar⟩, hcount⟩ := h
  have hpt := VisCert.parAll_spec hc hpar
  let F : Set ℕ := {v | v < 2 ^ 24 ∧ VisCert.Native.rd8 T.lev v ≠ 0}
  have hFfin : (dec '' F).Finite :=
    ((Set.finite_lt_nat (2 ^ 24)).subset fun v hv => hv.1).image dec
  have hseed : seed ∈ F := ⟨hs, by rw [hlev]; omega⟩
  have hX : ∀ v ∈ F, genXY 0 v ∈ F := fun v hv => by
    obtain ⟨-, -, h2, h3, -, -⟩ := orbPoint_spec (hpt v hv.1) hv.2
    exact ⟨h2, h3⟩
  have hY : ∀ v ∈ F, genXY 1 v ∈ F := fun v hv => by
    obtain ⟨-, -, -, -, h4, h5⟩ := orbPoint_spec (hpt v hv.1) hv.2
    exact ⟨h4, h5⟩
  have hreach : ∀ m v, v < 2 ^ 24 → VisCert.Native.rd8 T.lev v = m → m ≠ 0 →
      dec v ∈ MulAction.orbit Sgrp (dec seed) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro v hv hm hm0
      obtain ⟨h1, hpar', -⟩ := orbPoint_spec (hpt v hv) (by rw [hm]; exact hm0)
      by_cases hl1 : VisCert.Native.rd8 T.lev v = 1
      · rw [h1 hl1]
        exact MulAction.mem_orbit_self _
      · obtain ⟨hp, hg, hlp, himg⟩ := hpar' hl1
        have hpl : VisCert.Native.rd8 T.lev (VisCert.Native.rd32 T.par v) ≠ 0 := by omega
        have ih' := ih (VisCert.Native.rd8 T.lev (VisCert.Native.rd32 T.par v)) (by omega)
          (VisCert.Native.rd32 T.par v) hp rfl hpl
        obtain ⟨s, hs'⟩ := exists_smul_dec_genXY hg (VisCert.Native.rd32 T.par v)
        rw [← himg, ← hs']
        exact MulAction.mem_orbit_of_mem_orbit _ ih'
  have horb : MulAction.orbit Sgrp (dec seed) = dec '' F := by
    apply Set.Subset.antisymm
    · refine VisCert.orbit_closure_subset
        (S := ({(wordO xWordN)⁻¹, (wordO yWordN)⁻¹} : Set OLq)) hFfin ?_
        (x := dec seed) ⟨seed, hseed, rfl⟩
      rintro s (rfl | rfl) _ ⟨v, hv, rfl⟩
      · exact ⟨genXY 0 v, hX v hv, (smul_dec_genXY_zero v).symm⟩
      · exact ⟨genXY 1 v, hY v hv, (smul_dec_genXY_one v).symm⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact hreach _ v hv.1 rfl hv.2
  have hcardF : F.ncard = N := by
    have hF : F = ↑((Finset.range (2 ^ 24)).filter fun v => VisCert.Native.rd8 T.lev v ≠ 0) := by
      ext v
      simp [F]
    rw [hF, Set.ncard_coe_finset, ← hcount, VisCert.countBelow_eq]
    congr 1
  have hinj : Set.InjOn dec F := fun a ha b hb hab => dec_injective ha.1 hb.1 hab
  rw [horb, hinj.ncard_image, hcardF]

theorem ncard_orbit_Sgrp_of_orbitOf
    {seed N : ℕ} (hlt : CFSG.KC.AxisPlane.orbitOf 2 genXY seed ⊆ Set.Iio (2 ^ 24))
    (hN : (CFSG.KC.AxisPlane.orbitOf 2 genXY seed).ncard = N) :
    (MulAction.orbit Sgrp (dec seed)).ncard = N := by
  have hfin : (dec '' CFSG.KC.AxisPlane.orbitOf 2 genXY seed).Finite :=
    ((Set.finite_Iio (2 ^ 24)).subset hlt).image dec
  have hstep : ∀ v ∈ CFSG.KC.AxisPlane.orbitOf 2 genXY seed, ∀ g < 2,
      genXY g v ∈ CFSG.KC.AxisPlane.orbitOf 2 genXY seed :=
    fun v hv g hg => Relation.ReflTransGen.tail hv ⟨g, hg, rfl⟩
  have horb : MulAction.orbit Sgrp (dec seed) = dec '' CFSG.KC.AxisPlane.orbitOf 2 genXY seed := by
    apply Set.Subset.antisymm
    · refine VisCert.orbit_closure_subset
        (S := ({(wordO xWordN)⁻¹, (wordO yWordN)⁻¹} : Set OLq)) hfin ?_
        (x := dec seed) ⟨seed, Relation.ReflTransGen.refl, rfl⟩
      rintro s (rfl | rfl) _ ⟨v, hv, rfl⟩
      · exact ⟨genXY 0 v, hstep v hv 0 (by norm_num), (smul_dec_genXY_zero v).symm⟩
      · exact ⟨genXY 1 v, hstep v hv 1 (by norm_num), (smul_dec_genXY_one v).symm⟩
    · rintro _ ⟨v, hv, rfl⟩
      have hv' : Relation.ReflTransGen (fun a b => ∃ g < 2, b = genXY g a) seed v := hv
      clear hv
      induction hv' with
      | refl => exact MulAction.mem_orbit_self _
      | tail _ hab ih =>
        obtain ⟨g, hg, rfl⟩ := hab
        obtain ⟨s, hs⟩ := exists_smul_dec_genXY hg _
        rw [← hs]
        exact MulAction.mem_orbit_of_mem_orbit _ ih
  have hinj : Set.InjOn dec (CFSG.KC.AxisPlane.orbitOf 2 genXY seed) :=
    fun a ha b hb hab => dec_injective (hlt ha) (hlt hb) hab
  rw [horb, hinj.ncard_image, hN]

theorem ncard_orbit_Sgrp_one :
    (MulAction.orbit Sgrp (dec 1)).ncard = 47104 :=
  ncard_orbit_Sgrp_of_orbitOf kstabOrbit_one.1 kstabOrbit_one.2

theorem ncard_orbit_Sgrp_sixtyFour :
    (MulAction.orbit Sgrp (dec 64)).ncard = 46575 :=
  ncard_orbit_Sgrp_of_orbitOf kstabOrbit_sixtyFour.1 kstabOrbit_sixtyFour.2

theorem ncard_orbit_Sgrp_fourThousand :
    (MulAction.orbit Sgrp (dec 4096)).ncard = 4600 :=
  ncard_orbit_Sgrp_of_orbitOf kstabOrbit_fourThousand.1 kstabOrbit_fourThousand.2

theorem ellCls_mem_shortSet (j : Fin 24) : ellCls j ∈ shortSet := by
  have h : ∀ j : Fin 24, ∑ i : Fin 24, ellN (j : ℕ) (i : ℕ) * ellN (j : ℕ) (i : ℕ) = 32 := by
    decide +kernel
  refine ⟨ellVec j, mem_minVecs_iff.2 ⟨ellVec_mem j, ?_⟩, ?_⟩
  · simp only [normSq, ellVec_apply]
    exact h j
  · rw [classOf_of_mem (ellVec_mem j)]
    rfl

theorem dec_one_mem_shortSet : dec 1 ∈ shortSet := dec_one_shiftLeft 0 ▸ ellCls_mem_shortSet 0

theorem dec_sixtyFour_mem_shortSet : dec 64 ∈ shortSet :=
  dec_one_shiftLeft 6 ▸ ellCls_mem_shortSet 6

theorem dec_fourThousand_mem_shortSet : dec 4096 ∈ shortSet :=
  dec_one_shiftLeft 12 ▸ ellCls_mem_shortSet 12

theorem subset_sum_condition : ∀ I : Finset (Fin 4), 0 ∈ I →
    (∑ i ∈ I, (![1, 47104, 46575, 4600] : Fin 4 → ℕ) i) ∣ 98280 →
    I = {0} ∨ I = Finset.univ := by
  decide +kernel

theorem sizes_injective : Function.Injective (![1, 47104, 46575, 4600] : Fin 4 → ℕ) := by
  decide +kernel

theorem _root_.CFSG.Monster.B.Co2.Kstab_v0_eq_or_eq_top
    (X : Subgroup OLq) (hX : Kstab v0 ≤ X) :
    X = Kstab v0 ∨ X = ⊤ := by
  have o1 := ncard_orbit_Sgrp_one
  have o2 := ncard_orbit_Sgrp_sixtyFour
  have o3 := ncard_orbit_Sgrp_fourThousand
  have hn : ∀ i : Fin 4, (MulAction.orbit Sgrp
      ((![v0, dec 1, dec 64, dec 4096] : Fin 4 → L2) i)).ncard =
      (![1, 47104, 46575, 4600] : Fin 4 → ℕ) i := by
    intro i
    fin_cases i
    · exact ncard_orbit_Sgrp_v0
    · exact o1
    · exact o2
    · exact o3
  have hbmem : ∀ i : Fin 4, (![v0, dec 1, dec 64, dec 4096] : Fin 4 → L2) i ∈
      MulAction.orbit OLq v0 := by
    rw [orbit_olq_v0]
    intro i
    fin_cases i
    · exact classOf_vMinus_mem_shortSet
    · exact dec_one_mem_shortSet
    · exact dec_sixtyFour_mem_shortSet
    · exact dec_fourThousand_mem_shortSet
  rw [← stabilizer_olq] at hX ⊢
  refine GroupActions.eq_or_eq_top_of_orbit_partition v0 Sgrp
    (stabilizer_olq v0 ▸ Sgrp_le_Kstab) (![v0, dec 1, dec 64, dec 4096] : Fin 4 → L2)
    (![1, 47104, 46575, 4600] : Fin 4 → ℕ) 0 rfl hbmem hn
    (fun i j hij h => hij (sizes_injective (by rw [← hn i, ← hn j, h]))) (Set.toFinite _) ?_ ?_ X hX
  · rw [ncard_orbit_olq_v0]
    decide
  · rw [ncard_orbit_olq_v0]
    exact subset_sum_condition

theorem Kstab_v0_ne_top :
    Kstab v0 ≠ ⊤ := by
  intro h
  have := index_Kstab_v0
  rw [h, Subgroup.index_top] at this
  omega

theorem _root_.CFSG.Monster.B.Co2.isCoatom_Kstab_v0 :
    IsCoatom (Kstab v0) :=
  ⟨Kstab_v0_ne_top, fun X hX => (Kstab_v0_eq_or_eq_top X hX.le).resolve_left hX.ne'⟩

end CFSG.Monster.B.Co2.KstabMaximal
