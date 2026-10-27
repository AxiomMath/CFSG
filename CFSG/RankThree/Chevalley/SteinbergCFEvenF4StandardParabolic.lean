module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {J : Set (Fin τ.rank)}

theorem exists_smul_single_of_mem_parabolicRoots {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRoots τ J) :
    ∃ w ∈ parabolicWeylGroup τ J, ∃ j ∈ J, w • (Pi.single j 1 : Fin τ.rank → ℤ) = α := by
  rcases IsRoot.height_pos_or_neg hα.1 with hpos | hneg
  · exact exists_mem_parabolicWeylGroup_smul _ α rfl ⟨hα, hα.1, hpos⟩
  · obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-α) rfl
      ⟨neg_mem_parabolicRoots hα, IsRoot.neg hα.1, by rw [height_neg]; omega⟩
    refine ⟨w * simple τ j, mul_mem hw (Subgroup.subset_closure ⟨j, hj, rfl⟩), j, hj, ?_⟩
    rw [mul_smul, simple_smul, reflect_single_self, smul_neg, hwj, neg_neg]

theorem length_eq_parabolic_length {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ J) :
    (∃ ω : List (Fin τ.rank), (∀ i ∈ ω, i ∈ J) ∧ (coxeterSystem τ).wordProd ω = w ∧
      ω.length = (coxeterSystem τ).length w) ∧
    ∀ ω : List (Fin τ.rank), (∀ i ∈ ω, i ∈ J) → (coxeterSystem τ).wordProd ω = w →
      (coxeterSystem τ).length w ≤ ω.length := by
  obtain ⟨ω, hred, hprod, hJ⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.1 w hw
  refine ⟨⟨ω, hJ, hprod, ?_⟩, fun ω' _ hω' => ?_⟩
  · rw [← hprod]
    exact hred.symm
  · rw [← hω']
    exact (coxeterSystem τ).length_wordProd_le ω'

theorem nsmul_add_nsmul_mem_inversionSet {w : WeylGroup τ} {α β : Fin τ.rank → ℤ}
    (hα : α ∈ inversionSet w) (hβ : β ∈ inversionSet w) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot τ (a • α + b • β)) : a • α + b • β ∈ inversionSet w := by
  obtain ⟨-, hαp, -, hαn⟩ := hα
  obtain ⟨-, hβp, -, hβn⟩ := hβ
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, IsRoot.smul hr w, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · rw [smul_add, smul_comm, smul_comm w (b : ℕ), height_nsmul_add_nsmul]
    nlinarith

theorem exists_longest_mem_parabolicWeylGroup (τ : Tag) (J : Set (Fin τ.rank)) :
    ∃ w₀ ∈ parabolicWeylGroup τ J,
      (∀ w ∈ parabolicWeylGroup τ J, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) ∧
      (fun α => w₀ • α) '' parabolicPosRoots τ J = (fun α => -α) '' parabolicPosRoots τ J := by
  obtain ⟨wA, ⟨hwA, hA⟩, -⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.2.2
  have hfin : (parabolicPosRoots τ J).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1.1
  have hinv : inversionSet wA = parabolicPosRoots τ J := by
    refine Set.Subset.antisymm (inversionSet_subset_parabolicPosRoots hwA) fun α hα => ?_
    obtain ⟨β, hβ, hβα⟩ := (show wA • α ∈ (fun α => -α) '' parabolicPosRoots τ J from
      hA ▸ ⟨α, hα, rfl⟩)
    refine ⟨hα.1.1, hα.2.2, IsRoot.smul hα.1.1 wA, ?_⟩
    rw [← hβα, height_neg]
    have := hβ.2.2
    omega
  refine ⟨wA, hwA, fun w hw => ?_, hA⟩
  rw [(weyl_inversion_length τ).1, (weyl_inversion_length τ).1, hinv]
  exact Set.ncard_le_ncard (inversionSet_subset_parabolicPosRoots hw) hfin

variable (K : Type) [Field K]

theorem subsystemGroup_eq_iSup_rootSubgroup :
    subsystemGroup τ K J = ⨆ α ∈ parabolicRoots τ J, rootSubgroup τ K α := by
  apply le_antisymm
  · rw [subsystemGroup, Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact Subgroup.mem_iSup_of_mem (Pi.single i 1) (Subgroup.mem_iSup_of_mem
        (single_mem_parabolicRoots hi) (Subgroup.subset_closure ⟨c, rfl⟩))
    · rw [← pinnedX_neg_single]
      exact Subgroup.mem_iSup_of_mem (-Pi.single i 1) (Subgroup.mem_iSup_of_mem
        (neg_mem_parabolicRoots (single_mem_parabolicRoots hi)) (Subgroup.subset_closure ⟨c, rfl⟩))
  · refine iSup₂_le fun α hα => ?_
    obtain ⟨w, hw, j, hj, rfl⟩ := exists_smul_single_of_mem_parabolicRoots hα
    rw [← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ j)]
    rintro _ ⟨u, hu, rfl⟩
    have huQ : u ∈ subsystemGroup τ K J := by
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_single]
      exact xUnit_mem_subsystemGroup hj c
    have hn := canonicalRep_mem_subsystemGroup (K := K) hw
    exact mul_mem (mul_mem hn huQ) (inv_mem hn)

theorem existsUnique_subsystem_normal_form {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) :
    ∃! p : WeylGroup τ × ModGL τ K × ModGL τ K × ModGL τ K,
      p.1 ∈ parabolicWeylGroup τ J ∧ p.2.1 ∈ subsystemTorus τ K J ∧
      p.2.2.1 ∈ parabolicLeviUnipotent τ K J ∧ p.2.2.2 ∈ rootSpan τ K (inversionSet p.1) ∧
      g = p.2.1 * p.2.2.1 * canonicalRep (coxeterSystem τ) K p.1 * p.2.2.2 := by
  obtain ⟨-, -, hcover, -, -, -⟩ := subsystem_root_group_bruhat τ K J
  have hg' : g ∈ (subsystemGroup τ K J : Set (ModGL τ K)) := hg
  rw [hcover] at hg'
  simp only [Set.mem_iUnion, exists_prop] at hg'
  obtain ⟨w, hw, _, ⟨b, hb, _, rfl, rfl⟩, v, hv, rfl⟩ := hg'
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_subsystemBorel] at hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb
  refine ⟨(w, t, u, v), ⟨hw, ht, hu, hv, rfl⟩, ?_⟩
  rintro ⟨w', t', u', v'⟩ ⟨hw', ht', hu', hv', he⟩
  simp only at hw' ht' hu' hv' he
  have hcell : ∀ {w₁ : WeylGroup τ} {t₁ u₁ v₁ : ModGL τ K}, w₁ ∈ parabolicWeylGroup τ J →
      t₁ ∈ subsystemTorus τ K J → u₁ ∈ parabolicLeviUnipotent τ K J →
      v₁ ∈ rootSpan τ K (inversionSet w₁) →
      t₁ * u₁ * canonicalRep (coxeterSystem τ) K w₁ * v₁ ∈ subsystemCell τ K J w₁ :=
    fun hw₁ ht₁ hu₁ hv₁ => mem_subsystemCell.2 ⟨_, mul_mem (Subgroup.mem_sup_left ht₁)
      (Subgroup.mem_sup_right hu₁), _, rootSpan_inversionSet_le_subsystemBorel hw₁ hv₁, rfl⟩
  have hww : w' = w := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_subsystemCell (K := K) (A := J) hne)
      (hcell hw' ht' hu' hv') (he ▸ hcell hw ht hu hv)
  subst hww
  have hbv := (bijOn_subsystemCell (K := K) hw).injOn
    (show (t' * u', v') ∈ (subsystemBorel τ K J : Set (ModGL τ K)) ×ˢ
      (rootSpan τ K (inversionSet w') : Set (ModGL τ K)) from
      ⟨mul_mem (Subgroup.mem_sup_left ht') (Subgroup.mem_sup_right hu'), hv'⟩)
    (show (t * u, v) ∈ (subsystemBorel τ K J : Set (ModGL τ K)) ×ˢ
      (rootSpan τ K (inversionSet w') : Set (ModGL τ K)) from
      ⟨mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hu), hv⟩) he.symm
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hbv
  obtain ⟨h3, h4⟩ := eq_of_mul_eq_subsystem ht' ht hu' hu h1
  simp only at h2
  rw [h3, h4, h2]

theorem isNilpotent_parabolicLeviUnipotent :
    Group.IsNilpotent (parabolicLeviUnipotent τ K J) := by
  have : Group.IsNilpotent (posUnipotent τ K) :=
    ((positive_root_triangularity.{0, 0} τ).1 K).2.2.2.1
  have e : (parabolicLeviUnipotent τ K J).subgroupOf (posUnipotent τ K) ≃*
      parabolicLeviUnipotent τ K J :=
    Subgroup.subgroupOfEquivOfLe (parabolicLeviUnipotent_le_posUnipotent J)
  exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective

theorem parabolicLeviUnipotent_subgroupOf_normal :
    ((parabolicLeviUnipotent τ K J).subgroupOf (subsystemBorel τ K J)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
    (sup_le subsystemTorus_le_normalizer (Subgroup.le_normalizer))

theorem subsystemTorus_mul_comm {a b : ModGL τ K} (ha : a ∈ subsystemTorus τ K J)
    (hb : b ∈ subsystemTorus τ K J) : a * b = b * a := by
  refine closure_commute ?_ a ha b hb
  rintro _ ⟨i, -, s, rfl⟩ _ ⟨j, -, t, rfl⟩
  exact torusElt_mul_comm i j s t

theorem exists_subsystemBorel_hom_ker :
    ∃ φ : subsystemBorel τ K J →* subsystemTorus τ K J, Function.Surjective φ ∧
      φ.ker = (parabolicLeviUnipotent τ K J).subgroupOf (subsystemBorel τ K J) := by
  have : ((parabolicLeviUnipotent τ K J).subgroupOf (subsystemBorel τ K J)).Normal :=
    parabolicLeviUnipotent_subgroupOf_normal K
  let ψ : subsystemTorus τ K J →* (subsystemBorel τ K J) ⧸
      (parabolicLeviUnipotent τ K J).subgroupOf (subsystemBorel τ K J) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_left)
  have hbij : Function.Bijective ψ := by
    refine ⟨fun a b hab => ?_, fun x => ?_⟩
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
      have hmem : (a : ModGL τ K)⁻¹ * (b : ModGL τ K) ∈ parabolicLeviUnipotent τ K J :=
        Subgroup.mem_subgroupOf.1 hab
      have h1 : (a : ModGL τ K)⁻¹ * (b : ModGL τ K) ∈ subsystemTorus τ K J :=
        mul_mem (inv_mem a.2) b.2
      obtain ⟨-, h2⟩ := eq_of_mul_eq_subsystem (t := 1)
        (t' := (a : ModGL τ K)⁻¹ * (b : ModGL τ K)) (v := (a : ModGL τ K)⁻¹ * (b : ModGL τ K))
        (v' := 1) (one_mem _) h1 hmem (one_mem _) (by rw [one_mul, mul_one])
      exact Subtype.ext (by
        have := congrArg (fun x => (a : ModGL τ K) * x) h2
        simp only [mul_inv_cancel_left, mul_one] at this
        exact this.symm)
    · obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ x
      have hy' : y ∈ (subsystemTorus τ K J : Set (ModGL τ K)) *
          (parabolicLeviUnipotent τ K J : Set _) := by
        rw [← coe_subsystemBorel]
        exact hy
      obtain ⟨t, ht, u, hu, rfl⟩ := hy'
      refine ⟨⟨t, ht⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      change (t : ModGL τ K)⁻¹ * (t * u) ∈ parabolicLeviUnipotent τ K J
      rw [inv_mul_cancel_left]
      exact hu
  let e := MulEquiv.ofBijective ψ hbij
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _), e.symm.surjective.comp
    (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

variable {K}

theorem borel_mul_mem_subsystemCell {w : WeylGroup τ} {b x : ModGL τ K}
    (hb : b ∈ subsystemBorel τ K J) (hx : x ∈ subsystemCell τ K J w) :
    b * x ∈ subsystemCell τ K J w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_subsystemCell.1 hx
  exact mem_subsystemCell.2 ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩

theorem subsystemCell_simple_mul_subset {i : Fin τ.rank} (hi : i ∈ J) {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) {x : ModGL τ K}
    (hx : x ∈ subsystemCell τ K J (simple τ i) * subsystemCell τ K J w) :
    x ∈ subsystemCell τ K J (simple τ i * w) ∨ x ∈ subsystemCell τ K J w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_subsystemCell.1 hy
  rw [canonicalRep_simple] at *
  have e : b₁ * weylElt τ K i 1 * b₂ * z = b₁ * (weylElt τ K i 1 * (b₂ * z)) := by group
  change b₁ * weylElt τ K i 1 * b₂ * z ∈ _ ∨ b₁ * weylElt τ K i 1 * b₂ * z ∈ _
  rw [e]
  rcases weylElt_mul_mem_subsystemCell hi hw (borel_mul_mem_subsystemCell hb₂ hz) with h | h
  · exact Or.inl (borel_mul_mem_subsystemCell hb₁ h)
  · exact Or.inr (borel_mul_mem_subsystemCell hb₁ h)

theorem subsystemCell_simple_mul_of_length_eq_add_one {i : Fin τ.rank} (hi : i ∈ J)
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ J)
    (h : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1) :
    subsystemCell τ K J (simple τ i) * subsystemCell τ K J w =
      subsystemCell τ K J (simple τ i * w) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rcases subsystemCell_simple_mul_subset hi hw hx with h' | h'
    · exact h'
    · exfalso
      have hamb : x ∈ bruhatCell τ K (simple τ i * w) := by
        rw [← bruhatCell_simple_mul_of_length_eq_add_one h]
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        exact ⟨y, subsystemCell_subset_bruhatCell _ hy, z, subsystemCell_subset_bruhatCell _ hz,
          rfl⟩
      have hne : simple τ i * w ≠ w := fun he => by
        have := congrArg (coxeterSystem τ).length he
        omega
      exact Set.disjoint_left.1 (disjoint_bruhatCell hne) hamb
        (subsystemCell_subset_bruhatCell _ h')
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
    rw [← weylElt_mul_canonicalRep_of_length_eq h]
    refine ⟨b * canonicalRep (coxeterSystem τ) K (simple τ i) * 1,
      mem_subsystemCell.2 ⟨b, hb, 1, one_mem _, rfl⟩,
      1 * canonicalRep (coxeterSystem τ) K w * b', mem_subsystemCell.2 ⟨1, one_mem _, b', hb', rfl⟩,
      ?_⟩
    change b * canonicalRep (coxeterSystem τ) K (simple τ i) * 1 *
      (1 * canonicalRep (coxeterSystem τ) K w * b') = _
    rw [canonicalRep_simple]
    group

theorem subsystemCell_simple_mul_of_length_add_one_eq {i : Fin τ.rank} (hi : i ∈ J)
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ J)
    (h : (coxeterSystem τ).length (simple τ i * w) + 1 = (coxeterSystem τ).length w) :
    subsystemCell τ K J (simple τ i) * subsystemCell τ K J w =
      subsystemCell τ K J (simple τ i * w) ∪ subsystemCell τ K J w := by
  have hcell : ∀ {b b' : ModGL τ K}, b ∈ subsystemBorel τ K J → b' ∈ subsystemBorel τ K J →
      b * weylElt τ K i 1 * b' ∈ subsystemCell τ K J (simple τ i) := fun hb hb' => by
    rw [← canonicalRep_simple (coxeterSystem τ) K i]
    exact mem_subsystemCell.2 ⟨_, hb, _, hb', rfl⟩
  have hcellw : ∀ {b' : ModGL τ K}, b' ∈ subsystemBorel τ K J →
      canonicalRep (coxeterSystem τ) K w * b' ∈ subsystemCell τ K J w := fun hb' =>
    mem_subsystemCell.2 ⟨1, one_mem _, _, hb', by rw [one_mul]⟩
  have hd := torusElt_mem_subsystemBorel (K := K) hi (-1)
  refine Set.Subset.antisymm (fun x hx => subsystemCell_simple_mul_subset hi hw hx)
    (fun x hx => ?_)
  rcases hx with hx | hx
  ·
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
    have hn := weylElt_mul_canonicalRep_of_length_add_one_eq (R := K) (cs := coxeterSystem τ) h
    refine ⟨_, hcell (mul_mem hb (inv_mem hd)) (one_mem _), _, hcellw hb', ?_⟩
    rw [show canonicalRep (coxeterSystem τ) K (simple τ i * w) =
      (torusElt τ K i (-1))⁻¹ * (weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w) by
        rw [hn, inv_mul_cancel_left]]
    group
  ·
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
    have h' : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1 := by
      omega
    have hy : yUnit τ K i 1 ∈ rootSubgroup τ K (-Pi.single i 1) := by
      rw [← pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    obtain ⟨b₂, hb₂, h2⟩ := exists_mul_canonicalRep_eq_subsystem hw
      (neg_mem_parabolicRoots (single_mem_parabolicRoots hi)) (height_inv_smul_neg_single_pos h')
      hy
    have hr := weylElt_one_mul_xUnit (τ := τ) (R := K) i 1
    simp only [inv_one, Units.val_one] at hr
    have hx1 := xUnit_mem_subsystemBorel (K := K) hi 1
    have hxm := xUnit_mem_subsystemBorel (K := K) hi (-1)
    refine ⟨_, hcell (mul_mem (mul_mem hb (inv_mem hd)) (inv_mem hxm)) hx1, _,
      hcellw (mul_mem (inv_mem hb₂) hb'), ?_⟩
    calc b * (torusElt τ K i (-1))⁻¹ * (xUnit τ K i (-1))⁻¹ * weylElt τ K i 1 * xUnit τ K i 1 *
          (canonicalRep (coxeterSystem τ) K w * (b₂⁻¹ * b'))
        = b * (torusElt τ K i (-1))⁻¹ * (xUnit τ K i (-1))⁻¹ *
            (weylElt τ K i 1 * xUnit τ K i 1) *
            canonicalRep (coxeterSystem τ) K w * b₂⁻¹ * b' := by group
      _ = b * (torusElt τ K i (-1))⁻¹ * (xUnit τ K i (-1))⁻¹ *
            (xUnit τ K i (-1) * torusElt τ K i (-1)) *
            (yUnit τ K i 1 * canonicalRep (coxeterSystem τ) K w) * b₂⁻¹ * b' := by
          rw [hr]
          group
      _ = b * canonicalRep (coxeterSystem τ) K w * b' := by
          rw [h2]
          group

theorem list_prod_ofFn_eq_of_forall_ne {G : Type*} [Monoid G] :
    ∀ {n : ℕ} (f : Fin n → G) (j : Fin n), (∀ i, i ≠ j → f i = 1) → (List.ofFn f).prod = f j
  | 0, _, j, _ => j.elim0
  | n + 1, f, j, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun k hk => ?_) j h
    · intro h0
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h0 _ (Fin.succ_ne_zero i)
    · rw [hk 0 (Fin.succ_ne_zero k).symm, one_mul,
        list_prod_ofFn_eq_of_forall_ne (fun i => f i.succ) k fun i hi =>
          hk _ fun h' => hi (Fin.succ_injective _ h')]

theorem existsUnique_subsystemTorus_coords_F4 {M : Type} [Field M] {J : Set (Fin Tag.F4.rank)}
    {t : ModGL .F4 M} (ht : t ∈ subsystemTorus .F4 M J) :
    ∃! s : Fin Tag.F4.rank → Mˣ, (∀ j ∉ J, s j = 1) ∧
      t = (List.ofFn fun i => torusElt .F4 M i (s i)).prod := by
  obtain ⟨e, he⟩ := G2_F4_torus_coordinates .F4 (Or.inr rfl) M
  have hsingle : ∀ (j : Fin Tag.F4.rank) (c : Mˣ),
      (List.ofFn fun i => torusElt .F4 M i ((Pi.mulSingle j c : Fin Tag.F4.rank → Mˣ) i)).prod =
        torusElt .F4 M j c := by
    intro j c
    rw [list_prod_ofFn_eq_of_forall_ne _ j fun i hi => by
      rw [Pi.mulSingle_eq_of_ne hi, torusElt_one], Pi.mulSingle_eq_same]
  let S : Subgroup (Fin Tag.F4.rank → Mˣ) :=
    { carrier := {s | ∀ j ∉ J, s j = 1}
      mul_mem' := fun ha hb j hj => by rw [Pi.mul_apply, ha j hj, hb j hj, one_mul]
      one_mem' := fun _ _ => rfl
      inv_mem' := fun ha j hj => by rw [Pi.inv_apply, ha j hj, inv_one] }
  have hle : subsystemTorus .F4 M J ≤ ((S.map e.toMonoidHom).map (torusGroup .F4 M).subtype) := by
    rw [subsystemTorus, Subgroup.closure_le]
    rintro _ ⟨j, hj, c, rfl⟩
    refine ⟨e (Pi.mulSingle j c), ⟨Pi.mulSingle j c, fun i hi => ?_, rfl⟩, ?_⟩
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact Pi.mulSingle_eq_of_ne (M := fun _ => Mˣ) hij c
    · change ((e (Pi.mulSingle j c) : torusGroup .F4 M) : ModGL .F4 M) = _
      rw [he, hsingle]
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hle ht
  refine ⟨s, ⟨hs, he s⟩, fun s' ⟨_, hs'⟩ => ?_⟩
  apply e.injective
  apply Subtype.ext
  rw [he, he, ← hs']
  exact he s

theorem mem_map_rootSpan_of_entrywise_fixed {M : Type} [Field M] (σ : M ≃+* M)
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite) (hpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {u : ModGL τ M} (hu : u ∈ rootSpan τ M S) (hfix : Units.map (entrywiseHom σ.toRingHom) u = u) :
    u ∈ (rootSpan τ (fixSubfield σ) S).map (baseChangeGL (fixSubfield σ).subtype) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hbij := (positive_root_collection τ M).1 S hpos hclosed α hα hrange
  have hbijk := (positive_root_collection τ (fixSubfield σ)).1 S hpos hclosed α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : Units.map (entrywiseHom σ.toRingHom)
      ((List.ofFn fun k => pinnedX τ M (α k) (c k)).prod) =
        (List.ofFn fun k => pinnedX τ M (α k) (σ (c k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    refine Units.ext ?_
    rw [Function.comp_apply, Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom (α k) (c k)
  rw [hmap] at hfix
  have hc : (fun k => σ (c k)) = c := hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfix
  set c' : Fin n → fixSubfield σ := fun k => ⟨c k, congrFun hc k⟩
  refine ⟨(List.ofFn fun k => pinnedX τ (fixSubfield σ) (α k) (c' k)).prod,
    hbijk.1 (Set.mem_univ _), ?_⟩
  rw [map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  rw [Function.comp_apply, baseChangeGL_pinnedX]
  rfl

theorem baseChangeGL_canonicalRep {R S : Type} [Field R] [Field S] (f : R →+* S)
    (w : WeylGroup τ) :
    baseChangeGL f (canonicalRep (coxeterSystem τ) R w) = canonicalRep (coxeterSystem τ) S w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_weylElt_one f i)

theorem entrywise_mem_subsystemTorus {M : Type} [Field M] (σ : M ≃+* M) {t : ModGL τ M}
    (ht : t ∈ subsystemTorus τ M J) :
    Units.map (entrywiseHom σ.toRingHom) t ∈ subsystemTorus τ M J := by
  have hle : subsystemTorus τ M J ≤
      (subsystemTorus τ M J).comap (Units.map (entrywiseHom σ.toRingHom)) := by
    rw [subsystemTorus, Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, entrywise_torusElt]
    exact torusElt_mem_subsystemTorus hi _
  exact hle ht

theorem subsystemGroup_inf_entrywiseFixed_F4 {M : Type} [Field M] (σ : M ≃+* M)
    (J : Set (Fin Tag.F4.rank)) :
    subsystemGroup .F4 M J ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
      (subsystemGroup .F4 (fixSubfield σ) J).map (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι : ModGL .F4 k →* ModGL .F4 M := baseChangeGL k.subtype
  set σs : ModGL .F4 M →* ModGL .F4 M := Units.map (entrywiseHom σ.toRingHom)
  apply le_antisymm
  · rintro g ⟨hg, hgF⟩
    have hgF' : σs g = g := hgF
    obtain ⟨⟨w, t, u, v⟩, ⟨hw, ht, hu, hv, rfl⟩, huniq⟩ :=
      existsUnique_subsystem_normal_form M hg
    simp only at hw ht hu hv
    have hσ := huniq (w, σs t, σs u, σs v) ⟨hw, entrywise_mem_subsystemTorus σ ht,
      entrywise_mem_rootSpan hu, entrywise_mem_rootSpan hv, by
        rw [← hgF']
        simp only [σs, map_mul, entrywise_canonicalRep]⟩
    simp only [Prod.mk.injEq, true_and] at hσ
    obtain ⟨htF, huF, hvF⟩ := hσ
    obtain ⟨s, ⟨hs1, hst⟩, huniqt⟩ := existsUnique_subsystemTorus_coords_F4 ht
    have hσt : σs t = (List.ofFn fun i => torusElt .F4 M i
        (Units.map σ.toRingHom.toMonoidHom (s i))).prod := by
      rw [hst, map_list_prod, List.map_ofFn]
      exact congrArg List.prod (congrArg List.ofFn (funext fun i => entrywise_torusElt σ i (s i)))
    have hsF : ∀ i, Units.map σ.toRingHom.toMonoidHom (s i) = s i := by
      have h1 := huniqt (fun i => Units.map σ.toRingHom.toMonoidHom (s i)) ⟨fun j hj => by
        change Units.map σ.toRingHom.toMonoidHom (s j) = 1
        rw [hs1 j hj, map_one], by rw [← hσt, htF]⟩
      exact fun i => congrFun h1 i
    set s' : Fin Tag.F4.rank → kˣ := fun i => Units.mk0 ⟨(s i : M), by
      have := congrArg Units.val (hsF i)
      exact this⟩ (fun h => (s i).ne_zero (congrArg Subtype.val h))
    have ht' : t = ι ((List.ofFn fun i => torusElt .F4 k i (s' i)).prod) := by
      rw [hst, map_list_prod, List.map_ofFn]
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      rw [Function.comp_apply, baseChangeGL_torusElt]
      exact congrArg _ (Units.ext rfl)
    have ht'Q : (List.ofFn fun i => torusElt .F4 k i (s' i)).prod ∈ subsystemGroup .F4 k J := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      by_cases hi : i ∈ J
      · exact subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi _)
      · have : s' i = 1 := Units.ext (Subtype.ext (by
          change ((s i : Mˣ) : M) = 1
          rw [hs1 i hi, Units.val_one]))
        change torusElt .F4 k i (s' i) ∈ _
        rw [this, torusElt_one]
        exact one_mem _
    have hfinJ : (parabolicPosRoots .F4 J).Finite :=
      (finite_setOf_isRoot .F4).subset fun α hα => hα.1.1
    obtain ⟨u', hu', rfl⟩ := mem_map_rootSpan_of_entrywise_fixed σ hfinJ
      (fun α hα => hα.2) (fun α hα β hβ a b ha hb hr => add_mem_parabolicPosRoots hα hβ ha hb hr)
      hu huF
    obtain ⟨v', hv', rfl⟩ := mem_map_rootSpan_of_entrywise_fixed σ (inversionSet_finite w)
      (fun α hα => ⟨hα.1, hα.2.1⟩)
      (fun α hα β hβ a b ha hb hr => nsmul_add_nsmul_mem_inversionSet hα hβ ha hb hr) hv hvF
    refine ⟨(List.ofFn fun i => torusElt .F4 k i (s' i)).prod * u' *
      canonicalRep (coxeterSystem .F4) k w * v', mul_mem (mul_mem (mul_mem ht'Q
        (parabolicLeviUnipotent_le_subsystemGroup hu')) (canonicalRep_mem_subsystemGroup hw))
        (parabolicLeviUnipotent_le_subsystemGroup
          (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv')), ?_⟩
    rw [map_mul, map_mul, map_mul, ← ht', baseChangeGL_canonicalRep]
  · rw [subsystemGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, c, rfl | rfl⟩, rfl⟩
    · rw [baseChangeGL_xUnit]
      refine ⟨xUnit_mem_subsystemGroup hi _, ?_⟩
      change σs (xUnit .F4 M i (k.subtype c)) = xUnit .F4 M i (k.subtype c)
      rw [units_map_entrywiseHom_xUnit]
      exact congrArg _ c.2
    · rw [baseChangeGL_yUnit]
      refine ⟨yUnit_mem_subsystemGroup hi _, ?_⟩
      change σs (yUnit .F4 M i (k.subtype c)) = yUnit .F4 M i (k.subtype c)
      rw [units_map_entrywiseHom_yUnit]
      exact congrArg _ c.2


theorem even_F4_standard_parabolic_root_group_Bruhat_and_field_fixedness (M : Type) [Field M]
    (J : Set (Fin Tag.F4.rank)) :
    (∀ α ∈ parabolicRoots .F4 J, ∃ w ∈ parabolicWeylGroup .F4 J, ∃ j ∈ J,
      w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = α) ∧
    (∀ w ∈ parabolicWeylGroup .F4 J,
      (∃ ω : List (Fin Tag.F4.rank), (∀ i ∈ ω, i ∈ J) ∧ (coxeterSystem .F4).wordProd ω = w ∧
        ω.length = (coxeterSystem .F4).length w) ∧
      ∀ ω : List (Fin Tag.F4.rank), (∀ i ∈ ω, i ∈ J) → (coxeterSystem .F4).wordProd ω = w →
        (coxeterSystem .F4).length w ≤ ω.length) ∧
    (∃ w₀ ∈ parabolicWeylGroup .F4 J, (∀ w ∈ parabolicWeylGroup .F4 J,
        (coxeterSystem .F4).length w ≤ (coxeterSystem .F4).length w₀) ∧
      (fun α => w₀ • α) '' parabolicPosRoots .F4 J = (fun α => -α) '' parabolicPosRoots .F4 J) ∧
    subsystemGroup .F4 M J = ⨆ α ∈ parabolicRoots .F4 J, rootSubgroup .F4 M α ∧
    subsystemGroup .F4 M J ⊓ torusGroup .F4 M = subsystemTorus .F4 M J ∧
    (subsystemBorel .F4 M J : Set (ModGL .F4 M)) =
      (subsystemTorus .F4 M J : Set (ModGL .F4 M)) * (parabolicLeviUnipotent .F4 M J : Set _) ∧
    (∀ w ∈ parabolicWeylGroup .F4 J, inversionSet w ⊆ parabolicPosRoots .F4 J) ∧
    (∀ g ∈ subsystemGroup .F4 M J,
      ∃! p : WeylGroup .F4 × ModGL .F4 M × ModGL .F4 M × ModGL .F4 M,
        p.1 ∈ parabolicWeylGroup .F4 J ∧ p.2.1 ∈ subsystemTorus .F4 M J ∧
        p.2.2.1 ∈ parabolicLeviUnipotent .F4 M J ∧ p.2.2.2 ∈ rootSpan .F4 M (inversionSet p.1) ∧
        g = p.2.1 * p.2.2.1 * canonicalRep (coxeterSystem .F4) M p.1 * p.2.2.2) ∧
    (∀ {m : ℕ} (α : Fin m → Fin Tag.F4.rank → ℤ), Function.Injective α →
      Set.range α = parabolicPosRoots .F4 J →
      Set.BijOn (fun c : Fin m → M => (List.ofFn fun i => pinnedX .F4 M (α i) (c i)).prod)
        Set.univ (parabolicLeviUnipotent .F4 M J)) ∧
    (∀ w ∈ parabolicWeylGroup .F4 J, ∀ {m : ℕ} (α : Fin m → Fin Tag.F4.rank → ℤ),
      Function.Injective α → Set.range α = inversionSet w →
      Set.BijOn (fun c : Fin m → M => (List.ofFn fun i => pinnedX .F4 M (α i) (c i)).prod)
        Set.univ (rootSpan .F4 M (inversionSet w))) ∧
    (∀ s : Fin Tag.F4.rank → Mˣ, (∀ j ∉ J, s j = 1) →
      (List.ofFn fun i => torusElt .F4 M i (s i)).prod ∈ subsystemTorus .F4 M J) ∧
    (∀ t ∈ subsystemTorus .F4 M J, ∃! s : Fin Tag.F4.rank → Mˣ, (∀ j ∉ J, s j = 1) ∧
      t = (List.ofFn fun i => torusElt .F4 M i (s i)).prod) ∧
    (∀ w w' : WeylGroup .F4, w ≠ w' →
      Disjoint (subsystemCell .F4 M J w) (subsystemCell .F4 M J w')) ∧
    (∀ j ∈ J, ∀ w ∈ parabolicWeylGroup .F4 J,
      (coxeterSystem .F4).length (simple .F4 j * w) = (coxeterSystem .F4).length w + 1 →
      subsystemCell .F4 M J (simple .F4 j) * subsystemCell .F4 M J w =
        subsystemCell .F4 M J (simple .F4 j * w)) ∧
    (∀ j ∈ J, ∀ w ∈ parabolicWeylGroup .F4 J,
      (coxeterSystem .F4).length (simple .F4 j * w) + 1 = (coxeterSystem .F4).length w →
      subsystemCell .F4 M J (simple .F4 j) * subsystemCell .F4 M J w =
        subsystemCell .F4 M J (simple .F4 j * w) ∪ subsystemCell .F4 M J w) ∧
    Group.IsNilpotent (parabolicLeviUnipotent .F4 M J) ∧
    ((parabolicLeviUnipotent .F4 M J).subgroupOf (subsystemBorel .F4 M J)).Normal ∧
    (∃ φ : subsystemBorel .F4 M J →* subsystemTorus .F4 M J, Function.Surjective φ ∧
      φ.ker = (parabolicLeviUnipotent .F4 M J).subgroupOf (subsystemBorel .F4 M J)) ∧
    (∀ a ∈ subsystemTorus .F4 M J, ∀ b ∈ subsystemTorus .F4 M J, a * b = b * a) ∧
    ∀ σ : M ≃+* M,
      subsystemGroup .F4 M J ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
        (subsystemGroup .F4 (fixSubfield σ) J).map (baseChangeGL (fixSubfield σ).subtype) := by
  refine ⟨fun α hα => exists_smul_single_of_mem_parabolicRoots hα,
    fun w hw => length_eq_parabolic_length hw, exists_longest_mem_parabolicWeylGroup .F4 J,
    subsystemGroup_eq_iSup_rootSubgroup M, subsystemGroup_inf_torusGroup, coe_subsystemBorel,
    fun w hw => inversionSet_subset_parabolicPosRoots hw,
    fun g hg => existsUnique_subsystem_normal_form M hg,
    fun α hα hr => (positive_root_collection .F4 M).1 _ (fun β hβ => hβ.2)
      (fun β hβ γ hγ a b ha hb hab => add_mem_parabolicPosRoots hβ hγ ha hb hab) α hα hr,
    fun w _ {_} α hα hr => (positive_root_collection .F4 M).1 _ (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
      (fun β hβ γ hγ a b ha hb hab => nsmul_add_nsmul_mem_inversionSet hβ hγ ha hb hab) α hα hr,
    fun s hs => ?_, fun t ht => existsUnique_subsystemTorus_coords_F4 ht,
    fun w w' h => disjoint_subsystemCell h,
    fun j hj w hw h => subsystemCell_simple_mul_of_length_eq_add_one hj hw h,
    fun j hj w hw h => subsystemCell_simple_mul_of_length_add_one_eq hj hw h,
    isNilpotent_parabolicLeviUnipotent M, parabolicLeviUnipotent_subgroupOf_normal M,
    exists_subsystemBorel_hom_ker M, fun a ha b hb => subsystemTorus_mul_comm M ha hb,
    fun σ => subsystemGroup_inf_entrywiseFixed_F4 σ J⟩
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  by_cases hi : i ∈ J
  · exact torusElt_mem_subsystemTorus hi _
  · change torusElt .F4 M i (s i) ∈ _
    rw [hs i hi, torusElt_one]
    exact one_mem _

end CFSG.RankThree.Chevalley
