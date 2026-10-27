module

public import CFSG.RankThree.PartOne.KE8F.MultiStab
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal)
open scoped Pointwise

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L]

@[expose] def famKernel (F : Set (Fin τ.rank → Lˣ)) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ ∀ a ∈ F, rootChar a α = 1}

@[expose] def famStabilizer (F : Set (Fin τ.rank → Lˣ)) : Set (WeylGroup τ) :=
  {w | ∀ a ∈ F, w ∈ rootCharStabilizer a}

theorem famKernel_subset (F : Set (Fin τ.rank → Lˣ)) {a : Fin τ.rank → Lˣ} (ha : a ∈ F) :
    famKernel F ⊆ rootCharKernel a := fun _ hα => ⟨hα.1, hα.2 a ha⟩

theorem mem_rootSpan_famKernel_of_conj_eq (F : Set (Fin τ.rank → Lˣ))
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite) (hSroot : ∀ α ∈ S, IsRoot τ α)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → L => (List.ofFn fun k => pinnedX τ L (α k) (c k)).prod)
        Set.univ (rootSpan τ L S))
    {u : ModGL τ L} (hu : u ∈ rootSpan τ L S)
    (hfix : ∀ a ∈ F, rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u) :
    u ∈ rootSpan τ L (famKernel F ∩ S) := by
  classical
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
  have hαS : ∀ k, α k ∈ S := fun k => (e.symm k).2
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : ∀ a ∈ F, rootDiagUnit τ a * (List.ofFn fun k => pinnedX τ L (α k) (c k)).prod *
      (rootDiagUnit τ a)⁻¹ =
        (List.ofFn fun k => pinnedX τ L (α k) ((rootChar a (α k) : L) * c k)).prod := by
    intro a _
    have h := map_list_prod (MulAut.conj (rootDiagUnit τ a)).toMonoidHom
      (List.ofFn fun k => pinnedX τ L (α k) (c k))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_ofFn] at h
    rw [h]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    exact rootDiagUnit_conj_pinnedX a (hSroot _ (hαS k)) (c k)
  have hc : ∀ a ∈ F, (fun k => (rootChar a (α k) : L) * c k) = c := fun a ha => by
    have h := hfix a ha
    rw [hmap a ha] at h
    exact hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) h
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  by_cases hk : ∀ a ∈ F, rootChar a (α k) = 1
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ famKernel F ∩ S) => rootSubgroup τ L β) (α k)
      ⟨⟨hSroot _ (hαS k), hk⟩, hαS k⟩ le_rfl (Subgroup.subset_closure ⟨c k, rfl⟩)
  · push Not at hk
    obtain ⟨a, haF, hne⟩ := hk
    have hck : c k = 0 := by
      have h1 : (rootChar a (α k) : L) * c k = c k := congrFun (hc a haF) k
      have h2 : ((rootChar a (α k) : L) - 1) * c k = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (Units.ext (sub_eq_zero.1 h3)) hne
      · exact h3
    simp only [hck, pinnedX_zero]
    exact one_mem _

theorem fam_factor (F : Set (Fin τ.rank → Lˣ)) {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hcomm : ∀ a ∈ F, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g) :
    ∃ w ∈ famStabilizer F, ∃ h ∈ torusGroup τ L,
      ∃ u ∈ rootSpan τ L (famKernel F ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∃ v ∈ rootSpan τ L (famKernel F ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) L w * v := by
  classical
  have hTB := triangular_borel_structure.{0, 0} τ L
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have hIU : ∀ w : WeylGroup τ, rootSpan τ L (inversionSet w) ≤ posUnipotent τ L := fun w =>
    iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin τ.rank → ℤ |
      IsRoot τ β ∧ 0 < height β}) => rootSubgroup τ L β) α ⟨hα.1, hα.2.1⟩ le_rfl
  have huniq := (Chevalley_toral_centralizer_Bruhat_factors τ L (1 : Fin τ.rank → Lˣ)).2.1
  have hfactor : ∀ g ∈ adjointGroup τ L, ∃ w : WeylGroup τ, ∃ h ∈ torusGroup τ L,
      ∃ u ∈ posUnipotent τ L, ∃ v ∈ rootSpan τ L (inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) L w * v := by
    intro g hg
    have hg1 : g ∈ toralCentralizer τ L 1 := by
      rw [mem_toralCentralizer, rootDiagUnit_one]
      exact ⟨hg, by simp⟩
    obtain ⟨w, -, h, hh, u, hu, v, hv, rfl⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors τ L (1 : Fin τ.rank → Lˣ)).1 g hg1
    exact ⟨w, h, hh, u, rootSpan_mono Set.inter_subset_right hu, v,
      rootSpan_mono Set.inter_subset_right hv, rfl⟩
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := hfactor g hg
  have hper : ∀ a ∈ F, w ∈ rootCharStabilizer a ∧
      rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u ∧
      rootDiagUnit τ a * v * (rootDiagUnit τ a)⁻¹ = v := by
    intro a ha
    have hgfix := hcomm a ha
    set d := rootDiagUnit τ a with hd
    obtain ⟨t, ht, hnt⟩ := exists_conj_canonicalRep a w
    have hdu : d * u * d⁻¹ ∈ posUnipotent τ L := by
      have := ((chevalley_root_character_and_field_conjugation τ L).2.2.2.1 a).2.1
      rw [← this]
      exact ⟨u, hu, rfl⟩
    have hdv : d * v * d⁻¹ ∈ rootSpan τ L (inversionSet w) := by
      have : (rootSpan τ L (inversionSet w)).map (MulAut.conj d).toMonoidHom =
          rootSpan τ L (inversionSet w) :=
        map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
      rw [← this]
      exact ⟨v, hv, rfl⟩
    have hu' : t⁻¹ * (d * u * d⁻¹) * t ∈ posUnipotent τ L := by
      have hN := hTB.2.2.1 (inv_mem ht)
      have := (Subgroup.mem_normalizer_iff.1 hN (d * u * d⁻¹)).1 hdu
      simpa using this
    have heq : h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem τ) L w *
        (d * v * d⁻¹) = h * u * canonicalRep (coxeterSystem τ) L w * v := by
      calc h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem τ) L w *
            (d * v * d⁻¹) =
          (d * h * d⁻¹) * (d * u * d⁻¹) * (t * canonicalRep (coxeterSystem τ) L w) *
            (d * v * d⁻¹) := by
            rw [conj_rootDiagUnit_of_mem_torusGroup a hh]
            group
        _ = (d * h * d⁻¹) * (d * u * d⁻¹) * (d * canonicalRep (coxeterSystem τ) L w * d⁻¹) *
            (d * v * d⁻¹) := by rw [hnt]
        _ = d * (h * u * canonicalRep (coxeterSystem τ) L w * v) * d⁻¹ := by group
        _ = h * u * canonicalRep (coxeterSystem τ) L w * v := hgfix
    obtain ⟨-, h1, h2, h3⟩ := huniq w w (h * t) h _ u _ v (mul_mem hh ht) hh hu' hu hdv hv heq
    have ht1 : t = 1 := by
      have := h1
      rwa [mul_eq_left] at this
    subst ht1
    have hufix : d * u * d⁻¹ = u := by simpa using h2
    have hw : w ∈ rootCharStabilizer a := by
      rw [← conj_canonicalRep_eq_iff, ← hd, hnt, one_mul]
    exact ⟨hw, hufix, h3⟩
  refine ⟨w, fun a ha => (hper a ha).1, h, hh, u, ?_, v, ?_, rfl⟩
  · exact mem_rootSpan_famKernel_of_conj_eq F hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (positive_root_collection τ L).2 α hα hr) hu (fun a ha => (hper a ha).2.1)
  · exact mem_rootSpan_famKernel_of_conj_eq F (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization τ L).2.1 w α hα hr) hv
      (fun a ha => (hper a ha).2.2)

theorem canonicalRep_mem_sup_of_mem_closure {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α}) :
    canonicalRep (coxeterSystem τ) L w ∈ torusGroup τ L ⊔ rootSpan τ L S := by
  classical
  set Q := rootSpan τ L S with hQ
  set H := torusGroup τ L with hH
  let N := monomialSubgroup τ L
  let π := weylQuotientHom τ L
  let Wsub : Subgroup (WeylGroup τ) := ((H ⊔ Q).subgroupOf N).map π
  have hgen : ∀ α ∈ S, rootReflection α ∈ Wsub := by
    intro α hα
    have hαr := hS α hα
    obtain ⟨hmem, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hαr).2.2.1 1
    refine ⟨⟨rootWeylSL2 τ L α 1, hmem⟩, ?_, hπ⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_sup_right ?_
    exact rootRankOneGroup_le_rootSpan hαr hα (hSn α hα) ⟨_, rfl⟩
  have hclW : Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α} ≤ Wsub := by
    rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, rfl⟩
    exact hgen α hα
  obtain ⟨m, hm, hmπ⟩ := hclW hw
  have hcanN : canonicalRep (coxeterSystem τ) L w ∈ N := canonicalRep_mem_monomialSubgroup L w
  obtain ⟨ρ, -, hρ, -, -, hρker⟩ := (Weyl_normalizer_quotient τ L).2.1
  have hρπ : ∀ g : N, ρ g = π g := fun g =>
    (hρ g).unique (mapsRootLines_weylQuotientHom g)
  have hcan : π ⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hker1 : (⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ * m⁻¹ : N) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρπ, hρπ, hcan, hmπ, mul_inv_cancel]
  rw [hρker, Subgroup.mem_subgroupOf] at hker1
  have hker2 : canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹ ∈ H := hker1
  have hmQ : (m : ModGL τ L) ∈ H ⊔ Q := hm
  have hc : canonicalRep (coxeterSystem τ) L w =
      (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) := by group
  rw [hc]
  exact mul_mem (Subgroup.mem_sup_left hker2) hmQ

theorem mem_torus_mul_rootSpan_of_commute_fam (F : Set (Fin τ.rank → Lˣ))
    (hstab : famStabilizer F ⊆ (Subgroup.closure
      {s | ∃ α ∈ famKernel F, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (hker : famKernel F ⊆ S) {y : ModGL τ L} (hy : y ∈ adjointGroup τ L)
    (hcomm : ∀ a ∈ F, y * rootDiagUnit τ a = rootDiagUnit τ a * y) :
    y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L)) := by
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)]
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := fam_factor F hy (fun a ha => by
    rw [← hcomm a ha]
    group)
  have hcl : Subgroup.closure {s | ∃ α ∈ famKernel F, s = rootReflection α} ≤
      Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α} :=
    Subgroup.closure_mono fun s ⟨α, hα, hs⟩ => ⟨α, hker hα, hs⟩
  have hnw := canonicalRep_mem_sup_of_mem_closure (L := L) hS hSn (hcl (hstab hw))
  have hQ : ∀ {S' : Set (Fin τ.rank → ℤ)}, S' ⊆ famKernel F →
      rootSpan τ L S' ≤ torusGroup τ L ⊔ rootSpan τ L S := fun hS' =>
    (rootSpan_mono (hS'.trans hker)).trans le_sup_right
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh)
    (hQ Set.inter_subset_left hu)) hnw) (hQ Set.inter_subset_left hv)

theorem famStabilizer_subset_closure_of {p : ℕ} (hp : p.Prime) {ζ : Lˣ} (hζ : orderOf ζ = p)
    (F : Set (Fin τ.rank → Lˣ)) [Finite F] (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1)
    (hU : ∀ z : F → Fin τ.rank → ZMod p, (∀ a : F, ∀ i, a.1 i = ζ ^ (z a i).val) →
      ¬ p ∣ Nat.card (⨅ a : F, dualWeylStabilizer (z a) : Subgroup (WeylGroup τ))) :
    famStabilizer F ⊆ (Subgroup.closure
      {s | ∃ α ∈ famKernel F, s = rootReflection α} : Set (WeylGroup τ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hprim : IsPrimitiveRoot (ζ : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hexp : ∀ a : F, ∀ i, ∃ n : ℕ, a.1 i = ζ ^ n := fun a i => by
    have hi : ((a.1 i : Lˣ) : L) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hF a.1 a.2 i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  intro w hw
  set z : F → Fin τ.rank → ZMod p := fun a i => (e a i : ZMod p) with hz
  have hzval : ∀ a : F, ∀ i, a.1 i = ζ ^ (z a i).val := fun a i => by
    rw [he a i, hz]
    simp only [ZMod.val_natCast]
    exact pow_eq_pow_mod _ hζp
  have hmem : ∀ a : F, w ∈ dualWeylStabilizer (z a) := fun a y =>
    (rootChar_eq_rootChar_iff hζ (e a) a.1 (he a) (w • y) y).1 (hw a.1 a.2 y)
  have h1 := iInf_dualWeylStabilizer_le_of_card z (hU z hzval) (Subgroup.mem_iInf.2 hmem)
  have hset : {s | ∃ α, IsRoot τ α ∧ (∀ a, charVal (z a) α = 0) ∧ s = rootReflection α} ⊆
      {s | ∃ α ∈ famKernel F, s = rootReflection α} := by
    rintro s ⟨α, hα, h, rfl⟩
    refine ⟨α, ⟨hα, fun a ha => ?_⟩, rfl⟩
    have h0 : charVal (fun i => (e ⟨a, ha⟩ i : ZMod p)) α =
        charVal (fun i => (e ⟨a, ha⟩ i : ZMod p)) 0 := by
      have := h ⟨a, ha⟩
      rw [hz] at this
      simp only at this
      rw [this]
      simp [charVal]
    have := (rootChar_eq_rootChar_iff hζ (e ⟨a, ha⟩) a (he ⟨a, ha⟩) α 0).2 h0
    rwa [rootChar_zero] at this
  exact Subgroup.closure_mono hset h1

theorem famStabilizer_subset_closure {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {ζ : Lˣ} (hζ : orderOf ζ = p)
    (F : Set (Fin τ.rank → Lˣ)) [Finite F] (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1) :
    famStabilizer F ⊆ (Subgroup.closure
      {s | ∃ α ∈ famKernel F, s = rootReflection α} : Set (WeylGroup τ)) :=
  famStabilizer_subset_closure_of hp hζ F hF fun _ _ h =>
    hord (h.trans (Subgroup.card_subgroup_dvd_card _))

end CFSG.RankThree.PartOne.KE8F
