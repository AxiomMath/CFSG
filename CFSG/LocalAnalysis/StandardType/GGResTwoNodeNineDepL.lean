module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSide
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallAL
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepDepTwin
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6nl_span_gen_le_image {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) ≤
      (ι '' (Additive.ofMul '' (ggBstarComm X Bs : Set ↥Bs)) : Set V) := by
  let H : Submodule (ZMod p) V :=
    { carrier := ι '' (Additive.ofMul '' (ggBstarComm X Bs : Set ↥Bs))
      zero_mem' := ⟨0, ⟨1, Subgroup.one_mem _, rfl⟩, by simp⟩
      add_mem' := by
        rintro u v ⟨du, hdu, rfl⟩ ⟨dv, hdv, rfl⟩
        obtain ⟨cu, hcu, rfl⟩ := hdu
        obtain ⟨cv, hcv, rfl⟩ := hdv
        exact ⟨Additive.ofMul (cu * cv), ⟨cu * cv, Subgroup.mul_mem _ hcu hcv, rfl⟩, by
          show ι (Additive.ofMul (cu * cv)) = ι (Additive.ofMul cu) + ι (Additive.ofMul cv)
          rw [← map_add, ← ofMul_mul]⟩
      smul_mem' := by
        rintro a u ⟨d, hd, rfl⟩
        obtain ⟨c, hc, rfl⟩ := hd
        refine ⟨Additive.ofMul (c ^ a.val), ⟨c ^ a.val, Subgroup.pow_mem _ hc a.val, rfl⟩, ?_⟩
        show ι (Additive.ofMul (c ^ a.val)) = a • ι (Additive.ofMul c)
        have h1 : a • ι (Additive.ofMul c) = (a.val : ℕ) • ι (Additive.ofMul c) := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [h1, ← map_nsmul, ofMul_pow] }
  intro v hv
  have hle : Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
      ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) ≤ H := by
    rw [Submodule.span_le]
    rintro v ⟨q, rfl⟩
    change ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2 ∈ (H : Set V)
    obtain ⟨b, hb⟩ := ι.surjective q.2
    have hb' : q.2 = ι (Additive.ofMul (Additive.toMul b)) := by
      rw [← hb]
      exact congrArg ι (ofMul_toMul b).symm
    rw [hb']
    refine ⟨Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b)),
      ⟨(Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b), ?_, rfl⟩, ?_⟩
    · exact Subgroup.subset_closure ⟨Additive.toMul b, q.1, q.1.2, rfl⟩
    · show ι (Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b))) =
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) (ι (Additive.ofMul (Additive.toMul b))) -
          ι (Additive.ofMul (Additive.toMul b))
      rw [ggLin_apply_ofMul]
      have hkeyV : ι (Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b))) =
          ι (Additive.ofMul ((q.1 : MulAut ↥Bs) (Additive.toMul b))) -
            ι (Additive.ofMul (Additive.toMul b)) := by
        rw [ofMul_mul, ofMul_inv, map_add, map_neg]
        abel
      exact hkeyV
  exact hle hv

theorem ggTwoNodeNineDepL_closer (hNine : LR6NineDepPos) (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    (hXd : GGResXDatumA p Bs L 8) (hnc : x ∉ (ggBstarComm L Bs).map Bs.subtype)
    (hXs : GGResTwoNodeSideDatum p Bs L J) (hYs : GGResSideDatum p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp3
  have hp2 : 3 ≠ 2 := by norm_num
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hb, hcardΛa,
    hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK, hfL, hfK, hclosL, hclosK, hconn, hJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_one ggWeylSimpleSystemsConjInput_holds hp2 hXs hYs
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  obtain ⟨fL, hfL⟩ := hfL
  obtain ⟨fK, hfK⟩ := hfK
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hφsup : ∀ i : Λ, φ (Sum.inl i) ∈
      ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun i =>
    Subgroup.mem_sup_left (by rw [hclosL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hφK : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer K Bs := fun a => by
    rw [hclosK]; exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  have hφsupK : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    fun a => Subgroup.mem_sup_right (hφK a)
  have hgen : Subgroup.closure (Set.range φ) = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | inl i => exact hφsup i
      | inr a => exact hφsupK a
    · apply sup_le
      · rw [hclosL]
        apply Subgroup.closure_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      · rw [hclosK, Subgroup.closure_le]
        rintro _ (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact Subgroup.subset_closure ⟨Sum.inl j, rfl⟩
        · exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  haveI : Subsingleton Λa := by
    rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]
    omega
  haveI : Nonempty Λa := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card]
    omega
  let a₀ : Λa := Classical.choice (inferInstance : Nonempty Λa)
  let ha : V := h (Sum.inr a₀)
  let αa : Module.Dual (ZMod 3) V := α (Sum.inr a₀)
  let tt : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (φ (Sum.inr a₀))
  let xv : V := ι (Additive.ofMul ⟨x, hx⟩)
  obtain ⟨Λ₁, j1, j2, M₁, C₁, V₁, k1, k2, ι₁, φ₁, h₁, α₁, e₁, hM₁, hWM₁, hC₁, hlin₁, hrefl₁,
    hpair₁, ⟨f₁, hf₁⟩, hclos₁⟩ := hXd
  letI := j1; letI := j2; letI := k1; letI := k2
  obtain ⟨e, hML⟩ := ggTW_typeA_of_datum (p := 3) (n := 8) hp2 (by omega) hH.1.2.1.2.1
    (ggAutomizer L Bs) e₁ hM₁ hWM₁ f₁ φ₁ hf₁ hrefl₁ hWML fL (fun i => φ (Sum.inl i))
    (fun i => hfL i) (fun i => hrefl (Sum.inl i))
  have hN5 : 5 ≤ 9 := by omega
  have hpN : 3 ∣ 9 := by norm_num
  have hdepL : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) := by
    intro hindL
    have Find := ggXDatumA_indep_frame hFix hp2 hH hx hN5 hpN e hML hCL
      (fun i w => hlin (Sum.inl i) w) (fun i j => hpairL i j) hclosL hindL
    have hrange : Set.range (fun i : Fin 8 => h (Sum.inl (e i))) =
        Set.range (fun i : Λ => h (Sum.inl i)) :=
      e.surjective.range_comp (fun i : Λ => h (Sum.inl i))
    have hxmem : xv ∈ Submodule.span (ZMod 3) (Set.range (fun i : Λ => h (Sum.inl i))) := by
      rw [← hrange]
      exact Find.x_mem
    have hspan := l6tr_span_eq (p := 3) (X := L) (Bs := Bs) (ι := ι)
      (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i))
      (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hclosL
    have hxgen : xv ∈ Submodule.span (ZMod 3) (Set.range (fun q : ↥(ggAutomizer L Bs) × V =>
        ggLin (p := 3) ι q.1 q.2 - q.2)) := by
      rw [← hspan]
      exact hxmem
    have hxH := l6nl_span_gen_le_image (p := 3) (X := L) (Bs := Bs) ι hxgen
    obtain ⟨d, hd, hdv⟩ := hxH
    obtain ⟨c, hc, rfl⟩ := hd
    apply hnc
    refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
    have h1 : ι (Additive.ofMul c) = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) := by
      rw [hdv]
    have h2 : Additive.ofMul c = Additive.ofMul (⟨x, hx⟩ : ↥Bs) := ι.injective h1
    exact congrArg Subtype.val (by simpa using h2)
  have Fdep : GGDepAFrame 3 9 (fun i : Fin 8 => h (Sum.inl (e i)))
      (fun i => α (Sum.inl (e i))) xv :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e hML hCL
      (fun i w => hlin (Sum.inl i) w) (fun i j => hpairL i j) hclosL hdepL
  let h' : Fin 8 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 8 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let r : Fin 8 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))
  have hr : ∀ i v, r i v = v - α' i v • h' i := fun i v => hlin (Sum.inl (e i)) v
  have hαa' : α (Sum.inr a₀) (h (Sum.inr a₀)) = 2 := by
    have := hpairK (Sum.inr a₀) (Sum.inr a₀)
    rw [hCK.1] at this
    simpa using this
  have hαa : αa ha = 2 := hαa'
  have hform : ∀ v, tt v = v - αa v • ha := fun v => hlin (Sum.inr a₀) v
  have hmove := ggIndep_moving_K hFixK hH hx
  have hfixr : Subgroup.closure (Set.range r) ≤ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change r i ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv
    rw [MulAction.mem_stabilizer_iff]
    change r i xv = xv
    rw [hr i, Fdep.x_ker i, zero_smul, sub_zero]
  have hw : αa xv ≠ 0 := by
    intro h0
    have hStabK : (ggAutomizer K Bs).map (ggLin (p := 3) ι) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv := by
      rw [hclosK, MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro y ⟨g, hg, rfl⟩
      rcases hg with ⟨j, rfl⟩ | ⟨a, rfl⟩
      · exact hfixr (Subgroup.subset_closure ⟨e.symm j.1, by simp [r]⟩)
      · have ha0 : a = a₀ := Subsingleton.elim a a₀
        rw [ha0]
        change tt ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv
        rw [MulAction.mem_stabilizer_iff]
        change tt xv = xv
        rw [hform, h0, zero_smul, sub_zero]
    obtain ⟨t', ht'A, -, ht'move⟩ := hmove
    have hfix : ggLin (p := 3) ι t' xv = xv := by
      have hmem : ggLin (p := 3) ι t' ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv :=
        hStabK (Subgroup.mem_map.mpr ⟨t', ht'A, rfl⟩)
      rwa [MulAction.mem_stabilizer_iff] at hmem
    exact ht'move ((ggLin_fix_iff (p := 3) ι t' ⟨x, hx⟩).mpr hfix)
  have hnt0 : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 8 =>
      ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := 3) ι (φ (Sum.inr a₀))}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    ggIndep_nt (p := 3) (N := 9) (Bs := Bs)
      (A' := ggAutomizer L Bs ⊔ ggAutomizer K Bs) (e := e)
      (φ := fun i : Λ => φ (Sum.inl i)) (ι := ι)
      (hNT := hH.2.2.2.1) (hA' := hA)
      (hφ := fun i => hφsup i) (t := φ (Sum.inr a₀)) (ht := hφsupK a₀)
  have hnt : ∀ g ∈ lr6Group r tt,
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg
    exact hnt0 g hg
  have hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 :=
    ggJoint_coxeter_J_eq (Bs := Bs) (L := L) (K := K) (ML := ML) (MK := MK) (φ := φ)
      ⟨fL, hfL⟩ ⟨fK, hfK⟩
  obtain ⟨S, MK', CK', hSall, hSint, hWMK', hCK', hpairS, hattach, hfS⟩ :=
    ggJoint_oneNode_sideClause (p := 3) (N := 9) (Bs := Bs) (K := K) hb hcardΛa a₀ hN5
      e hML hconn hWMK hCK hJM hlin hpairK ⟨fK, hfK⟩ hclosK
  have hside : ∃ (S : Finset (Fin 8)) (MK' : CoxeterMatrix (Option ↥S))
      (CK' : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∃ s ≤ 2, ∀ i : Fin 8, i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + 6) ∧
      GGIsWeylMatrix MK' ∧ GGIntCartan MK' CK' ∧
      (∀ i j : Option ↥S, (CK' i j : ZMod 3) =
        (i.elim αa fun a => α' a) (j.elim ha fun b => h' b)) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK' none (some j) ≠ 0 ↔ j = c) ∧
      ∃ f : MK'.Group ≃* ↥(lr6Group (fun j : ↥S => r j) tt),
        ∀ o : Option ↥S, ((f (MK'.simple o) : V ≃ₗ[ZMod 3] V)) = o.elim tt fun j => r j :=
    ⟨S, MK', CK', hSint, hWMK', hCK', hpairS, hattach, hfS⟩
  have hmap0 : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) := by
    rw [← hgen, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hmap1 : Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) =
      lr6Group r tt := by
    rw [lr6Group]
    congr 1
    ext yy
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl i => exact Or.inl ⟨e.symm i, by simp [r]⟩
      | inr a =>
        refine Or.inr ?_
        have ha0 : a = a₀ := Subsingleton.elim a a₀
        rw [ha0]
        simp [tt]
    · rintro (⟨i, rfl⟩ | hy)
      · exact ⟨Sum.inl (e i), rfl⟩
      · rw [Set.mem_singleton_iff] at hy
        exact ⟨Sum.inr a₀, by rw [hy]⟩
  have hmap := hmap0.trans hmap1
  have hVN : Module.finrank (ZMod 3) V ≤ 9 := (ggDepA_finrank_bounds Fdep).2
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hBs : Nat.card ↥Bs ≤ 3 ^ 9 := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hVN
  have hcardA1 : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial 9 := by
    have h1 : Nat.card ↥(ggAutomizer L Bs) = Nat.card ML.Group :=
      (Nat.card_congr fL.toEquiv).symm
    have h2 : Nat.card ML.Group = Nat.card (CoxeterMatrix.A 8).Group := by
      rw [hML]
      exact Nat.card_congr ((CoxeterMatrix.A 8).reindexGroupEquiv e).toEquiv
    have h3 : Nat.card (CoxeterMatrix.A 8).Group = Nat.factorial 9 := by
      rw [l05nK3a_card_coxeterA 8]
    rw [h1, h2, h3]
  have hcardR : Nat.card ↥(lr6Group r tt) =
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rw [← hmap]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs) (ggLin (p := 3) ι) (ggLin_injective ι)).toEquiv).symm
  have hcard : Nat.card ↥(lr6Group r tt) ≤ 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by
    rw [hcardR]
    calc Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)
        ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
          ggIndep_card_join_le (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⟨x, hx⟩
            (hOrb G 3 B Bs x L D J y K hH hx)
      _ ≤ 3 ^ 9 * ((3 - 1) * 6 * Nat.factorial 9) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by rw [Nat.mul_comm (3 - 1) 6]
  have hLinWeyl : ZS.LinWeyl 3 (lr6Group r tt) :=
    hNine V hVN h' α' xv r ha αa tt Fdep hr hform hαa hw hside hnt hcard
  exact ggRC_weylReflGroup_of_linWeyl ι (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (by simpa only [hmap] using hLinWeyl)

end CFSG.StandardType

end
