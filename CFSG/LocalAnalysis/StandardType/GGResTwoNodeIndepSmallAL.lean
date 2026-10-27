module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSide
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepAtLK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepAtThree
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPm1
public import CFSG.LocalAnalysis.StandardType.GGRCCycleBalanced
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeIndepAtL_smallA (hPos : LR6SmallRankPosB) (hExcl : LR6SmallRankExcl)
    (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p N : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hcell : lr6SmallCellA p N) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    (hmove : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    (hXd : GGResXDatumAIndep p Bs L (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs L J)
    (hYs : GGResSideDatum p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hb, hcardΛa,
    hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK, hfL, hfK, hclosL, hclosK, hconn, hJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_one ggWeylSimpleSystemsConjInput_holds hp2 hXs hYs
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  obtain ⟨fL, hfL⟩ := hfL
  obtain ⟨fK, hfK⟩ := hfK
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
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
  let αa : Module.Dual (ZMod p) V := α (Sum.inr a₀)
  let tt : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ (Sum.inr a₀))
  let xv : V := ι (Additive.ofMul ⟨x, hx⟩)
  obtain ⟨Λ₁, j1, j2, M₁, C₁, V₁, k1, k2, ι₁, φ₁, h₁, α₁, e₁, hM₁, hWM₁, hC₁, hlin₁, hrefl₁,
    hpair₁, ⟨f₁, hf₁⟩, hclos₁, hind₁⟩ := hXd
  letI := j1; letI := j2; letI := k1; letI := k2
  obtain ⟨e, hML⟩ := ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega) hH.1.2.1.2.1
    (ggAutomizer L Bs) e₁ hM₁ hWM₁ f₁ φ₁ hf₁ hrefl₁ hWML fL (fun i => φ (Sum.inl i))
    (fun i => hfL i) (fun i => hrefl (Sum.inl i))
  have hcard : Fintype.card Λ₁ = Fintype.card Λ :=
    calc Fintype.card Λ₁ = Fintype.card (Fin (N - 1)) := (Fintype.card_congr e₁).symm
      _ = Fintype.card Λ := Fintype.card_congr e
  have hindL : LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    ggDatum_indep_transfer (p := p) hlin₁ hrefl₁ (fun i w => hlin (Sum.inl i) w)
      (fun i => hrefl (Sum.inl i)) hclos₁ hclosL hcard hind₁
  have F : GGIndepAFrame p N (fun i : Fin (N - 1) => h (Sum.inl (e i)))
      (fun i => α (Sum.inl (e i))) xv :=
    ggXDatumA_indep_frame hFix hp2 hH hx hN5 hpN e hML hCL (fun i w => hlin (Sum.inl i) w)
      (fun i j => hpairL i j) hclosL hindL
  let h' : Fin (N - 1) → V := fun i => h (Sum.inl (e i))
  let α' : Fin (N - 1) → Module.Dual (ZMod p) V := fun i => α (Sum.inl (e i))
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))
  have hr : ∀ i v, r i v = v - α' i v • h' i := fun i v => hlin (Sum.inl (e i)) v
  have hαa' : α (Sum.inr a₀) (h (Sum.inr a₀)) = 2 := by
    have := hpairK (Sum.inr a₀) (Sum.inr a₀)
    rw [hCK.1] at this
    simpa using this
  have hαa : αa ha = 2 := hαa'
  have hform : ∀ v, tt v = v - αa v • ha := fun v => hlin (Sum.inr a₀) v
  have hfixr : Subgroup.closure (Set.range r) ≤ MulAction.stabilizer (V ≃ₗ[ZMod p] V) xv := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change r i ∈ MulAction.stabilizer (V ≃ₗ[ZMod p] V) xv
    rw [MulAction.mem_stabilizer_iff]
    change r i xv = xv
    rw [hr i, F.x_ker i, zero_smul, sub_zero]
  have hw : αa xv ≠ 0 := by
    intro h0
    have hStabK : (ggAutomizer K Bs).map (ggLin (p := p) ι) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) xv := by
      rw [hclosK, MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro y ⟨g, hg, rfl⟩
      rcases hg with ⟨j, rfl⟩ | ⟨a, rfl⟩
      · exact hfixr (Subgroup.subset_closure ⟨e.symm j.1, by simp [r]⟩)
      · have ha0 : a = a₀ := Subsingleton.elim a a₀
        rw [ha0]
        change tt ∈ MulAction.stabilizer (V ≃ₗ[ZMod p] V) xv
        rw [MulAction.mem_stabilizer_iff]
        change tt xv = xv
        rw [hform, h0, zero_smul, sub_zero]
    obtain ⟨t', ht'A, -, ht'move⟩ := hmove
    have hfix : ggLin (p := p) ι t' xv = xv := by
      have hmem : ggLin (p := p) ι t' ∈ MulAction.stabilizer (V ≃ₗ[ZMod p] V) xv :=
        hStabK (Subgroup.mem_map.mpr ⟨t', ht'A, rfl⟩)
      rwa [MulAction.mem_stabilizer_iff] at hmem
    exact ht'move ((ggLin_fix_iff (p := p) ι t' ⟨x, hx⟩).mpr hfix)
  have hnt0 : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
      ggLin (p := p) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := p) ι (φ (Sum.inr a₀))}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    ggIndep_nt (p := p) (N := N) (Bs := Bs)
      (A' := ggAutomizer L Bs ⊔ ggAutomizer K Bs) (e := e)
      (φ := fun i : Λ => φ (Sum.inl i)) (ι := ι)
      (hNT := hH.2.2.2.1) (hA' := hA)
      (hφ := fun i => hφsup i) (t := φ (Sum.inr a₀)) (ht := hφsupK a₀)
  have hnt : ∀ g ∈ lr6Group r tt,
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg
    exact hnt0 g hg
  have hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 :=
    ggJoint_coxeter_J_eq (Bs := Bs) (L := L) (K := K) (ML := ML) (MK := MK) (φ := φ)
      ⟨fL, hfL⟩ ⟨fK, hfK⟩
  obtain ⟨S, MK', CK', hSall, hSint, hWMK', hCK', hpairS, hattach, hfS⟩ :=
    ggJoint_oneNode_sideClause (p := p) (N := N) (Bs := Bs) (K := K) hb hcardΛa a₀ hN5
      e hML hconn hWMK hCK hJM hlin hpairK ⟨fK, hfK⟩ hclosK
  have hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs := by
    intro j
    rw [hclosL]
    exact Subgroup.subset_closure ⟨j.1, rfl⟩
  have hφtop : ∀ o : Λ ⊕ Λa, φ o ∈ ggAutomizer ⊤ Bs := by
    intro o
    have h1 : φ o ∈ Subgroup.closure (Set.range φ) := Subgroup.subset_closure ⟨o, rfl⟩
    rw [hgen] at h1
    exact hA h1
  have hαj : ∀ j : Λ, α (Sum.inl j) (h (Sum.inl j)) = 2 := by
    intro j
    rw [hpairL j j, hCL.1 j]
    norm_num
  have hmap0 : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) := by
    rw [← hgen, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hmap1 : Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) =
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
  have htri : 5 ≤ p → LR6JTriangleBalanced S h' α' r (lr6Group r tt) := by
    intro hp5 j hjS j' hjS' hjne ψ hψ ht αt hformψ hαt hnc
    have hj : e j ≠ b₁ ∧ e j ≠ b₂ := (hSall j).mp hjS
    have hj' : e j' ≠ b₁ ∧ e j' ≠ b₂ := (hSall j').mp hjS'
    have hψmap : ψ ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) := by
      rw [hmap]; exact hψ
    obtain ⟨ψ', hψ'A, hψ'eq⟩ := Subgroup.mem_map.mp hψmap
    have hψ'clos : ψ' ∈ Subgroup.closure (Set.range φ) := by rw [hgen]; exact hψ'A
    have htl : ∀ w, ggLin (p := p) ι (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) w = w - αt w • ht := by
      intro w
      have h1 : ggLin (p := p) ι (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) = ψ * r j * ψ⁻¹ := by
        rw [map_mul, map_mul, map_inv, hψ'eq]
      rw [h1]
      exact hformψ w
    have hnc' : ψ' * φ (Sum.inl (e j)) * ψ'⁻¹ * φ (Sum.inl (e j')) ≠
        φ (Sum.inl (e j')) * (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) := by
      intro heq
      apply hnc
      have := congrArg (ggLin (p := p) ι) heq
      simpa only [map_mul, map_inv, hψ'eq, r, tt] using this
    have hcyc := ggRC_cycleBalanced_two hJr hPump hLB hSP hp5 hH
        (hφ := hlin) (j := e j) (j' := e j') (hαj (e j)) (hαj (e j'))
        hφtop hJL hJ hj hj' hψ'clos hαt htl hnc'
    simpa only [h', α'] using hcyc
  have hsidePos : ∃ (S : Finset (Fin (N - 1))) (MK' : CoxeterMatrix (Option ↥S))
      (CK' : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧
      GGIsWeylMatrix MK' ∧ GGIntCartan MK' CK' ∧
      (∀ i j : Option ↥S, (CK' i j : ZMod p) =
        (i.elim αa fun a => α' a) (j.elim ha fun b => h' b)) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK' none (some j) ≠ 0 ↔ j = c) ∧
      (5 ≤ p → LR6JTriangleBalanced S h' α' r (lr6Group r tt)) ∧
      ∃ f : MK'.Group ≃* ↥(lr6Group (fun j : ↥S => r j) tt),
        ∀ o : Option ↥S, ((f (MK'.simple o) : V ≃ₗ[ZMod p] V)) = o.elim tt fun j => r j :=
    ⟨S, MK', CK', hSint, hWMK', hCK', hpairS, hattach, htri, hfS⟩
  have hVN : Module.finrank (ZMod p) V ≤ N := ggIndepFrame_finrank_le (by omega) F
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
  have hBs : Nat.card ↥Bs ≤ p ^ N := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hVN
  have hcardA1 : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N :=
    ggIndep_card_A1 (p := p) (N := N) hp2 hN5 hx ι (fun i w => hlin (Sum.inl i) w) hclosL e F
  have hcardR : Nat.card ↥(lr6Group r tt) =
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rw [← hmap]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs) (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv).symm
  have hcard : Nat.card ↥(lr6Group r tt) ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) := by
    rw [hcardR]
    calc Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)
        ≤ Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
          ggIndep_card_join_le (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⟨x, hx⟩
            (hOrb G p B Bs x L D J y K hH hx)
      _ ≤ p ^ N * ((p - 1) * 6 * Nat.factorial N) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = p ^ N * (6 * (p - 1) * Nat.factorial N) := by rw [Nat.mul_comm (p - 1) 6]
  by_cases hmem : ha ∈ Submodule.span (ZMod p) (Set.range h')
  · exfalso
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      let A : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range r ∪ {tt})
      have hrA : ∀ i, r i ∈ A := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
      have htA : tt ∈ A := Subgroup.subset_closure (Or.inr rfl)
      have hntA : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧
          ∀ w, g (g w - w) = g w - w) := by
        intro g hg
        exact hnt g hg
      have hcα := ggIndep_center_functional_vanish F.dvd F.pair hmem
      have hfix0 := ggIndep_p3_fixes_x h' α' (fun i => (((i : ℕ) + 1 : ℕ) : ZMod 3))
        F.pair A hntA r hr hrA tt htA ha αa hcα hform hαa
      obtain ⟨c, hc0, hxc⟩ := ggIndep_x_eq_smul_center F.dvd (by omega) F.pair F.indep F.fix
      apply hw
      rw [hxc, map_smul, hfix0, smul_zero]
    · have hcellE : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) := by
        rcases hcell with ⟨hp5, hN5⟩ | ⟨hp3', hN6⟩ | ⟨hp7, hN7⟩
        · exact Or.inl ⟨hp5, hN5⟩
        · exact absurd hp3' hp3
        · exact Or.inr ⟨hp7, hN7⟩
      have hp5 : 5 ≤ p := by
        rcases hcellE with ⟨hp5', -⟩ | ⟨hp7', -⟩ <;> omega
      have hsideExcl : ∃ (S : Finset (Fin (N - 1))) (MK' : CoxeterMatrix (Option ↥S))
          (CK' : Matrix (Option ↥S) (Option ↥S) ℤ),
          (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧
          GGIsWeylMatrix MK' ∧ GGIntCartan MK' CK' ∧
          (∀ i j : Option ↥S, (CK' i j : ZMod p) =
            (i.elim αa fun a => α' a) (j.elim ha fun b => h' b)) ∧
          (∃ c : ↥S, ∀ j : ↥S, CK' none (some j) ≠ 0 ↔ j = c) ∧
          LR6JTriangleBalanced S h' α' r (lr6ExclGroup r tt) ∧
          ∃ f : MK'.Group ≃* ↥(lr6ExclGroup (fun j : ↥S => r j) tt),
            ∀ o : Option ↥S, ((f (MK'.simple o) : V ≃ₗ[ZMod p] V)) = o.elim tt fun j => r j :=
        ⟨S, MK', CK', hSint, hWMK', hCK', hpairS, hattach, htri hp5, hfS⟩
      exact hExcl p N hcellE V hVN h' α' xv r ha αa tt F hr hform hαa hw hmem hsideExcl hnt
  · have hdimV : Module.finrank (ZMod p) V = N :=
      (ggIndepA_top hp2 hN5 F r hr tt ha αa hform hαa hw hnt hmem hVN).1
    have hLinWeyl : ZS.LinWeyl p (lr6Group r tt) :=
      hPos p N hcell V hdimV h' α' xv r ha αa tt F hr hform hαa hw hmem hsidePos hnt hcard
    exact ggRC_weylReflGroup_of_linWeyl ι (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
      (by simpa only [hmap] using hLinWeyl)

end CFSG.StandardType

end