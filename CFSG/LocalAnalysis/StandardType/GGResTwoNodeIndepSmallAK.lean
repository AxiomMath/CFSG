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

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeIndepAtK_smallA (hPos : LR6SmallRankPosB) (hExcl : LR6SmallRankExcl)
    (hOrbK : GGResCentBoundNbrInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p N : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hcell : lr6SmallCellA p N) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩)
    (hXd : GGResXDatumAIndep p Bs K (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs K J)
    (hYs : GGResSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
  classical
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  obtain ⟨Λ, iΛf, iΛd, b₁, b₂, Λa, iΛaf, iΛad, ML, CL, MK, CK, V, iVadd, iVmod, ι, φ, h, α,
    hb, hΛa, hWML, hCLL, hWMK, hCK, hφ, hrefl, hpairLL, hpairCK, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hclosL, hclosK, hdel, hJ'⟩ :=
    ggResTwoNodeDatum_of_sides_card_one ggWeylSimpleSystemsConjInput_holds hp2 hXs hYs
  letI := iΛf
  letI := iΛd
  letI := iΛaf
  letI := iΛad
  letI := iVadd
  letI := iVmod
  obtain ⟨Λ₁, iΛ₁f, iΛ₁d, M₁, C₁, V₁, iV₁add, iV₁mod, ι₁, φ₁, h₁, α₁, e₁, hM₁, hWM₁, hC₁,
    hφ₁, hrefl₁, hpair₁, ⟨f₁, hf₁⟩, hclos₁, hind₁⟩ := hXd
  letI := iΛ₁f
  letI := iΛ₁d
  letI := iV₁add
  letI := iV₁mod
  obtain ⟨e, hML⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega) hBs (ggAutomizer K Bs) e₁ hM₁
      hWM₁ f₁ φ₁ hf₁ hrefl₁ hWML fL (fun i => φ (Sum.inl i)) (fun i => hfL i)
      (fun i => hrefl (Sum.inl i))
  have hcard₁ : Fintype.card Λ₁ = Fintype.card Λ := by
    rw [← Fintype.card_congr e₁, ← Fintype.card_congr e]
  have hind : LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    ggDatum_indep_transfer (p := p) (X := K) hφ₁ hrefl₁ (fun i w => hφ (Sum.inl i) w)
      (fun i => hrefl (Sum.inl i)) hclos₁ hclosL hcard₁ hind₁
  have hframe : GGIndepAFrame p N (fun i : Fin (N - 1) => h (Sum.inl (e i)))
      (fun i : Fin (N - 1) => α (Sum.inl (e i))) (ι (Additive.ofMul ⟨y, hy⟩)) :=
    ggXDatumA_indep_frame_K (p := p) hp2 hH hy hstrong hN5 hpN e hML hCLL
      (fun i w => hφ (Sum.inl i) w) hpairLL hclosL hind
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcard1 : Fintype.card Λa = 1 := by simpa using hΛa
  obtain ⟨a₀, ha₀⟩ := Fintype.card_eq_one_iff.mp hcard1
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))
  let t : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ (Sum.inr a₀))
  let hl : Fin (N - 1) → V := fun i => h (Sum.inl (e i))
  let al : Fin (N - 1) → Module.Dual (ZMod p) V := fun i => α (Sum.inl (e i))
  let xv : V := ι (Additive.ofMul ⟨y, hy⟩)
  let ha : V := h (Sum.inr a₀)
  let αa : Module.Dual (ZMod p) V := α (Sum.inr a₀)
  have hαa : αa ha = 2 := by
    have h1 : α (Sum.inr a₀) (h (Sum.inr a₀)) = (CK (Sum.inr a₀) (Sum.inr a₀) : ZMod p) := by
      simpa using hpairCK (Sum.inr a₀) (Sum.inr a₀)
    dsimp only [αa, ha]
    rw [h1, hCK.1]
    norm_num
  have ht_form : ∀ v, t v = v - αa v • ha := by
    intro v
    dsimp only [t, αa, ha]
    exact hφ (Sum.inr a₀) v
  have hr : ∀ (i : Fin (N - 1)) (v : V), r i v = v - al i v • hl i := by
    intro i v
    dsimp only [r, al, hl]
    exact hφ (Sum.inl (e i)) v
  have ht_moves : φ (Sum.inr a₀) ⟨y, hy⟩ ≠ ⟨y, hy⟩ := by
    intro hfix
    have hfix_all : ∀ o : Λ ⊕ Λa, φ o ⟨y, hy⟩ = ⟨y, hy⟩ := by
      intro o
      cases o with
      | inl i =>
          have h0 : α (Sum.inl i) xv = 0 := by
            have h1 := hframe.x_ker (e.symm i)
            simpa [xv, e.apply_symm_apply] using h1
          have hlin : ggLin (p := p) ι (φ (Sum.inl i)) xv = xv := by
            rw [hφ (Sum.inl i), h0, zero_smul, sub_zero]
          exact (ggLin_fix_iff (p := p) ι (φ (Sum.inl i)) ⟨y, hy⟩).mpr hlin
      | inr a =>
          rw [ha₀ a]
          exact hfix
    obtain ⟨t', ht'A, -, ht'move⟩ := hmove
    have h1 : t' ∈ Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) := by
      rw [hclosK] at ht'A
      exact ht'A
    have ht'gen : t' ∈ Subgroup.closure (Set.range φ) := by
      apply Subgroup.closure_mono _ h1
      intro x hx
      simp only [Set.mem_union, Set.mem_range] at hx ⊢
      rcases hx with ⟨j, hj⟩ | ⟨a, ha'⟩
      · exact ⟨Sum.inl j, hj⟩
      · exact ⟨Sum.inr a, ha'⟩
    have hle : Subgroup.closure (Set.range φ) ≤
        MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      simpa using hfix_all o
    exact ht'move (by simpa using hle ht'gen)
  have hw : αa xv ≠ 0 := by
    intro h0
    apply ht_moves
    have hlin : t xv = xv := by
      rw [ht_form, h0, zero_smul, sub_zero]
    exact (ggLin_fix_iff (p := p) ι (φ (Sum.inr a₀)) ⟨y, hy⟩).mpr
      (by simpa [t, xv] using hlin)
  have hφX : ∀ i : Λ, φ (Sum.inl i) ∈ ggAutomizer K Bs := fun i => by
    rw [hclosL]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hφY : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer L Bs := fun a => by
    rw [hclosK]
    exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  have hgen : Subgroup.closure (Set.range φ) = ggAutomizer K Bs ⊔ ggAutomizer L Bs := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | inl i => exact Subgroup.mem_sup_left (hφX i)
      | inr a => exact Subgroup.mem_sup_right (hφY a)
    · apply sup_le
      · rw [hclosL]
        apply Subgroup.closure_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      · rw [hclosK, Subgroup.closure_le]
        rintro _ (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact Subgroup.subset_closure ⟨Sum.inl j, rfl⟩
        · exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
  have hmap_gen : (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι) = lr6Group r t := by
    rw [MonoidHom.map_closure]
    show Subgroup.closure ((ggLin (p := p) ι) '' Set.range φ) =
      Subgroup.closure (Set.range r ∪ {t})
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨o, rfl⟩, rfl⟩
      cases o with
      | inl i =>
          exact Or.inl ⟨e.symm i, by dsimp only [r]; rw [e.apply_symm_apply]⟩
      | inr a =>
          rw [ha₀ a]
          exact Or.inr rfl
    · rintro (⟨k, rfl⟩ | hx)
      · exact ⟨φ (Sum.inl (e k)), ⟨Sum.inl (e k), rfl⟩, by dsimp only [r]⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨φ (Sum.inr a₀), ⟨Sum.inr a₀, rfl⟩, by dsimp only [t]⟩
  have hmapAX : (ggAutomizer K Bs ⊔ ggAutomizer L Bs).map (ggLin (p := p) ι) = lr6Group r t := by
    rw [← hgen, hmap_gen]
  have hnt : ∀ g ∈ lr6Group r t,
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    have hA' : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
    have hφmem : ∀ i : Λ, φ (Sum.inl i) ∈ ggAutomizer K Bs ⊔ ggAutomizer L Bs :=
      fun i => Subgroup.mem_sup_left (hφX i)
    have htmem : φ (Sum.inr a₀) ∈ ggAutomizer K Bs ⊔ ggAutomizer L Bs :=
      Subgroup.mem_sup_right (hφY a₀)
    have hntA := ggIndep_nt (p := p) (N := N) (V := V) (ι := ι)
      (φ := fun i : Λ => φ (Sum.inl i)) hH.2.2.2.1 hA' e hφmem htmem
    simpa [lr6Group, r, t] using hntA
  have hdimle : Module.finrank (ZMod p) V ≤ N := ggIndepFrame_finrank_le (by omega) hframe
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
  have hBs_le : Nat.card ↥Bs ≤ p ^ N := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdimle
  have hstab : Nat.card ↥((ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
    rw [sup_comm]
    exact hOrbK G p B Bs x L D J y K hH hy
  have hjoin := ggIndep_card_join_le (ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⟨y, hy⟩ hstab
  have hA1 := ggIndep_card_A1 (p := p) (N := N) hp2 (by omega) hy ι
    (fun i w => hφ (Sum.inl i) w) hclosL e hframe
  have horder : Nat.card ↥(lr6Group r t) ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) := by
    have hcard_eq : Nat.card ↥(lr6Group r t) =
        Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
      rw [← hmapAX]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective
        (ggAutomizer K Bs ⊔ ggAutomizer L Bs) (ggLin (p := p) ι)
        (ggLin_injective ι)).toEquiv).symm
    rw [hcard_eq]
    calc Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs)
        ≤ Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) := hjoin
      _ ≤ p ^ N * ((p - 1) * 6 * Nat.factorial N) :=
          Nat.mul_le_mul hBs_le (Nat.mul_le_mul_left _ hA1)
      _ = p ^ N * (6 * (p - 1) * Nat.factorial N) := by ring
  have hjmeq : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 :=
    ggJoint_coxeter_J_eq ⟨fL, hfL⟩ ⟨fK, hfK⟩
  obtain ⟨S, MK', CK', hS, hSint, hWMK', hCK', hpair', hjoin', hiso'⟩ :=
    ggJoint_oneNode_sideClause (p := p) (N := N) (Bs := Bs) (K := L) hb hΛa a₀ hN5 e hML hdel
      hWMK hCK hjmeq (fun o w => hφ o w) hpairCK ⟨fK, hfK⟩ hclosK
  have htri : 5 ≤ p → LR6JTriangleBalanced S hl al r (lr6Group r t) := by
    intro hp5 j hj j' hj' hne ψ hψ ht αt hlin_form hαt hnc
    have hj_ne : e j ≠ b₁ ∧ e j ≠ b₂ := (hS j).mp hj
    have hj'_ne : e j' ≠ b₁ ∧ e j' ≠ b₂ := (hS j').mp hj'
    rw [← hmap_gen] at hψ
    obtain ⟨ψ', hψ'gen, hψ'eq⟩ := Subgroup.mem_map.mp hψ
    have hαj : α (Sum.inl (e j)) (h (Sum.inl (e j))) = 2 := by
      rw [hpairLL (e j) (e j), hCLL.1]
      norm_num
    have hαj' : α (Sum.inl (e j')) (h (Sum.inl (e j'))) = 2 := by
      rw [hpairLL (e j') (e j'), hCLL.1]
      norm_num
    have hφtop : ∀ o : Λ ⊕ Λa, φ o ∈ ggAutomizer ⊤ Bs := by
      intro o
      cases o with
      | inl i => exact ggAutomizer_mono Bs le_top (hφX i)
      | inr a => exact ggAutomizer_mono Bs le_top (hφY a)
    have hJL : ∀ jj : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl jj) ∈ ggAutomizer L Bs := by
      intro jj
      rw [hclosK]
      exact Subgroup.subset_closure (Or.inl ⟨jj, rfl⟩)
    have hkey : ∀ w, ggLin (p := p) ι (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) w = w - αt w • ht := by
      intro w
      have h1 : ggLin (p := p) ι (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) = ψ * r j * ψ⁻¹ := by
        dsimp only [r]
        rw [map_mul, map_mul, map_inv, hψ'eq]
      rw [h1]
      exact hlin_form w
    have hnc' : ψ' * φ (Sum.inl (e j)) * ψ'⁻¹ * φ (Sum.inl (e j')) ≠
        φ (Sum.inl (e j')) * (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) := by
      intro hcon
      apply hnc
      have h2 := congrArg (ggLin (p := p) ι) hcon
      dsimp only [r] at h2 ⊢
      simpa only [map_mul, map_inv, hψ'eq] using h2
    exact ggRC_cycleBalanced_two hJr hPump hLB hSP hp5 hH hφ hαj hαj' hφtop hJL hJ'
      hj_ne hj'_ne hψ'gen hαt hkey hnc'
  have hside : ∃ (S : Finset (Fin (N - 1))) (MK' : CoxeterMatrix (Option ↥S))
      (CK' : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧
      GGIsWeylMatrix MK' ∧ GGIntCartan MK' CK' ∧
      (∀ i j : Option ↥S, (CK' i j : ZMod p) =
        (i.elim αa fun a => al a) (j.elim ha fun b => hl b)) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK' none (some j) ≠ 0 ↔ j = c) ∧
      (5 ≤ p → LR6JTriangleBalanced S hl al r (lr6Group r t)) ∧
      ∃ f : MK'.Group ≃* ↥(lr6Group (fun j : ↥S => r j) t),
        ∀ o : Option ↥S, ((f (MK'.simple o) : V ≃ₗ[ZMod p] V)) = o.elim t fun j => r j :=
    ⟨S, MK', CK', hSint, hWMK', hCK', hpair', hjoin', htri, hiso'⟩
  by_cases hmem : ha ∈ Submodule.span (ZMod p) (Set.range hl)
  · rcases hcell with ⟨hp5, hN5'⟩ | ⟨hp3, hN6⟩ | ⟨hp7, hN7⟩
    · exact (hExcl p N (Or.inl ⟨hp5, hN5'⟩) V hdimle hl al xv r ha αa t hframe hr ht_form hαa
        hw hmem
        ⟨S, MK', CK', hSint, hWMK', hCK', hpair', hjoin',
          by simpa [lr6ExclGroup] using htri (by omega),
          by exact hiso'⟩ hnt).elim
    · exfalso
      subst hp3
      have hntA : ∀ g ∈ Subgroup.closure (Set.range r ∪ {t}),
          ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧
              ∀ w, g (g w - w) = g w - w) := by
        simpa [lr6Group] using hnt
      have hcα := ggIndep_center_functional_vanish (p := 3) (N := N) hpN hframe.pair hmem
      have hfix0 := ggIndep_p3_fixes_x hl al (fun i => (((i : ℕ) + 1 : ℕ) : ZMod 3))
        hframe.pair (Subgroup.closure (Set.range r ∪ {t})) hntA r hr
        (fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)) t
        (Subgroup.subset_closure (Or.inr rfl)) ha αa hcα ht_form hαa
      obtain ⟨c, hc0, hxc⟩ :=
        ggIndep_x_eq_smul_center (p := 3) (N := N) hpN (by omega) hframe.pair hframe.indep
          hframe.fix
      apply hw
      dsimp only [xv]
      rw [hxc, map_smul, hfix0, smul_zero]
    · exact (hExcl p N (Or.inr ⟨hp7, hN7⟩) V hdimle hl al xv r ha αa t hframe hr ht_form hαa
        hw hmem
        ⟨S, MK', CK', hSint, hWMK', hCK', hpair', hjoin',
          by simpa [lr6ExclGroup] using htri (by omega),
          by exact hiso'⟩ hnt).elim
  · have htop := ggIndepA_top (p := p) hp2 hN5 hframe r hr t ha αa ht_form hαa hw hnt hmem hdimle
    have hdimV : Module.finrank (ZMod p) V = N := htop.1
    have hW := hPos p N hcell V hdimV hl al xv r ha αa t hframe hr ht_form hαa hw hmem hside
      hnt horder
    have hW' : ZS.LinWeyl p ((ggAutomizer K Bs ⊔ ggAutomizer L Bs).map (ggLin (p := p) ι)) := by
      rw [← hgen, hmap_gen]
      exact hW
    exact ggRC_weylReflGroup_of_linWeyl ι (ggAutomizer K Bs ⊔ ggAutomizer L Bs) hW'

end CFSG.StandardType

end
