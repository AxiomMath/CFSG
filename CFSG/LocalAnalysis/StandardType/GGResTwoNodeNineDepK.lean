module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeNineDepKAux
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSide
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallAK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepDepTwin
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGDepAOdd
public import CFSG.LocalAnalysis.StandardType.GGRowKFrameDim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeNineDepK_closer (hNine : LR6NineDepPos) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) (hXd : GGResXDatumA p Bs K 8)
    (hnc : y ∉ (ggBstarComm K Bs).map Bs.subtype) (hXs : GGResTwoNodeSideDatum p Bs K J)
    (hYs : GGResSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hx : x ∈ Bs :=
    hH.1.2.1.1 (hH.1.2.2.1.1 (hH.1.2.2.1.2.2.2.1))
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hb, hcardΛa,
    hWML, hCL, hWMK, hCK, hlin, hrefl, hpairK, hpairL, hfK, hfL, hclosK, hclosL, hconn, hJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_one ggWeylSimpleSystemsConjInput_holds hp2 hXs hYs
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  obtain ⟨fK, hfK⟩ := hfK
  obtain ⟨fL, hfL⟩ := hfL
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hφsup : ∀ i : Λ, φ (Sum.inl i) ∈ ggAutomizer K Bs ⊔ ggAutomizer L Bs := fun i =>
    Subgroup.mem_sup_left (by rw [hclosK]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hφsupL : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer K Bs ⊔ ggAutomizer L Bs := fun a =>
    Subgroup.mem_sup_right (by rw [hclosL]; exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩))
  have hgen : Subgroup.closure (Set.range φ) = ggAutomizer K Bs ⊔ ggAutomizer L Bs := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | inl i => exact hφsup i
      | inr a => exact hφsupL a
    · apply sup_le
      · rw [hclosK]
        apply Subgroup.closure_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      · rw [hclosL, Subgroup.closure_le]
        rintro _ (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact Subgroup.subset_closure ⟨Sum.inl j, rfl⟩
        · exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
  have hA : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
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
  let yv : V := ι (Additive.ofMul ⟨y, hy⟩)
  obtain ⟨Λ₁, j1, j2, M₁, C₁, V₁, k1, k2, ι₁, φ₁, h₁, α₁, e₁, hM₁, hWM₁, hC₁, hlin₁, hrefl₁,
    hpair₁, ⟨f₁, hf₁⟩, hclos₁⟩ := hXd
  letI := j1; letI := j2; letI := k1; letI := k2
  obtain ⟨e, hML⟩ := ggTW_typeA_of_datum (p := 3) (n := 8) hp2 (by norm_num) hH.1.2.1.2.1
    (ggAutomizer K Bs) e₁ hM₁ hWM₁ f₁ φ₁ hf₁ hrefl₁ hWML fK (fun i => φ (Sum.inl i))
    (fun i => hfK i) (fun i => hrefl (Sum.inl i))
  have hcardΛ : Fintype.card Λ = 8 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  let hK : Fin 8 → V := fun i => h (Sum.inl (e i))
  let αK : Fin 8 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  have hpairK' : ∀ i j, αK i (hK j) = (CartanMatrix.A 8 i j : ZMod 3) := by
    intro i j
    rw [hpairK (e i) (e j), ggIndep_cartan_of_reindex e hCL hML i j]
  let hL : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → V := fun o => h (o.map Subtype.val id)
  let αL : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → Module.Dual (ZMod 3) V :=
    fun o => α (o.map Subtype.val id)
  let φL : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → MulAut ↥Bs :=
    fun o => φ (o.map Subtype.val id)
  have hφL : ∀ o w, ggLin (p := 3) ι (φL o) w = w - αL o w • hL o := fun o => hlin _
  have hclosL' : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact Subgroup.subset_closure ⟨Sum.inl j, rfl⟩
      · exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      rcases o with j | a
      · exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  have hfixL : ∀ v : V, (∀ o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa, αL o v = 0) →
      v ∈ Submodule.span (ZMod 3) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) :=
    ggIndep_fixL hFix hH hx hφL hclosL'
  have hcardJ : Fintype.card {i : Λ // i ≠ b₁ ∧ i ≠ b₂} = 6 := by
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun i : Λ => i ≠ b₁ ∧ i ≠ b₂)) =
        (Finset.univ.erase b₁).erase b₂ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    have hmem1 : b₁ ∈ (Finset.univ : Finset Λ) := Finset.mem_univ _
    have hmem2 : b₂ ∈ (Finset.univ : Finset Λ).erase b₁ := by
      rw [Finset.mem_erase]
      exact ⟨hb.symm, Finset.mem_univ _⟩
    rw [hfilter, Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1,
      Finset.card_univ, hcardΛ]
  have hcardL : Fintype.card ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) = 7 := by
    rw [Fintype.card_sum, hcardJ, ← Nat.card_eq_fintype_card, hcardΛa]
  have hV_le : Module.finrank (ZMod 3) V ≤ 8 := by
    let Ψ : V →ₗ[ZMod 3] (({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → ZMod 3) := LinearMap.pi αL
    have hker_le : Ψ.ker ≤ Submodule.span (ZMod 3) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) := by
      intro v hv
      rw [LinearMap.mem_ker] at hv
      exact hfixL v (fun o => congrFun hv o)
    have hspan_le : Module.finrank (ZMod 3)
        ↥(Submodule.span (ZMod 3) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V)) ≤ 1 := by
      rcases eq_or_ne (ι (Additive.ofMul ⟨x, hx⟩)) 0 with h0 | h0
      · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl]
        simp
      · rw [finrank_span_singleton h0]
    have hkerfin : Module.finrank (ZMod 3) ↥Ψ.ker ≤ 1 :=
      le_trans (Submodule.finrank_mono hker_le) hspan_le
    have hrange_le : Module.finrank (ZMod 3) ↥Ψ.range ≤ 7 := by
      calc Module.finrank (ZMod 3) ↥Ψ.range
          ≤ Module.finrank (ZMod 3) (({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → ZMod 3) :=
            Submodule.finrank_le Ψ.range
        _ = Fintype.card ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) :=
            Module.finrank_fintype_fun_eq_card (ZMod 3)
        _ = 7 := hcardL
    have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
    omega
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := by
    haveI : IsMulCommutative ↥Bs := hH.1.2.1.2.1.1
    exact fun a b => Subtype.ext (setLike_mul_comm (s := Bs) a.2 b.2)
  have hclosK' : ggAutomizer K Bs = Subgroup.closure (Set.range (fun i : Fin 8 =>
      φ (Sum.inl (e i)))) := by
    rw [hclosK]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨e.symm i, by simp⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨e i, rfl⟩
  have hspan_le_comm : Submodule.span (ZMod 3) (Set.range hK) ≤
      Submodule.span (ZMod 3) (Set.range (fun c : ↥(ggBstarComm K Bs) =>
        ι (Additive.ofMul (c : ↥Bs)))) :=
    l6nk_span_le_image_comm (p := 3) hcomm (fun i w => hlin (Sum.inl (e i)) w)
      (fun i => hrefl (Sum.inl (e i))) hclosK'
  have hy_span : yv ∉ Submodule.span (ZMod 3) (Set.range hK) := by
    intro hmem
    have hmem' := hspan_le_comm hmem
    obtain ⟨c, hceq⟩ := l6nk_mem_image_comm (X := K) hmem'
    apply hnc
    refine Subgroup.mem_map.mpr ⟨c, c.2, ?_⟩
    have h1 : Additive.ofMul (c : ↥Bs) = Additive.ofMul ⟨y, hy⟩ := ι.injective hceq
    have h2 : (c : ↥Bs) = ⟨y, hy⟩ := Additive.ofMul.injective h1
    exact congrArg Subtype.val h2
  have hdepK : ¬ LinearIndependent (ZMod 3) hK := by
    intro hind
    have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range hK)) = 8 := by
      rw [finrank_span_eq_card hind, Fintype.card_fin]
    have hV_ge : 8 ≤ Module.finrank (ZMod 3) V := by
      rw [← hfin]; exact Submodule.finrank_le _
    have hV_eq : Module.finrank (ZMod 3) V = 8 := le_antisymm hV_le hV_ge
    have htop : Submodule.span (ZMod 3) (Set.range hK) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hfin, hV_eq])
    exact hy_span (by rw [htop]; exact Submodule.mem_top)
  have hdepΛ : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) := fun hli =>
    hdepK ((linearIndependent_equiv (R := ZMod 3) e).mpr hli)
  have hspanfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range hK)) = 7 :=
    l6nk_span_finrank (p := 3) (N := 9) (by norm_num) hpairK' hdepK
  have hyv_ne : yv ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := ι.injective (by simpa [yv] using h0)
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact ggRC_y_ne_one hH (by simpa using congrArg Subtype.val h2)
  have hspan1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({yv} : Set V)) = 1 :=
    finrank_span_singleton hyv_ne
  have hinf : Submodule.span (ZMod 3) (Set.range hK) ⊓
      Submodule.span (ZMod 3) ({yv} : Set V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hv
    obtain ⟨hv1, a, ha⟩ := hv
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha; exact ha.symm
    · exfalso
      apply hy_span
      have : yv = a⁻¹ • v := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hv1
  have hV_eq : Module.finrank (ZMod 3) V = 8 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod 3) (Set.range hK)) (Submodule.span (ZMod 3) ({yv} : Set V))
    rw [hinf] at h
    rw [hspanfin, hspan1, finrank_bot, add_zero] at h
    have hle := Submodule.finrank_mono (show Submodule.span (ZMod 3) (Set.range hK) ⊔
        Submodule.span (ZMod 3) ({yv} : Set V) ≤ ⊤ from le_top)
    rw [finrank_top] at hle
    omega
  have hN5 : 5 ≤ 9 := by norm_num
  have hpN : 3 ∣ 9 := by norm_num
  let h' : Fin 8 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 8 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let r : Fin 8 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))
  have F : GGDepAFrame 3 9 h' α' yv :=
    ggXDatumA_frame_K_dim (p := 3) (N := 9) hp2 hH hy hN5 hpN e hML hCL
      (fun i w => hlin (Sum.inl i) w) (fun i j => hpairK i j) hclosK hdepΛ hV_eq
  have hr : ∀ i v, r i v = v - α' i v • h' i := fun i v => hlin (Sum.inl (e i)) v
  have hLrefl : GGReflGenerated 3 (ggAutomizer L Bs) := l6a_reflGen_of_side (Or.inl hYs)
  have hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection 3 t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩ :=
    ggIndep_moving_L hFix hH hy hLrefl
  have hαa : αa ha = 2 := by
    have hh := hpairL (Sum.inr a₀) (Sum.inr a₀)
    rw [hCK.1] at hh
    simpa using hh
  have hform : ∀ v, tt v = v - αa v • ha := fun v => hlin (Sum.inr a₀) v
  have hfixr : Subgroup.closure (Set.range r) ≤ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change r i ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv
    rw [MulAction.mem_stabilizer_iff]
    change r i yv = yv
    rw [hr i, F.x_ker i, zero_smul, sub_zero]
  have hw : αa yv ≠ 0 := by
    intro h0
    have hStabL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv := by
      rw [hclosL, MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro z ⟨g, hg, rfl⟩
      rcases hg with ⟨j, rfl⟩ | ⟨a, rfl⟩
      · exact hfixr (Subgroup.subset_closure ⟨e.symm j.1, by simp [r]⟩)
      · have ha0 : a = a₀ := Subsingleton.elim a a₀
        rw [ha0]
        change tt ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv
        rw [MulAction.mem_stabilizer_iff]
        change tt yv = yv
        rw [hform, h0, zero_smul, sub_zero]
    obtain ⟨t', ht'L, -, ht'move⟩ := hmove
    have hfix : ggLin (p := 3) ι t' yv = yv := by
      have hmem : ggLin (p := 3) ι t' ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv :=
        hStabL (Subgroup.mem_map.mpr ⟨t', ht'L, rfl⟩)
      rwa [MulAction.mem_stabilizer_iff] at hmem
    exact ht'move ((ggLin_fix_iff (p := 3) ι t' ⟨y, hy⟩).mpr hfix)
  have hnt0 : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 8 =>
      ggLin (p := 3) ι (φ (Sum.inl (e i)))) ∪ {ggLin (p := 3) ι (φ (Sum.inr a₀))}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    ggIndep_nt (p := 3) (N := 9) (Bs := Bs)
      (A' := ggAutomizer K Bs ⊔ ggAutomizer L Bs) (e := e)
      (φ := fun i : Λ => φ (Sum.inl i)) (ι := ι)
      (hNT := hH.2.2.2.1) (hA' := hA)
      (hφ := fun i => hφsup i) (t := φ (Sum.inr a₀)) (ht := hφsupL a₀)
  have hnt : ∀ g ∈ lr6Group r tt,
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg
    exact hnt0 g hg
  have hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 :=
    ggJoint_coxeter_J_eq (Bs := Bs) (L := K) (K := L) (ML := ML) (MK := MK) (φ := φ)
      ⟨fK, hfK⟩ ⟨fL, hfL⟩
  obtain ⟨S, MK', CK', hSall, hSint, hWMK', hCK', hpairS, hattach, hfS⟩ :=
    ggJoint_oneNode_sideClause (p := 3) (N := 9) (Bs := Bs) (K := L) hb hcardΛa a₀ hN5
      e hML hconn hWMK hCK hJM hlin hpairL ⟨fL, hfL⟩ hclosL
  have hcardA : Nat.card ↥(ggAutomizer K Bs) ≤ Nat.factorial 9 :=
    l6nk_card_frame (p := 3) (N := 9) hp2 hN5 hy ι (fun o w => hlin (Sum.inl o) w) hclosK e F
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hBs : Nat.card ↥Bs ≤ 3 ^ 9 := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 3) (by omega)
  have hstab : Nat.card ↥((ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
    rw [sup_comm]
    exact hOrbK G 3 B Bs x L D J y K hH hy
  have hmap0 : (ggAutomizer K Bs ⊔ ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) := by
    rw [← hgen, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hmap1 : Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := 3) ι (φ o)) =
      lr6Group r tt := by
    rw [lr6Group]
    congr 1
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl i => exact Or.inl ⟨e.symm i, by simp [r]⟩
      | inr a =>
        refine Or.inr ?_
        have ha0 : a = a₀ := Subsingleton.elim a a₀
        rw [ha0]; simp [tt]
    · rintro (⟨i, rfl⟩ | hz)
      · exact ⟨Sum.inl (e i), rfl⟩
      · rw [Set.mem_singleton_iff] at hz
        exact ⟨Sum.inr a₀, by rw [hz]⟩
  have hmap := hmap0.trans hmap1
  have hcardR : Nat.card ↥(lr6Group r tt) =
      Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
    rw [← hmap]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (ggAutomizer K Bs ⊔ ggAutomizer L Bs) (ggLin (p := 3) ι)
      (ggLin_injective ι)).toEquiv).symm
  have hcard : Nat.card ↥(lr6Group r tt) ≤ 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by
    rw [hcardR]
    calc Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs)
        ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) :=
          ggIndep_card_join_le (ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⟨y, hy⟩ hstab
      _ ≤ 3 ^ 9 * ((3 - 1) * 6 * Nat.factorial 9) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA)
      _ = 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by rw [Nat.mul_comm (3 - 1) 6]
  have hV9 : Module.finrank (ZMod 3) V ≤ 9 := by omega
  have hLinWeyl : ZS.LinWeyl 3 (lr6Group r tt) :=
    hNine V hV9 h' α' yv r ha αa tt F hr hform hαa hw
      ⟨S, MK', CK', hSint, hWMK', hCK', hpairS, hattach, hfS⟩ hnt hcard
  exact ggRC_weylReflGroup_of_linWeyl ι (ggAutomizer K Bs ⊔ ggAutomizer L Bs)
    (by simpa only [hmap] using hLinWeyl)

end CFSG.StandardType

end
