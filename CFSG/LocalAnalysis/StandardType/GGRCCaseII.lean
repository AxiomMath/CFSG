module

public import CFSG.LocalAnalysis.StandardType.GGRCCaseI
public import CFSG.LocalAnalysis.StandardType.GGRCFixedVector
public import CFSG.LocalAnalysis.StandardType.GGRCCardMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCardGe
public import CFSG.LocalAnalysis.StandardType.GGRCWeylOfPerm
public import CFSG.LocalAnalysis.StandardType.GGRCClassify
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGRCRestrict
public import CFSG.LocalAnalysis.StandardType.GGRCKoneKerConn
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nC2f_inv_mem_ggInduced {G : Type} [Group G] {H Bs : Subgroup G}
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs) : φ⁻¹ ∈ ggInduced H Bs := by
  obtain ⟨g, hgH, hgN, hg⟩ := hφ
  refine ⟨g⁻¹, H.inv_mem hgH, Subgroup.inv_mem _ hgN, fun b => ?_⟩
  have h : ((b : ↥Bs) : G) = g * ((φ⁻¹ b : ↥Bs) : G) * g⁻¹ := by
    have h1 := hg (φ⁻¹ b)
    have h2 : φ (φ⁻¹ b) = b := by simp
    rw [h2] at h1
    exact h1
  rw [h]
  group

private noncomputable def l05nC2f_inducedSubgroup {G : Type} [Group G] (H Bs : Subgroup G) :
    Subgroup (MulAut ↥Bs) where
  carrier := ggInduced H Bs
  one_mem' := one_mem_ggInduced H Bs
  mul_mem' := fun ha hb => mul_mem_ggInduced ha hb
  inv_mem' := fun ha => l05nC2f_inv_mem_ggInduced ha

private theorem l05nC2f_inducedSubgroup_eq {G : Type} [Group G] (H Bs : Subgroup G) :
    l05nC2f_inducedSubgroup H Bs = ggAutomizer H Bs := by
  apply le_antisymm
  · intro x hx
    change x ∈ ggInduced H Bs at hx
    rw [ggAutomizer]
    exact Subgroup.subset_closure hx
  · rw [ggAutomizer, Subgroup.closure_le]
    intro x hx
    change x ∈ ggInduced H Bs
    exact hx

private theorem l05nC2f_mem_ggInduced_of_mem_automizer {G : Type} [Group G] {H Bs : Subgroup G}
    {ψ : MulAut ↥Bs} (h : ψ ∈ ggAutomizer H Bs) : ψ ∈ ggInduced H Bs := by
  have hsub : ggAutomizer H Bs ≤ l05nC2f_inducedSubgroup H Bs := by
    rw [l05nC2f_inducedSubgroup_eq]
  change ψ ∈ ggInduced H Bs
  exact hsub h

private theorem l05nC2f_mem_ggInduced_top_of_mem_sup {G : Type} [Group G] {L Bs K : Subgroup G}
    {ψ : MulAut ↥Bs} (h : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    ψ ∈ ggInduced ⊤ Bs := by
  have hsub : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ l05nC2f_inducedSubgroup ⊤ Bs := by
    apply sup_le
    · rw [l05nC2f_inducedSubgroup_eq]
      apply Subgroup.closure_mono
      intro x hx
      obtain ⟨g, hgL, hgN, hg⟩ := hx
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
    · rw [l05nC2f_inducedSubgroup_eq]
      apply Subgroup.closure_mono
      intro x hx
      obtain ⟨g, hgK, hgN, hg⟩ := hx
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  change ψ ∈ ggInduced ⊤ Bs
  exact hsub h

private theorem l05nC2f_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem l05nC2f_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hxBs : x ∈ Bs) :
    ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcent : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  intro ψ hψ
  have hψ' : ψ ∈ ggInduced L Bs := l05nC2f_mem_ggInduced_of_mem_automizer hψ
  obtain ⟨g, hgL, hgN, hg⟩ := hψ'
  have hmem : g ∈ Subgroup.centralizer ({x} : Set G) := hcent hgL
  have hcomm : g * x = x * g :=
    ((Subgroup.mem_centralizer_iff.mp hmem) x (by simp)).symm
  apply Subtype.ext
  have h : ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by
    have h1 := hg (⟨x, hxBs⟩ : ↥Bs)
    simpa using h1
  rw [h, hcomm]
  group

private noncomputable def l05nC2f_typeA_permIso {Λ : Type} [Fintype Λ]
    {M : CoxeterMatrix Λ} {m : ℕ} (eA : Fin m ≃ Λ)
    (hML : M = (CoxeterMatrix.A m).reindex eA) :
    Equiv.Perm (Fin (m + 1)) ≃* M.Group :=
  ((typeAWeylEquiv m).trans (MulEquiv.cast (coxeterMatrix_isFiniteType_A_eq m))).trans
    ((CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A m) eA).symm.trans
      (MulEquiv.cast hML.symm))

theorem ggResCaseIILargeInput_of_inputs
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) : GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K => GGResLeviDatum p Bs L J K ggSelII (ggTypRankGe 9) := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hP
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx : x ^ p = 1 := hH.1.tableB_facts.2.1.2 x hxBs
  have hLI : LinearIndependent (ZMod p) (fun i : Λ => h (some i)) := hsel.1
  have hn9 : 9 ≤ Fintype.card Λ := by
    have hh := htyp
    rw [ggTypRankGe] at hh
    rwa [Nat.card_eq_fintype_card] at hh
  have hrk : 3 ≤ Fintype.card Λ := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let U : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range fun i : Λ => h (some i))
  have hdimU : Module.finrank (ZMod p) U = Fintype.card Λ :=
    finrank_span_eq_card hLI
  have hnoneU : h none ∈ U := by
    by_contra hc
    exact hsel.2 ((linearIndependent_option (v := h) (K := ZMod p)).mpr ⟨hLI, hc⟩)
  have hmemU : ∀ o : Option Λ, h o ∈ U := by
    intro o
    cases o with
    | none => exact hnoneU
    | some i => exact Submodule.subset_span ⟨i, rfl⟩
  have hspanV : Submodule.span (ZMod p) (Set.range h) = U := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨o, rfl⟩
      exact hmemU o
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨some i, rfl⟩
  have hfixL : ∀ bb : Bs, (∀ i : Λ, φ (some i) bb = bb) → (bb : G) ∈ Subgroup.zpowers x := by
    intro bb hb
    refine hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb ?_
    rw [hAL]
    exact ggFixed_of_mem_closure (fun i : Λ => φ (some i)) bb hb
  have hdimV : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) U + 1 := by
    rw [hdimU]
    exact ggRC_finrank_le_of_fix hx ι (fun i : Λ => φ (some i)) (fun i : Λ => h (some i))
      (fun i : Λ => α (some i)) (fun i w => hφ (some i) w) hfixL
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  let g : Option Λ → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  have hA' : A' = Subgroup.closure (Set.range φ) := by
    dsimp [A']
    rw [hAL, hAK, ← Subgroup.closure_union]
    congr 1
    ext γ
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr (Or.inr rfl)
      | some i => exact Or.inl ⟨i, rfl⟩
  have hA : A_V = Subgroup.closure (Set.range g) := by
    dsimp [A_V]
    rw [hA', MonoidHom.map_closure, ← Set.range_comp]
    rfl
  let P : (V ≃ₗ[ZMod p] V) → Prop := fun a => ∀ w, a w - w ∈ U
  have hgenP : ∀ o : Option Λ, P (g o) := by
    intro o w
    have h1 := hφ o w
    dsimp only [P, g]
    rw [h1]
    have hsub : w - α o w • h o - w = -(α o w) • h o := by
      rw [sub_sub_cancel_left, ← neg_smul]
    rw [hsub]
    exact Submodule.smul_mem _ _ (hmemU o)
  have honeP : P 1 := by
    intro w
    simp [P]
  have hmulP : ∀ a b : V ≃ₗ[ZMod p] V, P a → P b → P (a * b) := by
    intro a b ha hb w
    have h1 : b w - w ∈ U := hb w
    have h2 : a (b w - w) - (b w - w) ∈ U := ha (b w - w)
    have h3 : a (b w - w) ∈ U := by
      have hsum : a (b w - w) = (a (b w - w) - (b w - w)) + (b w - w) := by abel_nf
      rw [hsum]
      exact Submodule.add_mem _ h2 h1
    have h4 : a w - w ∈ U := ha w
    have hmul : a (b w) - w = a (b w - w) + (a w - w) := by
      rw [map_sub]
      abel_nf
    rw [LinearEquiv.mul_apply, hmul]
    exact Submodule.add_mem _ h3 h4
  have hinvP : ∀ a : V ≃ₗ[ZMod p] V, P a → P a⁻¹ := by
    intro a ha w
    have h := ha (a⁻¹ w)
    have hw : w - a⁻¹ w ∈ U := by simpa using h
    have hneg : a⁻¹ w - w = -(w - a⁻¹ w) := by abel_nf
    rw [hneg]
    exact Submodule.neg_mem _ hw
  have hS4 : ∀ a ∈ A_V, ∀ w, a w - w ∈ U := by
    intro a ha
    rw [hA] at ha
    refine Subgroup.closure_induction (p := fun a _ => P a) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨o, rfl⟩
      exact hgenP o
    · exact honeP
    · intro x y _ _ hx hy
      exact hmulP x y hx hy
    · intro x _ hx
      exact hinvP x hx
  have hnt : ∀ a ∈ A_V, ¬ (Module.finrank (ZMod p) (ggLinMove a) = 1 ∧
      ∀ w, a (a w - w) = a w - w) := by
    intro a ha hcond
    obtain ⟨ψ, hψA', hψeq⟩ := Subgroup.mem_map.mp ha
    have hψsup : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by simpa [A'] using hψA'
    have hψind : ψ ∈ ggInduced ⊤ Bs :=
      l05nC2f_mem_ggInduced_top_of_mem_sup hψsup
    have hcond' : Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
        ∀ w, ggLin (p := p) ι ψ (ggLin (p := p) ι ψ w - w) = ggLin (p := p) ι ψ w - w := by
      rwa [hψeq]
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond')
  obtain ⟨AU, e, he_apply, he_refl⟩ := ggRC_restrict_equiv U hdimV A_V hS4 hnt
  let eA' : A' ≃* A_V := Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)
  let e' : A' ≃* AU := eA'.trans e
  have hcardAU : Nat.card AU = Nat.card A' := (Nat.card_congr e'.toEquiv).symm
  let hU : Option Λ → U := fun o => ⟨h o, hmemU o⟩
  let αU : Option Λ → Module.Dual (ZMod p) U := fun o => (α o).comp U.subtype
  have hgen_mem : ∀ o : Option Λ, g o ∈ A_V := fun o => by
    rw [hA]; exact Subgroup.subset_closure (Set.mem_range_self o)
  let gA : Option Λ → A_V := fun o => ⟨g o, hgen_mem o⟩
  have hgA_eq : (fun o : Option Λ => (gA o : V ≃ₗ[ZMod p] V)) = g := rfl
  let gU : Option Λ → (U ≃ₗ[ZMod p] U) := fun o => (e (gA o) : AU)
  have hclosureA : Subgroup.closure (Set.range gA) = ⊤ := by
    have hmap1 : Subgroup.map A_V.subtype (Subgroup.closure (Set.range gA)) = A_V := by
      rw [MonoidHom.map_closure]
      have himg : A_V.subtype '' Set.range gA = Set.range g := by
        ext x
        constructor
        · rintro ⟨y, ⟨o, rfl⟩, rfl⟩
          exact ⟨o, rfl⟩
        · rintro ⟨o, rfl⟩
          exact ⟨gA o, ⟨o, rfl⟩, rfl⟩
      rw [himg]
      exact hA.symm
    have hmap2 : Subgroup.map A_V.subtype (⊤ : Subgroup A_V) = A_V := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hker : A_V.subtype.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff (A_V.subtype)).mpr Subtype.val_injective
    have h := congrArg (Subgroup.comap A_V.subtype) (hmap1.trans hmap2.symm)
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, hker, sup_bot_eq, sup_bot_eq] at h
  have hAU_closure : AU = Subgroup.closure (Set.range gU) := by
    have htop : Subgroup.closure (Set.range fun o : Option Λ => e (gA o)) = ⊤ := by
      have hmap := MonoidHom.map_closure (e : A_V →* AU) (Set.range gA)
      rw [hclosureA, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at hmap
      have hrange : Set.range (fun o : Option Λ => e (gA o)) =
          ⇑(e : A_V →* AU) '' Set.range gA := by
        ext x
        constructor
        · rintro ⟨o, rfl⟩
          exact ⟨gA o, ⟨o, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨o, rfl⟩, rfl⟩
          exact ⟨o, rfl⟩
      rw [hrange]
      exact hmap.symm
    have himg2 : Set.range gU = AU.subtype '' Set.range (fun o : Option Λ => e (gA o)) := by
      ext x
      constructor
      · rintro ⟨o, rfl⟩
        exact ⟨e (gA o), ⟨o, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨o, rfl⟩, rfl⟩
        exact ⟨o, rfl⟩
    calc AU = Subgroup.map AU.subtype (⊤ : Subgroup AU) := by
            rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = Subgroup.map AU.subtype
            (Subgroup.closure (Set.range fun o : Option Λ => e (gA o))) := by rw [htop]
      _ = Subgroup.closure (AU.subtype '' Set.range (fun o : Option Λ => e (gA o))) :=
            MonoidHom.map_closure _ _
      _ = Subgroup.closure (Set.range gU) := by rw [← himg2]
  have hspanU : Submodule.span (ZMod p) (Set.range hU) = ⊤ := by
    have heq : U.subtype '' Set.range hU = Set.range h := by
      ext x
      constructor
      · rintro ⟨y, ⟨o, rfl⟩, rfl⟩
        exact ⟨o, rfl⟩
      · rintro ⟨o, rfl⟩
        exact ⟨hU o, ⟨o, rfl⟩, rfl⟩
    have hmap : Submodule.map U.subtype (Submodule.span (ZMod p) (Set.range hU)) =
        Submodule.map U.subtype (⊤ : Submodule (ZMod p) U) := by
      rw [← Submodule.span_image (f := U.subtype)]
      rw [heq, hspanV]
      rw [Submodule.map_top]
      exact (Submodule.range_subtype U).symm
    exact Submodule.map_injective_of_injective Subtype.val_injective hmap
  have hkerV : ∀ w : V, (∀ o : Option Λ, α o w = 0) → w = 0 :=
    (ggRC_kone_ker_conn hFix hFixK hp2 hH hWL hCL hWK hCK hrk hφ hL hK hAL hAK).1
  have hconnV : ∀ o o' : Option Λ,
      Relation.ReflTransGen (fun a c => α a (h c) ≠ 0 ∧ α c (h a) ≠ 0) o o' :=
    (ggRC_kone_ker_conn hFix hFixK hp2 hH hWL hCL hWK hCK hrk hφ hL hK hAL hAK).2
  have hα : ∀ o : Option Λ, α o (h o) = 2 := by
    intro o
    cases o with
    | none =>
      have h1 := hK none none
      rw [hCK.1 none] at h1
      simpa using h1
    | some i =>
      have h1 := hL i i
      rw [hCL.1 i] at h1
      simpa using h1
  have h2ne : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hne : ∀ o : Option Λ, h o ≠ 0 := by
    intro o h0
    have h1 := hα o
    rw [h0, map_zero] at h1
    exact h2ne h1.symm
  have hαU : ∀ o : Option Λ, αU o (hU o) = 2 := by
    intro o
    exact hα o
  have hkerU : ∀ u : U, (∀ o : Option Λ, αU o u = 0) → u = 0 := by
    intro u hu
    apply Subtype.ext
    exact hkerV (u : V) (fun o => hu o)
  have hconnU : ∀ o o' : Option Λ,
      Relation.ReflTransGen (fun a c => αU a (hU c) ≠ 0 ∧ αU c (hU a) ≠ 0) o o' := by
    intro o o'
    simpa only [αU, hU, LinearMap.comp_apply, Submodule.subtype_apply] using hconnV o o'
  have hgUapply : ∀ o u, gU o u = u - αU o u • hU o := by
    intro o u
    apply Subtype.ext
    change (((e (gA o) : AU) : U ≃ₗ[ZMod p] U) u : V) = ((u - αU o u • hU o : U) : V)
    rw [he_apply]
    show (g o) (u : V) = ((u - αU o u • hU o : U) : V)
    rw [hφ o (u : V)]
    simp only [Submodule.coe_sub, Submodule.coe_smul, hU, αU, LinearMap.comp_apply,
      Submodule.subtype_apply]
  have hirr : ZS.AbsIrred p AU :=
    ggRC_absIrred_of_connected hp2 gU hU αU hgUapply hαU hspanU hkerU hconnU AU hAU_closure
  have hreflLin : ∀ o : Option Λ, GGLinRefl (g o) :=
    fun o => (ggRC_isReflection_iff_linRefl ι (φ o)).mp (hrefl o)
  have hreflU : ∀ o : Option Λ, GGLinRefl (gU o) :=
    fun o => he_refl (gA o) (hreflLin o)
  have hgen : AU = Subgroup.closure {r | r ∈ AU ∧ GGLinRefl r} := by
    rw [hAU_closure]
    apply le_antisymm
    · apply Subgroup.closure_mono
      intro x hx
      obtain ⟨o, rfl⟩ := hx
      exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hreflU o⟩
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  let αx : V := ι (Additive.ofMul ⟨x, hxBs⟩)
  let S : Set ↥Bs := {bb | ι (Additive.ofMul bb) - αx ∈ U}
  have hOrbSet : ∀ a ∈ A', a ⟨x, hxBs⟩ ∈ S := by
    intro a ha
    have haV : ggLin (p := p) ι a ∈ A_V := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have h := hS4 (ggLin (p := p) ι a) haV αx
    simpa [S, αx, ggLin_apply_ofMul] using h
  have hcardS : Nat.card S = p ^ Fintype.card Λ := by
    have hSU : Nat.card S = Nat.card U := by
      apply Nat.card_congr
      refine
        { toFun := fun bb => ⟨ι (Additive.ofMul (bb : ↥Bs)) - αx, bb.2⟩
          invFun := fun u => ⟨Additive.toMul (ι.symm ((u : V) + αx)), ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · show ι (Additive.ofMul (Additive.toMul (ι.symm ((u : V) + αx)))) - αx ∈ U
        have hval : ι (Additive.ofMul (Additive.toMul (ι.symm ((u : V) + αx)))) =
            (u : V) + αx := by simp
        rw [hval]
        simpa using u.2
      · intro bb
        apply Subtype.ext
        have hval : ι (Additive.ofMul (Additive.toMul
            (ι.symm (ι (Additive.ofMul (bb : ↥Bs)) - αx + αx)))) =
            ι (Additive.ofMul (bb : ↥Bs)) := by
          simp
        simpa using hval
      · intro u
        apply Subtype.ext
        have hval : ι (Additive.ofMul (Additive.toMul (ι.symm ((u : V) + αx)))) - αx = (u : V) := by
          simp
        simpa using hval
    have hpow : Nat.card U = p ^ Fintype.card Λ := by
      rw [← hdimU]
      exact (FiniteField.pow_finrank_eq_natCard p U).symm
    exact hSU.trans hpow
  haveI : Finite U := Finite.of_injective (fun u : U => (u : V)) (fun a b hab => Subtype.ext hab)
  have hWcard : Nat.card ↥(ggAutomizer L Bs) = Nat.card ML.Group :=
    (Nat.card_congr fL.toEquiv).symm
  have hjoin : Nat.card A' ≤ Nat.card S * ((p - 1) * 6 * Nat.card ML.Group) := by
    rw [← hWcard]
    exact ggRC_card_join_le_of_orbit hOrb hH hxBs S hOrbSet
  have hsmall : 8 * Nat.card A' <
      p ^ (Fintype.card Λ * (Fintype.card Λ - 1) / 2) :=
    ggRC_small_of_card_II hp hp2 ML hWL hn9 (Nj := Nat.card A') (NU := Nat.card S)
      hcardS hjoin
  obtain himp | hclass | ⟨hndvd, e1, he1⟩ | ⟨hdvd, e2, he2⟩ :=
    hKG p hp2 U (Fintype.card Λ) hdimU hn9 AU hirr hgen
  ·
    exfalso
    obtain ⟨bU, hmon⟩ :=
      ggRC_monomial_of_imprimitive (p := p) (n := Fintype.card Λ) hdimU AU hirr hgen himp
    obtain ⟨π, hπ, hπker, hπcomm, hπp⟩ := ggRC_monomial_hom bU AU hmon
    by_cases hDelta : π.ker = ⊥
    ·
      have hdiag : ∀ a ∈ AU, (∀ i, ∃ c : ZMod p, a (bU i) = c • bU i) → a = 1 := by
        intro a ha hdiagA
        have hπa : π ⟨a, ha⟩ = 1 := by
          apply Equiv.ext
          intro i
          obtain ⟨c1, hc1, h1⟩ := hπ ⟨a, ha⟩ i
          obtain ⟨c2, h2⟩ := hdiagA i
          have hc2 : c2 ≠ 0 := by
            intro hc2
            have hzero : a (bU i) = 0 := by rw [h2, hc2, zero_smul]
            exact (bU.ne_zero i) (a.injective (by rw [hzero, map_zero]))
          have heq : c1 • bU (π ⟨a, ha⟩ i) = c2 • bU i := by rw [← h1, h2]
          have hcoord := congrArg (fun v => bU.equivFun v i) heq
          simp only [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self] at hcoord
          by_cases hπi : π ⟨a, ha⟩ i = i
          · exact hπi
          · exfalso
            simp only [hπi, if_false, if_true, mul_zero, mul_one] at hcoord
            exact hc2 hcoord.symm
        have h1 : (⟨a, ha⟩ : AU) = 1 := by
          have hmem : (⟨a, ha⟩ : AU) ∈ π.ker := hπa
          rw [hDelta] at hmem
          exact Subgroup.mem_bot.mp hmem
        exact Subtype.ext_iff.mp h1
      have hcard_le : Nat.card AU ≤ (Fintype.card Λ).factorial :=
        ggRC_card_le_factorial_of_monomial bU AU hmon hdiag
      have hweyl : (Fintype.card Λ + 1).factorial ≤ Nat.card AU := by
        have h1 : (Fintype.card Λ + 1).factorial ≤ Nat.card ML.Group :=
          ggRC_card_weyl_ge ML hWL hn9
        have h2 : Nat.card ML.Group ≤ Nat.card A' := by
          rw [Nat.card_congr fL.toEquiv]
          exact Subgroup.card_le_of_le le_sup_left
        have h3 : Nat.card A' ≤ Nat.card AU := by rw [hcardAU]
        exact h1.trans (h2.trans h3)
      have hlt : (Fintype.card Λ).factorial < (Fintype.card Λ + 1).factorial :=
        (Nat.factorial_lt (m := Fintype.card Λ + 1) (n := Fintype.card Λ)
          (by omega)).mpr (Nat.lt_succ_self _)
      exact absurd (hweyl.trans hcard_le) (not_le.mpr hlt)
    ·
      let Δ : Subgroup AU := π.ker
      let UDelta : Submodule (ZMod p) U :=
        { carrier := {u | ∀ d ∈ Δ, (d : U ≃ₗ[ZMod p] U) u = u}
          add_mem' := by
            intro u v hu hv d hd
            rw [map_add, hu d hd, hv d hd]
          zero_mem' := by
            intro d _
            rw [map_zero]
          smul_mem' := by
            intro c u hu d hd
            rw [map_smul, hu d hd] }
      have hDelta_normal : Δ.Normal := MonoidHom.normal_ker π
      have hUDelta_inv : ∀ a ∈ AU, ∀ u ∈ UDelta, a u ∈ UDelta := by
        intro a ha u hu d hd
        let j : AU := (⟨a, ha⟩ : AU)⁻¹ * d * ⟨a, ha⟩
        have hj : j ∈ Δ := hDelta_normal.conj_mem d hd (⟨a, ha⟩ : AU)⁻¹
        have hju : (j : U ≃ₗ[ZMod p] U) u = u := hu j hj
        have hcoe : (j : U ≃ₗ[ZMod p] U) = a⁻¹ * (d : U ≃ₗ[ZMod p] U) * a := by
          simp only [j, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hcoe] at hju
        have h1 : (a⁻¹ * (d : U ≃ₗ[ZMod p] U) * a) u =
            a⁻¹ ((d : U ≃ₗ[ZMod p] U) (a u)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        have h2 : a⁻¹ ((d : U ≃ₗ[ZMod p] U) (a u)) = u := by
          rw [← h1]; exact hju
        have h3 := congrArg (fun v => a v) h2
        simpa using h3
      have hUDelta_cases : UDelta = ⊥ ∨ UDelta = ⊤ := hirr.1 UDelta hUDelta_inv
      have hUDelta_bot : UDelta = ⊥ := by
        rcases hUDelta_cases with h | h
        · exact h
        · exfalso
          apply hDelta
          apply le_antisymm _ bot_le
          intro d hd
          rw [Subgroup.mem_bot]
          apply Subtype.ext
          apply LinearEquiv.ext
          intro u
          have hu : u ∈ UDelta := by rw [h]; exact Submodule.mem_top
          simpa using hu d hd
      by_cases hUt : U = ⊤
      ·
        have hx_ne : x ≠ 1 := l05nC2f_x_ne_one hH
        have hIx_ne : ι (Additive.ofMul ⟨x, hxBs⟩) ≠ 0 := by
          intro h0
          have h2 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = Additive.ofMul (1 : ↥Bs) :=
            ι.injective (by rw [h0]; simp)
          exact hx_ne (Subtype.ext_iff.mp (Additive.ofMul.injective h2))
        have hαx : ∀ i : Λ, α (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0 := by
          intro i
          have hfix : φ (some i) ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
            l05nC2f_automizer_fixes_x hH.1 hxBs (φ (some i))
              (by rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
          have h1 := hφ (some i) (ι (Additive.ofMul ⟨x, hxBs⟩))
          rw [ggLin_apply_ofMul, hfix] at h1
          have hX : α (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) • h (some i) = 0 := by
            have h2 : ι (Additive.ofMul ⟨x, hxBs⟩) -
                α (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) • h (some i) =
                ι (Additive.ofMul ⟨x, hxBs⟩) := h1.symm
            exact sub_eq_self.mp h2
          exact (smul_eq_zero.mp hX).resolve_right (hne (some i))
        have hdet : ((CL.det : ℤ) : ZMod p) = 0 :=
          ggRC_det_cast_eq_zero_of_kernel (fun i : Λ => h (some i)) (fun i : Λ => α (some i)) CL
            hL (ι (Additive.ofMul ⟨x, hxBs⟩))
            (by change ι (Additive.ofMul ⟨x, hxBs⟩) ∈ U; rw [hUt]; exact Submodule.mem_top)
            hIx_ne hαx
        have hTypeA : GGIsTypeA ML :=
          ggRC_typeA_of_dvd_det hp hp2 hWL hCL (by omega : 7 ≤ Fintype.card Λ) hdet
        obtain ⟨m, eA, _hm1, hML⟩ := hTypeA
        have hmn : m = Fintype.card Λ := by
          have h := Fintype.card_congr eA
          simpa using h
        let Φ : Equiv.Perm (Fin (m + 1)) ≃* ggAutomizer L Bs :=
          (l05nC2f_typeA_permIso eA hML).trans fL
        let inc : ggAutomizer L Bs →* A' :=
          Subgroup.inclusion (show ggAutomizer L Bs ≤ A' from le_sup_left)
        let Ψ : Equiv.Perm (Fin (m + 1)) →* AU :=
          (e'.toMonoidHom).comp (inc.comp Φ.toMonoidHom)
        let π' : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm (Fin (Fintype.card Λ)) := π.comp Ψ
        have hincinj : Function.Injective inc :=
          Subgroup.inclusion_injective (show ggAutomizer L Bs ≤ A' from le_sup_left)
        have hΨinj : Function.Injective Ψ := (e'.injective).comp (hincinj.comp Φ.injective)
        have hπ'comm : IsMulCommutative π'.ker := by
          rw [isMulCommutative_iff]
          intro a b
          apply Subtype.ext
          apply hΨinj
          rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
          exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
            ⟨Ψ (a : Equiv.Perm (Fin (m + 1))), a.2⟩
            ⟨Ψ (b : Equiv.Perm (Fin (m + 1))), b.2⟩)
        exact ggRC_perm_not_monomial (N := m + 1) (m := Fintype.card Λ)
          (by omega) (by omega) π' hπ'comm
      ·
        let ΔV : Subgroup (V ≃ₗ[ZMod p] V) := (Δ.comap (e : A_V →* AU)).map A_V.subtype
        have hΔA : ΔV ≤ A_V := Subgroup.map_subtype_le _
        have hΔn : ∀ a ∈ A_V, ∀ d ∈ ΔV, a * d * a⁻¹ ∈ ΔV := by
          intro a ha d hd
          obtain ⟨d', hd'mem, hd'eq⟩ := Subgroup.mem_map.mp hd
          have hd'Δ : e d' ∈ Δ := Subgroup.mem_comap.mp hd'mem
          refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩ * d' * ⟨a, ha⟩⁻¹, ?_, ?_⟩
          · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
            exact hDelta_normal.conj_mem (e d') hd'Δ (e ⟨a, ha⟩)
          · change a * (d' : V ≃ₗ[ZMod p] V) * a⁻¹ = a * d * a⁻¹
            rw [show (d' : V ≃ₗ[ZMod p] V) = d from hd'eq]
        have hcardΔV : Nat.card ΔV = Nat.card Δ := by
          apply Nat.card_congr
          refine
            { toFun := fun d => ⟨e ⟨d, hΔA d.2⟩, ?_⟩
              invFun := fun δ => ⟨((e.symm (δ : AU) : A_V) : V ≃ₗ[ZMod p] V), ?_⟩
              left_inv := ?_
              right_inv := ?_ }
          · obtain ⟨d', hd'mem, hd'eq⟩ := Subgroup.mem_map.mp d.2
            have hdd' : d' = ⟨d, hΔA d.2⟩ := Subtype.ext hd'eq
            rw [← hdd']
            exact Subgroup.mem_comap.mp hd'mem
          · refine Subgroup.mem_map.mpr ⟨e.symm (δ : AU), Subgroup.mem_comap.mpr ?_, rfl⟩
            simpa using δ.2
          · intro d
            apply Subtype.ext
            simp
          · intro δ
            apply Subtype.ext
            simp
        have hΔp : ¬ p ∣ Nat.card ΔV := by
          rw [hcardΔV]
          exact hπp
        have hUΔ : ∀ u ∈ U, (∀ d ∈ ΔV, d u = u) → u = 0 := by
          intro u hu hfix
          have hmem : (⟨u, hu⟩ : U) ∈ UDelta := by
            intro δ hδ
            apply Subtype.ext
            let a0 : A_V := e.symm δ
            have hea0 : e a0 = δ := MulEquiv.apply_symm_apply e δ
            have hd : (a0 : V ≃ₗ[ZMod p] V) ∈ ΔV := by
              refine Subgroup.mem_map.mpr ⟨a0, Subgroup.mem_comap.mpr ?_, rfl⟩
              simpa [hea0] using hδ
            have happ := he_apply a0 (⟨u, hu⟩ : U)
            rw [hfix (a0 : V ≃ₗ[ZMod p] V) hd, hea0] at happ
            exact happ
          rw [hUDelta_bot, Submodule.mem_bot] at hmem
          exact Subtype.ext_iff.mp hmem
        obtain ⟨w, hwU, hwfix⟩ :=
          ggRC_fixed_vector_of_diag U hUt A_V ΔV hΔA hS4 hΔn hΔp hUΔ
        have hαw : ∀ o : Option Λ, α o w = 0 := by
          intro o
          have hgo : g o w = w := hwfix (g o) (hgen_mem o)
          have h1 := hφ o w
          rw [hgo] at h1
          have hX : α o w • h o = 0 := by
            have h2 : w - α o w • h o = w := h1.symm
            exact sub_eq_self.mp h2
          exact (smul_eq_zero.mp hX).resolve_right (hne o)
        exact hwU (by rw [hkerV w hαw]; exact Submodule.zero_mem U)
  ·
    have : 8 * Nat.card A' < 8 * Nat.card A' := by
      calc 8 * Nat.card A' < p ^ (Fintype.card Λ * (Fintype.card Λ - 1) / 2) := hsmall
        _ ≤ 8 * Nat.card AU := hclass
        _ = 8 * Nat.card A' := by rw [hcardAU]
    exact absurd this (lt_irrefl _)
  ·
    exfalso
    have hcardAU1 : Nat.card AU = (Fintype.card Λ + 1).factorial := by
      rw [Nat.card_congr e1.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hWge : (Fintype.card Λ + 1).factorial ≤ Nat.card ↥(ggAutomizer L Bs) := by
      rw [hWcard]
      exact ggRC_card_weyl_ge ML hWL hn9
    have hAle : Nat.card A' ≤ Nat.card ↥(ggAutomizer L Bs) := by
      have h1 : Nat.card A' ≤ Nat.card AU := by rw [hcardAU]
      rw [hcardAU1] at h1
      exact le_trans h1 hWge
    have haut : ggAutomizer L Bs = A' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left hAle
    have hKleL : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
      rw [haut]
      exact le_sup_right
    have hfixLx : ∀ o : Option Λ, φ o ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      intro o
      cases o with
      | some i =>
        exact l05nC2f_automizer_fixes_x hH.1 hxBs (φ (some i))
          (by rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
      | none =>
        exact l05nC2f_automizer_fixes_x hH.1 hxBs (φ none)
          (hKleL (by
            rw [hAK]
            exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))))
    have hαx : ∀ o : Option Λ, α o (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0 := by
      intro o
      have h1 := hφ o (ι (Additive.ofMul ⟨x, hxBs⟩))
      rw [ggLin_apply_ofMul, hfixLx o] at h1
      have hX : α o (ι (Additive.ofMul ⟨x, hxBs⟩)) • h o = 0 := by
        have h2 : ι (Additive.ofMul ⟨x, hxBs⟩) -
            α o (ι (Additive.ofMul ⟨x, hxBs⟩)) • h o =
            ι (Additive.ofMul ⟨x, hxBs⟩) := h1.symm
        exact sub_eq_self.mp h2
      exact (smul_eq_zero.mp hX).resolve_right (hne o)
    have hIx0 : ι (Additive.ofMul ⟨x, hxBs⟩) = 0 := hkerV _ hαx
    exact l05nC2f_x_ne_one hH (by
      have h2 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = Additive.ofMul (1 : ↥Bs) :=
        ι.injective (by rw [hIx0]; simp)
      exact Subtype.ext_iff.mp (Additive.ofMul.injective h2))
  ·
    let e'' : A' ≃* Equiv.Perm (Fin (Fintype.card Λ + 2)) := e'.trans e2
    have hrefl'' : ∀ r : A', GGIsReflection p (r : MulAut ↥Bs) →
        ∃ i j, i ≠ j ∧ e'' r = Equiv.swap i j := by
      intro r hr
      have hrlin : GGLinRefl (ggLin (p := p) ι (r : MulAut ↥Bs)) :=
        (ggRC_isReflection_iff_linRefl ι (r : MulAut ↥Bs)).mp hr
      have hrV : ggLin (p := p) ι (r : MulAut ↥Bs) ∈ A_V :=
        Subgroup.mem_map.mpr ⟨(r : MulAut ↥Bs), r.2, rfl⟩
      have hrU : GGLinRefl
          (((e ⟨ggLin (p := p) ι (r : MulAut ↥Bs), hrV⟩ : AU)) : U ≃ₗ[ZMod p] U) :=
        he_refl ⟨ggLin (p := p) ι (r : MulAut ↥Bs), hrV⟩ hrlin
      obtain ⟨i, j, hij, heij⟩ := he2 (e ⟨ggLin (p := p) ι (r : MulAut ↥Bs), hrV⟩) hrU
      refine ⟨i, j, hij, ?_⟩
      show e2 (e' r) = Equiv.swap i j
      have he'r : e' r = e ⟨ggLin (p := p) ι (r : MulAut ↥Bs), hrV⟩ := by
        dsimp only [e']
        rw [MulEquiv.trans_apply]
        congr 1
      rw [he'r]
      exact heij
    have hgen'' : GGReflGenerated p A' := by
      rw [GGReflGenerated, hA']
      apply le_antisymm
      · apply Subgroup.closure_mono
        intro x hx
        obtain ⟨o, rfl⟩ := hx
        exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hrefl o⟩
      · rw [Subgroup.closure_le]
        intro x hx
        exact hx.1
    exact ggRC_weyl_of_perm A' (by omega : 3 ≤ Fintype.card Λ + 2) e'' hrefl'' hgen''

end CFSG.StandardType
