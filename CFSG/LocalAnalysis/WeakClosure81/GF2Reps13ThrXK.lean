module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXJ
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXKB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXKA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement BigOperators

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_odd_card_of_isElemAbelian_three {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 3 X) : Odd (Nat.card X) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpg : IsPGroup 3 X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 x.1 x.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  rw [hm]
  exact Odd.pow (by norm_num : Odd 3)

private theorem w16g_map_mem_s13IsoComps' {A X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ A) (hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (U : ↥(s13IsoComps X)) :
    U.1.map g.toMonoidHom ∈ s13IsoComps X :=
  map_mem_s13IsoComps (hXA g hg) (by simpa using hXA g⁻¹ (A.inv_mem hg)) U.2

private theorem w16g_conj_map_conj (Q : Subgroup (MulAut W)) (g a : MulAut W) :
    (Q.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Q.map (MulAut.conj (g * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16g_s13SuppGraph_adj_map {A X Q : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ A) (hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    {U U' : ↥(s13IsoComps X)} (h : (s13SuppGraph A X Q).Adj U U') :
    (s13SuppGraph A X Q).Adj
      ⟨U.1.map g.toMonoidHom, w16g_map_mem_s13IsoComps' hg hXA U⟩
      ⟨U'.1.map g.toMonoidHom, w16g_map_mem_s13IsoComps' hg hXA U'⟩ := by
  rw [s13SuppGraph, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hne, hrel⟩ := h
  refine ⟨?_, ?_⟩
  · intro heq
    exact hne (Subtype.ext (Subgroup.map_injective g.injective (congrArg Subtype.val heq)))
  · rcases hrel with ⟨a, ha, hsupp⟩ | ⟨a, ha, hsupp⟩
    · left
      refine ⟨g * a, A.mul_mem hg ha, ?_⟩
      rw [← w16g_conj_map_conj Q g a,
        w16g_s13Supp_conj (hXA g hg) (by simpa using hXA g⁻¹ (A.inv_mem hg)), hsupp,
        Set.image_pair]
    · right
      refine ⟨g * a, A.mul_mem hg ha, ?_⟩
      rw [← w16g_conj_map_conj Q g a,
        w16g_s13Supp_conj (hXA g hg) (by simpa using hXA g⁻¹ (A.inv_mem hg)), hsupp,
        Set.image_pair]

private theorem w16g_s13CompSet_image_eq {A X Q : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ A) (hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    ∃ c' : (s13SuppGraph A X Q).ConnectedComponent,
      s13CompSet A X Q c' =
        (fun U : Subgroup W => U.map g.toMonoidHom) '' s13CompSet A X Q c := by
  classical
  let ψ : ↥(s13IsoComps X) → ↥(s13IsoComps X) := fun U =>
    ⟨U.1.map g.toMonoidHom, w16g_map_mem_s13IsoComps' hg hXA U⟩
  let ψ' : ↥(s13IsoComps X) → ↥(s13IsoComps X) := fun U =>
    ⟨U.1.map g⁻¹.toMonoidHom, w16g_map_mem_s13IsoComps' (A.inv_mem hg) hXA U⟩
  have hψψ' : ∀ U, ψ (ψ' U) = U := by
    intro U
    apply Subtype.ext
    show (U.1.map g⁻¹.toMonoidHom).map g.toMonoidHom = U.1
    rw [Subgroup.map_map,
      show g.toMonoidHom.comp g⁻¹.toMonoidHom = MonoidHom.id W from by ext x; simp,
      Subgroup.map_id]
  have hψ'ψ : ∀ U, ψ' (ψ U) = U := by
    intro U
    apply Subtype.ext
    show (U.1.map g.toMonoidHom).map g⁻¹.toMonoidHom = U.1
    rw [Subgroup.map_map,
      show g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id W from by ext x; simp,
      Subgroup.map_id]
  let ψHom : (s13SuppGraph A X Q) →g (s13SuppGraph A X Q) :=
    { toFun := ψ, map_rel' := fun {U U'} h => w16g_s13SuppGraph_adj_map hg hXA h }
  let ψ'Hom : (s13SuppGraph A X Q) →g (s13SuppGraph A X Q) :=
    { toFun := ψ', map_rel' := fun {U U'} h => w16g_s13SuppGraph_adj_map (A.inv_mem hg) hXA h }
  obtain ⟨v, hv⟩ := c.exists_rep
  let c' : (s13SuppGraph A X Q).ConnectedComponent :=
    (s13SuppGraph A X Q).connectedComponentMk (ψ v)
  refine ⟨c', ?_⟩
  have hsupp : ψ '' c.supp = c'.supp := by
    ext U
    constructor
    · rintro ⟨V, hV, rfl⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hV ⊢
      exact SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Reachable.map ψHom
          (SimpleGraph.ConnectedComponent.exact (hV.trans hv.symm)))
    · intro hU
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hU
      refine ⟨ψ' U, ?_, hψψ' U⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hr : (s13SuppGraph A X Q).Reachable (ψ' U) (ψ' (ψ v)) :=
        SimpleGraph.Reachable.map ψ'Hom (SimpleGraph.ConnectedComponent.exact hU)
      rw [hψ'ψ v] at hr
      exact (SimpleGraph.ConnectedComponent.sound hr).trans hv
  change Subtype.val '' c'.supp =
    (fun U : Subgroup W => U.map g.toMonoidHom) '' (Subtype.val '' c.supp)
  rw [← hsupp, Set.image_image, Set.image_image]

private theorem w16g_s13CompSet_conj_disjoint_or_eq {A X Q : Subgroup (MulAut W)}
    (hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X) {g : MulAut W} (hg : g ∈ A)
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    (fun U : Subgroup W => U.map g.toMonoidHom) '' s13CompSet A X Q c =
        s13CompSet A X Q c ∨
      Disjoint ((fun U : Subgroup W => U.map g.toMonoidHom) '' s13CompSet A X Q c)
        (s13CompSet A X Q c) := by
  obtain ⟨c', hc'⟩ := w16g_s13CompSet_image_eq hg hXA c
  rw [← hc']
  rcases eq_or_ne c' c with h | h
  · exact Or.inl (by rw [h])
  · refine Or.inr ?_
    have hd : Disjoint c'.supp c.supp :=
      SimpleGraph.pairwise_disjoint_supp_connectedComponent (s13SuppGraph A X Q) h
    rw [Set.disjoint_left]
    rintro U hU hU'
    rw [show s13CompSet A X Q c' = Subtype.val '' c'.supp from rfl] at hU
    rw [show s13CompSet A X Q c = Subtype.val '' c.supp from rfl] at hU'
    obtain ⟨a, ha, rfl⟩ := hU
    obtain ⟨b, hb, hbU⟩ := hU'
    have hba : b = a := Subtype.ext hbU
    rw [hba] at hb
    exact Set.disjoint_left.mp hd ha hb

variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

private noncomputable def w16g_conjOnX (h : HAb A X Q t 3) : ↥X ≃* ↥X where
  toFun x := ⟨t * (x : MulAut W) * t⁻¹, h.hXA t h.htA (x : MulAut W) x.2⟩
  invFun x := ⟨t⁻¹ * (x : MulAut W) * t, by
    simpa using h.hXA t⁻¹ (A.inv_mem h.htA) (x : MulAut W) x.2⟩
  left_inv x := Subtype.ext (by group)
  right_inv x := Subtype.ext (by group)
  map_mul' x y := Subtype.ext (by
    show t * ((x : MulAut W) * (y : MulAut W)) * t⁻¹ =
      (t * (x : MulAut W) * t⁻¹) * (t * (y : MulAut W) * t⁻¹)
    group)

private theorem w16g_sum_eq_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ZMod 3)
    {i j : ι} (hij : i ≠ j) (h : ∀ k, k ≠ i → k ≠ j → g k = 0) :
    ∑ k, g k = g i + g j := by
  have h1 : (∑ k, g k) = ∑ k ∈ ({i, j} : Finset ι), g k :=
    (Finset.sum_subset (s₁ := ({i, j} : Finset ι)) (s₂ := Finset.univ)
      (Finset.subset_univ _) (by
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        push Not at hk
        exact h k hk.1 hk.2)).symm
  rw [h1, Finset.sum_pair hij]

private theorem w16g_conj_mem_s13XSupp (h : HAb A X Q t 3) {C : Set (Subgroup W)}
    (hC : (fun U : Subgroup W => U.map t.toMonoidHom) '' C = C) {y : MulAut W}
    (hy : y ∈ s13XSupp X C) : t * y * t⁻¹ ∈ s13XSupp X C := by
  rw [mem_s13XSupp] at hy ⊢
  refine ⟨h.hXA t h.htA y hy.1, ?_⟩
  intro U hU hUC
  have hU'mem : U.map t⁻¹.toMonoidHom ∈ s13IsoComps X :=
    w16g_map_mem_s13IsoComps' (A.inv_mem h.htA) h.hXA ⟨U, hU⟩
  have hU'notC : U.map t⁻¹.toMonoidHom ∉ C := by
    intro hmem
    apply hUC
    have himg : (U.map t⁻¹.toMonoidHom).map t.toMonoidHom ∈
        (fun U : Subgroup W => U.map t.toMonoidHom) '' C := ⟨_, hmem, rfl⟩
    rw [hC] at himg
    have hcomp : t.toMonoidHom.comp t⁻¹.toMonoidHom = MonoidHom.id W := by
      ext x; simp
    have : (U.map t⁻¹.toMonoidHom).map t.toMonoidHom = U := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rwa [this] at himg
  have hy' : y ∈ s13KerOn X (U.map t⁻¹.toMonoidHom) := hy.2 _ hU'mem hU'notC
  have hcent : t * y * t⁻¹ ∈ centSub U := by
    rw [mem_centSub]
    intro u hu
    have hmem : t⁻¹ u ∈ U.map t⁻¹.toMonoidHom :=
      Subgroup.mem_map_of_mem t⁻¹.toMonoidHom hu
    have hyfix : y (t⁻¹ u) = t⁻¹ u := mem_centSub.mp hy'.2 (t⁻¹ u) hmem
    show (t * y * t⁻¹) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, hyfix]
    simp [MulAut.mul_apply]
  exact ⟨h.hXA t h.htA y hy.1, hcent⟩

private theorem w16g_case_one_sign (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 2)
    (c : (s13SuppGraph A X Q).ConnectedComponent) [Fintype ↥c.supp]
    (hQc : Q ≤ s13XSupp X (s13CompSet A X Q c))
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam)
    {U U' : Subgroup W} (hUU' : U ≠ U') (hsuppQ : s13Supp X Q = {U, U'}) :
    ∃ (f : ↥c.supp → ZMod 3) (π : Equiv.Perm ↥c.supp) (ε : ZMod 3),
      (∀ V, f V ≠ 0) ∧
      (∀ y : ↥c.supp → ZMod 3, (∑ V, f V * y V) = 0 ↔
        ∃ x : ↥(s13XSupp X (s13CompSet A X Q c)),
          ∀ V, lam V.1 (Additive.ofMul (Subgroup.inclusion s13XSupp_le x)) = y V) ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ V, (π V).1.1 = V.1.1.map t.toMonoidHom) ∧
      (∀ V, π (π V) = V) ∧
      (∀ (V : ↥c.supp) (x : ↥X),
        f (π V) * lam (π V).1 (Additive.ofMul (w16g_conjOnX h x)) =
          ε * (f V * lam V.1 (Additive.ofMul x))) ∧
      (ε = 1 → U.map t.toMonoidHom = U' ∧ U'.map t.toMonoidHom = U) ∧
      (ε = -1 → U.map t.toMonoidHom = U ∧ U'.map t.toMonoidHom = U') := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨f, hfne, hfker⟩ := w16g_case_one_hyperplane h hH0 hQ3 he c hQc hl
  obtain ⟨σ, cu, hσsub, hσcoord⟩ := exists_monomial h.hW hp3 hp32 h.hXe hl
    (fun x hx => h.hXA t h.htA x hx)
    (fun x hx => by simpa using h.hXA t⁻¹ (A.inv_mem h.htA) x hx)
  have hQmap1 : Q.map (MulAut.conj t).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      change (MulAut.conj t) q ∈ Q
      rw [MulAut.conj_apply, h.hQinv q hq]
      exact Q.inv_mem hq
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have htMapC : (fun U : Subgroup W => U.map t.toMonoidHom) '' s13CompSet A X Q c =
      s13CompSet A X Q c := by
    rcases w16g_s13CompSet_conj_disjoint_or_eq h.hXA h.htA c with heq | hdis
    · exact heq
    · exfalso
      have hsupp_sub : s13Supp X Q ⊆ s13CompSet A X Q c :=
        (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
      have hUne : (s13Supp X Q).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hemp
        rw [hemp] at he
        simp at he
      obtain ⟨W₀, hW₀⟩ := hUne
      have hW₀c : W₀ ∈ s13CompSet A X Q c := hsupp_sub hW₀
      have hW₀t : W₀.map t.toMonoidHom ∈ s13CompSet A X Q c := by
        have h1 : W₀.map t.toMonoidHom ∈
            s13Supp X (Q.map (MulAut.conj t).toMonoidHom) := by
          rw [s13Supp_conj (fun x hx => h.hXA t h.htA x hx)
            (by simpa using h.hXA t⁻¹ (A.inv_mem h.htA))]
          exact ⟨W₀, hW₀, rfl⟩
        rw [hQmap1] at h1
        exact hsupp_sub h1
      exact (Set.disjoint_left.mp hdis) ⟨W₀, hW₀c, rfl⟩ hW₀t
  have hCsub : s13CompSet A X Q c ⊆ s13IsoComps X := by
    rintro V ⟨W', hW', rfl⟩
    exact W'.2
  have hσmem : ∀ V : ↥c.supp, σ V.1 ∈ c.supp := by
    intro V
    have hVt : V.1.1.map t.toMonoidHom ∈ s13CompSet A X Q c := by
      rw [← htMapC]
      exact ⟨V.1.1, ⟨V.1, V.2, rfl⟩, rfl⟩
    obtain ⟨W', hW', hW'V⟩ := hVt
    have hσeq : σ V.1 = W' := by
      apply Subtype.ext
      rw [hσsub V.1, hW'V]
    rw [hσeq]
    exact hW'
  let πfun : ↥c.supp → ↥c.supp := fun V => ⟨σ V.1, hσmem V⟩
  have hπfun_inj : Function.Injective πfun := by
    intro V W' h
    apply Subtype.ext
    exact σ.injective (congrArg Subtype.val h)
  have hπfun_surj : Function.Surjective πfun :=
    Finite.injective_iff_surjective.mp hπfun_inj
  let π : Equiv.Perm ↥c.supp := Equiv.ofBijective πfun ⟨hπfun_inj, hπfun_surj⟩
  have hπ_coe : ∀ V, (π V).1 = σ V.1 := fun V => rfl
  have hσ_invol : ∀ W' : s13IsoComps X, σ (σ W') = W' := by
    intro W'
    apply Subtype.ext
    have h1 : (σ (σ W')).1 = ((σ W').1).map t.toMonoidHom := hσsub (σ W')
    rw [h1, hσsub W', Subgroup.map_map]
    have hcomp : t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
      ext x
      change t (t x) = x
      rw [← MulAut.mul_apply, show t * t = 1 from by rw [← pow_two]; exact h.ht2]
      rfl
    rw [hcomp, Subgroup.map_id]
  have hπ_invol : ∀ V, π (π V) = V := by
    intro V
    apply Subtype.ext
    show σ (σ V.1) = V.1
    exact hσ_invol V.1
  have hmap_of_pi : ∀ V : ↥c.supp, (π V).1.1 = V.1.1.map t.toMonoidHom := by
    intro V
    rw [hπ_coe V, hσsub V.1]
  have hLnorm : ∀ y ∈ s13XSupp X (s13CompSet A X Q c),
      t * y * t⁻¹ ∈ s13XSupp X (s13CompSet A X Q c) :=
    fun y hy => w16g_conj_mem_s13XSupp h htMapC hy
  have hpres : ∀ y : ↥c.supp → ZMod 3, (∑ V, f V * y V) = 0 →
      (∑ V, f (π V) * ((cu V.1 : ZMod 3) * y V)) = 0 := by
    intro y hy
    obtain ⟨x, hx⟩ := (hfker y).mp hy
    let xX : ↥X := Subgroup.inclusion s13XSupp_le x
    have hxL : t * (xX : MulAut W) * t⁻¹ ∈ s13XSupp X (s13CompSet A X Q c) :=
      hLnorm (xX : MulAut W) x.2
    let x' : ↥(s13XSupp X (s13CompSet A X Q c)) := ⟨t * (xX : MulAut W) * t⁻¹, hxL⟩
    have hz : (∑ V, f V * lam V.1 (Additive.ofMul
        (Subgroup.inclusion s13XSupp_le x'))) = 0 :=
      (hfker _).mpr ⟨x', fun V => rfl⟩
    rw [← hz]
    rw [← Equiv.sum_comp π (fun W => f W * lam W.1 (Additive.ofMul
      (Subgroup.inclusion s13XSupp_le x')))]
    refine Finset.sum_congr rfl fun V _ => ?_
    have h1 : lam (σ V.1) (Additive.ofMul (w16g_conjOnX h xX)) =
        (cu V.1 : ZMod 3) * lam V.1 (Additive.ofMul xX) := by
      rw [show (w16g_conjOnX h xX : ↥X) = ⟨t * (xX : MulAut W) * t⁻¹,
        (w16g_conjOnX h xX).2⟩ from Subtype.ext rfl]
      exact hσcoord V.1 xX (w16g_conjOnX h xX).2
    have h2 : lam (π V).1 (Additive.ofMul (Subgroup.inclusion s13XSupp_le x')) =
        (cu V.1 : ZMod 3) * y V := by
      have h3 : (π V).1 = σ V.1 := rfl
      rw [h3]
      have hxeq : (Subgroup.inclusion s13XSupp_le x' : ↥X) = w16g_conjOnX h xX := by
        apply Subtype.ext
        rfl
      rw [hxeq, h1, ← hx V]
    rw [h2]
  have hεconst : ∀ i j : ↥c.supp, f (π i) * (cu i.1 : ZMod 3) * (f i)⁻¹ =
      f (π j) * (cu j.1 : ZMod 3) * (f j)⁻¹ :=
    w16g_const_of_preserves π f (fun V => (cu V.1 : ZMod 3)) hfne hpres
  have hsupp_sub : s13Supp X Q ⊆ s13CompSet A X Q c :=
    (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
  have hUc : U ∈ s13CompSet A X Q c := hsupp_sub (by rw [hsuppQ]; simp)
  have hU'c : U' ∈ s13CompSet A X Q c := hsupp_sub (by rw [hsuppQ]; simp)
  have hUmem : U ∈ s13IsoComps X := hCsub hUc
  have hU'mem : U' ∈ s13IsoComps X := hCsub hU'c
  have hUin : (⟨U, hUmem⟩ : s13IsoComps X) ∈ c.supp := by
    obtain ⟨W', hW', hW'U⟩ := hUc
    have : (⟨U, hUmem⟩ : s13IsoComps X) = W' := Subtype.ext hW'U.symm
    rw [this]; exact hW'
  have hU'in : (⟨U', hU'mem⟩ : s13IsoComps X) ∈ c.supp := by
    obtain ⟨W', hW', hW'U⟩ := hU'c
    have : (⟨U', hU'mem⟩ : s13IsoComps X) = W' := Subtype.ext hW'U.symm
    rw [this]; exact hW'
  let u : ↥c.supp := ⟨⟨U, hUmem⟩, hUin⟩
  let u' : ↥c.supp := ⟨⟨U', hU'mem⟩, hU'in⟩
  have hu : u ≠ u' := by
    intro hh
    apply hUU'
    exact congrArg (fun w : ↥c.supp => (w.1.1 : Subgroup W)) hh
  let ε : ZMod 3 := f (π u) * (cu u.1 : ZMod 3) * (f u)⁻¹
  have hεval : ∀ V : ↥c.supp, f (π V) * (cu V.1 : ZMod 3) * (f V)⁻¹ = ε :=
    fun V => hεconst V u
  obtain ⟨q, hq⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Q).mp
    (isCyclic_of_prime_card (p := 3) hQ3)
  have hqQ : q ∈ Q := hq ▸ Subgroup.mem_zpowers q
  have hsuppq : s13Supp X (Subgroup.zpowers q) = {U, U'} := by
    rw [hq, hsuppQ]
  have hqL : q ∈ s13XSupp X (s13CompSet A X Q c) := hQc hqQ
  let xq : ↥(s13XSupp X (s13CompSet A X Q c)) := ⟨q, hqL⟩
  let qX : ↥X := Subgroup.inclusion s13XSupp_le xq
  let m : ↥c.supp → ZMod 3 := fun V => f V * lam V.1 (Additive.ofMul qX)
  have hm_coe : (qX : MulAut W) = q := rfl
  have hmu : m u ≠ 0 := by
    have hcoord : lam u.1 (Additive.ofMul qX) ≠ 0 := by
      rw [coord_ne_zero_iff hl qX u.1]
      have hmem : U ∈ s13Supp X (Subgroup.zpowers q) := by rw [hsuppq]; simp
      exact hmem.2
    exact mul_ne_zero (hfne u) hcoord
  have hmu' : m u' ≠ 0 := by
    have hcoord : lam u'.1 (Additive.ofMul qX) ≠ 0 := by
      rw [coord_ne_zero_iff hl qX u'.1]
      have hmem : U' ∈ s13Supp X (Subgroup.zpowers q) := by rw [hsuppq]; simp
      exact hmem.2
    exact mul_ne_zero (hfne u') hcoord
  have hzero : ∀ v, v ≠ u → v ≠ u' → m v = 0 := by
    intro v hv hv'
    by_contra hne
    have hcoord : lam v.1 (Additive.ofMul qX) ≠ 0 := by
      intro h0
      exact hne (by simp [m, h0])
    have hmem : v.1.1 ∈ s13Supp X (Subgroup.zpowers q) :=
      ⟨v.1.2, (coord_ne_zero_iff hl qX v.1).mp hcoord⟩
    rw [hsuppq] at hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact hv (Subtype.ext (Subtype.ext h))
    · exact hv' (Subtype.ext (Subtype.ext (Set.mem_singleton_iff.mp h)))
  have hsum : m u + m u' = 0 := by
    have hsum0 : (∑ V, m V) = 0 :=
      (hfker (fun V => lam V.1 (Additive.ofMul qX))).mpr ⟨xq, fun V => rfl⟩
    rw [w16g_sum_eq_pair m hu hzero] at hsum0
    exact hsum0
  have hrel : ∀ (V : ↥c.supp) (x : ↥X),
      f (π V) * lam (π V).1 (Additive.ofMul (w16g_conjOnX h x)) =
        ε * (f V * lam V.1 (Additive.ofMul x)) := by
    intro V x
    have h1 : lam (σ V.1) (Additive.ofMul (w16g_conjOnX h x)) =
        (cu V.1 : ZMod 3) * lam V.1 (Additive.ofMul x) := by
      rw [show (w16g_conjOnX h x : ↥X) = ⟨t * (x : MulAut W) * t⁻¹,
        (w16g_conjOnX h x).2⟩ from Subtype.ext rfl]
      exact hσcoord V.1 x (w16g_conjOnX h x).2
    change f (π V) * lam (σ V.1) (Additive.ofMul (w16g_conjOnX h x)) =
      ε * (f V * lam V.1 (Additive.ofMul x))
    rw [h1, ← hεval V]
    have hfV : f V ≠ 0 := hfne V
    field_simp
  have hmul : ∀ V, ε * m V = - m (π V) := by
    intro V
    have h1 := hrel V qX
    have hconj : w16g_conjOnX h qX = qX⁻¹ := by
      apply Subtype.ext
      show t * (qX : MulAut W) * t⁻¹ = (qX : MulAut W)⁻¹
      rw [hm_coe, h.hQinv q hqQ]
    rw [hconj] at h1
    have h2 : lam (π V).1 (Additive.ofMul (qX⁻¹)) =
        - lam (π V).1 (Additive.ofMul qX) := by
      rw [ofMul_inv, map_neg]
    rw [h2, mul_neg] at h1
    change ε * (f V * lam V.1 (Additive.ofMul qX)) =
      -(f (π V) * lam (π V).1 (Additive.ofMul qX))
    exact h1.symm
  have hεsq : ε ^ 2 = 1 := by
    have h1 := hmul u
    have h2 := hmul (π u)
    rw [hπ_invol u] at h2
    have h3 : ε * (ε * m u) = m u := by rw [h1, mul_neg, h2, neg_neg]
    have h4 : (ε ^ 2 - 1) * m u = 0 := by
      rw [sub_mul, one_mul, sq, mul_assoc, h3, sub_self]
    have h5 : ε ^ 2 - 1 = 0 := (mul_eq_zero.mp h4).resolve_right hmu
    exact sub_eq_zero.mp h5
  have hεpm : ε = 1 ∨ ε = -1 := by
    have : ∀ e : ZMod 3, e ^ 2 = 1 → e = 1 ∨ e = -1 := by decide
    exact this ε hεsq
  have hdich := w16g_eps_pair π hπ_invol m u u' hu hmu hmu' hsum hzero ε hεpm hmul
  refine ⟨f, π, ε, hfne, hfker, hεpm, hmap_of_pi, hπ_invol, hrel, ?_, ?_⟩
  · intro he1
    obtain ⟨h1, h2⟩ := hdich.1 he1
    refine ⟨?_, ?_⟩
    · have := congrArg (fun w : ↥c.supp => (w.1.1 : Subgroup W)) h1
      rw [hmap_of_pi u] at this
      simpa [u, u'] using this
    · have := congrArg (fun w : ↥c.supp => (w.1.1 : Subgroup W)) h2
      rw [hmap_of_pi u'] at this
      simpa [u, u'] using this
  · intro he1
    obtain ⟨h1, h2⟩ := hdich.2 he1
    refine ⟨?_, ?_⟩
    · have := congrArg (fun w : ↥c.supp => (w.1.1 : Subgroup W)) h1
      rw [hmap_of_pi u] at this
      simpa [u, u'] using this
    · have := congrArg (fun w : ↥c.supp => (w.1.1 : Subgroup W)) h2
      rw [hmap_of_pi u'] at this
      simpa [u, u'] using this

private theorem w16g_dParam_three' : dParam 3 = 2 := by
  rw [dParam]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by decide) (by decide)

private theorem w16g_case_one_eps_neg (h : HAb A X Q t 3)
    (c : (s13SuppGraph A X Q).ConnectedComponent) [Fintype ↥c.supp]
    (hQc : Q ≤ s13XSupp X (s13CompSet A X Q c))
    (htMapC : (fun U : Subgroup W => U.map t.toMonoidHom) '' s13CompSet A X Q c =
      s13CompSet A X Q c)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam)
    {U U' : Subgroup W} (hUU' : U ≠ U') (hsuppQ : s13Supp X Q = {U, U'})
    {f : ↥c.supp → ZMod 3} {π : Equiv.Perm ↥c.supp} {ε : ZMod 3}
    (hfne : ∀ V, f V ≠ 0) (hε : ε = -1)
    (hmap_of_pi : ∀ V, (π V).1.1 = V.1.1.map t.toMonoidHom)
    (hπ_invol : ∀ V, π (π V) = V)
    (hrel : ∀ (V : ↥c.supp) (x : ↥X),
      f (π V) * lam (π V).1 (Additive.ofMul (w16g_conjOnX h x)) =
        ε * (f V * lam V.1 (Additive.ofMul x)))
    (hfixU : U.map t.toMonoidHom = U) (hfixU' : U'.map t.toMonoidHom = U')
    (hn : 3 ≤ (s13CompSet A X Q c).ncard) :
    (s13CompSet A X Q c).ncard = 3 ∧
      (∀ V ∈ s13CompSet A X Q c, rk ↥V = 2) ∧
      (∀ x ∈ s13XSupp X (s13CompSet A X Q c), t * x * t⁻¹ = x⁻¹) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hCsub : s13CompSet A X Q c ⊆ s13IsoComps X := by
    rintro V ⟨W', hW', rfl⟩
    exact W'.2
  have hsupp_sub : s13Supp X Q ⊆ s13CompSet A X Q c :=
    (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
  have hUc : U ∈ s13CompSet A X Q c := hsupp_sub (by rw [hsuppQ]; simp)
  have hU'c : U' ∈ s13CompSet A X Q c := hsupp_sub (by rw [hsuppQ]; simp)
  have hUmem : U ∈ s13IsoComps X := hCsub hUc
  have hU'mem : U' ∈ s13IsoComps X := hCsub hU'c
  have hUin : (⟨U, hUmem⟩ : s13IsoComps X) ∈ c.supp := by
    obtain ⟨W', hW', hW'U⟩ := hUc
    have : (⟨U, hUmem⟩ : s13IsoComps X) = W' := Subtype.ext hW'U.symm
    rw [this]; exact hW'
  have hU'in : (⟨U', hU'mem⟩ : s13IsoComps X) ∈ c.supp := by
    obtain ⟨W', hW', hW'U⟩ := hU'c
    have : (⟨U', hU'mem⟩ : s13IsoComps X) = W' := Subtype.ext hW'U.symm
    rw [this]; exact hW'
  let u : ↥c.supp := ⟨⟨U, hUmem⟩, hUin⟩
  let u' : ↥c.supp := ⟨⟨U', hU'mem⟩, hU'in⟩
  have hu : u ≠ u' := by
    intro hh
    exact hUU' (congrArg (fun w : ↥c.supp => (w.1.1 : Subgroup W)) hh)
  have hu_fix : π u = u := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hmap_of_pi u]
    show U.map t.toMonoidHom = U
    exact hfixU
  have hu'_fix : π u' = u' := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hmap_of_pi u']
    show U'.map t.toMonoidHom = U'
    exact hfixU'
  have hcard_supp : Fintype.card ↥c.supp = (s13CompSet A X Q c).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, s13CompSet]
    exact (Set.ncard_image_of_injective c.supp Subtype.val_injective).symm
  have hinv_at : ∀ (v : ↥c.supp), π v = v → ∀ (x : ↥X),
      lam v.1 (Additive.ofMul (w16g_conjOnX h x)) = - lam v.1 (Additive.ofMul x) := by
    intro v hv x
    have h1 := hrel v x
    rw [hv, hε] at h1
    have h3 : f v * lam v.1 (Additive.ofMul (w16g_conjOnX h x)) =
        f v * (- lam v.1 (Additive.ofMul x)) := by
      rw [mul_neg]
      simpa using h1
    exact mul_left_cancel₀ (hfne v) h3
  have hinv_fixed : ∀ V ∈ s13CompSet A X Q c, V.map t.toMonoidHom = V →
      ∀ x ∈ X, t * x * t⁻¹ * x ∈ s13KerOn X V := by
    intro V hV hVfix x hxX
    have hVmem : V ∈ s13IsoComps X := hCsub hV
    have hvin : (⟨V, hVmem⟩ : s13IsoComps X) ∈ c.supp := by
      obtain ⟨W', hW', hW'V⟩ := hV
      have : (⟨V, hVmem⟩ : s13IsoComps X) = W' := Subtype.ext hW'V.symm
      rw [this]; exact hW'
    let v : ↥c.supp := ⟨⟨V, hVmem⟩, hvin⟩
    have hpiv : π v = v := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hmap_of_pi v]
      show V.map t.toMonoidHom = V
      exact hVfix
    have h2 := hinv_at v hpiv ⟨x, hxX⟩
    have h4 : lam v.1 (Additive.ofMul (w16g_conjOnX h ⟨x, hxX⟩ * ⟨x, hxX⟩)) = 0 := by
      rw [ofMul_mul, map_add, h2, neg_add_cancel]
    have h5 : ((w16g_conjOnX h ⟨x, hxX⟩ * ⟨x, hxX⟩ : ↥X) : MulAut W) ∈
        s13KerOn X V := ((hl v.1).2 _).mp h4
    exact h5
  have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have hcost := s13_cost_eq (X := X) h.hW (p := 3) (Or.inl rfl) h.hXe ht2'
    (fun x hx => h.hXA t h.htA x hx) hCsub
    (fun V hV => by rw [← htMapC]; exact ⟨V, hV, rfl⟩)
    (fun V hV hVfix => ⟨rfl, hinv_fixed V hV hVfix⟩)
  haveI : Fintype ↥(s13CompSet A X Q c) := Fintype.ofFinite _
  have h2rk : ∀ V : ↥(s13CompSet A X Q c), 2 ≤ rk ↥(V.1 : Subgroup W) := by
    intro V
    obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hXe (hCsub V.2)
    rw [w16g_dParam_three'] at hsrk
    omega
  have hsum_eq : (∑ᶠ V ∈ s13CompSet A X Q c, rk ↥V) =
      ∑ V : ↥(s13CompSet A X Q c), rk ↥(V.1 : Subgroup W) := by
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  have hsum_ge : 2 * (s13CompSet A X Q c).ncard ≤
      ∑ V : ↥(s13CompSet A X Q c), rk ↥(V.1 : Subgroup W) := by
    have h1 : (∑ _ : ↥(s13CompSet A X Q c), (2 : ℕ)) ≤
        ∑ V : ↥(s13CompSet A X Q c), rk ↥(V.1 : Subgroup W) :=
      Finset.sum_le_sum fun V _ => h2rk V
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      show Fintype.card ↥(s13CompSet A X Q c) = (s13CompSet A X Q c).ncard from
        (Nat.card_eq_fintype_card (α := ↥(s13CompSet A X Q c))).symm.trans
          (Nat.card_coe_set_eq _)] at h1
    simpa [Nat.mul_comm] using h1
  have hrk_le : rk ↥(commSub (⨆ V ∈ s13CompSet A X Q c, V) (Subgroup.zpowers t)) ≤ 3 :=
    le_trans (rk_mono (commSub_mono le_top le_rfl)) h.hrk
  have htotal : 2 * (s13CompSet A X Q c).ncard ≤ 6 := by
    calc 2 * (s13CompSet A X Q c).ncard
        ≤ 2 * rk ↥(commSub (⨆ V ∈ s13CompSet A X Q c, V) (Subgroup.zpowers t)) := by
          rw [hcost, hsum_eq]; exact hsum_ge
      _ ≤ 2 * 3 := by gcongr
  have hn_le : (s13CompSet A X Q c).ncard ≤ 3 := by omega
  have hn_eq : (s13CompSet A X Q c).ncard = 3 := le_antisymm hn_le hn
  have hcard3 : Fintype.card ↥c.supp = 3 := hcard_supp.trans hn_eq
  have hall_fixed : ∀ v : ↥c.supp, π v = v := by
    intro v
    by_contra hne
    have hu_ne_v : u ≠ v := fun h => hne (by rw [← h, hu_fix])
    have hu'_ne_v : u' ≠ v := fun h => hne (by rw [← h, hu'_fix])
    have hπv_ne_u : π v ≠ u := fun h => hu_ne_v (by rw [← hπ_invol v, h, hu_fix])
    have hπv_ne_u' : π v ≠ u' := fun h => hu'_ne_v (by rw [← hπ_invol v, h, hu'_fix])
    have hnu : u ∉ ({u', v, π v} : Finset ↥c.supp) := by
      intro hmem
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hu h
      · exact hu_ne_v h
      · exact hπv_ne_u h.symm
    have hnu' : u' ∉ ({v, π v} : Finset ↥c.supp) := by
      intro hmem
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hu'_ne_v h
      · exact hπv_ne_u' h.symm
    have hnv : v ∉ ({π v} : Finset ↥c.supp) := by
      intro hmem
      rw [Finset.mem_singleton] at hmem
      exact hne hmem.symm
    have hcard4 : ({u, u', v, π v} : Finset ↥c.supp).card = 4 := by
      rw [Finset.card_insert_of_notMem hnu, Finset.card_insert_of_notMem hnu',
        Finset.card_insert_of_notMem hnv, Finset.card_singleton]
    have hle := Finset.card_le_univ ({u, u', v, π v} : Finset ↥c.supp)
    rw [hcard4, hcard3] at hle
    omega
  have hsum6 : ∑ V : ↥(s13CompSet A X Q c), rk ↥(V.1 : Subgroup W) = 6 := by
    have hle : ∑ V : ↥(s13CompSet A X Q c), rk ↥(V.1 : Subgroup W) ≤ 6 := by
      rw [← hsum_eq, ← hcost]
      omega
    rw [hn_eq] at hsum_ge
    omega
  have hrk_two : ∀ V ∈ s13CompSet A X Q c, rk ↥V = 2 := by
    intro V hV
    have hconst : (∑ _ : ↥(s13CompSet A X Q c), (2 : ℕ)) = 6 := by
      have hc : Fintype.card ↥(s13CompSet A X Q c) = 3 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact hn_eq
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hc]
    have heq : (∑ U : ↥(s13CompSet A X Q c), rk ↥(U.1 : Subgroup W)) =
        ∑ _ : ↥(s13CompSet A X Q c), (2 : ℕ) := by rw [hsum6, hconst]
    exact ((Finset.sum_eq_sum_iff_of_le (fun V _ => h2rk V)).mp heq.symm ⟨V, hV⟩
      (Finset.mem_univ _)).symm
  have hall_map : ∀ V ∈ s13CompSet A X Q c, V.map t.toMonoidHom = V := by
    intro V hV
    have hVmem : V ∈ s13IsoComps X := hCsub hV
    have hvin : (⟨V, hVmem⟩ : s13IsoComps X) ∈ c.supp := by
      obtain ⟨W', hW', hW'V⟩ := hV
      have : (⟨V, hVmem⟩ : s13IsoComps X) = W' := Subtype.ext hW'V.symm
      rw [this]; exact hW'
    let v : ↥c.supp := ⟨⟨V, hVmem⟩, hvin⟩
    have h1 := hmap_of_pi v
    rw [hall_fixed v] at h1
    exact h1.symm
  have hinvL : ∀ x ∈ s13XSupp X (s13CompSet A X Q c), t * x * t⁻¹ = x⁻¹ := by
    intro x hxL
    have hxX : x ∈ X := s13XSupp_le hxL
    have hconjL : t * x * t⁻¹ ∈ s13XSupp X (s13CompSet A X Q c) :=
      w16g_conj_mem_s13XSupp h htMapC hxL
    have hconjX : t * x * t⁻¹ ∈ X := s13XSupp_le hconjL
    let xX : ↥X := ⟨x, hxX⟩
    let yX : ↥X := ⟨t * x * t⁻¹, hconjX⟩
    have hcoord : ∀ U : s13IsoComps X,
        lam U (Additive.ofMul yX) = lam U (Additive.ofMul xX⁻¹) := by
      intro U
      by_cases hUC : (U : Subgroup W) ∈ s13CompSet A X Q c
      · have hUmem : (U : Subgroup W) ∈ s13IsoComps X := U.2
        have hUin : (⟨(U : Subgroup W), hUmem⟩ : s13IsoComps X) ∈ c.supp := by
          obtain ⟨W', hW', hW'U⟩ := hUC
          have : (⟨(U : Subgroup W), hUmem⟩ : s13IsoComps X) = W' := Subtype.ext hW'U.symm
          rw [this]; exact hW'
        let v : ↥c.supp := ⟨⟨(U : Subgroup W), hUmem⟩, hUin⟩
        have h2 := hinv_at v (hall_fixed v) xX
        have hy : yX = w16g_conjOnX h xX := Subtype.ext rfl
        rw [hy, h2, ofMul_inv, map_neg]
      · have hy0 : lam U (Additive.ofMul yX) = 0 :=
          ((hl U).2 _).mpr ((mem_s13XSupp.mp hconjL).2 U.1 U.2 hUC)
        have hx0 : lam U (Additive.ofMul xX) = 0 :=
          ((hl U).2 _).mpr ((mem_s13XSupp.mp hxL).2 U.1 U.2 hUC)
        rw [hy0, ofMul_inv, map_neg, hx0, neg_zero]
    have hxy : yX = xX⁻¹ := coord_injective h.hW hp3 hp32 h.hXe hl hcoord
    exact congrArg (fun z : ↥X => (z : MulAut W)) hxy
  exact ⟨hn_eq, hrk_two, hinvL⟩


private theorem w16g_two_cost_le (h : HAb A X Q t 3) {C : Set (Subgroup W)} {P R : Subgroup W}
    (hdisj : Disjoint P R) (hPs : ∀ a ∈ P, t a ∈ P) (hRs : ∀ b ∈ R, t b ∈ R)
    (hle : P ⊔ R ≤ ⨆ V ∈ C, V) :
    rk ↥(commSub P (Subgroup.zpowers t)) + rk ↥(commSub R (Subgroup.zpowers t)) ≤
      rk ↥(commSub (⨆ V ∈ C, V) (Subgroup.zpowers t)) := by
  classical
  let F : Fin 2 → Subgroup W := fun i => if i = 0 then P else R
  have hF0 : F 0 = P := by simp [F]
  have hF1 : F 1 = R := by simp [F]
  have hF_indep : iSupIndep F := by
    apply (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
      (fun k => by fin_cases k <;> simp)).mpr
    rw [hF0, hF1]
    exact hdisj
  have hF_stable : ∀ i, ∀ u ∈ F i, t u ∈ F i := by
    intro i
    fin_cases i
    · change ∀ u ∈ F 0, t u ∈ F 0
      rw [hF0]; exact hPs
    · change ∀ u ∈ F 1, t u ∈ F 1
      rw [hF1]; exact hRs
  have hsum := rk_commSub_iSup_eq_sum h.hW t F hF_indep hF_stable
  rw [Fin.sum_univ_two, hF0, hF1] at hsum
  have hsup : (⨆ i, F i) = P ⊔ R := by
    rw [← Finset.sup_univ_eq_iSup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl,
      Finset.sup_insert, Finset.sup_singleton, hF0, hF1]
  rw [← hsum, hsup]
  exact rk_mono (commSub_mono hle le_rfl)


private theorem w16g_case_one_eps_one (h : HAb A X Q t 3)
    (c : (s13SuppGraph A X Q).ConnectedComponent) [Fintype ↥c.supp]
    (hQc : Q ≤ s13XSupp X (s13CompSet A X Q c))
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam)
    {U U' : Subgroup W} (hUU' : U ≠ U') (hsuppQ : s13Supp X Q = {U, U'})
    (he2 : (s13Supp X Q).ncard = 2)
    {f : ↥c.supp → ZMod 3} {π : Equiv.Perm ↥c.supp} {ε : ZMod 3}
    (hfne : ∀ V, f V ≠ 0) (hε : ε = 1)
    (hmap_of_pi : ∀ V, (π V).1.1 = V.1.1.map t.toMonoidHom)
    (hrel : ∀ (V : ↥c.supp) (x : ↥X),
      f (π V) * lam (π V).1 (Additive.ofMul (w16g_conjOnX h x)) =
        ε * (f V * lam V.1 (Additive.ofMul x)))
    (hswapU : U.map t.toMonoidHom = U') (hswapU' : U'.map t.toMonoidHom = U) :
    rk ↥U = 2 ∧ ∀ v : ↥c.supp, v.1.1 ≠ U → v.1.1 ≠ U' →
      commSub v.1.1 (Subgroup.zpowers t) = ⊥ := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have hsX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx => h.hXA t h.htA x hx
  have hCsub : s13CompSet A X Q c ⊆ s13IsoComps X := by
    rintro V ⟨W', hW', rfl⟩
    exact W'.2
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian_three h.hXe
  have hsSupC : sSupIndep (s13CompSet A X Q c) :=
    (s13IsoComps_sSupIndep h.hW hodd).mono hCsub
  have hsupp_sub : s13Supp X Q ⊆ s13CompSet A X Q c :=
    (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
  have hUc : U ∈ s13CompSet A X Q c := hsupp_sub (by rw [hsuppQ]; simp)
  have hU'c : U' ∈ s13CompSet A X Q c := hsupp_sub (by rw [hsuppQ]; simp)
  have hUmem : U ∈ s13IsoComps X := hCsub hUc
  have hU'mem : U' ∈ s13IsoComps X := hCsub hU'c
  have hdisjC : ∀ {P R : Subgroup W}, P ∈ s13CompSet A X Q c → R ∈ s13CompSet A X Q c →
      P ≠ R → Disjoint P R := by
    intro P R hP hR hPR
    have h := hsSupC.disjoint_sSup hP
      (fun V (hV : V ∈ s13CompSet A X Q c \ {P}) => hV.1) (by simp)
    exact h.mono_right (le_sSup (show R ∈ s13CompSet A X Q c \ {P} from
      ⟨hR, by simpa [Set.mem_singleton_iff] using hPR.symm⟩))
  have hUU'_disj : U ⊓ U' = ⊥ := by
    rw [← disjoint_iff]
    exact hdisjC hUc hU'c hUU'
  have hpaircost : rk ↥(commSub (U ⊔ U') (Subgroup.zpowers t)) = rk ↥U :=
    (rk_commSub_swap h.hW ht2' hswapU.symm hUU'_disj).2
  have hrkU_le : rk ↥U ≤ 3 := by
    rw [← hpaircost]
    exact le_trans (rk_mono (commSub_mono le_top le_rfl)) h.hrk
  have hrkU_two : rk ↥U = 2 := by
    have hrank := (s13_three_ranks h).2 he2 U (by rw [hsuppQ]; simp)
    omega
  have hrkC_le : rk ↥(commSub (⨆ V ∈ s13CompSet A X Q c, V) (Subgroup.zpowers t)) ≤ 3 :=
    le_trans (rk_mono (commSub_mono le_top le_rfl)) h.hrk
  have hAs : ∀ a ∈ U ⊔ U', t a ∈ U ⊔ U' := by
    intro a ha
    rcases Subgroup.mem_sup.mp ha with ⟨b, hb, c, hc, rfl⟩
    have hb' : t b ∈ U ⊔ U' := by
      have h1 : t b ∈ U.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hb
      rw [hswapU] at h1
      exact Subgroup.mem_sup_right h1
    have hc' : t c ∈ U ⊔ U' := by
      have h1 : t c ∈ U'.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hc
      rw [hswapU'] at h1
      exact Subgroup.mem_sup_left h1
    rw [map_mul]
    exact Subgroup.mul_mem _ hb' hc'
  have hle_pair : ∀ {P : Subgroup W}, P ∈ s13CompSet A X Q c →
      (U ⊔ U') ⊔ P ≤ ⨆ V ∈ s13CompSet A X Q c, V := by
    intro P hP
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup_of_le U (le_iSup_of_le hUc le_rfl)
    · exact le_iSup_of_le U' (le_iSup_of_le hU'c le_rfl)
    · exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)
  have hsubUU' : ∀ R ∈ ({U, U'} : Set (Subgroup W)), R ∈ s13CompSet A X Q c := by
    intro R hR
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with rfl | rfl
    · exact hUc
    · exact hU'c
  have hdisj_pair : ∀ {P : Subgroup W}, P ∈ s13CompSet A X Q c → P ≠ U → P ≠ U' →
      Disjoint (U ⊔ U') P := by
    intro P hP hPU hPU'
    have hnot : P ∉ ({U, U'} : Set (Subgroup W)) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      push Not
      exact ⟨hPU, hPU'⟩
    have h := hsSupC.disjoint_sSup hP hsubUU' hnot
    rw [sSup_pair] at h
    exact h.symm
  have hfixed_le : ∀ v : ↥c.supp, v.1.1 ≠ U → v.1.1 ≠ U' →
      v.1.1.map t.toMonoidHom = v.1.1 → rk ↥(commSub v.1.1 (Subgroup.zpowers t)) ≤ 1 := by
    intro v hvU hvU' hvfix
    have hvc : v.1.1 ∈ s13CompSet A X Q c := ⟨v.1, v.2, rfl⟩
    have hVst : ∀ b ∈ v.1.1, t b ∈ v.1.1 := by
      intro b hb
      have h1 : t b ∈ v.1.1.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hb
      rwa [hvfix] at h1
    have hcostle := w16g_two_cost_le h (hdisj_pair hvc hvU hvU') hAs hVst (hle_pair hvc)
    rw [hpaircost] at hcostle
    omega
  have hcent_of_fixed : ∀ v : ↥c.supp, π v = v → ∀ x ∈ X,
      t * x * t⁻¹ * x⁻¹ ∈ s13KerOn X v.1.1 := by
    intro v hv x hxX
    have h1 := hrel v ⟨x, hxX⟩
    rw [hv, hε] at h1
    have h3 : f v * lam v.1 (Additive.ofMul (w16g_conjOnX h ⟨x, hxX⟩)) =
        f v * lam v.1 (Additive.ofMul ⟨x, hxX⟩) := by simpa using h1
    have h2 : lam v.1 (Additive.ofMul (w16g_conjOnX h ⟨x, hxX⟩)) =
        lam v.1 (Additive.ofMul ⟨x, hxX⟩) := mul_left_cancel₀ (hfne v) h3
    have h4 : lam v.1 (Additive.ofMul (w16g_conjOnX h ⟨x, hxX⟩ * ⟨x, hxX⟩⁻¹)) = 0 := by
      rw [ofMul_mul, ofMul_inv, map_add, map_neg, h2]
      abel
    exact ((hl v.1).2 _).mp h4
  have hcomp : t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
    ext x
    change t (t x) = x
    rw [← MulAut.mul_apply, ht2', MulAut.one_apply]
  have hπ_invol : ∀ V : ↥c.supp, π (π V) = V := by
    intro V
    apply Subtype.ext
    apply Subtype.ext
    rw [hmap_of_pi (π V), hmap_of_pi V, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hno_swap : ∀ v : ↥c.supp, v.1.1 ≠ U → v.1.1 ≠ U' → π v = v := by
    intro v hvU hvU'
    by_contra hne
    let w : ↥c.supp := π v
    have hvw' : v.1.1 ≠ w.1.1 := fun h => hne (Subtype.ext (Subtype.ext h.symm))
    have hvc : v.1.1 ∈ s13CompSet A X Q c := ⟨v.1, v.2, rfl⟩
    have hwc : w.1.1 ∈ s13CompSet A X Q c := ⟨w.1, w.2, rfl⟩
    have hwU : w.1.1 ≠ U := by
      intro hw
      have h1 : v.1.1.map t.toMonoidHom = U := by rw [← hmap_of_pi v]; exact hw
      have h3 := congrArg (Subgroup.map t.toMonoidHom) h1
      rw [Subgroup.map_map, hcomp, Subgroup.map_id, hswapU] at h3
      exact hvU' h3
    have hwU' : w.1.1 ≠ U' := by
      intro hw
      have h1 : v.1.1.map t.toMonoidHom = U' := by rw [← hmap_of_pi v]; exact hw
      have h3 := congrArg (Subgroup.map t.toMonoidHom) h1
      rw [Subgroup.map_map, hcomp, Subgroup.map_id, hswapU'] at h3
      exact hvU h3
    have hwfix : v.1.1 = w.1.1.map t.toMonoidHom := by
      rw [← hmap_of_pi w]
      rw [show w = π v from rfl, hπ_invol v]
    have hdisj_vw : v.1.1 ⊓ w.1.1 = ⊥ := by
      rw [← disjoint_iff]
      exact hdisjC hvc hwc hvw'
    have hpaircost_swap :
        rk ↥(commSub (v.1.1 ⊔ w.1.1) (Subgroup.zpowers t)) = rk ↥v.1.1 :=
      (rk_commSub_swap h.hW ht2' (hmap_of_pi v) hdisj_vw).2
    have hdisj_vw_Upair : Disjoint (v.1.1 ⊔ w.1.1) (U ⊔ U') := by
      let s : Finset (Subgroup W) :=
        ({v.1.1, w.1.1} : Finset (Subgroup W)) ∪ ({U, U'} : Finset (Subgroup W))
      have hTmem : ∀ x ∈ s, x ∈ s13CompSet A X Q c := by
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hvc
          · exact hwc
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hUc
          · exact hU'c
      have hSupIndep : s.SupIndep id := by
        have h1 : sSupIndep (s : Set (Subgroup W)) := hsSupC.mono hTmem
        have h2 : iSupIndep ((↑) : s → Subgroup W) := (sSupIndep_iff _).mp h1
        have h3 : iSupIndep ((fun U : Subgroup W => U) ∘ ((↑) : s → Subgroup W)) := h2
        exact (iSupIndep_comp_coe_iff_supIndep).mp h3
      have huv : Disjoint ({v.1.1, w.1.1} : Finset (Subgroup W))
          ({U, U'} : Finset (Subgroup W)) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hvU hab
        · exact hvU' hab
        · exact hwU hab
        · exact hwU' hab
      have h := Finset.SupIndep.disjoint_sup_sup hSupIndep
        Finset.subset_union_left Finset.subset_union_right huv
      simpa using h
    have hPst : ∀ a ∈ v.1.1 ⊔ w.1.1, t a ∈ v.1.1 ⊔ w.1.1 := by
      intro a ha
      rcases Subgroup.mem_sup.mp ha with ⟨b, hb, c', hc', rfl⟩
      have hb' : t b ∈ v.1.1 ⊔ w.1.1 := by
        have h1 : t b ∈ w.1.1 := by
          rw [hmap_of_pi v]
          exact Subgroup.mem_map_of_mem _ hb
        exact Subgroup.mem_sup_right h1
      have hc' : t c' ∈ v.1.1 ⊔ w.1.1 := by
        have h1 : t c' ∈ v.1.1 := by
          rw [hwfix]
          exact Subgroup.mem_map_of_mem _ hc'
        exact Subgroup.mem_sup_left h1
      rw [map_mul]
      exact Subgroup.mul_mem _ hb' hc'
    have hle_vw : (v.1.1 ⊔ w.1.1) ⊔ (U ⊔ U') ≤
        ⨆ V ∈ s13CompSet A X Q c, V := by
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · exact le_iSup_of_le v.1.1 (le_iSup_of_le hvc le_rfl)
      · exact le_iSup_of_le w.1.1 (le_iSup_of_le hwc le_rfl)
      · exact le_iSup_of_le U (le_iSup_of_le hUc le_rfl)
      · exact le_iSup_of_le U' (le_iSup_of_le hU'c le_rfl)
    have hcost_swap := w16g_two_cost_le h hdisj_vw_Upair hPst hAs hle_vw
    rw [hpaircost_swap, hpaircost] at hcost_swap
    have h2rk_v : 2 ≤ rk ↥v.1.1 := by
      obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hXe (hCsub hvc)
      rw [w16g_dParam_three'] at hsrk
      omega
    omega
  exact ⟨hrkU_two, fun v hvU hvU' => by
    have hvfix := hno_swap v hvU hvU'
    have hvc : v.1.1 ∈ s13CompSet A X Q c := ⟨v.1, v.2, rfl⟩
    have hVst : ∀ b ∈ v.1.1, t b ∈ v.1.1 := by
      intro b hb
      have h1 : t b ∈ v.1.1.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hb
      rw [← hmap_of_pi v, hvfix] at h1
      exact h1
    have hle1 := hfixed_le v hvU hvU' (by rw [← hmap_of_pi v, hvfix])
    have heven := even_rk_commSub_fixed_central h.hW h.hXe ht2' hsX (hCsub hvc) hVst
      (hcent_of_fixed v hvfix)
    have hzero : rk ↥(commSub v.1.1 (Subgroup.zpowers t)) = 0 := by
      obtain ⟨m, hm⟩ := heven
      omega
    exact (rk_eq_zero_iff (fun y => by rw [pow_two]; exact h.hW y)).mp hzero⟩


private theorem w16g_compSet_conj_self (h : HAb A X Q t 3) (hQ3 : Nat.card ↥Q = 3)
    (he : (s13Supp X Q).ncard = 2) (c : (s13SuppGraph A X Q).ConnectedComponent)
    (hQc : Q ≤ s13XSupp X (s13CompSet A X Q c)) :
    (fun U : Subgroup W => U.map t.toMonoidHom) '' s13CompSet A X Q c =
      s13CompSet A X Q c := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hQmap1 : Q.map (MulAut.conj t).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      change (MulAut.conj t) q ∈ Q
      rw [MulAut.conj_apply, h.hQinv q hq]
      exact Q.inv_mem hq
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  rcases w16g_s13CompSet_conj_disjoint_or_eq h.hXA h.htA c with heq | hdis
  · exact heq
  · exfalso
    have hsupp_sub : s13Supp X Q ⊆ s13CompSet A X Q c :=
      (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
    have hUne : (s13Supp X Q).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      rw [hemp] at he
      simp at he
    obtain ⟨W₀, hW₀⟩ := hUne
    have hW₀c : W₀ ∈ s13CompSet A X Q c := hsupp_sub hW₀
    have hW₀t : W₀.map t.toMonoidHom ∈ s13CompSet A X Q c := by
      have h1 : W₀.map t.toMonoidHom ∈
          s13Supp X (Q.map (MulAut.conj t).toMonoidHom) := by
        rw [s13Supp_conj (fun x hx => h.hXA t h.htA x hx)
          (by simpa using h.hXA t⁻¹ (A.inv_mem h.htA))]
        exact ⟨W₀, hW₀, rfl⟩
      rw [hQmap1] at h1
      exact hsupp_sub h1
    exact (Set.disjoint_left.mp hdis) ⟨W₀, hW₀c, rfl⟩ hW₀t

theorem w16g_s13_three_case_one_large (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 2)
    (c : (s13SuppGraph A X Q).ConnectedComponent)
    (hn : 3 ≤ (s13CompSet A X Q c).ncard)
    (hQc : Q ≤ s13XSupp X (s13CompSet A X Q c)) :
    Conc4_133 A t (s13XSupp X (s13CompSet A X Q c)) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian_three h.hXe
  have h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2 := by
    intro a ha
    have hconj := s13Supp_conj (X := X) (L := Q) (g := a)
      (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha))
    rw [hconj, Set.ncard_image_of_injective _ (Subgroup.map_injective a.injective)]
    exact he
  obtain ⟨hedge_all, -, -, hcomp⟩ := s13_graph_decomp h hQ3 h2
  let C : Set (Subgroup W) := s13CompSet A X Q c
  let L : Subgroup (MulAut W) := s13XSupp X C
  have hCsub : C ⊆ s13IsoComps X := by
    rintro U ⟨W', hW', rfl⟩
    exact W'.2
  have hCne : C.Nonempty := (Set.ncard_pos (Set.toFinite C)).mp
    (lt_of_lt_of_le (by norm_num : 0 < 3) hn)
  have hLle : L ≤ X := s13XSupp_le
  have hLsupp : s13Supp X L = C := (hcomp c).1
  have hLlt : Nat.card ↥L < 3 ^ C.ncard :=
    s13_card_XSupp_lt h.hW (p := 3) hp3 hp32 h.hXe hH0 hCsub hCne
  have hLpgroup : IsPGroup 3 ↥L := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (h.hXe.2 x.1 (hLle x.2))⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hLpgroup
  obtain ⟨-, hlow, -⟩ := hcomp c
  have hk_le : C.ncard - 1 ≤ k := by
    rw [hk] at hlow
    exact (Nat.pow_le_pow_iff_right (show (1:ℕ) < 3 by norm_num)).mp hlow
  have hk_lt : k < C.ncard := by
    rw [hk] at hLlt
    exact (Nat.pow_lt_pow_iff_right (show (1:ℕ) < 3 by norm_num)).mp hLlt
  have hk_eq : k = C.ncard - 1 := by omega
  have hLcard : Nat.card ↥L = 3 ^ (C.ncard - 1) := by rw [hk, hk_eq]
  have hrank : IsElemAbelianOfRank 3 (C.ncard - 1) ↥L :=
    w16g_isElemAbelianOfRank_of_card
      (fun a b : ↥L => Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W))
        (h.hXe.1.is_comm.comm ⟨a.1, hLle a.2⟩ ⟨b.1, hLle b.2⟩)))
      (fun a : ↥L => Subtype.ext (by simpa using h.hXe.2 a.1 (hLle a.2)))
      hLcard
  have hcomm_eq : commSub ⊤ L = ⨆ U : ↥C, (U.1 : Subgroup W) := by
    rw [commSub_top_eq_iSup_s13Supp h.hW (p := 3) hp3 hp32 h.hXe hLle, hLsupp]
    exact iSup_subtype' (p := fun U => U ∈ C) (f := fun U (_ : U ∈ C) => U)
  have hindC : iSupIndep (fun U : ↥C => (U.1 : Subgroup W)) :=
    (sSupIndep_iff C).mp ((s13IsoComps_sSupIndep h.hW hodd).mono hCsub)
  have hQL : Q ≤ L := hQc
  have hLcomm : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
      by_contra hc
      push Not at hc
      exact h.hQ1 (le_bot_iff.mp (fun q hq => Subgroup.mem_bot.mpr (hc q hq)))
    have hqL : q ∈ L := hQL hqQ
    have hq2 : q ^ 2 ≠ 1 := by
      intro hq2
      have hdvd3 : orderOf q ∣ 3 :=
        orderOf_dvd_iff_pow_eq_one.mpr (h.hXe.2 q (h.hQX hqQ))
      have hdvd2 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2
      have hd : orderOf q ∣ Nat.gcd 3 2 := Nat.dvd_gcd hdvd3 hdvd2
      rw [show Nat.gcd 3 2 = 1 from by norm_num] at hd
      exact hq1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
    have htq' : t * q⁻¹ * t⁻¹ = q := by
      calc t * q⁻¹ * t⁻¹ = (t * q * t⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]; group
        _ = (q⁻¹)⁻¹ := by rw [h.hQinv q hqQ]
        _ = q := inv_inv q
    have hcommq : ⁅q, t⁆ = q ^ 2 := by
      rw [commutatorElement_def]
      calc q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) := by group
        _ = q * q := by rw [htq']
        _ = q ^ 2 := by rw [pow_two]
    have hmem : ⁅q, t⁆ ∈ ⁅L, Subgroup.zpowers t⁆ :=
      Subgroup.commutator_mem_commutator hqL (Subgroup.mem_zpowers t)
    rw [hbot] at hmem
    exact hq2 (hcommq ▸ Subgroup.mem_bot.mp hmem)
  have hdisj : ∀ g ∈ A, s13Supp X (L.map (MulAut.conj g).toMonoidHom) = s13Supp X L ∨
      Disjoint (s13Supp X (L.map (MulAut.conj g).toMonoidHom)) (s13Supp X L) := by
    intro g hg
    have hconj : s13Supp X (L.map (MulAut.conj g).toMonoidHom) =
        (fun U : Subgroup W => U.map g.toMonoidHom) '' C := by
      rw [w16g_s13Supp_conj (h.hXA g hg) (by simpa using h.hXA g⁻¹ (A.inv_mem hg)), hLsupp]
    rw [hconj, hLsupp]
    exact w16g_s13CompSet_conj_disjoint_or_eq h.hXA hg c
  have hind : sSupIndep (conjSubs A (commSub ⊤ L)) :=
    sSupIndep_conjSubs_of_s13Supp h.hW (p := 3) hp3 hp32 h.hXe h.hXA hLle hdisj
  obtain ⟨U, U', hUU', hsuppQ⟩ := Set.ncard_eq_two.mp he
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype ↥c.supp := Fintype.ofFinite _
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp3 hp32 h.hXe
  obtain ⟨f, π, ε, hfne, -, hεpm, hmap_of_pi, hπ_invol, hrel, hε1_dich, hεm1_dich⟩ :=
    w16g_case_one_sign h hH0 hQ3 he c hQc hl hUU' hsuppQ
  refine ⟨3, hp3, hLle.trans h.hXO, hLcomm, hind, ?_⟩
  by_cases hε1 : ε = 1
  ·
    obtain ⟨hswapU, hswapU'⟩ := hε1_dich hε1
    obtain ⟨hrkU_two, hcent⟩ :=
      w16g_case_one_eps_one h c hQc hl hUU' hsuppQ he hfne hε1 hmap_of_pi hrel hswapU hswapU'
    have hsupp_sub : s13Supp X Q ⊆ C :=
      (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
    have hUC : U ∈ C := hsupp_sub (by rw [hsuppQ]; simp)
    have hU'C : U' ∈ C := hsupp_sub (by rw [hsuppQ]; simp)
    have hcentC : ∀ V ∈ C, V ≠ U → V ≠ U' →
        commSub V (Subgroup.zpowers t) = ⊥ := by
      intro V hV hVU hVU'
      have hVmem : V ∈ s13IsoComps X := hCsub hV
      obtain ⟨k, hk, hkval⟩ := hV
      have hkin : (⟨V, hVmem⟩ : ↥(s13IsoComps X)) ∈ c.supp := by
        have : (⟨V, hVmem⟩ : ↥(s13IsoComps X)) = k := Subtype.ext hkval.symm
        rw [this]; exact hk
      exact hcent ⟨⟨V, hVmem⟩, hkin⟩ hVU hVU'
    have hrkU'_two : rk ↥U' = 2 := by
      have h := CFSG.RankThree.S4Free.Stell.rk_map_mulAut t U'
      rw [hswapU'] at h
      exact h.symm.trans hrkU_two
    have hrk2C : ∀ V ∈ C, rk ↥V = 2 := by
      intro V hV
      obtain ⟨V', hAdj⟩ := hedge_all ⟨V, hCsub hV⟩
      rw [s13SuppGraph, SimpleGraph.fromRel_adj] at hAdj
      obtain ⟨-, hrel⟩ := hAdj
      rcases hrel with ⟨a, ha, hsupp⟩ | ⟨a, ha, hsupp⟩
      · have hset : ({V, V'.1} : Set (Subgroup W)) =
            {U.map a.toMonoidHom, U'.map a.toMonoidHom} :=
          hsupp.symm.trans (by
            rw [s13Supp_conj (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha)),
              hsuppQ, Set.image_pair])
        have hmem : V ∈ ({U.map a.toMonoidHom, U'.map a.toMonoidHom} : Set (Subgroup W)) := by
          rw [← hset]; simp
        rcases Set.mem_insert_iff.mp hmem with h | h
        · rw [h, CFSG.RankThree.S4Free.Stell.rk_map_mulAut]; exact hrkU_two
        · rw [Set.mem_singleton_iff.mp h, CFSG.RankThree.S4Free.Stell.rk_map_mulAut]
          exact hrkU'_two
      · rw [Set.pair_comm] at hsupp
        have hset : ({V, V'.1} : Set (Subgroup W)) =
            {U.map a.toMonoidHom, U'.map a.toMonoidHom} :=
          hsupp.symm.trans (by
            rw [s13Supp_conj (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha)),
              hsuppQ, Set.image_pair])
        have hmem : V ∈ ({U.map a.toMonoidHom, U'.map a.toMonoidHom} : Set (Subgroup W)) := by
          rw [← hset]; simp
        rcases Set.mem_insert_iff.mp hmem with h | h
        · rw [h, CFSG.RankThree.S4Free.Stell.rk_map_mulAut]; exact hrkU_two
        · rw [Set.mem_singleton_iff.mp h, CFSG.RankThree.S4Free.Stell.rk_map_mulAut]
          exact hrkU'_two
    have hsumC : rk ↥(commSub ⊤ L) = 2 * C.ncard := by
      haveI : Fintype ↥C := Fintype.ofFinite _
      rw [hcomm_eq, w16g_rk_iSup_eq_sum (fun w => by rw [pow_two]; exact h.hW w)
        (fun U : ↥C => (U.1 : Subgroup W)) hindC]
      have h2 : ∑ U : ↥C, rk ↥(U.1 : Subgroup W) = ∑ _ : ↥C, (2 : ℕ) :=
        Finset.sum_congr rfl fun U _ => hrk2C U.1 U.2
      rw [h2, Finset.sum_const, Finset.card_univ, Set.fintypeCard_eq_ncard, smul_eq_mul]
      ring
    have hsupC : sSup C = ⨆ U : ↥C, (U.1 : Subgroup W) :=
      le_antisymm
        (sSup_le fun V hV => le_iSup (fun U : ↥C => (U.1 : Subgroup W)) ⟨V, hV⟩)
        (iSup_le fun U => le_sSup U.2)
    have hcomm_eq' : commSub ⊤ L = sSup C := by rw [hcomm_eq, ← hsupC]
    have hCone : 1 ≤ C.ncard := le_trans (by norm_num : 1 ≤ 3) hn
    have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
    have hmap_eq_of_fix : ∀ {g : MulAut W} {V : Subgroup W}, g * g = 1 →
        commSub V (Subgroup.zpowers g) = ⊥ → V.map g.toMonoidHom = V := by
      intro g V hg2 hfix
      have hle : V ≤ fixV (Subgroup.zpowers g) := commSub_eq_bot_iff.mp hfix
      have hgg : ∀ y : W, g (g y) = y := fun y => by
        rw [show g (g y) = (g * g) y from rfl, hg2]
        rfl
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        rw [show (MulEquiv.toMonoidHom g) y = y from
          (mem_fixV.mp (hle hy)) g (Subgroup.mem_zpowers g)]
        exact hy
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨(MulEquiv.toMonoidHom g) y, ?_, hgg y⟩
        rw [show (MulEquiv.toMonoidHom g) y = y from
          (mem_fixV.mp (hle hy)) g (Subgroup.mem_zpowers g)]
        exact hy
    have hφmem : ∀ U : ↥C, (⟨U.1, hCsub U.2⟩ : ↥(s13IsoComps X)) ∈ c.supp := by
      intro U
      obtain ⟨V, hV, hVU⟩ := U.2
      have hVc : (s13SuppGraph A X Q).connectedComponentMk V = c :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c V).mp hV
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hV' : (⟨U.1, hCsub U.2⟩ : ↥(s13IsoComps X)) = V := Subtype.ext hVU.symm
      rw [hV', hVc]
    let Φ : ↥C → ↥c.supp := fun U => ⟨⟨U.1, hCsub U.2⟩, hφmem U⟩
    have hΦinj : Function.Injective Φ := by
      intro U U' h
      apply Subtype.ext
      exact congrArg (fun V : ↥c.supp => (V.1.1 : Subgroup W)) h
    have hΦsurj : Function.Surjective Φ := by
      intro V
      refine ⟨⟨V.1.1, ⟨V.1, V.2, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
    let e : ↥C ≃ ↥c.supp := Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
    let f : ↥C → ↥(s13IsoComps X) := fun U => ⟨U.1, hCsub U.2⟩
    let G : SimpleGraph ↥C := (s13SuppGraph A X Q).comap f
    have hiso : G ≃g c.toSimpleGraph :=
      { toEquiv := e
        map_rel_iff' := by
          rintro U U'
          rw [SimpleGraph.comap_adj]
          change (s13SuppGraph A X Q).Adj (f U) (f U') ↔
            (s13SuppGraph A X Q).Adj (e U).1 (e U').1
          rfl }
    have hconn : G.Connected :=
      (SimpleGraph.Iso.connected_iff hiso).mpr c.connected_toSimpleGraph
    have hstab_of_maps : ∀ {g : MulAut W}, g * g = 1 →
        (∀ U ∈ C, U.map g.toMonoidHom ∈ C) → g ∈ stabSub (sSup C) := by
      intro g hg2 hgC
      have hmap_le : (sSup C).map g.toMonoidHom ≤ sSup C := by
        rw [Subgroup.map_le_iff_le_comap]
        refine sSup_le fun U hU => ?_
        intro x hx
        exact le_sSup (hgC U hU) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      rw [mem_stabSub]
      intro u
      constructor
      · intro hu
        have h2 : g (g u) ∈ sSup C := hmap_le (Subgroup.mem_map.mpr ⟨g u, hu, rfl⟩)
        have hgg : g (g u) = u := by
          rw [show g (g u) = (g * g) u from rfl, hg2]
          rfl
        rwa [hgg] at h2
      · intro hu
        exact hmap_le (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    have key : ∀ {P₀ P₁ S T : Subgroup W} {g0 : MulAut W}, g0 * g0 = 1 → P₀ ≠ P₁ →
        P₁ = P₀.map g0.toMonoidHom → ({P₀, P₁} : Set (Subgroup W)) = {S, T} → S ≠ T →
        S.map g0.toMonoidHom = T ∧ T.map g0.toMonoidHom = S := by
      intro P₀ P₁ S T g0 hg2 hPne hPmap hset hST
      have hPt : P₁.map g0.toMonoidHom = P₀ := by
        rw [hPmap, Subgroup.map_map,
          show g0.toMonoidHom.comp g0.toMonoidHom = MonoidHom.id W from by
            ext x; rw [MonoidHom.comp_apply]
            show g0 (g0 x) = x
            rw [show g0 (g0 x) = (g0 * g0) x from rfl, hg2]
            rfl, Subgroup.map_id]
      have hmemS : S = P₀ ∨ S = P₁ := by
        have h1 : S ∈ ({P₀, P₁} : Set (Subgroup W)) := by rw [hset]; simp
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
      have hmemT : T = P₀ ∨ T = P₁ := by
        have h1 : T ∈ ({P₀, P₁} : Set (Subgroup W)) := by rw [hset]; simp
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
      have hswapS : S.map g0.toMonoidHom = T := by
        rcases hmemS with hS | hS
        · have hT : T = P₁ := by
            rcases hmemT with hT | hT
            · exact absurd (hT.trans hS.symm) (Ne.symm hST)
            · exact hT
          rw [hS, hT, hPmap]
        · have hT : T = P₀ := by
            rcases hmemT with hT | hT
            · exact hT
            · exact absurd (hT.trans hS.symm) (Ne.symm hST)
          rw [hS, hT, hPt]
      have hswapT : T.map g0.toMonoidHom = S := by
        rcases hmemT with hT | hT
        · have hS : S = P₁ := by
            rcases hmemS with hS | hS
            · exact absurd (hS.trans hT.symm) hST
            · exact hS
          rw [hT, hS, hPmap]
        · have hS : S = P₀ := by
            rcases hmemS with hS | hS
            · exact hS
            · exact absurd (hS.trans hT.symm) hST
          rw [hT, hS, hPt]
      exact ⟨hswapS, hswapT⟩
    have hmain : ∀ {a : MulAut W} {P Q' : Subgroup W}, a ∈ A → P ∈ C → Q' ∈ C → P ≠ Q' →
        s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = {P, Q'} →
        ∃ g ∈ A ⊓ stabSub (sSup C), P.map g.toMonoidHom = Q' ∧
          Q'.map g.toMonoidHom = P ∧
          ∀ V ∈ C, V ≠ P → V ≠ Q' → V.map g.toMonoidHom = V := by
      intro a P Q' ha hPC hQC hPQ hsupp
      have hsupp' : s13Supp X (Q.map (MulAut.conj a).toMonoidHom) =
          {U.map a.toMonoidHom, U'.map a.toMonoidHom} := by
        rw [s13Supp_conj (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha)),
          hsuppQ, Set.image_pair]
      have hset : ({U.map a.toMonoidHom, U'.map a.toMonoidHom} : Set (Subgroup W)) = {P, Q'} :=
        hsupp'.symm.trans hsupp
      have hPne : U.map a.toMonoidHom ≠ U'.map a.toMonoidHom :=
        fun h => hUU' (Subgroup.map_injective a.injective h)
      have hPmap : U'.map a.toMonoidHom =
          (U.map a.toMonoidHom).map (a * t * a⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        have hcomp : (a * t * a⁻¹).toMonoidHom.comp a.toMonoidHom = (a * t).toMonoidHom := by
          ext x
          simp only [MonoidHom.comp_apply]
          show (a * t * a⁻¹) (a x) = (a * t) x
          simp [MulAut.mul_apply]
        rw [hcomp]
        have hcomp2 : (a * t).toMonoidHom = a.toMonoidHom.comp t.toMonoidHom := by
          ext x
          simp [MulAut.mul_apply]
        rw [hcomp2, ← Subgroup.map_map, hswapU]
      have hg2 : (a * t * a⁻¹) * (a * t * a⁻¹) = 1 := by
        have := (h.conj ha).ht2
        rwa [pow_two] at this
      obtain ⟨hswapP, hswapQ⟩ := key (P₀ := U.map a.toMonoidHom) (P₁ := U'.map a.toMonoidHom)
        (S := P) (T := Q') hg2 hPne hPmap hset hPQ
      have haC : (fun U : Subgroup W => U.map a.toMonoidHom) '' C = C := by
        obtain ⟨c', hc'⟩ := w16g_s13CompSet_image_eq ha h.hXA c
        have hUmapaC : U.map a.toMonoidHom ∈ C := by
          have hmem : U.map a.toMonoidHom ∈ ({P, Q'} : Set (Subgroup W)) := by
            rw [← hset]; simp
          rcases Set.mem_insert_iff.mp hmem with h | h
          · rw [h]; exact hPC
          · rw [Set.mem_singleton_iff.mp h]; exact hQC
        have hc'eq : c' = c := by
          by_contra hne
          have hd : Disjoint c'.supp c.supp :=
            SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hne
          have hd' : Disjoint (s13CompSet A X Q c') (s13CompSet A X Q c) :=
            Set.disjoint_image_of_injective Subtype.val_injective hd
          have h1 : U.map a.toMonoidHom ∈ s13CompSet A X Q c' := by
            rw [hc']; exact ⟨U, hUC, rfl⟩
          exact Set.disjoint_left.mp hd' h1 hUmapaC
        rw [← hc', hc'eq]
      have hfixC : ∀ V ∈ C, V ≠ P → V ≠ Q' → V.map (a * t * a⁻¹).toMonoidHom = V := by
        intro V hV hVP hVQ
        have hV0C : V.map a⁻¹.toMonoidHom ∈ C := by
          have : V ∈ (fun U : Subgroup W => U.map a.toMonoidHom) '' C := by
            rw [haC]; exact hV
          obtain ⟨V0, hV0, hV0V⟩ := this
          have hV0eq : V0 = V.map a⁻¹.toMonoidHom := by
            have hmap : (V0.map a.toMonoidHom).map a⁻¹.toMonoidHom = V0 := by
              rw [Subgroup.map_map,
                show a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id W from by
                  ext x; simp, Subgroup.map_id]
            rw [← hmap]
            exact congrArg (fun W : Subgroup W => W.map a⁻¹.toMonoidHom) hV0V
          rw [← hV0eq]; exact hV0
        have hV0map : (V.map a⁻¹.toMonoidHom).map a.toMonoidHom = V := by
          rw [Subgroup.map_map,
            show a.toMonoidHom.comp a⁻¹.toMonoidHom = MonoidHom.id W from by
              ext x; simp, Subgroup.map_id]
        have hV0neU : V.map a⁻¹.toMonoidHom ≠ U := by
          intro h
          have hVeq : V = U.map a.toMonoidHom := by rw [← hV0map, h]
          have hmem : U.map a.toMonoidHom ∈ ({P, Q'} : Set (Subgroup W)) := by
            rw [← hset]; simp
          rcases Set.mem_insert_iff.mp hmem with h1 | h1
          · exact hVP (hVeq.trans h1)
          · exact hVQ (hVeq.trans (Set.mem_singleton_iff.mp h1))
        have hV0neU' : V.map a⁻¹.toMonoidHom ≠ U' := by
          intro h
          have hVeq : V = U'.map a.toMonoidHom := by rw [← hV0map, h]
          have hmem : U'.map a.toMonoidHom ∈ ({P, Q'} : Set (Subgroup W)) := by
            rw [← hset]; simp
          rcases Set.mem_insert_iff.mp hmem with h1 | h1
          · exact hVP (hVeq.trans h1)
          · exact hVQ (hVeq.trans (Set.mem_singleton_iff.mp h1))
        have hzp : (Subgroup.zpowers t).map (MulAut.conj a).toMonoidHom =
            Subgroup.zpowers (a * t * a⁻¹) := by
          rw [MonoidHom.map_zpowers]
          change Subgroup.zpowers (MulAut.conj a t) = Subgroup.zpowers (a * t * a⁻¹)
          rw [MulAut.conj_apply]
        have hconj : commSub ((V.map a⁻¹.toMonoidHom).map a.toMonoidHom)
            (Subgroup.zpowers (a * t * a⁻¹)) = ⊥ := by
          have hmap := CFSG.RankThree.S4Free.Stell.map_commSub a (V.map a⁻¹.toMonoidHom)
            (Subgroup.zpowers t)
          rw [hzp] at hmap
          rw [hcentC (V.map a⁻¹.toMonoidHom) hV0C hV0neU hV0neU'] at hmap
          simpa using hmap.symm
        have hfixg := hmap_eq_of_fix (g := a * t * a⁻¹)
          (V := (V.map a⁻¹.toMonoidHom).map a.toMonoidHom) hg2 hconj
        rwa [hV0map] at hfixg
      have hgC : ∀ V ∈ C, V.map (a * t * a⁻¹).toMonoidHom ∈ C := by
        intro V hV
        by_cases hVP : V = P
        · rw [hVP, hswapP]; exact hQC
        · by_cases hVQ : V = Q'
          · rw [hVQ, hswapQ]; exact hPC
          · rw [hfixC V hV hVP hVQ]; exact hV
      exact ⟨a * t * a⁻¹,
        ⟨A.mul_mem (A.mul_mem ha h.htA) (A.inv_mem ha), hstab_of_maps hg2 hgC⟩,
        hswapP, hswapQ, hfixC⟩
    have hedge : ∀ U U' : ↥C, G.Adj U U' → ∃ g ∈ A ⊓ stabSub (sSup C),
        U.1.map g.toMonoidHom = U'.1 ∧ U'.1.map g.toMonoidHom = U.1 ∧
          ∀ V ∈ C, V ≠ U.1 → V ≠ U'.1 → V.map g.toMonoidHom = V := by
      intro U U' hUU'
      have hrel : (s13SuppGraph A X Q).Adj (f U) (f U') := SimpleGraph.comap_adj.mp hUU'
      rw [s13SuppGraph, SimpleGraph.fromRel_adj] at hrel
      obtain ⟨hne, hrel⟩ := hrel
      rcases hrel with hrel | hrel
      · obtain ⟨a, ha, hsupp⟩ := hrel
        exact hmain ha U.2 U'.2 (fun h => hne (Subtype.ext h)) hsupp
      · obtain ⟨a, ha, hsupp⟩ := hrel
        refine hmain ha U.2 U'.2 (fun h => hne (Subtype.ext h)) ?_
        rw [hsupp, Set.pair_comm]
    have htC : ∀ V ∈ C, V.map t.toMonoidHom ∈ C := by
      intro V hV
      by_cases hVU : V = U
      · rw [hVU, hswapU]; exact hU'C
      · by_cases hVU' : V = U'
        · rw [hVU', hswapU']; exact hUC
        · rw [hmap_eq_of_fix (g := t) (V := V) ht2' (hcentC V hV hVU hVU')]; exact hV
    have ht_mem : t ∈ A ⊓ stabSub (sSup C) := ⟨h.htA, hstab_of_maps ht2' htC⟩
    have htswap : ∃ U ∈ C, ∃ U' ∈ C, U ≠ U' ∧ U.map t.toMonoidHom = U' ∧
        U'.map t.toMonoidHom = U ∧
        ∀ V ∈ C, V ≠ U → V ≠ U' → V.map t.toMonoidHom = V := by
      refine ⟨U, hUC, U', hU'C, hUU', hswapU, hswapU', ?_⟩
      intro V hV hVU hVU'
      exact hmap_eq_of_fix (g := t) (V := V) ht2' (hcentC V hV hVU hVU')
    have htfix : (2 < C.ncard - 1) → ∀ V ∈ C, V.map t.toMonoidHom = V →
        ∀ x ∈ V, t x = x := by
      intro _ V hV hVmap x hx
      have hVU : V ≠ U := by
        intro h
        rw [h] at hVmap
        exact hUU' (hVmap.symm.trans hswapU)
      have hVU' : V ≠ U' := by
        intro h
        rw [h] at hVmap
        exact hUU' (hVmap.symm.trans hswapU').symm
      have hle : V ≤ fixV (Subgroup.zpowers t) :=
        commSub_eq_bot_iff.mp (hcentC V hV hVU hVU')
      exact (mem_fixV.mp (hle hx)) t (Subgroup.mem_zpowers t)
    right; right; right; right; right; left
    refine ⟨C.ncard - 1, 2, Or.inl ⟨rfl, rfl⟩, ?_, hrank, ?_, ?_⟩
    · have hC3 : 3 ≤ C.ncard := hn
      omega
    · rw [hsumC, Nat.sub_add_cancel hCone]; ring
    · rw [hcomm_eq']
      exact s13_deltaSym_of_edge_swaps C (Nat.sub_add_cancel hCone).symm hrk2C
        ((s13IsoComps_sSupIndep h.hW hodd).mono hCsub)
        (fun g hg U hU => by
          have hgA : g ∈ A := hg.1
          have hgstab : g ∈ stabSub (sSup C) := hg.2
          by_contra hnot
          have hUcomp : U.map g.toMonoidHom ∈ s13IsoComps X :=
            w16g_map_mem_s13IsoComps' hgA h.hXA ⟨U, hCsub hU⟩
          have hCsub' : C ⊆ s13IsoComps X \ {U.map g.toMonoidHom} := by
            intro V hV
            exact ⟨hCsub hV, fun h => hnot (h ▸ hV)⟩
          have hstab_map : (sSup C).map g.toMonoidHom ≤ sSup C := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
            exact (mem_stabSub.mp hgstab y).mpr hy
          have hgUle : U.map g.toMonoidHom ≤ sSup C :=
            (Subgroup.map_mono (le_sSup hU)).trans hstab_map
          have hdisj : Disjoint (U.map g.toMonoidHom)
              (sSup (s13IsoComps X \ {U.map g.toMonoidHom})) :=
            (s13IsoComps_sSupIndep h.hW hodd).disjoint_sSup hUcomp
              (fun V (hV : V ∈ s13IsoComps X \ {U.map g.toMonoidHom}) => hV.1)
              (by simp)
          have hbot : U.map g.toMonoidHom ≤ (⊥ : Subgroup W) := by
            rw [← disjoint_iff.mp hdisj]
            exact le_inf le_rfl (hgUle.trans (sSup_le_sSup hCsub'))
          have hUne : U ≠ ⊥ := (s13IsoComps_le_commSub h.hW hodd (hCsub hU)).1
          exact hUne ((Subgroup.map_eq_bot_iff_of_injective (H := U) g.injective).mp
            (le_bot_iff.mp hbot)))
        G hconn hedge ht_mem htswap htfix
  ·
    have hεm1 : ε = -1 := by
      rcases hεpm with h | h
      · exact absurd h hε1
      · exact h
    obtain ⟨hn3, hrk2, hinvL⟩ :=
      w16g_case_one_eps_neg h c hQc (w16g_compSet_conj_self h hQ3 he c hQc) hl hUU' hsuppQ
        hfne hεm1 hmap_of_pi hπ_invol hrel (hεm1_dich hεm1).1 (hεm1_dich hεm1).2 hn
    right; right; right; right; right; right
    refine ⟨?_, ?_, hinvL⟩
    · have hL9 : Nat.card ↥L = 9 := by rw [hLcard, hn3]; norm_num
      exact w16g_isElemAbelianOfRank_of_card
        (fun a b : ↥L => Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W))
          (h.hXe.1.is_comm.comm ⟨a.1, hLle a.2⟩ ⟨b.1, hLle b.2⟩)))
        (fun a : ↥L => Subtype.ext (by simpa using h.hXe.2 a.1 (hLle a.2)))
        hL9
    · have hsum2 : rk ↥(commSub ⊤ L) = ∑ᶠ V ∈ C, rk ↥V := by
        rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hXe hLle, hLsupp]
      rw [hsum2]
      haveI : Fintype ↥C := Fintype.ofFinite _
      rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
      have h3 : (∑ V : ↥C, rk ↥(V.1 : Subgroup W)) = ∑ _ : ↥C, (2 : ℕ) :=
        Finset.sum_congr rfl fun V _ => hrk2 V.1 V.2
      rw [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      have hc : Fintype.card ↥C = 3 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact hn3
      rw [hc]

theorem s13_three_case_one (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 2) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Conc4_133 A t L ∧
      L = s13XSupp X (s13Supp X L) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian_three h.hXe
  have h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2 := by
    intro a ha
    have hconj := s13Supp_conj (X := X) (L := Q) (g := a)
      (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha))
    rw [hconj, Set.ncard_image_of_injective _ (Subgroup.map_injective a.injective)]
    exact he
  obtain ⟨hedge, hind_all, hsum, hcomp⟩ := s13_graph_decomp h hQ3 h2
  obtain ⟨U₀, U₁, hne01, hsuppQ⟩ := Set.ncard_eq_two.mp he
  have hU₀mem : U₀ ∈ s13IsoComps X := by
    have h : U₀ ∈ s13Supp X Q := by rw [hsuppQ]; simp
    exact h.1
  have hU₁mem : U₁ ∈ s13IsoComps X := by
    have h : U₁ ∈ s13Supp X Q := by rw [hsuppQ]; simp
    exact h.1
  let v₀ : ↥(s13IsoComps X) := ⟨U₀, hU₀mem⟩
  let c₀ : (s13SuppGraph A X Q).ConnectedComponent :=
    (s13SuppGraph A X Q).connectedComponentMk v₀
  let C : Set (Subgroup W) := s13CompSet A X Q c₀
  let L : Subgroup (MulAut W) := s13XSupp X C
  have hCsub : C ⊆ s13IsoComps X := by
    rintro U ⟨W', hW', rfl⟩
    exact W'.2
  have hadjQ : (s13SuppGraph A X Q).Adj v₀ ⟨U₁, hU₁mem⟩ := by
    rw [s13SuppGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨1, A.one_mem, ?_⟩⟩
    · intro heq
      exact hne01 (congrArg Subtype.val heq)
    · have hmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
        rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) from by
          ext x; simp [MulAut.conj_apply], Subgroup.map_id]
      rw [hmap1]; exact hsuppQ
  have hU₀C : U₀ ∈ C :=
    ⟨v₀, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hU₁C : U₁ ∈ C := by
    refine ⟨⟨U₁, hU₁mem⟩, ?_, rfl⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadjQ).symm
  have hCpair : ({U₀, U₁} : Set (Subgroup W)) ⊆ C := by
    intro U hU
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    rcases hU with rfl | rfl
    · exact hU₀C
    · exact hU₁C
  have hn : 2 ≤ C.ncard := by
    have hle := Set.ncard_le_ncard hCpair
    rwa [Set.ncard_pair hne01] at hle
  have hCne : C.Nonempty := ⟨U₀, hU₀C⟩
  have hLle : L ≤ X := s13XSupp_le
  have hLsupp : s13Supp X L = C := (hcomp c₀).1
  have hLlt : Nat.card ↥L < 3 ^ C.ncard :=
    s13_card_XSupp_lt h.hW (p := 3) hp3 hp32 h.hXe hH0 hCsub hCne
  have hLpgroup : IsPGroup 3 ↥L := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (h.hXe.2 x.1 (hLle x.2))⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hLpgroup
  obtain ⟨-, hlow, -⟩ := hcomp c₀
  have hk_le : C.ncard - 1 ≤ k := by
    rw [hk] at hlow
    exact (Nat.pow_le_pow_iff_right (show (1:ℕ) < 3 by norm_num)).mp hlow
  have hk_lt : k < C.ncard := by
    rw [hk] at hLlt
    exact (Nat.pow_lt_pow_iff_right (show (1:ℕ) < 3 by norm_num)).mp hLlt
  have hk_eq : k = C.ncard - 1 := by omega
  have hLcard : Nat.card ↥L = 3 ^ (C.ncard - 1) := by rw [hk, hk_eq]
  have hrank : IsElemAbelianOfRank 3 (C.ncard - 1) ↥L :=
    w16g_isElemAbelianOfRank_of_card
      (fun a b : ↥L => Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W))
        (h.hXe.1.is_comm.comm ⟨a.1, hLle a.2⟩ ⟨b.1, hLle b.2⟩)))
      (fun a : ↥L => Subtype.ext (by simpa using h.hXe.2 a.1 (hLle a.2)))
      hLcard
  have hcomm_eq : commSub ⊤ L = ⨆ U : ↥C, (U.1 : Subgroup W) := by
    rw [commSub_top_eq_iSup_s13Supp h.hW (p := 3) hp3 hp32 h.hXe hLle, hLsupp]
    exact iSup_subtype' (p := fun U => U ∈ C) (f := fun U (_ : U ∈ C) => U)
  have hindC : iSupIndep (fun U : ↥C => (U.1 : Subgroup W)) :=
    (sSupIndep_iff C).mp ((s13IsoComps_sSupIndep h.hW hodd).mono hCsub)
  have hQL : Q ≤ L :=
    (le_s13XSupp_iff h.hW (p := 3) hp3 hp32 h.hXe h.hQX).mpr
      (by rw [hsuppQ]; exact hCpair)
  have hcommQ_ne : commSub ⊤ Q ≠ ⊥ := by
    intro hbot
    apply h.hQ1
    apply le_bot_iff.mp
    intro q hq
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => ?_
    exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hbot) (Subgroup.mem_top w))) q hq
  have hLcomm : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
      by_contra hc
      push Not at hc
      exact h.hQ1 (le_bot_iff.mp (fun q hq => Subgroup.mem_bot.mpr (hc q hq)))
    have hqL : q ∈ L := hQL hqQ
    have hq2 : q ^ 2 ≠ 1 := by
      intro hq2
      have hdvd3 : orderOf q ∣ 3 :=
        orderOf_dvd_iff_pow_eq_one.mpr (h.hXe.2 q (h.hQX hqQ))
      have hdvd2 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2
      have hd : orderOf q ∣ Nat.gcd 3 2 := Nat.dvd_gcd hdvd3 hdvd2
      rw [show Nat.gcd 3 2 = 1 from by norm_num] at hd
      exact hq1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
    have htq' : t * q⁻¹ * t⁻¹ = q := by
      calc t * q⁻¹ * t⁻¹ = (t * q * t⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]; group
        _ = (q⁻¹)⁻¹ := by rw [h.hQinv q hqQ]
        _ = q := inv_inv q
    have hcommq : ⁅q, t⁆ = q ^ 2 := by
      rw [commutatorElement_def]
      calc q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) := by group
        _ = q * q := by rw [htq']
        _ = q ^ 2 := by rw [pow_two]
    have hmem : ⁅q, t⁆ ∈ ⁅L, Subgroup.zpowers t⁆ :=
      Subgroup.commutator_mem_commutator hqL (Subgroup.mem_zpowers t)
    rw [hbot] at hmem
    exact hq2 (hcommq ▸ Subgroup.mem_bot.mp hmem)
  have hdisj : ∀ g ∈ A, s13Supp X (L.map (MulAut.conj g).toMonoidHom) = s13Supp X L ∨
      Disjoint (s13Supp X (L.map (MulAut.conj g).toMonoidHom)) (s13Supp X L) := by
    intro g hg
    have hconj : s13Supp X (L.map (MulAut.conj g).toMonoidHom) =
        (fun U : Subgroup W => U.map g.toMonoidHom) '' C := by
      rw [w16g_s13Supp_conj (h.hXA g hg) (by simpa using h.hXA g⁻¹ (A.inv_mem hg)), hLsupp]
    rw [hconj, hLsupp]
    exact w16g_s13CompSet_conj_disjoint_or_eq h.hXA hg c₀
  have hind : sSupIndep (conjSubs A (commSub ⊤ L)) :=
    sSupIndep_conjSubs_of_s13Supp h.hW (p := 3) hp3 hp32 h.hXe h.hXA hLle hdisj
  refine ⟨L, hLle, ?_, ?_⟩
  · by_cases hn2 : C.ncard = 2
    · refine ⟨3, hp3, hLle.trans h.hXO, hLcomm, hind, ?_⟩
      left
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact isCyclic_of_prime_card (p := 3) (by rw [hLcard, hn2]; norm_num)
      · rw [hLcard, hn2]; norm_num
      · have hCeq' : ({U₀, U₁} : Set (Subgroup W)) = C :=
          Set.eq_of_subset_of_ncard_le hCpair (by simp [hn2, Set.ncard_pair hne01])
        have hCeq : C = s13Supp X Q := by rw [← hCeq', hsuppQ]
        have hcommLQ : commSub ⊤ L = commSub ⊤ Q := by
          rw [hcomm_eq, commSub_top_eq_iSup_s13Supp h.hW (p := 3) hp3 hp32 h.hXe h.hQX,
            ← hCeq]
          exact (iSup_subtype' (p := fun U => U ∈ C)
            (f := fun U (_ : U ∈ C) => U)).symm
        have hdvd : 2 ∣ rk ↥(commSub ⊤ L) := by
          rw [hcommLQ]
          exact ⟨rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)),
            (cost_commSub_Q h).1.symm⟩
        have hle : rk ↥(commSub ⊤ L) ≤ 6 := by
          rw [hcommLQ]; exact (cost_commSub_Q h).2
        have hne : rk ↥(commSub ⊤ L) ≠ 0 := by
          rw [hcommLQ]
          intro h0
          exact hcommQ_ne ((rk_eq_zero_iff (fun w => by rw [pow_two]; exact h.hW w)).mp h0)
        omega
    · have hn3 : 3 ≤ (s13CompSet A X Q c₀).ncard := by
        change 3 ≤ C.ncard
        omega
      exact w16g_s13_three_case_one_large h hH0 hQ3 he c₀ hn3 hQL
  · rw [hLsupp]

end CFSG.LocalAnalysis.WeakClosure81
