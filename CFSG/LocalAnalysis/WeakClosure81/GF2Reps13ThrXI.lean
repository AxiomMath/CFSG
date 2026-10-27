module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXG
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXH

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_mem_s13Supp_zpowers_iff {p : ℕ} {X : Subgroup (MulAut W)}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam)
    {z : MulAut W} (hz : z ∈ X) (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers z) ↔
      lam U (Additive.ofMul ⟨z, hz⟩) ≠ 0 := by
  have h1 : (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers z) ↔
      commSub (U : Subgroup W) (Subgroup.zpowers z) ≠ ⊥ := by
    simp only [s13Supp, Set.mem_setOf_eq, U.2, true_and]
  rw [h1]
  simpa using (coord_ne_zero_iff hl ⟨z, hz⟩ U).symm

theorem s13_card_XSupp_lt (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    {B : Set (Subgroup W)} (hB : B ⊆ s13IsoComps X) (hBne : B.Nonempty) :
    Nat.card ↥(s13XSupp X B) < p ^ B.ncard := by
  classical
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := NeZero.of_pos hp.pos
  obtain ⟨lam, hl⟩ := exists_coord hW hp hp2 hX
  let φ : ↥(s13XSupp X B) → (↥B → ZMod p) := fun x U =>
    lam ⟨U.1, hB U.2⟩ (Additive.ofMul ⟨x.1, s13XSupp_le x.2⟩)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hcoord : ∀ U : s13IsoComps X,
        lam U (Additive.ofMul ⟨x.1, s13XSupp_le x.2⟩) =
          lam U (Additive.ofMul ⟨y.1, s13XSupp_le y.2⟩) := by
      intro U
      by_cases hUB : (U : Subgroup W) ∈ B
      · have h1 : (⟨U.1, hB hUB⟩ : s13IsoComps X) = U := Subtype.ext rfl
        rw [← h1]
        exact congrFun hxy ⟨U.1, hUB⟩
      · rw [((hl U).2 ⟨x.1, s13XSupp_le x.2⟩).mpr
              ((mem_s13XSupp.mp x.2).2 U.1 U.2 hUB),
            ((hl U).2 ⟨y.1, s13XSupp_le y.2⟩).mpr
              ((mem_s13XSupp.mp y.2).2 U.1 U.2 hUB)]
    have hEq := coord_injective hW hp hp2 hX hl hcoord
    have hval : x.1 = y.1 := congrArg (fun z : ↥X => (z : MulAut W)) hEq
    exact Subtype.ext hval
  have hcard : Nat.card ↥(s13XSupp X B) ≤ p ^ B.ncard := by
    have h1 : Nat.card ↥(s13XSupp X B) ≤ Nat.card (↥B → ZMod p) :=
      Nat.card_le_card_of_injective φ hφinj
    have h2 : Nat.card (↥B → ZMod p) = p ^ B.ncard := by
      rw [Nat.card_fun, Nat.card_coe_set_eq, Nat.card_zmod]
    rwa [h2] at h1
  by_contra hlt
  rw [not_lt] at hlt
  have hcard_eq : Nat.card ↥(s13XSupp X B) = Nat.card (↥B → ZMod p) := by
    have h2 : Nat.card (↥B → ZMod p) = p ^ B.ncard := by
      rw [Nat.card_fun, Nat.card_coe_set_eq, Nat.card_zmod]
    rw [h2]
    exact le_antisymm hcard hlt
  have hrange : Set.range φ = Set.univ := by
    rw [Set.eq_univ_iff_ncard, Set.ncard_range_of_injective hφinj, hcard_eq]
  obtain ⟨U₀, hU₀B⟩ := hBne
  let v : ↥B → ZMod p := Function.update 0 ⟨U₀, hU₀B⟩ 1
  have hv : v ∈ Set.range φ := by rw [hrange]; trivial
  obtain ⟨x, hxφ⟩ := hv
  have hxne : x.1 ≠ 1 := by
    intro hx1
    have h1 : φ x ⟨U₀, hU₀B⟩ = 1 := by
      rw [hxφ]
      change Function.update (0 : ↥B → ZMod p) ⟨U₀, hU₀B⟩ 1 ⟨U₀, hU₀B⟩ = 1
      rw [Function.update_self]
    have h0 : φ x ⟨U₀, hU₀B⟩ = 0 := by
      change lam ⟨U₀, hB hU₀B⟩ (Additive.ofMul ⟨x.1, s13XSupp_le x.2⟩) = 0
      rw [show (⟨x.1, s13XSupp_le x.2⟩ : ↥X) = 1 from
            Subtype.ext (by simpa using hx1), ofMul_one, map_zero]
    rw [h0] at h1
    exact one_ne_zero h1.symm
  have hsupp : s13Supp X (Subgroup.zpowers x.1) = {U₀} := by
    ext U
    rw [Set.mem_singleton_iff]
    constructor
    · intro hU
      have hUmem : U ∈ s13IsoComps X := hU.1
      have hne : lam ⟨U, hUmem⟩ (Additive.ofMul ⟨x.1, s13XSupp_le x.2⟩) ≠ 0 :=
        (w16g_mem_s13Supp_zpowers_iff hl (s13XSupp_le x.2) ⟨U, hUmem⟩).mp hU
      by_cases hUB : U ∈ B
      · have hφeq : φ x ⟨U, hUB⟩ = v ⟨U, hUB⟩ := congrFun hxφ ⟨U, hUB⟩
        have hvne : v ⟨U, hUB⟩ ≠ 0 := by
          rw [← hφeq]
          change lam ⟨U, hB hUB⟩ (Additive.ofMul ⟨x.1, s13XSupp_le x.2⟩) ≠ 0
          rwa [show (⟨U, hB hUB⟩ : s13IsoComps X) = ⟨U, hUmem⟩ from Subtype.ext rfl]
        have heq : (⟨U, hUB⟩ : ↥B) = ⟨U₀, hU₀B⟩ := by
          by_contra hne'
          refine hvne ?_
          change Function.update (0 : ↥B → ZMod p) ⟨U₀, hU₀B⟩ 1 ⟨U, hUB⟩ = 0
          rw [Function.update_of_ne hne' (1 : ZMod p) (0 : ↥B → ZMod p)]
          exact Pi.zero_apply _
        exact congrArg Subtype.val heq
      · exfalso
        have hker : x.1 ∈ s13KerOn X U := (mem_s13XSupp.mp x.2).2 U hUmem hUB
        exact hne (((hl ⟨U, hUmem⟩).2 ⟨x.1, s13XSupp_le x.2⟩).mpr hker)
    · intro hU
      rw [hU]
      refine (w16g_mem_s13Supp_zpowers_iff hl (s13XSupp_le x.2) ⟨U₀, hB hU₀B⟩).mpr ?_
      have hφeq : φ x ⟨U₀, hU₀B⟩ = v ⟨U₀, hU₀B⟩ := congrFun hxφ ⟨U₀, hU₀B⟩
      change φ x ⟨U₀, hU₀B⟩ ≠ 0
      rw [hφeq]
      change Function.update (0 : ↥B → ZMod p) ⟨U₀, hU₀B⟩ 1 ⟨U₀, hU₀B⟩ ≠ 0
      rw [Function.update_self]
      exact one_ne_zero
  exact hH0 x.1 (s13XSupp_le x.2) hxne (by rw [hsupp]; simp)

variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_odd_card_of_isElemAbelian_seven {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 7 X) : Odd (Nat.card X) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpg : IsPGroup 7 X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 x.1 x.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  rw [hm]
  exact Odd.pow (by norm_num : Odd 7)

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

theorem s13_seven_branch (h : HAb A X Q t 7) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Conc4_133 A t L ∧
      L = s13XSupp X (s13Supp X L) := by
  classical
  by_cases hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1
  ·
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian_seven h.hXe
    have hQ7 : Nat.card ↥Q = 7 := h.hQ7 rfl
    have h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2 := by
      intro a ha
      obtain ⟨U₀', U₁', hne, hsupp, -⟩ := s13_seven_pair (h.conj ha)
      rw [hsupp, Set.ncard_pair hne]
    obtain ⟨hedge, hind_all, hsum, hcomp⟩ := s13_graph_decomp h hQ7 h2
    obtain ⟨U₀, U₁, hne01, hsuppQ, htmap, hfixQ, hfixVQ⟩ := s13_seven_pair h
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
    have hLlt : Nat.card ↥L < 7 ^ C.ncard :=
      s13_card_XSupp_lt h.hW (p := 7) (by norm_num) (by norm_num) h.hXe hH0 hCsub hCne
    have hLpgroup : IsPGroup 7 ↥L := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (h.hXe.2 x.1 (hLle x.2))⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hLpgroup
    obtain ⟨-, hlow, -⟩ := hcomp c₀
    have hk_le : C.ncard - 1 ≤ k := by
      rw [hk] at hlow
      exact (Nat.pow_le_pow_iff_right (show (1:ℕ) < 7 by norm_num)).mp hlow
    have hk_lt : k < C.ncard := by
      rw [hk] at hLlt
      exact (Nat.pow_lt_pow_iff_right (show (1:ℕ) < 7 by norm_num)).mp hLlt
    have hk_eq : k = C.ncard - 1 := by omega
    have hLcard : Nat.card ↥L = 7 ^ (C.ncard - 1) := by rw [hk, hk_eq]
    have hrank : IsElemAbelianOfRank 7 (C.ncard - 1) ↥L :=
      w16g_isElemAbelianOfRank_of_card
        (fun a b : ↥L => Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W))
          (h.hXe.1.is_comm.comm ⟨a.1, hLle a.2⟩ ⟨b.1, hLle b.2⟩)))
        (fun a : ↥L => Subtype.ext (by simpa using h.hXe.2 a.1 (hLle a.2)))
        hLcard
    have hcomm_eq : commSub ⊤ L = ⨆ U : ↥C, (U.1 : Subgroup W) := by
      rw [commSub_top_eq_iSup_s13Supp h.hW (p := 7) (by norm_num) (by norm_num) h.hXe hLle,
        hLsupp]
      exact iSup_subtype' (p := fun U => U ∈ C) (f := fun U (_ : U ∈ C) => U)
    have hindC : iSupIndep (fun U : ↥C => (U.1 : Subgroup W)) :=
      (sSupIndep_iff C).mp ((s13IsoComps_sSupIndep h.hW hodd).mono hCsub)
    haveI : Fintype ↥C := Fintype.ofFinite _
    have hrkL : rk ↥(commSub ⊤ L) = 3 * C.ncard := by
      rw [hcomm_eq, w16g_rk_iSup_eq_sum (fun w => by rw [pow_two]; exact h.hW w)
        (fun U : ↥C => (U.1 : Subgroup W)) hindC]
      have h3 : ∀ U : ↥C, rk ↥(U.1 : Subgroup W) = 3 :=
        fun U => rk_s13IsoComps_eq_three h (hCsub U.2)
      have hsum3 : ∑ U : ↥C, rk ↥(U.1 : Subgroup W) = ∑ _ : ↥C, (3 : ℕ) :=
        Finset.sum_congr rfl fun U _ => h3 U
      rw [hsum3, Finset.sum_const, Finset.card_univ, Set.fintypeCard_eq_ncard, smul_eq_mul]
      ring
    have hQL : Q ≤ L :=
      (le_s13XSupp_iff h.hW (p := 7) (by norm_num) (by norm_num) h.hXe h.hQX).mpr
        (by rw [hsuppQ]; exact hCpair)
    have hLcomm : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ := by
      intro hbot
      obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
        by_contra hc
        push Not at hc
        exact h.hQ1 (le_bot_iff.mp (fun q hq => Subgroup.mem_bot.mpr (hc q hq)))
      have hqL : q ∈ L := hQL hqQ
      have hq2 : q ^ 2 ≠ 1 := by
        intro hq2
        have hdvd7 : orderOf q ∣ 7 :=
          orderOf_dvd_iff_pow_eq_one.mpr (h.hXe.2 q (h.hQX hqQ))
        have hdvd2 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2
        have hd : orderOf q ∣ Nat.gcd 7 2 := Nat.dvd_gcd hdvd7 hdvd2
        rw [show Nat.gcd 7 2 = 1 from by norm_num] at hd
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
        rw [w16g_s13Supp_conj (h.hXA g hg) (by simpa using h.hXA g⁻¹ (A.inv_mem hg)),
          hLsupp]
      rw [hconj, hLsupp]
      exact w16g_s13CompSet_conj_disjoint_or_eq h.hXA hg c₀
    have hind : sSupIndep (conjSubs A (commSub ⊤ L)) :=
      sSupIndep_conjSubs_of_s13Supp h.hW (p := 7) (by norm_num) (by norm_num) h.hXe
        h.hXA hLle hdisj
    refine ⟨L, hLle, ?_, ?_⟩
    · refine ⟨7, by norm_num, hLle.trans h.hXO, hLcomm, hind, ?_⟩
      by_cases hn2 : C.ncard = 2
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))))
        · refine ⟨?_, ?_⟩
          · exact isCyclic_of_prime_card (p := 7) (by norm_num [hLcard, hn2])
          · norm_num [hLcard, hn2]
        · right
          norm_num [hrkL, hn2]
      · have hn3 : 3 ≤ C.ncard := by omega
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        refine ⟨C.ncard - 1, 3, Or.inr ⟨rfl, rfl⟩, ?_, hrank, ?_, ?_⟩
        · omega
        · rw [hrkL, Nat.sub_add_cancel (by omega : 1 ≤ C.ncard)]
          ring
        ·
          have hsupC : sSup C = ⨆ U : ↥C, (U.1 : Subgroup W) :=
            le_antisymm
              (sSup_le fun V hV => le_iSup (fun U : ↥C => (U.1 : Subgroup W)) ⟨V, hV⟩)
              (iSup_le fun U => le_sSup U.2)
          have hcomm_eq' : commSub ⊤ L = sSup C := by rw [hcomm_eq, ← hsupC]
          have hCone : 1 ≤ C.ncard := le_trans (by norm_num : 1 ≤ 2) hn
          have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
          have hindS : sSupIndep (s13IsoComps X) := s13IsoComps_sSupIndep h.hW hodd
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
          have hφmem : ∀ U : ↥C, (⟨U.1, hCsub U.2⟩ : ↥(s13IsoComps X)) ∈ c₀.supp := by
            intro U
            obtain ⟨V, hV, hVU⟩ := U.2
            have hVc : (s13SuppGraph A X Q).connectedComponentMk V = c₀ :=
              (SimpleGraph.ConnectedComponent.mem_supp_iff c₀ V).mp hV
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
            have hV' : (⟨U.1, hCsub U.2⟩ : ↥(s13IsoComps X)) = V := Subtype.ext hVU.symm
            rw [hV', hVc]
          let Φ : ↥C → ↥(c₀.supp) := fun U => ⟨⟨U.1, hCsub U.2⟩, hφmem U⟩
          have hΦinj : Function.Injective Φ := by
            intro U U' h
            apply Subtype.ext
            exact congrArg (fun V : ↥(c₀.supp) => (V.1.1 : Subgroup W)) h
          have hΦsurj : Function.Surjective Φ := by
            intro V
            refine ⟨⟨V.1.1, ⟨V.1, V.2, rfl⟩⟩, ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
          let e : ↥C ≃ ↥(c₀.supp) := Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
          let f : ↥C → ↥(s13IsoComps X) := fun U => ⟨U.1, hCsub U.2⟩
          let G : SimpleGraph ↥C := (s13SuppGraph A X Q).comap f
          have hiso : G ≃g c₀.toSimpleGraph :=
            { toEquiv := e
              map_rel_iff' := by
                rintro U U'
                rw [SimpleGraph.comap_adj]
                change (s13SuppGraph A X Q).Adj (f U) (f U') ↔
                  (s13SuppGraph A X Q).Adj (e U).1 (e U').1
                rfl }
          have hconn : G.Connected :=
            (SimpleGraph.Iso.connected_iff hiso).mpr c₀.connected_toSimpleGraph
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
          have htC : ∀ U ∈ C, U.map t.toMonoidHom ∈ C := by
            intro U hU
            by_cases hU0 : U = U₀
            · rw [hU0, ← htmap]; exact hU₁C
            · by_cases hU1 : U = U₁
              · have hmap : U₁.map t.toMonoidHom = U₀ := by
                  rw [htmap, Subgroup.map_map,
                    show t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W from by
                      ext x; rw [MonoidHom.comp_apply]
                      show t (t x) = x
                      rw [show t (t x) = (t * t) x from rfl, ht2']
                      rfl, Subgroup.map_id]
                rw [hU1, hmap]; exact hU₀C
              · rw [hmap_eq_of_fix (g := t) (V := U) ht2'
                  (hfixQ U (hCsub hU) hU0 hU1)]; exact hU
          have ht_mem : t ∈ A ⊓ stabSub (sSup C) :=
            ⟨h.htA, hstab_of_maps ht2' htC⟩
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
          have hedge : ∀ U U' : ↥C, G.Adj U U' → ∃ g ∈ A ⊓ stabSub (sSup C),
              U.1.map g.toMonoidHom = U'.1 ∧ U'.1.map g.toMonoidHom = U.1 ∧
                ∀ V ∈ C, V ≠ U.1 → V ≠ U'.1 → V.map g.toMonoidHom = V := by
            intro U U' hUU'
            have hrel : (s13SuppGraph A X Q).Adj (f U) (f U') := SimpleGraph.comap_adj.mp hUU'
            rw [s13SuppGraph, SimpleGraph.fromRel_adj] at hrel
            obtain ⟨hne, hrel⟩ := hrel
            have hmain : ∀ {a : MulAut W}, a ∈ A →
                s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = {U.1, U'.1} →
                ∃ g ∈ A ⊓ stabSub (sSup C), U.1.map g.toMonoidHom = U'.1 ∧
                  U'.1.map g.toMonoidHom = U.1 ∧
                  ∀ V ∈ C, V ≠ U.1 → V ≠ U'.1 → V.map g.toMonoidHom = V := by
              intro a ha hsupp
              obtain ⟨P₀, P₁, hPne, hPsupp, hPmap, hPfix, -⟩ := s13_seven_pair (h.conj ha)
              have hset : ({P₀, P₁} : Set (Subgroup W)) = {U.1, U'.1} := by rw [← hPsupp, hsupp]
              have hg2 : (a * t * a⁻¹) * (a * t * a⁻¹) = 1 := by
                have := (h.conj ha).ht2; rwa [pow_two] at this
              obtain ⟨hswap1, hswap2⟩ := key (S := U.1) (T := U'.1) hg2 hPne hPmap hset
                (fun h => hne (Subtype.ext h))
              have hfixC : ∀ V ∈ C, V ≠ U.1 → V ≠ U'.1 →
                  V.map (a * t * a⁻¹).toMonoidHom = V := by
                intro V hV hV1 hV2
                have hVP : V ≠ P₀ ∧ V ≠ P₁ := by
                  have hnot : V ∉ ({P₀, P₁} : Set (Subgroup W)) := by
                    rw [hset]; simp [hV1, hV2]
                  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hnot
                exact hmap_eq_of_fix (g := a * t * a⁻¹) (V := V) hg2
                  (hPfix V (hCsub hV) hVP.1 hVP.2)
              have hgC : ∀ V ∈ C, V.map (a * t * a⁻¹).toMonoidHom ∈ C := by
                intro V hV
                by_cases hV1 : V = U.1
                · rw [hV1, hswap1]; exact U'.2
                · by_cases hV2 : V = U'.1
                  · rw [hV2, hswap2]; exact U.2
                  · rw [hfixC V hV hV1 hV2]; exact hV
              exact ⟨a * t * a⁻¹,
                ⟨A.mul_mem (A.mul_mem ha h.htA) (A.inv_mem ha), hstab_of_maps hg2 hgC⟩,
                hswap1, hswap2, hfixC⟩
            rcases hrel with hrel | hrel
            · obtain ⟨a, ha, hsupp⟩ := hrel
              exact hmain (a := a) ha hsupp
            · obtain ⟨a, ha, hsupp⟩ := hrel
              refine hmain (a := a) ha ?_
              rw [hsupp, Set.pair_comm]
          have htswap : ∃ U ∈ C, ∃ U' ∈ C, U ≠ U' ∧ U.map t.toMonoidHom = U' ∧
              U'.map t.toMonoidHom = U ∧
              ∀ V ∈ C, V ≠ U → V ≠ U' → V.map t.toMonoidHom = V := by
            refine ⟨U₀, hU₀C, U₁, hU₁C, hne01, htmap.symm, ?_, ?_⟩
            · rw [htmap, Subgroup.map_map,
                show t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W from by
                  ext x; rw [MonoidHom.comp_apply]
                  show t (t x) = x
                  rw [show t (t x) = (t * t) x from rfl, ht2']
                  rfl, Subgroup.map_id]
            · intro V hV hV0 hV1
              exact hmap_eq_of_fix (g := t) (V := V) ht2' (hfixQ V (hCsub hV) hV0 hV1)
          have htfix : (2 < C.ncard - 1) → ∀ V ∈ C, V.map t.toMonoidHom = V →
              ∀ x ∈ V, t x = x := by
            intro _ V hV hVmap x hx
            have hV0 : V ≠ U₀ := by
              intro h
              rw [h] at hVmap
              exact hne01 (by rw [← hVmap, htmap])
            have hV1 : V ≠ U₁ := by
              intro h
              rw [h] at hVmap
              have hmap : U₁.map t.toMonoidHom = U₀ := by
                rw [htmap, Subgroup.map_map,
                  show t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W from by
                    ext y; rw [MonoidHom.comp_apply]
                    show t (t y) = y
                    rw [show t (t y) = (t * t) y from rfl, ht2']
                    rfl, Subgroup.map_id]
              exact hne01 (hmap.symm.trans hVmap)
            have hle : V ≤ fixV (Subgroup.zpowers t) :=
              commSub_eq_bot_iff.mp (hfixQ V (hCsub hV) hV0 hV1)
            exact (mem_fixV.mp (hle hx)) t (Subgroup.mem_zpowers t)
          rw [hcomm_eq']
          exact s13_deltaSym_of_edge_swaps C (Nat.sub_add_cancel hCone).symm
            (fun U hU => rk_s13IsoComps_eq_three h (hCsub hU))
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
    · rw [hLsupp]
  ·
    push Not at hH0
    obtain ⟨y, hyX, hy1, hysupp⟩ := hH0
    obtain ⟨L, hLX, hLcomm, hind, hLsupp1, hbranch⟩ :=
      exists_of_singleton_supp h hyX hy1 hysupp
    have hLcard : Nat.card ↥L = 7 := by
      rcases hbranch with ⟨h73, -⟩ | ⟨-, hcard, -⟩
      · exact absurd h73 (by norm_num)
      · exact hcard
    have hrk : rk ↥(commSub ⊤ L) = 3 := by
      rcases hbranch with ⟨h73, -⟩ | ⟨-, -, hrk⟩
      · exact absurd h73 (by norm_num)
      · exact hrk
    have hcyc : IsCyclicOrd ↥L 7 := by
      refine ⟨?_, hLcard⟩
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      exact isCyclic_of_prime_card hLcard
    have hconc : Conc4_133 A t L := by
      refine ⟨7, by norm_num, hLX.trans h.hXO, hLcomm, hind, ?_⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcyc, Or.inl hrk⟩))))
    have hclose : L = s13XSupp X (s13Supp X L) := by
      obtain ⟨U', hU'⟩ := Set.ncard_eq_one.mp hLsupp1
      have hU'mem : U' ∈ s13IsoComps X := by
        have h : U' ∈ s13Supp X L := by rw [hU']; exact Set.mem_singleton U'
        exact h.1
      have hle : L ≤ s13XSupp X (s13Supp X L) :=
        (le_s13XSupp_iff h.hW (p := 7) (by norm_num) (by norm_num) h.hXe hLX).mpr
          (le_refl _)
      have hcardle : Nat.card ↥(s13XSupp X (s13Supp X L)) ≤ Nat.card ↥L := by
        rw [hU', hLcard]
        exact card_s13XSupp_singleton_le h.hW (p := 7) (by norm_num) (by norm_num) h.hXe hU'mem
      exact Subgroup.eq_of_le_of_card_ge hle hcardle
    exact ⟨L, hLX, hconc, hclose⟩

end CFSG.LocalAnalysis.WeakClosure81
