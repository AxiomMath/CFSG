module

public import CFSG.Quasithin.Background.F3Paths
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.Quasithin.RonanF5C

open scoped Pointwise

universe u v u' v'

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
variable {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]

theorem faithfulSMul_iff (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w) :
    FaithfulSMul G X ↔ FaithfulSMul Gb Xb := by
  constructor
  · intro hG
    refine ⟨fun {gb1 gb2} h => ?_⟩
    obtain ⟨g1, rfl⟩ := groupIso.surjective gb1
    obtain ⟨g2, rfl⟩ := groupIso.surjective gb2
    have hg : g1 = g2 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
      intro w
      apply vertexIso.injective
      rw [equivariant, equivariant]
      exact h (vertexIso w)
    rw [hg]
  · intro hb
    refine ⟨fun {g1 g2} h => ?_⟩
    apply groupIso.injective
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Xb)
    intro ab
    obtain ⟨w, rfl⟩ := vertexIso.surjective ab
    rw [← equivariant, ← equivariant, h w]

theorem graphAction_iff (Γ : SimpleGraph X) (Γb : SimpleGraph Xb)
    (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (adjacency : ∀ a b : X, Γ.Adj a b ↔ Γb.Adj (vertexIso a) (vertexIso b)) :
    CFSG.Quasithin.GraphAction G Γ ↔ CFSG.Quasithin.GraphAction Gb Γb := by
  constructor
  · intro hG
    refine ⟨fun gb ab bb => ?_⟩
    obtain ⟨g, rfl⟩ := groupIso.surjective gb
    obtain ⟨a, rfl⟩ := vertexIso.surjective ab
    obtain ⟨b, rfl⟩ := vertexIso.surjective bb
    rw [← equivariant, ← equivariant, ← adjacency, ← adjacency]
    exact hG.adj_smul g a b
  · intro hb
    refine ⟨fun g a b => ?_⟩
    rw [adjacency, adjacency, equivariant, equivariant]
    exact hb.adj_smul (groupIso g) (vertexIso a) (vertexIso b)

theorem transitive_iff (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (x : X) (xb : Xb) (point : vertexIso x = xb) :
    (∀ w : X, ∃ g : G, g • x = w) ↔ (∀ wb : Xb, ∃ gb : Gb, gb • xb = wb) := by
  subst point
  constructor
  · intro h wb
    obtain ⟨w, rfl⟩ := vertexIso.surjective wb
    obtain ⟨g, hg⟩ := h w
    refine ⟨groupIso g, ?_⟩
    rw [← equivariant, hg]
  · intro h w
    obtain ⟨gb, hgb⟩ := h (vertexIso w)
    refine ⟨groupIso.symm gb, ?_⟩
    apply vertexIso.injective
    rw [equivariant, MulEquiv.apply_symm_apply]
    exact hgb

theorem edgeSet_orbit_iff (Γ : SimpleGraph X) (Γb : SimpleGraph Xb)
    (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (adjacency : ∀ a b : X, Γ.Adj a b ↔ Γb.Adj (vertexIso a) (vertexIso b))
    (x y : X) (xb yb : Xb) (point : vertexIso x = xb) (otherPoint : vertexIso y = yb) :
    Γ.edgeSet = Set.range (fun g : G => s(g • x, g • y)) ↔
      Γb.edgeSet = Set.range (fun g : Gb => s(g • xb, g • yb)) := by
  subst point otherPoint
  have hmap : ∀ (g : G) (a b : X),
      s(groupIso g • vertexIso a, groupIso g • vertexIso b) =
        Sym2.map vertexIso s(g • a, g • b) := by
    intro g a b
    rw [Sym2.map_mk, equivariant, equivariant]
  have hinj : Function.Injective (Sym2.map vertexIso) := Sym2.map.injective vertexIso.injective
  have hadj : ∀ a b : X, s(vertexIso a, vertexIso b) ∈ Γb.edgeSet ↔ s(a, b) ∈ Γ.edgeSet := by
    intro a b
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, adjacency]
  have hrange : ∀ a b : X,
      s(vertexIso a, vertexIso b) ∈ Set.range (fun g : Gb => s(g • vertexIso x, g • vertexIso y)) ↔
        s(a, b) ∈ Set.range (fun g : G => s(g • x, g • y)) := by
    intro a b
    constructor
    · rintro ⟨gb, hgb⟩
      obtain ⟨g, rfl⟩ := groupIso.surjective gb
      have hgb' : s(groupIso g • vertexIso x, groupIso g • vertexIso y) =
          s(vertexIso a, vertexIso b) := hgb
      rw [hmap, ← Sym2.map_mk vertexIso a b] at hgb'
      exact ⟨g, hinj hgb'⟩
    · rintro ⟨g, hg⟩
      have hg' : s(g • x, g • y) = s(a, b) := hg
      refine ⟨groupIso g, ?_⟩
      show s(groupIso g • vertexIso x, groupIso g • vertexIso y) = s(vertexIso a, vertexIso b)
      rw [hmap, hg', Sym2.map_mk]
  constructor
  · intro hS
    refine Set.ext (Sym2.forall.2 fun ab bb => ?_)
    obtain ⟨a, rfl⟩ := vertexIso.surjective ab
    obtain ⟨b, rfl⟩ := vertexIso.surjective bb
    rw [hadj a b, hrange a b, hS]
  · intro hSb
    refine Set.ext (Sym2.forall.2 fun a b => ?_)
    rw [← hadj a b, hSb]
    exact hrange a b

theorem swap_iff (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (I : Subgroup G) (Ib : Subgroup Gb) (subgroup : I.map groupIso.toMonoidHom = Ib)
    (x y : X) (xb yb : Xb) (point : vertexIso x = xb) (otherPoint : vertexIso y = yb) :
    (∃ t ∈ I, t • x = y ∧ t • y = x) ↔ (∃ t ∈ Ib, t • xb = yb ∧ t • yb = xb) := by
  subst point otherPoint subgroup
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨groupIso t, SetLike.mem_coe.mpr (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩), ?_, ?_⟩
    · rw [← equivariant, h1]
    · rw [← equivariant, h2]
  · rintro ⟨tb, htb, h1, h2⟩
    obtain ⟨t, ht, ht'⟩ := Subgroup.mem_map.mp htb
    have hteq : groupIso t = tb := ht'
    subst hteq
    refine ⟨t, ht, ?_, ?_⟩
    · apply vertexIso.injective
      rw [equivariant]
      exact h1
    · apply vertexIso.injective
      rw [equivariant]
      exact h2

theorem subgraph_edgeSet_iff (Γ : SimpleGraph X) (Γb : SimpleGraph Xb)
    (ΓI : Γ.Subgraph) (ΓIb : Γb.Subgraph)
    (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (I : Subgroup G) (Ib : Subgroup Gb) (subgroup : I.map groupIso.toMonoidHom = Ib)
    (subgraphAdjacency : ∀ a b : X,
      ΓI.spanningCoe.Adj a b ↔ ΓIb.spanningCoe.Adj (vertexIso a) (vertexIso b))
    (x y : X) (xb yb : Xb) (point : vertexIso x = xb) (otherPoint : vertexIso y = yb) :
    ΓI.edgeSet = (fun i : G => s(i • x, i • y)) '' (I : Set G) ↔
      ΓIb.edgeSet = (fun i : Gb => s(i • xb, i • yb)) '' (Ib : Set Gb) := by
  subst point otherPoint subgroup
  have hT : Function.Injective (Sym2.map vertexIso) := Sym2.map.injective vertexIso.injective
  have hTs : Function.Surjective (Sym2.map vertexIso) := by
    intro e
    induction e using Sym2.ind with
    | h a b => exact ⟨s(vertexIso.symm a, vertexIso.symm b), by simp [Sym2.map_mk]⟩
  have hadj : ∀ a b : X, ΓI.Adj a b ↔ ΓIb.Adj (vertexIso a) (vertexIso b) := by
    intro a b
    have h := subgraphAdjacency a b
    simpa only [SimpleGraph.Subgraph.spanningCoe_adj] using h
  have hpre : Sym2.map vertexIso ⁻¹' ΓIb.edgeSet = ΓI.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [Set.mem_preimage, Sym2.map_mk, SimpleGraph.Subgraph.mem_edgeSet]
      exact (hadj a b).symm
  have himg : Sym2.map vertexIso '' ΓI.edgeSet = ΓIb.edgeSet := by
    rw [← hpre]
    exact Set.image_preimage_eq _ hTs
  have hF : Sym2.map vertexIso '' ((fun i : G => s(i • x, i • y)) '' (I : Set G))
      = (fun i : Gb => s(i • vertexIso x, i • vertexIso y)) ''
        ((I.map groupIso.toMonoidHom : Subgroup Gb) : Set Gb) := by
    ext e
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨groupIso i,
        SetLike.mem_coe.mpr (Subgroup.mem_map.mpr ⟨i, SetLike.mem_coe.mp hi, rfl⟩), ?_⟩
      simp [Sym2.map_mk, equivariant]
    · rintro ⟨_, hb, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp hb)
      refine ⟨s(i • x, i • y), ⟨i, SetLike.mem_coe.mpr hi, rfl⟩, ?_⟩
      simp [Sym2.map_mk, equivariant]
  rw [← himg, ← hF, Set.image_eq_image hT]

private lemma stabilizer_vertexIso_eq (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w) (z : X) :
    MulAction.stabilizer Gb (vertexIso z) =
      (MulAction.stabilizer G z).map groupIso.toMonoidHom := by
  ext gb
  obtain ⟨g, rfl⟩ := groupIso.surjective gb
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    MulAction.mem_stabilizer_iff, ← equivariant, vertexIso.injective.eq_iff]

theorem sup_eq_top_iff (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (I : Subgroup G) (Ib : Subgroup Gb) (subgroup : I.map groupIso.toMonoidHom = Ib)
    (x : X) (xb : Xb) (point : vertexIso x = xb) :
    MulAction.stabilizer G x ⊔ I = ⊤ ↔ MulAction.stabilizer Gb xb ⊔ Ib = ⊤ := by
  subst point
  subst subgroup
  have hinj : Function.Injective groupIso.toMonoidHom := groupIso.injective
  have hmaptop : (⊤ : Subgroup G).map groupIso.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective groupIso.toMonoidHom groupIso.surjective
  have key : ∀ H : Subgroup G, H.map groupIso.toMonoidHom = ⊤ ↔ H = ⊤ := by
    intro H
    rw [← hmaptop]
    exact (Subgroup.map_injective hinj).eq_iff
  rw [stabilizer_vertexIso_eq groupIso vertexIso equivariant x, ← Subgroup.map_sup, key]

theorem stab_eq_iff (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (I : Subgroup G) (Ib : Subgroup Gb) (subgroup : I.map groupIso.toMonoidHom = Ib)
    (x y : X) (xb yb : Xb) (point : vertexIso x = xb) (otherPoint : vertexIso y = yb) :
    MulAction.stabilizer G x =
        (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) ⊔
          (I ⊓ MulAction.stabilizer G x) ↔
      MulAction.stabilizer Gb xb =
        (MulAction.stabilizer Gb xb ⊓ MulAction.stabilizer Gb yb) ⊔
          (Ib ⊓ MulAction.stabilizer Gb xb) := by
  subst point
  subst otherPoint
  subst subgroup
  have hinj : Function.Injective groupIso.toMonoidHom := groupIso.injective
  rw [stabilizer_vertexIso_eq groupIso vertexIso equivariant x,
    stabilizer_vertexIso_eq groupIso vertexIso equivariant y,
    ← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_sup,
    (Subgroup.map_injective hinj).eq_iff]

private lemma smul_image_vertexIso (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (g : G) (S : Set X) :
    groupIso g • (vertexIso '' S) = vertexIso '' (g • S) := by
  rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
  congr 1
  funext w
  exact (equivariant g w).symm

private lemma stabilizer_pair_vertexIso_eq (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (x y : X) :
    MulAction.stabilizer Gb ({vertexIso x, vertexIso y} : Set Xb) =
      (MulAction.stabilizer G ({x, y} : Set X)).map groupIso.toMonoidHom := by
  rw [← Set.image_pair vertexIso x y]
  ext gb
  obtain ⟨g, rfl⟩ := groupIso.surjective gb
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    MulAction.mem_stabilizer_iff, smul_image_vertexIso groupIso vertexIso equivariant,
    (Set.image_injective.mpr vertexIso.injective).eq_iff]

theorem I_eq_iff (groupIso : G ≃* Gb) (vertexIso : X ≃ Xb)
    (equivariant : ∀ g : G, ∀ w : X, vertexIso (g • w) = groupIso g • vertexIso w)
    (I : Subgroup G) (Ib : Subgroup Gb) (subgroup : I.map groupIso.toMonoidHom = Ib)
    (x y : X) (xb yb : Xb) (point : vertexIso x = xb) (otherPoint : vertexIso y = yb) :
    I = (I ⊓ MulAction.stabilizer G x) ⊔
        (I ⊓ MulAction.stabilizer G ({x, y} : Set X)) ↔
      Ib = (Ib ⊓ MulAction.stabilizer Gb xb) ⊔
        (Ib ⊓ MulAction.stabilizer Gb ({xb, yb} : Set Xb)) := by
  subst point
  subst otherPoint
  subst subgroup
  have hinj : Function.Injective groupIso.toMonoidHom := groupIso.injective
  rw [stabilizer_vertexIso_eq groupIso vertexIso equivariant x,
    stabilizer_pair_vertexIso_eq groupIso vertexIso equivariant x y,
    ← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_sup,
    (Subgroup.map_injective hinj).eq_iff]

end CFSG.Quasithin.RonanF5C
