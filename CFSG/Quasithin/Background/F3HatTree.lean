module

public import CFSG.Quasithin.Background.F3Amalgam
public import CFSG.Quasithin.Recognition.GoldschmidtTreeAcyclic

public section

namespace CFSG.Quasithin

universe u

namespace RankTwoAmalgam

variable (α : RankTwoAmalgam.{u})

@[expose] def toGold (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2) :
    GoldAmalgam α.G1 α.G12 α.G2 where
  toA := α.α1
  toB := α.α2
  toA_injective := h1
  toB_injective := h2

private noncomputable def ghatMu (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    ∀ d, α.toAmalgam.X d →* (α.toGold h1 h2).Universal
  | .one => (α.toGold h1 h2).ofA
  | .two => (α.toGold h1 h2).ofB
  | .onetwo => (α.toGold h1 h2).ofA.comp α.α1

private theorem ghatMu_compat (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    ∀ {d e : RankTwoIndex} (h : d ≤ e) (x : α.toAmalgam.X d),
      (α.ghatMu h1 h2) e (α.toAmalgam.map h x) = (α.ghatMu h1 h2) d x := by
  intro d e h x
  cases d <;> cases e <;>
    first
      | rfl
      | exact h.elim
      | exact (GoldAmalgam.ofB_toB (α.toGold h1 h2) x).trans
          (GoldAmalgam.ofA_toA (α.toGold h1 h2) x).symm

private noncomputable def ghatToGold (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) : α.Ghat →* (α.toGold h1 h2).Universal :=
  Amalgam.lift (α := α.toAmalgam) (α.ghatMu h1 h2) (α.ghatMu_compat h1 h2)

private noncomputable def goldMu (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    ∀ b : Bool, goldVertexGroup α.G1 α.G2 b →* α.Ghat
  | true => Amalgam.ξ α.toAmalgam RankTwoIndex.one
  | false => Amalgam.ξ α.toAmalgam RankTwoIndex.two

@[simp] private theorem goldMu_true (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.goldMu h1 h2 true = Amalgam.ξ α.toAmalgam RankTwoIndex.one := rfl

@[simp] private theorem goldMu_false (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.goldMu h1 h2 false = Amalgam.ξ α.toAmalgam RankTwoIndex.two := rfl

private noncomputable def goldEdge (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) : α.G12 →* α.Ghat :=
  Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo

private noncomputable def goldToGhat (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) : (α.toGold h1 h2).Universal →* α.Ghat :=
  Monoid.PushoutI.lift (α.goldMu h1 h2) (α.goldEdge h1 h2)
    (by
      intro b
      cases b
      · ext x
        exact Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo)
          (e := RankTwoIndex.two) trivial x
      · ext x
        exact Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo)
          (e := RankTwoIndex.one) trivial x)

@[simp] private theorem ghatMu_one (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.ghatMu h1 h2 RankTwoIndex.one = (α.toGold h1 h2).ofA := rfl

@[simp] private theorem ghatMu_two (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.ghatMu h1 h2 RankTwoIndex.two = (α.toGold h1 h2).ofB := rfl

@[simp] private theorem ghatMu_onetwo (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.ghatMu h1 h2 RankTwoIndex.onetwo = (α.toGold h1 h2).ofA.comp α.α1 := rfl

private theorem ghatToGold_xi_one (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) (g : α.toAmalgam.X RankTwoIndex.one) :
    α.ghatToGold h1 h2 (Amalgam.ξ α.toAmalgam RankTwoIndex.one g) =
      (α.toGold h1 h2).ofA (show α.G1 from g) :=
  Amalgam.lift_ξ (α := α.toAmalgam) (μ := α.ghatMu h1 h2)
    (hμ := α.ghatMu_compat h1 h2) RankTwoIndex.one g

private theorem ghatToGold_xi_two (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) (g : α.toAmalgam.X RankTwoIndex.two) :
    α.ghatToGold h1 h2 (Amalgam.ξ α.toAmalgam RankTwoIndex.two g) =
      (α.toGold h1 h2).ofB (show α.G2 from g) :=
  Amalgam.lift_ξ (α := α.toAmalgam) (μ := α.ghatMu h1 h2)
    (hμ := α.ghatMu_compat h1 h2) RankTwoIndex.two g

private theorem ghatToGold_xi_onetwo (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) (g : α.toAmalgam.X RankTwoIndex.onetwo) :
    α.ghatToGold h1 h2 (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g) =
      (α.toGold h1 h2).ofA (α.α1 (show α.G12 from g)) :=
  Amalgam.lift_ξ (α := α.toAmalgam) (μ := α.ghatMu h1 h2)
    (hμ := α.ghatMu_compat h1 h2) RankTwoIndex.onetwo g

private theorem goldToGhat_ghatToGold (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    (α.goldToGhat h1 h2).comp (α.ghatToGold h1 h2) = MonoidHom.id α.Ghat := by
  refine Amalgam.hom_ext (α := α.toAmalgam) ?_
  intro d x
  cases d with
  | one =>
    change α.goldToGhat h1 h2 (α.ghatToGold h1 h2
      (Amalgam.ξ α.toAmalgam RankTwoIndex.one x)) =
      Amalgam.ξ α.toAmalgam RankTwoIndex.one x
    rw [α.ghatToGold_xi_one h1 h2 x, goldToGhat]
    change (Monoid.PushoutI.lift (α.goldMu h1 h2) (α.goldEdge h1 h2) _)
      (Monoid.PushoutI.of (φ := (α.toGold h1 h2).diagram) true
        (show goldVertexGroup α.G1 α.G2 true from x)) = _
    rw [Monoid.PushoutI.lift_of]
    rfl
  | two =>
    change α.goldToGhat h1 h2 (α.ghatToGold h1 h2
      (Amalgam.ξ α.toAmalgam RankTwoIndex.two x)) =
      Amalgam.ξ α.toAmalgam RankTwoIndex.two x
    rw [α.ghatToGold_xi_two h1 h2 x, goldToGhat]
    change (Monoid.PushoutI.lift (α.goldMu h1 h2) (α.goldEdge h1 h2) _)
      (Monoid.PushoutI.of (φ := (α.toGold h1 h2).diagram) false
        (show goldVertexGroup α.G1 α.G2 false from x)) = _
    rw [Monoid.PushoutI.lift_of]
    rfl
  | onetwo =>
    change α.goldToGhat h1 h2 (α.ghatToGold h1 h2
      (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo x)) =
      Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo x
    rw [α.ghatToGold_xi_onetwo h1 h2 x, goldToGhat]
    change (Monoid.PushoutI.lift (α.goldMu h1 h2) (α.goldEdge h1 h2) _)
      (Monoid.PushoutI.of (φ := (α.toGold h1 h2).diagram) true
        (α.α1 (show α.G12 from x))) = _
    rw [Monoid.PushoutI.lift_of]
    exact Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo)
      (e := RankTwoIndex.one) trivial (show α.G12 from x)

private theorem ghatToGold_goldToGhat (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    (α.ghatToGold h1 h2).comp (α.goldToGhat h1 h2) =
      MonoidHom.id (α.toGold h1 h2).Universal := by
  refine Monoid.PushoutI.hom_ext_nonempty (φ := (α.toGold h1 h2).diagram) ?_
  intro b
  cases b
  · ext x
    change α.ghatToGold h1 h2 (α.goldToGhat h1 h2
      ((α.toGold h1 h2).ofB x)) = (α.toGold h1 h2).ofB x
    rw [goldToGhat]
    change α.ghatToGold h1 h2
      ((Monoid.PushoutI.lift (α.goldMu h1 h2) (α.goldEdge h1 h2) _)
        (Monoid.PushoutI.of (φ := (α.toGold h1 h2).diagram) false x)) = _
    rw [Monoid.PushoutI.lift_of]
    rw [α.goldMu_false]
    change α.ghatToGold h1 h2
      (Amalgam.ξ α.toAmalgam RankTwoIndex.two
        (show α.toAmalgam.X RankTwoIndex.two from x)) = _
    rw [α.ghatToGold_xi_two h1 h2 (show α.toAmalgam.X RankTwoIndex.two from x)]
  · ext x
    change α.ghatToGold h1 h2 (α.goldToGhat h1 h2
      ((α.toGold h1 h2).ofA x)) = (α.toGold h1 h2).ofA x
    rw [goldToGhat]
    change α.ghatToGold h1 h2
      ((Monoid.PushoutI.lift (α.goldMu h1 h2) (α.goldEdge h1 h2) _)
        (Monoid.PushoutI.of (φ := (α.toGold h1 h2).diagram) true x)) = _
    rw [Monoid.PushoutI.lift_of]
    rw [α.goldMu_true]
    change α.ghatToGold h1 h2
      (Amalgam.ξ α.toAmalgam RankTwoIndex.one
        (show α.toAmalgam.X RankTwoIndex.one from x)) = _
    rw [α.ghatToGold_xi_one h1 h2 (show α.toAmalgam.X RankTwoIndex.one from x)]

noncomputable def ghatEquiv (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2) :
    α.Ghat ≃* (α.toGold h1 h2).Universal where
  toFun := α.ghatToGold h1 h2
  invFun := α.goldToGhat h1 h2
  left_inv x := by
    have h := congrArg (fun f : α.Ghat →* α.Ghat => f x) (α.goldToGhat_ghatToGold h1 h2)
    simpa using h
  right_inv x := by
    have h := congrArg (fun f : (α.toGold h1 h2).Universal →* (α.toGold h1 h2).Universal =>
      f x) (α.ghatToGold_goldToGhat h1 h2)
    simpa using h
  map_mul' := (α.ghatToGold h1 h2).map_mul

@[simp] theorem ghatEquiv_xi1 (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2)
    (g : α.G1) :
    α.ghatEquiv h1 h2 (Amalgam.ξ α.toAmalgam RankTwoIndex.one g) =
      (α.toGold h1 h2).ofA g := by
  exact α.ghatToGold_xi_one h1 h2 (show α.toAmalgam.X RankTwoIndex.one from g)

@[simp] theorem ghatEquiv_xi2 (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2)
    (g : α.G2) :
    α.ghatEquiv h1 h2 (Amalgam.ξ α.toAmalgam RankTwoIndex.two g) =
      (α.toGold h1 h2).ofB g := by
  exact α.ghatToGold_xi_two h1 h2 (show α.toAmalgam.X RankTwoIndex.two from g)

@[simp] theorem ghatEquiv_xi12 (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2)
    (g : α.G12) :
    α.ghatEquiv h1 h2 (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g) =
      (α.toGold h1 h2).ofA (α.α1 g) := by
  exact α.ghatToGold_xi_onetwo h1 h2 (show α.toAmalgam.X RankTwoIndex.onetwo from g)

theorem map_ghatEquiv_Ghat1 (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2) :
    α.Ghat1.map (α.ghatEquiv h1 h2).toMonoidHom = (α.toGold h1 h2).ofA.range := by
  change (Amalgam.ξ α.toAmalgam RankTwoIndex.one).range.map
    (α.ghatEquiv h1 h2).toMonoidHom = _
  rw [← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (MonoidHom.ext fun g => α.ghatToGold_xi_one h1 h2 g)

theorem map_ghatEquiv_Ghat2 (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2) :
    α.Ghat2.map (α.ghatEquiv h1 h2).toMonoidHom = (α.toGold h1 h2).ofB.range := by
  change (Amalgam.ξ α.toAmalgam RankTwoIndex.two).range.map
    (α.ghatEquiv h1 h2).toMonoidHom = _
  rw [← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (MonoidHom.ext fun g => α.ghatToGold_xi_two h1 h2 g)

private noncomputable def ghatSubgroupEquiv (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    ↥(α.Ghat1 ⊔ α.Ghat2) ≃* (α.toGold h1 h2).Universal :=
  MulEquiv.ofBijective
    ((α.ghatEquiv h1 h2).toMonoidHom.comp (α.Ghat1 ⊔ α.Ghat2).subtype)
    ⟨(α.ghatEquiv h1 h2).injective.comp (α.Ghat1 ⊔ α.Ghat2).subtype_injective,
      fun x => ⟨⟨(α.ghatEquiv h1 h2).symm x, by
        rw [α.Ghat1_sup_Ghat2]
        exact Subgroup.mem_top _⟩, by simp⟩⟩

@[simp] private theorem toMonoidHom_ghatSubgroupEquiv (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) (g : ↥(α.Ghat1 ⊔ α.Ghat2)) :
    (α.ghatSubgroupEquiv h1 h2).toMonoidHom g = α.ghatEquiv h1 h2 (g : α.Ghat) := by
  simp [ghatSubgroupEquiv]

@[simp] private theorem coe_ghatSubgroupEquiv (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) (g : ↥(α.Ghat1 ⊔ α.Ghat2)) :
    ((α.ghatSubgroupEquiv h1 h2) g : (α.toGold h1 h2).Universal) =
      α.ghatEquiv h1 h2 (g : α.Ghat) := by
  simp [ghatSubgroupEquiv]

private theorem map_ghatSubgroupEquiv_Ghat1 (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2)).map (α.ghatSubgroupEquiv h1 h2).toMonoidHom =
      (α.toGold h1 h2).ofA.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [toMonoidHom_ghatSubgroupEquiv, ← α.map_ghatEquiv_Ghat1 h1 h2]
    exact Subgroup.mem_map_of_mem _ hy
  · intro hx
    rw [← α.map_ghatEquiv_Ghat1 h1 h2] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, Subgroup.mem_sup_left hy⟩, hy, by
      rw [toMonoidHom_ghatSubgroupEquiv]
      rfl⟩

private theorem map_ghatSubgroupEquiv_Ghat2 (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)).map (α.ghatSubgroupEquiv h1 h2).toMonoidHom =
      (α.toGold h1 h2).ofB.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [toMonoidHom_ghatSubgroupEquiv, ← α.map_ghatEquiv_Ghat2 h1 h2]
    exact Subgroup.mem_map_of_mem _ hy
  · intro hx
    rw [← α.map_ghatEquiv_Ghat2 h1 h2] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, Subgroup.mem_sup_right hy⟩, hy, by
      rw [toMonoidHom_ghatSubgroupEquiv]
      rfl⟩

section CosetEquiv

variable {H U : Type*} [Group H] [Group U]

private noncomputable def cosetEquiv (e : H ≃* U) (P : Subgroup H) (Q : Subgroup U)
    (hPQ : P.map e.toMonoidHom = Q) : H ⧸ P ≃ U ⧸ Q where
  toFun := CosetGeom.cosetMap P Q e (Subgroup.map_le_iff_le_comap.mp hPQ.le)
  invFun := CosetGeom.cosetMap Q P e.symm (Subgroup.map_le_iff_le_comap.mp (by
    rw [← hPQ, Subgroup.map_map]
    simp))
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H a => simp [CosetGeom.cosetMap_mk]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H a => simp [CosetGeom.cosetMap_mk]

@[simp] private theorem cosetEquiv_mk (e : H ≃* U) (P : Subgroup H) (Q : Subgroup U)
    (hPQ : P.map e.toMonoidHom = Q) (a : H) :
    cosetEquiv e P Q hPQ (QuotientGroup.mk a) = QuotientGroup.mk (e a) := rfl

private theorem cosetEquiv_exists_iff (e : H ≃* U) (P Q : Subgroup H) (P' Q' : Subgroup U)
    (hP : P.map e.toMonoidHom = P') (hQ : Q.map e.toMonoidHom = Q')
    {x : H ⧸ P} {y : H ⧸ Q} :
    (∃ g : H, (g : H ⧸ P) = x ∧ (g : H ⧸ Q) = y) ↔
      ∃ u : U, (u : U ⧸ P') = cosetEquiv e P P' hP x ∧
        (u : U ⧸ Q') = cosetEquiv e Q Q' hQ y := by
  constructor
  · rintro ⟨g, rfl, rfl⟩
    exact ⟨e g, rfl, rfl⟩
  · rintro ⟨u, hu1, hu2⟩
    refine ⟨e.symm u, ?_, ?_⟩
    · exact (cosetEquiv e P P' hP).injective (by
        rw [cosetEquiv_mk, MulEquiv.apply_symm_apply]
        exact hu1)
    · exact (cosetEquiv e Q Q' hQ).injective (by
        rw [cosetEquiv_mk, MulEquiv.apply_symm_apply]
        exact hu2)

end CosetEquiv

private noncomputable def vertexEquiv (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.Γhat ≃
      ((α.toGold h1 h2).Universal ⧸ (α.toGold h1 h2).ofA.range) ⊕
        ((α.toGold h1 h2).Universal ⧸ (α.toGold h1 h2).ofB.range) :=
  Equiv.sumCongr
    (cosetEquiv (α.ghatSubgroupEquiv h1 h2) (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2))
      (α.toGold h1 h2).ofA.range (α.map_ghatSubgroupEquiv_Ghat1 h1 h2))
    (cosetEquiv (α.ghatSubgroupEquiv h1 h2) (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2))
      (α.toGold h1 h2).ofB.range (α.map_ghatSubgroupEquiv_Ghat2 h1 h2))

@[simp] private theorem vertexEquiv_inl (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2)
    (x : ↥(α.Ghat1 ⊔ α.Ghat2) ⧸ α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) :
    α.vertexEquiv h1 h2 (Sum.inl x) =
      Sum.inl (cosetEquiv (α.ghatSubgroupEquiv h1 h2)
        (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofA.range
        (α.map_ghatSubgroupEquiv_Ghat1 h1 h2) x) := rfl

@[simp] private theorem vertexEquiv_inr (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2)
    (x : ↥(α.Ghat1 ⊔ α.Ghat2) ⧸ α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) :
    α.vertexEquiv h1 h2 (Sum.inr x) =
      Sum.inr (cosetEquiv (α.ghatSubgroupEquiv h1 h2)
        (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofB.range
        (α.map_ghatSubgroupEquiv_Ghat2 h1 h2) x) := rfl

noncomputable def graphHatIso (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) :
    α.graphHat ≃g (α.toGold h1 h2).treeGraph where
  toEquiv := α.vertexEquiv h1 h2
  map_rel_iff' := by
    intro v w
    cases v with
    | inl x =>
      cases w with
      | inl y =>
        simp only [vertexEquiv_inl]
        exact iff_of_false (by
          simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel])
          CosetGeom.not_adj_inl_inl
      | inr y =>
        rw [vertexEquiv_inl, vertexEquiv_inr, CosetGeom.adj_inl_inr,
          goldCosetGraph_adj_inl_inr]
        exact (cosetEquiv_exists_iff (α.ghatSubgroupEquiv h1 h2)
          (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2))
          (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofA.range
          (α.toGold h1 h2).ofB.range (α.map_ghatSubgroupEquiv_Ghat1 h1 h2)
          (α.map_ghatSubgroupEquiv_Ghat2 h1 h2)).symm
    | inr x =>
      cases w with
      | inl y =>
        have htarget : (goldCosetGraph (α.toGold h1 h2).ofA.range
            (α.toGold h1 h2).ofB.range).Adj
              (Sum.inr (cosetEquiv (α.ghatSubgroupEquiv h1 h2)
                (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofB.range
                (α.map_ghatSubgroupEquiv_Ghat2 h1 h2) x))
              (Sum.inl (cosetEquiv (α.ghatSubgroupEquiv h1 h2)
                (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofA.range
                (α.map_ghatSubgroupEquiv_Ghat1 h1 h2) y)) ↔
          ∃ u : (α.toGold h1 h2).Universal,
            (u : (α.toGold h1 h2).Universal ⧸ (α.toGold h1 h2).ofA.range) =
              cosetEquiv (α.ghatSubgroupEquiv h1 h2)
                (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofA.range
                (α.map_ghatSubgroupEquiv_Ghat1 h1 h2) y ∧
            (u : (α.toGold h1 h2).Universal ⧸ (α.toGold h1 h2).ofB.range) =
              cosetEquiv (α.ghatSubgroupEquiv h1 h2)
                (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofB.range
                (α.map_ghatSubgroupEquiv_Ghat2 h1 h2) x := by
          rw [SimpleGraph.adj_comm]
          exact goldCosetGraph_adj_inl_inr _ _ _ _
        rw [vertexEquiv_inr, vertexEquiv_inl, htarget, CosetGeom.adj_inr_inl]
        exact (cosetEquiv_exists_iff (α.ghatSubgroupEquiv h1 h2)
          (α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2))
          (α.Ghat2.subgroupOf (α.Ghat1 ⊔ α.Ghat2)) (α.toGold h1 h2).ofA.range
          (α.toGold h1 h2).ofB.range (α.map_ghatSubgroupEquiv_Ghat1 h1 h2)
          (α.map_ghatSubgroupEquiv_Ghat2 h1 h2) (x := y) (y := x)).symm
      | inr y =>
        simp only [vertexEquiv_inr]
        exact iff_of_false (by
          simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel])
          CosetGeom.not_adj_inr_inr

@[simp] private theorem graphHatIso_apply (h1 : Function.Injective α.α1)
    (h2 : Function.Injective α.α2) (v : α.Γhat) :
    α.graphHatIso h1 h2 v = α.vertexEquiv h1 h2 v := rfl

theorem graphHat_isTree (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2) :
    α.graphHat.IsTree :=
  (α.graphHatIso h1 h2).isTree_iff.mpr (α.toGold h1 h2).treeGraph_isTree

theorem graphHat_isAcyclic (h1 : Function.Injective α.α1) (h2 : Function.Injective α.α2) :
    α.graphHat.IsAcyclic :=
  (α.graphHatIso h1 h2).isAcyclic_iff.mpr (α.toGold h1 h2).treeGraph_isAcyclic

end RankTwoAmalgam

end CFSG.Quasithin
