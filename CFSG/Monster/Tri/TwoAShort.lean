module

public import CFSG.Monster.Tri.Equivariant
public import CFSG.Monster.GMS.TwoAGraph
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.YGroups CFSG.Monster.B.Recog CFSG.Monster.GMS

variable {G : Type*} [Group G] {a : G}

@[expose] def baseVertex (a : G) : ConjVert a := ⟨a, IsConj.refl a⟩

@[simp] theorem coe_baseVertex (a : G) : ((baseVertex a : ConjVert a) : G) = a := rfl

@[expose] def longTri (a : G) (x y z : ConjVert a) : Prop :=
  (twoAGraph a).Adj x y ∧ (twoAGraph a).Adj y z ∧ (twoAGraph a).Adj z x ∧ (z : G) ≠ x * y

open scoped Classical in
@[expose] noncomputable def shortMid (a : G) (x y : ConjVert a) : ConjVert a :=
  if h : (twoAGraph a).Adj x y then ⟨x * y, h.2⟩ else x

theorem mul_self_eq_one_of_isConj (ha : a * a = 1) {z : G} (h : IsConj a z) : z * z = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 1 := by rw [ha]; group

theorem ne_one_of_isConj (ha1 : a ≠ 1) {z : G} (h : IsConj a z) : z ≠ 1 :=
  fun e => ha1 (isConj_one_left.1 (e ▸ h))

theorem conjVert_mul_self (ha : a * a = 1) (x : ConjVert a) : (x : G) * x = 1 :=
  mul_self_eq_one_of_isConj ha x.2

theorem conjVert_ne_one (ha1 : a ≠ 1) (x : ConjVert a) : (x : G) ≠ 1 :=
  ne_one_of_isConj ha1 x.2

theorem conjVert_inv (ha : a * a = 1) (x : ConjVert a) : (x : G)⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (conjVert_mul_self ha x)

theorem adj_comm (ha : a * a = 1) {x y : ConjVert a} (h : (twoAGraph a).Adj x y) :
    (x : G) * y = y * x := by
  have h1 : ((x : G) * y) * ((x : G) * y) = 1 := mul_self_eq_one_of_isConj ha h.2
  have := eq_inv_of_mul_eq_one_left h1
  rwa [mul_inv_rev, conjVert_inv ha x, conjVert_inv ha y] at this

theorem shortMid_coe {x y : ConjVert a} (h : (twoAGraph a).Adj x y) :
    ((shortMid a x y : ConjVert a) : G) = x * y := by
  simp [shortMid, h]

theorem adj_shortMid_left (ha : a * a = 1) (ha1 : a ≠ 1) {x y : ConjVert a}
    (h : (twoAGraph a).Adj x y) : (twoAGraph a).Adj x (shortMid a x y) := by
  rw [twoAGraph_adj]
  refine ⟨fun e => ?_, ?_⟩
  · have e' : (x : G) * 1 = x * y := by
      rw [mul_one, ← shortMid_coe h]
      exact congrArg Subtype.val e
    exact conjVert_ne_one ha1 y (mul_left_cancel e').symm
  · rw [shortMid_coe h]
    have : (x : G) * (x * y) = y := by rw [← mul_assoc, conjVert_mul_self ha x, one_mul]
    rw [this]
    exact y.2

theorem adj_shortMid_right (ha : a * a = 1) (ha1 : a ≠ 1) {x y : ConjVert a}
    (h : (twoAGraph a).Adj x y) : (twoAGraph a).Adj y (shortMid a x y) := by
  rw [twoAGraph_adj]
  refine ⟨fun e => ?_, ?_⟩
  · have e' : (y : G) * 1 = y * x := by
      rw [mul_one, ← adj_comm ha h, ← shortMid_coe h]
      exact congrArg Subtype.val e
    exact conjVert_ne_one ha1 x (mul_left_cancel e').symm
  · rw [shortMid_coe h]
    have : (y : G) * (x * y) = x := by
      rw [adj_comm ha h, ← mul_assoc, conjVert_mul_self ha y, one_mul]
    rw [this]
    exact x.2

theorem shortMid_shortMid (ha : a * a = 1) (ha1 : a ≠ 1) {x y : ConjVert a}
    (h : (twoAGraph a).Adj x y) : shortMid a x (shortMid a x y) = y := by
  apply Subtype.ext
  rw [shortMid_coe (adj_shortMid_left ha ha1 h), shortMid_coe h, ← mul_assoc,
    conjVert_mul_self ha x, one_mul]

theorem shortMid_comm (ha : a * a = 1) {x y : ConjVert a} (h : (twoAGraph a).Adj x y) :
    shortMid a y x = shortMid a x y := by
  apply Subtype.ext
  rw [shortMid_coe h.symm, shortMid_coe h, adj_comm ha h]

theorem shortStruct_twoAGraph (ha : a * a = 1) (ha1 : a ≠ 1) :
    ShortStruct (twoAGraph a) (shortMid a) (longTri a) where
  adj_mid_left h := adj_shortMid_left ha ha1 h
  adj_mid_right h := adj_shortMid_right ha ha1 h
  mid_mid h := shortMid_shortMid ha ha1 h
  mid_comm h := shortMid_comm ha h
  adj_mid_mid {x y u} hxy hxu hyu _ := by
    rw [twoAGraph_adj]
    refine ⟨fun e => ?_, ?_⟩
    · have e' := congrArg Subtype.val e
      rw [shortMid_coe hxy, shortMid_coe hxu] at e'
      exact hyu.ne (Subtype.ext (mul_left_cancel e'))
    · rw [shortMid_coe hxy, shortMid_coe hxu]
      have : ((x : G) * y) * (x * u) = y * u := by
        calc ((x : G) * y) * (x * u) = x * (y * x) * u := by group
          _ = x * (x * y) * u := by rw [← adj_comm ha hxy]
          _ = (x * x) * y * u := by group
          _ = y * u := by rw [conjVert_mul_self ha x, one_mul]
      rw [this]
      exact hyu.2
  lg_iff {x y z} hxy hyz hzx := by
    constructor
    · intro hL hz
      have hz' : (z : G) = x * y := by rw [hz, shortMid_coe hxy]
      have cxy := adj_comm ha hxy
      rcases hL with h | h | h | h | h | h
      · exact h.2.2.2 hz'
      · refine h.2.2.2 ?_
        rw [hz', ← mul_assoc, conjVert_mul_self ha x, one_mul]
      · refine h.2.2.2 ?_
        rw [hz', cxy]
      · refine h.2.2.2 ?_
        rw [hz', cxy, ← mul_assoc, conjVert_mul_self ha y, one_mul]
      · refine h.2.2.2 ?_
        rw [hz', mul_assoc, ← cxy, ← mul_assoc, conjVert_mul_self ha x, one_mul]
      · refine h.2.2.2 ?_
        rw [hz', mul_assoc, conjVert_mul_self ha y, mul_one]
    · intro hne
      exact Or.inl ⟨hxy, hyz, hzx, fun e => hne (Subtype.ext (by rw [shortMid_coe hxy]; exact e))⟩

theorem permClosure_longTri_iff (ha : a * a = 1) (ha1 : a ≠ 1) {x y z : ConjVert a}
    (hxy : (twoAGraph a).Adj x y) (hyz : (twoAGraph a).Adj y z) (hzx : (twoAGraph a).Adj z x) :
    permClosure (longTri a) x y z ↔ longTri a x y z := by
  rw [(shortStruct_twoAGraph ha ha1).lg_iff hxy hyz hzx]
  refine ⟨fun h => ⟨hxy, hyz, hzx, fun e => h (Subtype.ext ?_)⟩, fun h e => h.2.2.2 ?_⟩
  · rw [shortMid_coe hxy]
    exact e
  · have := congrArg Subtype.val e
    rwa [shortMid_coe hxy] at this

theorem twoAGraph_adj_smul_iff (g : G) {x y : ConjVert a} :
    (twoAGraph a).Adj (g • x) (g • y) ↔ (twoAGraph a).Adj x y :=
  ⟨fun h => by simpa using twoAGraph_adj_smul g⁻¹ h, twoAGraph_adj_smul g⟩

theorem longTri_smul (g : G) (x y z : ConjVert a) :
    longTri a (g • x) (g • y) (g • z) ↔ longTri a x y z := by
  unfold longTri
  rw [twoAGraph_adj_smul_iff, twoAGraph_adj_smul_iff, twoAGraph_adj_smul_iff]
  have h1 : g * (x : G) * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have h2 : ∀ p q : G, g * p * g⁻¹ = g * q * g⁻¹ ↔ p = q := fun p q =>
    ⟨fun h => mul_left_cancel (mul_right_cancel h), fun h => by rw [h]⟩
  simp only [coe_smul_conjVert, h1, ne_eq, h2]

theorem shortMid_smul (g : G) (x y : ConjVert a) :
    shortMid a (g • x) (g • y) = g • shortMid a x y := by
  by_cases h : (twoAGraph a).Adj x y
  · apply Subtype.ext
    rw [shortMid_coe ((twoAGraph_adj_smul_iff g).2 h), coe_smul_conjVert, coe_smul_conjVert,
      coe_smul_conjVert, shortMid_coe h]
    group
  · have h' : ¬ (twoAGraph a).Adj (g • x) (g • y) := fun h2 => h ((twoAGraph_adj_smul_iff g).1 h2)
    simp [shortMid, h, h']

theorem exists_smul_baseVertex_eq (x : ConjVert a) : ∃ g : G, g • baseVertex a = x := by
  obtain ⟨c, hc⟩ := isConj_iff.1 x.2
  exact ⟨c, Subtype.ext (by simpa using hc)⟩

theorem equivariantShort_twoAGraph :
    EquivariantShort G (twoAGraph a) (shortMid a) (longTri a) where
  adj_iff g _ _ := twoAGraph_adj_smul_iff g
  mid_smul g x y := shortMid_smul g x y
  lg_iff g x y z := longTri_smul g x y z

theorem preconnected_longLinkGraph_of_reflTransGen {x : ConjVert a}
    (h : ∀ w w' : ConjVert a, (twoAGraph a).Adj x w → (twoAGraph a).Adj x w' →
      Relation.ReflTransGen (longTri a x) w w') :
    (longLinkGraph (twoAGraph a) (longTri a) x).Preconnected := by
  intro s t
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have key : ∀ {w w' : ConjVert a}, Relation.ReflTransGen (longTri a x) w w' →
      ∀ (hw : (twoAGraph a).Adj x w) (hw' : (twoAGraph a).Adj x w'),
        Relation.ReflTransGen (longLinkGraph (twoAGraph a) (longTri a) x).Adj ⟨w, hw⟩
          ⟨w', hw'⟩ := by
    intro w w' hr
    induction hr with
    | refl => exact fun _ _ => Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact fun hw hc => (ih hw hbc.1).tail ⟨hbc.2.1, Or.inl hbc⟩
  exact key (h s t s.2 t.2) s.2 t.2

theorem longLinkGraph_twoAGraph_of_base
    (h₀ : (longLinkGraph (twoAGraph a) (longTri a) (baseVertex a)).Preconnected)
    (x : ConjVert a) : (longLinkGraph (twoAGraph a) (longTri a) x).Preconnected :=
  longLinkGraph_preconnected_of_base equivariantShort_twoAGraph exists_smul_baseVertex_eq h₀ x

theorem quad_null_twoAGraph_of_base (ha : a * a = 1) (ha1 : a ≠ 1)
    (h₀ : ∀ {y u : ConjVert a} (hxy : (twoAGraph a).Adj (baseVertex a) y)
      (hxu : (twoAGraph a).Adj (baseVertex a) u) (hyu : (twoAGraph a).Adj y u)
      (hL : permClosure (longTri a) (baseVertex a) y u),
      MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha ha1).quad hxy hxu hyu hL) .nil)
    {x y u : ConjVert a} (hxy : (twoAGraph a).Adj x y) (hxu : (twoAGraph a).Adj x u)
    (hyu : (twoAGraph a).Adj y u) (hL : permClosure (longTri a) x y u) :
    MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha ha1).quad hxy hxu hyu hL) .nil :=
  (shortStruct_twoAGraph ha ha1).quad_null_of_base equivariantShort_twoAGraph
    exists_smul_baseVertex_eq h₀ hxy hxu hyu hL

theorem quad_null_twoAGraph_of_mu (ha : a * a = 1) (ha1 : a ≠ 1)
    (hμ : ∀ {y u : ConjVert a} (_ : (twoAGraph a).Adj (baseVertex a) y)
      (_ : (twoAGraph a).Adj (baseVertex a) u) (_ : (twoAGraph a).Adj y u)
      (_ : permClosure (longTri a) (baseVertex a) y u),
      (muGraph (longTri a) (twoAGraph a) y (shortMid a (baseVertex a) u)).Preconnected)
    {x y u : ConjVert a} (hxy : (twoAGraph a).Adj x y) (hxu : (twoAGraph a).Adj x u)
    (hyu : (twoAGraph a).Adj y u) (hL : permClosure (longTri a) x y u) :
    MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha ha1).quad hxy hxu hyu hL) .nil :=
  quad_null_twoAGraph_of_base ha ha1
    (fun hxy hxu hyu hL =>
      (shortStruct_twoAGraph ha ha1).quad_null_of_mu_preconnected hxy hxu hyu hL
        (hμ hxy hxu hyu hL))
    hxy hxu hyu hL

end CFSG.Monster.Tri
