module

public import CFSG.YGroups.MarkedWalks
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.YGroups

open SimpleGraph CFSG.Monster.B.Recog

section RightCosetGraph

variable {G : Type*} [Group G]

@[expose] def rcGraph (L : Subgroup G) (x : G) :
    SimpleGraph (Quotient (QuotientGroup.rightRel L)) :=
  SimpleGraph.fromRel fun u v => ∃ g : G, u = Quotient.mk'' g ∧ v = Quotient.mk'' (x * g)

@[expose] def yTri (L : Subgroup G) (x y : G) (u v w : Quotient (QuotientGroup.rightRel L)) :
    Prop :=
  ∃ g : G, u = Quotient.mk'' g ∧ v = Quotient.mk'' (x * g) ∧ w = Quotient.mk'' (x * y * g) ∧
    u ≠ v ∧ v ≠ w ∧ u ≠ w

variable {L : Subgroup G} {x y : G}

theorem rc_mk_eq_mk_iff {g h : G} :
    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' h ↔ h * g⁻¹ ∈ L :=
  Quotient.eq''.trans QuotientGroup.rightRel_apply

theorem rc_mk_mul_left_of_mem {k : G} (hk : k ∈ L) (g : G) :
    (Quotient.mk'' (k * g) : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' g := by
  rw [rc_mk_eq_mk_iff]
  simpa using L.inv_mem hk

theorem rcGraph_adj_iff {u v : Quotient (QuotientGroup.rightRel L)} :
    (rcGraph L x).Adj u v ↔ u ≠ v ∧ ((∃ g : G, u = Quotient.mk'' g ∧ v = Quotient.mk'' (x * g)) ∨
      ∃ g : G, v = Quotient.mk'' g ∧ u = Quotient.mk'' (x * g)) :=
  SimpleGraph.fromRel_adj _ u v

theorem rcGraph_adj_mk_iff (hx : x * x = 1) (hxL : x ∉ L) (g : G)
    (v : Quotient (QuotientGroup.rightRel L)) :
    (rcGraph L x).Adj (Quotient.mk'' g) v ↔ ∃ k ∈ L, v = Quotient.mk'' (x * k * g) := by
  induction v using Quotient.inductionOn' with | _ h => ?_
  rw [rcGraph_adj_iff]
  constructor
  · rintro ⟨-, ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩⟩
    · rw [rc_mk_eq_mk_iff] at ha
      refine ⟨a * g⁻¹, ha, ?_⟩
      rw [hb, mul_assoc, inv_mul_cancel_right]
    · rw [rc_mk_eq_mk_iff] at hb
      refine ⟨x * a * g⁻¹, hb, ?_⟩
      rw [ha]
      congr 1
      calc a = (x * x) * a := by rw [hx, one_mul]
        _ = x * (x * a * g⁻¹) * g := by group
  · rintro ⟨k, hk, hv⟩
    rw [hv]
    refine ⟨fun h => hxL ?_, Or.inl ⟨k * g, (rc_mk_mul_left_of_mem hk g).symm, by rw [mul_assoc]⟩⟩
    rw [rc_mk_eq_mk_iff] at h
    simpa using L.mul_mem h (L.inv_mem hk)

theorem rc_mk_nbr_eq_iff (hx : x * x = 1) (k₁ k₂ g : G) :
    (Quotient.mk'' (x * k₁ * g) : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' (x * k₂ * g)
      ↔ x * (k₂ * k₁⁻¹) * x ∈ L := by
  rw [rc_mk_eq_mk_iff]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have : x * k₂ * g * (x * k₁ * g)⁻¹ = x * (k₂ * k₁⁻¹) * x := by
    calc _ = x * (k₂ * k₁⁻¹) * x⁻¹ := by group
      _ = _ := by rw [hxi]
  rw [this]

theorem rc_mk_mul_right_iff (c g h : G) :
    (Quotient.mk'' (g * c) : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' (h * c) ↔
      (Quotient.mk'' g : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' h := by
  rw [rc_mk_eq_mk_iff, rc_mk_eq_mk_iff]
  have : h * c * (g * c)⁻¹ = h * g⁻¹ := by group
  rw [this]

@[expose] def rcRmul (L : Subgroup G) (x c : G) : rcGraph L x →g rcGraph L x where
  toFun := Quotient.map' (· * c) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h
  map_rel' {a b} h := by
    induction a using Quotient.inductionOn' with | _ g => ?_
    induction b using Quotient.inductionOn' with | _ g' => ?_
    rw [rcGraph_adj_iff] at h
    obtain ⟨hne, ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩⟩ := h
    · refine rcGraph_adj_iff.2 ⟨fun e => hne ((rc_mk_mul_right_iff c g g').1 e),
        Or.inl ⟨a * c, (rc_mk_mul_right_iff c g a).2 ha, ?_⟩⟩
      rw [← mul_assoc]
      exact (rc_mk_mul_right_iff c g' (x * a)).2 hb
    · refine rcGraph_adj_iff.2 ⟨fun e => hne ((rc_mk_mul_right_iff c g g').1 e),
        Or.inr ⟨a * c, (rc_mk_mul_right_iff c g' a).2 ha, ?_⟩⟩
      rw [← mul_assoc]
      exact (rc_mk_mul_right_iff c g (x * a)).2 hb

@[simp] theorem rcRmul_mk (L : Subgroup G) (x c g : G) :
    rcRmul L x c (Quotient.mk'' g) = Quotient.mk'' (g * c) := rfl

theorem rcGraph_reachable_mk_one (hx : x * x = 1) (hxL : x ∉ L)
    (hgen : Subgroup.closure ((L : Set G) ∪ {x}) = ⊤) (a : G) :
    (rcGraph L x).Reachable (Quotient.mk'' 1) (Quotient.mk'' a) := by
  have key : ∀ a ∈ Subgroup.closure ((L : Set G) ∪ {x}),
      (rcGraph L x).Reachable (Quotient.mk'' 1) (Quotient.mk'' a) := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · rw [rc_mk_eq_mk_iff.2 (by simpa using ha : a * 1⁻¹ ∈ L)]
      · rw [Set.mem_singleton_iff.1 ha]
        exact SimpleGraph.Adj.reachable
          ((rcGraph_adj_mk_iff hx hxL 1 _).2 ⟨1, L.one_mem, by rw [mul_one, mul_one]⟩)
    | one => rfl
    | mul a b _ _ iha ihb =>
      refine ihb.trans ?_
      simpa [rcRmul_mk] using iha.map (rcRmul L x b)
    | inv a _ ih =>
      refine SimpleGraph.Reachable.symm ?_
      simpa [rcRmul_mk] using ih.map (rcRmul L x a⁻¹)
  exact key a (hgen ▸ Subgroup.mem_top a)

theorem mul_inv_mul_eq_of_pow_three_eq_one (hx : x * x = 1) (hxy : (x * y) ^ 3 = 1) :
    x * y⁻¹ * x = y * x * y := by
  have h6 : x * y * x * y * x * y = 1 := by simpa [pow_succ, mul_assoc] using hxy
  have h5 : x * y * x * y * x = y⁻¹ := mul_eq_one_iff_eq_inv.1 h6
  calc x * y⁻¹ * x = x * (x * y * x * y * x) * x := by rw [h5]
    _ = (x * x) * y * x * y * (x * x) := by group
    _ = y * x * y := by rw [hx]; group

theorem yTri_rotate (hx : x * x = 1) (hy : y ∈ L) (hxy : (x * y) ^ 3 = 1)
    {u v w : Quotient (QuotientGroup.rightRel L)} (h : yTri L x y u v w) :
    yTri L x y v w u := by
  have I1 := mul_inv_mul_eq_of_pow_three_eq_one hx hxy
  obtain ⟨g, rfl, rfl, rfl, h₁, h₂, h₃⟩ := h
  refine ⟨y⁻¹ * x * g, ?_, ?_, ?_, h₂, h₃.symm, h₁.symm⟩
  · rw [rc_mk_eq_mk_iff]
    have : y⁻¹ * x * g * (x * g)⁻¹ = y⁻¹ := by group
    rw [this]
    exact L.inv_mem hy
  · rw [rc_mk_eq_mk_iff]
    have : x * (y⁻¹ * x * g) * (x * y * g)⁻¹ = (x * y⁻¹ * x) * y⁻¹ * x⁻¹ := by group
    rw [this, I1]
    have : y * x * y * y⁻¹ * x⁻¹ = y := by group
    rw [this]
    exact hy
  · rw [rc_mk_eq_mk_iff]
    have : x * y * (y⁻¹ * x * g) * g⁻¹ = x * x := by group
    rw [this, hx]
    exact L.one_mem

theorem yTri.adj {u v w : Quotient (QuotientGroup.rightRel L)} (h : yTri L x y u v w) :
    (rcGraph L x).Adj u v := by
  obtain ⟨g, rfl, rfl, -, h₁, -⟩ := h
  exact rcGraph_adj_iff.2 ⟨h₁, Or.inl ⟨g, rfl, rfl⟩⟩

theorem yTri_adj (hx : x * x = 1) (hy : y ∈ L) (hxy : (x * y) ^ 3 = 1)
    {u v w : Quotient (QuotientGroup.rightRel L)} (h : yTri L x y u v w) :
    (rcGraph L x).Adj u v ∧ (rcGraph L x).Adj v w ∧ (rcGraph L x).Adj w u :=
  ⟨h.adj, (yTri_rotate hx hy hxy h).adj, (yTri_rotate hx hy hxy (yTri_rotate hx hy hxy h)).adj⟩

end RightCosetGraph

section Covering

variable {G : Type*} [Group G] {E : Type*} [Group E] (f : E →* G)

@[expose] def rcMap (L : Subgroup E) :
    Quotient (QuotientGroup.rightRel L) → Quotient (QuotientGroup.rightRel (L.map f)) :=
  Quotient.map' f fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa using Subgroup.mem_map_of_mem f h

@[simp] theorem rcMap_mk (L : Subgroup E) (g : E) :
    rcMap f L (Quotient.mk'' g) = Quotient.mk'' (f g) := rfl

variable {L : Subgroup E} {x y : E}

@[expose] def rcHom (f : E →* G) (L : Subgroup E) (x : E) (hx : x * x = 1) (hxL : f x ∉ L.map f) :
    rcGraph L x →g rcGraph (L.map f) (f x) where
  toFun := rcMap f L
  map_rel' {a b} h := by
    induction a using Quotient.inductionOn' with | _ g => ?_
    have hxL' : x ∉ L := fun h => hxL (Subgroup.mem_map_of_mem f h)
    obtain ⟨k, hk, rfl⟩ := (rcGraph_adj_mk_iff hx hxL' g b).1 h
    refine (rcGraph_adj_mk_iff (by rw [← map_mul, hx, map_one]) hxL (f g) _).2
      ⟨f k, Subgroup.mem_map_of_mem f hk, ?_⟩
    rw [rcMap_mk, map_mul, map_mul]

@[simp] theorem rcHom_mk (hx : x * x = 1) (hxL : f x ∉ L.map f) (g : E) :
    rcHom f L x hx hxL (Quotient.mk'' g) = Quotient.mk'' (f g) := rfl

theorem rcMap_surjective (hf : Function.Surjective f) (L : Subgroup E) :
    Function.Surjective (rcMap f L) := by
  intro q
  induction q using Quotient.inductionOn' with | _ g => ?_
  obtain ⟨a, rfl⟩ := hf g
  exact ⟨Quotient.mk'' a, rfl⟩

theorem injective_of_mk_one_eq (hinj : Set.InjOn f L)
    (h : ∀ a, f a = 1 →
      (Quotient.mk'' 1 : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' a) :
    Function.Injective f := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact hinj (by simpa using rc_mk_eq_mk_iff.1 (h a ha)) L.one_mem (by rw [ha, map_one])

theorem rcMap_injective_iff (hinj : Set.InjOn f L) :
    Function.Injective (rcMap f L) ↔ Function.Injective f := by
  refine ⟨fun h => injective_of_mk_one_eq f hinj fun a ha => h ?_, fun h => ?_⟩
  · rw [rcMap_mk, rcMap_mk, ha, map_one]
  · intro p q hpq
    induction p using Quotient.inductionOn' with | _ a => ?_
    induction q using Quotient.inductionOn' with | _ b => ?_
    rw [rcMap_mk, rcMap_mk, rc_mk_eq_mk_iff] at hpq
    obtain ⟨c, hc, hcf⟩ := Subgroup.mem_map.1 hpq
    have : c = b * a⁻¹ := h (by rw [hcf, map_mul, map_inv])
    exact rc_mk_eq_mk_iff.2 (this ▸ hc)

theorem rcHom_isCovering (hx : x * x = 1) (hxL : f x ∉ L.map f) (hinj : Set.InjOn f L)
    (hedge : ∀ h ∈ L.map f, f x * h * f x ∈ L.map f → ∃ k ∈ L, x * k * x ∈ L ∧ f k = h) :
    IsCovering (rcHom f L x hx hxL) := by
  have hx' : f x * f x = 1 := by rw [← map_mul, hx, map_one]
  have hxL' : x ∉ L := fun h => hxL (Subgroup.mem_map_of_mem f h)
  refine IsCovering.of_existsUnique fun a y hay => ?_
  induction a using Quotient.inductionOn' with | _ m => ?_
  rw [rcHom_mk] at hay
  obtain ⟨k', hk', rfl⟩ := (rcGraph_adj_mk_iff hx' hxL (f m) y).1 hay
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
  refine ⟨Quotient.mk'' (x * k * m),
    ⟨(rcGraph_adj_mk_iff hx hxL' m _).2 ⟨k, hk, rfl⟩, by rw [rcHom_mk, map_mul, map_mul]⟩, ?_⟩
  rintro b ⟨hb, hby⟩
  obtain ⟨j, hj, rfl⟩ := (rcGraph_adj_mk_iff hx hxL' m b).1 hb
  simp only [rcHom_mk, map_mul] at hby
  have h₁ := (rc_mk_nbr_eq_iff hx' (f j) (f k) (f m)).1 hby
  obtain ⟨c, hc, hcL, hfc⟩ := hedge (f k * (f j)⁻¹)
    (by simpa using Subgroup.mem_map_of_mem f (L.mul_mem hk (L.inv_mem hj))) h₁
  have : c = k * j⁻¹ :=
    hinj hc (L.mul_mem hk (L.inv_mem hj)) (by rw [hfc, map_mul, map_inv])
  rw [this] at hcL
  exact (rc_mk_nbr_eq_iff hx j k m).2 hcL

theorem exists_lift_yTri (hx : x * x = 1) (hy : y ∈ L) (hxy : (x * y) ^ 3 = 1)
    (hxL : f x ∉ L.map f) (a : Quotient (QuotientGroup.rightRel L))
    {v w : Quotient (QuotientGroup.rightRel (L.map f))}
    (h : yTri (L.map f) (f x) (f y) (rcHom f L x hx hxL a) v w) :
    ∃ b c, (rcGraph L x).Adj a b ∧ (rcGraph L x).Adj b c ∧ (rcGraph L x).Adj c a ∧
      rcHom f L x hx hxL b = v ∧ rcHom f L x hx hxL c = w := by
  have hxL' : x ∉ L := fun h => hxL (Subgroup.mem_map_of_mem f h)
  have I1 := mul_inv_mul_eq_of_pow_three_eq_one hx hxy
  induction a using Quotient.inductionOn' with | _ m => ?_
  obtain ⟨g, hu, rfl, rfl, -, -, -⟩ := h
  rw [rcHom_mk, rc_mk_eq_mk_iff] at hu
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 hu
  obtain rfl : g = f k * f m := by rw [hkg]; group
  refine ⟨Quotient.mk'' (x * k * m), Quotient.mk'' (x * (y * k) * m), ?_, ?_, ?_, ?_, ?_⟩
  · exact (rcGraph_adj_mk_iff hx hxL' m _).2 ⟨k, hk, rfl⟩
  · refine (rcGraph_adj_mk_iff hx hxL' (x * k * m) _).2 ⟨y⁻¹, L.inv_mem hy, ?_⟩
    have : x * y⁻¹ * (x * k * m) = y * (x * (y * k) * m) := by
      calc x * y⁻¹ * (x * k * m) = (x * y⁻¹ * x) * k * m := by group
        _ = (y * x * y) * k * m := by rw [I1]
        _ = y * (x * (y * k) * m) := by group
    rw [this, rc_mk_mul_left_of_mem hy]
  · exact ((rcGraph_adj_mk_iff hx hxL' m _).2 ⟨y * k, L.mul_mem hy hk, rfl⟩).symm
  · rw [rcHom_mk, map_mul, map_mul, mul_assoc]
  · simp only [rcHom_mk, map_mul, mul_assoc]

theorem rcHom_liftsMarked_yTri (hx : x * x = 1) (hy : y ∈ L) (hxy : (x * y) ^ 3 = 1)
    (hxL : f x ∉ L.map f) :
    LiftsMarked (rcHom f L x hx hxL) (yTri (L.map f) (f x) (f y)) :=
  LiftsMarked.of_rotate
    (yTri_rotate (by rw [← map_mul, hx, map_one]) (Subgroup.mem_map_of_mem f hy)
      (by rw [← map_mul, ← map_pow, hxy, map_one]))
    fun a _ _ h => exists_lift_yTri f hx hy hxy hxL a h

theorem injective_of_marked_homotopy (hx : x * x = 1)
    (hgen : Subgroup.closure ((L : Set E) ∪ {x}) = ⊤) (hinj : Set.InjOn f L)
    (hxL : f x ∉ L.map f)
    (hedge : ∀ h ∈ L.map f, f x * h * f x ∈ L.map f → ∃ k ∈ L, x * k * x ∈ L ∧ f k = h)
    {T : Quotient (QuotientGroup.rightRel (L.map f)) → Quotient (QuotientGroup.rightRel (L.map f)) →
      Quotient (QuotientGroup.rightRel (L.map f)) → Prop}
    (hT : LiftsMarked (rcHom f L x hx hxL) T)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (L.map f)))
      (p : (rcGraph (L.map f) (f x)).Walk v v), MarkedHomotopic T p SimpleGraph.Walk.nil) :
    Function.Injective f := by
  have hxL' : x ∉ L := fun h => hxL (Subgroup.mem_map_of_mem f h)
  have hcov := rcHom_isCovering f hx hxL hinj hedge
  exact injective_of_mk_one_eq f hinj fun a ha =>
    eq_of_reachable_of_markedHomotopic hcov hT htri (rcGraph_reachable_mk_one hx hxL' hgen a)
      (by rw [rcHom_mk, rcHom_mk, ha, map_one])

theorem injective_of_closedWalk_homotopy (hx : x * x = 1)
    (hgen : Subgroup.closure ((L : Set E) ∪ {x}) = ⊤) (hinj : Set.InjOn f L)
    (hxL : f x ∉ L.map f)
    (hedge : ∀ h ∈ L.map f, f x * h * f x ∈ L.map f → ∃ k ∈ L, x * k * x ∈ L ∧ f k = h)
    {C : ∀ {a : Quotient (QuotientGroup.rightRel (L.map f))},
      (rcGraph (L.map f) (f x)).Walk a a → Prop}
    (hC : ClosedLifts (rcHom_isCovering f hx hxL hinj hedge) C)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (L.map f)))
      (p : (rcGraph (L.map f) (f x)).Walk v v),
      ClosedHomotopic (CyclicClosure C) p SimpleGraph.Walk.nil) :
    Function.Injective f := by
  have hxL' : x ∉ L := fun h => hxL (Subgroup.mem_map_of_mem f h)
  exact injective_of_mk_one_eq f hinj fun a ha =>
    eq_of_reachable_of_closedHomotopic hC.cyclicClosure htri
      (rcGraph_reachable_mk_one hx hxL' hgen a) (by rw [rcHom_mk, rcHom_mk, ha, map_one])

end Covering

theorem injective_of_yTriangle_homotopy {E G : Type*} [Group E] [Group G] (f : E →* G)
    (hf : Function.Surjective f) (L : Subgroup E) (x y : E) (hx : x * x = 1) (hy : y ∈ L)
    (hxy : (x * y) ^ 3 = 1) (hgen : Subgroup.closure ((L : Set E) ∪ {x}) = ⊤)
    (hinj : Set.InjOn f L) (hxL : f x ∉ L.map f)
    (hedge : ∀ h ∈ L.map f, f x * h * f x ∈ L.map f → ∃ k ∈ L, x * k * x ∈ L ∧ f k = h)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (L.map f)))
      (p : (rcGraph (L.map f) (f x)).Walk v v),
      MarkedHomotopic (yTri (L.map f) (f x) (f y)) p SimpleGraph.Walk.nil) :
    Function.Injective f := by
  have _ := hf
  exact injective_of_marked_homotopy f hx hgen hinj hxL hedge
    (rcHom_liftsMarked_yTri f hx hy hxy hxL) htri

end CFSG.YGroups
