module

public import CFSG.Quasithin.Background.SimsF5Defs2
public import CFSG.Quasithin.Background.RonanF5CTransport

public section

namespace CFSG.Quasithin.SimsF5

noncomputable section

open scoped Pointwise

section Transport

open CFSG.Quasithin.Asc94

variable {M : Type} [Group M] (Φ : M ≃* ↥MDot) {M0 H R Tf : Subgroup M}

theorem us_stab_iff (hM0 : ∀ g : M, g ∈ M0 ↔ ((Φ g : ↥MDot) : GL6) ∈ M0Dot)
    (hstab : MulAction.stabilizer ↥MDot xDot = M0Dot.subgroupOf MDot) (g : M) :
    g ∈ M0 ↔ Φ g • xDot = xDot := by
  rw [hM0, ← MulAction.mem_stabilizer_iff, hstab, Subgroup.mem_subgroupOf]

@[expose] def usVertex (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot) : M ⧸ M0 → PtX := fun q =>
  Quotient.liftOn' q (fun g : M => Φ g • xDot) fun a b hab => by
    have h := (hs _).1 (QuotientGroup.leftRel_apply.mp hab)
    rw [map_mul, mul_smul, map_inv] at h
    exact (inv_smul_eq_iff.1 h).symm

theorem us_vertex_mk (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot) (g : M) :
    usVertex Φ hs (g : M ⧸ M0) = Φ g • xDot := rfl

theorem us_vertex_injective (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot) :
    Function.Injective (usVertex Φ hs) := by
  intro p q hpq
  induction p using QuotientGroup.induction_on with
  | _ a =>
  induction q using QuotientGroup.induction_on with
  | _ b =>
  rw [us_vertex_mk, us_vertex_mk] at hpq
  rw [QuotientGroup.eq, hs, map_mul, mul_smul, map_inv, inv_smul_eq_iff]
  exact hpq.symm

theorem us_vertex_surjective (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) :
    Function.Surjective (usVertex Φ hs) := by
  intro w
  obtain ⟨g, rfl⟩ := htrans w
  exact ⟨((Φ.symm g : M) : M ⧸ M0), by rw [us_vertex_mk, MulEquiv.apply_symm_apply]⟩

@[expose] def usEquiv (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) : M ⧸ M0 ≃ PtX :=
  Equiv.ofBijective (usVertex Φ hs) ⟨us_vertex_injective Φ hs, us_vertex_surjective Φ hs htrans⟩

theorem us_equiv_mk (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) (g : M) :
    usEquiv Φ hs htrans (g : M ⧸ M0) = Φ g • xDot := rfl

theorem us_equiv_smul (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) (g : M) (w : M ⧸ M0) :
    usEquiv Φ hs htrans (g • w) = Φ g • usEquiv Φ hs htrans w := by
  induction w using QuotientGroup.induction_on with
  | _ a =>
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, us_equiv_mk, us_equiv_mk, map_mul, mul_smul]

theorem us_equiv_x (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) :
    usEquiv Φ hs htrans (xOf M0) = xDot := by
  rw [xOf, us_equiv_mk, map_one, one_smul]

theorem us_equiv_y (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) {r : M} (hy : Φ r • xDot = yDot) :
    usEquiv Φ hs htrans (yOf M0 r) = yDot := by
  rw [yOf, us_equiv_mk, hy]

theorem us_rel_iff (a b : M) :
    (∃ a' b' : M, (a' : M ⧸ M0) = (a : M ⧸ M0) ∧ (b' : M ⧸ M0) = (b : M ⧸ M0) ∧
      ∃ r ∈ R, r ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, a'⁻¹ * b' = m₁ * r * m₂) ↔
    ∃ r ∈ R, r ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, a⁻¹ * b = m₁ * r * m₂ := by
  constructor
  · rintro ⟨a', b', ha, hb, r, hr, hrT, m₁, hm₁, m₂, hm₂, h⟩
    rw [QuotientGroup.eq] at ha hb
    refine ⟨r, hr, hrT, (a'⁻¹ * a)⁻¹ * m₁, M0.mul_mem (M0.inv_mem ha) hm₁,
      m₂ * (b'⁻¹ * b), M0.mul_mem hm₂ hb, ?_⟩
    calc a⁻¹ * b = (a'⁻¹ * a)⁻¹ * (a'⁻¹ * b') * (b'⁻¹ * b) := by group
      _ = (a'⁻¹ * a)⁻¹ * m₁ * r * (m₂ * (b'⁻¹ * b)) := by rw [h]; group
  · rintro ⟨r, hr, hrT, m₁, hm₁, m₂, hm₂, h⟩
    exact ⟨a, b, rfl, rfl, r, hr, hrT, m₁, hm₁, m₂, hm₂, h⟩

theorem us_adj_x_iff (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot) {r : M} (hr : r ∈ R)
    (hrT : r ∉ Tf) (hy : Φ r • xDot = yDot)
    (hRy : ∀ r' ∈ R, r' ∉ Tf → Φ r' • xDot = yDot) (hadj : DeltaDot.Adj xDot yDot)
    (hga : GraphAction ↥MDot DeltaDot)
    (hnbr : ∀ P : PtX, DeltaDot.Adj xDot P → ∃ m : M, m ∈ M0 ∧ Φ m • yDot = P) (g : M) :
    DeltaDot.Adj xDot (Φ g • xDot) ↔
      ∃ r' ∈ R, r' ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, g = m₁ * r' * m₂ := by
  constructor
  · intro h
    obtain ⟨m, hm, hmP⟩ := hnbr _ h
    refine ⟨r, hr, hrT, m, hm, (m * r)⁻¹ * g, ?_, (mul_inv_cancel_left (m * r) g).symm⟩
    rw [← hy, ← mul_smul, ← map_mul] at hmP
    rw [hs, map_mul, mul_smul, ← hmP, map_inv, inv_smul_smul]
  · rintro ⟨r', hr', hr'T, m₁, hm₁, m₂, hm₂, rfl⟩
    rw [map_mul, map_mul, mul_smul, mul_smul, (hs m₂).1 hm₂, hRy r' hr' hr'T]
    have := (hga.adj_smul (Φ m₁) xDot yDot).2 hadj
    rwa [(hs m₁).1 hm₁] at this

theorem us_adj_equiv_iff (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) {r : M} (hr : r ∈ R) (hrT : r ∉ Tf)
    (hy : Φ r • xDot = yDot) (hRy : ∀ r' ∈ R, r' ∉ Tf → Φ r' • xDot = yDot)
    (hadj : DeltaDot.Adj xDot yDot) (hga : GraphAction ↥MDot DeltaDot)
    (hnbr : ∀ P : PtX, DeltaDot.Adj xDot P → ∃ m : M, m ∈ M0 ∧ Φ m • yDot = P)
    (u v : M ⧸ M0) :
    (DeltaGraph M0 R Tf).Adj u v ↔
      DeltaDot.Adj (usEquiv Φ hs htrans u) (usEquiv Φ hs htrans v) := by
  induction u using QuotientGroup.induction_on with
  | _ a =>
  induction v using QuotientGroup.induction_on with
  | _ b =>
  have key : ∀ a b : M, DeltaDot.Adj (Φ a • xDot) (Φ b • xDot) ↔
      ∃ r' ∈ R, r' ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, a⁻¹ * b = m₁ * r' * m₂ := by
    intro a b
    have h1 : Φ b • xDot = Φ a • (Φ (a⁻¹ * b) • xDot) := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel_left]
    rw [h1, hga.adj_smul, us_adj_x_iff Φ hs hr hrT hy hRy hadj hga hnbr]
  rw [us_equiv_mk, us_equiv_mk, DeltaGraph, SimpleGraph.fromRel_adj, us_rel_iff, us_rel_iff]
  constructor
  · rintro ⟨_, h | h⟩
    · exact (key a b).2 h
    · exact ((key b a).2 h).symm
  · intro h
    refine ⟨fun hab => h.ne ?_, Or.inl ((key a b).1 h)⟩
    rw [← us_vertex_mk Φ hs a, ← us_vertex_mk Φ hs b, hab]

theorem us_map_eq (hH : ∀ g : M, g ∈ H ↔ Φ g ∈ HDot) : H.map Φ.toMonoidHom = HDot := by
  ext g
  rw [Subgroup.mem_map_equiv, hH, MulEquiv.apply_symm_apply]

theorem us_mem_orbit_iff (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) (hH : ∀ g : M, g ∈ H ↔ Φ g ∈ HDot)
    (u : M ⧸ M0) :
    u ∈ (fun h : M => h • xOf M0) '' (H : Set M) ↔
      usEquiv Φ hs htrans u ∈ (fun i : ↥MDot => i • xDot) '' (HDot : Set ↥MDot) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨Φ h, (hH h).1 hh, ?_⟩
    dsimp only
    rw [us_equiv_smul, us_equiv_x]
  · rintro ⟨hb, hhb, hbu⟩
    refine ⟨Φ.symm hb, (hH _).2 (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    apply (usEquiv Φ hs htrans).injective
    dsimp only
    rw [us_equiv_smul, us_equiv_x, MulEquiv.apply_symm_apply]
    exact hbu

theorem us_isUniquenessSystem {r : M} (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (hH : ∀ g : M, g ∈ H ↔ Φ g ∈ HDot) (hr : r ∈ R) (hrT : r ∉ Tf) (hy : Φ r • xDot = yDot)
    (hRy : ∀ r' ∈ R, r' ∉ Tf → Φ r' • xDot = yDot)
    (hnbr : ∀ P : PtX, DeltaDot.Adj xDot P → ∃ m : M, m ∈ M0 ∧ Φ m • yDot = P)
    (hU : IsUniquenessSystem DeltaDot HDot DeltaDotSub xDot yDot) :
    IsUniquenessSystem (DeltaGraph M0 R Tf) H
      ((⊤ : (DeltaGraph M0 R Tf).Subgraph).induce ((fun h : M => h • xOf M0) '' (H : Set M)))
      (xOf M0) (yOf M0 r) := by
  have htrans := hU.trans
  have hadj : DeltaDot.Adj xDot yDot := by
    have h : s(xDot, yDot) ∈ DeltaDot.edgeSet := by
      rw [hU.edgeSet_eq]
      exact ⟨1, by simp only [one_smul]⟩
    exact h
  have eqv := us_equiv_smul Φ hs htrans
  have hx := us_equiv_x Φ hs htrans (M0 := M0)
  have hy' := us_equiv_y Φ hs htrans (M0 := M0) hy
  have hadjEquiv := us_adj_equiv_iff Φ hs htrans hr hrT hy hRy hadj hU.graphAction hnbr
  have hsub := us_map_eq Φ hH
  have hver : DeltaDotH = (fun i : ↥MDot => i • xDot) '' (HDot : Set ↥MDot) := by
    have h := hU.verts_eq
    rwa [DeltaDotSub, SimpleGraph.Subgraph.induce_verts] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (RonanF5C.graphAction_iff _ _ Φ _ eqv hadjEquiv).2 hU.graphAction
  · exact (RonanF5C.transitive_iff Φ _ eqv (xOf M0) xDot hx).2 hU.trans
  · exact (RonanF5C.edgeSet_orbit_iff _ _ Φ _ eqv hadjEquiv (xOf M0) (yOf M0 r) xDot yDot
      hx hy').2 hU.edgeSet_eq
  · exact (RonanF5C.swap_iff Φ _ eqv H HDot hsub (xOf M0) (yOf M0 r) xDot yDot hx hy').2 hU.swap
  · rw [SimpleGraph.Subgraph.induce_verts]
  · refine (RonanF5C.subgraph_edgeSet_iff _ _ _ DeltaDotSub Φ _ eqv H HDot hsub ?_ (xOf M0)
      (yOf M0 r) xDot yDot hx hy').2 hU.edgeSet_I_eq
    intro a b
    simp only [SimpleGraph.Subgraph.spanningCoe_adj, DeltaDotSub, SimpleGraph.Subgraph.induce_adj,
      SimpleGraph.Subgraph.top_adj]
    rw [us_mem_orbit_iff Φ hs htrans hH a, us_mem_orbit_iff Φ hs htrans hH b, hadjEquiv a b,
      hver]
  · exact (RonanF5C.sup_eq_top_iff Φ _ eqv H HDot hsub (xOf M0) xDot hx).2 hU.sup_eq_top
  · exact (RonanF5C.stab_eq_iff Φ _ eqv H HDot hsub (xOf M0) (yOf M0 r) xDot yDot hx hy').2
      hU.stab_eq
  · exact (RonanF5C.I_eq_iff Φ _ eqv H HDot hsub (xOf M0) (yOf M0 r) xDot yDot hx hy').2 hU.I_eq

@[expose] def usRestrict {N : Type} [Group N] (e : M ≃* N) (A : Subgroup M) (B : Subgroup N)
    (h : ∀ g : M, g ∈ A ↔ e g ∈ B) : B ≃* A where
  toFun b := ⟨e.symm b, (h _).2 (by rw [MulEquiv.apply_symm_apply]; exact b.2)⟩
  invFun a := ⟨e a, (h _).1 a.2⟩
  left_inv b := Subtype.ext (MulEquiv.apply_symm_apply e b)
  right_inv a := Subtype.ext (MulEquiv.symm_apply_apply e a)
  map_mul' a b := Subtype.ext (map_mul e.symm (a : N) (b : N))

theorem us_map_subgroupOf {N : Type} [Group N] (e : M ≃* N) {A : Subgroup M} {B : Subgroup N}
    (ι : B ≃* A) (hι : ∀ b : B, (ι b : M) = e.symm b) {SA : Subgroup M} {SB : Subgroup N}
    (hS : ∀ g : M, g ∈ SA ↔ e g ∈ SB) :
    (SB.subgroupOf B).map ι.toMonoidHom = SA.subgroupOf A := by
  ext a
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hS]
  have h : e (a : M) = ((ι.symm a : B) : N) := by
    have h1 := hι (ι.symm a)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1, MulEquiv.apply_symm_apply]
  rw [h]

theorem us_mem_stabilizer_iff (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) (u : M ⧸ M0) (g : M) :
    g ∈ MulAction.stabilizer M u ↔
      Φ g ∈ MulAction.stabilizer ↥MDot (usEquiv Φ hs htrans u) := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← us_equiv_smul Φ hs htrans,
    (usEquiv Φ hs htrans).injective.eq_iff]

theorem us_mem_stabilizer_pair_iff (hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot)
    (htrans : ∀ w : PtX, ∃ g : ↥MDot, g • xDot = w) (u v : M ⧸ M0) (g : M) :
    g ∈ MulAction.stabilizer M ({u, v} : Set (M ⧸ M0)) ↔
      Φ g ∈ MulAction.stabilizer ↥MDot
        ({usEquiv Φ hs htrans u, usEquiv Φ hs htrans v} : Set PtX) := by
  have himg : Φ g • ((usEquiv Φ hs htrans) '' ({u, v} : Set (M ⧸ M0))) =
      (usEquiv Φ hs htrans) '' (g • ({u, v} : Set (M ⧸ M0))) := by
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    funext w
    exact (us_equiv_smul Φ hs htrans g w).symm
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← Set.image_pair, himg,
    (Set.image_injective.mpr (usEquiv Φ hs htrans).injective).eq_iff]

end Transport

open CFSG.Quasithin.Asc94 in
theorem us_transport {M : Type} [Group M] (Φ : M ≃* ↥MDot) {M0 H R Tf : Subgroup M} {r : M}
    (hM0 : ∀ g : M, g ∈ M0 ↔ ((Φ g : ↥MDot) : GL6) ∈ M0Dot)
    (hH : ∀ g : M, g ∈ H ↔ Φ g ∈ HDot)
    (hR : ∀ r' ∈ R, r' ∉ Tf → ((Φ r' : ↥MDot) : GL6) * fDot = fDot * ((Φ r' : ↥MDot) : GL6) ∧
      ((Φ r' : ↥MDot) : GL6) ∉ M0Dot)
    (hr : r ∈ R) (hrT : r ∉ Tf)
    (hstab : MulAction.stabilizer ↥MDot xDot = M0Dot.subgroupOf MDot)
    (hcen : ∀ g : ↥MDot, (g : GL6) * fDot = fDot * (g : GL6) → (g : GL6) ∉ M0Dot →
      g • xDot = yDot)
    (hnbr : ∀ P : PtX, DeltaDot.Adj xDot P → ∃ g : ↥MDot, (g : GL6) ∈ M0Dot ∧ g • yDot = P)
    (hfaith : FaithfulSMul ↥MDot PtX)
    (hU : IsUniquenessSystem DeltaDot HDot DeltaDotSub xDot yDot) :
    FaithfulSMul M (M ⧸ M0) ∧
      IsUniquenessSystem (DeltaGraph M0 R Tf) H
        ((⊤ : (DeltaGraph M0 R Tf).Subgraph).induce ((fun h : M => h • xOf M0) '' (H : Set M)))
        (xOf M0) (yOf M0 r) ∧
      ∃ (β' : ↥(MulAction.stabilizer ↥MDot xDot) ≃* ↥(MulAction.stabilizer M (xOf M0)))
        (ζ : ↥HDot ≃* ↥H),
        (∀ g : ↥(MulAction.stabilizer ↥MDot xDot),
          ((β' g : ↥(MulAction.stabilizer M (xOf M0))) : M) = Φ.symm (g : ↥MDot)) ∧
        (∀ g : ↥HDot, ((ζ g : ↥H) : M) = Φ.symm (g : ↥MDot)) ∧
        ((MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX)).subgroupOf HDot).map ζ.toMonoidHom =
          (MulAction.stabilizer M ({xOf M0, yOf M0 r} : Set (M ⧸ M0))).subgroupOf H ∧
        IsEquivalence HDot xDot yDot H (xOf M0) (yOf M0 r) β' ζ := by
  have hs : ∀ g : M, g ∈ M0 ↔ Φ g • xDot = xDot := us_stab_iff Φ hM0 hstab
  have hRy : ∀ r' ∈ R, r' ∉ Tf → Φ r' • xDot = yDot := fun r' h1 h2 =>
    hcen (Φ r') (hR r' h1 h2).1 (hR r' h1 h2).2
  have hy : Φ r • xDot = yDot := hRy r hr hrT
  have hnbr' : ∀ P : PtX, DeltaDot.Adj xDot P → ∃ m : M, m ∈ M0 ∧ Φ m • yDot = P := by
    intro P hP
    obtain ⟨g, hg, hgP⟩ := hnbr P hP
    refine ⟨Φ.symm g, (hM0 _).2 (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    rwa [MulEquiv.apply_symm_apply]
  have htrans := hU.trans
  have eqv := us_equiv_smul Φ hs htrans
  have hx := us_equiv_x Φ hs htrans (M0 := M0)
  have hy' := us_equiv_y Φ hs htrans (M0 := M0) hy
  have hsx : ∀ g : M, g ∈ MulAction.stabilizer M (xOf M0) ↔
      Φ g ∈ MulAction.stabilizer ↥MDot xDot := fun g => by
    have h := us_mem_stabilizer_iff Φ hs htrans (xOf M0) g
    rwa [hx] at h
  have hsy : ∀ g : M, g ∈ MulAction.stabilizer M (yOf M0 r) ↔
      Φ g ∈ MulAction.stabilizer ↥MDot yDot := fun g => by
    have h := us_mem_stabilizer_iff Φ hs htrans (yOf M0 r) g
    rwa [hy'] at h
  have hsxy : ∀ g : M, g ∈ MulAction.stabilizer M ({xOf M0, yOf M0 r} : Set (M ⧸ M0)) ↔
      Φ g ∈ MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX) := fun g => by
    have h := us_mem_stabilizer_pair_iff Φ hs htrans (xOf M0) (yOf M0 r) g
    rwa [hx, hy'] at h
  let β' := usRestrict Φ (MulAction.stabilizer M (xOf M0)) (MulAction.stabilizer ↥MDot xDot) hsx
  let ζ := usRestrict Φ H HDot hH
  have hβ : ∀ b : ↥(MulAction.stabilizer ↥MDot xDot),
      ((β' b : ↥(MulAction.stabilizer M (xOf M0))) : M) = Φ.symm (b : ↥MDot) := fun b => rfl
  have hζ : ∀ g : ↥HDot, ((ζ g : ↥H) : M) = Φ.symm (g : ↥MDot) := fun g => rfl
  have hedge := us_map_subgroupOf Φ ζ hζ hsxy
  refine ⟨(RonanF5C.faithfulSMul_iff Φ (usEquiv Φ hs htrans) eqv).2 hfaith,
    us_isUniquenessSystem Φ hs hH hr hrT hy hRy hnbr' hU, β', ζ, hβ, hζ, hedge, ?_⟩
  refine ⟨⟨us_map_subgroupOf Φ ζ hζ hsx, fun i h => rfl, us_map_subgroupOf Φ β' hβ hsy, hedge⟩, ?_⟩
  obtain ⟨t, ht, h1, h2⟩ := hU.swap
  refine ⟨⟨t, ht⟩, h1, h2, fun b c _ hc => ?_⟩
  show Φ.symm (c : ↥MDot) = (Φ.symm t)⁻¹ * Φ.symm (b : ↥MDot) * Φ.symm t
  rw [hc, map_mul, map_mul, map_inv]

end

end CFSG.Quasithin.SimsF5
