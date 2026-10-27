module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QOrbitAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Assembly
open scoped Matrix

open TwD7Q

private theorem zmod3_neg_add_sub (a b : ZMod 3) : -b + (a - b) = a + b := by
  revert a b
  decide

private theorem isD6Root_of_exists_normalizer_conj {G : Type} [Group G] [Finite G]
    {B : Basis3 G 8} (hrec : RecOutTwD7 B (B.b 0)) {e : Coords 7}
    (h : ∃ n ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))),
      n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec e) : IsD6Root e := by
  classical
  obtain ⟨n, hnN, hnconj⟩ := h
  obtain ⟨c, hc⟩ := pr_surjective (B.b 0 * B.b 1) n
  have hvecβ : B.vec twD7VBeta = B.b 0 * B.b 1 := by
    rw [twD7VBeta, B.vec_add, B.vec_single, B.vec_single]
  have hβmem : B.b 0 * B.b 1 ∈ B.span := by
    rw [← hvecβ]
    exact B.vec_mem_span twD7VBeta
  have hspanCen : B.span ≤ cen (B.b 0 * B.b 1) := by
    intro y hy
    obtain ⟨v, rfl⟩ := B.exists_vec_eq hy
    exact B.vec_mem_cen_twD7 v
  have hcN : (c : G) ∈ normalizer (B.span : Set G) := by
    refine (pr_mem_normalizer_img_iff hβmem hspanCen).mp ?_
    rw [← B.twD7Quot_span, hc]
    exact hnN
  have hβcen : (c : G) * (B.b 0 * B.b 1) = (B.b 0 * B.b 1) * c := mem_cen_iff.mp c.2
  have hβconj : (c : G) * (B.b 0 * B.b 1) * (c : G)⁻¹ = B.b 0 * B.b 1 := by
    rw [hβcen]; group
  obtain ⟨f, hf⟩ : ∃ f : Coords 8, B.vec f = (c : G) * B.b 0 * (c : G)⁻¹ :=
    B.exists_vec_eq ((Subgroup.mem_normalizer_iff.mp hcN (B.b 0)).mp (B.b_mem_span 0))
  have hq : n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec (Basis3.quotCoords f) := by
    calc n * B.twD7Quot.b 0 * n⁻¹
        = pr (B.b 0 * B.b 1) c * pr (B.b 0 * B.b 1) ⟨B.b 0, B.b_mem_cen_twD7 0⟩ *
            (pr (B.b 0 * B.b 1) c)⁻¹ := by rw [B.pr_b_zero_twD7Quot, hc]
      _ = pr (B.b 0 * B.b 1) (c * ⟨B.b 0, B.b_mem_cen_twD7 0⟩ * c⁻¹) := by
            rw [← map_inv, ← map_mul, ← map_mul]
      _ = pr (B.b 0 * B.b 1) ⟨B.vec f, B.vec_mem_cen_twD7 f⟩ := by
            congr 1
            apply Subtype.ext
            simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using hf.symm
      _ = B.twD7Quot.vec (Basis3.quotCoords f) := B.pr_vec_twD7Quot f (B.vec_mem_cen_twD7 f)
  have he : e = Basis3.quotCoords f := by
    apply B.twD7Quot.vec_injective
    rw [← hnconj, hq]
  have hf_ne : f ≠ 0 := by
    intro h0
    have h1 : B.vec f = 1 := by rw [h0, B.vec_zero]
    rw [hf] at h1
    have h2 : B.b 0 = 1 := by
      calc B.b 0 = (c : G)⁻¹ * ((c : G) * B.b 0 * (c : G)⁻¹) * c := by group
        _ = 1 := by rw [h1]; simp
    have h3 : orderOf (B.b 0) = 3 := B.ord 0
    rw [h2] at h3
    simp only [orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hlinef : IsConjLine (B.b 0) (B.line f) := by
    refine ⟨c, ?_⟩
    rw [Basis3.line, hf]
  have hwt1 : wt f = 1 ∨ wt f = 4 ∨ wt f = 7 := (hrec.2.1 f hf_ne).mp hlinef
  have hb1conj : (c : G) * B.b 1 * (c : G)⁻¹ = B.vec (twD7VBeta - f) := by
    have hsplit : (c : G) * B.b 1 * (c : G)⁻¹ =
        ((c : G) * B.b 0 * (c : G)⁻¹)⁻¹ * ((c : G) * (B.b 0 * B.b 1) * (c : G)⁻¹) := by
      group
    rw [hsplit, ← hf, hβconj, ← hvecβ, ← B.vec_neg, ← B.vec_add]
    congr 1
    funext i
    exact neg_add_eq_sub (f i) (twD7VBeta i)
  have hne2 : twD7VBeta - f ≠ 0 := by
    intro h0
    have h1 : B.vec (twD7VBeta - f) = 1 := by rw [h0, B.vec_zero]
    rw [← hb1conj] at h1
    have h2 : B.b 1 = 1 := by
      calc B.b 1 = (c : G)⁻¹ * ((c : G) * B.b 1 * (c : G)⁻¹) * c := by group
        _ = 1 := by rw [h1]; simp
    have h3 : orderOf (B.b 1) = 3 := B.ord 1
    rw [h2] at h3
    simp only [orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hline_b1 : IsConjLine (B.b 0) (B.line (Pi.single (1 : Fin 8) 1)) := by
    refine (hrec.2.1 (Pi.single (1 : Fin 8) 1) ?_).mpr (Or.inl ?_)
    · intro h0
      have := congrFun h0 1
      simp at this
    · decide
  have hline_sub : IsConjLine (B.b 0) (B.line (twD7VBeta - f)) := by
    have h := isConjLine_map_conj hline_b1 (c : G)
    have hmap : (B.line (Pi.single (1 : Fin 8) 1)).map (MulAut.conj (c : G)).toMonoidHom =
        B.line (twD7VBeta - f) := by
      rw [Basis3.line, MonoidHom.map_zpowers, B.vec_single]
      change Subgroup.zpowers ((c : G) * B.b 1 * (c : G)⁻¹) = B.line (twD7VBeta - f)
      rw [hb1conj, Basis3.line]
    rwa [hmap] at h
  have hwt2 : wt (twD7VBeta - f) = 1 ∨ wt (twD7VBeta - f) = 4 ∨ wt (twD7VBeta - f) = 7 :=
    (hrec.2.1 (twD7VBeta - f) hne2).mp hline_sub
  have hwt_w : wt (-(Pi.single (0 : Fin 8) 1) + Pi.single (1 : Fin 8) 1 : Coords 8) = 2 := by
    decide
  have hw_ne : (-(Pi.single (0 : Fin 8) 1) + Pi.single (1 : Fin 8) 1 : Coords 8) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
  have hlineIn_w : IsConjLineIn B.span (B.b 0 * B.b 1)
      (B.line (-(Pi.single (0 : Fin 8) 1) + Pi.single (1 : Fin 8) 1)) :=
    (hrec.2.2 _ hw_ne).mpr (Or.inl hwt_w)
  obtain ⟨n', hn'N, hn'conj⟩ := hlineIn_w
  have hwvec : B.vec (-(Pi.single (0 : Fin 8) 1) + Pi.single (1 : Fin 8) 1) =
      (B.b 0)⁻¹ * B.b 1 := by
    have hneg : B.vec (-(Pi.single (0 : Fin 8) (1 : ZMod 3))) =
        (B.vec (Pi.single (0 : Fin 8) (1 : ZMod 3)))⁻¹ := Basis3.vec_neg B _
    rw [B.vec_add, hneg, B.vec_single, B.vec_single]
  have hcw : (c : G) * B.vec (-(Pi.single (0 : Fin 8) 1) + Pi.single (1 : Fin 8) 1) *
      (c : G)⁻¹ = B.vec (twD7VBeta + f) := by
    rw [hwvec]
    have hsplit : (c : G) * ((B.b 0)⁻¹ * B.b 1) * (c : G)⁻¹ =
        ((c : G) * B.b 0 * (c : G)⁻¹)⁻¹ * ((c : G) * B.b 1 * (c : G)⁻¹) := by group
    rw [hsplit, ← hf, hb1conj, ← B.vec_neg, ← B.vec_add]
    congr 1
    funext i
    exact zmod3_neg_add_sub (twD7VBeta i) (f i)
  have hlineIn_add : IsConjLineIn B.span (B.b 0 * B.b 1) (B.line (twD7VBeta + f)) := by
    refine ⟨(c : G) * n', mul_mem hcN hn'N, ?_⟩
    calc Subgroup.zpowers (((c : G) * n') * (B.b 0 * B.b 1) * ((c : G) * n')⁻¹)
        = Subgroup.zpowers ((c : G) * (n' * (B.b 0 * B.b 1) * n'⁻¹) * (c : G)⁻¹) := by
          congr 1; group
      _ = (Subgroup.zpowers (n' * (B.b 0 * B.b 1) * n'⁻¹)).map
            (MulAut.conj (c : G)).toMonoidHom := by
          rw [MonoidHom.map_zpowers]; rfl
      _ = (B.line (-(Pi.single (0 : Fin 8) 1) + Pi.single (1 : Fin 8) 1)).map
            (MulAut.conj (c : G)).toMonoidHom := by rw [hn'conj]
      _ = Subgroup.zpowers ((c : G) * B.vec (-(Pi.single (0 : Fin 8) 1) +
            Pi.single (1 : Fin 8) 1) * (c : G)⁻¹) := by
          rw [Basis3.line, MonoidHom.map_zpowers]; rfl
      _ = Subgroup.zpowers (B.vec (twD7VBeta + f)) := by rw [hcw]
      _ = B.line (twD7VBeta + f) := rfl
  have hne_add : twD7VBeta + f ≠ 0 := by
    intro h0
    have h1 : B.vec (twD7VBeta + f) = 1 := by rw [h0, B.vec_zero]
    rw [← hcw, hwvec] at h1
    have h2 : (B.b 0)⁻¹ * B.b 1 = 1 := by
      calc (B.b 0)⁻¹ * B.b 1
          = (c : G)⁻¹ * ((c : G) * ((B.b 0)⁻¹ * B.b 1) * (c : G)⁻¹) * c := by group
        _ = 1 := by rw [h1]; simp
    have h3 : B.b 1 = B.b 0 := by
      calc B.b 1 = B.b 0 * ((B.b 0)⁻¹ * B.b 1) := by group
        _ = B.b 0 := by rw [h2, mul_one]
    have h4 : B.vec ((Pi.single (1 : Fin 8) 1 : Coords 8) - (Pi.single 0 1 : Coords 8)) = 1 := by
      have hneg : B.vec (-(Pi.single (0 : Fin 8) (1 : ZMod 3))) =
          (B.vec (Pi.single (0 : Fin 8) (1 : ZMod 3)))⁻¹ := Basis3.vec_neg B _
      rw [sub_eq_add_neg, B.vec_add, hneg, B.vec_single, B.vec_single, h3, mul_inv_cancel]
    have h5 : ((Pi.single (1 : Fin 8) 1 : Coords 8) - (Pi.single 0 1 : Coords 8)) = 0 :=
      B.vec_injective (by rw [h4, B.vec_zero])
    have h6 := congrFun h5 (1 : Fin 8)
    simp at h6
  have hcond : wt (twD7VBeta + f) = 2 ∨ (wt (twD7VBeta + f) = 8 ∧
      ∏ i : Fin 8, (twD7VBeta + f) i = -1) :=
    (hrec.2.2 (twD7VBeta + f) hne_add).mp hlineIn_add
  rw [he]
  exact isD6Root_quotCoords_of_wt hwt1 hwt2 hcond

private theorem normalizer_conj_of_glHom {G : Type} [Group G] {B : Basis3 G 8}
    {φ : MulAut ↥B.twD7Quot.span} {n : Q (B.b 0 * B.b 1)} {v : Coords 7}
    (hnact : ∀ b : ↥B.twD7Quot.span,
      ((φ b : ↥B.twD7Quot.span) : Q (B.b 0 * B.b 1)) = n * b * n⁻¹)
    (hv : B.twD7Quot.matOf φ *ᵥ Pi.single 0 1 = v) :
    n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec v := by
  have h1 : ((φ (B.twD7Quot.bS 0) : ↥B.twD7Quot.span) : Q (B.b 0 * B.b 1)) =
      n * B.twD7Quot.b 0 * n⁻¹ := hnact (B.twD7Quot.bS 0)
  have h2 : B.twD7Quot.coords (φ (B.twD7Quot.bS 0)) = v := by
    rw [B.twD7Quot.coords_apply, B.twD7Quot.coords_bS, hv]
  calc n * B.twD7Quot.b 0 * n⁻¹
      = ((φ (B.twD7Quot.bS 0) : ↥B.twD7Quot.span) : Q (B.b 0 * B.b 1)) := h1.symm
    _ = B.twD7Quot.vec (B.twD7Quot.coords (φ (B.twD7Quot.bS 0))) :=
        (B.twD7Quot.vec_coords _).symm
    _ = B.twD7Quot.vec v := by rw [h2]

private theorem card_d6RootType : Nat.card {e : Coords 7 // IsD6Root e} = 126 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_isD6Root

private theorem exists_normalizer_conj_of_isD6Root {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (hcard : Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) = 2903040) {e : Coords 7}
    (he : IsD6Root e) :
    ∃ n ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))),
      n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec e := by
  classical
  have hrec' : RecOutTwD7 B (B.b 0) := by rw [hB.2.1]; exact hrec
  let Xg : Subgroup (GL (Fin 7) (ZMod 3)) :=
    (ggAutomizer ⊤ B.twD7Quot.span).map B.twD7Quot.glHom
  let xf : ↥Xg → Coords 7 := fun A => (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1
  have hcardX : Nat.card ↥Xg = 2903040 := by
    change Nat.card ↥((ggAutomizer ⊤ B.twD7Quot.span).map B.twD7Quot.glHom) = 2903040
    rw [Subgroup.card_map_of_injective B.twD7Quot.glHom_injective]
    exact hcard
  have hstab : Nat.card {A : ↥Xg // xf A = Pi.single 0 1} ≤ 23040 := by
    change Nat.card {A : ↥((ggAutomizer ⊤ B.twD7Quot.span).map B.twD7Quot.glHom) //
      (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single (0 : Fin 7) 1 =
        Pi.single 0 1} ≤ 23040
    exact card_twD7Quot_stabilizer_le hstd hB hrec
  have himg : Set.range xf ⊆ {e : Coords 7 | IsD6Root e} := by
    rintro w ⟨A, rfl⟩
    obtain ⟨φ, n, hnN, hnact, hxeq⟩ := B.twD7Quot.exists_of_mem_xg A.2
    have hxmap : xf A = (B.twD7Quot.matOf φ) *ᵥ Pi.single (0 : Fin 7) 1 := by
      show ((A.1 : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
          Pi.single 0 1 = _
      rw [← hxeq]
      rfl
    rw [hxmap]
    exact isD6Root_of_exists_normalizer_conj hrec'
      ⟨n, hnN, normalizer_conj_of_glHom hnact rfl⟩
  have hfib : ∀ b ∈ Set.range xf, Nat.card {A : ↥Xg // xf A = b} ≤ 23040 := by
    intro b hb
    obtain ⟨A₀, hA₀⟩ := hb
    have hmap : ∀ A : {A : ↥Xg // xf A = b}, xf (A₀⁻¹ * A.1) = Pi.single 0 1 := by
      intro A
      have hAb : (A.1.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 = b := A.2
      have hA₀b : (A₀.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 = b := hA₀
      show (((A₀⁻¹ * A.1 : ↥Xg).1 : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
          Pi.single 0 1 = Pi.single 0 1
      have hcoe : (((A₀⁻¹ * A.1 : ↥Xg).1 : GL (Fin 7) (ZMod 3)) :
            Matrix (Fin 7) (Fin 7) (ZMod 3)) =
          (((A₀.1)⁻¹ * A.1.1 : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) := by
        rw [show (A₀⁻¹ * A.1 : ↥Xg).1 = (A₀.1)⁻¹ * A.1.1 from rfl]
      rw [hcoe, Units.val_mul, ← Matrix.mulVec_mulVec, hAb, ← hA₀b, Matrix.mulVec_mulVec]
      have hcancel : (((A₀.1)⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *
          ((A₀.1 : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hcancel, Matrix.one_mulVec]
    have hinj : Function.Injective (fun A : {A : ↥Xg // xf A = b} =>
        (⟨A₀⁻¹ * A.1, hmap A⟩ : {A : ↥Xg // xf A = Pi.single 0 1})) := by
      intro A A' h
      apply Subtype.ext
      have h1 : A₀⁻¹ * A.1 = A₀⁻¹ * A'.1 := congrArg Subtype.val h
      exact mul_left_cancel h1
    calc Nat.card {A : ↥Xg // xf A = b}
        ≤ Nat.card {A : ↥Xg // xf A = Pi.single 0 1} :=
          Nat.card_le_card_of_injective _ hinj
      _ ≤ 23040 := hstab
  have hrange_le : Nat.card (Set.range xf) ≤ 126 := by
    calc Nat.card (Set.range xf) = (Set.range xf).ncard := Nat.card_coe_set_eq _
      _ ≤ ({e : Coords 7 | IsD6Root e}).ncard := Set.ncard_le_ncard himg
      _ = Nat.card {e : Coords 7 // IsD6Root e} := (Nat.card_coe_set_eq _).symm
      _ = 126 := card_d6RootType
  have hle := natCard_le_mul_natCard_range xf 23040 hfib
  have hge : 126 ≤ Nat.card (Set.range xf) := by
    have h := hle
    rw [hcardX] at h
    have h' : 126 * 23040 ≤ Nat.card (Set.range xf) * 23040 := by
      calc 126 * 23040 = 2903040 := by norm_num
        _ ≤ Nat.card (Set.range xf) * 23040 := h
    exact Nat.le_of_mul_le_mul_right h' (by norm_num)
  have hrange_card : Nat.card (Set.range xf) = 126 := le_antisymm hrange_le hge
  have hrange_set : Set.range xf = {e : Coords 7 | IsD6Root e} := by
    apply Set.eq_of_subset_of_ncard_le himg
    have h1 : ({e : Coords 7 | IsD6Root e}).ncard = 126 := by
      rw [← Nat.card_coe_set_eq]
      change Nat.card {e : Coords 7 // IsD6Root e} = 126
      exact card_d6RootType
    have h2 : (Set.range xf).ncard = 126 := by
      rw [← Nat.card_coe_set_eq]
      exact hrange_card
    rw [h1, h2]
  have he_mem : e ∈ Set.range xf := by rw [hrange_set]; exact he
  obtain ⟨A, hA⟩ := Set.mem_range.mp he_mem
  obtain ⟨φ, n, hnN, hnact, hxeq⟩ := B.twD7Quot.exists_of_mem_xg A.2
  refine ⟨n, hnN, ?_⟩
  have hconj := normalizer_conj_of_glHom hnact
    (v := (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) (by
      show B.twD7Quot.matOf φ *ᵥ Pi.single 0 1 =
        (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1
      rw [← hxeq]
      rfl)
  rw [hconj]
  exact congrArg B.twD7Quot.vec hA

open TwD7Q in
theorem exists_normalizer_conj_twD7Quot_iff {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (hcard : Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) = 2903040) (e : Coords 7) :
    (∃ n ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))),
        n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec e) ↔ IsD6Root e :=
  ⟨isD6Root_of_exists_normalizer_conj (by rw [hB.2.1]; exact hrec),
    exists_normalizer_conj_of_isD6Root hstd hB hrec hcard⟩

end CFSG.StandardType.FrameRoute.FS81

end
