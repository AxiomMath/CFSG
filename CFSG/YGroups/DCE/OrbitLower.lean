module

public import CFSG.YGroups.DCE.OutSpecB
public import Mathlib.Order.CompletePartialOrder
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.YGroups.SymGen.Setup

open CFSG.YGroups.DCE

variable {G E Ω X : Type*} [Group G] [Group E] [MulAction E Ω] [MulAction E X]
  (S : Setup G E Ω)

@[expose] def cosetOf (y : G) (e : E) : G ⧸ S.H := ((S.ψ e * y⁻¹ : G) : G ⧸ S.H)

theorem cosetOf_eq_iff {y : G} {e e' : E} :
    S.cosetOf y e = S.cosetOf y e' ↔ e⁻¹ * e' ∈ B.stabSub S y := by
  rw [cosetOf, cosetOf, QuotientGroup.eq, B.mem_stabSub, map_mul, map_inv]
  constructor <;> intro h <;> simpa [mul_assoc] using h

@[expose] def fib (y : G) (ω₀ ω : X) : Set (G ⧸ S.H) :=
  {c | ∃ e : E, e⁻¹ • ω₀ ∈ MulAction.orbit (B.stabSub S y) ω ∧ c = S.cosetOf y e}

@[expose] def porb (P : Subgroup G) : Set (G ⧸ S.H) :=
  {c | ∃ p ∈ P, c = ((p : G) : G ⧸ S.H)}

variable {S}

theorem mul_mem_porb {P : Subgroup G} {p : G} (hp : p ∈ P) {g : G}
    (hg : ((g : G) : G ⧸ S.H) ∈ S.porb P) : ((p * g : G) : G ⧸ S.H) ∈ S.porb P := by
  obtain ⟨q, hq, he⟩ := hg
  refine ⟨p * q, P.mul_mem hp hq, ?_⟩
  rw [QuotientGroup.eq] at he ⊢
  simpa [mul_assoc] using he

theorem fib_subset_porb {P : Subgroup G} {ω₀ : X} (hJ : ∀ e : E, e • ω₀ = ω₀ → S.ψ e ∈ P)
    {y : G} {ω : X} {e₀ : E} (he₀ : e₀⁻¹ • ω₀ ∈ MulAction.orbit (B.stabSub S y) ω)
    (hc : S.cosetOf y e₀ ∈ S.porb P) : S.fib y ω₀ ω ⊆ S.porb P := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨⟨s₁, hs₁⟩, hs₁e⟩ := he
  obtain ⟨⟨s₀, hs₀⟩, hs₀e⟩ := he₀
  have hs₁e : s₁ • ω = e⁻¹ • ω₀ := hs₁e
  have hs₀e : s₀ • ω = e₀⁻¹ • ω₀ := hs₀e
  set s := s₁ * s₀⁻¹ with hs
  have hsS : s ∈ B.stabSub S y := mul_mem hs₁ (inv_mem hs₀)
  have hse : e⁻¹ • ω₀ = s • (e₀⁻¹ • ω₀) := by
    rw [← hs₀e, ← mul_smul, hs, inv_mul_cancel_right, hs₁e]
  have hj : (e * s * e₀⁻¹) • ω₀ = ω₀ := by
    rw [mul_smul, mul_smul, ← hse, smul_inv_smul]
  have hjP := hJ _ hj
  have heq : S.cosetOf y e = ((S.ψ (e * s * e₀⁻¹) * (S.ψ e₀ * y⁻¹) : G) : G ⧸ S.H) := by
    rw [cosetOf, QuotientGroup.eq]
    have h1 : y * S.ψ s * y⁻¹ ∈ S.H := (B.mem_stabSub S _ _).1 hsS
    have h2 : (S.ψ e * y⁻¹)⁻¹ * (S.ψ (e * s * e₀⁻¹) * (S.ψ e₀ * y⁻¹)) = y * S.ψ s * y⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [h2]
    exact h1
  rw [heq]
  exact mul_mem_porb hjP hc

theorem fib_base_subset_porb {P : Subgroup G} {ω₀ : X}
    (hJ : ∀ e : E, e • ω₀ = ω₀ → S.ψ e ∈ P) {x₀ : G} (hx₀ : x₀ ∈ S.H) :
    S.fib x₀ ω₀ ω₀ ⊆ S.porb P := by
  refine fib_subset_porb hJ (e₀ := 1) (by rw [inv_one, one_smul]; exact MulAction.mem_orbit_self _)
    ⟨1, P.one_mem, ?_⟩
  rw [cosetOf, QuotientGroup.eq]
  simpa using hx₀

theorem fib_move {P : Subgroup G} {ω₀ : X} (hJ : ∀ e : E, e • ω₀ = ω₀ → S.ψ e ∈ P)
    (ht : S.t ∈ P) {xi xk : G} {ω ω'' : X} {r : Ω} {er : E}
    (hfib : S.fib xi ω₀ ω ⊆ S.porb P) (hrc : S.RCoset (xi * S.T r) (xk * S.ψ er))
    (hω : ω'' ∈ MulAction.orbit (B.stabSub S xi) ω) (hinc : ∃ g : E, g • ω₀ = ω'' ∧ g • S.o = r) :
    S.fib xk ω₀ (er • ω'') ⊆ S.porb P := by
  obtain ⟨g, hgω, hgo⟩ := hinc
  have hc : S.cosetOf xi g⁻¹ ∈ S.porb P :=
    hfib ⟨g⁻¹, by rw [inv_inv, hgω]; exact hω, rfl⟩
  refine fib_subset_porb hJ (e₀ := g⁻¹ * er⁻¹) ?_ ?_
  · rw [mul_inv_rev, inv_inv, inv_inv, mul_smul, hgω]
    exact MulAction.mem_orbit_self _
  ·
    obtain ⟨q, hq, hqe⟩ := hc
    have hT : S.T r = S.ψ g * S.t * (S.ψ g)⁻¹ := S.T_eq_of_smul g r hgo
    refine ⟨S.t * q, P.mul_mem ht hq, ?_⟩
    rw [cosetOf, QuotientGroup.eq] at hqe ⊢
    have hrc' : xi * S.T r * (xk * S.ψ er)⁻¹ ∈ S.H := hrc
    rw [hT] at hrc'
    have key : (S.ψ (g⁻¹ * er⁻¹) * xk⁻¹)⁻¹ * (S.t * q) =
        (xi * (S.ψ g * S.t * (S.ψ g)⁻¹) * (xk * S.ψ er)⁻¹)⁻¹ *
          ((S.ψ g⁻¹ * xi⁻¹)⁻¹ * q) := by
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
      have ht' : S.t⁻¹ = S.t := S.t_inv
      rw [ht']
      group
    rw [key]
    exact S.H.mul_mem (S.H.inv_mem hrc') hqe

theorem fib_subset_porb_of_moves {P : Subgroup G} {ω₀ : X}
    (hJ : ∀ e : E, e • ω₀ = ω₀ → S.ψ e ∈ P) (ht : S.t ∈ P) (x : ℕ → G) (labels : ℕ → ℕ × X)
    (m : ℕ) (h0 : x (labels 0).1 ∈ S.H) (h0' : (labels 0).2 = ω₀)
    (hmove : ∀ i, 0 < i → i < m → ∃ i' < i, ∃ (r : Ω) (er : E) (ω'' : X),
      S.RCoset (x (labels i').1 * S.T r) (x (labels i).1 * S.ψ er) ∧
      ω'' ∈ MulAction.orbit (B.stabSub S (x (labels i').1)) (labels i').2 ∧
      (∃ g : E, g • ω₀ = ω'' ∧ g • S.o = r) ∧ (labels i).2 = er • ω'') :
    ∀ i < m, S.fib (x (labels i).1) ω₀ (labels i).2 ⊆ S.porb P := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0']
      exact fib_base_subset_porb hJ h0
    · obtain ⟨i', hi', r, er, ω'', hrc, hω, hinc, hlab⟩ := hmove i hpos hi
      rw [hlab]
      exact fib_move hJ ht (ih i' hi' (hi'.trans hi)) hrc hω hinc

theorem le_ncard_fib [Finite E] [Finite X] {y : G} {ω₀ ω : X}
    (hω : ω ∈ MulAction.orbit E ω₀) {s : ℕ} (hs : s ≤ (B.stabSub S y).index) :
    s * (MulAction.orbit (B.stabSub S y) ω).ncard ≤
      (MulAction.orbit E ω₀).ncard * (S.fib y ω₀ ω).ncard := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have : Fintype X := Fintype.ofFinite X
  set Sn := B.stabSub S y
  set Ob : Set X := MulAction.orbit Sn ω
  let A : Finset E := Finset.univ.filter fun e => e⁻¹ • ω₀ ∈ Ob
  let ObF : Finset X := Finset.univ.filter fun b => b ∈ Ob
  have hObF : ObF.card = Ob.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext b
    simp [ObF]
  have hfibre : ∀ b ∈ ObF, (A.filter fun e => e⁻¹ • ω₀ = b).card =
      Nat.card (MulAction.stabilizer E ω₀) := by
    intro b hb
    have hbO : b ∈ MulAction.orbit E ω₀ := by
      have hbOb : b ∈ Ob := (Finset.mem_filter.1 hb).2
      obtain ⟨⟨s', _⟩, hs'⟩ := hbOb
      obtain ⟨g, hg⟩ := hω
      have hg' : g • ω₀ = ω := hg
      have hs'' : s' • ω = b := hs'
      refine ⟨s' * g, ?_⟩
      show (s' * g) • ω₀ = b
      rw [mul_smul, hg', hs'']
    obtain ⟨g, hg⟩ := hbO
    have hg' : g • ω₀ = b := hg
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun e => ⟨g⁻¹ * e.1⁻¹, ?_⟩
        invFun := fun k => ⟨(g * k.1)⁻¹, ?_⟩
        left_inv := fun e => by ext; simp
        right_inv := fun k => by ext; simp }
    · obtain ⟨e, he⟩ := e
      have he' : e⁻¹ • ω₀ = b := (Finset.mem_filter.1 he).2
      rw [MulAction.mem_stabilizer_iff, mul_smul, he', ← hg', inv_smul_smul]
    · obtain ⟨k, hk⟩ := k
      have hk' : k • ω₀ = ω₀ := hk
      have hmem : (g * k)⁻¹⁻¹ • ω₀ = b := by rw [inv_inv, mul_smul, hk', hg']
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hmem⟩
      rw [hmem]
      exact (Finset.mem_filter.1 hb).2
  have hA : A.card = Ob.ncard * Nat.card (MulAction.stabilizer E ω₀) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun e => e⁻¹ • ω₀) (t := ObF)
      (fun e he => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2⟩),
      Finset.sum_congr rfl hfibre, Finset.sum_const, smul_eq_mul, hObF]
  let img : Finset (G ⧸ S.H) := A.image (S.cosetOf y)
  have himg : (img : Set (G ⧸ S.H)) ⊆ S.fib y ω₀ ω := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    exact ⟨e, (Finset.mem_filter.1 he).2, rfl⟩
  have hfin : (S.fib y ω₀ ω).Finite := by
    refine Set.Finite.subset (A.image (S.cosetOf y)).finite_toSet ?_
    rintro _ ⟨e, he, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩))
  have hle_img : img.card ≤ (S.fib y ω₀ ω).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg hfin
  have hA_le : A.card ≤ Nat.card Sn * img.card := by
    refine Finset.card_le_mul_card_image (f := S.cosetOf y) A (Nat.card Sn) fun c hc => ?_
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 hc
    calc (A.filter fun e => S.cosetOf y e = S.cosetOf y e₀).card
        ≤ (Finset.univ.filter fun e : E => e₀⁻¹ * e ∈ Sn).card := by
          refine Finset.card_le_card fun e he => ?_
          have h1 := (Finset.mem_filter.1 he).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          exact (S.cosetOf_eq_iff).1 h1.symm
      _ = Nat.card Sn := by
          rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun e => ⟨e₀⁻¹ * e.1, (Finset.mem_filter.1 e.2).2⟩
              invFun := fun k => ⟨e₀ * k.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, by
                simp⟩⟩
              left_inv := fun e => by ext; simp
              right_inv := fun k => by ext; simp }
  have hidx := Subgroup.index_mul_card Sn
  have hpos : 0 < Nat.card (MulAction.stabilizer E ω₀) := Nat.card_pos
  have horb' : (MulAction.orbit E ω₀).ncard * Nat.card (MulAction.stabilizer E ω₀) =
      Nat.card E := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_mul_card _
  have h1 : Ob.ncard * Nat.card (MulAction.stabilizer E ω₀) * Sn.index ≤
      (MulAction.orbit E ω₀).ncard * Nat.card (MulAction.stabilizer E ω₀) *
        (S.fib y ω₀ ω).ncard := by
    rw [horb', ← hidx, ← hA]
    calc A.card * Sn.index ≤ Nat.card Sn * img.card * Sn.index := Nat.mul_le_mul_right _ hA_le
      _ ≤ Nat.card Sn * (S.fib y ω₀ ω).ncard * Sn.index :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hle_img)
      _ = Sn.index * Nat.card Sn * (S.fib y ω₀ ω).ncard := by ring
  have h2 : Ob.ncard * Sn.index ≤ (MulAction.orbit E ω₀).ncard * (S.fib y ω₀ ω).ncard := by
    have h3 : Ob.ncard * Sn.index * Nat.card (MulAction.stabilizer E ω₀) ≤
        (MulAction.orbit E ω₀).ncard * (S.fib y ω₀ ω).ncard *
          Nat.card (MulAction.stabilizer E ω₀) := by
      calc Ob.ncard * Sn.index * Nat.card (MulAction.stabilizer E ω₀)
          = Ob.ncard * Nat.card (MulAction.stabilizer E ω₀) * Sn.index := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h3 hpos
  calc s * Ob.ncard ≤ Sn.index * Ob.ncard := Nat.mul_le_mul_right _ hs
    _ = Ob.ncard * Sn.index := by ring
    _ ≤ _ := h2

theorem sum_ncard_fib_eq [Finite G] {ω₀ : X} (x : ℕ → G) (labels : List (ℕ × X))
    (hnodup : (labels.map Prod.fst).Nodup)
    (hdisj : ∀ lab ∈ labels, ∀ lab' ∈ labels, ∀ a b : E,
      S.cosetOf (x lab.1) a = S.cosetOf (x lab'.1) b → lab.1 = lab'.1) :
    (labels.map fun lab => (S.fib (x lab.1) ω₀ lab.2).ncard).sum =
      (⋃ lab ∈ labels, S.fib (x lab.1) ω₀ lab.2).ncard := by
  induction labels with
  | nil => simp
  | cons lab rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    have hU : (⋃ a ∈ lab :: rest, S.fib (x a.1) ω₀ a.2) =
        S.fib (x lab.1) ω₀ lab.2 ∪ ⋃ a ∈ rest, S.fib (x a.1) ω₀ a.2 := by
      ext c
      simp only [Set.mem_iUnion, Set.mem_union, List.mem_cons, exists_prop]
      constructor
      · rintro ⟨a, rfl | ha, hc⟩
        · exact Or.inl hc
        · exact Or.inr ⟨a, ha, hc⟩
      · rintro (hc | ⟨a, ha, hc⟩)
        · exact ⟨lab, Or.inl rfl, hc⟩
        · exact ⟨a, Or.inr ha, hc⟩
    have hdisjU : Disjoint (S.fib (x lab.1) ω₀ lab.2) (⋃ a ∈ rest, S.fib (x a.1) ω₀ a.2) := by
      rw [Set.disjoint_left]
      rintro c ⟨e, -, rfl⟩ hcU
      obtain ⟨a, ha, ⟨e', -, he'⟩⟩ := Set.mem_iUnion₂.1 hcU
      have := hdisj lab List.mem_cons_self a (List.mem_cons_of_mem _ ha) e e' he'
      exact hnodup.1 ⟨a, ha, this.symm⟩
    rw [List.map_cons, List.sum_cons, hU, Set.ncard_union_eq hdisjU (Set.toFinite _)
      (Set.toFinite _), ih hnodup.2 fun a ha b hb => hdisj a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)]

theorem sum_le_ncard_porb [Finite G] [Finite E] [Finite X] {P : Subgroup G} {ω₀ : X}
    (x : ℕ → G) (labels : List (ℕ × X)) (hnodup : (labels.map Prod.fst).Nodup)
    (hdisj : ∀ lab ∈ labels, ∀ lab' ∈ labels, ∀ a b : E,
      S.cosetOf (x lab.1) a = S.cosetOf (x lab'.1) b → lab.1 = lab'.1)
    (hreach : ∀ lab ∈ labels, S.fib (x lab.1) ω₀ lab.2 ⊆ S.porb P)
    (s : ℕ → ℕ) (hs : ∀ lab ∈ labels, s lab.1 ≤ (B.stabSub S (x lab.1)).index)
    (horb : ∀ lab ∈ labels, lab.2 ∈ MulAction.orbit E ω₀) :
    (labels.map fun lab => s lab.1 * (MulAction.orbit (B.stabSub S (x lab.1)) lab.2).ncard).sum ≤
      (MulAction.orbit E ω₀).ncard * (S.porb P).ncard := by
  have h1 : (labels.map fun lab =>
      s lab.1 * (MulAction.orbit (B.stabSub S (x lab.1)) lab.2).ncard).sum ≤
      (labels.map fun lab =>
        (MulAction.orbit E ω₀).ncard * (S.fib (x lab.1) ω₀ lab.2).ncard).sum :=
    List.sum_le_sum fun lab hlab => le_ncard_fib (horb lab hlab) (hs lab hlab)
  have h2 : (labels.map fun lab =>
      (MulAction.orbit E ω₀).ncard * (S.fib (x lab.1) ω₀ lab.2).ncard).sum =
      (MulAction.orbit E ω₀).ncard * (⋃ lab ∈ labels, S.fib (x lab.1) ω₀ lab.2).ncard := by
    rw [← sum_ncard_fib_eq x labels hnodup hdisj, List.sum_map_mul_left]
  have h3 : (⋃ lab ∈ labels, S.fib (x lab.1) ω₀ lab.2).ncard ≤ (S.porb P).ncard :=
    Set.ncard_le_ncard (Set.iUnion₂_subset hreach) (Set.toFinite _)
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := Nat.mul_le_mul_left _ h3

theorem ncard_porb [Finite G] (P : Subgroup G) : (S.porb P).ncard = (S.H.subgroupOf P).index := by
  classical
  have : Finite (P ⧸ S.H.subgroupOf P) := inferInstance
  rw [← Nat.card_coe_set_eq, Subgroup.index]
  refine (Nat.card_congr (Equiv.ofBijective (fun q : P ⧸ S.H.subgroupOf P =>
    (⟨Quotient.liftOn' q (fun p : P => ((p : G) : G ⧸ S.H)) fun a b hab => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
      rw [QuotientGroup.eq]
      simpa using hab, ?_⟩ : S.porb P)) ⟨?_, ?_⟩)).symm
  · induction q using QuotientGroup.induction_on with
    | H p => exact ⟨p, p.2, rfl⟩
  · intro q q' hqq'
    induction q using QuotientGroup.induction_on with
    | H p =>
    induction q' using QuotientGroup.induction_on with
    | H p' =>
    have h := congrArg Subtype.val hqq'
    simp only [Quotient.liftOn'_mk''] at h
    rw [QuotientGroup.eq] at h ⊢
    rw [Subgroup.mem_subgroupOf]
    simpa using h
  · rintro ⟨c, p, hp, rfl⟩
    exact ⟨QuotientGroup.mk (⟨p, hp⟩ : P), rfl⟩

end CFSG.YGroups.SymGen.Setup
