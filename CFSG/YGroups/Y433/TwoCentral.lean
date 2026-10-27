module

public import CFSG.YGroups.Y433.Central
public import CFSG.YGroups.Y433.CyclicArm
public import CFSG.YGroups.Y443.OddInvolutionDiagram

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord)

theorem mem_zpowers_involution {G : Type*} [Group G] {x w : G} (hx : x * x = 1)
    (hw : w ∈ Subgroup.zpowers x) : w = 1 ∨ w = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ← pow_two, hx2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ← pow_two, hx2, one_zpow, one_mul, zpow_one]

theorem normalClosure_singleton_eq_zpowers_of_mem_center {G : Type*} [Group G] {x : G}
    (hx : x ∈ Subgroup.center G) : Subgroup.normalClosure {x} = Subgroup.zpowers x := by
  have : (Subgroup.zpowers x).Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hx)
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_
  · rw [Set.singleton_subset_iff]
    exact Subgroup.mem_zpowers x
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_normalClosure rfl)

namespace U433

@[expose] noncomputable def gen : Fin (ngen 4 3 3) → U433 := PresentedGroup.of

theorem gen_eq_yGen (i : Fin (ngen 4 3 3)) : gen i = yGen 4 3 3 i := (yGen_of_lt i.2).symm

theorem gen_mul_self (i : Fin (ngen 4 3 3)) : gen i * gen i = 1 := by
  rw [gen_eq_yGen]
  exact yGen_mul_self 4 3 3 _

@[expose] def graph : SimpleGraph (Fin (ngen 4 3 3)) :=
  SimpleGraph.fromRel fun i j => (i.val, j.val) ∈ yEdges 4 3 3

theorem graph_adj {i j : Fin (ngen 4 3 3)} :
    graph.Adj i j ↔ i ≠ j ∧ ((i.val, j.val) ∈ yEdges 4 3 3 ∨ (j.val, i.val) ∈ yEdges 4 3 3) :=
  SimpleGraph.fromRel_adj _ _ _

@[expose] def parent (c : ℕ) : ℕ := [0, 0, 1, 2, 3, 0, 5, 6, 0, 8, 9].getD c 0

theorem parent_spec : ∀ c < 11, 0 < c → parent c < c ∧ (parent c, c) ∈ yEdges 4 3 3 := by decide

theorem edges_lt : ∀ p ∈ yEdges 4 3 3, p.1 < p.2 ∧ p.2 < 11 := by decide

theorem graph_connected : graph.Connected := by
  have h : ∀ n, ∀ c : Fin (ngen 4 3 3), c.val = n → graph.Reachable c ⟨0, by decide⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hc
      by_cases h0 : c.val = 0
      · have : c = ⟨0, by decide⟩ := Fin.ext h0
        rw [this]
      · have hpos : 0 < c.val := Nat.pos_of_ne_zero h0
        obtain ⟨hlt, hmem⟩ := parent_spec c.val c.2 hpos
        let p : Fin (ngen 4 3 3) := ⟨parent c.val, by have := c.2; omega⟩
        have hadj : graph.Adj p c := by
          rw [graph_adj]
          exact ⟨fun h => by have := congrArg Fin.val h; simp [p] at this; omega, Or.inl hmem⟩
        have hp : graph.Reachable p ⟨0, by decide⟩ := ih p.val (by rw [← hc]; exact hlt) p rfl
        exact hadj.symm.reachable.trans hp
  have : Nonempty (Fin (ngen 4 3 3)) := ⟨⟨0, by decide⟩⟩
  exact ⟨fun a b => (h a.val a rfl).trans (h b.val b rfl).symm⟩

theorem pow_three_of_adj {i j : Fin (ngen 4 3 3)} (h : graph.Adj i j) :
    (gen i * gen j) ^ 3 = 1 := by
  obtain ⟨-, h1 | h1⟩ := graph_adj.1 h
  · have hlt := edges_lt _ h1
    have := Y443.yGen_pair_pow (p := 4) (q := 3) (r := 3) hlt.1 j.2
    rw [show pairExp 4 3 3 i.val j.val = 3 by simp [pairExp, h1]] at this
    rw [gen_eq_yGen, gen_eq_yGen]
    exact this
  · have hlt := edges_lt _ h1
    have := Y443.yGen_pair_pow (p := 4) (q := 3) (r := 3) hlt.1 i.2
    rw [show pairExp 4 3 3 j.val i.val = 3 by simp [pairExp, h1]] at this
    rw [gen_eq_yGen, gen_eq_yGen]
    exact Y443.pow_eq_one_of_swap (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) this

theorem exists_odd_of_adj {i j : Fin (ngen 4 3 3)} (h : graph.Adj i j) :
    ∃ m : ℕ, Odd m ∧ (gen i * gen j) ^ m = 1 :=
  ⟨3, by decide, pow_three_of_adj h⟩

theorem exists_free_letter : ∀ p ∈ yEdges 4 3 3, ∃ k < 11, k ≠ p.1 ∧ k ≠ p.2 ∧
    (k, p.1) ∉ yEdges 4 3 3 ∧ (p.1, k) ∉ yEdges 4 3 3 ∧
    (k, p.2) ∉ yEdges 4 3 3 ∧ (p.2, k) ∉ yEdges 4 3 3 := by decide

theorem exists_commute_of_adj {i j : Fin (ngen 4 3 3)} (h : graph.Adj i j) :
    ∃ k, Commute (gen k) (gen i) ∧ Commute (gen k) (gen j) := by
  have key : ∀ a b : ℕ, (a, b) ∈ yEdges 4 3 3 → ∀ (ha : a < ngen 4 3 3) (hb : b < ngen 4 3 3),
      ∃ k : Fin (ngen 4 3 3), Commute (gen k) (gen ⟨a, ha⟩) ∧ Commute (gen k) (gen ⟨b, hb⟩) := by
    intro a b hab ha hb
    obtain ⟨k, hk, hk1, hk2, hk3, hk4, hk5, hk6⟩ := exists_free_letter (a, b) hab
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · rw [gen_eq_yGen, gen_eq_yGen]
      exact Relabel.commute_yGen_of_not_edge hk ha hk1 hk3 hk4
    · rw [gen_eq_yGen, gen_eq_yGen]
      exact Relabel.commute_yGen_of_not_edge hk hb hk2 hk5 hk6
  obtain ⟨-, h1 | h1⟩ := graph_adj.1 h
  · exact key i j h1 i.2 j.2
  · obtain ⟨k, hk1, hk2⟩ := key j i h1 j.2 i.2
    exact ⟨k, hk2, hk1⟩

theorem gen_mul_gen_mem_commutator (i j : Fin (ngen 4 3 3)) :
    gen i * gen j ∈ commutator U433 :=
  OddInvolutionDiagram.pair_mem_commutator graph gen graph_connected gen_mul_self
    (fun _ _ h => exists_odd_of_adj h) i j

theorem sgn_A : sgn A = Multiplicative.ofAdd 1 := sgn_yGen (by decide)

theorem commutator_le_ker_sgn : commutator U433 ≤ sgn.ker :=
  Abelianization.commutator_subset_ker sgn

theorem top_le_commutator_sup : (⊤ : Subgroup U433) ≤ commutator U433 ⊔ Subgroup.zpowers A := by
  refine le_trans (le_of_eq (closure_yGen 4 3 3).symm) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  have h1 : yGen 4 3 3 c * A ∈ commutator U433 := by
    have := gen_mul_gen_mem_commutator ⟨c, hc⟩ ⟨0, by decide⟩
    rwa [gen_eq_yGen, gen_eq_yGen] at this
  have h2 : yGen 4 3 3 c = (yGen 4 3 3 c * A) * A := by rw [mul_assoc, A_mul_self, mul_one]
  rw [SetLike.mem_coe, h2]
  exact Subgroup.mul_mem_sup h1 (Subgroup.mem_zpowers A)

theorem commutator_eq_ker_sgn : commutator U433 = sgn.ker := by
  refine le_antisymm commutator_le_ker_sgn fun g hg => ?_
  obtain ⟨c, hc, w, hw, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.1 (top_le_commutator_sup (Subgroup.mem_top g))
  rcases mem_zpowers_involution A_mul_self hw with rfl | rfl
  · simpa using hc
  · exfalso
    rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.1 (commutator_le_ker_sgn hc), one_mul,
      sgn_A] at hg
    exact absurd hg (by decide)

theorem sgn_surjective : Function.Surjective sgn := by
  intro x
  have h : x = 1 ∨ x = Multiplicative.ofAdd 1 := by revert x; decide
  rcases h with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨A, sgn_A⟩

theorem commutator_index : (commutator U433).index = 2 := by
  rw [commutator_eq_ker_sgn, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ sgn_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  rfl

theorem commutator_commutator : ⁅commutator U433, commutator U433⁆ = commutator U433 :=
  OddInvolutionDiagram.commutator_commutator_eq graph gen graph_connected
    (PresentedGroup.closure_range_of _) gen_mul_self (fun _ _ h => exists_odd_of_adj h)
    (fun _ _ h => exists_commute_of_adj h)

theorem isPerfect_commutator : Group.IsPerfect (commutator U433) :=
  Subgroup.isPerfect_iff.2 commutator_commutator

end U433

theorem F433_213_not_mem_commutator : F433 2 1 3 ∉ commutator U433 := by
  intro h
  rw [U433.commutator_eq_ker_sgn, MonoidHom.mem_ker, U433.sgn_F433] at h
  exact absurd h (by decide)

theorem zpowers_F433_213_le_center :
    Subgroup.zpowers (F433 2 1 3) ≤ Subgroup.center U433 :=
  Subgroup.zpowers_le.2 F433_213_mem_center

theorem disjoint_commutator_zpowers_F433_213 :
    Disjoint (commutator U433) (Subgroup.zpowers (F433 2 1 3)) := by
  rw [Subgroup.disjoint_def]
  intro x hx hxz
  rcases mem_zpowers_involution F433_213_mul_self hxz with rfl | rfl
  · rfl
  · exact absurd hx F433_213_not_mem_commutator

theorem commutator_sup_zpowers_F433_213 :
    commutator U433 ⊔ Subgroup.zpowers (F433 2 1 3) = ⊤ := by
  refine eq_top_iff.2 fun u _ => ?_
  by_cases hu : u ∈ commutator U433
  · exact Subgroup.mem_sup_left hu
  · have hs : U433.sgn u = Multiplicative.ofAdd 1 := by
      have h : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
      rcases h (U433.sgn u) with h | h
      · exact absurd (by rw [U433.commutator_eq_ker_sgn]; exact h) hu
      · exact h
    have huF : u * F433 2 1 3 ∈ commutator U433 := by
      rw [U433.commutator_eq_ker_sgn, MonoidHom.mem_ker, map_mul, hs, U433.sgn_F433]
      decide
    have h2 : u = (u * F433 2 1 3) * F433 2 1 3 := by
      rw [mul_assoc, F433_213_mul_self, mul_one]
    rw [h2]
    exact Subgroup.mul_mem_sup huF (Subgroup.mem_zpowers _)

theorem commute_commutator_zpowers
    (m : commutator U433)
    (n : Subgroup.zpowers (F433 2 1 3)) :
    Commute ((commutator U433).subtype m) ((Subgroup.zpowers (F433 2 1 3)).subtype n) :=
  Subgroup.mem_center_iff.1 (zpowers_F433_213_le_center n.2) m

@[expose] noncomputable def derivedProdHom :
    (commutator U433) × (Subgroup.zpowers (F433 2 1 3)) →* U433 :=
  MonoidHom.noncommCoprod (commutator U433).subtype (Subgroup.zpowers (F433 2 1 3)).subtype
    commute_commutator_zpowers

theorem derivedProdHom_apply
    (a : commutator U433) (z : Subgroup.zpowers (F433 2 1 3)) :
    derivedProdHom (a, z) = (a : U433) * (z : U433) :=
  MonoidHom.noncommCoprod_apply _ _ _ _

theorem derivedProdHom_injective :
    Function.Injective derivedProdHom := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, z⟩ h
  rw [derivedProdHom_apply] at h
  have haz : (a : U433) = (z : U433)⁻¹ := eq_inv_of_mul_eq_one_left h
  have h1 : (a : U433) ∈ Subgroup.zpowers (F433 2 1 3) := by
    rw [haz]
    exact inv_mem z.2
  have ha : (a : U433) = 1 :=
    Subgroup.disjoint_def.1 disjoint_commutator_zpowers_F433_213 a.2 h1
  have hz : (z : U433) = 1 := by
    rw [ha, one_mul] at h
    exact h
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hz)

theorem derivedProdHom_surjective :
    Function.Surjective derivedProdHom := fun u => by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1
    (commutator_sup_zpowers_F433_213 ▸ Subgroup.mem_top u)
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), derivedProdHom_apply _ _⟩

@[expose] noncomputable def derivedProdEquiv :
    (commutator U433) × (Subgroup.zpowers (F433 2 1 3)) ≃* U433 :=
  MulEquiv.ofBijective derivedProdHom ⟨derivedProdHom_injective, derivedProdHom_surjective⟩

theorem derivedProdEquiv_apply
    (a : commutator U433) (z : Subgroup.zpowers (F433 2 1 3)) :
    derivedProdEquiv (a, z) = (a : U433) * (z : U433) :=
  derivedProdHom_apply a z

theorem ker_π_eq_zpowers :
    R433.π.ker = Subgroup.zpowers (F433 2 1 3) := by
  rw [R433.ker_π, normalClosure_singleton_eq_zpowers_of_mem_center F433_213_mem_center]

namespace R433

@[expose] noncomputable def derivedHom : commutator U433 →* R433 :=
  π.comp (commutator U433).subtype

theorem derivedHom_apply (a : commutator U433) : derivedHom a = π (a : U433) := rfl

theorem derivedHom_injective :
    Function.Injective derivedHom := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (a : U433) ∈ π.ker := ha
  rw [ker_π_eq_zpowers] at h1
  exact Subtype.ext (Subgroup.disjoint_def.1 disjoint_commutator_zpowers_F433_213 a.2 h1)

theorem derivedHom_surjective :
    Function.Surjective derivedHom := by
  intro r
  obtain ⟨u, rfl⟩ := π_surjective r
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1
    (commutator_sup_zpowers_F433_213 ▸ Subgroup.mem_top u)
  refine ⟨⟨y, hy⟩, ?_⟩
  have hz1 : π z = 1 := by
    rw [← MonoidHom.mem_ker, ker_π_eq_zpowers]
    exact hz
  rw [derivedHom_apply, map_mul, hz1, mul_one]

@[expose] noncomputable def derivedEquiv :
    commutator U433 ≃* R433 :=
  MulEquiv.ofBijective derivedHom ⟨derivedHom_injective, derivedHom_surjective⟩

theorem derivedEquiv_apply
    (a : commutator U433) : derivedEquiv a = π (a : U433) := rfl

theorem map_commutator_π :
    (commutator U433).map π = ⊤ := by
  rw [eq_top_iff]
  intro r _
  obtain ⟨a, ha⟩ := derivedHom_surjective r
  exact ⟨a, a.2, ha⟩

theorem commutator_eq_top :
    commutator R433 = ⊤ := by
  calc commutator R433 = ⁅(⊤ : Subgroup R433), ⊤⁆ := commutator_def R433
    _ = ⁅(commutator U433).map π, (commutator U433).map π⁆ := by rw [map_commutator_π]
    _ = (⁅commutator U433, commutator U433⁆).map π := (Subgroup.map_commutator _ _ _).symm
    _ = (commutator U433).map π := by rw [U433.commutator_commutator]
    _ = ⊤ := map_commutator_π

theorem isPerfect :

    Group.IsPerfect R433 := Group.isPerfect_def.2 commutator_eq_top

@[expose] noncomputable def c312 : R433 := π (F433 3 1 2)

theorem c312_mem_center :
    c312 ∈ Subgroup.center R433 := π_F433_312_mem_center

theorem c312_mul_self :
    c312 * c312 = 1 := π_F433_312_mul_self

theorem c312_pow_two :
    c312 ^ 2 = 1 := by rw [pow_two, c312_mul_self]

theorem c312_ne_one_iff :
    c312 ≠ 1 ↔ F433 3 1 2 ∉ Subgroup.zpowers (F433 2 1 3) := by
  rw [Ne, c312, ← MonoidHom.mem_ker, ker_π_eq_zpowers]

end R433

abbrev B433 : Type := U433 ⧸ Subgroup.normalClosure {F433 2 1 3, F433 3 1 2}

theorem normalClosure_pair_eq_closure :
    Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433) =
      Subgroup.closure {F433 2 1 3, F433 3 1 2} := by
  have hle : Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433) ≤ Subgroup.center U433 := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact F433_213_mem_center
    · exact F433_312_mem_center
  have : (Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433)).Normal :=
    Subgroup.normal_of_le_center hle
  exact le_antisymm (Subgroup.normalClosure_le_normal Subgroup.subset_closure)
    Subgroup.closure_le_normalClosure

namespace R433

@[expose] noncomputable def toB433 : R433 →* B433 :=
  QuotientGroup.map (Subgroup.normalClosure {F433 2 1 3})
    (Subgroup.normalClosure {F433 2 1 3, F433 3 1 2}) (MonoidHom.id U433) (by
      rw [Subgroup.comap_id]
      exact Subgroup.normalClosure_mono (by intro x hx; exact Or.inl hx))

theorem toB433_π (u : U433) : toB433 (π u) = (u : B433) := QuotientGroup.map_mk _ _ _ _ u

theorem toB433_surjective : Function.Surjective toB433 := by
  intro b
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨π u, toB433_π u⟩

theorem map_normalClosure_pair :
    (Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433)).map π =
      Subgroup.zpowers c312 := by
  rw [normalClosure_pair_eq_closure, MonoidHom.map_closure, Set.image_pair, π_F433_213]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers c312
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (Or.inr rfl))

theorem ker_toB433 :
    toB433.ker = Subgroup.zpowers c312 := by
  rw [toB433, QuotientGroup.ker_map, Subgroup.comap_id]
  exact map_normalClosure_pair

theorem toB433_exact :
    Subgroup.zpowers c312 ≤ Subgroup.center R433 ∧ Function.Surjective toB433 ∧
      toB433.ker = Subgroup.zpowers c312 :=
  ⟨Subgroup.zpowers_le.2 c312_mem_center, toB433_surjective, ker_toB433⟩

end R433

@[expose] def Q343N : ℕ := 2 ^ 42 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

theorem Q343N_even : 2 ∣ Q343N := by
  unfold Q343N
  norm_num

namespace R433

theorem card_eq_mul :

    Nat.card R433 = Nat.card (Subgroup.zpowers c312) * Nat.card B433 := by
  have h := toB433.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ toB433_surjective,
    Subgroup.card_top, ker_toB433] at h
  exact h.symm

theorem card_zpowers_c312_pos :
    0 < Nat.card (Subgroup.zpowers c312) := by
  rw [Nat.card_zpowers]
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, c312_pow_two⟩)

theorem card_zpowers_c312_le :
    Nat.card (Subgroup.zpowers c312) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one c312_pow_two)

theorem card_zpowers_c312_eq_two
    (hc : c312 ≠ 1) : Nat.card (Subgroup.zpowers c312) = 2 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime c312_pow_two hc

theorem finite_iff :
    Finite R433 ↔ Finite B433 := by
  refine ⟨fun h => Finite.of_surjective _ toB433_surjective, fun h => ?_⟩
  have hB : 0 < Nat.card B433 := Nat.card_pos
  exact Nat.finite_of_card_ne_zero (by
    rw [card_eq_mul]
    exact (Nat.mul_pos card_zpowers_c312_pos hB).ne')

theorem card_eq_two_mul
    (hc : c312 ≠ 1) : Nat.card R433 = 2 * Nat.card B433 := by
  rw [card_eq_mul, card_zpowers_c312_eq_two hc]

end R433

theorem Q343_bound_of_B433_le
    {M : ℕ} (h : Finite B433 ∧ Nat.card B433 ≤ M) :
    Finite Q343 ∧ Nat.card Q343 ≤ 2 * M := by
  obtain ⟨hfin, hle⟩ := h
  have hRfin : Finite R433 := R433.finite_iff.2 hfin
  refine ⟨Finite.of_equiv _ Q343EquivR433.symm.toEquiv, ?_⟩
  rw [Nat.card_congr Q343EquivR433.toEquiv, R433.card_eq_mul]
  exact Nat.mul_le_mul R433.card_zpowers_c312_le hle

theorem B433_bound_of_Q343_le
    {M : ℕ} (hc : R433.c312 ≠ 1)
    (h : Finite Q343 ∧ Nat.card Q343 ≤ 2 * M) : Finite B433 ∧ Nat.card B433 ≤ M := by
  obtain ⟨hfin, hle⟩ := h
  have hRfin : Finite R433 := Finite.of_equiv _ Q343EquivR433.toEquiv
  refine ⟨R433.finite_iff.1 hRfin, ?_⟩
  have h1 := R433.card_eq_two_mul hc
  have h2 : Nat.card R433 = Nat.card Q343 := (Nat.card_congr Q343EquivR433.toEquiv).symm
  omega

theorem Q343_bound_of_B433
    (h : Finite B433 ∧ Nat.card B433 ≤ Q343N / 2) :
    Finite Q343 ∧ Nat.card Q343 ≤ Q343N := by
  have := Q343_bound_of_B433_le h
  rwa [Nat.mul_div_cancel' Q343N_even] at this

theorem B433_bound_of_Q343
    (hc : R433.c312 ≠ 1) (h : Finite Q343 ∧ Nat.card Q343 ≤ Q343N) :
    Finite B433 ∧ Nat.card B433 ≤ Q343N / 2 := by
  refine B433_bound_of_Q343_le hc ?_
  rwa [Nat.mul_div_cancel' Q343N_even]

theorem Q343_bound_iff_B433
    (hc : R433.c312 ≠ 1) :
    (Finite Q343 ∧ Nat.card Q343 ≤ Q343N) ↔ (Finite B433 ∧ Nat.card B433 ≤ Q343N / 2) :=
  ⟨B433_bound_of_Q343 hc, Q343_bound_of_B433⟩

theorem Q343_card_eq_two_mul_B433
    (hc : R433.c312 ≠ 1) : Nat.card Q343 = 2 * Nat.card B433 :=
  (Nat.card_congr Q343EquivR433.toEquiv).trans (R433.card_eq_two_mul hc)

namespace R433

theorem orderOf_c312
    (hc : c312 ≠ 1) : orderOf c312 = 2 := by
  rw [← Nat.card_zpowers]
  exact card_zpowers_c312_eq_two hc

end R433

theorem zpowers_F433_213_le_pair :
    Subgroup.zpowers (F433 2 1 3) ≤ Subgroup.closure {F433 2 1 3, F433 3 1 2} :=
  Subgroup.zpowers_le.2 (Subgroup.subset_closure (Or.inl rfl))

theorem F433_312_mem_pair :
    F433 3 1 2 ∈ Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433) :=
  Subgroup.subset_closure (Or.inr rfl)

theorem card_pair :
    Nat.card (Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433)) =
      Nat.card (Subgroup.zpowers (F433 2 1 3)) * Nat.card (Subgroup.zpowers R433.c312) := by
  set W := Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433) with hW
  let φ : W →* R433 := R433.π.comp W.subtype
  have hrange : φ.range = Subgroup.zpowers R433.c312 := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨w, hw⟩, rfl⟩
      have h : R433.π w ∈
          (Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433)).map R433.π :=
        ⟨w, by rw [normalClosure_pair_eq_closure]; exact hw, rfl⟩
      rw [R433.map_normalClosure_pair] at h
      exact h
    · exact Subgroup.zpowers_le.2 ⟨⟨F433 3 1 2, F433_312_mem_pair⟩, rfl⟩
  have hker : φ.ker = (Subgroup.zpowers (F433 2 1 3)).subgroupOf W := by
    ext ⟨w, hw⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← ker_π_eq_zpowers, MonoidHom.mem_ker]
    rfl
  have h := φ.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, hker] at h
  rw [← h]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe zpowers_F433_213_le_pair).toEquiv

theorem card_pair_eq_four
    (hc : R433.c312 ≠ 1) :
    Nat.card (Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433)) = 4 := by
  rw [card_pair, Nat.card_zpowers, orderOf_F433_213, R433.card_zpowers_c312_eq_two hc]

theorem card_pair_eq_four_iff :
    Nat.card (Subgroup.closure ({F433 2 1 3, F433 3 1 2} : Set U433)) = 4 ↔ R433.c312 ≠ 1 := by
  refine ⟨fun h hc1 => ?_, card_pair_eq_four⟩
  rw [card_pair, Nat.card_zpowers, orderOf_F433_213, hc1, Subgroup.zpowers_one_eq_bot,
    Subgroup.card_bot] at h
  omega

end CFSG.YGroups
