module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec711CentralProduct
public import CFSG.RankThree.GF2n.Stroth80.Sec711Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def n12X {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B)
    (t : G) : Set G :=
  {x | x ∈ QB B ⊓ M ∧ x ∈ hc.CN t}

@[expose] def n12Y {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B)
    (t r : G) : Set G :=
  {y | y ∈ QB (conjSubgroup r B) ⊓ M ∧ y ∈ hc.CN t}

@[expose] def N12Lemma2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    (∀ a ∈ Vt M (LB M Q B) B Z t, ∀ b ∈ Vt M (LB M Q B) B Z t, ⁅a, b⁆ = 1) ∧
    ∀ lam : ↥Z →* Multiplicative (ZMod 2), lam ≠ 1 →
      ∀ a ∈ Q, a ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔
        ∀ v ∈ Vt M (LB M Q B) B Z t, LamOrth Z lam a v

@[expose] def N12Lemma3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t r : G),
    Sec7Hyp hc n t → Sec7A hc t r →
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ a ∈ Q, g * a * g⁻¹ ∈ Q) ∧
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ z ∈ Z, g * z * g⁻¹ = z) ∧
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ a ∈ Q, ⁅g, a⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ a ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅g, a⁆ ∈ Vt M (LB M Q B) B Z t) ∧
    (∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∀ b ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, b⁆ = 1) ∧
    (∀ a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∀ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, b⁆ = 1) ∧
    Wt Q (Vt M (LB M Q B) B Z t) = QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ⊔
      QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ⊔ Vt M (LB M Q B) B Z t

@[expose] def N12Lemma4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t r : G),
    Sec7Hyp hc n t → Sec7A hc t r →
    Z ≤ QB (conjSubgroup r B) ∧
    (∀ x ∈ n12X hc t, ∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, a⁆ ∈ B ⊔ Z) ∧
    (∀ x ∈ n12X hc t, ∀ a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅x, a⁆ ∈ Q ⊓ QB (conjSubgroup r B)) ∧
    (∀ y ∈ n12Y hc t r, ∀ a ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅y, a⁆ ∈ Q ⊓ QB (conjSubgroup r B)) ∧
    (B ⊔ Z) ⊓ (Q ⊓ QB (conjSubgroup r B)) = Z

@[expose] def N12Lemma5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t r : G),
    Sec7Hyp hc n t → Sec7A hc t r →
    (∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), (∀ x ∈ n12X hc t, ⁅x, a⁆ ∈ Z) →
      a ∈ Vt M (LB M Q B) B Z t) ∧
    (∀ a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      (∀ y ∈ n12Y hc t r, ⁅y, a⁆ ∈ Z) → a ∈ Vt M (LB M Q B) B Z t)

@[expose] def N12WneVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → Wt Q (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t

theorem n12Q_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B →
      Z ≤ Q ∧ (∀ z ∈ Z, ∀ a ∈ Q, Commute z a) ∧ (∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) ∧
        ∀ a ∈ Q, a ^ 2 ∈ Z := fun _ _ _ M Q Z _ hc =>
  ⟨hc.Z_le_Q, fun _ hz _ ha => hc.hyp.toHyp79.V_central hz ha,
    fun _ ha _ hb => hc.hyp.toHyp79.comm_mem_V ha hb, fun _ ha => hc.hyp.toHyp79.sq_mem_V ha⟩

theorem n12Lemma1_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B →
      ∀ lam : ↥Z →* Multiplicative (ZMod 2), lam ≠ 1 →
      ∀ a ∈ Q, (∀ b ∈ Q, LamOrth Z lam a b) → a ∈ Z := by
  intro G _ _ M Q Z B hc lam hlam a ha h
  obtain ⟨n, k, -, hcp⟩ := hc.hyp.cp
  exact n12_mem_of_lam_comm_trivial hcp lam hlam ha h

theorem exists_char_zmod_two {G : Type} [Group G] {Z : Subgroup G}
    (hc : ∀ x ∈ Z, ∀ y ∈ Z, ⁅x, y⁆ = 1) (hsq : ∀ x ∈ Z, x ^ 2 = 1) {x : G} (hx : x ∈ Z)
    (hx1 : x ≠ 1) : ∃ θ : ↥Z →* Multiplicative (ZMod 2), θ ⟨x, hx⟩ ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsec : SecHyp (⊥ : Subgroup G) Z ⊥ :=
    ⟨bot_le, fun a ha b hb => by simpa using hc a ha b hb, fun a ha => by simpa using hsq a ha,
      fun r hr a ha => by rw [Subgroup.mem_bot] at hr; simpa [hr] using ha,
      fun r hr a ha => by rw [Subgroup.mem_bot] at hr; simpa [hr] using ha⟩
  obtain ⟨M, iM, iA, κ, hκ⟩ := exists_sectionModule hsec
  letI : Module (ZMod 2) M := AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]; exact hκ.two a)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) M,
      φ (Multiplicative.toAdd (κ ⟨x, hx⟩)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 hcon
    exact hx1 (by
      have h1 : κ ⟨x, hx⟩ = 1 := by rw [← ofAdd_toAdd (κ ⟨x, hx⟩), h0]; rfl
      have := (hκ.ker ⟨x, hx⟩).1 h1
      simpa using this)
  refine ⟨(AddMonoidHom.toMultiplicative (φ : M →ₗ[ZMod 2] ZMod 2).toAddMonoidHom).comp κ, ?_⟩
  intro h
  apply hφ
  simpa using h

theorem n12Lam_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B →
      ∃ lam : ↥Z →* Multiplicative (ZMod 2), lam ≠ 1 := by
  intro G _ _ M Q Z B hc
  have hZ : (1 : ℕ) < Nat.card Z := lt_of_lt_of_le (by norm_num) hc.hyp.q4
  obtain ⟨x, hx⟩ := (Subgroup.one_lt_card_iff_ne_bot Z).1 hZ |> Subgroup.ne_bot_iff_exists_ne_one.1
  obtain ⟨θ, hθ⟩ := exists_char_zmod_two (Z := Z)
    (fun a ha b hb => by
      have := hc.hyp.toHyp79.V_central ha (hc.Z_le_Q hb)
      exact (commutatorElement_eq_one_iff_commute.2 this))
    (fun e he => hc.hyp.toHyp79.sq_eq_one e he) (x := (x : G)) x.2 (fun h => hx (Subtype.ext h))
  exact ⟨θ, fun h => hθ (by rw [h]; rfl)⟩

theorem stroth711Strong_of_n12 (hAex : Sec7AExistsStatement)
    (h2 : N12Lemma2Statement) (h3 : N12Lemma3Statement) (h4 : N12Lemma4Statement)
    (h5 : N12Lemma5Statement) (hN : N12WneVStatement) : Stroth711StrongStatement := by
  have hA := propAGroup_holds
  have h0 := n12Q_holds
  have h1a := n12Lam_holds
  have h1 := n12Lemma1_holds
  intro G _ _ M Q Z B hc n t hs hle
  obtain ⟨r, hr⟩ := hAex G M Q Z B hc n t hs
  obtain ⟨hZQ, hZc, hcomm, hsq⟩ := h0 G M Q Z B hc
  obtain ⟨lam, hlam⟩ := h1a G M Q Z B hc
  obtain ⟨hVab, hW⟩ := h2 G M Q Z B hc n t hs
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := h3 G M Q Z B hc n t r hs hr
  obtain ⟨k0, k1, k2, k3, k4⟩ := h4 G M Q Z B hc n t r hs hr
  obtain ⟨f1, f2⟩ := h5 G M Q Z B hc n t r hs hr
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := le_sup_left
  obtain ⟨x, hx, y, hy, hxy⟩ := hA G Q Z (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))
    (B ⊔ Z) (Q ⊓ QB (conjSubgroup r B)) lam (n12X hc t) (n12Y hc t r)
    hZQ hZc hcomm hsq (h1 G M Q Z B hc lam hlam) hZV (hc.Vt_le_Q t) inf_le_left hVab
    (hW lam hlam) g7 g5 g6 le_sup_right (le_inf hZQ k0) (sup_le hc.le hZQ) inf_le_left k4
    g1 g2 g3 g4 (fun g _ a ha => (Ctx.mem_CN.1 (by rcases ‹g ∈ _› with h | h <;> exact h.2)).2 a ha)
    k1 k2 k3 f1 f2 (hN G M Q Z B hc n t hs)
  exact hxy (hle (Subgroup.commutator_mem_commutator hx.2 hy.2))

end CFSG.RankThree.GF2n.Stroth80
