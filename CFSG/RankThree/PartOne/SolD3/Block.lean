module

public import CFSG.CGT.PushingUpLit.SolK.ThreeBlock
public import CFSG.CGT.PushingUpLit.SolK.Basics

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK
open scoped commutatorElement

variable {G : Type} [Group G]

structure Blk3 (X : Subgroup G) (a : G) : Prop where
  mem : a ∈ X
  cube : a ^ 3 = 1
  dec : ∀ x ∈ X, ∃ y ∈ pCoreOf 2 X, ∃ j : ℕ, x = y * a ^ j
  comm : ∀ y ∈ pCoreOf 2 X, ∀ y' ∈ pCoreOf 2 X, y * y' = y' * y
  sq : ∀ y ∈ pCoreOf 2 X, y * y = 1
  card : Nat.card ↥(pCoreOf 2 X) = 4
  fix : ∀ y ∈ pCoreOf 2 X, a * y * a⁻¹ = y → y = 1

theorem exists_blk3 [Finite G] {X : Subgroup G} (hX : IsShortGroup ↥X)
    (hnat : IsNaturalAltModule ↥X 1) : ∃ a, Blk3 X a := by
  obtain ⟨a, haX, ha3, hdec, hab, hsq, hcard, hfix⟩ := three_block_ambient hX hnat
  exact ⟨a, ⟨haX, ha3, hdec, hab, hsq, hcard, hfix⟩⟩

namespace Blk3

variable {X : Subgroup G} {a : G} (h : Blk3 X a)
include h

theorem conj_mem {w : G} (hw : w ∈ pCoreOf 2 X) : a * w * a⁻¹ ∈ pCoreOf 2 X :=
  pCoreOf_normalized X h.mem hw

theorem conj_mem' {w : G} (hw : w ∈ pCoreOf 2 X) : a⁻¹ * w * a ∈ pCoreOf 2 X := by
  have := pCoreOf_normalized X (X.inv_mem h.mem) hw
  simpa using this

theorem exists_ne_one : ∃ w ∈ pCoreOf 2 X, w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : pCoreOf 2 X = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
  have hc := h.card
  rw [hbot, Subgroup.card_bot] at hc
  omega

theorem W_ne_bot : pCoreOf 2 X ≠ ⊥ := by
  obtain ⟨w, hw, hw1⟩ := h.exists_ne_one
  intro hbot
  rw [hbot] at hw
  exact hw1 (Subgroup.mem_bot.1 hw)

theorem isPGroup_W : IsPGroup 2 ↥(pCoreOf 2 X) := by
  intro w
  refine ⟨1, Subtype.ext ?_⟩
  have := h.sq w w.2
  simpa [pow_two] using this

theorem conj_cube (w : G) : a * (a * (a * w * a⁻¹) * a⁻¹) * a⁻¹ = w := by
  have h3 : a * a * a = 1 := by
    have := h.cube
    simpa [pow_succ] using this
  have e : a * (a * (a * w * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * w * (a * a * a)⁻¹ := by group
  rw [e, h3]
  group

theorem norm_eq_one {w : G} (hw : w ∈ pCoreOf 2 X) :
    w * (a * w * a⁻¹) * (a * (a * w * a⁻¹) * a⁻¹) = 1 := by
  have hw₁ : a * w * a⁻¹ ∈ pCoreOf 2 X := h.conj_mem hw
  have hw₂ : a * (a * w * a⁻¹) * a⁻¹ ∈ pCoreOf 2 X := h.conj_mem hw₁
  have hN : w * (a * w * a⁻¹) * (a * (a * w * a⁻¹) * a⁻¹) ∈ pCoreOf 2 X :=
    (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).mul_mem hw hw₁) hw₂
  refine h.fix _ hN ?_
  have e : a * (w * (a * w * a⁻¹) * (a * (a * w * a⁻¹) * a⁻¹)) * a⁻¹ =
      (a * w * a⁻¹) * (a * (a * w * a⁻¹) * a⁻¹) *
        (a * (a * (a * w * a⁻¹) * a⁻¹) * a⁻¹) := by group
  rw [e, h.conj_cube]
  have c1 := h.comm _ hw _ hw₁
  have c2 := h.comm _ hw _ hw₂
  have c3 := h.comm _ hw₁ _ hw₂
  calc (a * w * a⁻¹) * (a * (a * w * a⁻¹) * a⁻¹) * w
      = (a * w * a⁻¹) * ((a * (a * w * a⁻¹) * a⁻¹) * w) := by group
    _ = (a * w * a⁻¹) * (w * (a * (a * w * a⁻¹) * a⁻¹)) := by rw [c2.symm]
    _ = ((a * w * a⁻¹) * w) * (a * (a * w * a⁻¹) * a⁻¹) := by group
    _ = (w * (a * w * a⁻¹)) * (a * (a * w * a⁻¹) * a⁻¹) := by rw [c1.symm]

end Blk3

abbrev Wn (X : Subgroup G) : Type := {w : G // w ∈ pCoreOf 2 X ∧ w ≠ 1}

theorem card_Wn [Finite G] {X : Subgroup G} {a : G} (h : Blk3 X a) : Nat.card (Wn X) = 3 := by
  classical
  have h4 := h.card
  let e : Wn X ≃ {w : ↥(pCoreOf 2 X) // w ≠ 1} :=
    { toFun := fun w => ⟨⟨w.1, w.2.1⟩, fun h1 => w.2.2 (congrArg Subtype.val h1)⟩
      invFun := fun w => ⟨(w.1 : G), w.1.2, fun h1 => w.2 (Subtype.ext h1)⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }
  rw [Nat.card_congr e]
  have : Fintype ↥(pCoreOf 2 X) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h4 ⊢
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at *
  omega

def wnPerm (X : Subgroup G) (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ w ∈ pCoreOf 2 X, h * w * h⁻¹ ∈ pCoreOf 2 X) :
    ↥H →* Equiv.Perm (Wn X) where
  toFun g :=
    { toFun := fun w => ⟨(g : G) * w.1 * (g : G)⁻¹, hH g g.2 w.1 w.2.1, fun h1 => w.2.2 (by
        calc w.1 = (g : G)⁻¹ * ((g : G) * w.1 * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h1]; group)⟩
      invFun := fun w => ⟨(g : G)⁻¹ * w.1 * (g : G), by
        have := hH (g⁻¹ : ↥H) (g⁻¹ : ↥H).2 w.1 w.2.1
        simpa using this, fun h1 => w.2.2 (by
        calc w.1 = (g : G) * ((g : G)⁻¹ * w.1 * (g : G)) * (g : G)⁻¹ := by group
          _ = 1 := by rw [h1]; group)⟩
      left_inv := fun w => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    refine Equiv.ext fun w => Subtype.ext ?_
    simp
  map_mul' g₁ g₂ := by
    refine Equiv.ext fun w => Subtype.ext ?_
    simp [mul_assoc]

theorem wnPerm_eq_one_iff (X : Subgroup G) (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ w ∈ pCoreOf 2 X, h * w * h⁻¹ ∈ pCoreOf 2 X) (g : ↥H) :
    wnPerm X H hH g = 1 ↔ ∀ w ∈ pCoreOf 2 X, (g : G) * w * (g : G)⁻¹ = w := by
  constructor
  · intro h1 w hw
    by_cases hw1 : w = 1
    · subst hw1
      group
    · have := congrArg (fun p : Equiv.Perm (Wn X) => (p ⟨w, hw, hw1⟩ : G)) h1
      simpa [wnPerm] using this
  · intro h1
    refine Equiv.ext fun w => Subtype.ext ?_
    simpa [wnPerm] using h1 w.1 w.2.1

theorem perm3_comm_trivial {α : Type} [Finite α] (hα : Nat.card α = 3) (ρ σ : Equiv.Perm α)
    (hρ : ∀ x, ρ x ≠ x) (hc : σ * ρ = ρ * σ) (hσ : σ * σ = 1) : σ = 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hc3 : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact hα
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hc3
  let φ := e.permCongrHom
  have key : ∀ ρ' σ' : Equiv.Perm (Fin 3), (∀ x, ρ' x ≠ x) → σ' * ρ' = ρ' * σ' →
      σ' * σ' = 1 → σ' = 1 := by decide
  have h1 : φ σ = 1 := by
    refine key (φ ρ) (φ σ) ?_ ?_ ?_
    · intro x hx
      apply hρ (e.symm x)
      have : e (ρ (e.symm x)) = x := hx
      exact e.injective (by simpa using this)
    · rw [← map_mul, ← map_mul, hc]
    · rw [← map_mul, hσ, map_one]
  exact φ.injective (by rw [h1, map_one])

theorem perm3_involution_fixed {α : Type} [Finite α] (hα : Nat.card α = 3) (σ : Equiv.Perm α)
    (h1 : σ ≠ 1) (h2 : σ * σ = 1) : ∃ x, σ x = x ∧ ∀ y, σ y = y → y = x := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hc3 : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact hα
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hc3
  let φ := e.permCongrHom
  have key : ∀ σ' : Equiv.Perm (Fin 3), σ' ≠ 1 → σ' * σ' = 1 →
      ∃ x, σ' x = x ∧ ∀ y, σ' y = y → y = x := by decide
  obtain ⟨x, hx, hy⟩ := key (φ σ) (fun h => h1 (φ.injective (by rw [h, map_one])))
    (by rw [← map_mul, h2, map_one])
  refine ⟨e.symm x, ?_, fun y hy' => ?_⟩
  · have : e (σ (e.symm x)) = x := hx
    apply e.injective
    simpa using this
  · have := hy (e y) (by
      show e (σ (e.symm (e y))) = e y
      rw [Equiv.symm_apply_apply, hy'])
    rw [← this]
    simp

theorem perm3_two_subgroup_card {α : Type} [Finite α] (hα : Nat.card α = 3)
    (P : Subgroup (Equiv.Perm α)) (hP : IsPGroup 2 ↥P) : Nat.card ↥P ≤ 2 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hc3 : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact hα
  have hcard : Nat.card (Equiv.Perm α) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hc3]
    rfl
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hP)
  have hdvd : Nat.card ↥P ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card P
  rw [hn] at hdvd ⊢
  by_contra hlt
  have h2 : 2 ≤ n := by
    by_contra hn2
    have : n ≤ 1 := by omega
    interval_cases n <;> simp at hlt
  have h4 : 4 ∣ 2 ^ n := by
    have := pow_dvd_pow 2 h2
    simpa using this
  have := h4.trans hdvd
  omega

theorem perm3_sq_of_two_power {α : Type} [Finite α] (hα : Nat.card α = 3) (σ : Equiv.Perm α)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1) : σ * σ = 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hc3 : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact hα
  have hcard : Nat.card (Equiv.Perm α) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hc3]
    rfl
  obtain ⟨k, hk⟩ := hσ
  have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf σ ∣ 6 := hcard ▸ orderOf_dvd_natCard σ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hj] at h2
  have hj1 : j ≤ 1 := by
    by_contra hlt
    have h2j : 2 ≤ j := by omega
    have h4 : 4 ∣ 2 ^ j := by
      have := pow_dvd_pow 2 h2j
      simpa using this
    have := h4.trans h2
    omega
  have : σ ^ 2 = 1 := by
    have h3 : orderOf σ ∣ 2 := by
      rw [hj]
      calc 2 ^ j ∣ 2 ^ 1 := pow_dvd_pow 2 hj1
        _ = 2 := by norm_num
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  simpa [pow_two] using this

section Action

variable [Finite G] {X : Subgroup G} {a : G}

theorem card_le_two_mul_card_centralizer (hb : Blk3 X a) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X) :
    Nat.card ↥S ≤ 2 * Nat.card ↥(Subgroup.centralizer (pCoreOf 2 X : Set G) ⊓ S : Subgroup G) := by
  classical
  let φ := wnPerm X S hSn
  have hcard3 : Nat.card (Wn X) = 3 := card_Wn hb
  have hrange : IsPGroup 2 ↥φ.range := by
    have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
    exact hS.of_surjective φ.rangeRestrict hsurj
  have hr2 : Nat.card ↥φ.range ≤ 2 := perm3_two_subgroup_card hcard3 φ.range hrange
  have hker : Nat.card ↥φ.ker =
      Nat.card ↥(Subgroup.centralizer (pCoreOf 2 X : Set G) ⊓ S : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨(g.1 : G), Subgroup.mem_inf.2 ⟨?_, g.1.2⟩⟩
        invFun := fun g => ⟨⟨(g : G), (Subgroup.mem_inf.1 g.2).2⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := (wnPerm_eq_one_iff X S hSn g.1).1 g.2 w hw
      calc w * (g.1 : G) = ((g.1 : G) * w * (g.1 : G)⁻¹) * (g.1 : G) := by rw [this]
        _ = (g.1 : G) * w := by group
    · rw [MonoidHom.mem_ker, wnPerm_eq_one_iff]
      intro w hw
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 g.2).1 w hw
      calc (g : G) * w * (g : G)⁻¹ = (w * (g : G)) * (g : G)⁻¹ := by rw [this]
        _ = w := by group
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hquot : Nat.card (↥S ⧸ φ.ker) = Nat.card ↥φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [hsplit, hquot, hker]
  exact Nat.mul_le_mul_right _ hr2

theorem exists_fixed_of_not_centralizes (hb : Blk3 X a) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X) {s : G} (hs : s ∈ S)
    (hns : ¬ ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ = w) :
    ∃ c ∈ pCoreOf 2 X, c ≠ 1 ∧ s * c * s⁻¹ = c ∧
      ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ = w → w = 1 ∨ w = c := by
  classical
  let φ := wnPerm X S hSn
  have hcard3 : Nat.card (Wn X) = 3 := card_Wn hb
  have hne : φ ⟨s, hs⟩ ≠ 1 := fun h => hns ((wnPerm_eq_one_iff X S hSn ⟨s, hs⟩).1 h)
  have hsq : φ ⟨s, hs⟩ * φ ⟨s, hs⟩ = 1 := by
    refine perm3_sq_of_two_power hcard3 _ ?_
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨x, hx, hy⟩ := perm3_involution_fixed hcard3 _ hne hsq
  refine ⟨x.1, x.2.1, x.2.2, ?_, fun w hw hsw => ?_⟩
  · have := congrArg Subtype.val hx
    simpa [φ, wnPerm] using this
  · by_cases hw1 : w = 1
    · exact Or.inl hw1
    · refine Or.inr ?_
      have := hy ⟨w, hw, hw1⟩ (Subtype.ext (by simpa [φ, wnPerm] using hsw))
      exact congrArg Subtype.val this

theorem centralizes_of_commutator (hb : Blk3 X a) {M : Subgroup G}
    (hM : ∀ h ∈ M, ∀ w ∈ pCoreOf 2 X, h * w * h⁻¹ ∈ pCoreOf 2 X) (haM : a ∈ M) {q : G}
    (hqM : q ∈ M) (hq2 : ∃ k : ℕ, q ^ (2 ^ k) = 1) (hqa : q * a * q⁻¹ * a⁻¹ ∈ pCoreOf 2 X) :
    ∀ w ∈ pCoreOf 2 X, q * w * q⁻¹ = w := by
  classical
  let φ := wnPerm X M hM
  have hcard3 : Nat.card (Wn X) = 3 := card_Wn hb
  have hρ : ∀ x, φ ⟨a, haM⟩ x ≠ x := by
    intro x hx
    have h1 : a * x.1 * a⁻¹ = x.1 := by
      have := congrArg Subtype.val hx
      simpa [φ, wnPerm] using this
    exact x.2.2 (hb.fix x.1 x.2.1 h1)
  have hc : φ ⟨q, hqM⟩ * φ ⟨a, haM⟩ = φ ⟨a, haM⟩ * φ ⟨q, hqM⟩ := by
    refine Equiv.ext fun x => Subtype.ext ?_
    have hx := x.2.1
    have hxq : q * x.1 * q⁻¹ ∈ pCoreOf 2 X := hM q hqM x.1 hx
    have hxa : a * x.1 * a⁻¹ ∈ pCoreOf 2 X := hb.conj_mem hx
    have hcc := hb.comm _ hqa _ (hb.conj_mem hxq)
    have e : q * (a * x.1 * a⁻¹) * q⁻¹ =
        (q * a * q⁻¹ * a⁻¹) * (a * (q * x.1 * q⁻¹) * a⁻¹) * (q * a * q⁻¹ * a⁻¹)⁻¹ := by
      group
    show q * (a * x.1 * a⁻¹) * q⁻¹ = a * (q * x.1 * q⁻¹) * a⁻¹
    rw [e, hcc]
    group
  have hsq : φ ⟨q, hqM⟩ * φ ⟨q, hqM⟩ = 1 := by
    refine perm3_sq_of_two_power hcard3 _ ?_
    obtain ⟨k, hk⟩ := hq2
    exact ⟨k, by
      rw [← map_pow]
      have : (⟨q, hqM⟩ : ↥M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]⟩
  have h1 := perm3_comm_trivial hcard3 (φ ⟨a, haM⟩) (φ ⟨q, hqM⟩) hρ hc hsq
  exact (wnPerm_eq_one_iff X M hM ⟨q, hqM⟩).1 h1

end Action

end CFSG.RankThree.PartOne.SolD3
