module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7Fix
public import CFSG.Quasithin.Background.G11Bridge

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11

namespace Case34A7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero_of_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

theorem card_eq_range_mul_ker_add {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

theorem false_alt [Finite V] {g : GLV V} (hord : orderOf g = 7) (hV : Nat.card V = 16)
    (a : V →+ V →+ ZMod 2) (halt : ∀ v, a v v = 0) (hinv : ∀ v w, a (g v) (g w) = a v w)
    (hnd : ∀ v, (∀ w, a v w = 0) → v = 0) : False := by
  obtain ⟨u, hu0, hgu, -⟩ := exists_fixed_probe hord hV
  let φ : V →+ V := AddMonoidHom.mk' (fun x => g x - x) (fun x y => by
    rw [map_add]; abel)
  have hker : φ.ker = fixedAddSubgroup g := by
    ext x
    simp [φ, AddMonoidHom.mem_ker, fixedAddSubgroup, sub_eq_zero]
  have hkerc : Nat.card φ.ker = 2 := by
    rw [hker]
    exact card_fixed_eq_two hord hV
  have hr : Nat.card φ.range = 8 := by
    have := card_eq_range_mul_ker_add φ
    rw [hV, hkerc] at this
    omega
  let ψ : V →+ ZMod 2 := a u
  have hψφ : φ.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    show a u (g x - x) = 0
    rw [map_sub]
    have : a u (g x) = a u x := by
      have := hinv u x
      rwa [hgu] at this
    exact sub_eq_zero.2 this
  obtain ⟨w0, hw0⟩ : ∃ w, a u w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hnd u h)
  have hrange : Nat.card ψ.range = 2 := by
    have hd : Nat.card ψ.range ∣ Nat.card (ZMod 2) := AddSubgroup.card_addSubgroup_dvd_card _
    rw [Nat.card_zmod] at hd
    have h1 : Nat.card ψ.range ≠ 1 := by
      intro h
      have hb : ψ.range = ⊥ := AddSubgroup.eq_bot_of_card_eq _ h
      have : ψ w0 ∈ ψ.range := ⟨w0, rfl⟩
      rw [hb, AddSubgroup.mem_bot] at this
      exact hw0 this
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h h1
    · exact h
  have hkerψ : Nat.card ψ.ker = 8 := by
    have h : Nat.card V = Nat.card ψ.range * Nat.card ψ.ker := card_eq_range_mul_ker_add ψ
    rw [hV, hrange] at h
    omega
  have hle : φ.range = ψ.ker := AddSubgroup.eq_of_le_of_card_ge hψφ (by rw [hr, hkerψ])
  have huker : u ∈ ψ.ker := by
    show a u u = 0
    exact halt u
  rw [← hle] at huker
  obtain ⟨x, hx⟩ := huker
  have hx' : g x - x = u := hx
  have hgx : g x = x + u := by rw [← hx']; abel
  have hg2 : g (g x) = x := by
    rw [hgx, map_add, hgu, hgx, add_assoc, add_self_eq_zero_of_zmod2, add_zero]
  have hpow : ∀ n : ℕ, (g ^ (2 * n)) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, LinearEquiv.mul_apply, ih, pow_two,
        LinearEquiv.mul_apply, hg2]
  have hg8 : g ^ (2 * 4) = g := by
    have h7 : g ^ 7 = 1 := hord ▸ pow_orderOf_eq_one g
    calc g ^ (2 * 4) = g * g ^ 7 := by rw [← pow_succ']
      _ = g := by rw [h7, mul_one]
  have : g x = x := by
    have := hpow 4
    rwa [hg8] at this
  rw [this] at hx'
  exact hu0 (by rw [← hx']; simp)

theorem addSubgroup_eq_bot_or_top {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) (S : AddSubgroup V)
    (hS : ∀ k ∈ L, ∀ v ∈ S, k v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let U : Submodule (ZMod 2) V :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c v hv => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simpa using S.zero_mem
        · simpa using hv }
  rcases hL.2.2 U hS bot_le le_top with h | h
  · left
    ext v
    constructor
    · intro hv
      have : v ∈ U := hv
      rw [h, Submodule.mem_bot] at this
      rw [this]
      exact AddSubgroup.zero_mem _
    · intro hv
      rw [AddSubgroup.mem_bot] at hv
      rw [hv]
      exact S.zero_mem
  · right
    ext v
    constructor
    · intro _; trivial
    · intro _
      have : v ∈ U := by rw [h]; trivial
      exact this

theorem exists_alt_of_form [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    (hV : 2 < Nat.card V) (b : V →+ V →+ ZMod 2)
    (hnd : ∀ v, (∀ w, b v w = 0) → v = 0) (hinv : ∀ k ∈ L, ∀ v w, b (k v) (k w) = b v w) :
    ∃ a : V →+ V →+ ZMod 2, (∀ v, a v v = 0) ∧ (∀ k ∈ L, ∀ v w, a (k v) (k w) = a v w) ∧
      (∀ v, (∀ w, a v w = 0) → v = 0) := by
  let s : V →+ V →+ ZMod 2 := b + b.flip
  have hs : ∀ v w, s v w = b v w + b w v := fun v w => rfl
  have hs_inv : ∀ k ∈ L, ∀ v w, s (k v) (k w) = s v w := by
    intro k hk v w
    rw [hs, hs, hinv k hk, hinv k hk]
  have hs_alt : ∀ v, s v v = 0 := by
    intro v
    rw [hs]
    have : ∀ x : ZMod 2, x + x = 0 := by decide
    exact this _
  let R : AddSubgroup V := s.ker
  have hRmem : ∀ v, v ∈ R ↔ ∀ w, s v w = 0 := by
    intro v
    rw [AddMonoidHom.mem_ker, AddMonoidHom.ext_iff]
    rfl
  have hRinv : ∀ k ∈ L, ∀ v ∈ R, k v ∈ R := by
    intro k hk v hv
    rw [hRmem] at hv ⊢
    intro w
    have hv' : s v (k⁻¹ w) = 0 := hv _
    have e : k (k⁻¹ w) = w := k.apply_symm_apply w
    rw [← hs_inv k hk v (k⁻¹ w), e] at hv'
    exact hv'
  rcases addSubgroup_eq_bot_or_top hL R hRinv with h | h
  · refine ⟨s, hs_alt, hs_inv, fun v hv => ?_⟩
    have : v ∈ R := (hRmem v).2 hv
    rw [h, AddSubgroup.mem_bot] at this
    exact this
  · have hsz : ∀ v w, s v w = 0 := by
      intro v w
      have : v ∈ R := by rw [h]; trivial
      exact (hRmem v).1 this w
    let q : V →+ ZMod 2 := AddMonoidHom.mk' (fun v => b v v) (fun v w => by
      have := hsz v w
      rw [hs] at this
      have e : b (v + w) (v + w) = b v v + b v w + (b w v + b w w) := by
        simp only [map_add, AddMonoidHom.add_apply]
        abel
      have e2 : b v v + b v w + (b w v + b w w) = b v v + (b v w + b w v) + b w w := by abel
      rw [e, e2, this, add_zero])
    have hqinv : ∀ k ∈ L, ∀ v, q (k v) = q v := fun k hk v => hinv k hk v v
    have hker : q.ker = ⊤ := by
      rcases addSubgroup_eq_bot_or_top hL q.ker (fun k hk v hv => by
        show q (k v) = 0
        rw [hqinv k hk]
        exact hv) with h0 | h1
      · exfalso
        have hinj : Function.Injective q := (AddMonoidHom.ker_eq_bot_iff q).1 h0
        have := Nat.card_le_card_of_injective q hinj
        rw [Nat.card_zmod] at this
        omega
      · exact h1
    refine ⟨b, fun v => ?_, hinv, hnd⟩
    have : v ∈ q.ker := by rw [hker]; trivial
    exact this

theorem not_selfDual_of_order_seven [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    {g : GLV V} (hgL : g ∈ L) (hg : orderOf g = 7) (hV : Nat.card V = 16) :
    ¬ SelfDual L ⊤ := by
  rintro ⟨B, ⟨hl, -⟩, hinv⟩
  have h1 : ∀ v v' w : V, B ⟨v + v', trivial⟩ ⟨w, trivial⟩ =
      B ⟨v, trivial⟩ ⟨w, trivial⟩ + B ⟨v', trivial⟩ ⟨w, trivial⟩ := by
    intro v v' w
    have : (⟨v + v', trivial⟩ : ↥(⊤ : Submodule (ZMod 2) V)) = ⟨v, trivial⟩ + ⟨v', trivial⟩ := rfl
    rw [this, map_add, LinearMap.add_apply]
  have h2 : ∀ v w w' : V, B ⟨v, trivial⟩ ⟨w + w', trivial⟩ =
      B ⟨v, trivial⟩ ⟨w, trivial⟩ + B ⟨v, trivial⟩ ⟨w', trivial⟩ := by
    intro v w w'
    have : (⟨w + w', trivial⟩ : ↥(⊤ : Submodule (ZMod 2) V)) = ⟨w, trivial⟩ + ⟨w', trivial⟩ := rfl
    rw [this, map_add]
  have h0 : ∀ w : V, B ⟨0, trivial⟩ ⟨w, trivial⟩ = 0 := by
    intro w
    have : (⟨0, trivial⟩ : ↥(⊤ : Submodule (ZMod 2) V)) = 0 := rfl
    rw [this, map_zero, LinearMap.zero_apply]
  have h0' : ∀ v : V, B ⟨v, trivial⟩ ⟨0, trivial⟩ = 0 := by
    intro v
    have : (⟨0, trivial⟩ : ↥(⊤ : Submodule (ZMod 2) V)) = 0 := rfl
    rw [this, map_zero]
  let b : V →+ V →+ ZMod 2 :=
    { toFun := fun v =>
        { toFun := fun w => B ⟨v, trivial⟩ ⟨w, trivial⟩
          map_zero' := h0' v
          map_add' := h2 v }
      map_zero' := by
        ext w
        exact h0 w
      map_add' := fun v v' => by
        ext w
        exact h1 v v' w }
  have hb : ∀ v w, b v w = B ⟨v, trivial⟩ ⟨w, trivial⟩ := fun v w => rfl
  have hnd : ∀ v, (∀ w, b v w = 0) → v = 0 := by
    intro v hv
    have := hl ⟨v, trivial⟩ (fun y => by
      have := hv y.1
      rw [hb] at this
      exact this)
    exact congrArg Subtype.val this
  have hinv' : ∀ k ∈ L, ∀ v w, b (k v) (k w) = b v w := fun k hk v w =>
    hinv k hk ⟨v, trivial⟩ ⟨w, trivial⟩ ⟨k v, trivial⟩ ⟨k w, trivial⟩ rfl rfl
  obtain ⟨a, halt, hainv, hand⟩ := exists_alt_of_form hL (by omega) b hnd hinv'
  exact false_alt hg hV a halt (fun v w => hainv g hgL v w) hand

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
