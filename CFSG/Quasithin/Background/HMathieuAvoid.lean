module

public import CFSG.Quasithin.Background.HMathieuPred

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

structure Msk (n : ℕ) where
  val : ℕ
  lt : val < 2 ^ n
deriving DecidableEq

namespace Msk

variable {n : ℕ}

theorem ext' {a b : Msk n} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance : Mul (Msk n) := ⟨fun a b => ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow a.lt b.lt⟩⟩

instance : One (Msk n) := ⟨⟨0, Nat.two_pow_pos n⟩⟩

instance : Inv (Msk n) := ⟨fun a => a⟩

theorem val_mul (a b : Msk n) : (a * b).val = a.val ^^^ b.val := rfl

theorem val_one : (1 : Msk n).val = 0 := rfl

instance instGroup : Group (Msk n) :=
  Group.ofLeftAxioms (fun _ _ _ => ext' (Nat.xor_assoc _ _ _)) (fun _ => ext' (Nat.zero_xor _))
    (fun _ => ext' (Nat.xor_self _))

theorem mul_comm' (a b : Msk n) : a * b = b * a := ext' (Nat.xor_comm _ _)

theorem mul_self (a : Msk n) : a * a = 1 := ext' (Nat.xor_self _)

instance : Finite (Msk n) :=
  Finite.of_injective (fun a : Msk n => (⟨a.val, a.lt⟩ : Fin (2 ^ n))) fun _ _ h =>
    ext' (congrArg Fin.val h)

end Msk

@[expose] def avoidList (n : ℕ) (O F : List ℕ) : List (Msk n) :=
  (F.filter fun m => m != 0 && !(m ∈ O)).filterMap fun m =>
    if h : m < 2 ^ n then some ⟨m, h⟩ else none

@[expose] def avoidOK (n b : ℕ) (O F : List ℕ) : Bool :=
  forallGreedy (avoidList n O F) (fun l => (subprods l).any fun x => x.val ∈ O) (b + 1) []

theorem mem_avoidList {n : ℕ} {O F : List ℕ} {x : Msk n} (hF : x.val ∈ F) (h0 : x.val ≠ 0)
    (hO : x.val ∉ O) : x ∈ avoidList n O F := by
  rw [avoidList, List.mem_filterMap]
  refine ⟨x.val, ?_, by simp [x.lt]⟩
  rw [List.mem_filter]
  exact ⟨hF, by simp [h0, hO]⟩

variable {V : Type*} [CommGroup V] {n : ℕ}

theorem rk_le_of_avoidOK (c : MaskCoords V n) {X U : Subgroup V} {F O : List ℕ} {Oset : Set V}
    {b : ℕ} (hF : ∀ m < 2 ^ n, c.vm m ∈ X → m ∈ F) (hO : ∀ o ∈ O, c.vm o ∈ Oset)
    (hUX : U ≤ X) (hUO : ∀ v ∈ U, v ∉ Oset) (h : avoidOK n b O F = true) : rk U ≤ b := by
  have := c.finite
  have hV := c.sq_eq_one
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcU := card_eq_two_pow hV U
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := U) (n := b + 1)
    (by rw [hcU]; exact Nat.pow_dvd_pow 2 (by omega))
  set U' := K.map U.subtype with hU'
  have hU'U : U' ≤ U := Subgroup.map_subtype_le K
  have hcU' : Nat.card U' = 2 ^ (b + 1) := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hK]
  let B : Subgroup (Msk n) :=
    { carrier := {m | c.vm m.val ∈ U'}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Msk.val_mul, c.vm_xor] at ha hb ⊢
        exact U'.mul_mem ha hb
      one_mem' := by
        simp only [Set.mem_ofPred_eq, Msk.val_one, c.vm_zero]
        exact U'.one_mem
      inv_mem' := fun {a} ha => ha }
  have hcardB : Nat.card B = 2 ^ (b + 1) := by
    rw [← hcU']
    refine Nat.card_congr (Equiv.ofBijective (fun m : B => (⟨c.vm m.1.val, m.2⟩ : U')) ⟨?_, ?_⟩)
    · intro a a' haa
      have := congrArg Subtype.val haa
      exact Subtype.ext (Msk.ext' (c.vm_inj _ _ a.1.lt a'.1.lt this))
    · intro v
      obtain ⟨m, hm, hmv⟩ := c.vm_surj v
      exact ⟨⟨⟨m, hm⟩, show c.vm m ∈ U' by rw [hmv]; exact v.2⟩, Subtype.ext hmv⟩
  have hR : ∀ x ∈ B, x ≠ 1 → x ∈ avoidList n O F := by
    intro x hx hx1
    have hxU : c.vm x.val ∈ U := hU'U hx
    refine mem_avoidList (hF x.val x.lt (hUX hxU)) (fun h0 => hx1 (Msk.ext' h0)) fun hxO =>
      hUO _ hxU (hO _ hxO)
  obtain ⟨l, -, -, hsub, hpred⟩ := forallGreedy_sound h B (fun x _ y _ => Msk.mul_comm' x y)
    (fun x _ => Msk.mul_self x) hR hcardB
  rw [List.any_eq_true] at hpred
  obtain ⟨x, hx, hxO⟩ := hpred
  have hxB : x ∈ B := (hsub x).2 hx
  exact hUO _ (hU'U hxB) (hO _ (by simpa using hxO))

end CFSG.Quasithin.H.Mathieu
