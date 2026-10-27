module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS11
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem subgroupOf_pCoreOf (L : Subgroup G) : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L :=
  CFSG.openPCoreOf_subgroupOf 2 L

theorem mem_pCoreOf_of_alpha {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 5)}
    (hαk : α.ker = CFSG.pCore 2 ↥L) {x : G} (hxL : x ∈ L) (hx : α ⟨x, hxL⟩ = 1) :
    x ∈ pCoreOf 2 L := by
  have h1 : (⟨x, hxL⟩ : ↥L) ∈ (pCoreOf 2 L).subgroupOf L := by
    rw [subgroupOf_pCoreOf, ← hαk]
    exact hx
  exact Subgroup.mem_subgroupOf.mp h1

variable [Finite G]

theorem alpha_ne_one_of_three {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 5)}
    (hαk : α.ker = CFSG.pCore 2 ↥L) {q : G} (hqL : q ∈ L) (hq3 : orderOf q = 3) :
    α ⟨q, hqL⟩ ≠ 1 := fun h =>
  orderOf_ne_three_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    (mem_pCoreOf_of_alpha hαk hqL h) hq3

omit [Finite G] in
theorem relIndex_pCoreOf_eq_four {L S : Subgroup G} {α : ↥L →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) (hS : IsSylowTwoOf S L)
    (hOS : pCoreOf 2 L ≤ S) : (pCoreOf 2 L).relIndex S = 4 := by
  have hker : (pCoreOf 2 L).subgroupOf L = α.ker := by
    rw [hαk, subgroupOf_pCoreOf]
  have h2 := Subgroup.relIndex_map_map α ⊥ (S.subgroupOf L)
  rw [Subgroup.map_bot, Subgroup.relIndex_bot_left, bot_sup_eq, ← hker,
    sup_eq_left.mpr (Subgroup.subgroupOf_mono _ hOS),
    Subgroup.relIndex_subgroupOf hS.1] at h2
  rw [← h2]
  exact card_of_isSylowTwoOf (SecB.isSylowTwoOf_map_of_surjective hS α hαs)

theorem inf_centralizer_le_pCoreOf {L S : Subgroup G} {α : ↥L →* alternatingGroup (Fin 5)}
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hS2 : IsPGroup 2 S) (hSL : S ≤ L) {q : G} (hqL : q ∈ L)
    (hq3 : orderOf q = 3) : S ⊓ Subgroup.centralizer ({q} : Set G) ≤ pCoreOf 2 L := by
  rintro x ⟨hxS, hxC⟩
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  obtain ⟨k, hk⟩ := hS2 ⟨x, hxS⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hαx : (α ⟨x, hSL hxS⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x, hSL hxS⟩ : ↥L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, map_one]
  have hαq : (α ⟨q, hqL⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨q, hqL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hq3')
    rw [this, map_one]
  have hcomm : α ⟨x, hSL hxS⟩ * α ⟨q, hqL⟩ = α ⟨q, hqL⟩ * α ⟨x, hSL hxS⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have h1 := eq_one_of_commute_three (mul_self_eq_one_of_two_elt hαx) hαq
    (alpha_ne_one_of_three hαk hqL hq3) hcomm
  exact mem_pCoreOf_of_alpha hαk (hSL hxS) h1

theorem card_centralizer_modEq {V : Subgroup G} {q : G} (hq : q ^ 3 = 1)
    (hqV : q ∈ Subgroup.normalizer (V : Set G)) :
    Nat.card ((Subgroup.centralizer ({q} : Set G)).subgroupOf V) ≡ Nat.card V [MOD 3] := by
  classical
  have hmem : ∀ v : ↥V, q * (v : G) * q⁻¹ ∈ V := fun v =>
    (Subgroup.mem_normalizer_iff.mp hqV v).mp v.2
  let f : ↥V → ↥V := fun v => ⟨q * v * q⁻¹, hmem v⟩
  have hq3 : q * (q * q) = 1 := (pow_three q).symm.trans hq
  have hf3 : ∀ v, f (f (f v)) = v := fun v => Subtype.ext (by
    show q * (q * (q * (v : G) * q⁻¹) * q⁻¹) * q⁻¹ = v
    have e : q * (q * (q * (v : G) * q⁻¹) * q⁻¹) * q⁻¹ = q * (q * q) * v * (q * (q * q))⁻¹ := by
      group
    rw [e, hq3]
    group)
  let σ : Equiv.Perm ↥V := ⟨f, fun v => f (f v), fun v => hf3 v, fun v => hf3 v⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun v => ?_
    rw [pow_one, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hf3 v
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥V := Fintype.ofFinite _
  have h1 := Equiv.Perm.card_compl_support_modEq hσ
  have hfix : ∀ v : ↥V, v ∈ σ.supportᶜ ↔
      v ∈ (Subgroup.centralizer ({q} : Set G)).subgroupOf V := by
    intro v
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : q * (v : G) * q⁻¹ = v := congrArg Subtype.val h
      calc (v : G) * q = q * v * q⁻¹ * q := by rw [h']
        _ = q * v := by group
    · intro h
      apply Subtype.ext
      show q * (v : G) * q⁻¹ = v
      rw [← h]
      group
  have h2 : σ.supportᶜ.card =
      Nat.card ((Subgroup.centralizer ({q} : Set G)).subgroupOf V) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hfix)
  rw [← h2, Nat.card_eq_fintype_card]
  exact h1

theorem four_le_relIndex_of_card {V : Subgroup G} (hV : Nat.card V = 16) {q : G} (hq : q ^ 3 = 1)
    (hqV : q ∈ Subgroup.normalizer (V : Set G))
    (hnot : ¬ V ≤ Subgroup.centralizer ({q} : Set G)) :
    4 ≤ (Subgroup.centralizer ({q} : Set G)).relIndex V := by
  have h1 := card_centralizer_modEq hq hqV
  have h2 := ((Subgroup.centralizer ({q} : Set G)).subgroupOf V).card_mul_index
  rw [hV] at h1 h2
  have h3 : (Subgroup.centralizer ({q} : Set G)).relIndex V ≠ 1 := fun h =>
    hnot (Subgroup.relIndex_eq_one.mp h)
  unfold Subgroup.relIndex at h3 ⊢
  set c := Nat.card ((Subgroup.centralizer ({q} : Set G)).subgroupOf V)
  set i := ((Subgroup.centralizer ({q} : Set G)).subgroupOf V).index
  unfold Nat.ModEq at h1
  have hc : c ≤ 16 := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · rw [hi, mul_zero] at h2; omega
    · nlinarith
  interval_cases c <;> omega

omit [Finite G] in
@[expose] def trivOn (Y N : Subgroup G) : Subgroup G where
  carrier := {l | l ∈ Subgroup.normalizer (Y : Set G) ∧ l ∈ Subgroup.normalizer (N : Set G) ∧
    ∀ y ∈ Y, l * y * l⁻¹ * y⁻¹ ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun y _ => by simp [N.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haY, haN, ha⟩ ⟨hbY, hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haY hbY, Subgroup.mul_mem _ haN hbN, fun y hy => ?_⟩
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb y hy)) (ha y hy)
  inv_mem' := by
    rintro a ⟨haY, haN, ha⟩
    refine ⟨Subgroup.inv_mem _ haY, Subgroup.inv_mem _ haN, fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haY) y).mp hy
      simpa using this
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by group
    rw [e]
    exact N.inv_mem (ha _ hy')

omit [Finite G] in
theorem le_normalizer_trivOn {X Y N : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    X ≤ Subgroup.normalizer (trivOn Y N : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (Y : Set G) → g ∈ Subgroup.normalizer (N : Set G) →
      ∀ l ∈ trivOn Y N, g * l * g⁻¹ ∈ trivOn Y N := by
    rintro g hgY hgN l ⟨hlY, hlN, hl⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgY hlY) (Subgroup.inv_mem _ hgY),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgY) y).mp hy
      simpa using this
    have e : g * l * g⁻¹ * y * (g * l * g⁻¹)⁻¹ * y⁻¹ =
        g * (l * (g⁻¹ * y * g) * l⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp (hl _ hy')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨key g (hXY hg) (hXN hg) l, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ (hXY hg)) (Subgroup.inv_mem _ (hXN hg)) _ h
  simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
