module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A

open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_or_eq_of_relIndex_two {N K L : Subgroup G} (hNK : N ≤ K) (hKL : K ≤ L)
    (h : N.relIndex L = 2) : K = N ∨ K = L := by
  have hm := Subgroup.relIndex_mul_relIndex N K L hNK hKL
  rw [h] at hm
  rcases (Nat.dvd_prime Nat.prime_two).mp ⟨K.relIndex L, hm.symm⟩ with h1 | h2
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hNK)
  · rw [h2] at hm
    exact Or.inr (le_antisymm hKL (Subgroup.relIndex_eq_one.mp (by omega)))

theorem le_of_relIndex_two {N L U : Subgroup G} (h : N.relIndex L = 2) (hNL : N ≤ L)
    (hNU : N ≤ U) {x : G} (hxL : x ∈ L) (hxU : x ∈ U) (hxN : x ∉ N) : L ≤ U := by
  rcases eq_or_eq_of_relIndex_two (le_inf hNU hNL) inf_le_right h with h1 | h1
  · exact absurd (by rw [← h1]; exact ⟨hxU, hxL⟩) hxN
  · exact h1.symm.le.trans inf_le_left

theorem mul_mem_of_relIndex_two {N K : Subgroup G} (h : N.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (hna : a ∉ N) (hnb : b ∉ N) : a * b ∈ N := by
  have hna' : a⁻¹ ∉ N := fun h' => hna (by simpa using N.inv_mem h')
  simpa using inv_mul_mem_of_relIndex_two h (K.inv_mem ha) hb hna' hnb

open Classical in
@[expose] noncomputable def bit (Z : Subgroup G) (t : G) : ZMod 2 := if t ∈ Z then 0 else 1

theorem bit_eq_zero_iff {Z : Subgroup G} {t : G} : bit Z t = 0 ↔ t ∈ Z := by
  unfold bit
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

theorem bit_of_mem {Z : Subgroup G} {t : G} (h : t ∈ Z) : bit Z t = 0 := bit_eq_zero_iff.mpr h

theorem bit_of_not_mem {Z : Subgroup G} {t : G} (h : t ∉ Z) : bit Z t = 1 := by
  unfold bit
  simp [h]

theorem bit_mul {Z T : Subgroup G} (h2 : Z.relIndex T = 2) {t t' : G} (ht : t ∈ T)
    (ht' : t' ∈ T) : bit Z (t * t') = bit Z t + bit Z t' := by
  by_cases h1 : t ∈ Z <;> by_cases h1' : t' ∈ Z
  · rw [bit_of_mem h1, bit_of_mem h1', bit_of_mem (Z.mul_mem h1 h1')]
    rfl
  · have : t * t' ∉ Z := fun h => h1' (by simpa using Z.mul_mem (Z.inv_mem h1) h)
    rw [bit_of_mem h1, bit_of_not_mem h1', bit_of_not_mem this]
    rfl
  · have : t * t' ∉ Z := fun h => h1 (by simpa using Z.mul_mem h (Z.inv_mem h1'))
    rw [bit_of_not_mem h1, bit_of_mem h1', bit_of_not_mem this]
    rfl
  · rw [bit_of_not_mem h1, bit_of_not_mem h1',
      bit_of_mem (mul_mem_of_relIndex_two h2 ht ht' h1 h1')]
    decide

theorem bit_conj {Z : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G)) (t : G) :
    bit Z (g * t * g⁻¹) = bit Z t := by
  have h : g * t * g⁻¹ ∈ Z ↔ t ∈ Z := (Subgroup.mem_normalizer_iff.mp hg t).symm
  by_cases ht : t ∈ Z
  · rw [bit_of_mem ht, bit_of_mem (h.mpr ht)]
  · rw [bit_of_not_mem ht, bit_of_not_mem (fun h' => ht (h.mp h'))]

theorem comm_mul_left (q q' v : G) : ⁅q * q', v⁆ = q * ⁅q', v⁆ * q⁻¹ * ⁅q, v⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right {q v w : G} (h : Commute ⁅q, w⁆ v) : ⁅q, v * w⁆ = ⁅q, v⁆ * ⁅q, w⁆ := by
  have h' : ⁅q, w⁆ * v⁻¹ = v⁻¹ * ⁅q, w⁆ := h.inv_right.eq
  calc ⁅q, v * w⁆ = q * v * q⁻¹ * (⁅q, w⁆ * v⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = q * v * q⁻¹ * (v⁻¹ * ⁅q, w⁆) := by rw [h']
    _ = ⁅q, v⁆ * ⁅q, w⁆ := by
        simp only [commutatorElement_def]
        group

theorem comm_inv_left (q v : G) : ⁅q⁻¹, v⁆ = q⁻¹ * ⁅q, v⁆⁻¹ * q := by
  simp only [commutatorElement_def]
  group

@[expose] noncomputable def bitHom {Z T P : Subgroup G} (h2 : Z.relIndex T = 2)
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    {e : G} (he : ∀ q ∈ P, ⁅q, e⁆ ∈ T) : ↥P →* Multiplicative (ZMod 2) where
  toFun q := Multiplicative.ofAdd (bit Z ⁅(q : G), e⁆)
  map_one' := by
    have h1 : ⁅((1 : ↥P) : G), e⁆ = 1 := by simp
    rw [h1, bit_of_mem Z.one_mem]
    rfl
  map_mul' q q' := by
    have hm : (q : G) * ⁅(q' : G), e⁆ * (q : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hPT q.2) _).mp (he q' q'.2)
    show Multiplicative.ofAdd (bit Z ⁅(q : G) * q', e⁆) =
      Multiplicative.ofAdd (bit Z ⁅(q : G), e⁆) * Multiplicative.ofAdd (bit Z ⁅(q' : G), e⁆)
    rw [← ofAdd_add, comm_mul_left, bit_mul h2 hm (he q q.2), bit_conj (hPZ q.2), add_comm]

theorem bitHom_apply {Z T P : Subgroup G} (h2 : Z.relIndex T = 2)
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    {e : G} (he : ∀ q ∈ P, ⁅q, e⁆ ∈ T) (q : ↥P) :
    Multiplicative.toAdd (bitHom h2 hPZ hPT he q) = bit Z ⁅(q : G), e⁆ := rfl

theorem bitHom_eq_one_iff {Z T P : Subgroup G} (h2 : Z.relIndex T = 2)
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    {e : G} (he : ∀ q ∈ P, ⁅q, e⁆ ∈ T) (q : ↥P) :
    bitHom h2 hPZ hPT he q = 1 ↔ ⁅(q : G), e⁆ ∈ Z := by
  rw [← bit_eq_zero_iff, ← bitHom_apply h2 hPZ hPT he q]
  exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← ofAdd_toAdd (bitHom h2 hPZ hPT he q), h]; rfl⟩

section Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem index_iInf_ker {P : Type*} [Group P] {n : ℕ} (f : Fin n → P →* Multiplicative (ZMod 2))
    (h : ∀ x : Fin n → ZMod 2, x ≠ 0 → ∃ q, ∑ i, x i * Multiplicative.toAdd (f i q) ≠ 0) :
    (⨅ i, (f i).ker).index = 2 ^ n := by
  classical
  let F : P →* Multiplicative (Fin n → ZMod 2) :=
    { toFun := fun q => Multiplicative.ofAdd fun i => Multiplicative.toAdd (f i q)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        funext i
        simp [toAdd_mul] }
  have hF : ∀ q i, Multiplicative.toAdd (F q) i = Multiplicative.toAdd (f i q) := fun _ _ => rfl
  have hker : F.ker = ⨅ i, (f i).ker := by
    ext q
    simp only [MonoidHom.mem_ker, Subgroup.mem_iInf]
    constructor
    · intro hq i
      have h1 := congrFun (congrArg Multiplicative.toAdd hq) i
      rw [hF] at h1
      rw [← ofAdd_toAdd (f i q), h1]
      rfl
    · intro hq
      apply Multiplicative.toAdd.injective
      funext i
      rw [hF, hq i]
      rfl
  have hrange : F.range = ⊤ := by
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let S : Submodule (ZMod 2) (Fin n → ZMod 2) :=
      { carrier := {x | Multiplicative.ofAdd x ∈ F.range}
        add_mem' := fun {a b} ha hb => F.range.mul_mem ha hb
        zero_mem' := F.range.one_mem
        smul_mem' := fun c x hx => by
          rcases h01 c with rfl | rfl
          · show Multiplicative.ofAdd ((0 : ZMod 2) • x) ∈ F.range
            rw [zero_smul]
            exact F.range.one_mem
          · show Multiplicative.ofAdd ((1 : ZMod 2) • x) ∈ F.range
            rw [one_smul]
            exact hx }
    have hS : S < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun hS => hne ?_
      refine eq_top_iff.mpr fun y _ => ?_
      have : Multiplicative.toAdd y ∈ S := hS ▸ Submodule.mem_top
      exact this
    obtain ⟨φ, hφ0, hle⟩ := S.exists_le_ker_of_lt_top hS
    let x : Fin n → ZMod 2 := fun i => φ (fun j => if i = j then 1 else 0)
    have hφ : ∀ y, φ y = ∑ i, y i * x i := fun y => by
      rw [LinearMap.pi_apply_eq_sum_univ φ y]
      rfl
    have hx : x ≠ 0 := by
      intro hx0
      apply hφ0
      refine LinearMap.ext fun y => ?_
      rw [hφ y]
      simp [hx0]
    obtain ⟨q, hq⟩ := h x hx
    apply hq
    have hmem : (fun i => Multiplicative.toAdd (f i q)) ∈ S := ⟨q, rfl⟩
    have h0 := hle hmem
    rw [LinearMap.mem_ker, hφ] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [← hker, Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

end Dual

theorem relIndex_eq_of_iInf_ker {R P : Subgroup G} {n : ℕ}
    (f : Fin n → ↥P →* Multiplicative (ZMod 2)) (hR : ∀ q : ↥P, (q : G) ∈ R ↔ ∀ i, f i q = 1)
    (h : ∀ x : Fin n → ZMod 2, x ≠ 0 → ∃ q, ∑ i, x i * Multiplicative.toAdd (f i q) ≠ 0) :
    R.relIndex P = 2 ^ n := by
  have e : R.subgroupOf P = ⨅ i, (f i).ker := by
    ext q
    rw [Subgroup.mem_subgroupOf, hR, Subgroup.mem_iInf]
    simp only [MonoidHom.mem_ker]
  rw [Subgroup.relIndex, e]
  exact index_iInf_ker f h

@[expose] def pw (e : G) (z : ZMod 2) : G := if z = 0 then 1 else e

theorem pw_zero (e : G) : pw e 0 = 1 := by simp [pw]

theorem pw_one (e : G) : pw e 1 = e := by simp [pw]

theorem eq_zero_or_eq_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

theorem pw_mem {K : Subgroup G} {e : G} (he : e ∈ K) (z : ZMod 2) : pw e z ∈ K := by
  rcases eq_zero_or_eq_one z with rfl | rfl
  · rw [pw_zero]; exact K.one_mem
  · rw [pw_one]; exact he

theorem bit_comm_pw (Z : Subgroup G) (q e : G) (z : ZMod 2) :
    bit Z ⁅q, pw e z⁆ = z * bit Z ⁅q, e⁆ := by
  rcases eq_zero_or_eq_one z with rfl | rfl
  · rw [pw_zero, commutatorElement_one_right, bit_of_mem Z.one_mem, zero_mul]
  · rw [pw_one, one_mul]

theorem conjSub_eq_of_mem_normalizer {g : G} {A : Subgroup G}
    (h : g ∈ Subgroup.normalizer (A : Set G)) : conjSub g A = A := by
  ext x
  rw [mem_conjSub]
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h) x
  rw [inv_inv] at h1
  exact h1.symm

theorem le_normalizer_commutator {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ X, conjSub g ⁅A, B⁆ ≤ ⁅A, B⁆ := fun g hg => by
    rw [← conjSub_commutator, conjSub_eq_of_mem_normalizer (hA hg),
      conjSub_eq_of_mem_normalizer (hB hg)]
  exact fun g hg => F7.mem_normalizer_of_conj_le (key g hg) (key g⁻¹ (X.inv_mem hg))

theorem commutator_le_left_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 := (Subgroup.mem_normalizer_iff.mp (h hb) a⁻¹).mp (A.inv_mem ha)
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  exact A.mul_mem ha (by simpa [mul_assoc] using h1)

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A
