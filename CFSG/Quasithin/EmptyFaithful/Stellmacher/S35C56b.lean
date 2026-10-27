module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C56

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem commutator_commutator_le {X Y Z N E : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (hXE : X ≤ Subgroup.normalizer (E : Set G))
    (hZE : Z ≤ E) (hEY : ⁅E, Y⁆ ≤ N) : ⁅⁅X, Y⁆, Z⁆ ≤ N := by
  refine three_subgroups_mod (X := Y) (Y := Z) (Z := X) hY hZ hX ?_ ?_
  · have h1 : ⁅Y, Z⁆ ≤ N := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hZE le_rfl).trans hEY
    exact (Subgroup.commutator_mono h1 le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hX)
  · have h1 : ⁅Z, X⁆ ≤ E := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl hZE).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hXE)
    exact (Subgroup.commutator_mono h1 le_rfl).trans hEY

theorem conj_mem_commutator {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) : ∀ c ∈ ⁅A, B⁆, g * c * g⁻¹ ∈ ⁅A, B⁆ := by
  have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅a, b⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulAut.conj_apply]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hA a ha) (hB b hb)
  intro c hc
  exact hle hc

@[expose] def commSpan (Z Q : Subgroup G) (b : G) : Subgroup G :=
  Subgroup.closure ((Z : Set G) ∪ {c | ∃ q ∈ Q, c = ⁅b, q⁆})

theorem le_commSpan (Z Q : Subgroup G) (b : G) : Z ≤ commSpan Z Q b :=
  fun _ hz => Subgroup.subset_closure (Or.inl hz)

theorem comm_mem_commSpan {Z Q : Subgroup G} {b q : G} (hq : q ∈ Q) :
    ⁅b, q⁆ ∈ commSpan Z Q b :=
  Subgroup.subset_closure (Or.inr ⟨q, hq, rfl⟩)

theorem commSpan_le {Z Q V : Subgroup G} {b : G} (hZ : Z ≤ V) (hb : ∀ q ∈ Q, ⁅b, q⁆ ∈ V) :
    commSpan Z Q b ≤ V := by
  refine (Subgroup.closure_le V).mpr ?_
  rintro x (hx | ⟨q, hq, rfl⟩)
  · exact hZ hx
  · exact hb q hq

theorem conj_mem_commSpan {Z Q V : Subgroup G} {b x : G}
    (hV : ∀ u ∈ V, ∀ w ∈ V, u * w = w * u) (hZ : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z)
    (hQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxb : ⁅x, b⁆ ∈ V) (hVQ : ∀ v ∈ V, ∀ q ∈ Q, ⁅v, q⁆ ∈ Z)
    (hbV : ∀ q ∈ Q, ⁅b, q⁆ ∈ V) :
    ∀ u ∈ commSpan Z Q b, x * u * x⁻¹ ∈ commSpan Z Q b := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨q, hq, rfl⟩
    · exact le_commSpan Z Q b (hZ y hy)
    · set v : G := ⁅x, b⁆ with hv
      have hq' := hQ q hq
      have hc : ⁅b, x * q * x⁻¹⁆ ∈ V := hbV _ hq'
      have e : x * ⁅b, q⁆ * x⁻¹ = v * ⁅b, x * q * x⁻¹⁆ * v⁻¹ * ⁅v, x * q * x⁻¹⁆ := by
        simp only [hv, commutatorElement_def]
        group
      have e2 : v * ⁅b, x * q * x⁻¹⁆ * v⁻¹ = ⁅b, x * q * x⁻¹⁆ := by
        rw [hV v hxb _ hc]
        group
      rw [e, e2]
      exact Subgroup.mul_mem _ (comm_mem_commSpan hq')
        (le_commSpan Z Q b (hVQ v hxb _ hq'))
  | one => simp
  | mul y w _ _ hy hw =>
    have : x * (y * w) * x⁻¹ = (x * y * x⁻¹) * (x * w * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hy hw
  | inv y _ hy =>
    have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hy

theorem exists_card_le [Finite G] {R V : Subgroup G} (hV : ∀ u ∈ V, ∀ w ∈ V, u * w = w * u)
    (hRV : R ≤ V) {c : G} (hc : c ∈ V) (hc2 : c * c = 1) :
    ∃ K : Subgroup G, R ≤ K ∧ c ∈ K ∧ Nat.card K ≤ 2 * Nat.card R := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  let K : Subgroup G :=
    { carrier := {x | x ∈ R ∨ ∃ r ∈ R, x = c * r}
      mul_mem' := by
        rintro x y (hx | ⟨r, hr, rfl⟩) (hy | ⟨s, hs, rfl⟩)
        · exact Or.inl (R.mul_mem hx hy)
        · exact Or.inr ⟨x * s, R.mul_mem hx hs, by
            rw [← mul_assoc, hV x (hRV hx) c hc, mul_assoc]⟩
        · exact Or.inr ⟨r * y, R.mul_mem hr hy, by rw [mul_assoc]⟩
        · refine Or.inl ?_
          have : c * r * (c * s) = r * s := by
            rw [mul_assoc, ← mul_assoc r c s, hV r (hRV hr) c hc, mul_assoc c r s,
              ← mul_assoc c c, hc2, one_mul]
          rw [this]
          exact R.mul_mem hr hs
      one_mem' := Or.inl R.one_mem
      inv_mem' := by
        rintro x (hx | ⟨r, hr, rfl⟩)
        · exact Or.inl (R.inv_mem hx)
        · refine Or.inr ⟨r⁻¹, R.inv_mem hr, ?_⟩
          rw [mul_inv_rev, hcinv]
          exact hV _ (V.inv_mem (hRV hr)) c hc }
  refine ⟨K, fun x hx => Or.inl hx, Or.inr ⟨1, R.one_mem, by simp⟩, ?_⟩
  have hsub : (K : Set G) ⊆ (R : Set G) ∪ (fun r => c * r) '' (R : Set G) := by
    rintro x (hx | ⟨r, hr, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨r, hr, rfl⟩
  have h1 : Nat.card K = (K : Set G).ncard := (Nat.card_coe_set_eq _).symm
  have h2 : Nat.card R = (R : Set G).ncard := (Nat.card_coe_set_eq _).symm
  rw [h1, h2]
  calc (K : Set G).ncard ≤ ((R : Set G) ∪ (fun r => c * r) '' (R : Set G)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (R : Set G).ncard + ((fun r => c * r) '' (R : Set G)).ncard := Set.ncard_union_le _ _
    _ ≤ (R : Set G).ncard + (R : Set G).ncard := by
        exact Nat.add_le_add_left (Set.ncard_image_le (R : Set G).toFinite) _
    _ = 2 * (R : Set G).ncard := by ring

theorem inv_mul_mem_of_relIndex_eq_two {N K : Subgroup G} (h : N.relIndex K = 2) {q t : G}
    (hq : q ∈ K) (ht : t ∈ K) (hqN : q ∉ N) (htN : t ∉ N) : t⁻¹ * q ∈ N := by
  obtain ⟨a, ha, hx⟩ := Subgroup.relIndex_eq_two_iff'.mp h
  have h1 : a * q ∈ N := by
    rcases hx q hq with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd h2 hqN
  have h2 : a * t ∈ N := by
    rcases hx t ht with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd h2 htN
  have := N.mul_mem (N.inv_mem h2) h1
  simpa [mul_assoc] using this

end CFSG.Quasithin.F53.Stellmacher.S35.C56
