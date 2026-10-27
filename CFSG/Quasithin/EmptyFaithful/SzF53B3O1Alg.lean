module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.F53B3.O1

open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj {N : Subgroup G} {g : G} (h1 : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, g⁻¹ * n * g ∈ N) : g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun hn => ?_⟩
  have := h2 _ hn
  simpa [mul_assoc] using this

theorem le_normalizer_commutator {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ X, ∀ n ∈ ⁅A, B⁆, g * n * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hg n hn
    rw [Subgroup.commutator_def] at hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have ha' : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hA hg) a).mp ha
      have hb' : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hB hg) b).mp hb
      have := Subgroup.commutator_mem_commutator ha' hb'
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact this
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact (⁅A, B⁆).mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact (⁅A, B⁆).inv_mem hx
  intro g hg
  exact mem_normalizer_of_conj (key g hg) (by simpa using key g⁻¹ (X.inv_mem hg))

theorem inf_centralizer_ne_bot_of_normalized [Finite G] {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem relIndex_inf_centralizer_le [Finite G] {R Z : Subgroup G} {s : G}
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r)
    (hs : ∀ r ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Z) :
    (R ⊓ Subgroup.centralizer ({s} : Set G)).relIndex R ≤ Nat.card Z := by
  let f : ↥R →* ↥Z :=
    { toFun := fun r => ⟨r * s * r⁻¹ * s⁻¹, hs r r.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        rintro ⟨r, hr⟩ ⟨r', hr'⟩
        apply Subtype.ext
        have h1 : r * (r' * s * r'⁻¹ * s⁻¹) = (r' * s * r'⁻¹ * s⁻¹) * r :=
          hRZ r hr _ (hs r' hr')
        have h2 := hZc _ (hs r hr) _ (hs r' hr')
        show (r * r') * s * (r * r')⁻¹ * s⁻¹ = (r * s * r⁻¹ * s⁻¹) * (r' * s * r'⁻¹ * s⁻¹)
        rw [h2]
        calc (r * r') * s * (r * r')⁻¹ * s⁻¹
            = (r * (r' * s * r'⁻¹ * s⁻¹)) * r⁻¹ * (r * s * r⁻¹ * s⁻¹) := by group
          _ = (r' * s * r'⁻¹ * s⁻¹ * r) * r⁻¹ * (r * s * r⁻¹ * s⁻¹) := by rw [h1]
          _ = _ := by group }
  have hker : f.ker = (R ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf R := by
    ext r
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : (r : G) * s * (r : G)⁻¹ * s⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨r.2, ?_⟩
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show (r : G) * s * (r : G)⁻¹ * s⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h.symm
  have : (R ⊓ Subgroup.centralizer ({s} : Set G)).relIndex R = f.ker.index := by
    rw [hker]; rfl
  rw [this, Subgroup.index_ker]
  exact Subgroup.card_le_card_group _

theorem mul_inv_mem_of_relIndex_two {A B : Subgroup G} (h2 : A.relIndex B = 2) {a b : G}
    (ha : a ∈ B) (hb : b ∈ B) (haA : a ∉ A) (hbA : b ∉ A) : a * b⁻¹ ∈ A := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp h2
  have h1 := hc ⟨a, ha⟩
  have h2' := hc ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h1 h2'
  have ha' : a * (c : G) ∈ A := by
    rcases h1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h haA
  have hb' : b * (c : G) ∈ A := by
    rcases h2' with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hbA
  have := A.mul_mem ha' (A.inv_mem hb')
  simpa [mul_assoc] using this

end CFSG.Quasithin.F53B3.O1
