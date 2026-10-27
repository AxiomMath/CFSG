
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.KGFactC31EBasis

public section

namespace CFSG.Quasithin.KGC31

section Coset

variable {G : Type*} [Group G]

theorem card_le_sum_coset {K : Subgroup G} [Finite K] (b : G) (rs : List G) (P : G → Prop)
    (hP : ∀ g ∈ K, P g → ∃ r ∈ rs, g * b * g⁻¹ = r * b * r⁻¹) (hrs : ∀ r ∈ rs, r ∈ K) :
    Nat.card {g : K // P g} ≤
      (rs.map fun r => Nat.card {c : K // (c : G) * b = b * c ∧ P (r * c)}).sum := by
  classical
  have key : ∀ l : List G, (∀ r ∈ l, r ∈ K) →
      Nat.card {g : K // P g ∧ ∃ r ∈ l, (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹} ≤
        (l.map fun r => Nat.card {c : K // (c : G) * b = b * c ∧ P (r * c)}).sum := by
    intro l
    induction l with
    | nil =>
      intro _
      have : IsEmpty {g : K // P g ∧ ∃ r ∈ ([] : List G), (g : G) * b * (g : G)⁻¹ =
          r * b * r⁻¹} := ⟨fun ⟨_, _, _, hr, _⟩ => by simp at hr⟩
      simp
    | cons r l ih =>
      intro hl
      have hr : r ∈ K := hl r (by simp)
      have h1 : Nat.card {g : K // P g ∧ ∃ r' ∈ r :: l, (g : G) * b * (g : G)⁻¹ =
            r' * b * r'⁻¹} ≤
          Nat.card {g : K // P g ∧ (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹} +
            Nat.card {g : K // P g ∧ ∃ r' ∈ l, (g : G) * b * (g : G)⁻¹ = r' * b * r'⁻¹} := by
        have := Fintype.ofFinite K
        simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
        refine le_trans (Finset.card_le_card fun g hg => ?_) (Finset.card_union_le _ _)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
          Finset.mem_union] at hg ⊢
        obtain ⟨hPg, r', hr', hg'⟩ := hg
        rcases hr' with rfl | hr'
        · exact Or.inl ⟨hPg, hg'⟩
        · exact Or.inr ⟨hPg, r', hr', hg'⟩
      have h2 : Nat.card {g : K // P g ∧ (g : G) * b * (g : G)⁻¹ = r * b * r⁻¹} ≤
          Nat.card {c : K // (c : G) * b = b * c ∧ P (r * c)} := by
        refine Nat.card_le_card_of_injective (fun g => ⟨⟨r⁻¹ * g, K.mul_mem (K.inv_mem hr) g.1.2⟩,
          ?_, ?_⟩) ?_
        · have h := g.2.2
          calc r⁻¹ * (g : G) * b = r⁻¹ * ((g : G) * b * (g : G)⁻¹) * g := by group
            _ = r⁻¹ * (r * b * r⁻¹) * g := by rw [h]
            _ = b * (r⁻¹ * g) := by group
        · simpa using g.2.1
        · intro g₁ g₂ h
          have := congrArg (fun x => (x.1 : G)) h
          simp only [mul_right_inj] at this
          exact Subtype.ext (Subtype.ext this)
      rw [List.map_cons, List.sum_cons]
      exact h1.trans (Nat.add_le_add h2 (ih fun r' h' => hl r' (by simp [h'])))
  refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_))) (key rs hrs)
  exact ⟨fun h => ⟨h, hP g g.2 h⟩, fun h => h.1⟩

end Coset

section Fix

variable {α : Type*}

theorem fix_of_normalizer {U : Subgroup (Equiv.Perm α)} {g : Equiv.Perm α}
    (hg : g ∈ Subgroup.normalizer (U : Set (Equiv.Perm α))) {i : α} (hi : ∀ u ∈ U, u i = i) :
    ∀ u ∈ U, u (g i) = g i := by
  intro u hu
  have h1 : g⁻¹ * u * g ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * u * g)).mpr
      (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
  have h2 := hi _ h1
  have : u (g i) = g ((g⁻¹ * u * g) i) := by simp [Equiv.Perm.mul_apply]
  rw [this, h2]

theorem sign_commutator_fin3 : ∀ a b : Equiv.Perm (Fin 3),
    Equiv.Perm.sign (a * b * a⁻¹ * b⁻¹) = 1 := by
  decide

theorem commutator_alt_fin3 : ∀ a b : Equiv.Perm (Fin 3), Equiv.Perm.sign a = 1 →
    Equiv.Perm.sign b = 1 → a * b * a⁻¹ * b⁻¹ = 1 := by
  decide

theorem fixes_of_perfect {U K : Subgroup (Equiv.Perm α)}
    (hK : K ≤ Subgroup.normalizer (U : Set (Equiv.Perm α))) (hperf : ⁅K, K⁆ = K) (T : Finset α)
    (hT : T.card = 3) (hfix : ∀ i, (∀ u ∈ U, u i = i) ↔ i ∈ T) : ∀ k ∈ K, ∀ i ∈ T, k i = i := by
  let St : Subgroup (Equiv.Perm α) :=
    { carrier := {g | ∀ i, i ∈ T ↔ g i ∈ T}
      mul_mem' := fun {a b} ha hb i => (hb i).trans (ha (b i))
      one_mem' := fun i => Iff.rfl
      inv_mem' := fun {a} ha i => by
        have e : a (a⁻¹ i) = i := by
          rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
        have := ha (a⁻¹ i)
        rw [e] at this
        exact this.symm }
  have hKS : K ≤ St := fun k hk i => by
    have hk' := hK hk
    constructor
    · intro hi
      exact (hfix _).mp (fix_of_normalizer hk' ((hfix i).mpr hi))
    · intro hi
      have hki := fix_of_normalizer (Subgroup.inv_mem _ hk') ((hfix _).mpr hi)
      rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply] at hki
      exact (hfix i).mp hki
  let e : {i // i ∈ T} ≃ Fin 3 := T.equivFinOfCardEq hT
  let φ : ↥St →* Equiv.Perm (Fin 3) :=
    { toFun := fun g => e.permCongr ((g : Equiv.Perm α).subtypePerm fun x => (g.2 x).symm)
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [Equiv.permCongr_apply] }
  let B₁ : Subgroup (Equiv.Perm α) := φ.ker.map St.subtype
  let B₂ : Subgroup (Equiv.Perm α) := ((alternatingGroup (Fin 3)).comap φ).map St.subtype
  have hc1 : ⁅St, St⁆ ≤ B₂ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    let a' : ↥St := ⟨a, ha⟩
    let b' : ↥St := ⟨b, hb⟩
    refine ⟨a' * b' * a'⁻¹ * b'⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv,
      Equiv.Perm.mem_alternatingGroup]
    exact sign_commutator_fin3 _ _
  have hc2 : ⁅B₂, B₂⁆ ≤ B₁ := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [commutatorElement_def]
    refine ⟨a * b * a⁻¹ * b⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_alt_fin3 _ _ (Equiv.Perm.mem_alternatingGroup.mp ha)
      (Equiv.Perm.mem_alternatingGroup.mp hb)
  have hKB₂ : K ≤ B₂ := by
    rw [← hperf]
    exact (Subgroup.commutator_mono hKS hKS).trans hc1
  have hKB₁ : K ≤ B₁ := by
    rw [← hperf]
    exact (Subgroup.commutator_mono hKB₂ hKB₂).trans hc2
  intro k hk i hi
  obtain ⟨g, hg, hgk⟩ := hKB₁ hk
  have h1 : φ g = 1 := hg
  have h2 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (e ⟨i, hi⟩)) h1
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, φ, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.Perm.coe_one, id_eq] at h2
  have h3 := congrArg Subtype.val (e.injective h2)
  simp only [Equiv.Perm.subtypePerm_apply] at h3
  rw [← hgk]
  exact h3

end Fix

end CFSG.Quasithin.KGC31

end
