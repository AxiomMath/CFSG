module

public import CFSG.Monster.GMS.Orbits

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

namespace TableVOf

@[expose] def selfMem (a : G) : Subgroup.centralizer ({a} : Set G) :=
  ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[simp]
theorem coe_selfMem (a : G) : (selfMem a : G) = a := rfl

theorem centralizer_selfMem_eq_top (a : G) :
    Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem card_inf_centralizer_eq {K : Subgroup G} (k : K) :
    Nat.card ↥(K ⊓ Subgroup.centralizer ({(k : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({k} : Set K)) := by
  have : (Subgroup.centralizer ({k} : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(k : G)} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hg, hgk⟩
      exact ⟨⟨g, hg⟩, Subtype.ext hgk, rfl⟩
  rw [← this, Subgroup.card_map_of_injective K.subtype_injective]

theorem cover_iff (a : G) (b z u : Subgroup.centralizer ({a} : Set G)) :
    (∀ t ∈ Subgroup.centralizer ({a} : Set G), orderOf t = 2 → t ≠ a →
      ∃ g ∈ Subgroup.centralizer ({a} : Set G),
        g * t * g⁻¹ = (b : G) ∨ g * t * g⁻¹ = (z : G) ∨ g * t * g⁻¹ = a * z ∨
          g * t * g⁻¹ = (u : G)) ↔
    (∀ t ∈ Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))),
      orderOf t = 2 → t ≠ selfMem a →
      ∃ g ∈ Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))),
        g * t * g⁻¹ = b ∨ g * t * g⁻¹ = z ∨ g * t * g⁻¹ = selfMem a * z ∨ g * t * g⁻¹ = u) := by
  constructor
  · intro h t _ ht2 hta
    obtain ⟨g, hg, hgt⟩ := h t t.2 (by rw [Subgroup.orderOf_coe]; exact ht2)
      (fun e => hta (Subtype.ext e))
    refine ⟨⟨g, hg⟩, by rw [centralizer_selfMem_eq_top]; trivial, ?_⟩
    simpa [Subtype.ext_iff] using hgt
  · intro h t ht ht2 hta
    obtain ⟨g, -, hgt⟩ := h ⟨t, ht⟩ (by rw [centralizer_selfMem_eq_top]; trivial)
      ((Subgroup.orderOf_mk t ht).trans ht2) (fun e => hta (congrArg Subtype.val e))
    refine ⟨g, g.2, ?_⟩
    simpa [Subtype.ext_iff] using hgt

theorem sylow_iff (a : G) (z : Subgroup.centralizer ({a} : Set G)) :
    (∀ T : Subgroup G,
      T ≤ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {(z : G)} →
      Nat.card T = 2 ^ 42 → ∀ x : G,
        (x ∈ T ∧ ∀ s ∈ T, x * s = s * x) ↔ (x = 1 ∨ x = a ∨ x = (z : G) ∨ x = a * z)) ↔
    (∀ T : Subgroup (Subgroup.centralizer ({a} : Set G)),
      T ≤ Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))) ⊓
        Subgroup.centralizer {z} →
      Nat.card T = 2 ^ 42 → ∀ x : Subgroup.centralizer ({a} : Set G),
        (x ∈ T ∧ ∀ s ∈ T, x * s = s * x) ↔
          (x = 1 ∨ x = selfMem a ∨ x = z ∨ x = selfMem a * z)) := by
  constructor
  · intro hG T hT hcard x
    have hT₀ : T.map (Subgroup.centralizer ({a} : Set G)).subtype ≤
        Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {(z : G)} := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      have hyz := (Subgroup.mem_inf.mp (hT hy)).2
      rw [Subgroup.mem_centralizer_singleton_iff] at hyz ⊢
      exact congrArg Subtype.val hyz
    have key := hG (T.map (Subgroup.centralizer ({a} : Set G)).subtype) hT₀
      (by
        rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective]
        exact hcard) (x : G)
    have h1 : ((x : G) ∈ T.map (Subgroup.centralizer ({a} : Set G)).subtype ∧
        ∀ s ∈ T.map (Subgroup.centralizer ({a} : Set G)).subtype, (x : G) * s = s * (x : G)) ↔
          (x ∈ T ∧ ∀ s ∈ T, x * s = s * x) := by
      refine and_congr
        (Subgroup.mem_map_iff_mem (Subgroup.centralizer ({a} : Set G)).subtype_injective) ?_
      constructor
      · intro h s hs
        exact Subtype.ext (h s (Subgroup.mem_map_of_mem _ hs))
      · rintro h _ ⟨s, hs, rfl⟩
        exact congrArg Subtype.val (h s hs)
    rw [← h1, key]
    simp only [Subtype.ext_iff, Subgroup.coe_one, Subgroup.coe_mul, coe_selfMem]
  · intro hC' T hT hcard x
    have hTC : T ≤ Subgroup.centralizer ({a} : Set G) := fun t ht =>
      (Subgroup.mem_inf.mp (hT ht)).1
    have hT₁ : T.subgroupOf (Subgroup.centralizer ({a} : Set G)) ≤
        Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))) ⊓
          Subgroup.centralizer {z} := by
      intro y hy
      refine Subgroup.mem_inf.mpr ⟨by rw [centralizer_selfMem_eq_top]; trivial, ?_⟩
      have hyz := (Subgroup.mem_inf.mp (hT (Subgroup.mem_subgroupOf.mp hy))).2
      rw [Subgroup.mem_centralizer_singleton_iff] at hyz ⊢
      exact Subtype.ext hyz
    have hcard₁ : Nat.card (T.subgroupOf (Subgroup.centralizer ({a} : Set G))) = 2 ^ 42 := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
    by_cases hx : x ∈ Subgroup.centralizer ({a} : Set G)
    · have key := hC' (T.subgroupOf (Subgroup.centralizer ({a} : Set G))) hT₁ hcard₁ ⟨x, hx⟩
      have h1 : ((⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) ∈
            T.subgroupOf (Subgroup.centralizer ({a} : Set G)) ∧
          ∀ s ∈ T.subgroupOf (Subgroup.centralizer ({a} : Set G)),
            (⟨x, hx⟩ : Subgroup.centralizer ({a} : Set G)) * s = s * ⟨x, hx⟩) ↔
          (x ∈ T ∧ ∀ s ∈ T, x * s = s * x) := by
        refine and_congr Subgroup.mem_subgroupOf ?_
        constructor
        · intro h s hs
          exact congrArg Subtype.val (h ⟨s, hTC hs⟩ (Subgroup.mem_subgroupOf.mpr hs))
        · intro h s hs
          exact Subtype.ext (h s (Subgroup.mem_subgroupOf.mp hs))
      rw [← h1, key]
      simp only [Subtype.ext_iff, Subgroup.coe_one, Subgroup.coe_mul, coe_selfMem]
    · have hxT : x ∉ T := fun h => hx (hTC h)
      simp only [hxT, false_and, false_iff]
      rintro (h | h | h | h) <;> refine hx ?_ <;> rw [h]
      · exact Subgroup.one_mem _
      · exact (selfMem a).2
      · exact z.2
      · exact Subgroup.mul_mem _ (selfMem a).2 z.2

theorem tableV_iff_centralizer {a : G} (b z u : Subgroup.centralizer ({a} : Set G)) :
    TableV a (b : G) (z : G) (u : G) ↔ TableV (selfMem a) b z u := by
  have hcen := centralizer_selfMem_eq_top a
  have hmem : ∀ x : Subgroup.centralizer ({a} : Set G),
      x ∈ Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))) :=
    fun x => by rw [hcen]; trivial
  have hne : ∀ x : Subgroup.centralizer ({a} : Set G), (x : G) ≠ a ↔ x ≠ selfMem a :=
    fun x => ⟨fun h e => h (by rw [e]; rfl), fun h e => h (Subtype.ext e)⟩
  have hcard : ∀ x : Subgroup.centralizer ({a} : Set G),
      Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {(x : G)}) =
        Nat.card ↥(Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G))) ⊓
          Subgroup.centralizer {x}) := fun x => by
    rw [hcen, top_inf_eq, card_inf_centralizer_eq]
  have hcardC : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) =
      Nat.card
        ↥(Subgroup.centralizer ({selfMem a} : Set (Subgroup.centralizer ({a} : Set G)))) := by
    rw [hcen, Subgroup.card_top]
  constructor
  · rintro ⟨-, -, -, hb2, hz2, hu2, hba, hza, hua, hcov, hC, hcb, hcz, hcu, hsyl⟩
    exact ⟨hmem b, hmem z, hmem u, (Subgroup.orderOf_coe b).symm.trans hb2,
      (Subgroup.orderOf_coe z).symm.trans hz2, (Subgroup.orderOf_coe u).symm.trans hu2,
      (hne b).mp hba, (hne z).mp hza, (hne u).mp hua, (cover_iff a b z u).mp hcov,
      hcardC.symm.trans hC, (hcard b).symm.trans hcb, (hcard z).symm.trans hcz,
      (hcard u).symm.trans hcu, (sylow_iff a z).mp hsyl⟩
  · rintro ⟨-, -, -, hb2, hz2, hu2, hba, hza, hua, hcov, hC, hcb, hcz, hcu, hsyl⟩
    exact ⟨b.2, z.2, u.2, (Subgroup.orderOf_coe b).trans hb2, (Subgroup.orderOf_coe z).trans hz2,
      (Subgroup.orderOf_coe u).trans hu2, (hne b).mpr hba, (hne z).mpr hza, (hne u).mpr hua,
      (cover_iff a b z u).mpr hcov, hcardC.trans hC, (hcard b).trans hcb, (hcard z).trans hcz,
      (hcard u).trans hcu, (sylow_iff a z).mpr hsyl⟩

end TableVOf

theorem TableV.of_centralizerMulEquiv {H : Type*} [Group H] {a : G} {a' : H}
    (φ : Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({a'} : Set H))
    (hφa : ∀ c : Subgroup.centralizer ({a} : Set G), (c : G) = a → (φ c : H) = a')
    {b z u : Subgroup.centralizer ({a} : Set G)} (h : TableV a (b : G) (z : G) (u : G)) :
    TableV a' (φ b : H) (φ z : H) (φ u : H) := by
  have h1 := TableV.of_mulEquiv φ ((TableVOf.tableV_iff_centralizer b z u).mp h)
  have hφ : φ (TableVOf.selfMem a) = TableVOf.selfMem a' := Subtype.ext (hφa _ rfl)
  rw [hφ] at h1
  exact (TableVOf.tableV_iff_centralizer (φ b) (φ z) (φ u)).mpr h1

theorem TableV.exists_of_centralizerMulEquiv {H : Type*} [Group H] {a : G} {a' : H}
    (φ : Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({a'} : Set H))
    (hφa : ∀ c : Subgroup.centralizer ({a} : Set G), (c : G) = a → (φ c : H) = a')
    {b z u : G} (h : TableV a b z u) : ∃ b' z' u' : H, TableV a' b' z' u' :=
  ⟨_, _, _, TableV.of_centralizerMulEquiv φ hφa (b := ⟨b, h.1⟩) (z := ⟨z, h.2.1⟩)
    (u := ⟨u, h.2.2.1⟩) h⟩

end CFSG.Monster.GMS
