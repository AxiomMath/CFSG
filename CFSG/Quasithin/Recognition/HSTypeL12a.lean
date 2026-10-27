module

public import CFSG.Quasithin.Recognition.HSTypeK

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem ZQ_le_P [Finite G] (h : HSSetting z V) : hsZQ z ≤ hsP V := by
  rw [← h.centralizer_V_eq]
  exact fun x hx => ⟨h.Q_le_M hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_iff.mp hx.2 v (h.two.le hv)⟩

theorem exists_mem_ZQ_ne [Finite G] (h : HSSetting z V) :
    ∃ u ∈ hsZQ z, u ≠ 1 ∧ u ≠ z ∧ u * u = z := by
  obtain ⟨u, huZ, hu⟩ : ∃ u ∈ hsZQ z, u ∉ Subgroup.zpowers z := by
    by_contra hne
    push Not at hne
    have hle : hsZQ z ≤ Subgroup.zpowers z := fun u hu => hne u hu
    have := Subgroup.card_le_of_le hle
    rw [h.card_ZQ, Nat.card_zpowers, h.orderOf_z] at this
    omega
  have hu1 : u ≠ 1 := fun h1 => hu (h1 ▸ (Subgroup.zpowers z).one_mem)
  have huz : u ≠ z := fun h1 => hu (h1 ▸ Subgroup.mem_zpowers z)
  rcases h.z_eq_or_sq_of_mem_ZQ huZ hu1 with h1 | h1
  · exact absurd h1.symm huz
  · exact ⟨u, huZ, hu1, huz, h1.symm⟩

theorem exists_conj_ZQ_not_le_Q [Finite G] (h : HSSetting z V) :
    ∃ m ∈ hsM V, ∃ w ∈ hsZQ z, m * w * m⁻¹ ∉ hsQ z := by
  by_contra hall
  push Not at hall
  obtain ⟨u, huZ, -, -, huu⟩ := h.exists_mem_ZQ_ne
  set A := Subgroup.closure {x : G | ∃ m ∈ hsM V, ∃ w ∈ hsZQ z, m * w * m⁻¹ = x} with hA
  have hAQ : A ≤ hsQ z := by
    rw [hA, Subgroup.closure_le]
    rintro _ ⟨m, hm, w, hw, rfl⟩
    exact hall m hm w hw
  have hAP : A ≤ hsP V := by
    rw [hA, Subgroup.closure_le]
    rintro _ ⟨m, hm, w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting (hsM V) hm) w).mp
      (h.ZQ_le_P hw)
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.P_comm (hAP hx) (hAP hy)
  have h16 : Nat.card A ≤ 16 := by
    have := card_le_sixteen_of_isZ4Q8Q8 h.one.fstar (A.subgroupOf (hsQ z))
      (fun x hx y hy => Subtype.ext (hAc x hx y hy))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv] at this
  have hsqA : ∀ v ∈ V, ∃ a ∈ A, a * a = v := by
    intro v hv
    by_cases hv1 : v = 1
    · exact ⟨1, A.one_mem, by rw [hv1, mul_one]⟩
    obtain ⟨m, hm, hmz⟩ := h.exists_conj_eq_of_mem_V hv hv1
    refine ⟨m * u * m⁻¹, Subgroup.subset_closure ⟨m, hm, u, huZ, rfl⟩, ?_⟩
    rw [← hmz, ← huu]
    group
  have hVA : V ≤ A := fun v hv => by
    obtain ⟨a, ha, rfl⟩ := hsqA v hv
    exact A.mul_mem ha ha
  let s : ↥A →* ↥A :=
    { toFun := fun a => a * a
      map_one' := by simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hab := hAc a a.2 b b.2
        calc (a : G) * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = a * a * (b * b) := by group }
  have hker : s.ker = V.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro ha
      exact h.mem_V_of_mem_P (hAP a.2) (congrArg Subtype.val ha)
    · intro ha
      apply Subtype.ext
      have := h.elem.2 _ ha
      show (a : G) * a = 1
      simpa [sq] using this
  have hcardker : Nat.card s.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, h.card_V]
  have hrange : V.subgroupOf A ≤ s.range := by
    intro a ha
    obtain ⟨b, hb, hbb⟩ := hsqA a ha
    exact ⟨⟨b, hb⟩, Subtype.ext hbb⟩
  have hcardrange : 8 ≤ Nat.card s.range := by
    have := Subgroup.card_le_of_le hrange
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, h.card_V] at this
  have h1 := Subgroup.card_mul_index s.ker
  rw [Subgroup.index_ker, hcardker] at h1
  omega

end HSSetting

end CFSG.Quasithin.HSType
