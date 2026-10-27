module

public import CFSG.Sporadic.Th.Max3.OddCase

public section

namespace CFSG.Sporadic.Th

open Native Max3

theorem centralizer_conj (g u : J) :
    Subgroup.centralizer ({g * u * g⁻¹} : Set J) =
      (Subgroup.centralizer ({u} : Set J)).map (MulAut.conj g).toMonoidHom := by
  ext v
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro hv
    refine ⟨g⁻¹ * v * g, ?_, by group⟩
    calc g⁻¹ * v * g * u = g⁻¹ * (v * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * v) * g := by rw [hv]
      _ = u * (g⁻¹ * v * g) := by group
  · rintro ⟨w, hw, rfl⟩
    calc g * w * g⁻¹ * (g * u * g⁻¹) = g * (w * u) * g⁻¹ := by group
      _ = g * (u * w) * g⁻¹ := by rw [hw]
      _ = g * u * g⁻¹ * (g * w * g⁻¹) := by group

theorem eq_one_or_eq_a_of_comm
    {s : J} (hs : s ∈ M) (hc : ∀ m ∈ M, s * m = m * s) :
    s = 1 ∨ s = a := by
  have hsz : s ∈ Subgroup.zpowers z := by
    rw [← centralizer_Q_inf_M]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun g hg => (hc g (Q_le_M hg)).symm, hs⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hsz
  have hz2 : z * z = 1 := z_mul_self
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left; rw [← two_mul, zpow_mul, zpow_two, hz2, one_zpow]
  · right; rw [zpow_add, zpow_mul, zpow_two, hz2, one_zpow, one_mul, zpow_one, z_eq_a]

theorem closure_genPair_eq_top {c : J}
    (ha : a ∈ Subgroup.closure (Kernel.genPair c)) (hb : b ∈ Subgroup.closure (Kernel.genPair c)) :
    Subgroup.closure (Kernel.genPair c) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

theorem gen_facts_kernel (hK : Kernel.KernelFacts) :
    (∃ c : J, c * Max3.q 0 * c⁻¹ = a ∧ Subgroup.closure (Kernel.genPair c) = ⊤) ∧
      ∃ c : J, c * Max3.x * c⁻¹ = a ∧ Subgroup.closure (Kernel.genPair c) = ⊤ := by
  obtain ⟨c0, a0, b0⟩ := hK.gen0
  obtain ⟨c1, a1, b1⟩ := hK.gen1
  exact ⟨⟨_, c0, closure_genPair_eq_top a0 b0⟩, _, c1, closure_genPair_eq_top a1 b1⟩

theorem eq_top_of_centralizer_le
    (hK : Kernel.KernelFacts)
    {F : Subgroup J} (hMF : M ≤ F) {b : J} (hb : b ∈ M)
    (hb2 : orderOf b = 2) (hba : b ≠ a) (hbF : Subgroup.centralizer ({b} : Set J) ≤ F) :
    F = ⊤ := by
  obtain ⟨⟨c₀, h0c, h0g⟩, c₁, h1c, h1g⟩ := gen_facts_kernel hK
  have hCa := Kernel.centralizer_a_eq_M hK
  obtain ⟨m, hm, hr⟩ := max3_involution_representatives b hb hb2
  have hrF : ∀ r : J, m * b * m⁻¹ = r → Subgroup.centralizer ({r} : Set J) ≤ F := by
    intro r hmr
    rw [← hmr, centralizer_conj]
    rintro _ ⟨v, hv, rfl⟩
    exact F.mul_mem (F.mul_mem (hMF hm) (hbF hv)) (F.inv_mem (hMF hm))
  have hconjF : ∀ (c r : J), c * r * c⁻¹ = a → Subgroup.centralizer ({r} : Set J) ≤ F →
      Subgroup.closure ({x * (c⁻¹ * (x * c)), y * (c⁻¹ * (y * c))} : Set J) = ⊤ → F = ⊤ := by
    intro c r hc hrF' hgen
    have hCr : ∀ u ∈ M, c⁻¹ * u * c ∈ F := by
      intro u hu
      apply hrF'
      have hu' : u ∈ Subgroup.centralizer ({a} : Set J) := hCa ▸ hu
      rw [Subgroup.mem_centralizer_singleton_iff] at hu' ⊢
      have hr : r = c⁻¹ * a * c := by rw [← hc]; group
      rw [hr]
      calc c⁻¹ * u * c * (c⁻¹ * a * c) = c⁻¹ * (u * a) * c := by group
        _ = c⁻¹ * (a * u) * c := by rw [hu']
        _ = c⁻¹ * a * c * (c⁻¹ * u * c) := by group
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact F.mul_mem (hMF x_mem_M) (by rw [← mul_assoc]; exact hCr _ x_mem_M)
    · exact F.mul_mem (hMF y_mem_M) (by rw [← mul_assoc]; exact hCr _ y_mem_M)
  rcases hr with hz | hq | hx
  ·
    exfalso
    apply hba
    have hza : z = a := z_eq_a
    have hcomm : m * a = a * m := by
      have := (commute_z_of_mem_M hm).eq
      rw [hza] at this
      exact this.symm
    calc b = m⁻¹ * (m * b * m⁻¹) * m := by group
      _ = m⁻¹ * a * m := by rw [hz, hza]
      _ = a := by rw [mul_assoc, ← hcomm]; group
  · exact hconjF c₀ (q 0) h0c (hrF _ hq) h0g
  · exact hconjF c₁ x h1c (hrF _ hx) h1g

theorem sup_centralizer_a_eq_top
    (hK : Kernel.KernelFacts)
    {s : J} (hs2 : orderOf s = 2) (hsa : s ≠ a) :
    Subgroup.centralizer ({a} : Set J) ⊔ Subgroup.centralizer ({s} : Set J) = ⊤ := by
  have hCa := Kernel.centralizer_a_eq_M hK
  set F := Subgroup.centralizer ({a} : Set J) ⊔ Subgroup.centralizer ({s} : Set J)
  have hMF : M ≤ F := by rw [← hCa]; exact le_sup_left
  by_cases hiso : ∀ g ∈ F, g * a * g⁻¹ * a = a * (g * a * g⁻¹) → g * a * g⁻¹ = a
  · exfalso
    have hFM := eq_M_of_isolated hK hMF hiso
    have hle : Subgroup.centralizer ({s} : Set J) ≤ Subgroup.centralizer ({a} : Set J) := by
      rw [hCa, ← hFM]; exact le_sup_right
    obtain ⟨g, hg⟩ := isConj_iff.1 (all_involutions_conjugate s hs2)
    have hcard : Nat.card (Subgroup.centralizer ({s} : Set J)) =
        Nat.card (Subgroup.centralizer ({a} : Set J)) := by
      rw [← hg, centralizer_conj,
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    have hsM : s ∈ M := by
      rw [← hCa, ← heq, Subgroup.mem_centralizer_singleton_iff]
    have hsc : ∀ m ∈ M, s * m = m * s := by
      intro m hm
      have : m ∈ Subgroup.centralizer ({s} : Set J) := by rw [heq, hCa]; exact hm
      exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
    rcases eq_one_or_eq_a_of_comm hsM hsc with h1 | h1
    · rw [h1, orderOf_one] at hs2; exact absurd hs2 (by norm_num)
    · exact hsa h1
  · push Not at hiso
    obtain ⟨g, hgF, hcomm, hne⟩ := hiso
    have hbM : g * a * g⁻¹ ∈ M := by
      rw [← hCa, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hb2 : orderOf (g * a * g⁻¹) = 2 := by
      rw [← orderOf_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩ : IsConj a (g * a * g⁻¹)), ← z_eq_a]
      exact orderOf_eq_prime (by rw [sq]; exact z_mul_self) z_ne_one
    have hbF : Subgroup.centralizer ({g * a * g⁻¹} : Set J) ≤ F := by
      rw [centralizer_conj]
      rintro _ ⟨v, hv, rfl⟩
      exact F.mul_mem (F.mul_mem hgF (Subgroup.mem_sup_left hv)) (F.inv_mem hgF)
    exact eq_top_of_centralizer_le hK hMF hbM hb2 hne hbF

theorem sup_centralizer_eq_top
    (hK : Kernel.KernelFacts)
    {t₁ t₂ : J} (h₁ : orderOf t₁ = 2) (h₂ : orderOf t₂ = 2)
    (hne : t₁ ≠ t₂) :
    Subgroup.centralizer ({t₁} : Set J) ⊔ Subgroup.centralizer ({t₂} : Set J) = ⊤ := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (all_involutions_conjugate t₁ h₁)
  have ht₂ : t₂ = g * (g⁻¹ * t₂ * g) * g⁻¹ := by group
  have hs2 : orderOf (g⁻¹ * t₂ * g) = 2 := by
    rw [← orderOf_eq_of_isConj (isConj_iff.2 ⟨g⁻¹, by group⟩ : IsConj t₂ (g⁻¹ * t₂ * g)), h₂]
  have hsa : g⁻¹ * t₂ * g ≠ a := by
    intro h
    apply hne
    rw [ht₂, h]
  rw [ht₂, centralizer_conj, centralizer_conj, ← Subgroup.map_sup,
    sup_centralizer_a_eq_top hK hs2 hsa,
    Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective]

theorem isCoatom_M
    (hK : Kernel.KernelFacts) :
    IsCoatom M := by
  have hCa := Kernel.centralizer_a_eq_M hK
  refine ⟨fun h => ?_, fun F hF => ?_⟩
  · have := congrArg (fun K : Subgroup J => Nat.card K) h
    norm_num [card_M, Subgroup.card_top, natCard_J] at this
  · obtain ⟨g, hgF, hgM⟩ := IsConcreteLE.exists_of_lt hF
    have hne : g * a * g⁻¹ ≠ a := by
      intro h
      apply hgM
      rw [← hCa, Subgroup.mem_centralizer_singleton_iff]
      calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [h]
    have hs2 : orderOf (g * a * g⁻¹) = 2 := by
      rw [← orderOf_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩ : IsConj a (g * a * g⁻¹)), ← z_eq_a]
      exact orderOf_eq_prime (by rw [sq]; exact z_mul_self) z_ne_one
    have key := sup_centralizer_a_eq_top hK hs2 hne
    rw [eq_top_iff, ← key, sup_le_iff, hCa]
    refine ⟨hF.le, ?_⟩
    rw [centralizer_conj, hCa]
    rintro _ ⟨v, hv, rfl⟩
    exact F.mul_mem (F.mul_mem hgF (hF.le hv)) (F.inv_mem hgF)

theorem th_sup_centralizer_eq_top
    (t₁ t₂ : Blueprint.NativeSporadic.Th) (h₁ : orderOf t₁ = 2)
    (h₂ : orderOf t₂ = 2) (hne : t₁ ≠ t₂) :
    Subgroup.centralizer ({t₁} : Set Blueprint.NativeSporadic.Th) ⊔
      Subgroup.centralizer {t₂} = ⊤ := by
  set e := thEquivJ
  have key := sup_centralizer_eq_top th_kernel_facts (t₁ := e t₁) (t₂ := e t₂)
    (by rw [MulEquiv.orderOf_eq]; exact h₁) (by rw [MulEquiv.orderOf_eq]; exact h₂)
    (fun h => hne (e.injective h))
  have hc : ∀ t : Blueprint.NativeSporadic.Th,
      Subgroup.centralizer ({t} : Set Blueprint.NativeSporadic.Th) =
        (Subgroup.centralizer ({e t} : Set J)).comap (e : Blueprint.NativeSporadic.Th →* J) := by
    intro t
    ext u
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul, e.injective.eq_iff]
  rw [hc, hc, Subgroup.comap_sup_eq (f := (e : Blueprint.NativeSporadic.Th →* J)) _ _ e.surjective,
    key, Subgroup.comap_top]

end CFSG.Sporadic.Th
