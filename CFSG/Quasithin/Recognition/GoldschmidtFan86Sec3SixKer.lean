module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SixEnd

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable {F : FanTree Γ G}

theorem comm_mem_nbrStab (F : FanTree Γ G) (L : LocalFacts F) {u v : V} (huv : Γ.Adj u v) :
    ∀ s ∈ nbrStab Γ G v, ∀ t ∈ nbrStab Γ G v, s * t * s⁻¹ * t⁻¹ ∈ nbrStab Γ G u := by
  have hS : nbrStab Γ G v ≤ MulAction.stabilizer G u ⊓ MulAction.stabilizer G v :=
    fun k hk => ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk u huv.symm),
      F.nbrStab_le_stabilizer v hk⟩
  obtain ⟨g, hgS, -, hgen⟩ := L.cyc huv (nbrStab Γ G v) hS
  exact comm_mem_of_cyclic_gen (nbrStab Γ G u) (nbrStab Γ G v)
    (fun k hk => F.mem_normalizer_nbrStab (hS hk).1) hgS hgen

theorem mem_normalizer_left (L : LocalFacts F) {a₁ a₂ a₃ a₄ : V} (h12 : Γ.Adj a₁ a₂)
    (h23 : Γ.Adj a₂ a₃)
    (hNR : nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≤ nbrStab Γ G a₄) {k : G}
    (hk : k ∈ nbrStab Γ G a₂) :
    k ∈ Subgroup.normalizer
      ((nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ : Subgroup G) : Set G) := by
  have key : ∀ k ∈ nbrStab Γ G a₂, ∀ m ∈ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄,
      k * m * k⁻¹ ∈ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ := by
    intro k hk m hm
    have hm2 : m ∈ nbrStab Γ G a₂ := hm.1.1
    have hc1 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₁ := F.comm_mem_nbrStab L h12 k hk m hm2
    have hc3 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₃ := F.comm_mem_nbrStab L h23.symm k hk m hm2
    have hc2 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₂ :=
      (nbrStab Γ G a₂).mul_mem ((nbrStab Γ G a₂).mul_mem ((nbrStab Γ G a₂).mul_mem hk hm2)
        ((nbrStab Γ G a₂).inv_mem hk)) ((nbrStab Γ G a₂).inv_mem hm2)
    have hc4 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₄ := hNR ⟨⟨hc1, hc2⟩, hc3⟩
    have e : k * m * k⁻¹ = (k * m * k⁻¹ * m⁻¹) * m := by group
    rw [e]
    exact ⟨⟨(nbrStab Γ G a₂).mul_mem hc2 hm.1.1, (nbrStab Γ G a₃).mul_mem hc3 hm.1.2⟩,
      (nbrStab Γ G a₄).mul_mem hc4 hm.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key k hk y, fun hy => ?_⟩
  have := key k⁻¹ ((nbrStab Γ G a₂).inv_mem hk) _ hy
  simpa [mul_assoc] using this

theorem mem_normalizer_right (L : LocalFacts F) {a₂ a₃ a₄ a₅ : V} (h34 : Γ.Adj a₃ a₄)
    (h45 : Γ.Adj a₄ a₅)
    (hNL : nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ⊓ nbrStab Γ G a₅ ≤ nbrStab Γ G a₂) {k : G}
    (hk : k ∈ nbrStab Γ G a₄) :
    k ∈ Subgroup.normalizer
      ((nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ : Subgroup G) : Set G) := by
  have key : ∀ k ∈ nbrStab Γ G a₄, ∀ m ∈ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄,
      k * m * k⁻¹ ∈ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ := by
    intro k hk m hm
    have hm4 : m ∈ nbrStab Γ G a₄ := hm.2
    have hc3 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₃ := F.comm_mem_nbrStab L h34 k hk m hm4
    have hc5 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₅ := F.comm_mem_nbrStab L h45.symm k hk m hm4
    have hc4 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₄ :=
      (nbrStab Γ G a₄).mul_mem ((nbrStab Γ G a₄).mul_mem ((nbrStab Γ G a₄).mul_mem hk hm4)
        ((nbrStab Γ G a₄).inv_mem hk)) ((nbrStab Γ G a₄).inv_mem hm4)
    have hc2 : k * m * k⁻¹ * m⁻¹ ∈ nbrStab Γ G a₂ := hNL ⟨⟨hc3, hc4⟩, hc5⟩
    have e : k * m * k⁻¹ = (k * m * k⁻¹ * m⁻¹) * m := by group
    rw [e]
    exact ⟨⟨(nbrStab Γ G a₂).mul_mem hc2 hm.1.1, (nbrStab Γ G a₃).mul_mem hc3 hm.1.2⟩,
      (nbrStab Γ G a₄).mul_mem hc4 hm.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key k hk y, fun hy => ?_⟩
  have := key k⁻¹ ((nbrStab Γ G a₄).inv_mem hk) _ hy
  simpa [mul_assoc] using this

theorem le_ballStab_of_both (L : LocalFacts F) (h40 : Fan40 F) {a₁ a₂ a₃ a₄ a₅ : V}
    (h12 : Γ.Adj a₁ a₂) (h23 : Γ.Adj a₂ a₃) (h34 : Γ.Adj a₃ a₄) (h45 : Γ.Adj a₄ a₅)
    (h24 : a₂ ≠ a₄)
    (hNR : nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≤ nbrStab Γ G a₄)
    (hNL : nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ⊓ nbrStab Γ G a₅ ≤ nbrStab Γ G a₂) :
    nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ ballStab Γ G 2 a₃ := by
  set M := nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ with hM
  obtain ⟨g₁, hg₁2, hg₁3⟩ : ∃ g ∈ nbrStab Γ G a₂, g ∉ nbrStab Γ G a₃ :=
    Set.not_subset.1 (F.not_nbrStab_le_nbrStab h40 h23)
  obtain ⟨g₂, hg₂4, hg₂3⟩ : ∃ g ∈ nbrStab Γ G a₄, g ∉ nbrStab Γ G a₃ :=
    Set.not_subset.1 (F.not_nbrStab_le_nbrStab h40 h34.symm)
  have hg₁α : g₁ ∈ MulAction.stabilizer G a₃ :=
    MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg₁2 a₃ h23)
  have hg₂α : g₂ ∈ MulAction.stabilizer G a₃ :=
    MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg₂4 a₃ h34.symm)
  have hg₁u : g₁ • a₂ = a₂ := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer a₂ hg₁2)
  have hg₂w : g₂ • a₄ = a₄ := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer a₄ hg₂4)
  have hg₁w : g₁ • a₄ ≠ a₄ := fun h =>
    hg₁3 (F.fix_two_nbrs h23.symm h34 h24 hg₁u h)
  have hg₂u : g₂ • a₂ ≠ a₂ := fun h =>
    hg₂3 (F.fix_two_nbrs h23.symm h34 h24 h hg₂w)
  have hcl : Subgroup.closure ({g₁, g₂} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact F.mem_normalizer_left L h12 h23 hNR hg₁2
    · exact F.mem_normalizer_right L h34 h45 hNL hg₂4
  rw [hM]
  intro y hy
  rw [F.mem_ballStab_two_iff]
  refine ⟨hy.1.2, fun γ hγ => ?_⟩
  obtain ⟨m, hm, -, hma⟩ := F.transitive_of_two_fixers h23.symm h34 h24 hg₁α hg₂α hg₁u hg₁w hg₂w
    hg₂u h23.symm hγ
  have hmy : m⁻¹ * y * m ∈ M := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hcl hm)) y).1 hy
    simpa using this
  have := (F.mem_nbrStab_smul_iff m a₂ (h := y)).2 hmy.1.1
  rwa [hma] at this

theorem le_ballStab_of_left (L : LocalFacts F) (h40 : Fan40 F) {a₁ a₂ a₃ a₄ : V}
    (h12 : Γ.Adj a₁ a₂) (h23 : Γ.Adj a₂ a₃) (h34 : Γ.Adj a₃ a₄) (h24 : a₂ ≠ a₄)
    (ha2 : pval Γ a₂ = 3)
    (hc : (nbrStab Γ G a₃).relIndex (MulAction.stabilizer G a₃ ⊓ MulAction.stabilizer G a₂) =
      pval Γ a₃ - 1)
    (hNR : nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≤ nbrStab Γ G a₄) :
    nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ ballStab Γ G 2 a₃ := by
  intro y hy
  rw [F.mem_ballStab_two_iff]
  refine ⟨hy.1.2, fun γ hγ => ?_⟩
  by_cases hγ2 : γ = a₂
  · rw [hγ2]
    exact hy.1.1
  obtain ⟨k, hk, hka⟩ := F.exists_mem_nbrStab_smul_eq h23 ha2
    (F.not_nbrStab_le_nbrStab h40 h23.symm) hc h34 h24.symm hγ hγ2
  have hky : k⁻¹ * y * k ∈
      nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (F.mem_normalizer_left L h12 h23 hNR hk)) y).1
      hy
    simpa using this
  have := (F.mem_nbrStab_smul_iff k a₄ (h := y)).2 hky.2
  rwa [hka] at this

end FanTree

end CFSG.Quasithin.Fan86
