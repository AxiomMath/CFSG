module

public import CFSG.Quasithin.EmptyFaithful.SzN28S8Mod
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Data

variable {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V} {x : GLV V}
  (d : S8Data Γ A I I' x)

include d in
theorem S8Data.x_not_mem : x ∉ A := by
  intro hx
  have : Module.Finite (ZMod 2) I := Module.finite_of_finrank_pos (by rw [d.rank4]; omega)
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ I, i ≠ 0 := by
    have := Module.finrank_pos_iff_exists_ne_zero.1 (show 0 < Module.finrank (ZMod 2) I by
      rw [d.rank4]; omega)
    obtain ⟨⟨i, hi⟩, h0⟩ := this
    exact ⟨i, hi, fun h => h0 (Subtype.ext h)⟩
  have h1 : x i ∈ I := d.A_inv_I x hx i hi
  have h2 : x i ∈ I' := by rw [d.I'_eq]; exact ⟨i, hi, rfl⟩
  have h3 : x i ∈ I ⊓ I' := ⟨h1, h2⟩
  rw [d.compl.inf_eq_bot, Submodule.mem_bot] at h3
  have h4 : x (x i) = x 0 := by rw [h3]
  rw [d.xx_apply, map_zero] at h4
  exact hi0 h4

include d in
theorem S8Data.index_two : (A.subgroupOf Γ).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, d.x_mem⟩, fun b => ?_⟩
  by_cases hb : (b : GLV V) ∈ A
  · right
    refine ⟨hb, fun h => d.x_not_mem ?_⟩
    have h1 : (b : GLV V) * x ∈ A := h
    have h2 : (b : GLV V)⁻¹ * ((b : GLV V) * x) ∈ A := A.mul_mem (A.inv_mem hb) h1
    simpa using h2
  · left
    refine ⟨?_, hb⟩
    obtain ⟨a, ha, hba⟩ := d.outer b b.2 hb
    show (b : GLV V) * x ∈ A
    rw [hba, mul_assoc, d.x_sq, mul_one]
    exact ha

include d in
theorem S8Data.outer_I {γ : GLV V} (hγ : γ ∈ Γ) (hγA : γ ∉ A) {i : V} (hi : i ∈ I) : γ i ∈ I' := by
  obtain ⟨a, ha, rfl⟩ := d.outer γ hγ hγA
  show a (x i) ∈ I'
  exact d.A_inv_I' a ha (x i) (by rw [d.I'_eq]; exact ⟨i, hi, rfl⟩)

include d in
theorem S8Data.outer_I' {γ : GLV V} (hγ : γ ∈ Γ) (hγA : γ ∉ A) {j : V} (hj : j ∈ I') : γ j ∈ I := by
  obtain ⟨a, ha, rfl⟩ := d.outer γ hγ hγA
  rw [d.I'_eq] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  show a (x (x i)) ∈ I
  rw [d.xx_apply]
  exact d.A_inv_I a ha i hi

include d in
theorem S8Data.eq_of_add_eq {i₁ i₂ j₁ j₂ : V} (hi₁ : i₁ ∈ I) (hi₂ : i₂ ∈ I) (hj₁ : j₁ ∈ I')
    (hj₂ : j₂ ∈ I') (h : i₁ + j₁ = i₂ + j₂) : i₁ = i₂ ∧ j₁ = j₂ := by
  have h1 : i₁ - i₂ ∈ I ⊓ I' := ⟨I.sub_mem hi₁ hi₂, by
    have : i₁ - i₂ = j₂ - j₁ := by
      calc i₁ - i₂ = (i₁ + j₁) - (i₂ + j₂) + (j₂ - j₁) := by abel
        _ = j₂ - j₁ := by rw [h, sub_self, zero_add]
    rw [this]
    exact I'.sub_mem hj₂ hj₁⟩
  rw [d.compl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h1
  refine ⟨h1, ?_⟩
  rw [h1] at h
  exact add_left_cancel h

end Data

structure F8Form (B : LinearMap.BilinForm (ZMod 2) V) (Γ A : Subgroup (GLV V))
    (I I' : Submodule (ZMod 2) V) (x : GLV V) : Prop where
  data : S8Data Γ A I I' x
  alt : ∀ v, B v v = 0
  nondeg : ∀ v, (∀ w, B v w = 0) → v = 0
  isom : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w
  iso_I : ∀ w ∈ I, ∀ w' ∈ I, B w w' = 0

namespace F8Form

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
  {x : GLV V} (c : F8Form B Γ A I I' x)

include c in
theorem symm (v w : V) : B v w = B w v := by
  have h := c.alt (v + w)
  simp only [map_add, LinearMap.add_apply, c.alt v, c.alt w, zero_add, add_zero] at h
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact (key _ _ h).symm

include c in
theorem iso_I' : ∀ w ∈ I', ∀ w' ∈ I', B w w' = 0 := by
  intro w hw w' hw'
  rw [c.data.I'_eq] at hw hw'
  obtain ⟨i, hi, rfl⟩ := hw
  obtain ⟨j, hj, rfl⟩ := hw'
  show B (x i) (x j) = 0
  rw [c.isom x c.data.x_mem, c.iso_I i hi j hj]

include c in
theorem pair_I' {j : V} (hj : j ∈ I') (h : ∀ i ∈ I, B i j = 0) : j = 0 := by
  apply c.nondeg
  intro w
  have hw : w ∈ I ⊔ I' := by rw [c.data.compl.sup_eq_top]; trivial
  obtain ⟨i, hi, j', hj', rfl⟩ := Submodule.mem_sup.1 hw
  rw [c.symm j (i + j')]
  simp only [map_add, LinearMap.add_apply, h i hi, c.iso_I' j' hj' j hj, add_zero]

include c in
theorem v1_not_mem {v₁ : V} (hv₁ : v₁ ≠ 0) (hodd : Odd (MulAction.stabilizer Γ v₁).index) :
    v₁ ∉ I ∧ v₁ ∉ I' := by
  have key : (v₁ ∈ I ∨ v₁ ∈ I') → False := by
    intro hv
    have hle : MulAction.stabilizer Γ v₁ ≤ A.subgroupOf Γ := by
      intro g hg
      by_contra hgA
      have hgA' : (g : GLV V) ∉ A := hgA
      have hfix : (g : GLV V) v₁ = v₁ := hg
      have hmem : v₁ ∈ I ⊓ I' := by
        rcases hv with hv | hv
        · exact ⟨hv, by have := c.data.outer_I g.2 hgA' hv; rwa [hfix] at this⟩
        · exact ⟨by have := c.data.outer_I' g.2 hgA' hv; rwa [hfix] at this, hv⟩
      rw [c.data.compl.inf_eq_bot, Submodule.mem_bot] at hmem
      exact hv₁ hmem
    have h2 : 2 ∣ (MulAction.stabilizer Γ v₁).index := by
      have := Subgroup.index_dvd_of_le hle
      rwa [c.data.index_two] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

include c in
theorem exists_decomp {v₁ : V} (hv₁ : v₁ ≠ 0) (hodd : Odd (MulAction.stabilizer Γ v₁).index) :
    ∃ e₀ ∈ I, ∃ f₀ ∈ I', v₁ = e₀ + f₀ ∧ e₀ ≠ 0 ∧ f₀ ≠ 0 := by
  obtain ⟨hnI, hnI'⟩ := c.v1_not_mem hv₁ hodd
  have hw : v₁ ∈ I ⊔ I' := by rw [c.data.compl.sup_eq_top]; trivial
  obtain ⟨e₀, he, f₀, hf, hv⟩ := Submodule.mem_sup.1 hw
  refine ⟨e₀, he, f₀, hf, hv.symm, fun h => ?_, fun h => ?_⟩
  · apply hnI'
    rw [← hv, h, zero_add]
    exact hf
  · apply hnI
    rw [← hv, h, add_zero]
    exact he

include c in
theorem act_fix {γ : GLV V} (hγ : γ ∈ Γ) {e₀ f₀ : V} (he : e₀ ∈ I) (hf : f₀ ∈ I')
    (hfix : γ (e₀ + f₀) = e₀ + f₀) :
    (γ ∈ A ∧ γ e₀ = e₀ ∧ γ f₀ = f₀) ∨ (γ ∉ A ∧ γ e₀ = f₀ ∧ γ f₀ = e₀) := by
  rw [map_add] at hfix
  by_cases hγA : γ ∈ A
  · left
    obtain ⟨h1, h2⟩ := c.data.eq_of_add_eq (c.data.A_inv_I γ hγA e₀ he) he
      (c.data.A_inv_I' γ hγA f₀ hf) hf hfix
    exact ⟨hγA, h1, h2⟩
  · right
    have hfix' : γ f₀ + γ e₀ = e₀ + f₀ := by rw [add_comm, hfix]
    obtain ⟨h1, h2⟩ := c.data.eq_of_add_eq (c.data.outer_I' hγ hγA hf) he
      (c.data.outer_I hγ hγA he) hf hfix'
    exact ⟨hγA, h2, h1⟩

end F8Form

end CFSG.Quasithin.SzN28
