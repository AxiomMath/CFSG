module

public import CFSG.Quasithin.Vol2.Ch11SecBK10C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

namespace BK10

variable {G : Type} [Group G]

theorem mem_map_conj_iff {t x : G} {K : Subgroup G} :
    x ∈ K.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * x * t ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

section Sup

variable {J M : Subgroup G}

theorem exists_mul_of_mem_sup (hJM : J ≤ Subgroup.normalizer (M : Set G)) {z : G}
    (hz : z ∈ J ⊔ M) : ∃ j : ↥J, ∃ m ∈ M, z = j * m := by
  have h : z ∈ ((J ⊔ M : Subgroup G) : Set G) := hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J M hJM] at h
  obtain ⟨j, hj, m, hm, rfl⟩ := h
  exact ⟨⟨j, hj⟩, m, hm, rfl⟩

theorem piX_eq_of_mul_eq (hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1) {j j' : ↥J}
    {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) (h : (j : G) * m = j' * m') :
    piX J j = piX J j' := by
  have h1 : ((j'⁻¹ * j : ↥J) : G) = m' * m⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (j' : G)⁻¹ * j = (j' : G)⁻¹ * (j * m) * m⁻¹ := by group
      _ = m' * m⁻¹ := by rw [h]; group
  have h2 : piX J (j'⁻¹ * j) = 1 :=
    hJMK _ (j'⁻¹ * j).2 (by rw [h1]; exact M.mul_mem hm' (M.inv_mem hm))
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

@[expose] noncomputable def projSupFun (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (z : ↥(J ⊔ M)) : XCls J :=
  piX J (exists_mul_of_mem_sup hJM z.2).choose

theorem projSupFun_eq (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1) {z : ↥(J ⊔ M)} {j : ↥J} {m : G}
    (hm : m ∈ M) (hz : (z : G) = j * m) : projSupFun hJM z = piX J j := by
  obtain ⟨m', hm', h'⟩ := (exists_mul_of_mem_sup hJM z.2).choose_spec
  exact piX_eq_of_mul_eq hJMK hm' hm (h'.symm.trans hz)

@[expose] noncomputable def projSup (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1) : ↥(J ⊔ M) →* XCls J where
  toFun := projSupFun hJM
  map_one' := by
    rw [projSupFun_eq hJM hJMK (j := 1) M.one_mem (by simp), map_one]
  map_mul' z w := by
    obtain ⟨j₁, m₁, hm₁, h₁⟩ := exists_mul_of_mem_sup hJM z.2
    obtain ⟨j₂, m₂, hm₂, h₂⟩ := exists_mul_of_mem_sup hJM w.2
    have hm : (j₂ : G)⁻¹ * m₁ * j₂ * m₂ ∈ M := by
      refine M.mul_mem ?_ hm₂
      have := (Subgroup.mem_normalizer_iff.mp (hJM (J.inv_mem j₂.2)) m₁).mp hm₁
      simpa [mul_assoc] using this
    rw [projSupFun_eq hJM hJMK hm₁ h₁, projSupFun_eq hJM hJMK hm₂ h₂,
      projSupFun_eq hJM hJMK (j := j₁ * j₂) hm (by
        simp only [Subgroup.coe_mul, h₁, h₂]
        group), map_mul]

theorem projSup_eq (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1) {z : ↥(J ⊔ M)} {j : ↥J} {m : G}
    (hm : m ∈ M) (hz : (z : G) = j * m) : projSup hJM hJMK z = piX J j :=
  projSupFun_eq hJM hJMK hm hz

theorem projSup_of_mem (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1) {z : G} (hz : z ∈ J) :
    projSup hJM hJMK ⟨z, Subgroup.mem_sup_left hz⟩ = piX J ⟨z, hz⟩ :=
  projSup_eq hJM hJMK M.one_mem (by simp)

theorem conj_mem_sup (hJM : J ≤ Subgroup.normalizer (M : Set G)) {g : G}
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G))
    {z : G} (hz : z ∈ J ⊔ M) : g * z * g⁻¹ ∈ J ⊔ M := by
  obtain ⟨j, m, hm, rfl⟩ := exists_mul_of_mem_sup hJM hz
  have h1 : g * (j * m) * g⁻¹ = (g * j * g⁻¹) * (g * m * g⁻¹) := by group
  rw [h1]
  exact (J ⊔ M).mul_mem
    (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hgJ j).mp j.2))
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgM m).mp hm))

theorem conj_mem_sup_of_swap (hJM : J ≤ Subgroup.normalizer (M : Set G)) {g : G}
    (hgJ : ∀ x ∈ J, g * x * g⁻¹ ∈ M) (hgM : ∀ x ∈ M, g * x * g⁻¹ ∈ J) {z : G} (hz : z ∈ J ⊔ M) :
    g * z * g⁻¹ ∈ J ⊔ M := by
  obtain ⟨j, m, hm, rfl⟩ := exists_mul_of_mem_sup hJM hz
  have h1 : g * (j * m) * g⁻¹ = (g * j * g⁻¹) * (g * m * g⁻¹) := by group
  rw [h1]
  exact (J ⊔ M).mul_mem (Subgroup.mem_sup_right (hgJ j j.2)) (Subgroup.mem_sup_left (hgM m hm))

theorem projSup_conj (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1) {g : G}
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G))
    (z : ↥(J ⊔ M)) :
    projSup hJM hJMK ⟨g * z * g⁻¹, conj_mem_sup hJM hgJ hgM z.2⟩ =
      rhoX J ⟨g, hgJ⟩ (projSup hJM hJMK z) := by
  obtain ⟨j, m, hm, hz⟩ := exists_mul_of_mem_sup hJM z.2
  rw [projSup_eq hJM hJMK hm hz, rhoX_piX]
  refine projSup_eq hJM hJMK ((Subgroup.mem_normalizer_iff.mp hgM m).mp hm) ?_
  change g * (z : G) * g⁻¹ = g * j * g⁻¹ * (g * m * g⁻¹)
  rw [hz]
  group

end Sup

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
