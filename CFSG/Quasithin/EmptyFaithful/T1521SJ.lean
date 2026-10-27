module

public import CFSG.Quasithin.EmptyFaithful.T1521SAux
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.EmptyFaithful.T1521SDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def innerPart1521 (S L : Subgroup G) : Subgroup G :=
  (S ⊓ L) ⊔ (S ⊓ Subgroup.centralizer (L : Set G))

theorem innerPart1521_le (S L : Subgroup G) : innerPart1521 S L ≤ S :=
  sup_le inf_le_left inf_le_left

theorem borel_le_normalizer_innerPart (S L : Subgroup G) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (innerPart1521 S L : Set G) := by
  have hcn : S ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hc.2 y hy.2
    exact Subgroup.centralizer_le_normalizer _ hc'
  have hnorm : ∀ b ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G),
      ∀ x ∈ innerPart1521 S L, b * x * b⁻¹ ∈ innerPart1521 S L := by
    intro b hb x hx
    have hx' : x ∈ ((S ⊓ L : Subgroup G) : Set G) * ((S ⊓ Subgroup.centralizer (L : Set G) :
        Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (S ⊓ L) _ hcn]
      exact hx
    obtain ⟨a, ha, c, hc, rfl⟩ := hx'
    have hbc : b * c * b⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.mp hc.2 b hb.1
      calc b * c * b⁻¹ = (c * b) * b⁻¹ := by rw [this]
        _ = c := by group
    have hba : b * a * b⁻¹ ∈ S ⊓ L := (Subgroup.mem_normalizer_iff.mp hb.2 a).mp ha
    have e : b * (a * c) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹) := by group
    rw [e, hbc]
    exact Subgroup.mul_mem_sup hba hc
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hnorm b hb x hx, fun hx => ?_⟩
  have hb' : b⁻¹ ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).inv_mem hb
  have := hnorm b⁻¹ hb' _ hx
  simpa [mul_assoc] using this

variable [Finite G]

theorem borel_le_normalizer_thompsonJ_of_le {S L : Subgroup G}
    (hJ : thompsonJ S ≤ innerPart1521 S L) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (thompsonJ S : Set G) := by
  intro b hb
  have h1 := borel_le_normalizer_innerPart S L hb
  have h2 := normalizer_le_normalizer_thompsonJ (innerPart1521 S L) h1
  rw [B6.thompsonJ_eq_of_le hJ (innerPart1521_le S L)] at h2
  exact h2

theorem nrm1521_of_inner {S L : Subgroup G} (hJ : thompsonJ S ≤ innerPart1521 S L)
    (hAut : ∀ v ∈ S, v ∈ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)), v * b = b * v) →
      ∀ l ∈ L, v * l = l * v) : Nrm1521 S L :=
  ⟨oTwoUpper (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)),
    (oTwoUpper_le _).trans le_conjJoin,
    (oTwoUpper_le _).trans (borel_le_normalizer_thompsonJ_of_le hJ),
    oTwoUpper_oTwoUpper1521 _, hAut⟩

end CFSG.Quasithin
