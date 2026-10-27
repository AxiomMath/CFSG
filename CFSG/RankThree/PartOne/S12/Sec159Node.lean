module

public import CFSG.RankThree.PartOne.S12.Sec159Aut
public import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec12FusChoice
public import CFSG.RankThree.PartOne.S12.Sec159Tools

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec159Node

variable {G : Type} [Group G]

theorem le_of_acts_trivially {p : ℕ} [Fact p.Prime] {E U V X N : Subgroup G} (hUE : U ≤ E)
    (hEp : IsPGroup p ↥E) (hVp : ¬ p ∣ Nat.card ↥V) (hUV : U ≤ Subgroup.normalizer (V : Set G))
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hVN : V ≤ N)
    (hU : ∀ u ∈ U, ∀ y ∈ X, u * y * u⁻¹ * y⁻¹ ∈ V)
    (hNU : Subgroup.normalizer (U : Set G) ≤ N) : X ≤ N := by
  intro y hy
  obtain ⟨v, hv, hfix⟩ := Sec159.exists_fixed_in_coset (hEp.to_le hUE) hVp hUV (hXV hy)
    (fun u hu => hU u hu y hy)
  have hyv : y * v ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := hfix u hu
    calc u * (y * v) = u * (y * v) * u⁻¹ * u := by group
      _ = (y * v) * u := by rw [this]
  have h1 : y * v ∈ N := hNU (Subgroup.centralizer_le_normalizer _ hyv)
  have h2 := N.mul_mem h1 (N.inv_mem (hVN hv))
  simpa using h2

theorem card_dvd_of_isCyclic_exp {p : ℕ} {U : Subgroup G} (hcyc : IsCyclic ↥U)
    (hexp : ∀ u ∈ U, u ^ p = 1) : Nat.card ↥U ∣ p := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥U := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hexp g g.2))

variable {p : ℕ} {A c : _} {L E : Subgroup G}

omit [Finite G] in
theorem card_reflectionGroup_dvd {A : Subgroup G} {I : Subgroup G} (hEA : E = A)
    (hout : Outcome152 p E A I) : Nat.card ↥(reflectionGroup p E) ∣ 48 := by
  have h4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := Sec159Aut.card_perm_four
  have h48 : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
    rw [Nat.card_prod, h4]
    have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [this]
  rcases hout with h1 | h2 | h3 | h4' | h5
  · obtain ⟨f, -, -, -, ⟨e⟩, -, -⟩ := h1
    rw [Nat.card_congr e.toEquiv, h4]; norm_num
  · obtain ⟨f, -, -, -, ⟨e⟩, -, -⟩ := h2
    rw [Nat.card_congr e.toEquiv, h48]
  · obtain ⟨f, -, -, -, ⟨e⟩, -, -⟩ := h3
    rw [Nat.card_congr e.toEquiv, h48]
  · obtain ⟨f, -, -, -, ⟨e⟩, -, -⟩ := h4'
    rw [Nat.card_congr e.toEquiv, h48]
  · obtain ⟨f, -, -, -, -, -, hne, -⟩ := h5
    exact absurd hEA hne

omit [Finite G] in
theorem weyl154_perm_four {A : Subgroup G} {I : Subgroup G} (hEA : E = A)
    (hout : Outcome152 p E A I) {W₀ : Subgroup (MulAut ↥E)} (hW : Weyl154 p E W₀) :
    Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) := by
  rcases hW.2.2.1 with h4 | ⟨⟨e⟩⟩
  · exact h4
  · exfalso
    have h1 : Nat.card ↥W₀ ∣ Nat.card ↥(reflectionGroup p E) := Subgroup.card_dvd_of_le hW.2.1
    have h2 := h1.trans (card_reflectionGroup_dvd (p := p) hEA hout)
    have h5 : Nat.card ↥W₀ = 120 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rw [h5] at h2
    omega

variable [Finite G]

theorem exists_sylow (hp : p.Prime) (h155 : Node155) {A : Subgroup G} {X : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152 p E A (lieGenerated p E)) (hEA : E = A) :
    ∃ P : Subgroup G, IsSylowOf p P (X ⊔ E) ∧ E ≤ P ∧ P ≤ torusNormalizer E ∧ omegaOne p P = E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h := h15.h12
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEp : IsPGroup p ↥E := hEel.isPGroup p ↥E
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout hEQ hQW hQ
  have hle : E ≤ (X ⊔ E) ⊓ Subgroup.normalizer (E : Set G) := le_inf le_sup_right Subgroup.le_normalizer
  obtain ⟨Q₀, hQ0, hEQ⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hle hEp
  have hQM : IsSylowOf p Q₀ (X ⊔ E) := Sec15FA.sylow_of_torus_normalizer hJ hQ0 hEQ
  have hQW : Q₀ ≤ Subgroup.normalizer (E : Set G) := hQ0.1.trans inf_le_right
  obtain ⟨PW, hPW, hQPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hQW hQ0.2.1
  have hΩW : omegaOne p PW = E := by
    rcases h155 G p A c L E h15 hF hout PW hPW with hΩ | ⟨h5, -, -, -⟩
    · exact hΩ
    · obtain ⟨f, -, -, -, -, -, hne, -⟩ := h5
      exact absurd hEA hne
  refine ⟨Q₀, hQM, hEQ, hQW, le_antisymm ?_ ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hy, hy1⟩
    have : y ∈ omegaOne p PW := Subgroup.subset_closure ⟨hQPW hy, hy1⟩
    exact hΩW ▸ this
  · refine fun e he => Subgroup.subset_closure ⟨hEQ he, ?_⟩
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he

end Sec159Node

end CFSG.RankThree.PartOne
