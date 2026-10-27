module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sup_le_normalizer {L S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer hSL

theorem c134Q_le_pCoreOf {L S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    c134Q (L ⊔ S) L ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := pCoreOf 2 (L ⊔ S) with hA
  have hAn : L ⊔ S ≤ Subgroup.normalizer (A : Set G) := le_normalizer_pCoreOf 2 (L ⊔ S)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le 2 (L ⊔ S)).trans (sup_le_normalizer hSL)
  have hcommL : ⁅A, L⁆ ≤ L := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have h1 : a * l * a⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hAL ha) l).mp hl
      simpa using (Subgroup.mem_normalizer_iff.mp (hAL ha) l).mp hl
    have e : ⁅a, l⁆ = (a * l * a⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hcommA : ⁅A, L⁆ ≤ A := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have h1 : l * a⁻¹ * l⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hAn (Subgroup.mem_sup_left hl)) a⁻¹).mp (A.inv_mem ha)
    have e : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact A.mul_mem ha h1
  have hp : IsPGroup 2 ↥(⁅A, L⁆) := (pCoreOf_isPGroup 2 (L ⊔ S)).to_le hcommA
  have hnorm : L ≤ Subgroup.normalizer ((⁅A, L⁆ : Subgroup G) : Set G) := fun l hl =>
    SBd5.mem_normalizer_commutator_of (hAn (Subgroup.mem_sup_left hl))
      (Subgroup.le_normalizer hl)
  exact le_pCoreOf_of_le_normalizer 2 hcommL hnorm hp

theorem c134Q_eq_of_comm_self {L S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hQ : ⁅c134Q (L ⊔ S) L, L⁆ = c134Q (L ⊔ S) L) :
    c134Q (L ⊔ S) L = ⁅pCoreOf 2 L, L⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · calc c134Q (L ⊔ S) L = ⁅c134Q (L ⊔ S) L, L⁆ := hQ.symm
      _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono (c134Q_le_pCoreOf hSL) le_rfl
  · have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
        (pCoreOf_isPGroup 2 L)
      intro x hx
      have hxL : x ∈ Subgroup.normalizer (L : Set G) := sup_le_normalizer hSL hx
      have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 L hxL
      exact hxO
    exact Subgroup.commutator_mono hle le_rfl

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_of_mem {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have e : g * (g⁻¹ * l * g) * g⁻¹ = l := by group
      exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * l * g)).mpr (by rw [e]; exact hl)
    have h1 := hx _ hl'
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * l := by group
  · intro hx h hh
    have h1 := hx _ ((Subgroup.mem_normalizer_iff.mp hg h).mp hh)
    have e1 : g * (h * x) * g⁻¹ = g * (x * h) * g⁻¹ := by
      calc g * (h * x) * g⁻¹ = (g * h * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * h * g⁻¹) := h1
        _ = g * (x * h) * g⁻¹ := by group
    simpa using e1

omit [Finite G] in
theorem normalizer_le_normalizer_c134CQ {L S : Subgroup G}
    (hQ : c134Q (L ⊔ S) L = ⁅pCoreOf 2 L, L⁆) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (c134CQ (L ⊔ S) L : Set G) := by
  intro g hg
  have hQn : g ∈ Subgroup.normalizer ((c134Q (L ⊔ S) L : Subgroup G) : Set G) := by
    rw [hQ]
    exact SBd5.mem_normalizer_commutator_of (normalizer_le_normalizer_pCoreOf 2 L hg) hg
  have hCn : g ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_centralizer_of_mem hg
  rw [Subgroup.mem_normalizer_iff] at hQn hCn ⊢
  intro x
  unfold c134CQ
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hQn x, hCn x]

end Stellmacher.CD.L3YC

end CFSG.Quasithin
