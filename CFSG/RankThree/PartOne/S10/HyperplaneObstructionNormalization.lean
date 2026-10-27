module

import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.PartOne.HyperplaneObstruction

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem commutator_mem_normalizer_thetaComponent {H : Type} [Group H] [Finite H]
    (he : evenRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Y : Subgroup H}
    (hY : Y ∈ thetaComponents p H) {s β : H} (hβ : ∃ k : ℕ, orderOf β = p ^ k) :
    ⁅s, β⁆ ∈ normalizer (Y : Set H) := by
  have hβY : β ∈ normalizer (Y : Set H) :=
    selected_prime_elements_normalize_theta_components.1 H he p hp hp3 β hβ Y hY
  have hY' : Y.map (MulAut.conj s⁻¹).toMonoidHom ∈ thetaComponents p H :=
    map_mulEquiv_mem_thetaComponents hp (MulAut.conj s⁻¹) hY
  have hβY' := Subgroup.mem_normalizer_iff.mp
    (selected_prime_elements_normalize_theta_components.1 H he p hp hp3 β hβ _ hY')
  have hmem : ∀ x : H, x ∈ Y.map (MulAut.conj s⁻¹).toMonoidHom ↔ s * x * s⁻¹ ∈ Y := by
    intro x
    rw [Subgroup.mem_map_equiv]
    simp
  have hsβ : s * β * s⁻¹ ∈ normalizer (Y : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := hβY' (s⁻¹ * h * s)
    rw [hmem, hmem] at h1
    have e1 : s * (s⁻¹ * h * s) * s⁻¹ = h := by group
    have e2 : s * (β * (s⁻¹ * h * s) * β⁻¹) * s⁻¹ = (s * β * s⁻¹) * h * (s * β * s⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  have e : ⁅s, β⁆ = (s * β * s⁻¹) * β⁻¹ := commutatorElement_def s β
  rw [e]
  exact mul_mem hsβ (inv_mem hβY)

theorem commutator_le_normalizer_of_mem_thetaComponentsAt {G : Type} [Group G] [Finite G]
    (he : evenRank G ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {b : G} {X W B : Subgroup G}
    (hX : X ∈ thetaComponentsAt p b) (hWb : W ≤ Subgroup.centralizer ({b} : Set G))
    (hBb : B ≤ Subgroup.centralizer ({b} : Set G)) (hB : IsPGroup p B) :
    ⁅W, B⁆ ≤ normalizer (X : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have heC : evenRank C ≤ 3 := (Sec9A.evenRank_subgroup_le C).trans he
  obtain ⟨X', hX', rfl⟩ := hX
  rw [Subgroup.commutator_le]
  intro s hs β hβ
  have hord : ∃ k : ℕ, orderOf (⟨β, hBb hβ⟩ : C) = p ^ k := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hB ⟨β, hβ⟩
    exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact (Subgroup.orderOf_coe (⟨β, hβ⟩ : B)).trans hk⟩
  have h := commutator_mem_normalizer_thetaComponent heC hp hp3 hX' (s := ⟨s, hWb hs⟩) hord
  exact Subgroup.le_normalizer_map C.subtype ⟨_, h, rfl⟩

theorem commutator_le_theta_of_commutator_eq_self {G : Type*} [Group G] {p : ℕ}
    {X R B : Subgroup G} (hBX : B ≤ normalizer (X : Set G)) (hRX : R ≤ normalizer (X : Set G))
    (hRB : ⁅R, B⁆ = R) (hXB : ⁅X, B⁆ ≤ inSubgroup (aschbacherSolvableCore p) X) :
    ⁅R, X⁆ ≤ inSubgroup (aschbacherSolvableCore p) X := by
  set M := normalizer (X : Set G) with hM
  set φ := thetaQuotientConj p X with hφ
  have hBker : B.subgroupOf M ≤ φ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker, hφ, thetaQuotientConj_eq_one_iff]
    intro k hk
    have h1 : ⁅k, (b : G)⁆ ∈ ⁅X, B⁆ :=
      Subgroup.commutator_mem_commutator hk (Subgroup.mem_subgroupOf.mp hb)
    have h2 := Subgroup.inv_mem _ (hXB h1)
    have e : (⁅k, (b : G)⁆)⁻¹ = (b : G) * k * (b : G)⁻¹ * k⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [e] at h2
  have hRn : R.subgroupOf M = ⁅R.subgroupOf M, B.subgroupOf M⁆ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRX,
      Subgroup.map_subgroupOf_eq_of_le hBX, hRB]
  have hRker : R.subgroupOf M ≤ φ.ker :=
    hRn.le.trans ((Subgroup.commutator_mono le_top hBker).trans
      (Subgroup.commutator_le_right _ _))
  rw [Subgroup.commutator_le]
  intro r hr x hx
  exact (thetaQuotientConj_eq_one_iff p X ⟨r, hRX hr⟩).mp
    (hRker (Subgroup.mem_subgroupOf.mpr hr)) x hx

end CFSG.RankThree.PartOne.HyperplaneObstruction
