module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNine
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.mem_centralizer_V₀_of_odd_of_mul_conj (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ)
    {x : G} (hxS : conjSubgroup V x ≤ S) {a : G} (ha : a ∈ conjSubgroup V x) {α : MulAut X}
    (hα : ∀ k k' : ↥(conjClosure V H), (k' : G) = a * k * a⁻¹ → α (φ k) = φ k')
    {P : Subgroup X} (hP : IsPGroup 2 P) {c : ↥(conjClosure V H)} (hodd : Odd (orderOf c))
    (hcV : φ c ∈ centralizer (SevenK.barSub (conjClosure V H) φ V : Set X))
    (hcP : α (φ c) * φ c ∈ P) : (c : G) ∈ centralizer (V₀ : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun x hx z hz =>
      H.mul_mem (H.mul_mem hx (hVH hz)) (H.inv_mem hx)
  have hcH : (c : G) ∈ H := hKH c.2
  have hcVbar : ∀ v ∈ V, (c : G) * v * (c : G)⁻¹ ∈
      V ⊔ pCoreOf 2 (conjClosure V H) := by
    intro v hv
    let vK : ↥(conjClosure V H) := ⟨v, CFSG.Quasithin.le_conjClosure V H hv⟩
    have hvbar : φ vK ∈ SevenK.barSub (conjClosure V H) φ V :=
      SevenK.mem_barSub.mpr ⟨vK, hv, rfl⟩
    have hcomm : φ vK * φ c = φ c * φ vK :=
      (Subgroup.mem_centralizer_iff.mp hcV) (φ vK) hvbar
    have hker : φ (c * vK * c⁻¹ * vK⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    have hp : ((c * vK * c⁻¹ * vK⁻¹ : ↥(conjClosure V H)) : G) ∈
        pCoreOf 2 (conjClosure V H) := (hφ.ker_iff _).mp hker
    have hp' : (c : G) * v * (c : G)⁻¹ * v⁻¹ ∈
        pCoreOf 2 (conjClosure V H) := by
      simpa [vK] using hp
    have heq : (c : G) * v * (c : G)⁻¹ =
        ((c : G) * v * (c : G)⁻¹ * v⁻¹) * v := by group
    rw [heq, ← sup_comm]
    exact Subgroup.mul_mem_sup hp' hv
  have hcM : (c : G) ∈ M :=
    Cex16.mem_of_conj_le_sup h1 h5 hS h hH.1 hV hQ hcH hcVbar
  have hcNorm : (c : G) ∈ normalizer (V₀ : Set G) := by
    rw [h.hyp.normalizer₀]
    exact hcM
  have hSx : conjSubgroup V x ≤ centralizer (V : Set G) :=
    Cex16.conj_le_centralizer_of_le_S h1 hS h hxS
  have haCentV : a ∈ centralizer (V : Set G) := hSx ha
  have haCent : a ∈ centralizer (V₀ : Set G) :=
    (Subgroup.centralizer_le h.hyp.h6.le) haCentV
  have haH : a ∈ H := hH.1.1 (hxS ha)
  have haNormK : a ∈ normalizer (conjClosure V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure V H haH
  have haca : a * (c : G) * a⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.mp haNormK (c : G)).mp c.2
  let k' : ↥(conjClosure V H) := ⟨a * (c : G) * a⁻¹, haca⟩
  have hαc : α (φ c) = φ k' := hα c k' rfl
  have hr_mem : a * (c : G) * a⁻¹ * (c : G) ∈ conjClosure V H :=
    (conjClosure V H).mul_mem haca c.2
  let rK : ↥(conjClosure V H) := ⟨a * (c : G) * a⁻¹ * (c : G), hr_mem⟩
  have hrK : rK = k' * c := rfl
  have hφr : φ rK = α (φ c) * φ c := by
    rw [hrK, map_mul, ← hαc]
  have hrP : φ rK ∈ P := by
    rw [hφr]
    exact hcP
  have hker_eq : φ.ker = (pCoreOf 2 (conjClosure V H)).subgroupOf
      (conjClosure V H) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  have hker : IsPGroup 2 φ.ker := by
    rw [hker_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure V H)).comap_subtype
  have hQ : IsPGroup 2 (P.comap φ) := hP.comap_of_ker_isPGroup φ hker
  have hrQ : rK ∈ P.comap φ := hrP
  obtain ⟨k, hk⟩ := hQ.exists_orderOf_eq_pow ⟨rK, hrQ⟩
  have h2 : ∃ n : ℕ, orderOf (a * (c : G) * a⁻¹ * (c : G)) = 2 ^ n := by
    refine ⟨k, ?_⟩
    simpa [rK, Subgroup.orderOf_mk] using hk
  exact mem_centralizer_of_odd_of_mul_conj (W := V₀) (a := a) (c := (c : G))
    haCent hcNorm (by simpa [Subgroup.orderOf_mk] using hodd) h2

end CFSG.LocalAnalysis.WeakClosure81

end
