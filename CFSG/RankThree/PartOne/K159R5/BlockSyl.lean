module

public import CFSG.RankThree.PartOne.S15K.U5Model
public import CFSG.RankThree.PartOne.K159R5.SylTransfer
import CFSG.RankThree.PartOne.K159R5.SylGL

public section

namespace CFSG.RankThree.PartOne.K159R5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
open CFSG.RankThree.PartOne.S15K

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem sylAb_specialBlock {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    {g : ↥(idU h)} (HU : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 g)) {μ : K}
    (hax : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)))
    (hμ : h.bar μ * μ = 1)
    (hmlt : Module.finrank K (primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) < p) :
    SylAb p (specialBlock (idForm h 5) (toLinU h 5 g) (X - C μ)) := by
  classical
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  have hcard : Fintype.card K = 2 ^ (2 * f) := (Nat.card_eq_fintype_card (α := K)).symm.trans h.card
  have hpK : ¬ p ∣ Fintype.card K := by
    intro hdvd
    rw [hcard] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hK1 : Fintype.card K ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have h1 : ((2 ^ f + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h1
    have h2 : (2 : ZMod p) ^ f = -1 := eq_neg_of_add_eq_zero_left h1
    rw [hcard]
    push_cast
    rw [pow_mul', h2]
    exact neg_one_sq
  have hself := dualPoly_X_sub_C_eq h hμ
  have hsq := HU.squarefree
  set x : Module.End K (Fin 5 → K) :=
    ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) with hx
  set W := primaryComponent x (X - C μ) with hW
  have : FiniteDimensional K W := inferInstance
  obtain ⟨f', hf'⟩ := exists_injective_hom_GL_of_restrict
    (specialBlock (idForm h 5) (toLinU h 5 g) (X - C μ)) W (d := Module.finrank K W) rfl
    (fun g' hg' v hv => by
      have hc := (mem_unitaryCentralizer.mp (specialBlock_le_unitaryCentralizer hg')).2
      exact apply_mem_primaryComponent hc hv)
    (fun g' hg' hfix => by
      set π := primaryProjection x (X - C μ) with hπ
      have hππ : ∀ v, π (π v) = π v := fun v => by
        have := congrArg (fun T : Module.End K (Fin 5 → K) => T v)
          (primaryProjection_mul_self hsq hax)
        exact this
      refine Units.ext (LinearMap.ext fun v => ?_)
      have h1 : π (v - π v) = 0 := by rw [map_sub, hππ, sub_self]
      have h2 := fix_of_mem_orbitFactor HU hax hself (specialBlock_le_orbitFactor hg') h1
      have h3 := hfix (π v) (primaryProjection_mem hsq hax v)
      have h4 : v = π v + (v - π v) := by abel
      conv_lhs => rw [h4]
      rw [map_add, h3, h2]
      change π v + (v - π v) = v
      abel)
  exact SylAb.of_hom f' hf' (fun T hT => abelian_of_pGroup_GL hp1 hpK hK1 hmlt T hT)

theorem sylAb_blockSU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hq : 4 ≤ 2 ^ f)
    {g : ↥(idU h)} (HU : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 g))
    (a : BlockIdx (toLinU h 5 g)) {μ : K} (hax : (a.1 : K[X]) = X - C μ) (hμ : h.bar μ * μ = 1)
    (hmlt : Module.finrank K (primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) < p) :
    SylAb p (blockSU h g a) := by
  have h1 := sylAb_specialBlock h hp hp2 hpq HU (mem_primaryFactors_of_blockIdx a hax) hμ hmlt
  refine SylAb.of_map (idPhi h) (fun t _ _ ht => idPhi_injective h (by rw [ht, map_one])) ?_
  rw [map_blockSU HU hq a, hax]
  exact h1

theorem sylAb_map_blockSU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hq : 4 ≤ 2 ^ f)
    {g : ↥(idU h)} (HU : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 g))
    (a : BlockIdx (toLinU h 5 g)) {μ : K} (hax : (a.1 : K[X]) = X - C μ) (hμ : h.bar μ * μ = 1)
    (hnot : ∃ v : Fin 5 → K, v ∉ primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ))
    (hmlt : Module.finrank K (primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) < p) :
    SylAb p ((blockSU h g a).map (idPi h)) := by
  refine SylAb.map_of_injOn (idPi h) (fun x hx y hy hxy => ?_)
    (sylAb_blockSU h hp hp2 hpq hq HU a hax hμ hmlt)
  have hk : x⁻¹ * y ∈ (idPi h).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have := eq_one_of_mem_blockSU_of_mem_ker HU a hax hμ hnot
    (mul_mem (inv_mem hx) hy) hk
  exact inv_mul_eq_one.1 this

end CFSG.RankThree.PartOne.K159R5
