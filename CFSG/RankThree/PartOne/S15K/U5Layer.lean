module

public import CFSG.RankThree.PartOne.S15K.U5Model
public import CFSG.RankThree.PartOne.S15K.AutBlock

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_autLayerFamily {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {β : MulAut (primeFormP h (idGram K 5))} (hβD : β ∈ primeFormD h (idGram K 5)) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) :
    ∃ (ι : Type) (F : ι → Subgroup (primeFormP h (idGram K 5))),
      AutLayerFamily p β
        {α | α ∈ primeFormD h (idGram K 5) ∧ α * β = β * α ∧ α ^ p = 1} F := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) hpq
    omega
  have hq3 : 3 < 2 ^ f := by omega
  obtain ⟨g, hg⟩ : β ∈ (primeFormConjHom h (idGram K 5)).range := hβD
  have hgp1 : primeFormConjHom h (idGram K 5) (g ^ p) = 1 := by rw [map_pow, hg, hβp]
  obtain ⟨c, hc, hgc⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq3 (g ^ p)).mp hgp1
  have hgp : (g : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c := by
    rw [← Subgroup.coe_pow]; exact hgc
  have hg1 : ¬ ∃ d : Kˣ, d ^ (2 ^ f + 1) = 1 ∧
      (g : GL (Fin 5) K) = GeneralLinearGroup.scalar (Fin 5) d := by
    rintro ⟨d, hd, hgd⟩
    apply hβ1
    rw [← hg]
    exact (primeFormConjHom_eq_one_iff (by norm_num) hq3 g).mpr ⟨d, hd, hgd⟩
  have HU := unitaryPrimaryData_of_pow_scalar h hp hp2 g hgp
  have hπa : ∀ w, idPi h (idConj h g w) = β (idPi h w) := fun w => by
    rw [idPi_idConj, hg]
  have hdata : ∀ a : BlockIdx (toLinU h 5 g), ∃ μ : K, (a.1 : K[X]) = X - C μ ∧ h.bar μ * μ = 1 ∧
      (∃ v : Fin 5 → K, v ∉ primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
        (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) ∧
      Module.finrank K (primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
        (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) < p := by
    intro a
    obtain ⟨μ, hax, -, hμ⟩ := linear_of_mult_two h hp hp5 hpq g hc hgp _ rfl a.1 a.2
    have hnot := exists_not_mem_primaryComponent hμ hg1
    refine ⟨μ, hax, hμ, hnot, ?_⟩
    obtain ⟨v, hv⟩ := hnot
    have h1 := Submodule.finrank_lt (s := primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
        (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) (fun h' => hv (by rw [h']; trivial))
    have h2 : Module.finrank K (Fin 5 → K) = 5 := by simp
    omega
  refine ⟨BlockIdx (toLinU h 5 g), fun a => (blockSU h g a).map (idPi h), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a
    exact (isComponent_map_block_aut (idPi_surjective h) (ker_idPi_le_center h) hπa
      (isQuasisimple_blockSU HU hq4 a) (blockSU_le_fixed a)
      (fun w hw u hu => conj_mem_blockSU a hw hu)).1
  · intro a
    exact (isComponent_map_block_aut (idPi_surjective h) (ker_idPi_le_center h) hπa
      (isQuasisimple_blockSU HU hq4 a) (blockSU_le_fixed a)
      (fun w hw u hu => conj_mem_blockSU a hw hu)).2
  · intro Y hY hYp
    exact le_iSup_map_of_isPerfect (idPi_surjective h) (ker_idPi_le_center h) hπa
      (idConj_fix_ker h g) (blockSU h g) (derived_fixed_le_iSup HU hq4) hY
      (Subgroup.isPerfect_iff.1 hYp)
  ·
    intro α hα a
    obtain ⟨hαD, hαβ, hαp⟩ := hα
    obtain ⟨A, hA⟩ : α ∈ (primeFormConjHom h (idGram K 5)).range := hαD
    obtain ⟨μ, hax, hμ, hnot, -⟩ := hdata a
    have hcomm : primeFormConjHom h (idGram K 5) A * primeFormConjHom h (idGram K 5) g =
        primeFormConjHom h (idGram K 5) g * primeFormConjHom h (idGram K 5) A := by
      rw [hA, hg]; exact hαβ
    obtain ⟨lam, hlam, hEnd⟩ := exists_twist h hq3 g A hcomm
    have hlam1 : lam = 1 := twist_eq_one h hp hp5 hpq g A hc hgp _ rfl a.1 a.2 hEnd
    have hAx : Commute ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) := by
      rw [hlam1] at hEnd
      simp only [Units.val_one, one_smul] at hEnd
      exact hEnd
    have hAp1 : primeFormConjHom h (idGram K 5) (A ^ p) = 1 := by rw [map_pow, hA, hαp]
    obtain ⟨c₀, hc₀, hAc⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq3 (A ^ p)).mp hAp1
    have hAp : (A : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c₀ := by
      rw [← Subgroup.coe_pow]; exact hAc
    obtain ⟨w₀, hw₀, hconj⟩ :=
      exists_inner_blockSU HU hq4 a hax hμ hp hp5 hpq A hnot hAx hc₀ hAp
    refine ⟨idPi h w₀, Subgroup.mem_map_of_mem _ hw₀, ?_⟩
    rintro _ ⟨w', hw', rfl⟩
    rw [← hA, ← idPi_idConj, hconj w' hw', map_mul, map_mul, map_inv]
  ·
    intro a u hu hc hup
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨μ, hax, hμ, hnot, hmlt⟩ := hdata a
    have hcomm : ∀ w' ∈ blockSU h g a, w * w' = w' * w := by
      intro w' hw'
      have h1 : idPi h w * idPi h w' = idPi h w' * idPi h w :=
        hc _ (Subgroup.mem_map_of_mem _ hw')
      have h2 : w * w' * (w' * w)⁻¹ ∈ (idPi h).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel]
      have h3 : w * w' * (w' * w)⁻¹ ∈ blockSU h g a :=
        mul_mem (mul_mem hw hw') (inv_mem (mul_mem hw' hw))
      exact mul_inv_eq_one.mp (eq_one_of_mem_blockSU_of_mem_ker HU a hax hμ hnot h3 h2)
    have hwp : w ^ p = 1 :=
      eq_one_of_mem_blockSU_of_mem_ker HU a hax hμ hnot (pow_mem hw p)
        (by rw [MonoidHom.mem_ker, map_pow]; exact hup)
    have := eq_one_of_central_blockSU HU hq4 a hax hμ hp hmlt hw hcomm hwp
    rw [this, map_one]

end CFSG.RankThree.PartOne.S15K
