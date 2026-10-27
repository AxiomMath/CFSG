module

public import CFSG.Quasithin.H13.U4ParModule
import CFSG.Sporadic.Recognition.LyonsAS44Frattini
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.Quasithin.F112R

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin
  CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private theorem sq_mem_zRad {g : hypSU h 2 0} (hg : g ∈ radQ h) : g ^ 2 ∈ zRad h := by
  have := h.charP
  obtain ⟨x, y, c, -, hg⟩ := hg
  have hsq : sMat h x y c ^ 2 = sMat h 0 0 (h.bar y * x + h.bar x * y) := by
    rw [sq, sMat_mul, CharTwo.add_self_eq_zero x, CharTwo.add_self_eq_zero y]
    congr 1
    grind
  refine ⟨h.bar y * x + h.bar x * y, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
    ring
  · rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, hsq]

private theorem sq_eq_one_of_mem_zRad {g : hypSU h 2 0} (hg : g ∈ zRad h) : g ^ 2 = 1 := by
  have := h.charP
  obtain ⟨c, -, hg⟩ := hg
  apply hypSU_ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, sq, sMat_mul]
  have hcc : c + c = 0 := CharTwo.add_self_eq_zero c
  rw [hcc]
  simp only [map_zero, zero_mul, add_zero]
  ext i j
  simp [sMat_apply]

theorem isSpecialPow_radQ : IsSpecialPow 2 (2 ^ m) 2 ↥(radQ h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := radQ h with hQ
  haveI : Finite (hypSU h 2 0) := finite_hypSU h
  haveI : Finite ↥Q := inferInstance
  have hP : IsPGroup 2 ↥Q := by rw [hQ]; exact radQ_isPGroup h
  have hcenter : Subgroup.center ↥Q = (zRad h).subgroupOf Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (zRad_le_radQ h), ← centerOf_radQ h]
    ext z
    simpa [CFSG.Quasithin.centerOf] using
      (CFSG.LocalCores.mem_map_center_iff (G := hypSU h 2 0) Q (g := z))
  have hmapcenter : (Subgroup.center ↥Q).map Q.subtype = zRad h := by
    rw [hcenter, Subgroup.map_subgroupOf_eq_of_le (zRad_le_radQ h)]
  have hcomm : commutator ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_subtype_commutator, commutator_radQ h, hmapcenter]
  have hsq_mem : ∀ a : ↥Q, a ^ 2 ∈ Subgroup.center ↥Q := by
    intro a
    rw [hcenter, Subgroup.mem_subgroupOf]
    simpa [Subgroup.coe_pow] using sq_mem_zRad h a.2
  have hfrattini : frattini ↥Q = Subgroup.center ↥Q := by
    haveI : (Subgroup.center ↥Q).Normal := inferInstance
    refine CFSG.Sporadic.Recognition.LyonsSims.frattini_eq_of_commutator_eq hP ?_ ?_
    · rw [← commutator_def]
      exact hcomm
    · exact hsq_mem
  have hcenterSq : ∀ z ∈ Subgroup.center ↥Q, z ^ 2 = 1 := by
    intro z hz
    rw [hcenter] at hz
    have hz' := Subgroup.mem_subgroupOf.mp hz
    exact Subtype.ext (by simpa [Subgroup.coe_pow] using sq_eq_one_of_mem_zRad h hz')
  have htop : radS h ⊤ = radQ h := by
    ext g
    simp [mem_radS]
  have htopcard : Nat.card (⊤ : Submodule h.fixedField K) = Nat.card K :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  have harith : (2 : ℕ) ^ (2 * m) * 2 ^ (2 * m) * 2 ^ m = (2 ^ m) ^ 5 := by
    rw [← pow_add, ← pow_add, ← pow_mul]
    congr 1
    omega
  have hcardQ : Nat.card ↥Q = (2 ^ m) ^ 5 := by
    rw [hQ, ← htop, card_radS h ⊤, htopcard, h.card]
    exact harith
  have hcardZ : Nat.card (Subgroup.center ↥Q) = 2 ^ m := by
    rw [hcenter, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zRad_le_radQ h)).toEquiv,
      card_zRad h]
  exact ⟨⟨hP, Or.inr ⟨hcomm, hfrattini, hcenterSq⟩⟩, hcardQ, hcardZ⟩

end CFSG.Quasithin.F112R
