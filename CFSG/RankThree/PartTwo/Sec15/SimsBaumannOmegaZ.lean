module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannCases
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem sbomz_omegaOneCenterOf_le_centerOf (R : Subgroup X) :
    CFSG.Quasithin.omegaOneCenterOf R ≤ CFSG.Quasithin.centerOf R :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

omit [Finite X] in
private theorem sbomz_sq_eq_one {R : Subgroup X} {z : X}
    (hz : z ∈ CFSG.Quasithin.omegaOneCenterOf R) : z ^ 2 = 1 := by
  have hcomm : ∀ a ∈ CFSG.Quasithin.omegaOneCenterOf R, ∀ b ∈ CFSG.Quasithin.omegaOneCenterOf R,
      a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (sbomz_omegaOneCenterOf_le_centerOf R ha).2 b
      (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R hb)).symm
  unfold CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := hcomm x hx y hy
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

omit [Finite X] in
private theorem sbomz_normal_omegaOneCenterOf (R : Subgroup X) [R.Normal] :
    (CFSG.Quasithin.omegaOneCenterOf R).Normal := by
  have hR : Subgroup.normalizer (R : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr ‹R.Normal›
  have h := CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv
    (F := CFSG.Quasithin.omegaOneCenterOf) CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv R
  rw [hR] at h
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)

theorem concl315_of_commutator_eq_bot (hF : generalizedFitting X = CFSG.pCore 2 X)
    {A S : Subgroup X} (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (hX : Nontrivial X) (hWL : ⁅W315 X, oResidual 2 X⁆ = ⊥)
    (hnorm : (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).Normal) : Concl315 X S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : CFSG.pCore 2 X ≤ S := Push153.pCore_le_of_mem_maxInvariant hS
  have hQ1 : CFSG.pCore 2 X ≠ ⊥ := Push153.pCore_ne_bot_of_nontrivial hF
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hS1 : S ≠ ⊥ := fun h => hQ1 (eq_bot_iff.mpr (hQS.trans h.le))
  have hchar : IsCharacteristicP 2 X :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).mpr hF
  refine Or.inl ⟨CFSG.Quasithin.omegaOneCenterOf S,
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 hS1,
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S,
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S, ?_⟩
  have hCW : CFSG.Quasithin.omegaOneCenterOf S ≤
      CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hx' : x ∈ CFSG.Quasithin.centerOf S ∧ x ^ 2 = 1 := hx
    have hxC : x ∈ Subgroup.centralizer (S : Set X) := (Subgroup.mem_inf.mp hx'.1).2
    have hcx : x ∈ Subgroup.centralizer (CFSG.pCore 2 X : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh =>
        Subgroup.mem_centralizer_iff.mp hxC h (hQS hh)
    exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hchar hcx, hcx⟩, hx'.2⟩
  haveI hWn : (CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X)).Normal :=
    sbomz_normal_omegaOneCenterOf (CFSG.pCore 2 X)
  refine ⟨fun c hc g => ?_⟩
  have hcW : c ∈ CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X) := hCW hc
  have hcS : c ∈ Subgroup.centralizer (S : Set X) :=
    (Subgroup.mem_inf.mp (sbomz_omegaOneCenterOf_le_centerOf S hc)).2
  have hle : S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X ≤ Subgroup.centralizer ({c} : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hcS s hs
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWL hcW) l hl
    · intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (sbomz_omegaOneCenterOf_le_centerOf _ hcW)).2 q hq
  have hgcW : g * c * g⁻¹ ∈ CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X) :=
    hWn.conj_mem c hcW g
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hQS
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _ hgcW),
    Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩, sbomz_sq_eq_one hgcW⟩
  have hSN : S ≤ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X := le_sup_left.trans le_sup_left
  have ht : (g⁻¹ * s * g) * c = c * (g⁻¹ * s * g) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle (hnorm.conj_mem' s (hSN hs) g))
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [ht]
    _ = g * c * g⁻¹ * s := by group

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
