module

public import CFSG.RankThree.GF2n.Stroth80.Sec73bOf72

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Stroth73aOm4BaseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ m ∈ M, m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) → m * t * m⁻¹ ∈ Z0

theorem stroth73aOm4_of_base (hZt : Sec7ZtStatement) (hZc : Sec7CentreMpStatement)
    (hb : Stroth73aOm4BaseStatement) : Stroth73aOm4Statement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 m hmM hmV
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hmQ : m ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hmM
  have key : ∀ x ∈ Z0, m * x * m⁻¹ ∈ Z0 := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · exact hQZ0 ((Subgroup.mem_normalizer_iff.mp hmQ x).mp hxQ)
    · obtain ⟨hR, hV⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 x hx hxQ
      have hxL : x ∈ LB M Q B := (hZc G M Q Z B hc n t hs Z0 hZ0 x hx).1
      have hs' : Sec7Hyp hc n x := hs.congr hxL hxQ hR hV
      have hno' : ¬ Conc71abcd hc n x := fun h => hno ((s73b_conc71abcd_congr hc hR hV).mp h)
      have hom' : OmegaMinusNat hc x 2 := (OmegaMinusNat_congr hc hR hV 2).mpr hom
      have hZ0' : IsCentrePre Z0 (Rt M (LB M Q B) x) Q := by
        rw [hR]
        exact hZ0
      have hmV' : m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z x : Set G) := by
        rw [hV]
        exact hmV
      exact hb G M Q Z B hc n x hs' hno' hom' Z0 hZ0' m hmM hmV'
  have hle : conjSubgroup m Z0 ≤ Z0 := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have h := key _ hy
    rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h
  have heq : conjSubgroup m Z0 = Z0 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  exact conjSubgroup_eq_self_iff.mp heq

end CFSG.RankThree.GF2n.Stroth80
