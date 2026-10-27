module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.V4Aut
public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem fixes_of_fixes_sub_and_quotient {N H : Subgroup G} (hNH : N ≤ H) (hN2 : IsPGroup 2 ↥N)
    {g : G} (hgH : g ∈ Subgroup.normalizer (H : Set G)) {m : ℕ} (hgm : g ^ 3 ^ m = 1)
    (hfix : ∀ n ∈ N, g * n * g⁻¹ = n) (hdisp : ∀ h ∈ H, h⁻¹ * (g * h * g⁻¹) ∈ N) :
    ∀ h ∈ H, g * h * g⁻¹ = h := by
  classical
  have hpow : actAut hgH ^ 3 ^ m = 1 := by
    rw [actAut_pow, actAut_eq_one_iff]
    intro x _
    rw [hgm]
    group
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hN2
  have hcard : Nat.card (N.subgroupOf H) = 2 ^ b := by
    rw [← hb]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hcop : (3 ^ m).Coprime (Nat.card (N.subgroupOf H)) := by
    rw [hcard]
    exact Nat.Coprime.pow m b (by norm_num)
  have h1 := CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
    (N.subgroupOf H) (actAut hgH) (3 ^ m) hpow hcop
    (fun n hn => Subtype.ext (hfix n hn))
    (fun h => hdisp h h.2)
  exact (actAut_eq_one_iff hgH).mp h1

end Stellmacher.L3YC

end CFSG.Quasithin
