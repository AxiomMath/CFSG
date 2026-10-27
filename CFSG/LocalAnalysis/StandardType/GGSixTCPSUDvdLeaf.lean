module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPairDeg

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem false_of_dvd_PSU
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .PSU n f).K →* X} (h : GGTCHyp .PSU n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSU f) (hp : p ∣ 2 ^ f + 1) : False := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := h.adm.2.1; omega⟩
  exact false_of_dvd_PSU_of_models h hF hp fun hb hself hJ'g hJ'm =>
    hb.two_le_blockDegree_of_dualPair (PSULiftHyp.of_ggTCHyp h) hself h.d_card h.j_cent hJ'g hJ'm hF

theorem false_of_not_dvd_PSU_of_hM2
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .PSU n f).K →* X} (h : GGTCHyp .PSU n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSU f) (hp : ¬ p ∣ 2 ^ f + 1) (hM2 : p ∣ Nat.card J) :
    False := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := h.adm.2.1; omega⟩
  exact false_of_not_dvd_PSU_of_models h hF hp (fun hb hself hJ'g hJ'm =>
    hb.two_le_blockDegree_of_dualPair (PSULiftHyp.of_ggTCHyp h) hself h.d_card h.j_cent hJ'g hJ'm
      hF) hM2

end CFSG.StandardType.TableCRes
