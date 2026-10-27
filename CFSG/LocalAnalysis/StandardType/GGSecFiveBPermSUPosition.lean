module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGKGPosSUTableB
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

theorem ggSecFiveBPermSU_localHyp_of_centralImage {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} {i0 : Fin n}
    (hn : n = 4) (ha : 2 ≤ a) (hpa : p ∣ 2 ^ a - 1) (hK : K ∈ 𝒦)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {ψ₀ : (ggU .PSU 6 a).K →* G} (hker : ψ₀.ker ≤ Subgroup.center (ggU .PSU 6 a).K)
    (hrange : ψ₀.range = K) :
    GGKGPosLocalHypTw p Bs K .PSU 6 a ψ₀ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hBs : GGBstar p B Bs := hR.1.1.2.1
  obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hK
  have hInn : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hy
  obtain ⟨f, rfl⟩ : ∃ f, a = f + 1 := ⟨a - 1, by omega⟩
  let a := f + 1
  have hcardBs : Nat.card ↥Bs = p ^ 4 := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, Nat.card_fin, hn,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    ggSecFiveBPermSpK_card_inf_centralizer_le hp2 hA
  have hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs := by
    rw [hcardBs]
    calc p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p ^ 3 * p :=
          Nat.mul_le_mul_left _ hcent
      _ = p ^ 4 := (pow_succ p 3).symm
  have hadm : StatedLieAdmissible .PSU 6 2 a :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  exact ggKGPosLocalHypTw_of_innerDiagOn hMp hp hp2 hBs ha hpa
    (by norm_num [bnRank]) ψ₀ hadm hker hrange hInn hcard (by rw [hcardBs])

end CFSG.StandardType

end
