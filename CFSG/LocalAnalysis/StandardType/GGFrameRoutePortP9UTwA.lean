module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U8
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1Trans
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U5

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

theorem twoLocalPrimeRank_le_of_bmax_le {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) {n : ℕ} (hcard : Nat.card Bs = 3 ^ n) :
    CFSG.Open.twoLocalPrimeRank 3 G ≤ n := by
  unfold LargeEvenIsBmax LargeEvenTwoLocalRank at hB
  obtain ⟨-, hBcard, -⟩ := hB
  have hle : 3 ^ CFSG.Open.twoLocalPrimeRank 3 G ≤ 3 ^ n := by
    rw [← hBcard, ← hcard]
    exact Subgroup.card_le_of_le hBBs
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle

open CFSG.ClassicalGroups.UnitaryFlag in
theorem P9_U_twA_false
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {m : ℕ} (hm : 3 ≤ m) {n : ℕ} (hn : n = 7 ∨ n = 8) {K : Subgroup G}
    {ψ : K →* LargeEvenProj (unitarySU 2 1 F m)} {A : Subgroup (MulAut K)}
    (hTB : GGTorusTBGroup 3 (n - 1) (LargeEvenProj (unitarySU 2 1 F m))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1))) K ψ A)
    (hAr : Nat.card A = 3 ^ (n - 1))
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G)) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (h2loc : CFSG.Open.twoLocalPrimeRank 3 G ≤ n)
    (W : Subgroup (MulAut ↥A)) (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) A)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) : False := by
  have hm1 : (n - 1) + 1 ≤ m := P9_U1t_succ_le (r := n - 1) hF hm hTB hAr
  have hm7 : 7 ≤ m := by omega
  have hu5 : m - 2 ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
    P9_U5a_sub_two_le_of_cover hF (by omega) (by omega) hTB.1 hTB.2.1 hTB.2.2.1 hz hz1 hz3
  have hmle : m ≤ n - 1 + 3 := by omega
  obtain ⟨hdim, hdvd⟩ := P9_U_dim_and_card_dvd hF (by omega) (by omega) hmle hTB hAr
  rcases hn with rfl | rfl
  · have hm7' : m = 7 := by
      rcases hdim with h | ⟨h3, h8⟩
      · omega
      · rw [h8] at h3
        norm_num at h3
    rw [hm7'] at hdvd
    exact P9_Wa_unitary_n7_false hW (by simpa using hWord) hdvd
  · have hm89 : m = 8 ∨ m = 9 := by
      rcases hdim with h | ⟨-, h⟩
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact P9_Wa_unitary_n8_false hm89 hW (by simpa using hWord) hdvd

theorem P9_Wa_twA_false
    {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → lab.tag = .twA ∧ lab.n = 1) (hK : GGInnerDiagOnLabel S 3 Bs K)
    (h2loc : CFSG.Open.twoLocalPrimeRank 3 G ≤ n)
    (W : Subgroup (MulAut ↥(ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) : False := by
  obtain ⟨k, F, hfield, hfin, θ, -, hF, hk, hTB, hrk⟩ :=
    P9_Wa_tbGroup_twA hBs hcard hn hz hz1 hN hker hBstar hS hK
  letI := hfield
  letI := hfin
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
    have hmem : z ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hker]
      exact Subgroup.mem_zpowers z
    exact (Subgroup.mem_inf.mp hmem).2
  have hz3 : z ^ 3 = 1 := hBs.2 z hz
  exact P9_U_twA_false hF (by omega) hn hTB hrk hzK hz1 hz3 h2loc W hW hWord

end CFSG.StandardType.FrameRoute

end
