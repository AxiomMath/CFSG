module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteCard
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

noncomputable section

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem qtwoD5_join_type (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hBs : 3 ^ 5 ≤ Nat.card Bs)
    (hA : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) ≤ 1920) {y : G} {K : Subgroup G}
    (hK : GGNbr 3 B x D J y K) :
    (GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∧
        Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 720) ∨
      (GGWeylOfType 3 (ggCoxeterMatrixD 5) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∧
        Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 1920) := by
  classical
  let W : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  have hWeyl : GGWeylReflectionGroup 3 W :=
    hcfg.1.2.2.2.2.1 y K hK (hcfg.2.1 y K hK) (Or.inr hcfg.2.1)
  have hjoin : GGWeylReflectionGroup 3 (ggAutomizerJoin L Bs {K}) := by
    rwa [ggAutomizerJoin_singleton]
  have hcardW : Nat.card ↥W ≤ 1920 := by
    have hmax := hcfg.2.2.2.2.2 {K} (ggNbrSet_singleton hK) hjoin
    rw [ggAutomizerJoin_singleton] at hmax
    exact hmax.trans hA
  have hfix : ∀ b : ↥Bs, (∀ ψ ∈ W, ψ b = b) → b = 1 :=
    FrameRoute.eq_one_of_fix_join' hTBF hWI hcfg.1 hcfg.2.1 hK
  rcases ggWeylReflectionGroup_cases hWeyl with ⟨n, _, hAn⟩ | ⟨n, hn2, hBn⟩ |
    ⟨n, hn4, hDn⟩ | hE6 | hE7 | hE8 | hF4 | hG2
  · have hcard : Nat.card ↥W = (n + 1).factorial := CFSG.StandardType.ggWeylOfType_A_card hAn
    have hfac : (n + 1).factorial ≤ 1920 := by rw [← hcard]; exact hcardW
    have h5 : 5 ≤ n := by
      have h := SpJoinRefl.card_le_pow_of_weylOfType hAn hfix
      have h' : 3 ^ 5 ≤ 3 ^ n := hBs.trans (by simpa using h)
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h'
    have hnle : n ≤ 5 := by
      by_contra h
      have h7 : 7 ≤ n + 1 := by omega
      have hf : Nat.factorial 7 ≤ (n + 1).factorial := Nat.factorial_le h7
      have h7' : Nat.factorial 7 = 5040 := by norm_num
      rw [h7'] at hf
      omega
    have hn5 : n = 5 := by omega
    exact Or.inl ⟨hn5 ▸ hAn, by rw [hcard, hn5]; norm_num⟩
  · have h5 : 5 ≤ n := by
      have h := SpJoinRefl.card_le_pow_of_weylOfType hBn hfix
      have h' : 3 ^ 5 ≤ 3 ^ n := hBs.trans (by simpa using h)
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h'
    obtain ⟨e, -⟩ := hBn
    have hcard : Nat.card ↥W = 2 ^ n * n.factorial := by
      rw [← Nat.card_congr e.toEquiv]
      exact le_antisymm (CFSG.StandardType.card_coxeterB_le n)
        (CFSG.StandardType.SpFrame.card_coxeterB_ge n hn2)
    have hbig : 3840 ≤ 2 ^ n * n.factorial := by
      have hp : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
      have hf : Nat.factorial 5 ≤ n.factorial := Nat.factorial_le h5
      have h := Nat.mul_le_mul hp hf
      norm_num at h ⊢
      exact h
    have hle : 2 ^ n * n.factorial ≤ 1920 := by rw [← hcard]; exact hcardW
    omega
  · have h5 : 5 ≤ n := by
      have h := SpJoinRefl.card_le_pow_of_weylOfType hDn hfix
      have h' : 3 ^ 5 ≤ 3 ^ n := hBs.trans (by simpa using h)
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h'
    have hDn' := hDn
    obtain ⟨e, -⟩ := hDn
    have hcard : Nat.card ↥W = 2 ^ (n - 1) * n.factorial := by
      rw [← Nat.card_congr e.toEquiv]
      exact CFSG.StandardType.OrthF3.card_coxeterD_eq n hn4
    have hle : 2 ^ (n - 1) * n.factorial ≤ 1920 := by rw [← hcard]; exact hcardW
    have hnle : n ≤ 5 := by
      by_contra h
      have h6 : 6 ≤ n := by omega
      have hp : 2 ^ 5 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hf : Nat.factorial 6 ≤ n.factorial := Nat.factorial_le h6
      have hbig : 2 ^ 5 * Nat.factorial 6 ≤ 2 ^ (n - 1) * n.factorial :=
        Nat.mul_le_mul hp hf
      norm_num at hbig
      omega
    have hn5 : n = 5 := by omega
    exact Or.inr ⟨hn5 ▸ hDn', by rw [hcard, hn5]; norm_num⟩
  · obtain ⟨e, -⟩ := hE6
    have hcard : Nat.card ↥W = 51840 := by
      rw [← Nat.card_congr e.toEquiv]
      exact CFSG.StandardType.card_coxeterE6_group
    omega
  · obtain ⟨e, -⟩ := hE7
    have hcard : Nat.card ↥W = 2903040 := by
      rw [← Nat.card_congr e.toEquiv]
      exact CFSG.StandardType.card_coxeterE7_group
    omega
  · obtain ⟨e, -⟩ := hE8
    have hcard : Nat.card ↥W = 696729600 := by
      rw [← Nat.card_congr e.toEquiv]
      exact CFSG.StandardType.card_coxeterE8_group
    omega
  · have hle : Nat.card Bs ≤ 3 ^ 4 := by
      have h := SpJoinRefl.card_le_pow_of_weylOfType hF4 hfix
      simpa using h
    have h := hBs.trans hle
    norm_num at h
  · have hle : Nat.card Bs ≤ 3 ^ 2 := by
      have h := SpJoinRefl.card_le_pow_of_weylOfType hG2 hfix
      simpa using h
    have h := hBs.trans hle
    norm_num at h

end

end CFSG.StandardType.QTwo

end
