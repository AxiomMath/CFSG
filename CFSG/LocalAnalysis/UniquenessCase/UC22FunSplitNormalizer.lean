module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitNormalizerAssembly
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOddCoreFrontier

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ComponentClassification.AS81.Sec2
open scoped Pointwise


theorem normalizes_fundamental_of_permuting
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p f : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : LieModel X t n p f) (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) (B : Subgroup X) (_hB : B ≠ ⊥)
    (hBab : IsMulCommutative B) (hBo : Odd (Nat.card B))
    (hB3 : ¬ 3 ∣ Nat.card B) (hBp : ¬ p ∣ Nat.card B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (hrank : ∀ s : ℕ, s.Prime → s ∣ Nat.card B →
      pRank s B ≤ 2 ∧ pRank s (⊤ : Subgroup X) ≤ 3)
    (K : Subgroup X) (hK : K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    B ≤ normalizer (K : Set X) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, _, hL2, hΩ⟩ := fundamental_ambient_of_lieModel hp hp2 hadm hX hA1 hK.1
  let H : Subgroup X := B ⊔ (P : Subgroup X)
  have hHsolv : Group.IsSolvable H :=
    isSolvable_of_eq_sup hBab hBo P.isPGroup' rfl hperm
  have hH3 : ¬ 3 ∣ Nat.card H :=
    not_three_dvd_card_of_eq_sup hBo P.isPGroup' rfl hperm hB3
  have hfix : ∀ J ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      ∀ z : X, CFSG.ClassicalInvolution.Generic.IsUniqueInvolution J z →
        ∀ o ∈ (classicalInvolutionOddCore H).map H.subtype, o * z = z * o := by
    intro J hJ z hz
    exact oddCore_commutes_fundamental_involution_of_permuting hp hp2 hadm hX hA1 hRee
      P B hBab hBo hB3 hBp (fun r hr hdvd => (hrank r hr hdvd).1) hperm hJ hz
  have hpres := mapsTo_funSet_of_oddCore_fixes_involutions hp2 hL2 hΩ P H le_sup_right
    hHsolv hH3 hfix
  have hBpres : ∀ b ∈ B, Set.MapsTo (Subgroup.map (MulAut.conj b).toMonoidHom)
      (FunSet (fundPred (p ^ f)) X (P : Subgroup X))
      (FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :=
    fun b hb => hpres b ((le_sup_left : B ≤ H) hb)
  have hconj : ∀ (g : X) {J : Subgroup X},
      fundPred (p ^ f) ⊤ J → fundPred (p ^ f) ⊤ (J.map (MulAut.conj g).toMonoidHom) :=
    fun g _ hJ => isFundamentalOver_map_mulEquiv (MulAut.conj g) hJ
  by_cases htwo : FunTwoType t n
  · obtain ⟨N, hNnormal, hN2, ⟨eN⟩⟩ :=
      F14.funSet_action_twoKernel_quotient_of_funTwoType X t n p f hp hp2 hadm hX htwo P
    let := hNnormal
    exact F14.le_normalizer_funSet_of_preserves_of_quotient_perm hconj P B hBpres
      hBo hB3 hperm (Fin 1) N hN2 eN K hK
  by_cases hsmall : (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard ≤ 4
  · let Δ := FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    let T := conjSetStab Δ
    have hBT : B ≤ T := F14.le_conjSetStab_of_mapsTo_conj hBpres
    have hbot := funSet_action_eq_bot_of_ncard_le_four Δ B hBT hBo hB3 hsmall
    intro b hb
    have hbT : (⟨b, hBT hb⟩ : T) ∈ B.subgroupOf T := hb
    have himage := Subgroup.mem_map_of_mem (conjPermHom (le_refl T)) hbT
    rw [hbot, Subgroup.mem_bot] at himage
    exact (conjPermHom_eq_one_iff (le_refl T) _).mp himage K hK
  rcases funSet_action_twoKernel_quotient_of_four_lt hp hp2 hadm hX hA1 hRee P hK htwo
      (Nat.lt_of_not_ge hsmall) with
    ⟨m, N, hNnormal, hN2, ⟨eN⟩⟩ | ⟨N, hNnormal, hN2, hNsimple, hNcard⟩
  · let := hNnormal
    exact F14.le_normalizer_funSet_of_preserves_of_quotient_perm hconj P B hBpres
      hBo hB3 hperm (Fin m) N hN2 eN K hK
  · let := hNnormal
    let := hNsimple
    exact F14.le_normalizer_funSet_of_preserves_of_quotient_card_168 hNcard hconj P B hBpres
      hBo hB3 hperm N hN2 (MulEquiv.refl _) K hK

end CFSG.LocalAnalysis.UniquenessCase.UC22
