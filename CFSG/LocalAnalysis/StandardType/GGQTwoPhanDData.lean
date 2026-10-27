module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.MainB

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

@[expose] def GGSecFivePhanDQTwoSystemInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        ∀ (m : ℕ) (e' : Fin m ≃ ι), 4 ≤ m → M = (ggCoxeterMatrixD m).reindex e' →
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
        GGSecFiveData p B x L D J ∨
          ∃ (U : Fin m → Subgroup G) (W : Fin m → Fin m → Subgroup G),
            QTwoWeakPhanSystemD (GaloisField 2 2) m (ggG0 p B x L D J) U W

theorem ggSecFiveData_of_qTwoWeakPhanSystemD
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 4 ≤ m) {H : Subgroup G}
    {U : Fin m → Subgroup G} {W : Fin m → Fin m → Subgroup G}
    (hsys : QTwoWeakPhanSystemD K m H U W) (hH : H = ggG0 p B x L D J)
    (hB : GHNSMainBQTwo) :
    GGSecFiveData p B x L D J := by
  have hne : ggG0 p B x L D J ≠ ⊥ := by
    rw [← hH]
    exact hsys.ne_bot (by omega)
  rcases Nat.even_or_odd m with hmEven | hmOdd
  · obtain ⟨ψ, hrange⟩ := (hB K m hm H U W hsys).1 hmEven
    have hU : ggU .POmegaPlus m 1 =
        ⟨spinGroup (quadPlus m (GaloisField 2 1)),
          plusDatum m (GaloisField 2 1) (by omega : 3 ≤ m)⟩ := by
      simp only [ggU, lieUniversal, show 3 ≤ m by omega, ↓reduceDIte]
    let e : (ggU .POmegaPlus m 1).K ≃* ↥(spinGroup (quadPlus m (GaloisField 2 1))) :=
      MulEquiv.cast (M := fun U : LieUniversal => U.K) hU
    have hrange' : (ψ.comp e.toMonoidHom).range = ggG0 p B x L D J := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, Subgroup.map_top]
      exact hrange.trans hH
    exact ggSecFiveData_of_psi_POmegaPlus_one hm (ψ.comp e.toMonoidHom) hrange' hne
  · obtain ⟨ψ, hrange⟩ := (hB K m hm H U W hsys).2 hmOdd
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 (minusCoeffs_irr 2 1)
    have hU : ggU .POmegaMinus m 1 =
        ⟨spinGroup (quadMinus m (GaloisField 2 1) (minusCoeffs 2 1).1
            (minusCoeffs 2 1).2), minusDatum m (minusCoeffs_irr 2 1)⟩ := rfl
    let e : (ggU .POmegaMinus m 1).K ≃*
        ↥(spinGroup (quadMinus m (GaloisField 2 1) (minusCoeffs 2 1).1
          (minusCoeffs 2 1).2)) :=
      MulEquiv.cast (M := fun U : LieUniversal => U.K) hU
    have hrange' : (ψ.comp e.toMonoidHom).range = ggG0 p B x L D J := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, Subgroup.map_top]
      exact hrange.trans hH
    exact ggSecFiveData_of_psi_POmegaMinus_one hm (ψ.comp e.toMonoidHom) hrange' hne

theorem ggSecFiveDataResPhanDQTwoInput_of_parts
    (hB : GHNSMainBQTwo) (hSys : GGSecFivePhanDQTwoSystemInput) :
    GGSecFiveDataResPhanDQTwoInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hNotReg hs ι M e hpres hDm h6
  obtain ⟨m, e', hm, hM⟩ := hDm
  rcases hSys G p B Bs x L D J 𝒦 hcfg hNotReg hs ι M e hpres m e' hm hM h6 with
    h | ⟨U, W, hUW⟩
  · exact h
  · exact ggSecFiveData_of_qTwoWeakPhanSystemD hm hUW rfl hB

end CFSG.StandardType.QTwo

end
