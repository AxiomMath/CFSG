module

public import CFSG.Adapters.LinearFieldTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp

public section

namespace CFSG.Quasithin.E9P2L

open CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

variable {X : Type} [Group X] {n : ℕ}

theorem one_le_of_sp4_model (h : StatedClassicalModel X .PSp 2 2 n) : 1 ≤ n :=
  h.1.2.1

theorem nonempty_mulEquiv_symplectic_of_model (h : StatedClassicalModel X .PSp 2 2 n) :
    Nonempty (X ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 n))) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : K ≃+* GaloisField 2 n :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 n hadm.2.1 hK
  have e2 : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 (GaloisField 2 n)) :=
    statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
      (glCongr_statedScalars φ)
  exact ⟨(e.trans e2).trans (CFSG.QuasithinUnique.Lin2.Five.projEquivSymplectic _)⟩

theorem center_eq_bot_of_sp4_model (h : StatedClassicalModel X .PSp 2 2 n) :
    Subgroup.center X = ⊥ := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (f := n) ?_
    rw [← Nat.card_eq_fintype_card, hK]
  exact CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv e

end CFSG.Quasithin.E9P2L
