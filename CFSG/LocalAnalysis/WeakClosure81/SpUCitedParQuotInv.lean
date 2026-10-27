module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParQuotA
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParLattice

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G Q : Type} [Group G] [Group Q]

theorem spUCited_invariant_map [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : ¬ 2 ∣ Nat.card π.ker) {U R Pα : Subgroup G}
    (hU : IsPGroup 2 U) (hR : IsPGroup 2 R)
    (hBP : Subgroup.normalizer (U : Set G) ≤ Pα)
    (hcov : ∀ A : Subgroup G, Subgroup.normalizer (U : Set G) ≤ A → A ≤ Pα →
      A = Subgroup.normalizer (U : Set G) ∨ A = Pα)
    (hnot : ¬ Pα ≤ Subgroup.normalizer (R : Set G))
    (huniq : ∀ P' : Subgroup G, Subgroup.normalizer (U : Set G) ≤ P' →
      (∀ A : Subgroup G, Subgroup.normalizer (U : Set G) ≤ A → A ≤ P' →
        A = Subgroup.normalizer (U : Set G) ∨ A = P') →
      ¬ P' ≤ Subgroup.normalizer (R : Set G) → P' = Pα) :
    ∀ α : MulAut Q, Subgroup.map α.toMonoidHom (U.map π) = U.map π →
      Subgroup.map α.toMonoidHom (R.map π) = R.map π →
      Subgroup.map α.toMonoidHom (Pα.map π) = Pα.map π := by
  intro α hαU hαR
  have hNU : (Subgroup.normalizer (U : Set G)).map π =
      Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) :=
    spUCited_normalizer_map_of_ker π hπ hker hodd hU
  have hNR : (Subgroup.normalizer (R : Set G)).map π =
      Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q) :=
    spUCited_normalizer_map_of_ker π hπ hker hodd hR
  have hCU : (Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q)).comap π =
      Subgroup.normalizer (U : Set G) :=
    spUCited_comap_normalizer_map π hπ hker hodd hU
  have hCR : (Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q)).comap π =
      Subgroup.normalizer (R : Set G) :=
    spUCited_comap_normalizer_map π hπ hker hodd hR
  have hkerB : π.ker ≤ Subgroup.normalizer (U : Set G) :=
    hker.trans (Subgroup.center_le_normalizer (U : Set G))
  have hkerNR : π.ker ≤ Subgroup.normalizer (R : Set G) :=
    hker.trans (Subgroup.center_le_normalizer (R : Set G))
  have hkerP : π.ker ≤ Pα := hkerB.trans hBP
  have hBP' : Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ≤ Pα.map π := by
    rw [← hNU]
    exact Subgroup.map_mono hBP
  have hcov' : ∀ A : Subgroup Q, Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ≤ A →
      A ≤ Pα.map π →
      A = Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ∨ A = Pα.map π := by
    intro A hA hAP
    have hB : Subgroup.normalizer (U : Set G) ≤ A.comap π := by
      calc Subgroup.normalizer (U : Set G)
          ≤ (Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q)).comap π := by
            rw [← hNU]
            exact Subgroup.le_comap_map π (Subgroup.normalizer (U : Set G))
        _ ≤ A.comap π := Subgroup.comap_mono hA
    have hAP₀ : A.comap π ≤ Pα := by
      calc A.comap π ≤ (Pα.map π).comap π := Subgroup.comap_mono hAP
        _ = Pα := Subgroup.comap_map_eq_self hkerP
    rcases hcov (A.comap π) hB hAP₀ with h | h
    · left
      calc A = (A.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ A).symm
        _ = (Subgroup.normalizer (U : Set G)).map π := by rw [h]
        _ = Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) := hNU
    · right
      calc A = (A.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ A).symm
        _ = Pα.map π := by rw [h]
  have hnot' : ¬ Pα.map π ≤ Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q) := by
    intro h
    apply hnot
    calc Pα ≤ (Pα.map π).comap π := Subgroup.le_comap_map π Pα
      _ ≤ (Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q)).comap π :=
            Subgroup.comap_mono h
      _ = Subgroup.normalizer (R : Set G) := hCR
  have huniq' : ∀ P'' : Subgroup Q,
      Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ≤ P'' →
      (∀ A : Subgroup Q, Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ≤ A →
        A ≤ P'' →
        A = Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ∨ A = P'') →
      ¬ P'' ≤ Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q) → P'' = Pα.map π := by
    intro P'' hBP'' hcov'' hnot''
    have hB₀ : Subgroup.normalizer (U : Set G) ≤ P''.comap π := by
      calc Subgroup.normalizer (U : Set G)
          ≤ (Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q)).comap π := by
            rw [← hNU]
            exact Subgroup.le_comap_map π (Subgroup.normalizer (U : Set G))
        _ ≤ P''.comap π := Subgroup.comap_mono hBP''
    have hcov₀ : ∀ A : Subgroup G, Subgroup.normalizer (U : Set G) ≤ A → A ≤ P''.comap π →
        A = Subgroup.normalizer (U : Set G) ∨ A = P''.comap π := by
      intro A hBA hAP
      have hkerA : π.ker ≤ A := hkerB.trans hBA
      have hNA : Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q) ≤ A.map π := by
        rw [← hNU]
        exact Subgroup.map_mono hBA
      have hAP'' : A.map π ≤ P'' := by
        calc A.map π ≤ (P''.comap π).map π := Subgroup.map_mono hAP
          _ = P'' := Subgroup.map_comap_eq_self_of_surjective hπ P''
      rcases hcov'' (A.map π) hNA hAP'' with h | h
      · left
        calc A = (A.map π).comap π := (Subgroup.comap_map_eq_self hkerA).symm
          _ = (Subgroup.normalizer ((U.map π : Subgroup Q) : Set Q)).comap π := by rw [h]
          _ = Subgroup.normalizer (U : Set G) := hCU
      · right
        calc A = (A.map π).comap π := (Subgroup.comap_map_eq_self hkerA).symm
          _ = P''.comap π := by rw [h]
    have hnot₀ : ¬ P''.comap π ≤ Subgroup.normalizer (R : Set G) := by
      intro h
      apply hnot''
      calc P'' = (P''.comap π).map π :=
            (Subgroup.map_comap_eq_self_of_surjective hπ P'').symm
        _ ≤ (Subgroup.normalizer (R : Set G)).map π := Subgroup.map_mono h
        _ = Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q) := hNR
    calc P'' = (P''.comap π).map π :=
          (Subgroup.map_comap_eq_self_of_surjective hπ P'').symm
      _ = Pα.map π := by rw [huniq (P''.comap π) hB₀ hcov₀ hnot₀]
  exact spUCited_map_eq_of_unique_cover (U := U.map π) (R := R.map π) (P := Pα.map π)
    hBP' hcov' hnot' huniq' α hαU hαR

end CFSG.LocalAnalysis.WeakClosure81

end
