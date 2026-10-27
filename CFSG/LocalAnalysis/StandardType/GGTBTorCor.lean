module

public import CFSG.LocalAnalysis.StandardType.GGTBTorItems

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusNoFixTB_of_torW {p r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)}
    (hnb : ∀ k, ∃ j, C j k = -1) {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusTorW p r m N C M R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A →
        ∀ a ∈ A, (∀ n : L', GGTorusWeylElt p A n →
          MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1 := by
  intro L' _ _ ψ A hTB a ha hfix
  have hA : IsElemAbelian p A := hTB.2.2.2.1
  obtain ⟨w, hw⟩ := h L' ψ A hTB
  have hAT := hw.2.1
  have hαmul := hw.2.2.2.1
  have hpair := hw.2.2.2.2.2.2.2.1
  have hWaut := hw.2.2.2.2.2.2.2.2.1
  have hsep := hw.2.2.2.2.2.2.2.2.2.2.1
  refine hsep a (hAT ha) fun k => ?_
  have h1 := hfix (w.n k) (w.weylElt hw hA k)
  rw [hWaut k a (hAT ha)] at h1
  have h2 : MulAut.conj (w.cor k (w.α k a)) = 1 := inv_eq_one.mp (mul_eq_left.mp h1)
  obtain ⟨j, hj⟩ := hnb k
  have h3 := hpair j k (w.α k a)
  rw [h2, ggTor_alpha_one w.T (w.α j) (hαmul j), hj, zpow_neg_one] at h3
  exact inv_eq_one.mp h3.symm

end CFSG.StandardType
