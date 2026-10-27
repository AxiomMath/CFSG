module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

abbrev theta4 : Fin (Tag.rank .E7) → ℤ := ![0, 1, 1, 2, 2, 2, 1]

theorem isRoot_theta4 : IsRoot .E7 theta4 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk⟩ : ∃ k : Fin 126, (Tag.rootCertificate .E7).root k = theta4 := by
    decide +kernel
  rw [← hk]
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)

theorem theta4_mem_Perp : theta4 ∈ Perp :=
  perp_iff.2 ⟨isRoot_theta4, rfl⟩

@[expose] def Perp4 : Set (Fin (Tag.rank .E7) → ℤ) :=
  {β | β ∈ Perp ∧ MinData.toWeight β ⬝ᵥ theta4 = 0}

theorem mem_Perp4 {β : Fin (Tag.rank .E7) → ℤ} :
    β ∈ Perp4 ↔ β ∈ Perp ∧ MinData.toWeight β ⬝ᵥ theta4 = 0 := Iff.rfl

theorem Perp4_subset_Perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp4) : β ∈ Perp := hβ.1

end CFSG.RankThree.GF2n.Smith81.D6Spin
