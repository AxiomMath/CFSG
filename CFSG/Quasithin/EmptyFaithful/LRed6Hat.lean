module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases1
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin

namespace LRed6

variable {V : Type} [CommGroup V]

theorem hat_conclusion {L : Subgroup (MulAut V)} (h : TripleA6Six L ⊤ ⊥) :
    F6.IsHatAlt 6 ↥L ∧ Nat.card V = 2 ^ 6 := by
  obtain ⟨K, hK, hKf, Γ₀, hK4, -, hhat, -, π, hπ⟩ := h
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  let e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hL : IsHat ↥L ↥(alternatingGroup (Fin 6)) := IsHat.of_mulEquiv e hhat
  refine ⟨⟨Insp9.open_of_isQuasisimple hL.1, hL.2.1, hL.2.2⟩, ?_⟩
  obtain ⟨e', -⟩ := B5.exists_linModel hπ
  have h1 : Nat.card ↥(⊤ : Subgroup V) = Nat.card (Multiplicative (Fin 3 → K)) :=
    Nat.card_congr e'.toEquiv
  rw [Subgroup.card_top] at h1
  rw [h1]
  change Nat.card (Fin 3 → K) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_fin, hK4]
  norm_num

end LRed6

end CFSG.Quasithin
