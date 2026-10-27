module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10Spor
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

@[expose] def K105SporAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X s →
    ∀ S H : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → S ≤ H → Group.IsSolvable ↥H →
      ¬ 3 ∣ Nat.card ↥H → H ≤ S

theorem k105Spor_of_forall (h : ∀ s : TauCeti.SporadicName, s ≠ .J1 → K105SporAt s) :
    K105Spor :=
  fun X _ _ s hs hX S H hS hSH hHs h3 => h s hs X hX S H hS hSH hHs h3

theorem k105SporAt_of_index {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ]
    {S₀ : Subgroup Γ} (hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf S₀ ⊤)
    (hidx : ∀ Z : Subgroup Γ, S₀ ≤ Z → Group.IsSolvable ↥Z → ∀ m : ℕ,
      Nat.card ↥Z = m * Nat.card ↥S₀ → m = 1 ∨ 3 ∣ m)
    (e : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ) : K105SporAt s := by
  intro X _ _ hX S H hS hSH hHs h3
  obtain ⟨e₀⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e₁ : X ≃* Γ := e₀.trans e
  obtain ⟨hp, hi⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp
    (CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e₁ hS)
  obtain ⟨hp₀, hi₀⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S₀ = (S.map e₁.toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  let ψ : X ≃* Γ := e₁.trans (MulAut.conj g)
  have hψ : S.map ψ.toMonoidHom = S₀ := by
    rw [hST, Subgroup.map_map]
    rfl
  have hSZ : S₀ ≤ H.map ψ.toMonoidHom := by
    rw [← hψ]
    exact Subgroup.map_mono hSH
  have hZs : Group.IsSolvable ↥(H.map ψ.toMonoidHom) :=
    Group.isSolvable_of_surjective (ψ.toMonoidHom.subgroupMap_surjective H)
  have hcH : Nat.card ↥(H.map ψ.toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective ψ.injective
  have hcS : Nat.card ↥S₀ = Nat.card ↥S := by
    rw [← hψ]
    exact Subgroup.card_map_of_injective ψ.injective
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hSZ
  rcases hidx _ hSZ hZs m (hm.trans (mul_comm _ _)) with rfl | h3m
  · rw [hcH, mul_one, hcS] at hm
    exact (Subgroup.eq_of_le_of_card_ge hSH hm.le).ge
  · refine absurd ?_ h3
    rw [← hcH, hm]
    exact Dvd.dvd.mul_left h3m _

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
