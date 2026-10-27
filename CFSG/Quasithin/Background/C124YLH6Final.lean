module

public import CFSG.Quasithin.Background.C124YLH6Pkg
public import CFSG.Quasithin.Background.C124YLH6LiftMain
public import CFSG.Quasithin.Background.C124YLPack

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.C124.YL.A6
open scoped MatrixGroups

namespace HatCtx

variable {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K] [Finite K]
  {Γ₀ : Subgroup (GL (Fin 3) K)} {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : HatCtx K Γ₀ Ls U Z)

include C in
theorem card_Ls : Nat.card ↥Ls = 1080 := by
  obtain ⟨q, hq, hker3, -⟩ := C.exists_q
  rw [← card_hat hq hker3]
  exact (Nat.card_congr (Equiv.ofBijective C.π ⟨C.π_injective, C.real.1⟩)).symm

include C in
theorem exists_package {K1 : Subgroup (MulAut W)} (hK1 : K1 ≤ Ls) (hw : WOff U Z K1) :
    ∃ P1 Y1 : Subgroup (MulAut W), IsSylowTwoOf P1 Ls ∧ K1 ≤ P1 ∧
      (∀ B ≤ P1, WOff U Z B → B = K1) ∧ Package Ls Ls U Z K1 Y1 := by
  obtain ⟨K1', rfl⟩ : ∃ K1' : Subgroup ↥Γ₀, K1'.map C.phi = K1 :=
    ⟨K1.comap C.phi, C.map_comap_phi hK1⟩
  obtain ⟨hne, hc, hs, h4, h16, hst⟩ := C.model_facts hw
  obtain ⟨q, hq, hker3, hkc⟩ := C.exists_q
  have hφ := C.phi_injective
  have hK2 : IsPGroup 2 K1' := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
  obtain ⟨S, hS⟩ := hK2.exists_le_sylow
  have hΓ : Nat.card ↥Γ₀ = 1080 := card_hat hq hker3
  have hS8 : Nat.card (S : Subgroup ↥Γ₀) = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Sylow.card_eq_multiplicity, hΓ, Nat.factorization_def _ Nat.prime_two]
    have h3 : padicValNat 2 1080 = 3 := by decide +kernel
    rw [h3]
    norm_num
  obtain ⟨Y', hKY, hY60, hYA5, hYgen⟩ := exists_A5_of_hat q hq hker3 hkc h4 hc hs
  have hKcard : Nat.card (K1'.map C.phi) = 4 := by rw [Subgroup.card_map_of_injective hφ, h4]
  have hYcard : Nat.card (Y'.map C.phi) = 60 := by rw [Subgroup.card_map_of_injective hφ, hY60]
  refine ⟨(S : Subgroup ↥Γ₀).map C.phi, Y'.map C.phi, ?_, Subgroup.map_mono hS,
    fun B hB hwB => C.unique_in_sylow hS8 hS hw hB hwB, ?_⟩
  · refine isSylowTwoOf_of_card (C.map_phi_le _) (a := 3) (m := 135) ?_ ?_ (by norm_num)
    · rw [Subgroup.card_map_of_injective hφ, hS8]
      norm_num
    · rw [C.card_Ls]
      norm_num
  · refine ⟨C.map_phi_le _, hw, C.tight_model h4 h16, ?_, C.map_phi_le _,
      isSylowTwoOf_of_card (Subgroup.map_mono hKY) (a := 2) (m := 15)
        (by rw [hKcard]; norm_num) (by rw [hYcard]; norm_num) (by norm_num), ?_, ?_,
      C.gen_map hYgen⟩
    · intro x hx _ _ hfix
      exact C.cent_model hst hx hfix
    · obtain ⟨e5⟩ := hYA5
      obtain ⟨e2⟩ := sl2_equiv_alt_five (F := K) C.hK
      exact ⟨K, inferInstance, inferInstance, C.hK,
        ⟨((Subgroup.equivMapOfInjective Y' C.phi hφ).symm.trans e5).trans e2.symm⟩⟩
    · refine C.moves_model (Y' := Y') fun hle => ?_
      have := Subgroup.card_le_of_le hle
      rw [← hst, hY60, h4] at this
      omega

end HatCtx

end CFSG.Quasithin.C124.YL.H6
