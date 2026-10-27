module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.lemma_3_1

public section

namespace CFSG.BenderSuzuki.External

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

noncomputable section

theorem suzukiRootClosure_center_data
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2) :
    let F : Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure {A | ∃ a b, A = SuzukiRootGL m a b}
    (∀ z ∈ Subgroup.center F, z ^ 2 = 1) ∧
      Nat.card (Subgroup.center F) = 2 ^ (2 * m + 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  change (∀ z ∈ Subgroup.center F, z ^ 2 = 1) ∧
    Nat.card (Subgroup.center F) = 2 ^ (2 * m + 1)
  rcases huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hu, hformula, _hFp, _hfour, _hord, _hclass, _hFcard, _hType,
      hmul, hcomm, hcoord, _htorus, _hconj, _hdisjoint, _hfree⟩
  have hcenter (z : F) : z ∈ Subgroup.center F ↔
      ∃ b : K, (z : GL (Fin 4) K) = SuzukiRootGL m 0 b := by
    rw [← hcomm]
    exact hcoord z
  have hrootmem (b : K) : SuzukiRootGL m 0 b ∈ F :=
    Subgroup.subset_closure ⟨0, b, rfl⟩
  let param : K → Subgroup.center F := fun b =>
    ⟨⟨SuzukiRootGL m 0 b, hrootmem b⟩, (hcenter _).mpr ⟨b, rfl⟩⟩
  have hinj : Function.Injective param := by
    intro b c hbc
    have h02 := congrArg
      (fun z : Subgroup.center F =>
        (((z : F) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) hbc
    simpa [param, SuzukiRootGL, SuzukiRootMatrix] using h02
  have hsurj : Function.Surjective param := by
    intro z
    obtain ⟨b, hb⟩ := (hcenter z).mp z.property
    refine ⟨b, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hb.symm
  constructor
  · intro z hz
    obtain ⟨b, hb⟩ := (hcenter z).mp hz
    apply Subtype.ext
    change (z : GL (Fin 4) K) ^ 2 = 1
    rw [pow_two, hb, hmul]
    simp only [zero_mul, CharTwo.add_self_eq_zero]
    exact suzukiRootGL_zero_zero m
  · calc
      Nat.card (Subgroup.center F) = Nat.card K :=
        Nat.card_congr (Equiv.ofBijective param ⟨hinj, hsurj⟩).symm
      _ = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)

end

end CFSG.BenderSuzuki.External
