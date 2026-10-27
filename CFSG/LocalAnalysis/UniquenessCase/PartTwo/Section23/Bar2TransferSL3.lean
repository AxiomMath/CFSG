module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem IsSLn.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSLn X n a) : IsSLn Y n a := by
  obtain ⟨K, hKf, hKfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hKf, hKfin, hcard, ⟨e.symm.trans e'⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

theorem map_pCore_comap_eq_bot_of_isSLn {X Y : Type} [Group X] [Finite X]
    [Group Y] [Finite Y] (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurSL3) {j : ℕ} (hshape : PartTwo.IsSLn Y 3 j) (hj : 3 ≤ j)
    (hbot : CFSG.pCore 2 Y = ⊥) :
    ((CFSG.pCore 2 Y).comap f).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := CFSG.pCore 2 X
  let P : Subgroup Y := CFSG.pCore 2 Y
  have hNbot : CFSG.pCore 2 (X ⧸ N) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := X)
  have hNleM : N ≤ P.comap f := pCore_le_comap_of_surjective f hf
  haveI hMn : (P.comap f).Normal := (CFSG.pCore_normal (p := 2) (G := Y)).comap f
  let C : Subgroup (X ⧸ N) := f.ker.map (QuotientGroup.mk' N)
  let K : Subgroup (X ⧸ N) := (P.comap f).map (QuotientGroup.mk' N)
  have hKnormal : K.Normal :=
    hMn.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hCK : C ≤ K := Subgroup.map_mono (by
    rw [← MonoidHom.comap_bot (f := f)]
    exact Subgroup.comap_mono bot_le)
  have hcenterC : C ≤ Subgroup.center (X ⧸ N) :=
    image_ker_le_center_of_commutator_le (N := N) hker
  have hpowK : ∀ k ∈ K, ∃ a : ℕ, k ^ (2 ^ a) ∈ C :=
    pow_two_mem_map_of_isPGroup (N := N) (P := P) f
      (CFSG.pCore_isPGroup (p := 2) (G := Y))
  haveI : K.Normal := hKnormal
  obtain ⟨hKC, -⟩ :=
    eq_of_pow_two_mem_of_pCore_eq_bot (C := C) (K := K) hCK hcenterC hpowK hNbot
  rw [← hKC] at hcenterC
  have hperfectX : commutator X = ⊤ := by rwa [_root_.commutator_def]
  haveI hPerfX : Group.IsPerfect X := Group.IsPerfect.mk hperfectX
  haveI hPerfXbar : Group.IsPerfect (X ⧸ N) := inferInstance
  have e : (X ⧸ N) ⧸ K ≃* Y ⧸ P :=
    quotientQuotientEquivQuotientOfSurjective (N := N) (P := P) f hf hNleM
  have hshapeY : PartTwo.IsSLn (Y ⧸ P) 3 j := by
    have eP : Y ⧸ P ≃* Y :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact PartTwo.IsSLn.of_mulEquiv eP.symm hshape
  have hshapeX : PartTwo.IsSLn ((X ⧸ N) ⧸ K) 3 j :=
    PartTwo.IsSLn.of_mulEquiv e.symm hshapeY
  have hcommX : ⁅(⊤ : Subgroup (X ⧸ N)), (⊤ : Subgroup (X ⧸ N))⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hKbot : K = ⊥ := hS (X ⧸ N) j hcommX K hcenterC hshapeX hj
  simpa only [K] using hKbot

theorem comap_pCore_eq_of_pCore_eq_bot_of_isSLn {X Y : Type} [Group X] [Finite X]
    [Group Y] [Finite Y] (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hS : KSchurSL3) {j : ℕ} (hshape : PartTwo.IsSLn Y 3 j) (hj : 3 ≤ j)
    (hbot : CFSG.pCore 2 Y = ⊥) :
    f.ker = CFSG.pCore 2 X ∧ Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* Y) := by
  let N : Subgroup X := CFSG.pCore 2 X
  let P : Subgroup Y := CFSG.pCore 2 Y
  let K : Subgroup (X ⧸ N) := (P.comap f).map (QuotientGroup.mk' N)
  have hKbot : K = ⊥ := map_pCore_comap_eq_bot_of_isSLn f hf hperfect hker hS hshape hj hbot
  have hNleM : N ≤ P.comap f := pCore_le_comap_of_surjective f hf
  have hPle : P.comap f ≤ N := by
    have hle : P.comap f ≤ (QuotientGroup.mk' N).ker :=
      (Subgroup.map_eq_bot_iff (H := P.comap f) (f := QuotientGroup.mk' N)).mp hKbot
    simpa [N, QuotientGroup.ker_mk'] using hle
  have hPN : P.comap f = N := le_antisymm hPle hNleM
  have hkerEq : f.ker = N := by
    rw [← hPN, show P = ⊥ from hbot, MonoidHom.comap_bot]
  refine ⟨hkerEq, ⟨?_⟩⟩
  have e : (X ⧸ N) ⧸ K ≃* Y ⧸ P :=
    quotientQuotientEquivQuotientOfSurjective (N := N) (P := P) f hf hNleM
  have e' : (X ⧸ N) ⧸ (⊥ : Subgroup (X ⧸ N)) ≃* Y ⧸ P :=
    (QuotientGroup.quotientMulEquivOfEq hKbot).symm.trans e
  exact (QuotientGroup.quotientBot (G := X ⧸ N)).symm.trans
    (e'.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
