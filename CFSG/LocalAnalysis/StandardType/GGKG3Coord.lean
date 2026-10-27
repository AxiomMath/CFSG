module

public import CFSG.LocalAnalysis.StandardType.GGKG3Setup
public import CFSG.LocalAnalysis.StandardType.GGKG3Act

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

private lemma kg3_cast_rank : Tag.E6.rank = 6 := rfl

private lemma kg3_k3Star_apply' (c : WeylGroup .E6) (y : Fin 6 → ZMod 7)
    (i : Fin Tag.E6.rank) :
    k3Star c y i = k3Pair y (c⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
  k3Star_apply c y (Fin.cast kg3_cast_rank i)

private lemma kg3_k3Pair_single (y : Fin 6 → ZMod 7) (j : Fin 6) :
    k3Pair y (Pi.single j 1 : Fin 6 → ℤ) = y j := by
  simp [k3Pair, Pi.single_apply]

private lemma kg3_toMat_e6Three_eq_kMw (i j : Fin Tag.E6.rank) :
    (toMat Tag.E6.rank e6ThreeMat : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) i j =
      K3dCheck.kMw i j := rfl

private lemma kg3_k3Pair_mulVec_single (y : Fin 6 → ZMod 7) (j : Fin Tag.E6.rank) :
    k3Pair y ((toMat Tag.E6.rank e6ThreeMat : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) *ᵥ
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
      ∑ i : Fin Tag.E6.rank, y i * ((K3dCheck.kMw i j : ℤ) : ZMod 7) := by
  show (∑ i : Fin Tag.E6.rank, y i *
      ((((toMat Tag.E6.rank e6ThreeMat : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) *ᵥ
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i : ℤ) : ZMod 7)) =
    ∑ i : Fin Tag.E6.rank, y i * ((K3dCheck.kMw i j : ℤ) : ZMod 7)
  refine Finset.sum_congr rfl fun i _ => ?_
  have hval : (((toMat Tag.E6.rank e6ThreeMat :
      Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) *ᵥ
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i) = K3dCheck.kMw i j := by
    rw [Matrix.mulVec_single_one]
    exact kg3_toMat_e6Three_eq_kMw i j
  exact congrArg (fun t : ℤ => y i * ((t : ℤ) : ZMod 7)) hval

theorem k3Diag_injective {L : Type}
    [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 7) :
    Function.Injective (k3Diag ζ : (Fin 6 → ZMod 7) → ModGL .E6 L) := by
  intro y y' h
  exact k3Tor_injective hζ (rootDiagUnit_injective (by simpa [k3Diag] using h))

theorem k3_conj_diag {L : Type}
    [Field L] {ζ : Lˣ} (h7 : ζ ^ 7 = 1) (c : WeylGroup .E6) (y : Fin 6 → ZMod 7) :
    canonicalRep (coxeterSystem .E6) L c * k3Diag ζ y * (canonicalRep (coxeterSystem .E6) L c)⁻¹ =
      k3Diag ζ (k3Star c y) := by
  rw [k3Diag, k3Diag, canonicalRep_conj_rootDiagUnit]
  have hcoord : weylTuple c (k3Tor ζ y) = k3Tor ζ (k3Star c y) := by
    funext i
    change rootChar (k3Tor ζ y) (c⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
        k3Chi ζ (k3Star c y i)
    rw [kg3_k3Star_apply' c y i]
    exact rootChar_k3Tor h7 y (c⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
  rw [hcoord]

theorem k3_E_eq {L : Type} [Field L]
    [IsAlgClosed L] (S : LangSetup .E6 L 7) (hS : IsK3Setup S) {ζ : Lˣ} (hζ : orderOf ζ = 7)
    (x : ModGL .E6 L) : x ∈ S.E ↔ ∃ y ∈ k3Ex, x = k3Diag ζ y := by
  have h7 : ζ ^ 7 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hsub : (S.E : Set (ModGL .E6 L)) ⊆ k3Diag ζ '' k3Ex := by
    rintro x hx
    have hxT : x ∈ S.D.torus := (S.E_le hx).1
    have hxTor : x ∈ torusGroup .E6 L :=
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hxT).1
    obtain ⟨a, ha⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom hxTor
    have hxa : x = rootDiagUnit .E6 a := ha.symm
    have hapow : ∀ i, a i ^ 7 = 1 := by
      have hx7 : x ^ 7 = 1 := S.E_exp x hx
      have h1 : rootDiagUnit .E6 (a ^ 7) = rootDiagUnit .E6 a ^ 7 :=
        map_pow (rootDiagUnitHom .E6 L) a 7
      have h2 : rootDiagUnit .E6 (a ^ 7) = rootDiagUnit .E6 1 := by
        rw [h1, ← hxa, hx7, rootDiagUnit_one]
      have h3 : a ^ 7 = 1 := rootDiagUnit_injective h2
      intro i
      exact congrFun h3 i
    obtain ⟨y, hy⟩ := exists_eq_k3Tor hζ a hapow
    have hxd : rootDiagUnit .E6 a ∈ S.D.torus := by rw [← hxa]; exact hxT
    have heig : ∀ j : Fin Tag.E6.rank,
        ∑ i : Fin Tag.E6.rank, y i * ((K3dCheck.kMw i j : ℤ) : ZMod 7) = 2 * y j := by
      intro j
      have hroot := S.frob.rootChar_eq a hxd (Pi.single j 1) (isRoot_single .E6 j)
      rw [hS.rho_eq _ (isRoot_single .E6 j), e6Three_wordMat, hS.q_eq, hy,
          rootChar_k3Tor h7, rootChar_k3Tor h7, pow_two, ← k3Chi_add h7] at hroot
      have h1 := k3Chi_injective hζ hroot
      have h2 : k3Pair y ((toMat Tag.E6.rank e6ThreeMat :
          Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) *ᵥ
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
          ∑ i : Fin Tag.E6.rank, y i * ((K3dCheck.kMw i j : ℤ) : ZMod 7) :=
        kg3_k3Pair_mulVec_single y j
      have h3 : k3Pair y (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = y j :=
        kg3_k3Pair_single y j
      calc ∑ i : Fin Tag.E6.rank, y i * ((K3dCheck.kMw i j : ℤ) : ZMod 7)
          = k3Pair y ((toMat Tag.E6.rank e6ThreeMat :
              Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) *ᵥ
              (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := h2.symm
        _ = k3Pair y (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
            k3Pair y (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := h1
        _ = y j + y j := congrArg₂ (· + ·) h3 h3
        _ = 2 * y j := (two_mul (y j)).symm
    refine ⟨y, mem_k3Ex_iff.2 heig, ?_⟩
    rw [hxa, hy, k3Diag]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hsub hx
    exact ⟨y, hy, hyx.symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hk3ExFin : k3Ex.Finite := by
      rw [k3Ex_eq_range]
      exact Set.finite_range k3Par
    have hfinI : (k3Diag ζ '' k3Ex).Finite := Set.Finite.image (k3Diag ζ) hk3ExFin
    have hIle : (k3Diag ζ '' k3Ex).ncard ≤ k3Ex.ncard :=
      Set.ncard_image_le (s := k3Ex) (f := k3Diag ζ) hk3ExFin
    have hEcard : (S.E : Set (ModGL .E6 L)).ncard = 343 := by
      rw [← Nat.card_coe_set_eq (S.E : Set (ModGL .E6 L))]
      show Nat.card S.E = 343
      rw [hS.card_E]
      norm_num
    have hIle' : (k3Diag ζ '' k3Ex).ncard ≤ (S.E : Set (ModGL .E6 L)).ncard := by
      rw [hEcard]
      exact hIle.trans_eq k3Ex_ncard
    have hEq : (S.E : Set (ModGL .E6 L)) = k3Diag ζ '' k3Ex :=
      Set.eq_of_subset_of_ncard_le hsub hIle' hfinI
    have hxI : k3Diag ζ y ∈ k3Diag ζ '' k3Ex := ⟨y, hy, rfl⟩
    rw [← hEq] at hxI
    exact hxI

end CFSG.StandardType.GGKG3
