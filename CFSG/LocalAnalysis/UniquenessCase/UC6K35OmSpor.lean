module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.Native.HSMcLFiveCentralizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.AGLEmbedding.KFactProofs.SmallIdent

theorem false_of_sylowCube_of_omega {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hcube : SylowCube p Y) {S B : Subgroup Y} (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤)
    (hBcard : Nat.card B = p ^ 2) (hΩ : ∀ x ∈ S, x ^ p = 1 → x ∈ B) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hSp, hSi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  let T : Sylow p Y := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSi)
  have hTS : (T : Subgroup Y) = S := IsPGroup.toSylow_coe _ _
  obtain ⟨hTcard, hTexp⟩ := hcube T
  rw [hTS] at hTcard hTexp
  have hSB : S ≤ B := fun x hx => hΩ x hx (hTexp x hx)
  have hle := Subgroup.card_le_of_le hSB
  rw [hTcard, hBcard] at hle
  have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)
  omega

theorem not_omega_central_mcl
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .McL)
    {S B : Subgroup Y} (hS : CFSG.ABGLocalTools.IsSylowOf 5 S ⊤) (hBcard : Nat.card B = 5 ^ 2)
    (hΩ : ∀ x ∈ S, x ^ 5 = 1 → x ∈ B) : False := by
  obtain ⟨e₀⟩ := hY
  obtain ⟨e⟩ : Nonempty (Y ≃* CFSG.Sporadic.Schreier.mclP) :=
    ⟨e₀.trans CFSG.Sporadic.Schreier.mclPermEquiv⟩
  have hfin : Finite CFSG.Sporadic.Schreier.mclP := Finite.of_equiv Y e.toEquiv
  have hcard : Nat.card Y = 5 ^ 3 * 7185024 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.card_mclP]
    norm_num
  obtain ⟨-, ⟨Q, hQ⟩, -, hexp⟩ :=
    (CFSG.RankThree.Native.R3E_McL_full_five_centralizer_structures).1
  have hcube : SylowCube 5 Y := by
    refine sylowCube_of_equiv (by norm_num) e hcard (by norm_num) Q fun s hs' => ?_
    rw [hQ] at hs'
    have h5 : (⟨(s : Equiv.Perm (Fin 275)), hs'⟩ : CFSG.RankThree.Native.mcl275FiveQ) ^ 5 = 1 := by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one _
    exact Subtype.ext (by simpa using congrArg Subtype.val h5)
  exact false_of_sylowCube_of_omega (by norm_num) hcube hS hBcard hΩ

theorem not_omega_central_j4
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .J4) {S B : Subgroup Y}
    (hS : CFSG.ABGLocalTools.IsSylowOf 11 S ⊤) (hBcard : Nat.card B = 11 ^ 2)
    (hΩ : ∀ x ∈ S, x ^ 11 = 1 → x ∈ B) : False := by
  obtain ⟨e₀⟩ := hY
  obtain ⟨e⟩ : Nonempty (Y ≃* CFSG.Sporadic.J4.J) :=
    ⟨e₀.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)⟩
  have hfin : Finite CFSG.Sporadic.J4.J := Finite.of_equiv Y e.toEquiv
  have hcard : Nat.card Y = 11 ^ 3 * 65195770883604480 := by
    have h1 : Nat.card Y = Nat.card CFSG.Blueprint.NativeSporadic.J4 := Nat.card_congr e₀.toEquiv
    rw [h1, CFSG.Sporadic.J4.card_J4]
    norm_num
  obtain ⟨Q, hQ⟩ := exists_sylow_exp_j4
  have hcube := @sylowCube_of_equiv Y _ _ 11 CFSG.Sporadic.J4.J _ _ 65195770883604480
    (by norm_num) e hcard
  exact false_of_sylowCube_of_omega (by norm_num) (hcube (by omega) Q hQ) hS hBcard hΩ

end CFSG.LocalAnalysis.UniquenessCase.UCK
