module

public import CFSG.RankThree.PartTwo.Sec21.U4FourGroupLines
public import CFSG.RankThree.PartOne.KF.ClsSpUpper

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open CFSG CFSG.RankThree
open Matrix
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor spRev mem_spRev_iff exists_conj_into_d8Tor_sp)
open CFSG.LieType.Universal.Unitary (antidiag)
open U4Lines (torusD line_cases mapL mapL_le mapL_mono card_mapL mapL_conj)
open U4FourLines (rootHom coe_rootHom rootHom_injective rootFour mem_rootFour card_rootFour
  isElemAbelian_rootFour torus_le_normalizer_rootFour torusD_mem_centralizer_iff nL nL' nS nS'
  nL_mul_self nL'_mul_self nS_mul_self nS'_mul_self chiL chiL' chiS chiS' conj_nL conj_nL'
  conj_nS conj_nS' mem_zpowers_of_chiL mem_zpowers_of_chiL' mem_zpowers_of_chiS
  mem_zpowers_of_chiS' FourGroupFor fourGroupFor_of_mapL pow_three_of_mem_mapL)

namespace Sp4FourLines

variable {F : Type} [Field F] [CharP F 2]

theorem rootHom_nL_mem_spRev (t : F) :
    rootHom nL nL_mul_self (Multiplicative.ofAdd t) ∈ spRev F := by
  rw [mem_spRev_iff, coe_rootHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nL, antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      CharTwo.add_self_eq_zero, Fin.rev]

theorem rootHom_nL'_mem_spRev (t : F) :
    rootHom nL' nL'_mul_self (Multiplicative.ofAdd t) ∈ spRev F := by
  rw [mem_spRev_iff, coe_rootHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nL', antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      CharTwo.add_self_eq_zero, Fin.rev]

theorem rootHom_nS_mem_spRev (t : F) :
    rootHom nS nS_mul_self (Multiplicative.ofAdd t) ∈ spRev F := by
  rw [mem_spRev_iff, coe_rootHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nS, antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      CharTwo.add_self_eq_zero, Fin.rev]

theorem rootHom_nS'_mem_spRev (t : F) :
    rootHom nS' nS'_mul_self (Multiplicative.ofAdd t) ∈ spRev F := by
  rw [mem_spRev_iff, coe_rootHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nS', antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      CharTwo.add_self_eq_zero, Fin.rev]

theorem exists_rootFour_line_sp [Finite F] (hμ : Nat.card (rootsOfUnity 3 F) = 3)
    {N : Matrix (Fin 4) (Fin 4) F} (hN : N * N = 0) {i j : Fin 4} (hij : N i j = 1)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) (χ : D8Mod 3 F →* rootsOfUnity 3 F)
    (hconj : ∀ v (t : F), torusD v * rootHom N hN (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom N hN (Multiplicative.ofAdd (((χ v : Fˣ) : F) * t)))
    (hSp : ∀ t : F, rootHom N hN (Multiplicative.ofAdd t) ∈ spRev F)
    (w : D8Mod 3 F) (hw : χ w = 1) (hker : ∀ v, χ v = 1 → v ∈ Subgroup.zpowers w) :
    ∃ U : Subgroup (GL (Fin 4) F), U ≤ spRev F ∧ IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ d8Tor 3 F 4 ≤ Subgroup.normalizer (U : Set (GL (Fin 4) F)) ∧
      d8Tor 3 F 4 ⊓ Subgroup.centralizer (U : Set (GL (Fin 4) F)) =
        Subgroup.zpowers (torusD w) := by
  have ha1 : ((ω : Fˣ) : F) ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : ((ω : Fˣ) : F) ≠ 0 := Units.ne_zero _
  refine ⟨rootFour N hN ((ω : Fˣ) : F), ?_, isElemAbelian_rootFour N hN _,
    card_rootFour hN hij ha0 ha1, torus_le_normalizer_rootFour hN hμ hω χ hconj, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := mem_rootFour.mp hx
    exact hSp _
  · have hC := torusD_mem_centralizer_iff hN hij ((ω : Fˣ) : F) χ hconj
    ext x
    constructor
    · rintro ⟨⟨v, rfl⟩, hxC⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hker v ((hC v).mp hxC))
      exact ⟨k, (map_zpow torusD w k).symm⟩
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨⟨w ^ k, map_zpow torusD w k⟩, Subgroup.zpow_mem _ ((hC w).mpr hw) k⟩

theorem exists_fourGroup_of_le_torus_sp [Finite F] (hμ : Nat.card (rootsOfUnity 3 F) = 3)
    {ℓ : Subgroup (GL (Fin 4) F)} (hℓT : ℓ ≤ d8Tor 3 F 4) (h3 : Nat.card ℓ = 3) :
    ∃ U : Subgroup (GL (Fin 4) F), U ≤ spRev F ∧ IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ d8Tor 3 F 4 ≤ Subgroup.normalizer (U : Set (GL (Fin 4) F)) ∧
      d8Tor 3 F 4 ⊓ Subgroup.centralizer (U : Set (GL (Fin 4) F)) = ℓ := by
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  rcases line_cases hμ hω hℓT h3 with rfl | rfl | rfl | rfl
  · exact exists_rootFour_line_sp hμ nL_mul_self (i := 1) (j := 2) rfl hω chiL conj_nL
      rootHom_nL_mem_spRev (ω, 1) (by simp [chiL]) (mem_zpowers_of_chiL hμ hω)
  · exact exists_rootFour_line_sp hμ nL'_mul_self (i := 0) (j := 3) rfl hω chiL' conj_nL'
      rootHom_nL'_mem_spRev (1, ω) (by simp [chiL']) (mem_zpowers_of_chiL' hμ hω)
  · exact exists_rootFour_line_sp hμ nS_mul_self (i := 0) (j := 1) rfl hω chiS conj_nS
      rootHom_nS_mem_spRev (ω, ω) (by simp [chiS]) (mem_zpowers_of_chiS hμ hω)
  · exact exists_rootFour_line_sp hμ nS'_mul_self (i := 0) (j := 2) rfl hω chiS' conj_nS'
      rootHom_nS'_mem_spRev (ω, ω⁻¹) (by simp [chiS']) (mem_zpowers_of_chiS' hμ hω)

theorem fourGroupFor_spRev [Finite F] (hμ : Nat.card (rootsOfUnity 3 F) = 3)
    (hdvd : 3 ∣ Nat.card F - 1) {F' ℓ : Subgroup (GL (Fin 4) F)} (hFY : F' ≤ spRev F)
    (hF3 : ∀ x ∈ F', x ^ 3 = 1) (hℓF : ℓ ≤ F') (hℓ3 : Nat.card ℓ = 3) :
    FourGroupFor (spRev F) F' ℓ := by
  have hX : ∀ x ∈ F'.subgroupOf (spRev F), x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hF3 _ hx)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_sp Nat.prime_three (by norm_num) hdvd _ hX
  have hT : ∀ Z ≤ F', mapL (MulAut.conj g) Z ≤ d8Tor 3 F 4 := by
    intro Z hZ
    rw [mapL_conj g (hZ.trans hFY)]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hFY (hZ hx)⟩ (hZ hx)
  refine fourGroupFor_of_mapL (MulAut.conj g) hFY hℓF ?_
  obtain ⟨U, hUY, hUe, hU4, hTN, hTC⟩ := exists_fourGroup_of_le_torus_sp hμ (hT ℓ hℓF)
    (by rw [card_mapL _ (hℓF.trans hFY), hℓ3])
  refine ⟨U, hUY, hUe, hU4, (hT F' le_rfl).trans hTN, ?_⟩
  apply le_antisymm
  · rw [← hTC]
    exact inf_le_inf_right _ (hT F' le_rfl)
  · exact le_inf (mapL_mono _ hℓF) (hTC ▸ inf_le_right)

end Sp4FourLines

open Sp4FourLines

theorem sp4FourGroupLines {b : ℕ} (hb : 0 < b) (hbe : Even b) :
    ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), Nonempty (Y ≃* projSp 2 (GaloisField 2 b)) →
      ∀ F ℓ : Subgroup G, F ≤ Y → IsElemAbelian 3 F → ℓ ≤ F → Nat.card ℓ = 3 →
        ∃ U : Subgroup G, U ≤ Y ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
          F ≤ Subgroup.normalizer (U : Set G) ∧ F ⊓ Subgroup.centralizer (U : Set G) = ℓ := by
  intro G _ _ Y ⟨eY⟩ F ℓ hFY hFe hℓF hℓ3
  set K := GaloisField 2 b with hKdef
  have hK : Nat.card K = 2 ^ b := GaloisField.card 2 b hb.ne'
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_two_pow_sub_one hbe
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd hdvd
  let e₀ : projSp 2 K ≃* ↥(spRev K) :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 K)).symm.trans
      ((CFSG.RankThree.PartOne.KFU.spEquivProj (K := K) (by norm_num)).symm.trans
        (CFSG.RankThree.PartOne.KFU.spRevEquiv K))
  set E := eY.trans e₀
  exact fourGroupFor_of_mapL E hFY hℓF (fourGroupFor_spRev hμ hdvd (mapL_le E F)
    (pow_three_of_mem_mapL E hFe.2) (mapL_mono E hℓF) (by rw [card_mapL E (hℓF.trans hFY), hℓ3]))

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof
