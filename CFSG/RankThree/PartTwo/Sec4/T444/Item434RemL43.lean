module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43K3
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
import CFSG.RankThree.PartTwo.Sec4.Item49Small
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Item434RemL43

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

noncomputable abbrev fieldEquiv : GaloisField 3 1 ≃+* ZMod 3 :=
  (GaloisField.equivZmodP 3).toRingEquiv

noncomputable def projSLEquivPSL43 : projSL 4 (GaloisField 3 1) ≃* PSL43 :=
  (projSLEquivPSLn 4 (GaloisField 3 1)).trans
    ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 4)
      fieldEquiv).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 (ZMod 3)))

theorem not_three_dvd_card_outer_PSL43 : ¬ 3 ∣ Nat.card (Outer PSL43) := by
  have h := Item49Small.not_three_dvd_card_outer_projSL (n := 4) (e := 1) (by norm_num) le_rfl
    (by norm_num)
  rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    projSLEquivPSL43).toEquiv] at h

theorem eq_bot_of_isPGroup_two_three {X : Type*} [Group X] {H : Subgroup X} [Finite H]
    (h2 : IsPGroup 2 H) (h3 : IsPGroup 3 H) : H = ⊥ := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h2
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp h3
  rw [ha] at hb
  have hb0 : b = 0 := by
    by_contra hb0
    have h3d : 3 ∣ 2 ^ a := hb ▸ dvd_pow_self 3 hb0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3d)
    omega
  rw [hb0, pow_zero] at hb
  rw [← Subgroup.card_eq_one, ha, hb]

theorem center_layer_eq_bot
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 4 (GaloisField 3 1)) :
    Subgroup.center (layer G) = ⊥ := by
  have hmX : CFSG.Models.LieModel (projSL 4 (GaloisField 3 1)) .PSL 4 3 1 :=
    Census.lieModel_projSL ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hmL := Census.lieModel_of_mulEquiv e₀ hmX
  have hbL := Census.blueprint_lieModel_of_classical (by decide) hmL
  have h2 := CFSG.ComponentClassification.CatFactsL4U4.Cover82.multiplierL4U4 (layer G)
    h.isQuasisimple 3 1 Nat.prime_three (by norm_num) le_rfl (Or.inl hbL)
  exact eq_bot_of_isPGroup_two_three h2 h.isPGroup_center_layer

theorem isElemAbelian_map_piL {H : Subgroup SL4} (hH : CFSG.Assembly.IsElemAbelian 3 H) :
    CFSG.Assembly.IsElemAbelian 3 (H.map piL) :=
  CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hH

theorem map_piL_map_conj (H : Subgroup SL4) (k : SL4) :
    (H.map (MulAut.conj k).toMonoidHom).map piL =
      (H.map piL).map (MulAut.conj (piL k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem false_of_projSL_four_three
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 4 (GaloisField 3 1)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := center_layer_eq_bot h e₀
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* PSL43 := e₀.trans projSLEquivPSL43 with hθ
  have hcen : Subgroup.center PSL43 = ⊥ := Item434SmallTwoIV.center_eq_bot_of_layer_quotient h θ
  have hP0e : CFSG.Assembly.IsElemAbelian 3 (pZeroGrp.map piL) :=
    isElemAbelian_map_piL isElemAbelian_pZeroGrp
  have hP027 : Nat.card (pZeroGrp.map piL) = 27 := by
    rw [card_map_piL_of_le pZeroGrp_le_unitriangular, card_pZeroGrp]
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434Spor.false_of_card_nine h hZ θ hP0e hP027 h9
  obtain ⟨P, hPe, hPc, hPA⟩ := Item434SmallTwoOther.exists_inner h θ
    not_three_dvd_card_outer_PSL43 hcen
  rw [h27] at hPc
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := ZMod 3) 3 (n := 4) (by norm_num)
  have hScard : Nat.card (projUnitriangular 4 (ZMod 3)) =
      3 ^ (Nat.card PSL43).factorization 3 := by
    rw [← hS]
    exact Sylow.card_eq_multiplicity S
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hScard hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'le : P' ≤ projUnitriangular 4 (ZMod 3) := Item434AltPerm.map_conj_inv_le hg
  have hP'g : P'.map (MulAut.conj g).toMonoidHom = P := by
    rw [hP', Item434AltPerm.map_conj_map_conj_inv]
  have hP'card : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, hPc]
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hPe
  set Pt := P'.comap piL ⊓ unitriangular 4 (ZMod 3) with hPt
  have hPtU : Pt ≤ unitriangular 4 (ZMod 3) := inf_le_right
  have hPtmap : Pt.map piL = P' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hxU, rfl⟩ := hP'le hy
      exact ⟨x, ⟨hy, hxU⟩, rfl⟩
  have hPtcard : Nat.card Pt = 27 := by
    rw [← card_map_piL_of_le hPtU, hPtmap, hP'card]
  have hinjU : ∀ x ∈ unitriangular 4 (ZMod 3), ∀ y ∈ unitriangular 4 (ZMod 3),
      piL x = piL y → x = y := fun x hx y hy hxy => proj_injOn_unitriangular 4 hx hy hxy
  have hPte : CFSG.Assembly.IsElemAbelian 3 Pt := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · refine hinjU _ ((unitriangular 4 (ZMod 3)).mul_mem (hPtU x.2) (hPtU y.2)) _
        ((unitriangular 4 (ZMod 3)).mul_mem (hPtU y.2) (hPtU x.2)) ?_
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hP'e.1.is_comm.comm ⟨piL x, x.2.1⟩ ⟨piL y, y.2.1⟩)
    · refine hinjU _ ((unitriangular 4 (ZMod 3)).pow_mem (hPtU hx) 3) _
        (unitriangular 4 (ZMod 3)).one_mem ?_
      rw [map_pow, map_one]
      exact hP'e.2 _ hx.1
  rcases classify hPtU hPte hPtcard with ⟨k, B, hBP, hB9, hBk⟩ | ⟨k, hk⟩
  ·
    obtain ⟨D, hD⟩ : ∃ D : Subgroup SL4, D = rGrp.map (MulAut.conj k).toMonoidHom := ⟨_, rfl⟩
    have hDcube : ∀ x ∈ D, x ^ 3 = 1 := by
      rw [hD]
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_pow, isElemAbelian_rGrp.2 r hr, map_one]
    have hD0 : Nat.card D = 81 := by
      rw [hD, Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom)
        (MulAut.conj k).injective, card_rGrp]
    have hDcard : Nat.card (D.map piL) = 81 := by
      rw [card_map_of_injOn piL (fun x hx y hy hxy =>
        eq_of_proj_eq_of_pow_three (hDcube x hx) (hDcube y hy) hxy), hD0]
    have hDe : CFSG.Assembly.IsElemAbelian 3 D := by
      rw [hD]
      exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ isElemAbelian_rGrp
    obtain ⟨BX, hBX⟩ : ∃ BX : Subgroup PSL43,
        BX = (B.map piL).map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
    obtain ⟨DX, hDX⟩ : ∃ DX : Subgroup PSL43,
        DX = (D.map piL).map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
    have hBXP : BX ≤ P := by
      rw [hBX, ← hP'g, ← hPtmap]
      exact Subgroup.map_mono (Subgroup.map_mono hBP)
    have hBXcard : Nat.card BX = Nat.card B := by
      rw [hBX, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective,
        card_map_piL_of_le (hBP.trans hPtU)]
    have hDXe : CFSG.Assembly.IsElemAbelian 3 DX := by
      rw [hDX]
      exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
        (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hDe)
    have hDXcard : Nat.card DX = 81 := by
      rw [hDX, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, hDcard]
    have hcomm : ∀ b ∈ BX, ∀ d ∈ DX, b * d = d * b := by
      rw [hBX, hDX, hD]
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ _ ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, rfl⟩
      have hb' := hBk b hb
      have h1 : b * (k * r * k⁻¹) = (k * r * k⁻¹) * b := by
        have e := rGrp_comm hb' hr
        calc b * (k * r * k⁻¹) = k * ((k⁻¹ * b * k) * r) * k⁻¹ := by group
          _ = k * (r * (k⁻¹ * b * k)) * k⁻¹ := by rw [e]
          _ = (k * r * k⁻¹) * b := by group
      have h2 : piL b * piL (MulAut.conj k r) = piL (MulAut.conj k r) * piL b := by
        rw [← map_mul, ← map_mul, MulAut.conj_apply, h1]
      change MulAut.conj g (piL b) * MulAut.conj g (piL (MulAut.conj k r)) =
        MulAut.conj g (piL (MulAut.conj k r)) * MulAut.conj g (piL b)
      rw [← map_mul (MulAut.conj g), ← map_mul (MulAut.conj g), h2]
    have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
    obtain ⟨F, hF⟩ : ∃ F : Subgroup (MulAut PSL43),
        F = BX.map (MulAut.conj : PSL43 →* MulAut PSL43) := ⟨_, rfl⟩
    have hFA : F ≤ A.map (Item434Alt.quotConj θ) := by
      rw [hPA, hF]
      exact Subgroup.map_mono hBXP
    have hF9 : 9 ≤ Nat.card F := by
      rw [hF, Subgroup.card_map_of_injective hinj, hBXcard]
      exact hB9
    refine Item434Kit.false_of_fixed h hZ θ (B := A ⊓ F.comap (Item434Alt.quotConj θ))
      inf_le_left (hF9.trans (Item434Kit.card_le_card_inf_comap θ hFA)) hDXe hDXcard.ge ?_
    rintro a ⟨-, ha⟩ d hd
    rw [hF] at ha
    obtain ⟨β, hβ, hβa⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp ha)
    rw [← hβa, MulAut.conj_apply, hcomm β hβ d hd, mul_inv_cancel_right]
  ·
    have hPt0 : Pt = pZeroGrp.map (MulAut.conj k⁻¹).toMonoidHom := by
      have e := Item434AltPerm.map_conj_map_conj_inv Pt k⁻¹
      rw [inv_inv, hk] at e
      exact e.symm
    have hPeq : P = ((pZeroGrp.map piL).map (MulAut.conj (piL k⁻¹)).toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
      rw [← hP'g, ← hPtmap, hPt0, map_piL_map_conj]
    have hN := ((noSignalizer_pZero hcen).map_conj (piL k⁻¹)).map_conj g
    rw [← hPeq] at hN
    exact Item434Kit.false_of_normalizer h θ fun Y hY3 hAY => hN Y hY3 (hPA ▸ hAY)

end Item434RemL43

section Families

theorem item434CharThreeL4 :
    Item434CharThreeL4 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (Item434RemL43.false_of_projSL_four_three hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
