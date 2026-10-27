module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVO8p
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Certificate9541
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projOmegaPlus)
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.EvenSmallLie.OmegaEight (omegaT genArrs gen gen_mem_omegaT card_omegaT genArrs_size
  extract_getElem! nonempty_mulEquiv_omegaT card_outer_le_six)

namespace Item434O8pOuter

open Item434O8pE9

theorem pg_size : o8pE9.pg.size = 8 := by
  simp [o8pE9, genArrs_size]

theorem pg_mem :
    ∀ l < o8pE9.pg.size, CFSG.Monster.B.Co2.permOfArr o8pE9.n o8pE9.pg[l]! ∈ omegaT := by
  intro l hl
  rw [pg_size] at hl
  have h : o8pE9.pg[l]! = genArrs[l]! := by
    simp only [o8pE9]
    exact extract_getElem! hl (by rw [genArrs_size]; norm_num)
  rw [h]
  exact gen_mem_omegaT hl

theorem qOrd_eq :
    o8pE9.qOrd = 3 ^ (Nat.card omegaT).factorization 3 := by
  have h : o8pE9.qOrd = 3 ^ 5 := by simp [o8pE9]
  rw [h, card_omegaT, show (174182400 : ℕ) = 3 ^ 5 * 716800 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 5 (by norm_num)]

theorem exists_e81_of_e9_omegaT
    {P : Subgroup omegaT} (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    ∃ E : Subgroup omegaT, CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ P ≤ E := by
  obtain ⟨Q, hQJ, hQcard, hgood⟩ := e9_sound o8pE9 Certificates.certificate9541 omegaT pg_mem
  exact exists_e81_of_e9_ambient hQJ (hQcard.trans qOrd_eq) hgood hP hP9

theorem exists_e81_of_e9_o8p
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1) {P : Subgroup X}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ P ≤ E := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_omegaT hX
  have hPe : CFSG.Assembly.IsElemAbelian 3 (P.map φ.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP9' : Nat.card (P.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hP9]
  obtain ⟨E', hE'e, hE'81, hPE'⟩ := exists_e81_of_e9_omegaT hPe hP9'
  refine ⟨E'.map φ.symm.toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E' hE'e, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact hE'81
  · intro p hp
    exact ⟨φ p, hPE' ⟨p, hp, rfl⟩, by simp⟩

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_o8p_27
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projOmegaPlus 4 (GaloisField 2 1))
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (projOmegaPlus 4 (GaloisField 2 1)) := Finite.of_equiv _ e₀.toEquiv
  have h27' : Nat.card h.layerStar = 27 := h27
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  have hcen := Item434SmallTwoIV.center_eq_bot_of_layer_quotient h e₀
  have hinj := conj_injective_of_center_eq_bot hcen
  have hA27 : Nat.card (A.map (quotConj e₀)) = 27 := by
    rw [Item434Spor.card_map_quotConj h e₀, h27']
  have hKe := isElemAbelian_map_quotConj h e₀
  set K := A.map (quotConj e₀) with hK
  have hmodel : StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero, ⟨Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  have hout := card_outer_le_six hmodel
  have hlm : CFSG.Blueprint.LieModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    Or.inl ⟨by decide, hmodel⟩
  set π : MulAut (projOmegaPlus 4 (GaloisField 2 1)) →* Outer (projOmegaPlus 4 (GaloisField 2 1)) :=
    QuotientGroup.mk' (inner (projOmegaPlus 4 (GaloisField 2 1))) with hπ
  have h1 := card_eq_card_inf_ker_mul_card_map π K
  have hker : π.ker = inner (projOmegaPlus 4 (GaloisField 2 1)) := QuotientGroup.ker_mk' _
  rw [hker, hA27] at h1
  have hπK : Nat.card (K.map π) ≤ 3 := by
    have hp : IsPGroup 3 (K.map π) := by
      intro x
      obtain ⟨a, ha, hax⟩ := x.2
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hax, ← map_pow, hKe.2 a ha, map_one]
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hle : Nat.card (K.map π) ≤ 6 :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)).trans hout
    rw [hk] at hle ⊢
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hF9 : 9 ≤ Nat.card (K ⊓ inner (projOmegaPlus 4 (GaloisField 2 1)) : Subgroup _) := by
    have hm0 : 0 < Nat.card (K.map π) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul (show Nat.card (K ⊓ inner (projOmegaPlus 4 (GaloisField 2 1)) :
      Subgroup _) ≤ 8 by omega) hπK
    omega
  set F₀ := (K ⊓ inner (projOmegaPlus 4 (GaloisField 2 1)) : Subgroup _) with hF₀
  have hF₀K : F₀ ≤ K := inf_le_left
  have hF₀dvd : Nat.card F₀ ∣ 3 ^ 3 := by
    have h := Subgroup.card_dvd_of_le hF₀K
    rw [hA27] at h
    exact h
  obtain ⟨j, hj, hjF⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hF₀dvd
  have hj2 : 2 ≤ j := by
    by_contra hj2
    have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K₁, hK₁⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := F₀) (n := 2)
    (by rw [hjF]; exact pow_dvd_pow 3 hj2)
  set F₁ := K₁.map F₀.subtype with hF₁
  have hF₁F : F₁ ≤ F₀ := Subgroup.map_subtype_le K₁
  have hF₁9 : Nat.card F₁ = 9 := by
    rw [hF₁, Subgroup.card_map_of_injective F₀.subtype_injective, hK₁]
    norm_num
  have hF₁K : F₁ ≤ K := hF₁F.trans hF₀K
  have hF₁e : CFSG.Assembly.IsElemAbelian 3 F₁ :=
    CFSG.RankThree.PartTwo.Source.isElemAbelian_of_le hKe hF₁K
  set P₁ := F₁.comap (MulAut.conj : projOmegaPlus 4 (GaloisField 2 1) →* _) with hP₁
  have hP₁map : P₁.map MulAut.conj = F₁ :=
    Subgroup.map_comap_eq_self (hF₁F.trans inf_le_right)
  have hP₁9 : Nat.card P₁ = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hP₁map, hF₁9]
  have hP₁e : CFSG.Assembly.IsElemAbelian 3 P₁ :=
    isElemAbelian_of_map_injective hinj (by rw [hP₁map]; exact hF₁e)
  obtain ⟨E, hEe, hE81, hP₁E⟩ := exists_e81_of_e9_o8p hlm hP₁e hP₁9
  refine false_of_fixed h hZ e₀ (B := A ⊓ F₁.comap (quotConj e₀)) inf_le_left
    (hF₁9.symm.le.trans (card_le_card_inf_comap e₀ hF₁K)) hEe hE81 ?_
  rintro b ⟨-, hb⟩ d hd
  have hb' : quotConj e₀ b ∈ P₁.map (MulAut.conj : projOmegaPlus 4 (GaloisField 2 1) →* _) := by
    rw [hP₁map]
    exact hb
  obtain ⟨p, hp, hpb⟩ := hb'
  have hpd : p * d = d * p := congrArg Subtype.val (hEe.1.is_comm.comm ⟨p, hP₁E hp⟩ ⟨d, hd⟩)
  rw [← hpb, MulAut.conj_apply, hpd, mul_inv_cancel_right]

end Ctx

end Item434O8pOuter

open Item434O8pOuter

section Families

theorem item434SmallTwoIV_O8p_27Outer :
    Item434SmallTwoIV_O8p_27Outer := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27 _
  obtain ⟨e₀⟩ := hL
  exact (false_of_o8p_27 hc e₀ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
