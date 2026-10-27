module

public import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bFrobenius

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.GH74.GLS.IVK hiding innAut
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bWreath
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bFrobenius
open scoped commutatorElement

namespace K4bL227

theorem factorization_three_9828 : (9828 : ℕ).factorization 3 = 3 := by
  have h : (9828 : ℕ) = 3 ^ 3 * 364 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_three_29484 : (29484 : ℕ).factorization 3 = 4 := by
  have h : (29484 : ℕ) = 3 ^ 4 * 364 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem exists_mulEquiv_L2 {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 9828)
    (hmodel : LieModel (Y ⧸ center Y) .PSL 2 3 3) : Nonempty (Y ≃* L2 F27) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := F27) 3 3 (by norm_num)
    (by rw [GaloisField.card 3 3 (by norm_num)]) hmodel
  let e' : Y ⧸ center Y ≃* L2 F27 := e.trans (L2.equivPSL F27).symm
  have hcard : Nat.card (Y ⧸ center Y) = 9828 := by
    rw [Nat.card_congr e'.toEquiv]
    have hF : L2Field F27 := ⟨by rw [card_F27]; decide, by rw [card_F27]; decide⟩
    rw [card_eq_of_L2Field (MulEquiv.refl (L2 F27)) hF, card_F27]
    norm_num
  have hZ : Nat.card (center Y) = 1 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Y)
    rw [hY, hcard] at this
    omega
  have hZbot : center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  have hinj : Function.Injective (QuotientGroup.mk' (center Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZbot]
  have hbij : Function.Bijective (QuotientGroup.mk' (center Y)) :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hY])
  exact ⟨(MulEquiv.ofBijective _ hbij).trans e'⟩

theorem sylow_isElemAbelian_card {Y : Type} [Group Y] [Finite Y] (e : Y ≃* L2 F27)
    (hY : Nat.card Y = 9828) (S : Sylow 3 Y) :
    IsElemAbelian 3 (S : Subgroup Y) ∧ Nat.card S = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card S = 27 := by
    rw [Sylow.card_eq_multiplicity, hY, factorization_three_9828]; norm_num
  refine ⟨?_, hcard⟩
  let Q : Sylow 3 Y := Sylow.ofCard (U₀ e) (by rw [card_U₀, hY, factorization_three_9828]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Y) Q S
  have hS : (S : Subgroup Y) = (U₀ e).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  rw [hS]
  exact isElemAbelian_map (isElemAbelian_U₀ e) _

theorem exists_conj_of_card_81 {A : Type*} [Group A] (hA : Nat.card A = 58968)
    {M R : Subgroup A} (hM : Nat.card M = 81) (hR : Nat.card R = 81) :
    ∃ g : A, R = M.map (MulAut.conj g).toMonoidHom := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h81 : (3 : ℕ) ^ (Nat.card A).factorization 3 = 81 := by
    rw [hA, factorization_three_58968]; norm_num
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := A)
    (Sylow.ofCard M (hM.trans h81.symm)) (Sylow.ofCard R (hR.trans h81.symm))
  exact ⟨g, by rw [← Sylow.coe_ofCard R (hR.trans h81.symm), ← hg]; rfl⟩

theorem card_innAut_eq {Y : Type} [Group Y] (e : Y ≃* L2 F27) :
    Nat.card (innAut Y) = Nat.card Y :=
  (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_L2 e)).toEquiv).symm

theorem card_of_isSylowOf {Y : Type} [Group Y] [Finite Y] (e : Y ≃* L2 F27)
    (hY : Nat.card Y = 9828) (hA : Nat.card (MulAut Y) = 58968)
    {B : Subgroup (MulAut Y)} (hB : innAut Y ≤ B) (h3 : 3 ∣ (innAut Y).relIndex B)
    {R : Subgroup (MulAut Y)} (hR : CFSG.ABGLocalTools.IsSylowOf 3 R B) : Nat.card R = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut Y) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have h1 := Subgroup.relIndex_mul_card (innAut Y) B
  rw [inf_eq_left.2 hB, card_innAut_eq e, hY] at h1
  have hdvd : Nat.card B ∣ 58968 := hA ▸ Subgroup.card_subgroup_dvd_card B
  rw [← h1] at hdvd
  have h6 : (innAut Y).relIndex B ∣ 6 :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 9828) (by simpa using hdvd)
  have hle : (innAut Y).relIndex B ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hpos : 0 < (innAut Y).relIndex B := Nat.pos_of_dvd_of_pos h6 (by norm_num)
  have hcases : (innAut Y).relIndex B = 3 ∨ (innAut Y).relIndex B = 6 := by omega
  rw [hR.card_eq, ← h1]
  rcases hcases with h | h
  · rw [h, show 3 * 9828 = 29484 by norm_num, factorization_three_29484]; norm_num
  · rw [h, show 6 * 9828 = 58968 by norm_num, factorization_three_58968]; norm_num

theorem normal_innAut (Y : Type) [Group Y] : (innAut Y).Normal :=
  inferInstanceAs (CFSG.GH74.GLS.IVK.innAut Y).Normal

theorem map_conj_innAut {Y : Type} [Group Y] (g : MulAut Y) :
    (innAut Y).map (MulAut.conj g).toMonoidHom = innAut Y := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (normal_innAut Y).conj_mem y hy g
  · intro hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, (normal_innAut Y).conj_mem x hx g⁻¹, ?_⟩
    simp [MulAut.conj_apply]
    group

end K4bL227

open K4bL227

theorem k4b_of_orders
    (horders : ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
      Odd (Nat.card (center Y)) → LieModel (Y ⧸ center Y) .PSL 2 3 3 →
        Nat.card Y = 2 ^ 2 * 3 ^ 3 * 7 * 13 ∧ Nat.card (MulAut Y) = 6 * Nat.card Y) :
    K4b := by
  intro Y _ _ hq hodd hmodel
  obtain ⟨hY, hA⟩ := horders Y hq hodd hmodel
  have hY' : Nat.card Y = 9828 := by rw [hY]; norm_num
  have hA' : Nat.card (MulAut Y) = 58968 := by rw [hA, hY']
  obtain ⟨e⟩ := exists_mulEquiv_L2 hY' hmodel
  refine ⟨fun S => sylow_isElemAbelian_card e hY' S, ?_⟩
  intro B hB h3 R hR
  have hR81 := card_of_isSylowOf e hY' hA' hB h3 hR
  have hW0 := wreath81_M₀ e hA'
  obtain ⟨g, hg⟩ := exists_conj_of_card_81 hA' hW0.card_R hR81
  have hS : R ⊓ innAut Y = (M₀ e ⊓ innAut Y).map (MulAut.conj g).toMonoidHom := by
    rw [hg, Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      map_conj_innAut]
  have hW : Wreath81 R (R ⊓ innAut Y) := by
    rw [hS, hg]; exact hW0.map (MulAut.conj g)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hW.clauses
  refine ⟨c1, c2, c3, c4, ?_, c6, ?_⟩
  · obtain ⟨y, hy, hyS, hy3⟩ := c5
    exact ⟨y, hy, fun h => hyS ⟨hy, h⟩, hy3⟩
  · intro y hy hyI hy3
    exact c7 y hy (fun h => hyI h.2) hy3

theorem k4b_of_k4a (hK4a : K4a) : K4b :=
  k4b_of_orders fun Y _ _ hq hodd hmodel =>
    let h := hK4a Y hq hodd hmodel
    ⟨h.1, h.2.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
