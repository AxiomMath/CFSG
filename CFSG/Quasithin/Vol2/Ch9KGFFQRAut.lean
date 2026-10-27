module

public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.KGFactG2RuMain
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHS
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin CFSG.Blueprint

theorem autRankLe_of_index {S : Type} [Group S] [Finite S]
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) {r k : ℕ}
    (hidx : (MulAut.conj : S →* MulAut S).range.index ≤ 2 ^ k)
    (hS : ∀ E : Subgroup S, IsElemAb2 E → Nat.card E ≤ 2 ^ r) : AutRankLe S (r + k) := by
  intro E hE
  have : Finite (MulAut S) :=
    Finite.of_injective (fun α : MulAut S => (α : S → S)) DFunLike.coe_injective
  set I : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hI
  have hIn : I.Normal := by
    constructor
    rintro _ ⟨g, rfl⟩ β
    refine ⟨β g, ?_⟩
    apply MulEquiv.ext
    intro x
    change β g * x * (β g)⁻¹ = β (g * β.symm x * g⁻¹)
    rw [map_mul, map_mul, map_inv, β.apply_symm_apply]
  set ρ : ↥E →* MulAut S ⧸ I := (QuotientGroup.mk' I).comp E.subtype with hρ
  have hcard : Nat.card ↥E = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hr : Nat.card ρ.range ≤ 2 ^ k := (Subgroup.card_le_card_group ρ.range).trans hidx
  have hker : ρ.ker = I.subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hk : Nat.card ρ.ker ≤ 2 ^ r := by
    rw [hker, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype, hI, ← Subgroup.map_comap_eq,
      Subgroup.card_map_of_injective hinj]
    exact hS _ (hE.comap _ hinj)
  refine rk_le_of_card_le_two_pow hE.isPGroup ?_
  rw [hcard, pow_add, mul_comm (2 ^ r)]
  exact Nat.mul_le_mul hr hk

theorem index_le_two_of_card_mulAut_le {S : Type} [Group S] [Finite S]
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (h : Nat.card (MulAut S) ≤ 2 * Nat.card S) :
    (MulAut.conj : S →* MulAut S).range.index ≤ 2 := by
  have : Finite (MulAut S) :=
    Finite.of_injective (fun α : MulAut S => (α : S → S)) DFunLike.coe_injective
  have h1 := (MulAut.conj : S →* MulAut S).range.index_mul_card
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h1
  have hpos : 0 < Nat.card S := Nat.card_pos
  by_contra hlt
  have : 3 * Nat.card S ≤ (MulAut.conj : S →* MulAut S).range.index * Nat.card S :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem autRankLe_m22 :
    AutRankLe ↥NativeSporadic.M22 5 := by
  have hinj := conj_injective_of_center_eq_bot CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have hfin : Finite ↥NativeSporadic.M22 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.QuasithinUnique.Setup.X1.m22_card_eq]; norm_num)
  refine autRankLe_of_index (k := 1) hinj
    (index_le_two_of_card_mulAut_le hinj CFSG.Sporadic.Schreier.m22_mulAut_card) ?_
  intro E hE
  exact CFSG.QuasithinUnique.Setup.X1.m22_rank_le E hE.1 fun x hx => by rw [← sq]; exact hE.2 x hx

theorem autRankLe_hs :
    AutRankLe (NativeSporadic.Carrier .HS) 5 := by
  have hZ : Subgroup.center (NativeSporadic.Carrier .HS) = ⊥ := by
    have hs : IsSimpleGroup (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.2.2
    have hc : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (NativeSporadic.Carrier .HS)) with
      h1 | h1
    · exact h1
    · exfalso
      have : IsMulCommutative (NativeSporadic.Carrier .HS) := Subgroup.center_eq_top_iff.1 h1
      have hp := Group.is_simple_iff_prime_card.1 hs
      rw [hc] at hp
      norm_num at hp
  have hinj := conj_injective_of_center_eq_bot hZ
  have hfin : Finite (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.1
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (NativeSporadic.Carrier .HS)) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      CFSG.Sporadic.Schreier.hsPermEquiv
  refine autRankLe_of_index (k := 1) hinj (by rw [pow_one]; exact hout) ?_
  intro E hE
  have h := CFSG.QuasithinUnique.Lin2.hs_native_rank E (IsElemAb2.isElemAbelian hE)
  rw [card_eq_two_pow_of_isPGroup (IsElemAb2.isPGroup hE)] at h ⊢
  have hk : rk ↥E < 5 := by
    by_contra hk
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_of_not_lt hk)
    omega
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem autRankLe_j2 :
    AutRankLe (NativeSporadic.Carrier .J2) 4 := by
  obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
  have : Finite (NativeSporadic.Carrier .J2) :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card NativeSporadic.J2 ≠ 0
      rw [CFSG.Sporadic.J2.card_J2]
      norm_num)
  have : Finite (MulAut (NativeSporadic.Carrier .J2)) :=
    Finite.of_injective (fun α : MulAut (NativeSporadic.Carrier .J2) => (α : _ → _))
      DFunLike.coe_injective
  intro E hE
  have h := CFSG.QuasithinUnique.Bridge.J2Excl.j2_rank_R (E.map Φ.symm.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hE.1 x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← sq, hE.2 x hx, map_one])
  rw [Subgroup.card_map_of_injective Φ.symm.injective] at h
  exact rk_le_of_card_le_two_pow hE.isPGroup h

theorem card_le_of_elemAb_ruP
    (E : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP)
    (hE : IsElemAb2 E) : Nat.card E ≤ 2 ^ 6 := by
  set X := E.map CFSG.Sporadic.RuSchreier.ruP.subtype with hX
  have hXP : X ≤ CFSG.Sporadic.RuSchreier.ruP := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hXp : IsPGroup 2 ↥X := hE.isPGroup.map _
  obtain ⟨g, -, hgX⟩ := CFSG.Quasithin.H13.Ch4.G2Ru.exists_conj_le_ruS hXP hXp
  set Y := X.map (MulAut.conj g).toMonoidHom with hY
  have hYsq : ∀ y ∈ Y, y * y = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← sq, hE.2 x hx, map_one, map_one]
  have hcY : Nat.card ↥Y = Nat.card ↥E := by
    rw [hY, Subgroup.card_map_of_injective (MulAut.conj g).injective, hX,
      Subgroup.card_map_of_injective CFSG.Sporadic.RuSchreier.ruP.subtype_injective]
  rw [← hcY]
  by_cases h64 : 64 ≤ Nat.card ↥Y
  · obtain ⟨r, -, hYr⟩ := CFSG.Quasithin.H13.Ch4.G2Ru.le_g2Wr_of_card hgX hYsq h64
    have hW : Nat.card ↥(CFSG.Quasithin.H13.Ch4.G2Ru.g2Wr r) ≤ 64 := by
      rw [CFSG.Quasithin.H13.Ch4.G2Ru.g2Wr, Subgroup.card_map_of_injective
        (MulAut.conj (CFSG.Quasithin.H13.Ch4.G2Ru.g2Sigma r)).injective]
      exact CFSG.Quasithin.H13.Ch4.G2Ru.card_g2W_le
    exact (Subgroup.card_le_of_le hYr).trans hW
  · norm_num
    omega

theorem autRankLe_ruP :
    AutRankLe ↥CFSG.Sporadic.RuSchreier.ruP 6 := by
  have hb := CFSG.Sporadic.RuSchreier.conj_bijective
  have hfin : Finite ↥CFSG.Sporadic.RuSchreier.ruP :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.RuSchreier.card_ruP']; norm_num)
  have hidx : (MulAut.conj : ↥CFSG.Sporadic.RuSchreier.ruP →* MulAut _).range.index ≤ 2 ^ 0 := by
    rw [MonoidHom.range_eq_top_of_surjective _ hb.2, Subgroup.index_top, pow_zero]
  exact autRankLe_of_index hb.1 hidx card_le_of_elemAb_ruP

theorem autRankLe_ru
    {X : Type} [Group X] (hX : IsSporadic .Ru X) :
    AutRankLe X 6 := by
  obtain ⟨e₀⟩ := hX
  exact AutRankLe.of_mulEquiv (e₀.trans CFSG.Sporadic.RuSchreier.ruEquivP) autRankLe_ruP

theorem autRankLe_of_m22
    {X : Type} [Group X] (hX : IsSporadic .M22 X) : AutRankLe X 5 := by
  obtain ⟨e₀⟩ := hX
  let e : X ≃* ↥NativeSporadic.M22 := e₀
  exact AutRankLe.of_mulEquiv e autRankLe_m22

theorem autRankLe_of_hs
    {X : Type} [Group X] (hX : IsSporadic .HS X) : AutRankLe X 5 := by
  obtain ⟨e₀⟩ := hX
  exact AutRankLe.of_mulEquiv e₀ autRankLe_hs

theorem autRankLe_of_j2
    {X : Type} [Group X] (hX : IsSporadic .J2 X) :
    AutRankLe X 4 := by
  obtain ⟨e₀⟩ := hX
  exact AutRankLe.of_mulEquiv e₀ autRankLe_j2

theorem autRankLe_alt7 : AutRankLe ↥(alternatingGroup (Fin 7)) 4 := by
  intro E _
  have hc : Nat.card (MulAut ↥(alternatingGroup (Fin 7))) = 5040 := by
    rw [← Nat.card_eq_of_bijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num)), Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h := padicValNat_two_le_of_dvd (by rw [hc]; norm_num) (Subgroup.card_subgroup_dvd_card E)
  rw [hc, show (5040 : ℕ) = 2 ^ 4 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)] at h
  exact h

end CFSG.Quasithin.H13.Ch9.KGFF
