module

public import CFSG.Quasithin.Background.B610TwoOff
public import CFSG.CGT.PushingUpLit.A78.OppSL2

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Timmesfeld CFSG.Timmesfeld.ARS

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl2_card_le_of_isPGroup {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CGT.PushingUpLit.A78.isElemAbRankOne_upper_lower F
  have hodd := ElemAbRankOne.not_two_dvd_index h
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h1 : Nat.card P ∣ Nat.card (upperUnipotent F) * (upperUnipotent F).index := by
    rw [Subgroup.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card P
  have hcop : Nat.Coprime (Nat.card P) (upperUnipotent F).index := by
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  rw [← RankOne.card_upperUnipotent F]
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right h1)

theorem sl2_not_two_dvd_index {S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hcard : Nat.card S = Nat.card F) : ¬ 2 ∣ S.index := by
  have h := CGT.PushingUpLit.A78.isElemAbRankOne_upper_lower F
  have hodd := ElemAbRankOne.not_two_dvd_index h
  have e1 := S.card_mul_index
  have e2 := (upperUnipotent F).card_mul_index
  rw [hcard, ← RankOne.card_upperUnipotent F, ← e2] at e1
  rwa [Nat.eq_of_mul_eq_mul_left Nat.card_pos e1]

theorem sl2_exists_sup_conj_eq_top {S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hS : IsPGroup 2 S) (hcard : Nat.card S = Nat.card F) :
    ∃ z, S ⊔ S.map (MulAut.conj z).toMonoidHom = ⊤ := by
  have h := CGT.PushingUpLit.A78.isElemAbRankOne_upper_lower F
  obtain ⟨x, hx⟩ := ElemAbRankOne.exists_eq_map_conj h hS
    (hcard.trans (RankOne.card_upperUnipotent F).symm)
  refine ⟨x * NaturalModule.weylElt F * x⁻¹, ?_⟩
  have e : S.map (MulAut.conj (x * NaturalModule.weylElt F * x⁻¹)).toMonoidHom =
      (upperUnipotent F).map (MulAut.conj (x * NaturalModule.weylElt F)).toMonoidHom := by
    rw [hx, ← RankOne.map_conj_mul, inv_mul_cancel_right]
  rw [e, hx]
  refine ElemAbRankOne.sup_map_conj_eq_top h fun heq => ?_
  rw [RankOne.map_conj_mul (upperUnipotent F) x (NaturalModule.weylElt F),
    CGT.PushingUpLit.A78.map_conj_weylElt_upper] at heq
  exact RankOne.upperUnipotent_ne_lowerUnipotent F
    (Subgroup.map_injective (MulAut.conj x).injective heq)

end SL2

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F] (D : NatData L V F)

include D in
theorem NatData.exists_psi (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (IntMod V hV),
      Function.Injective ψ ∧ ψ.range = autI hV L := by
  set π : ↥L →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hLV) with hπ
  set σ := Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F with hσ
  set α' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F := σ.symm.toMonoidHom.comp D.α with hα'
  have hα's : Function.Surjective α' := σ.symm.surjective.comp D.surj
  have hker : α'.ker = π.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, D.ker,
      Subgroup.mem_subgroupOf, hπ, MonoidHom.comp_apply, convI_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective α' hα's
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (IntMod V hV) :=
    ((QuotientGroup.kerLift π).comp (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom).comp
      e.symm.toMonoidHom
  have hψα : ∀ l, ψ (α' l) = π l := by
    intro l
    have h1 : e.symm (α' l) = (QuotientGroup.mk l : ↥L ⧸ α'.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.kerLift π (QuotientGroup.quotientMulEquivOfEq hker (e.symm (α' l))) = _
    rw [h1]
    rfl
  refine ⟨ψ, ?_, ?_⟩
  · exact (QuotientGroup.kerLift_injective π).comp
      ((QuotientGroup.quotientMulEquivOfEq hker).injective.comp e.symm.injective)
  · ext φ
    rw [mem_autI hV, MonoidHom.mem_range]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨l, rfl⟩ := hα's z
      exact ⟨Subgroup.inclusion hLV l, l.2, (hψα l).symm⟩
    · rintro ⟨g, hgL, rfl⟩
      refine ⟨α' ⟨g, hgL⟩, ?_⟩
      rw [hψα]
      rfl

include D in
theorem NatData.exists_conj_gen [Finite F] [CharP F 2] (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {Y : Subgroup (MulAut (IntMod V hV))}
    (hYL : Y ≤ autI hV L) (hY2 : IsPGroup 2 Y) (hYc : Nat.card Y = Nat.card F) :
    ∃ (ℓ : G) (hℓ : ℓ ∈ L), autI hV L ≤ Y ⊔ B1.conjAut (convI hV ⟨ℓ, hLV hℓ⟩) Y := by
  obtain ⟨ψ, hψi, hψr⟩ := D.exists_psi hV hLV
  have hYr : Y ≤ ψ.range := hψr ▸ hYL
  have hSY : (Y.comap ψ).map ψ = Y := Subgroup.map_comap_eq_self hYr
  have hSc : Nat.card (Y.comap ψ) = Nat.card F := by
    rw [← Subgroup.card_map_of_injective hψi, hSY, hYc]
  obtain ⟨z, hz⟩ := sl2_exists_sup_conj_eq_top (hY2.comap_of_injective ψ hψi) hSc
  have hzr : ψ z ∈ autI hV L := hψr ▸ ⟨z, rfl⟩
  obtain ⟨g, hgL, hg⟩ := (mem_autI hV).mp hzr
  refine ⟨g, hgL, ?_⟩
  have h1 := congrArg (Subgroup.map ψ) hz
  rw [Subgroup.map_sup, RankOne.map_map_conj, hSY, ← MonoidHom.range_eq_map, hψr] at h1
  rw [← h1]
  refine sup_le_sup_left (le_of_eq ?_) Y
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  have hg' : convI hV ⟨g, hLV hgL⟩ = ψ z := hg
  rw [hg']
  simp

include D in
theorem NatData.card_le_of_isPGroup [Finite F] [CharP F 2] (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {Q : Subgroup (MulAut (IntMod V hV))}
    (hQL : Q ≤ autI hV L) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card F := by
  obtain ⟨ψ, hψi, hψr⟩ := D.exists_psi hV hLV
  have hQr : Q ≤ ψ.range := hψr ▸ hQL
  have h1 : Nat.card (Q.comap ψ) = Nat.card Q := by
    rw [← Subgroup.card_map_of_injective hψi, Subgroup.map_comap_eq_self hQr]
  rw [← h1]
  exact sl2_card_le_of_isPGroup (hQ.comap_of_injective ψ hψi)

include D in
theorem NatData.isSylowTwoOf_of_card [Finite F] [CharP F 2] (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {Y : Subgroup (MulAut (IntMod V hV))}
    (hYL : Y ≤ autI hV L) (hY2 : IsPGroup 2 Y) (hYc : Nat.card Y = Nat.card F) :
    IsSylowTwoOf Y (autI hV L) := by
  obtain ⟨ψ, hψi, hψr⟩ := D.exists_psi hV hLV
  have hYr : Y ≤ ψ.range := hψr ▸ hYL
  have hSc : Nat.card (Y.comap ψ) = Nat.card F := by
    rw [← Subgroup.card_map_of_injective hψi, Subgroup.map_comap_eq_self hYr, hYc]
  refine ⟨hYL, hY2, ?_⟩
  have h := sl2_not_two_dvd_index hSc
  rwa [Subgroup.index_comap, hψr] at h

end CFSG.Quasithin.B610T

end
