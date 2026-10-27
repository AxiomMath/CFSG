module

public import CFSG.Milestones.ASVolI.F411.Ident
public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.LieType.BorelTits.Ree

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.LieType.BorelTits CFSG.Blueprint
  CFSG.Blueprint.Chevalley

section Bridge

variable {E : Type} [Group E]

theorem burnsideF411_borelTitsIn_of_holds [Finite E] {p : ℕ} [Fact p.Prime] {Gp : Subgroup E}
    (h : Holds ↥Gp p) : burnsideF411_BorelTitsIn p Gp := by
  intro R hRGp hR hRp
  have hR' : R.subgroupOf Gp ≠ ⊥ := by
    intro hbot
    apply hR
    rw [← Subgroup.map_subgroupOf_eq_of_le hRGp, hbot, Subgroup.map_bot]
  have hRp' : IsPGroup p (R.subgroupOf Gp) := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRGp).symm
  obtain ⟨S'', P', hP', hN, -, -, hS⟩ := h (R.subgroupOf Gp) hR' hRp'
  have hS'' : ((S'' : Subgroup ↥Gp).map Gp.subtype).subgroupOf Gp = S'' :=
    Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  refine ⟨(S'' : Subgroup ↥Gp).map Gp.subtype, ⟨Subgroup.map_subtype_le _, S''.isPGroup'.map _, ?_⟩,
    P'.map Gp.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  ·
    rw [show ((S'' : Subgroup ↥Gp).map Gp.subtype).relIndex Gp = (S'' : Subgroup ↥Gp).index by
      rw [Subgroup.relIndex, hS'']]
    exact S''.not_dvd_index
  · intro heq
    apply hP'
    apply Subgroup.map_injective Gp.subtype_injective
    rw [heq, Subgroup.map_top, Subgroup.range_subtype]
  · rintro x ⟨hxGp, hxN⟩
    refine ⟨⟨x, hxGp⟩, hN ?_, rfl⟩
    exact (burnsideF4j_mem_normalizer_subgroupOf hRGp ⟨x, hxGp⟩).mpr hxN
  · rintro x ⟨hxGp, hxN⟩
    refine ⟨⟨x, hxGp⟩, hS ?_, rfl⟩
    have := (burnsideF4j_mem_normalizer_subgroupOf (Subgroup.map_subtype_le _) ⟨x, hxGp⟩).mpr hxN
    rwa [hS''] at this

end Bridge

section Models


theorem burnsideF411_holds_twoF4Two {H : Type} [Group H] (h : IsTwoF4Two H) : Holds H 2 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_natCard_eq (f := 1) (by rw [hK, pow_one])
  have hc' : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hc
  have hfix := CFSG.LieType.Ree.holds_reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0
  have heq := CFSG.LieType.Ree.reeFixedGroup_eq_map_reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0
  let Γ : Subgroup (ModGL Tag.F4 K) := reeFixedGroup Tag.F4 K reeF4Perm
    (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))
  have hΓ : Holds ↥Γ 2 := by
    have e1 : ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0) ≃* ↥Γ :=
      ((CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0).equivMapOfInjective _
        Subtype.val_injective).trans (MulEquiv.subgroupCongr heq.symm)
    exact hfix.of_mulEquiv e1
  haveI : Finite ↥Γ := inferInstance
  exact (hΓ.center_quotient).of_mulEquiv e.symm

theorem burnsideF411_holds_of_isGenLie {H : Type} [Group H] {κ : GLKind} {p f : ℕ}
    (h : IsGenLie H κ p f) (hκ : κ.IsLie) : Holds H p := by
  cases κ with
  | L3 =>
    obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_natCard_eq hK
    exact (holds_statedProj_statedSL 3 K p).of_mulEquiv e.symm
  | Sp4 =>
    obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_natCard_eq hK
    exact (holds_statedProj_statedSp (n := 2) (K := K) p).of_mulEquiv e.symm
  | G2 =>
    obtain ⟨hp, -, hm⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    exact holds_of_untwistedChevalleyModel hm
  | D4tw =>
    obtain ⟨hp, hf, hm⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    exact holds_of_twistedChevalleyModel hf hm
  | F4tw =>
    obtain ⟨rfl, -, ⟨-, h2⟩ | ⟨-, hm⟩⟩ := h
    · exact burnsideF411_holds_twoF4Two h2
    · exact holds_of_reeTitsModel hm (by decide)
  | U4 =>
    obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_natCard_eq (f := f * 2) (by rw [hK, pow_mul])
    exact (holds_statedProj_statedSU hK 4).of_mulEquiv e.symm
  | U5 =>
    obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_natCard_eq (f := f * 2) (by rw [hK, pow_mul])
    exact (holds_statedProj_statedSU hK 5).of_mulEquiv e.symm
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

theorem burnsideF411_borelTitsIn {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) :
    burnsideF411_BorelTitsIn p Gp := by
  haveI : Finite E := hyp.finite
  haveI : Fact p.Prime := ⟨burnsideF4a_prime_of_isGenLie hyp.model⟩
  exact burnsideF411_borelTitsIn_of_holds (burnsideF411_holds_of_isGenLie hyp.model hκ)

end Models

end CFSG.ASVolI
