module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SectionRank

section Quo

variable {X : Type*} [Group X] [Finite X] (R : Subgroup X) [R.Normal]

omit [Finite X] in
theorem isSylowTwoOf_map_quotient {T' : Subgroup X} (hT : IsPGroup 2 T') (hi : ¬ 2 ∣ T'.index) :
    IsSylowTwoOf (T'.map (QuotientGroup.mk' R)) ⊤ := by
  refine ⟨le_top, hT.map _, ?_⟩
  rw [show ((T'.map (QuotientGroup.mk' R)).subgroupOf ⊤).index = (T'.map (QuotientGroup.mk' R)).index
    from Subgroup.relIndex_top_right _]
  exact fun hd => hi (hd.trans (Subgroup.index_map_dvd T' (QuotientGroup.mk'_surjective R)))

omit [Finite X] in
theorem isElemAbelian_map_quotient (hR : IsPGroup 2 R) {p : ℕ} (hp2 : p ≠ 2) [Fact p.Prime]
    {E : Subgroup X} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map (QuotientGroup.mk' R)) ∧
      Nat.card (E.map (QuotientGroup.mk' R)) = Nat.card E := by
  refine ⟨isElemAbelian_map hE _, ?_⟩
  have hinj : Function.Injective ((QuotientGroup.mk' R).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    obtain ⟨k, hk⟩ := hR ⟨(x : X), hx⟩
    have hk' : (x : X) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hp' : (x : X) ^ p = 1 := hE.2 x x.2
    have h1 : orderOf (x : X) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf (x : X) ∣ p := orderOf_dvd_of_pow_eq_one hp'
    have hcop : Nat.Coprime (2 ^ k) p :=
      (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2)))
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have : orderOf (x : X) = 1 := Nat.dvd_one.mp h3
    simpa using orderOf_eq_one_iff.mp this
  have hrange : E.map (QuotientGroup.mk' R) = ((QuotientGroup.mk' R).comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isSolvable_of_quotient_two_group (hR : IsPGroup 2 R) (h : Group.IsSolvable (X ⧸ R)) :
    Group.IsSolvable X := by
  have : Group.IsNilpotent ↥R := hR.isNilpotent
  have : Group.IsSolvable ↥R := inferInstance
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_comap_quotient (hR : IsPGroup 2 R) {Y : Subgroup (X ⧸ R)}
    (hY : Group.IsSolvable ↥Y) : Group.IsSolvable ↥(Y.comap (QuotientGroup.mk' R)) := by
  have hRC : R ≤ Y.comap (QuotientGroup.mk' R) := fun x hx => by
    rw [Subgroup.mem_comap]
    have h1 : (QuotientGroup.mk' R) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact Y.one_mem
  have : Group.IsNilpotent ↥(R.subgroupOf (Y.comap (QuotientGroup.mk' R))) := by
    have : IsPGroup 2 ↥(R.subgroupOf (Y.comap (QuotientGroup.mk' R))) :=
      hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    exact this.isNilpotent
  have : Group.IsSolvable ↥(R.subgroupOf (Y.comap (QuotientGroup.mk' R))) := inferInstance
  refine Group.isSolvable_of_ker_le_range (R.subgroupOf (Y.comap (QuotientGroup.mk' R))).subtype
    ((QuotientGroup.mk' R).subgroupComap Y) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : (QuotientGroup.mk' R) (x : X) = 1 := congrArg Subtype.val hx
  have h2 : (x : X) ∈ R := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr h2⟩, rfl⟩

omit [Finite X] in
theorem card_dvd_comap_quotient (Y : Subgroup (X ⧸ R)) :
    Nat.card Y ∣ Nat.card ↥(Y.comap (QuotientGroup.mk' R)) :=
  Subgroup.card_dvd_of_surjective
    ((QuotientGroup.mk' R).subgroupComap_surjective Y (QuotientGroup.mk'_surjective R))

end Quo

end CFSG.Quasithin
