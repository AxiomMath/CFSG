module

public import CFSG.Sporadic.Recognition.M22MultiplierCert
public import CFSG.Quasithin.Background.SmithB45M22HatHat

public section

namespace CFSG.Quasithin.HM22

open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.Recognition.CoverCyclic CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.HatM22 CFSG.Sporadic.Mathieu

section Cover

theorem isPresentation_m22 :
    IsPresentation m22Gen (wordSet m22Rels) :=
  isPresentation_m22Gen m22TabCheck_eq_true card_PG_m22Rels_le

noncomputable abbrev m22Pi :
    M22Cover →* NativeSporadic.M22 :=
  coverMap isPresentation_m22 (lift_m22CommWord m22TabCheck_eq_true)

theorem m22Pi_ker :
    IsCyclic m22Pi.ker ∧ Nat.card m22Pi.ker = 12 := by
  obtain ⟨_, h1, h2⟩ := cover_ker_cyclic_of_bounds isPresentation_m22 m22Comm
    (lift_m22CommWord m22TabCheck_eq_true) (N := 12)
    (lift_m22B11 m22TabCheck_eq_true) cover_bounds (by rw [card_M22])
  exact ⟨h1, h2⟩

theorem exists_lift {E : Type}
    [Group E] [Group.IsPerfect E] (q : E →* NativeSporadic.M22)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center E) :
    ∃ φ : M22Cover →* E, Function.Surjective φ ∧ φ.ker ≤ m22Pi.ker := by
  obtain ⟨φ, hφ, hcomp⟩ : ∃ φ : M22Cover →* E, Function.Surjective φ ∧ q.comp φ = m22Pi :=
    exists_surjective_lift isPresentation_m22
      (fun i => mk_commWords_mem_commutator (m22Comm i)) (lift_m22CommWord m22TabCheck_eq_true) q
      hq hker
  refine ⟨φ, hφ, fun x hx => ?_⟩
  have hx' : φ x = 1 := hx
  show m22Pi x = 1
  rw [← hcomp, MonoidHom.comp_apply, hx', map_one]

theorem card_cover_eq {E : Type} [Group E] (φ : M22Cover →* E) (hφ : Function.Surjective φ) :
    Nat.card M22Cover = Nat.card E * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]

theorem nonempty_mulEquiv_of_card_eq
    {E E' : Type} [Group E]
    [Group E'] [Group.IsPerfect E] [Group.IsPerfect E'] (q : E →* NativeSporadic.M22)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) (q' : E' →* NativeSporadic.M22)
    (hq' : Function.Surjective q') (hker' : q'.ker ≤ Subgroup.center E')
    (hcard : Nat.card E = Nat.card E') (hpos : Nat.card E ≠ 0) : Nonempty (E ≃* E') := by
  obtain ⟨φ, hφ, hφk⟩ := exists_lift q hq hker
  obtain ⟨φ', hφ', hφk'⟩ := exists_lift q' hq' hker'
  obtain ⟨hcyc, hK⟩ := m22Pi_ker
  have hKfin : Finite m22Pi.ker := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hc : Nat.card φ.ker = Nat.card φ'.ker := by
    have h1 := card_cover_eq φ hφ
    have h2 := card_cover_eq φ' hφ'
    rw [h1, hcard] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hcard ▸ hpos)) h2
  have hsub : φ.ker.subgroupOf m22Pi.ker = φ'.ker.subgroupOf m22Pi.ker := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hφk).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hφk').toEquiv, hc]
  have heq : φ.ker = φ'.ker := by
    have h := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_of_le_left hφk, inf_of_le_left hφk'] at h
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq heq)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hφ')⟩

end Cover

section Model

noncomputable abbrev hatM22Q : ↥hatM22Γ₀ →* NativeSporadic.M22 :=
  hatM22Act.codRestrict NativeSporadic.M22 hatM22Act_mem

theorem hatM22Q_surjective : Function.Surjective hatM22Q := by
  rintro ⟨σ, hσ⟩
  have hσ' : σ ∈ hatM22Act.range := by rw [range_hatM22Act]; exact hσ
  obtain ⟨g, hg⟩ := hσ'
  exact ⟨g, Subtype.ext hg⟩

theorem hatM22Q_ker :
    hatM22Q.ker = Subgroup.center ↥hatM22Γ₀ := by
  rw [center_hatM22Γ₀]
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem card_hatM22Γ₀ :
    Nat.card ↥hatM22Γ₀ = 443520 * 3 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥hatM22Γ₀),
    Nat.card_congr hatM22QuotEquiv.toEquiv, card_center_hatM22Γ₀, quasithinM22_eq, card_M22]

end Model

theorem card_of_isHat {L : Type} [Group L]
    (hL : IsHat L (NativeSporadic.Carrier .M22)) : Nat.card L = 443520 * 3 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hL
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L),
    Nat.card_congr e.toEquiv, hZ]
  change Nat.card ↥NativeSporadic.M22 * 3 = 443520 * 3
  rw [card_M22]

theorem nonempty_mulEquiv_hatM22Γ₀
    {L : Type} [Group L]
    (hL : IsHat L (NativeSporadic.Carrier .M22)) : Nonempty (↥hatM22Γ₀ ≃* L) := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hL
  have hperf : Group.IsPerfect L := hq.1
  have hperfΓ : Group.IsPerfect ↥hatM22Γ₀ := isPerfect_hatM22Γ₀
  let e' : L ⧸ Subgroup.center L ≃* ↥NativeSporadic.M22 := e
  let q : L →* NativeSporadic.M22 :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hqs : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change e' (QuotientGroup.mk' (Subgroup.center L) x) = 1 at hx
    rw [map_eq_one_iff _ e'.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have hcard : Nat.card ↥hatM22Γ₀ = Nat.card L := by
    rw [card_hatM22Γ₀, card_of_isHat ⟨hq, hZ, ⟨e⟩⟩]
  exact nonempty_mulEquiv_of_card_eq hatM22Q hatM22Q_surjective hatM22Q_ker.le q hqs hqk hcard
    (by rw [card_hatM22Γ₀]; norm_num)

end CFSG.Quasithin.HM22
