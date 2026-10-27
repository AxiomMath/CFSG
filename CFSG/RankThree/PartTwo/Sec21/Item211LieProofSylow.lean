module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofStar
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem toConjAct_smul_subgroup (g : G) (Q : Subgroup G) :
    ConjAct.toConjAct g • Q = Q.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    rfl

omit [Finite G] in
theorem map_conj_map_conj (g h : G) (Q : Subgroup G) :
    (Q.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      Q.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer' {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : Q.map (MulAut.conj g).toMonoidHom = Q :=
  map_conj_eq_of_mem_normalizer hg

theorem exists_normalized_threeSubgroup {P K O U : Subgroup G}
    (hKP : K ≤ P) (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hK3 : ¬ 3 ∣ Nat.card K) {m : ℕ}
    (hcard : Nat.card P = Nat.card K * 3 ^ m)
    (hOK : O ≤ K) (hPO : P ≤ Subgroup.normalizer (O : Set G)) (hOodd : Odd (Nat.card O))
    (hact : ∀ q ∈ P, ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ O)
    (hU2 : IsPGroup 2 U) (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hUO : U ≤ Subgroup.normalizer (O : Set G)) :
    ∃ Q : Subgroup G, Q ≤ P ∧ Nat.card Q = 3 ^ m ∧ U ≤ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card P).factorization 3 = m := by
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (pow_ne_zero _ (by norm_num)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hK3,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, zero_add]
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 P))
  set Q : Subgroup G := (Q₀ : Subgroup P).map P.subtype with hQdef
  have hQP : Q ≤ P := Subgroup.map_subtype_le _
  have hQc : Nat.card Q = 3 ^ m := by
    rw [hQdef, Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity,
      hfac]
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card hQc
  have hsyl : ∀ Q' : Subgroup G, Q' ≤ P → Nat.card Q' = 3 ^ m →
      ∃ p ∈ P, Q' = Q.map (MulAut.conj p).toMonoidHom := by
    intro Q' hQ'P hQ'c
    have hc : Nat.card (Q'.subgroupOf P) = 3 ^ (Nat.card P).factorization 3 := by
      rw [hfac, ← hQ'c]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'P).toEquiv
    obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (↥P) Q₀ (Sylow.ofCard (Q'.subgroupOf P) hc)
    refine ⟨p, p.2, ?_⟩
    have h1 := congrArg (fun S : Sylow 3 P => ((S : Subgroup P).map P.subtype : Subgroup G)) hp
    simp only [Sylow.coe_ofCard] at h1
    rw [Subgroup.map_subgroupOf_eq_of_le hQ'P] at h1
    rw [← h1]
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨(z : G), ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨MulAut.conj p z, ?_, rfl⟩
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨z, hz, rfl⟩
  have hPKQ : ∀ p ∈ P, ∃ k ∈ K, ∃ q ∈ Q, p = k * q := by
    have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQP.trans hPK
    have hdisj : Q ⊓ K = ⊥ := by
      refine Subgroup.disjoint_def.mpr ?_ |>.eq_bot
      intro x hxQ hxK
      have h1 : orderOf x ∣ 3 ^ m := by
        rw [← hQc]
        exact Subgroup.orderOf_dvd_natCard Q hxQ
      have h2 : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
      have hcop : Nat.Coprime (3 ^ m) (Nat.card K) :=
        Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3)
      have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
      exact orderOf_eq_one_iff.mp h3
    have hsup : Q ⊔ K = P := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hQP hKP) ?_
      have h1 := Sec6.card_sup_mul_card_inf hQK
      rw [hdisj, Subgroup.card_bot, mul_one, hQc] at h1
      rw [h1, hcard, mul_comm]
    have hset : ((K ⊔ Q : Subgroup G) : Set G) = (K : Set G) * (Q : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left K Q hQK
    intro p hp
    have hp' : p ∈ ((K ⊔ Q : Subgroup G) : Set G) := by
      rw [sup_comm, hsup]
      exact hp
    rw [hset] at hp'
    obtain ⟨k, hk, q, hq, rfl⟩ := hp'
    exact ⟨k, hk, q, hq, rfl⟩
  have hKO : ∀ k ∈ K, ∃ o ∈ O, Q.map (MulAut.conj k).toMonoidHom =
      Q.map (MulAut.conj o).toMonoidHom := by
    intro k hk
    have hO3 : ¬ 3 ∣ Nat.card O := fun h3 => hK3 (h3.trans (Subgroup.card_dvd_of_le hOK))
    obtain ⟨w, hwK, hwk, hwQ⟩ := exists_fixed_conj_of_coprime hQ3 (hQP.trans hPK) hOK
      (hKP.trans hPO) (hQP.trans hPO) hO3 hk fun g hg => by
        have h1 := hact g (hQP hg) k hk
        have h2 := (Subgroup.mem_normalizer_iff.mp (hPO (hKP (K.inv_mem hk))) _).mp h1
        rw [inv_inv] at h2
        have e : k⁻¹ * (g * k * g⁻¹) = k⁻¹ * (g * k * g⁻¹ * k⁻¹) * k := by group
        rw [e]
        exact h2
    refine ⟨(w * k⁻¹)⁻¹, O.inv_mem hwk, ?_⟩
    have hwN : w ∈ Subgroup.normalizer (Q : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have h1 := hwQ x hx
      have h2 : x * w = w * x := by
        calc x * w = x * w * x⁻¹ * x := by group
          _ = w * x := by rw [h1]
      have : w * x * w⁻¹ = x := by
        calc w * x * w⁻¹ = x * w * w⁻¹ := by rw [h2]
          _ = x := by group
      rw [this]
      exact hx
    have e : k = (w * k⁻¹)⁻¹ * w := by group
    conv_lhs => rw [e]
    rw [← map_conj_map_conj, map_conj_eq_of_mem_normalizer' hwN]
  have hUQ : ∀ u ∈ U, ∃ o ∈ O, Q.map (MulAut.conj u).toMonoidHom =
      Q.map (MulAut.conj o).toMonoidHom := by
    intro u hu
    have hle : Q.map (MulAut.conj u).toMonoidHom ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hUP hu) x).mp (hQP hx)
    have hc : Nat.card (Q.map (MulAut.conj u).toMonoidHom) = 3 ^ m := by
      rw [Subgroup.card_map_of_injective (MulAut.conj u).injective, hQc]
    obtain ⟨p, hp, hpQ⟩ := hsyl _ hle hc
    obtain ⟨k, hk, q, hq, rfl⟩ := hPKQ p hp
    obtain ⟨o, ho, hko⟩ := hKO k hk
    refine ⟨o, ho, ?_⟩
    rw [hpQ, ← map_conj_map_conj, map_conj_eq_of_mem_normalizer'
      (Subgroup.le_normalizer hq), hko]
  set O' := O.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hO'
  set Ω := MulAction.orbit O' Q with hΩ
  have hmemΩ : ∀ H : Subgroup G, H ∈ Ω ↔ ∃ o ∈ O, H = Q.map (MulAut.conj o).toMonoidHom := by
    intro H
    constructor
    · rintro ⟨⟨g, o, ho, rfl⟩, rfl⟩
      refine ⟨o, ho, ?_⟩
      show (ConjAct.toConjAct o : ConjAct G) • Q = _
      exact toConjAct_smul_subgroup o Q
    · rintro ⟨o, ho, rfl⟩
      refine ⟨⟨ConjAct.toConjAct o, o, ho, rfl⟩, ?_⟩
      show (ConjAct.toConjAct o : ConjAct G) • Q = _
      exact toConjAct_smul_subgroup o Q
  have hUΩ : ∀ u ∈ U, ∀ H ∈ Ω, H.map (MulAut.conj u).toMonoidHom ∈ Ω := by
    intro u hu H hH
    obtain ⟨o, ho, rfl⟩ := (hmemΩ H).mp hH
    obtain ⟨o', ho', e⟩ := hUQ u hu
    have hou : u * o * u⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hUO hu) o).mp ho
    refine (hmemΩ _).mpr ⟨u * o * u⁻¹ * o', O.mul_mem hou ho', ?_⟩
    rw [map_conj_map_conj, show u * o = (u * o * u⁻¹) * u by group, ← map_conj_map_conj, e,
      map_conj_map_conj, show u * o * u⁻¹ * u * u⁻¹ * o' = u * o * u⁻¹ * o' by group]
  have hΩodd : Odd (Nat.card Ω) := by
    have h1 : Nat.card Ω * Nat.card (MulAction.stabilizer O' Q) = Nat.card O' := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup O' Q)
    have h2 : Nat.card O' = Nat.card O :=
      Subgroup.card_map_of_injective (ConjAct.toConjAct : G ≃* ConjAct G).injective
    rw [← h2, ← h1] at hOodd
    exact Nat.Odd.of_mul_left hOodd
  set U' := U.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hU'
  have hU'2 : IsPGroup 2 U' := hU2.map _
  let S : SubMulAction U' (Subgroup G) :=
    { carrier := Ω
      smul_mem' := by
        rintro ⟨g, u, hu, rfl⟩ H hH
        show (ConjAct.toConjAct u : ConjAct G) • H ∈ Ω
        rw [toConjAct_smul_subgroup]
        exact hUΩ u hu H hH }
  have hScard : Nat.card S = Nat.card Ω := rfl
  have hmod := hU'2.card_modEq_card_fixedPoints S
  have hne : (MulAction.fixedPoints U' S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints U' S) = 0 := by
      rw [hemp]
      simp
    rw [h0, hScard] at hmod
    exact (Nat.not_even_iff_odd.mpr hΩodd) (Nat.even_iff.mpr hmod)
  obtain ⟨⟨H, hH⟩, hfix⟩ := hne
  obtain ⟨o, ho, rfl⟩ := (hmemΩ H).mp hH
  refine ⟨Q.map (MulAut.conj o).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hoP : o ∈ P := hKP (hOK ho)
    exact P.mul_mem (P.mul_mem hoP (hQP hx)) (P.inv_mem hoP)
  · rw [Subgroup.card_map_of_injective (MulAut.conj o).injective, hQc]
  · intro u hu
    have h1 := congrArg Subtype.val (hfix ⟨ConjAct.toConjAct u, u, hu, rfl⟩)
    change (ConjAct.toConjAct u : ConjAct G) • Q.map (MulAut.conj o).toMonoidHom =
      Q.map (MulAut.conj o).toMonoidHom at h1
    rw [toConjAct_smul_subgroup] at h1
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [← h1]
    exact ⟨x, hx, rfl⟩

end Item211LieProof

end CFSG.RankThree.PartTwo.Sec21
