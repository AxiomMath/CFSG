module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1L3
public import CFSG.Quasithin.EmptyFaithful.SzN2Quot
public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace CFSG.Quasithin.S15223P4.D1

section MapParabolic

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M]

theorem isMaxParabolic2_map_of_ker_le (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker) {P : Subgroup Γ} (hkP : ρ.ker ≤ P)
    (h : IsMaxParabolic2 (⊤ : Subgroup Γ) P) : IsMaxParabolic2 (⊤ : Subgroup M) (P.map ρ) := by
  have hcm : (P.map ρ).comap ρ = P := Subgroup.comap_map_eq_self hkP
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, S', hS', hN⟩ := h.1
    have hkS := SzN2.ker_le_of_isSylowTwoOf hk hS'
    refine ⟨le_top, S'.map ρ, isSylowTwoOf_top_map_of_surjective hS' ρ hρ, ?_⟩
    intro m hm
    obtain ⟨x, rfl⟩ := hρ m
    have hx : x ∈ Subgroup.normalizer (S' : Set Γ) :=
      SzN2.mem_normalizer_of_ker_le ρ hkS hm.2
    exact Subgroup.mem_map_of_mem ρ (hN ⟨Subgroup.mem_top _, hx⟩)
  · intro htop
    apply h.2.1
    rw [← hcm, htop, Subgroup.comap_top]
  · intro Q' hQ' hQ'top hPQ'
    obtain ⟨-, U, hU, hNU⟩ := hQ'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS : IsSylowTwoOf (U.comap ρ) ⊤ := by
      refine ⟨le_top, hU.2.1.comap_of_ker_isPGroup ρ hk, ?_⟩
      have h1 : ((U.comap ρ).subgroupOf ⊤).index = (U.comap ρ).index :=
        Subgroup.relIndex_top_right _
      rw [h1, Subgroup.index_comap_of_surjective _ hρ]
      have h2 := hU.2.2
      rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h2
    have hkS' : ρ.ker ≤ U.comap ρ := Subgroup.ker_le_comap ρ U
    have hmapU : (U.comap ρ).map ρ = U := Subgroup.map_comap_eq_self_of_surjective hρ U
    have hpar : IsParabolic2 (⊤ : Subgroup Γ) (Q'.comap ρ) := by
      refine ⟨le_top, U.comap ρ, hS, fun x hx => ?_⟩
      have h1 := SzN2.map_mem_normalizer_map ρ hρ hkS' hx.2
      rw [hmapU] at h1
      exact hNU ⟨Subgroup.mem_top _, h1⟩
    have hne : Q'.comap ρ ≠ ⊤ := by
      intro htop
      apply hQ'top
      rw [← Subgroup.map_comap_eq_self_of_surjective hρ Q', htop,
        Subgroup.map_top_of_surjective _ hρ]
    have hPle : P ≤ Q'.comap ρ := fun p hp => hPQ' (Subgroup.mem_map_of_mem ρ hp)
    have heq := h.2.2 _ hpar hne hPle
    rw [← Subgroup.map_comap_eq_self_of_surjective hρ Q', heq]

end MapParabolic

section Orders

local instance decEqSL3F2' : DecidableEq SL3F2 := fun a b =>
  decidable_of_iff ((a : Matrix (Fin 3) (Fin 3) (ZMod 2)) = b) Subtype.ext_iff.symm

theorem card_SL3F2 : Nat.card SL3F2 = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_sylow_SL3F2 {U : Subgroup SL3F2} (hU : IsSylowTwoOf U ⊤) : Nat.card U = 8 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hU.2.1
  have h1 : Nat.card U * U.index = 168 := by rw [Subgroup.card_mul_index, card_SL3F2]
  have hodd : ¬ 2 ∣ U.index := by
    have := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
  rw [hk] at h1 ⊢
  have hk3 : k ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have : 2 ^ 4 ∣ 168 := h16.trans (Dvd.intro _ h1)
    omega
  interval_cases k <;> omega

end Orders

section Cards

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M]

theorem card_eq_card_map_mul_card_ker (ρ : Γ →* M) (hρ : Function.Surjective ρ) {Q : Subgroup Γ}
    (hkQ : ρ.ker ≤ Q) : Nat.card Q = Nat.card (Q.map ρ) * Nat.card ρ.ker := by
  have : Finite M := Finite.of_surjective ρ hρ
  have h1 : Nat.card ρ.ker * Nat.card M = Nat.card Γ := by
    have := Subgroup.card_ker_mul_card_range ρ
    rwa [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top] at this
  have hQ : (Q.map ρ).comap ρ = Q := Subgroup.comap_map_eq_self hkQ
  have hidx : Q.index = (Q.map ρ).index := by
    conv_lhs => rw [← hQ]
    exact Subgroup.index_comap_of_surjective (H := Q.map ρ) hρ
  have a := Subgroup.card_mul_index Q
  have b := Subgroup.card_mul_index (Q.map ρ)
  have hpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hidx] at a hpos
  have : Nat.card Q * (Q.map ρ).index = Nat.card (Q.map ρ) * Nat.card ρ.ker * (Q.map ρ).index := by
    rw [a, ← h1, ← b]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Cards

section Parabolic

variable {G : Type} [Group G] [Finite G] {X A P : Subgroup G}

omit [Finite G] in
theorem sylow_subgroupOf_top {S : Subgroup G} (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.subgroupOf X) (⊤ : Subgroup ↥X) := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact hS.2.2

@[expose] def rhoOf (ψ : OTwoQuot X ≃* SL3F2) : ↥X →* SL3F2 :=
  ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))

omit [Finite G] in
theorem rhoOf_surjective (ψ : OTwoQuot X ≃* SL3F2) : Function.Surjective (rhoOf ψ) :=
  ψ.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem rhoOf_ker (ψ : OTwoQuot X ≃* SL3F2) : (rhoOf ψ).ker = CFSG.Open.pCore 2 ↥X := by
  rw [rhoOf, MonoidHom.ker_comp_of_injective _ _ ψ.injective, QuotientGroup.ker_mk']

omit [Finite G] in
theorem rhoOf_ker_isPGroup (ψ : OTwoQuot X ≃* SL3F2) : IsPGroup 2 (rhoOf ψ).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rhoOf_ker]
  exact CFSG.pCore_isPGroup

omit [Finite G] in
theorem rhoOf_eq_one_iff (ψ : OTwoQuot X ≃* SL3F2) {x : G} (hx : x ∈ X) :
    rhoOf ψ ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 X := by
  rw [← MonoidHom.mem_ker, rhoOf_ker]
  exact SBc16.mem_pCore_iff_coe X ⟨x, hx⟩

theorem card_isMaxParabolic2 (ψ : OTwoQuot X ≃* SL3F2) (hA : IsSylowTwoOf A X) (hAP : A ≤ P)
    (hP : IsMaxParabolic2 X P) : Nat.card P = 3 * Nat.card A := by
  have hρ := rhoOf_surjective ψ
  have hk := rhoOf_ker_isPGroup ψ
  have hA' := sylow_subgroupOf_top hA
  have hkA : (rhoOf ψ).ker ≤ A.subgroupOf X := SzN2.ker_le_of_isSylowTwoOf hk hA'
  have hAP' : A.subgroupOf X ≤ P.subgroupOf X := fun a ha => hAP ha
  have hP' := QP.isMaxParabolic2_top_of_subgroupOf hP
  have hPbar := isMaxParabolic2_map_of_ker_le (rhoOf ψ) hρ hk (hkA.trans hAP') hP'
  have h24 := card_maxParabolic hPbar
  have h8 := card_sylow_SL3F2 (isSylowTwoOf_top_map_of_surjective hA' (rhoOf ψ) hρ)
  have e1 := card_eq_card_map_mul_card_ker (rhoOf ψ) hρ (hkA.trans hAP')
  have e2 := card_eq_card_map_mul_card_ker (rhoOf ψ) hρ hkA
  have c1 : Nat.card (P.subgroupOf X) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1.1).toEquiv
  have c2 : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  rw [h24] at e1
  rw [h8] at e2
  omega

theorem inf_eq_of_card {P Q A : Subgroup G} (hAP : A ≤ P) (hAQ : A ≤ Q)
    (hP : Nat.card P = 3 * Nat.card A) (hQ : Nat.card Q = 3 * Nat.card A) (hne : P ≠ Q) :
    P ⊓ Q = A := by
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hdvd : Nat.card ↥(P ⊓ Q) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm⟩ := (Subgroup.card_dvd_of_le (le_inf hAP hAQ) :
    Nat.card A ∣ Nat.card ↥(P ⊓ Q))
  rw [hm, hP] at hdvd
  have hm3 : m ∣ 3 := by
    have : Nat.card A * m ∣ Nat.card A * 3 := by rwa [mul_comm 3] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hApos this
  rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with h1 | h3
  · rw [h1, mul_one] at hm
    symm
    exact Subgroup.eq_of_le_of_card_ge (le_inf hAP hAQ) (by rw [hm])
  · exfalso
    apply hne
    rw [h3, mul_comm, ← hP] at hm
    have h1 : P ⊓ Q = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm])
    have h2 : P ⊓ Q = Q := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hm, hP, hQ])
    rw [← h1, h2]

theorem exists_inv_mem (ψ : OTwoQuot X ≃* SL3F2) (hA : IsSylowTwoOf A X) (hAP : A ≤ P)
    (hP : IsMaxParabolic2 X P) {y : G} (hy : y ∈ P) (hy3 : y ^ 3 ∈ pCoreOf 2 X)
    (hy1 : y ∉ pCoreOf 2 X) : ∃ g ∈ P, g * y * g⁻¹ * y ∈ pCoreOf 2 X := by
  have hPX : P ≤ X := hP.1.1
  have hyX : y ∈ X := hPX hy
  have hρ := rhoOf_surjective ψ
  have hk := rhoOf_ker_isPGroup ψ
  have hA' := sylow_subgroupOf_top hA
  have hkA : (rhoOf ψ).ker ≤ A.subgroupOf X := SzN2.ker_le_of_isSylowTwoOf hk hA'
  have hAP' : A.subgroupOf X ≤ P.subgroupOf X := fun a ha => hAP ha
  have hP' := QP.isMaxParabolic2_top_of_subgroupOf hP
  have hPbar := isMaxParabolic2_map_of_ker_le (rhoOf ψ) hρ hk (hkA.trans hAP') hP'
  have h24 : Nat.card ((P.subgroupOf X).map (rhoOf ψ)) = 24 := card_maxParabolic hPbar
  let yX : ↥X := ⟨y, hyX⟩
  have hy3' : rhoOf ψ yX ^ 3 = 1 := by
    rw [← map_pow]
    exact (rhoOf_eq_one_iff ψ (X.pow_mem hyX 3)).mpr hy3
  have hy1' : rhoOf ψ yX ≠ 1 := fun h => hy1 ((rhoOf_eq_one_iff ψ hyX).mp h)
  have hord : orderOf (rhoOf ψ yX) = 3 := orderOf_eq_prime hy3' hy1'
  have hmem : rhoOf ψ yX ∈ (P.subgroupOf X).map (rhoOf ψ) :=
    Subgroup.mem_map_of_mem (rhoOf ψ) (show yX ∈ P.subgroupOf X from hy)
  let ŷ : ↥((P.subgroupOf X).map (rhoOf ψ)) := ⟨rhoOf ψ yX, hmem⟩
  have hŷord : orderOf ŷ = 3 := (Subgroup.orderOf_coe ŷ).symm.trans hord
  have hC : ∀ z : ↥((P.subgroupOf X).map (rhoOf ψ)), z * ŷ = ŷ * z → z ∈ Subgroup.zpowers ŷ := by
    intro z hz
    have hz' : (z : SL3F2) * rhoOf ψ yX = rhoOf ψ yX * z := congrArg Subtype.val hz
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_commute (MulEquiv.refl SL3F2) hord hz')
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk')⟩
  obtain ⟨ĝ, hĝ⟩ := exists_inv_of_card_24 (Q := ↥((P.subgroupOf X).map (rhoOf ψ))) h24 hŷord hC
  obtain ⟨g', hg'P, hg'⟩ := Subgroup.mem_map.mp ĝ.2
  refine ⟨(g' : G), hg'P, ?_⟩
  have hwX : (g' : G) * y * (g' : G)⁻¹ * y ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem g'.2 hyX) (X.inv_mem g'.2)) hyX
  have h1 : rhoOf ψ ⟨(g' : G) * y * (g' : G)⁻¹ * y, hwX⟩ = 1 := by
    have e : (⟨(g' : G) * y * (g' : G)⁻¹ * y, hwX⟩ : ↥X) = g' * yX * g'⁻¹ * yX := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hg']
    have := congrArg Subtype.val hĝ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [this]
    exact inv_mul_cancel _
  exact (rhoOf_eq_one_iff ψ hwX).mp h1

end Parabolic

end CFSG.Quasithin.S15223P4.D1
