module

public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.Quasithin.H13.U3SimpleRoot
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneTorus
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

theorem isCyclic_quotient_of_forall_eq_mul {X : Type*} [Group X] {U T B : Subgroup X}
    (hUB : U ≤ B) (hTB : T ≤ B) [(U.subgroupOf B).Normal] [IsCyclic T]
    (hB : ∀ x ∈ B, ∃ u ∈ U, ∃ t ∈ T, x = u * t) : IsCyclic (B ⧸ U.subgroupOf B) := by
  refine isCyclic_of_surjective
    ((QuotientGroup.mk' (U.subgroupOf B)).comp (Subgroup.inclusion hTB)) fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨u, hu, t, ht, hx⟩ := hB x x.2
  refine ⟨⟨t, ht⟩, ?_⟩
  have hxe : x = ⟨u, hUB hu⟩ * ⟨t, hTB ht⟩ := Subtype.ext hx
  have hu1 : QuotientGroup.mk' (U.subgroupOf B) ⟨u, hUB hu⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := U.subgroupOf B) _).2 hu
  rw [hxe, map_mul, hu1, one_mul]
  rfl

theorem isCyclic_rkOneGInf_quotient {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    [((rkOneUStar h).subgroupOf (rkOneGInf h)).Normal] :
    IsCyclic (rkOneGInf h ⧸ (rkOneUStar h).subgroupOf (rkOneGInf h)) := by
  have := h.finite
  obtain ⟨-, ⟨eT, -⟩, -⟩ := unitary_rank_one_torus_action h
  have hTcyc : IsCyclic (rkOneT h) := isCyclic_of_injective eT.toMonoidHom eT.injective
  exact isCyclic_quotient_of_forall_eq_mul (rkOneUStar_le_rkOneGInf h) (rkOneT_le_rkOneGInf h)
    fun x hx => (mem_rkOneGInf_iff h).1 hx

theorem isCyclic_of_permutable_rkOneUStar {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h3 : 3 ∣ Nat.card S) (Φ : S →* Equiv.Perm (hypIsotropicLines h 1 1))
    (hΦ : Function.Injective Φ) (hrange : Φ.range = rkOneG h) (A : Subgroup S)
    (hAodd : Odd (Nat.card A)) (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set S) * ((rkOneUStar h).comap Φ : Set S) =
      ((rkOneUStar h).comap Φ : Set S) * (A : Set S)) : IsCyclic A := by
  classical
  have := h.finite
  set U := (rkOneUStar h).comap Φ with hUdef
  have hUmap : U.map Φ = rkOneUStar h := by
    rw [hUdef, Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.2 (rkOneUStar_le_rkOneG h)
  have hcard : Nat.card U = 2 ^ (f * 3) := by
    rw [← Subgroup.card_map_of_injective hΦ, hUmap, card_rkOneUStar h, ← pow_mul]
  have hU2 : IsPGroup 2 U := IsPGroup.of_card hcard
  have hUne : U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card U = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 : 1 < 2 ^ (f * 3) := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
    omega
  let _ : MulAction S (hypIsotropicLines h 1 1) := MulAction.compHom _ Φ
  have hsmul : ∀ (g : S) (L : hypIsotropicLines h 1 1), g • L = Φ g L := fun _ _ => rfl
  have hstab : ∀ g ∈ MulAction.stabilizer S (infL h), Φ g ∈ rkOneGInf h := fun g hg =>
    ⟨hrange ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩, hg⟩
  have hUα : U ≤ MulAction.stabilizer S (infL h) := fun u hu => by
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact rkOneUStar_fix h hu
  have hUn : (U.subgroupOf (MulAction.stabilizer S (infL h))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc := (rkOneUStar_normal h).conj_mem ⟨Φ n, hstab n n.2⟩ hn ⟨Φ g, hstab g g.2⟩
    rw [Subgroup.mem_subgroupOf] at hc
    show Φ (↑g * ↑n * (↑g)⁻¹) ∈ rkOneUStar h
    rw [map_mul, map_mul, map_inv]
    exact hc
  have hUt : ∀ β γ : hypIsotropicLines h 1 1, β ≠ infL h → γ ≠ infL h →
      ∃ u ∈ U, u • β = γ := by
    intro β γ hβ hγ
    obtain ⟨a₁, b₁, hab₁, hβ₁⟩ := exists_rkPtL_eq β hβ
    obtain ⟨a₂, b₂, hab₂, hγ₂⟩ := exists_rkPtL_eq γ hγ
    have hx₁ := rkOneU_mem h hab₁
    have hx₂ := rkOneU_mem h hab₂
    have hx₁0 : rkOneU h a₁ b₁ hab₁ (zeroL h) = β := by rw [rkOneU_zeroL, hβ₁]
    have hx₂0 : rkOneU h a₂ b₂ hab₂ (zeroL h) = γ := by rw [rkOneU_zeroL, hγ₂]
    set x₁ := rkOneU h a₁ b₁ hab₁
    set x₂ := rkOneU h a₂ b₂ hab₂
    have hx : x₂ * x₁⁻¹ ∈ rkOneG h := rkOneUStar_le_rkOneG h
      ((rkOneUStar h).mul_mem hx₂ ((rkOneUStar h).inv_mem hx₁))
    rw [← hrange] at hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨u, ?_, ?_⟩
    · show Φ u ∈ rkOneUStar h
      rw [hu]
      exact (rkOneUStar h).mul_mem hx₂ ((rkOneUStar h).inv_mem hx₁)
    · rw [hsmul, hu, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.2 hx₁0.symm, hx₂0]
  have hM3 := NQTerm.not_three_dvd_card_permProd A U hAU hA3 hU2
  have hMtop : NQTerm.permProd A U hAU < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hM => hM3 ?_
    rw [hM, Subgroup.card_top]
    exact h3
  have hMle := U3.simple_transitive_root_proper_overgroups (infL h) hUne hUα hUn hUt hMtop
    (NQTerm.le_permProd_right A U hAU)
  have hAle : A ≤ MulAction.stabilizer S (infL h) :=
    (NQTerm.le_permProd_left A U hAU).trans hMle
  have hAU0 : A ⊓ U = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hcard]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hAodd)
  have hN := rkOneUStar_normal h
  have hAinf : ∀ a : A, Φ a ∈ rkOneGInf h := fun a => hstab a (hAle a.2)
  let ψ : A →* rkOneGInf h ⧸ (rkOneUStar h).subgroupOf (rkOneGInf h) :=
    (QuotientGroup.mk' _).comp ((Φ.comp A.subtype).codRestrict (rkOneGInf h) hAinf)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (⟨Φ a, hAinf a⟩ : rkOneGInf h) ∈ (rkOneUStar h).subgroupOf (rkOneGInf h) :=
      (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (a : S) ∈ A ⊓ U := ⟨a.2, h1⟩
    rw [hAU0, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have := isCyclic_rkOneGInf_quotient h
  exact isCyclic_of_injective ψ hψ

theorem isCyclic_of_permutable_sylow_of_statedPSU3 {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] {f : ℕ} (hf : 2 ≤ f) (hS : StatedClassicalModel S .PSU 3 2 f)
    (T : Sylow 2 S) (A : Subgroup S) (hAodd : Odd (Nat.card A)) (hA3 : ¬ 3 ∣ Nat.card A)
    (hAT : (A : Set S) * (T : Set S) = (T : Set S) * (A : Set S)) : IsCyclic A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := F134.three_dvd_card_of_statedPSU_three hS
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hS
  have hf1 : 1 ≤ f := by omega
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e₁ : S ≃* hypPSU h 1 1 := e₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
  let Φ₀ : S →* Equiv.Perm (hypIsotropicLines h 1 1) :=
    (hypProjLineAction h 1 1).comp e₁.toMonoidHom
  have hΦ₀ : Function.Injective Φ₀ :=
    (hypProjLineAction_injective h (by norm_num)).comp e₁.injective
  have hrange₀ : Φ₀.range = rkOneG h := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨e₁ s, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e₁.symm y, by simp [Φ₀]⟩
  set U₀ := (rkOneUStar h).comap Φ₀ with hU₀
  have hU₀map : U₀.map Φ₀ = rkOneUStar h := by
    rw [hU₀, Subgroup.map_comap_eq, hrange₀]
    exact inf_eq_right.2 (rkOneUStar_le_rkOneG h)
  have hU₀card : Nat.card U₀ = 2 ^ (f * 3) := by
    rw [← Subgroup.card_map_of_injective hΦ₀, hU₀map, card_rkOneUStar h, ← pow_mul]
  have hcardS : Nat.card S = CFSG.Open.ordTwistedA 2 (2 ^ f) := by
    rw [Nat.card_congr e₀.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf1 hK (by norm_num),
      CFSG.Open.ordTwistedA]
  obtain ⟨r, hr, hr'⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := f) le_rfl hf1).two
  have hidx : U₀.index = r := by
    have hmul := U₀.card_mul_index
    rw [hU₀card, hcardS, hr', show f * (2 * (2 + 1) / 2) = f * 3 by norm_num] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  have hidx2 : ¬ 2 ∣ U₀.index := by
    rw [hidx]
    exact fun h2 => (Nat.not_even_iff_odd.2 hr) (even_iff_two_dvd.2 h2)
  let P₀ : Sylow 2 S := (IsPGroup.of_card hU₀card).toSylow hidx2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P₀ T
  let Φ : S →* Equiv.Perm (hypIsotropicLines h 1 1) := Φ₀.comp (MulAut.conj g⁻¹).toMonoidHom
  have hΦ : Function.Injective Φ := hΦ₀.comp (MulAut.conj g⁻¹).injective
  have hrange : Φ.range = rkOneG h := by
    rw [← hrange₀]
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨g * s * g⁻¹, ?_⟩
      simp only [Φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      congr 1
      group
  have hTU : (rkOneUStar h).comap Φ = (T : Subgroup S) := by
    ext x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def]
    rfl
  refine isCyclic_of_permutable_rkOneUStar h h3 Φ hΦ hrange A hAodd hA3 ?_
  rw [hTU]
  exact hAT

theorem even_unitary_three_three_free_sylow_product_is_cyclic (S : Type) [Group S] [Finite S]
    [IsSimpleGroup S] (_hnonab : ¬ IsMulCommutative S) {f : ℕ} (hf : 2 ≤ f)
    (hS : StatedClassicalModel S .PSU 3 2 f) (T : Sylow 2 S) :
    (∀ A : Subgroup S, Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
      (A : Set S) * (T : Set S) = (T : Set S) * (A : Set S) → IsCyclic A) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ E : Subgroup S, IsElementaryAbelian p E →
      Nat.card E = p ^ 2 → (E : Set S) * (T : Set S) ≠ (T : Set S) * (E : Set S) := by
  have hcyc := fun A hAodd hA3 hAT =>
    isCyclic_of_permutable_sylow_of_statedPSU3 hf hS T A hAodd hA3 hAT
  refine ⟨hcyc, fun p hp hp5 E hE hEcard hET => ?_⟩
  have hEodd : Odd (Nat.card E) := by
    rw [hEcard]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hE3 : ¬ 3 ∣ Nat.card E := by
    rw [hEcard]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have := hcyc E hEodd hE3 hET
  have hexp := IsElementaryAbelian.exponent_dvd_p p E
  rw [IsCyclic.exponent_eq_card, hEcard] at hexp
  have hle := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.two_le]

end CFSG.Quasithin.H13.NQCat
