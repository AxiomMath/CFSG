module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Quasithin.H13.NQCatUnitary

public section

namespace CFSG.Quasithin.F134.LieU3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

theorem le_stabilizer_of_not_dvd_card {G Ω : Type*} [Group G] [MulAction G Ω] (α : Ω)
    {U H : Subgroup G} (hUH : U ≤ H) (hUt : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃ u ∈ U, u • β = γ)
    (hH : ¬ Nat.card Ω ∣ Nat.card H) : H ≤ MulAction.stabilizer G α := by
  intro m hm
  by_contra hmα
  rw [MulAction.mem_stabilizer_iff] at hmα
  have horbit : MulAction.orbit H α = Set.univ := by
    refine Set.eq_univ_of_forall fun β => ?_
    by_cases hβ : β = α
    · rw [hβ]
      exact MulAction.mem_orbit_self α
    · obtain ⟨u, hu, huβ⟩ := hUt (m • α) β hmα hβ
      refine ⟨⟨u * m, H.mul_mem (hUH hu) hm⟩, ?_⟩
      change (u * m) • α = β
      rw [mul_smul, huβ]
  have hidx := MulAction.index_stabilizer H α
  rw [horbit, Set.ncard_univ] at hidx
  exact hH (hidx ▸ Subgroup.index_dvd_card _)

variable {p f : ℕ} {K : Type} [Field K]

theorem card_hypIsotropicLines_one (h : UnitaryFieldData p f K) :
    Nat.card (hypIsotropicLines h 1 1) = (p ^ f) ^ 3 + 1 := by
  have h1 := card_hypLines h (r := 1) (ε := 1) le_rfl
  have hq : (2 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast two_le_q h
  have hq1 : ((p ^ f : ℕ) : ℤ) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) ^ 2 := by nlinarith
    intro h0
    linarith
  have h2 : (Nat.card (hypIsotropicLines h 1 1) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 3 + 1 := by
    refine mul_right_cancel₀ hq1 ?_
    rw [h1]
    norm_num
  exact_mod_cast h2

theorem le_stabilizer_infL_of_not_dvd (h : UnitaryFieldData p f K)
    {H : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1))} (hUH : rkOneUStar h ≤ H)
    (hH : ¬ (p ^ f) ^ 3 + 1 ∣ Nat.card H) :
    H ≤ MulAction.stabilizer (Equiv.Perm (hypIsotropicLines h 1 1)) (infL h) := by
  refine le_stabilizer_of_not_dvd_card (infL h) hUH (fun β γ hβ hγ => ?_)
    (by rwa [card_hypIsotropicLines_one])
  obtain ⟨a₁, b₁, hab₁, rfl⟩ := exists_rkPtL_eq β hβ
  obtain ⟨a₂, b₂, hab₂, rfl⟩ := exists_rkPtL_eq γ hγ
  refine ⟨rkOneU h a₂ b₂ hab₂ * (rkOneU h a₁ b₁ hab₁)⁻¹,
    (rkOneUStar h).mul_mem (rkOneU_mem h hab₂) ((rkOneUStar h).inv_mem (rkOneU_mem h hab₁)), ?_⟩
  rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, ← rkOneU_zeroL h hab₁,
    Equiv.Perm.inv_eq_iff_eq.mpr rfl, rkOneU_zeroL]

theorem isCyclic_rkOneGInf_quotient (h : UnitaryFieldData p f K)
    [((rkOneUStar h).subgroupOf (rkOneGInf h)).Normal] :
    IsCyclic (rkOneGInf h ⧸ (rkOneUStar h).subgroupOf (rkOneGInf h)) := by
  have := h.finite
  obtain ⟨-, ⟨eT, -⟩, -⟩ := unitary_rank_one_torus_action h
  have : IsCyclic (rkOneT h) := isCyclic_of_injective eT.toMonoidHom eT.injective
  exact H13.NQCat.isCyclic_quotient_of_forall_eq_mul (rkOneUStar_le_rkOneGInf h)
    (rkOneT_le_rkOneGInf h) fun x hx => (mem_rkOneGInf_iff h).1 hx

theorem isCyclic_of_le_rkOneGInf (h : UnitaryFieldData p f K)
    {A : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1))} (hA : A ≤ rkOneGInf h)
    (hAp : ¬ p ∣ Nat.card A) : IsCyclic A := by
  have := rkOneUStar_normal h
  have := isCyclic_rkOneGInf_quotient h
  have hcop : (Nat.card A).Coprime p := ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hAp).symm
  have hAU : A ⊓ rkOneUStar h = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [card_rkOneUStar h]
    exact Nat.Coprime.pow_right 3 (Nat.Coprime.pow_right f hcop)
  refine isCyclic_of_injective
    ((QuotientGroup.mk' ((rkOneUStar h).subgroupOf (rkOneGInf h))).comp
      (Subgroup.inclusion hA)) ?_
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : Subgroup.inclusion hA a ∈ (rkOneUStar h).subgroupOf (rkOneGInf h) :=
    (QuotientGroup.eq_one_iff _).1 ha
  have h2 : (a : Equiv.Perm (hypIsotropicLines h 1 1)) ∈ A ⊓ rkOneUStar h :=
    ⟨a.2, Subgroup.mem_subgroupOf.mp h1⟩
  rw [hAU, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem exists_perm_comap_rkOneUStar_eq {S : Type} [Group S] [Finite S]
    (hS : StatedClassicalModel S .PSU 3 p f) (T : Sylow p S) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K)
      (Φ : S →* Equiv.Perm (hypIsotropicLines h 1 1)),
      Function.Injective Φ ∧ Φ.range = rkOneG h ∧ (rkOneUStar h).comap Φ = T := by
  obtain ⟨⟨hp, hf1, -⟩, K, _, _, hK, ⟨e₀⟩⟩ := hS
  have : Fact p.Prime := ⟨hp⟩
  have h : UnitaryFieldData p f K := ⟨hp, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  obtain ⟨e₁, -⟩ : ∃ e₁ : S ≃* hypPSU h 1 1,
      e₁ = e₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm := ⟨_, rfl⟩
  have hρ := hypProjLineAction_injective h (r := 1) (ε := 1) (by norm_num)
  have he₁ : e₁.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e₁.surjective
  have he₁inj : Function.Injective e₁.toMonoidHom := e₁.injective
  obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ₀ : S →* Equiv.Perm (hypIsotropicLines h 1 1),
      Φ₀ = (hypProjLineAction h 1 1).comp e₁.toMonoidHom := ⟨_, rfl⟩
  have hΦ₀inj : Function.Injective Φ₀ := by
    rw [hΦ₀]
    exact hρ.comp he₁inj
  have hrange₀ : Φ₀.range = rkOneG h := by
    rw [hΦ₀, MonoidHom.range_comp, he₁, ← MonoidHom.range_eq_map]
    rfl
  obtain ⟨-, -, -, -, ⟨P, hP⟩, -, -⟩ :=
    unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hPle : (P : Subgroup (hypPSU h 1 1)) ≤ e₁.toMonoidHom.range := by
    rw [he₁]
    exact le_top
  have hP₀ : ((P.comapOfInjective e₁.toMonoidHom he₁inj hPle : Sylow p S) :
      Subgroup S) = (rkOneUStar h).comap Φ₀ := by
    rw [Sylow.coe_comapOfInjective, hP, hΦ₀, ← Subgroup.comap_comap]
    change _ = (((hypProjUnitriangular h 1 1).map (hypProjLineAction h 1 1)).comap
      (hypProjLineAction h 1 1)).comap e₁.toMonoidHom
    rw [Subgroup.comap_map_eq_self_of_injective hρ]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S
    (P.comapOfInjective e₁.toMonoidHom he₁inj hPle) T
  refine ⟨K, inferInstance, h, Φ₀.comp (MulAut.conj g⁻¹).toMonoidHom,
    hΦ₀inj.comp (MulAut.conj g⁻¹).injective, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj g⁻¹).surjective,
      ← MonoidHom.range_eq_map, hrange₀]
  · ext x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, hP₀]
    rfl

theorem not_dvd_nine_mul_cube {q : ℕ} (hq : 3 ≤ q) : ¬ q ^ 3 + 1 ∣ 9 * q ^ 3 := by
  intro hdvd
  have hcop : (q ^ 3 + 1).Coprime (q ^ 3) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have h9 := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  omega

end CFSG.Quasithin.F134.LieU3

namespace CFSG.Quasithin.P134

open CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieU3 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem facts134E9_psu3Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n := by
  intro n A _ _ L P T hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 3 ≤ 2 ^ n := by
    obtain ⟨-, hn1, -, hne⟩ := hL.1
    have hn : 2 ≤ n := by
      by_contra hlt
      obtain rfl : n = 1 := by omega
      exact hne rfl
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨K, _, h, Φ, hΦ, hrange, hTU⟩ := exists_perm_comap_rkOneUStar_eq hL
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace hTU : (rkOneUStar h).comap Φ = (T ⊓ L).subgroupOf L := hTU
  have hcardU : Nat.card (T ⊓ L : Subgroup A) = (2 ^ n) ^ 3 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ← hTU,
      ← Subgroup.card_map_of_injective hΦ, Subgroup.map_comap_eq, hrange,
      inf_eq_right.2 (rkOneUStar_le_rkOneG h), card_rkOneUStar h]
  have hUH : rkOneUStar h ≤ ((P ⊔ T ⊓ L).subgroupOf L).map Φ := by
    intro x hx
    have hx' : x ∈ Φ.range := by
      rw [hrange]
      exact rkOneUStar_le_rkOneG h hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ (rkOneUStar h).comap Φ := hx
    rw [hTU] at hy
    exact ⟨y, Subgroup.subgroupOf_mono _ le_sup_right hy, rfl⟩
  have hcardH : Nat.card (((P ⊔ T ⊓ L).subgroupOf L).map Φ) = 9 * (2 ^ n) ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E9Config.sup_inf_le hcfg)).toEquiv,
      E9Config.card_sup_inf hcfg, hcardU]
  have hfix := le_stabilizer_infL_of_not_dvd h hUH (by
    rw [hcardH]
    exact not_dvd_nine_mul_cube hq)
  have hQinf : (P.subgroupOf L).map Φ ≤ rkOneGInf h := fun x hx =>
    ⟨hrange ▸ Subgroup.map_le_range Φ _ hx,
      hfix (Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_left) hx)⟩
  have hQcard : Nat.card ((P.subgroupOf L).map Φ) = 9 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hQexp : ∀ x ∈ (P.subgroupOf L).map Φ, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 :=
      Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy3, map_one]
  exact not_isCyclic_of_card_nine hQcard hQexp
    (isCyclic_of_le_rkOneGInf h hQinf (by rw [hQcard]; norm_num))

end CFSG.Quasithin.P134
