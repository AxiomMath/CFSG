module

public import CFSG.Quasithin.MS93.S5Q2Par
public import CFSG.Quasithin.MS93.S5B58Sp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5Q2

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem mem_centralizer_of_commute (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {z : ↥M} (hz : a z ∉ commutator (MSP.Sp4 F)) {c : G} (hc : c ∈ Zq M L)
    (hcz : (z : G) * c = c * z) : c ∈ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  by_cases hmc : a ⟨m, hm⟩ ∈ commutator (MSP.Sp4 F)
  · exact commute_of_mem_commutator h hd hmc hc
  · have e := conj_eq_of_not_mem h hd hmc hz hc
    have hzc : (z : G) * c * (z : G)⁻¹ = c := by rw [hcz, mul_inv_cancel_right]
    simp only at e
    rw [hzc] at e
    calc m * c = m * c * m⁻¹ * m := by group
      _ = c * m := by rw [e]

theorem xq_inf_centralizer_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {z : ↥M} (hz : a z ∉ commutator (MSP.Sp4 F)) :
    Xq M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≤
      Uq M T L ⊔ (Zq M L ⊓ Subgroup.centralizer (M : Set G)) := by
  have hlift := (sp4Lift_holds G M T L h 1 F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hZn : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  intro x hx
  obtain ⟨hxX, hxz⟩ := Subgroup.mem_inf.1 hx
  have hZU : Zq M L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (inf_le_left.trans (Xq_le M)).trans hUn
  have hx' : x ∈ ((Uq M T L ⊔ Zq M L : Subgroup G) : Set G) := hXU ▸ hxX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZU] at hx'
  obtain ⟨u, hu, c, hc, rfl⟩ := hx'
  have hzM := z.2
  have huX : u ∈ Xq M := h.Uq_le_Xq hu
  have hcX : c ∈ Xq M := hc.1
  set u' := (z : G) * u * (z : G)⁻¹ with hu'
  set c' := (z : G) * c * (z : G)⁻¹ with hc'
  have hc'Z : c' ∈ Zq M L := (Subgroup.mem_normalizer_iff.1 (hZn hzM) c).1 hc
  have hxz2 : u * c * (z : G) = z * (u * c) := Subgroup.mem_centralizer_singleton_iff.1 hxz
  have hxz' : (z : G) * (u * c) * (z : G)⁻¹ = u * c := by rw [← hxz2, mul_inv_cancel_right]
  have hprod : u' * c' = u * c := by
    rw [hu', hc', ← hxz']
    group
  have hcomm : u' * u⁻¹ = c * c'⁻¹ := by
    have h1 : u' = u * c * c'⁻¹ := by rw [← hprod]; group
    rw [h1]
    have h2 : u * (c * c'⁻¹) = (c * c'⁻¹) * u :=
      mul_comm_of_mem_Xq huX (mul_mem hcX (inv_mem hc'Z.1))
    calc u * c * c'⁻¹ * u⁻¹ = u * (c * c'⁻¹) * u⁻¹ := by group
      _ = c * c'⁻¹ := by rw [h2, mul_inv_cancel_right]
  have hL : (z : G) * u * (z : G)⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [← hu', hcomm]
    exact (mul_mem hc (inv_mem hc'Z)).2
  have hzu : (z : G) * u * (z : G)⁻¹ = u := hlift _ hzM u hu hL
  have hzc : c' = c := by
    have : u' = u := hzu
    rw [this] at hprod
    exact mul_left_cancel hprod
  have hcz : (z : G) * c = c * z := by
    calc (z : G) * c = (z : G) * c * (z : G)⁻¹ * z := by group
      _ = c * z := by rw [← hc', hzc]
  exact Subgroup.mul_mem_sup hu ⟨hc, mem_centralizer_of_commute h hd hz hc hcz⟩

theorem zq_inf_centralizer_le_z0q (h : PUHyp M T L) :
    Zq M L ⊓ Subgroup.centralizer (M : Set G) ≤ Z0q M T := by
  refine le_trans ?_ (le_normalClosureIn (PU.omegaOneCenterOf_le T |>.trans h.le))
  rw [h.omegaOneCenterOf_eq]
  exact le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans (Subgroup.centralizer_le h.le))

theorem not_mem_commutator_of_relIndex_le_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {z : ↥M} (hz2 : ∃ e : ℕ, (z : G) ^ 2 ^ e = 1) (hzO : (z : G) ∉ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer ({(z : G)} : Set G)).relIndex (Uq M T L) ≤ 2) :
    a z ∉ commutator (MSP.Sp4 F) := by
  have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  set E : Subgroup G := Subgroup.closure {(z : G)} with hE
  have hEM : E ≤ M := (Subgroup.closure_le M).2 (Set.singleton_subset_iff.2 z.2)
  have hzE : (z : G) ∈ E := Subgroup.subset_closure rfl
  have hE2 : IsPGroup 2 E := by
    obtain ⟨e, he⟩ := hz2
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hg
    refine ⟨e, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have hEO : ¬ E ≤ pCoreOf 2 M := fun hle => hzO (hle hzE)
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.centralizer ({(z : G)} : Set G) :=
    Subgroup.centralizer_closure _
  obtain ⟨p, hp, hfix⟩ := (S5B.relIndex_centralizer_M h hd hEM hE2 hEO).2
    (by rw [hCE, pow_one]; exact hrel)
  have h3 : Module.finrank F (MSP.fixSp ((E.subgroupOf M).map a)) = 3 := by
    have h1 := MSP.finrank_perp p
    have h2 : Module.finrank F p = 1 := hp
    rw [hfix]
    omega
  obtain ⟨p', hp', -, hĒ⟩ := MSP.exists_point_of_finrank_fixSp_three h3
  have hzĒ : a z ∈ (E.subgroupOf M).map a := ⟨z, Subgroup.mem_subgroupOf.2 hzE, rfl⟩
  have hz1 : a z ≠ 1 := fun h1 => hzO (S5B.mem_pCoreOf_of_ker h hd h1 hz2)
  obtain ⟨v, hv, rfl⟩ := MSP.exists_eq_span_of_isPoint hp'
  obtain ⟨c, hc⟩ := (MSP.mem_xPoint_span hv).1 (hĒ hzĒ)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [MSP.transv_zero] at hc
    exact hz1 hc.symm
  rw [← hc]
  exact MSP.transv_not_mem_commutator_of_card_two hF hv c hc0

end S5Q2

end CFSG.Quasithin.MS93
