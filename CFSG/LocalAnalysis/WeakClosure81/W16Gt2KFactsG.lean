module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Out21.A6

private theorem exists_mem_pow_two_ne_one_sylow (S : Sylow 2 (alternatingGroup (Fin 6))) :
    ∃ x ∈ (S : Subgroup (alternatingGroup (Fin 6))), x ^ 2 ≠ 1 := by
  let σ : Equiv.Perm (Fin 6) := (List.formPerm [(0 : Fin 6), 1, 2, 3]) * Equiv.swap 4 5
  have hσ : σ ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  let x₀ : alternatingGroup (Fin 6) := ⟨σ, hσ⟩
  have hx₀2 : x₀ ^ 2 ≠ 1 := by
    intro h
    have h1 : σ ^ 2 = 1 := congrArg Subtype.val h
    revert h1
    decide
  have hx₀4 : x₀ ^ 4 = 1 := by
    apply Subtype.ext
    show σ ^ 4 = 1
    decide
  have hp : IsPGroup 2 (Subgroup.zpowers x₀) := by
    have hord : orderOf x₀ = 2 ^ 2 := by
      have h1 : orderOf x₀ ∣ 4 := orderOf_dvd_of_pow_eq_one hx₀4
      have h2 : ¬ orderOf x₀ ∣ 2 := fun h =>
        hx₀2 (orderOf_dvd_iff_pow_eq_one.mp h)
      have : orderOf x₀ ∈ Nat.divisors 4 := by simp [h1]
      have hd : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact absurd (by rw [h]; exact one_dvd _) h2
      · exact absurd (by rw [h]) h2
      · rw [h]; norm_num
    exact IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) P S
  have hx₀P : x₀ ∈ (P : Subgroup (alternatingGroup (Fin 6))) :=
    hP (Subgroup.mem_zpowers x₀)
  have hy : (MulAut.conj g) x₀ ∈ (S : Subgroup (alternatingGroup (Fin 6))) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x₀, hx₀P, rfl⟩
  refine ⟨(MulAut.conj g) x₀, hy, fun h => hx₀2 ?_⟩
  rw [← map_pow] at h
  exact (MulAut.conj g).injective (h.trans (map_one _).symm)

theorem kFacts_rank_A6 :
    ∀ E : Subgroup (alternatingGroup (Fin 6)), IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  intro E hE
  by_contra hgt
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  obtain ⟨k, hk⟩ := (IsElemAbelian.isPGroup hE).exists_card_eq
  have hdvd : 2 ^ k ∣ 360 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card E
  have hk3 : k ≤ 3 := by
    by_contra h
    have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (not_le.mp h)
    have := (h4.trans hdvd)
    omega
  have h8 : Nat.card E = 8 := by
    have h2k : 4 < 2 ^ k := hk ▸ not_le.mp hgt
    interval_cases k <;> simp_all
  have hidx : ¬ 2 ∣ E.index := by
    have h := E.card_mul_index
    rw [h8, hcard] at h
    have : E.index = 45 := by omega
    rw [this]; norm_num
  let S : Sylow 2 (alternatingGroup (Fin 6)) := (IsElemAbelian.isPGroup hE).toSylow hidx
  obtain ⟨x, hxS, hx⟩ := exists_mem_pow_two_ne_one_sylow S
  exact hx (hE.2 x hxS)

private theorem mem_range_conj_of_thetaEquiv_mem_psl29 {K : Type} [Group K]
    (φ : K ≃* ↥CFSG.QuasithinUnique.A6Models.psl29) (γ : MulAut K)
    (hγ : ((CFSG.QuasithinUnique.Unc25K1.A6Model.thetaEquiv φ γ :
      ↥CFSG.QuasithinUnique.A6Models.autA6) : Equiv.Perm (Fin 10)) ∈
        CFSG.QuasithinUnique.A6Models.psl29) :
    γ ∈ (MulAut.conj : K →* MulAut K).range := by
  set b : ↥A6Models.autA6 := CFSG.QuasithinUnique.Unc25K1.A6Model.thetaEquiv φ γ with hb
  refine ⟨φ.symm ⟨(b : P10), hγ⟩, MulEquiv.ext fun k => ?_⟩
  apply φ.injective
  apply Subtype.ext
  have hspec := CFSG.QuasithinUnique.Unc25K1.A6Model.thetaEquiv_spec φ γ k
  rw [← hb] at hspec
  rw [hspec, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have : φ (φ.symm ⟨(b : P10), hγ⟩) = ⟨(b : P10), hγ⟩ := by simp
  rw [this]
  rfl

private theorem card_le_two_of_isElemAbelian_autA6
    (E : Subgroup ↥CFSG.QuasithinUnique.A6Models.autA6) (hE : IsElemAbelian 2 E)
    (hEN : E ⊓ CFSG.QuasithinUnique.A6Models.psl29.subgroupOf
      CFSG.QuasithinUnique.A6Models.autA6 = ⊥) : Nat.card E ≤ 2 := by
  set N : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6 with hN
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using psl29_normal (g : P10) g.2 (n : P10) hn⟩
  have hcardN : Nat.card N = 360 := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
  have hQ : Nat.card (↥A6Models.autA6 ⧸ N) = 4 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [card_autA6, hcardN] at this
    omega
  set f : E →* (↥A6Models.autA6 ⧸ N) := (QuotientGroup.mk' N).comp E.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : ↥A6Models.autA6) ∈ N := by
      have := hx
      simpa [hf, QuotientGroup.eq_one_iff] using this
    have : (x : ↥A6Models.autA6) ∈ E ⊓ N := ⟨x.2, hxN⟩
    rw [hEN] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hle : Nat.card E ≤ 4 := hQ ▸ Nat.card_le_card_of_injective f hinj
  obtain ⟨k, hk⟩ := (IsElemAbelian.isPGroup hE).exists_card_eq
  by_contra hgt
  have h4 : Nat.card E = 4 := by
    have h2k : 2 < 2 ^ k := hk ▸ not_le.mp hgt
    have h2k4 : 2 ^ k ≤ 4 := hk ▸ hle
    have hk2 : k ≤ 2 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_le.mp h)
      omega
    interval_cases k <;> simp_all
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hQ, h4])
  obtain ⟨e, he⟩ := hbij.2 (QuotientGroup.mk ⟨A6Models.tMulFrob, tMulFrob_mem_autA6⟩)
  have he' : (e : ↥A6Models.autA6)⁻¹ * ⟨A6Models.tMulFrob, tMulFrob_mem_autA6⟩ ∈ N :=
    QuotientGroup.eq.mp he
  have hep : ((e : ↥A6Models.autA6) : P10)⁻¹ * A6Models.tMulFrob ∈ A6Models.psl29 :=
    Subgroup.mem_subgroupOf.mp he'
  have hem10 : ((e : ↥A6Models.autA6) : P10) ∈ A6Models.m10 := by
    have : ((e : ↥A6Models.autA6) : P10) =
        A6Models.tMulFrob * (((e : ↥A6Models.autA6) : P10)⁻¹ * A6Models.tMulFrob)⁻¹ := by
      group
    rw [this]
    exact A6Models.m10.mul_mem tMulFrob_mem_m10
      (A6Models.m10.inv_mem (psl29_le_m10 hep))
  have hee : ((e : ↥A6Models.autA6) : P10) * ((e : ↥A6Models.autA6) : P10) = 1 := by
    have := hE.2 e e.2
    rw [pow_two] at this
    exact congrArg (fun z : ↥A6Models.autA6 => (z : P10)) this
  have hepsl := m10_involution_mem_psl29 hem10 hee
  have heN : (e : ↥A6Models.autA6) ∈ E ⊓ N := ⟨e.2, Subgroup.mem_subgroupOf.mpr hepsl⟩
  rw [hEN] at heN
  have he1 : e = 1 := Subtype.ext (Subgroup.mem_bot.mp heN)
  rw [he1, map_one] at he
  have h1 : (⟨A6Models.tMulFrob, tMulFrob_mem_autA6⟩ : ↥A6Models.autA6) ∈ N := by
    have := QuotientGroup.eq.mp he
    simpa using this
  exact tMulFrob_not_mem_psl29 (Subgroup.mem_subgroupOf.mp h1)

theorem kFacts_rank_out_A6 :
    ∀ E : Subgroup (MulAut (alternatingGroup (Fin 6))), IsElemAbelian 2 E →
      E ⊓ (MulAut.conj : alternatingGroup (Fin 6) →* _).range = ⊥ → Nat.card E ≤ 2 := by
  intro E hE hEI
  obtain ⟨-, ψ, -, -⟩ := CFSG.QuasithinUnique.Unc25K1.A6Model.exists_pslEquiv
  set φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm with hφ
  set θ := CFSG.QuasithinUnique.Unc25K1.A6Model.thetaEquiv φ with hθ
  have hE' : IsElemAbelian 2 (E.map θ.toMonoidHom) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      apply Subtype.ext
      show θ a * θ b = θ b * θ a
      rw [← map_mul, ← map_mul]
      exact congrArg (fun z : E => θ z) this
    · rintro _ ⟨a, ha, rfl⟩
      show θ a ^ 2 = 1
      rw [← map_pow]
      simp [hE.2 a ha]
  have hcard : Nat.card (E.map θ.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective θ.injective
  have hEN : E.map θ.toMonoidHom ⊓ A6Models.psl29.subgroupOf A6Models.autA6 = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨⟨γ, hγE, rfl⟩, hbN⟩
    have hb : ((θ γ : ↥A6Models.autA6) : P10) ∈ A6Models.psl29 :=
      Subgroup.mem_subgroupOf.mp hbN
    have hγI := mem_range_conj_of_thetaEquiv_mem_psl29 φ γ hb
    have : γ ∈ E ⊓ (MulAut.conj : alternatingGroup (Fin 6) →* _).range := ⟨hγE, hγI⟩
    rw [hEI] at this
    have hγ1 : γ = 1 := Subgroup.mem_bot.mp this
    show θ γ = 1
    rw [hγ1, map_one]
  rw [← hcard]
  exact card_le_two_of_isElemAbelian_autA6 _ hE' hEN

end CFSG.LocalAnalysis.WeakClosure81
