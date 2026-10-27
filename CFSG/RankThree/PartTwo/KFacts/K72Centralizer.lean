module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
public import CFSG.RankThree.PartTwo.Sec8.Groups
public import CFSG.GH74.GLS.IVK.L2.FixedSL
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter

section PSL2

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem exists_fixed_iff_of_isField {α : MulAut (PSL2 K)} (hα : (stdPinnedPSL2 K).IsField α)
    (hα3 : α ^ 3 = 1) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ d : MulAut (PSL2 K),
      ∀ y, α y = y ↔ d⁻¹ y ∈ (GH74.GLS.IVK.pslIncl σ).range := by
  obtain ⟨φ, ⟨σ, rfl⟩, hφ1, d, -, rfl⟩ := hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφ3 : psl2FieldAut K σ ^ 3 = 1 := by
    have h1 : (d * psl2FieldAut K σ * d⁻¹) ^ 3 = d * psl2FieldAut K σ ^ 3 * d⁻¹ := conj_pow
    rw [h1] at hα3
    calc psl2FieldAut K σ ^ 3 = d⁻¹ * (d * psl2FieldAut K σ ^ 3 * d⁻¹) * d := by group
      _ = 1 := by rw [hα3]; group
  have hσ3 : orderOf σ = 3 := by
    rw [← orderOf_injective (psl2FieldAut K) (psl2FieldAut_injective K) σ]
    exact orderOf_eq_prime hφ3 hφ1
  refine ⟨σ, hσ3, d, fun y => ?_⟩
  rw [GH74.GLS.IVK.mem_range_pslIncl_iff σ (by rw [hσ3]; decide)]
  constructor
  · intro h
    have h1 : d (psl2FieldAut K σ (d⁻¹ y)) = y := h
    have h2 := congrArg (d⁻¹ : MulAut (PSL2 K)) h1
    rwa [MulAut.inv_apply_self] at h2
  · intro h
    show d (psl2FieldAut K σ (d⁻¹ y)) = y
    rw [h, MulAut.apply_inv_self]

end PSL2

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_barCentralizer_zpowers_iff {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (y : L ⧸ aschbacherSolvableCore 3 L) :
    y ∈ Sec8.barCentralizer (Subgroup.zpowers a) L ↔
      thetaQuotMulAut L (compAction L ⟨a, ha⟩) y = y := by
  rw [Sec8.barCentralizer, FixedPoints.mem_subgroup]
  constructor
  · intro hy
    exact hy ⟨_, mem_autThetaQuot_iff.mpr ⟨a, ha, Subgroup.mem_zpowers a, rfl⟩⟩
  · intro hy τ
    obtain ⟨h, hN, hh, hτ⟩ := mem_autThetaQuot_iff.mp τ.2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hk : (⟨a ^ k, hN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, ha⟩ ^ k :=
      Subtype.ext (by simp)
    have hτ' : (τ : MulAut (L ⧸ aschbacherSolvableCore 3 L)) =
        thetaQuotMulAut L (compAction L ⟨a, ha⟩) ^ k := by
      rw [← hτ, hk, map_zpow, map_zpow]
      rfl
    change (τ : MulAut (L ⧸ aschbacherSolvableCore 3 L)) y = y
    rw [hτ']
    exact MulAction.mem_fixedBy_zpow (show y ∈ MulAction.fixedBy _
      (thetaQuotMulAut L (compAction L ⟨a, ha⟩)) from hy) k

variable {K : Type} [Field K] [Finite K]

theorem exists_barCentralizer_mulEquiv_of_field {a : G} (ha3 : a ^ 3 = 1)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K)
    (ha : InducesKind L (stdPinnedPSL2 K) e a .field) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ Nat.card (GH74.GLS.IVK.fixedField σ) ^ 3 = Nat.card K ∧
      Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃*
        PSL2 (GH74.GLS.IVK.fixedField σ)) := by
  obtain ⟨hN, hfield⟩ := ha
  set τ₀ := thetaQuotMulAut L (compAction L ⟨a, hN⟩) with hτ₀
  set α := inducedAutHom L e ⟨a, hN⟩ with hαdef
  have hα : ∀ y, α (e y) = e (τ₀ y) := fun y => by
    show e (τ₀ (e.symm (e y))) = e (τ₀ y)
    rw [MulEquiv.symm_apply_apply]
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, hN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext ha3
    rw [hαdef, ← map_pow, h1, map_one]
  obtain ⟨σ, hσ3, d, hd⟩ := exists_fixed_iff_of_isField hfield hα3
  have hcard := GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ3] at hcard
  refine ⟨σ, hσ3, hcard, ?_⟩
  set ψ : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K := e.trans d⁻¹ with hψ
  have hψ_apply : ∀ y, ψ y = d⁻¹ (e y) := fun y => rfl
  have hmap : (Sec8.barCentralizer (Subgroup.zpowers a) L).map ψ.toMonoidHom =
      (GH74.GLS.IVK.pslIncl σ).range := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_barCentralizer_zpowers_iff hN] at hy
      rw [MulEquiv.coe_toMonoidHom, hψ_apply]
      exact (hd (e y)).mp (by rw [hα]; exact congrArg e hy)
    · intro hz
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      rw [SetLike.mem_coe, mem_barCentralizer_zpowers_iff hN]
      have h1 : d⁻¹ (e (ψ.symm z)) ∈ (GH74.GLS.IVK.pslIncl σ).range := by
        rw [← hψ_apply, ψ.apply_symm_apply]
        exact hz
      have h2 := (hd (e (ψ.symm z))).mpr h1
      rw [hα] at h2
      exact e.injective h2
  exact ⟨(ψ.subgroupMap _).trans ((MulEquiv.subgroupCongr hmap).trans
    (MonoidHom.ofInjective (GH74.GLS.IVK.pslIncl_injective σ)).symm)⟩

end Bar

theorem isCyclic_sylow_three_psl2 {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3)
    (h4 : 4 ≤ Nat.card F) (Q : Sylow 3 (PSL2 F)) : IsCyclic Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  set p := ringChar F with hp
  have hpr : p.Prime := CharP.char_is_prime F p
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  by_cases hp2 : p = 2
  ·
    have hn2 : 2 ≤ (n : ℕ) := by
      by_contra h
      have h1 : (n : ℕ) = 1 := by have := n.pos; omega
      rw [hcard, hp2, h1] at h4
      norm_num at h4
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hGF : Fintype.card (GaloisField 2 n) = 2 ^ (n : ℕ) := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 n n.ne_zero
    have eF : F ≃+* GaloisField 2 n :=
      FiniteField.ringEquivOfCardEq (by rw [hn, hGF, hp2])
    set e := psl2RingEquiv eF
    have hQ := CFSG.Timmesfeld.RankOne.isCyclic_sylow_psl2 hn2 3 (by norm_num)
      (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
    change IsCyclic ((Q : Subgroup (PSL2 F)).map e.toMonoidHom) at hQ
    exact isCyclic_of_surjective
      ((Q : Subgroup (PSL2 F)).equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
      ((Q : Subgroup (PSL2 F)).equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  · exact CFSG.SectionRank.OddCover.psl_two_sylow_isCyclic hpr hp2 hcard (by norm_num)
      (fun h => h3 h.symm) Q

end CFSG.RankThree.PartTwo.KFacts
