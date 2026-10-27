module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rb
public import CFSG.Walter.W67.W1Basic
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

theorem exists_conj_mem_funSet {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X}, 𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    {K₀ : Subgroup X} (hK₀ : 𝔉 ⊤ K₀) (P : Sylow 2 X) :
    ∃ g : X, K₀.map (MulAut.conj g).toMonoidHom ∈ FunSet 𝔉 X (P : Subgroup X) := by
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 K₀
  obtain ⟨g, -, hg⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow ⊤ P le_top Q
    le_top hQ.isPGroup
  refine ⟨g, hconj g hK₀, ?_⟩
  have hS : IsSylowOf 2 (Q.map (MulAut.conj g).toMonoidHom)
      (K₀.map (MulAut.conj g).toMonoidHom) := by
    simpa only [CFSG.Open.uniqueFourConj, inv_inv] using
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_isSylowOf_conj hQ g⁻¹
  have heq := hS.eq_of_le (le_inf hg hS.le) inf_le_right (P.isPGroup'.to_inf_left)
  rw [heq]
  exact hS

theorem exists_conj_pair_mem_funSet {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X}, 𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    {K₁ K₂ : Subgroup X} (h₁ : 𝔉 ⊤ K₁) (h₂ : 𝔉 ⊤ K₂) (hc : ⁅K₁, K₂⁆ = ⊥) (P : Sylow 2 X) :
    ∃ g : X, K₁.map (MulAut.conj g).toMonoidHom ∈ FunSet 𝔉 X (P : Subgroup X) ∧
      K₂.map (MulAut.conj g).toMonoidHom ∈ FunSet 𝔉 X (P : Subgroup X) := by
  have h21 : K₂ ≤ Subgroup.centralizer (K₁ : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc
  have h12 : K₁ ≤ Subgroup.centralizer (K₂ : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hN₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set X) :=
    sup_le Subgroup.le_normalizer (h21.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set X) :=
    sup_le (h12.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (K₁ ⊔ K₂)
  have hQ₁ := hQ.inf_of_le_normalizer le_sup_left hN₁
  have hQ₂ := hQ.inf_of_le_normalizer le_sup_right hN₂
  obtain ⟨g, -, hg⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow ⊤ P le_top Q
    le_top hQ.isPGroup
  have key : ∀ {K : Subgroup X}, IsSylowOf 2 (Q ⊓ K) K →
      IsSylowOf 2 ((P : Subgroup X) ⊓ K.map (MulAut.conj g).toMonoidHom)
        (K.map (MulAut.conj g).toMonoidHom) := by
    intro K hK
    have hS : IsSylowOf 2 ((Q ⊓ K).map (MulAut.conj g).toMonoidHom)
        (K.map (MulAut.conj g).toMonoidHom) := by
      simpa only [CFSG.Open.uniqueFourConj, inv_inv] using
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_isSylowOf_conj hK g⁻¹
    have heq := hS.eq_of_le (le_inf ((Subgroup.map_mono inf_le_left).trans hg) hS.le)
      inf_le_right P.isPGroup'.to_inf_left
    rw [heq]
    exact hS
  exact ⟨g, ⟨hconj g h₁, key hQ₁⟩, ⟨hconj g h₂, key hQ₂⟩⟩

theorem commute_of_map_mem_map {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) {R S : Subgroup U}
    (hRS : ∀ x ∈ R, ∀ y ∈ S, x * y = y * x) {a : U} (ha : a ∈ R) (haS : ψ a ∈ S.map ψ) :
    ∀ y ∈ R, a * y = y * a := by
  obtain ⟨b, hb, hab⟩ := haS
  have hc : b⁻¹ * a ∈ Subgroup.center U := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel])
  have ha' : a = b * (b⁻¹ * a) := by group
  intro y hy
  rw [ha', mul_assoc, (Subgroup.mem_center_iff.mp hc y).symm, ← mul_assoc,
    (hRS y hy b hb).symm, mul_assoc]

section ElemAbelian

open scoped MatrixGroups

theorem exists_orderOf_of_equiv_sl2 {U F : Type} [Group U] [Field F] [Finite F]
    {R : Subgroup U} (e : R ≃* SL(2, F)) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ∣ Nat.card F * (Nat.card F ^ 2 - 1)) : ∃ a ∈ R, orderOf a = ℓ := by
  have hcard : Nat.card R = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  have : Finite R := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hF1
    exact Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ (hcard ▸ hℓ)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem exists_elemAbelian_sq_of_equiv_sl2 {U X F : Type} [Group U] [Group X] [Field F]
    [Finite F] {r k : ℕ} [Fact r.Prime] [CharP F r] (hk : 2 ≤ k) (hF : Nat.card F = r ^ k)
    (ψ : U →* X) (hker : ψ.ker ≤ Subgroup.center U) {R : Subgroup U} (e : R ≃* SL(2, F)) :
    ∃ E : Subgroup X, IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ E ≤ R.map ψ := by
  classical
  let up := CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup.upper F
  let φ : Multiplicative F →* X := ψ.comp (R.subtype.comp (e.symm.toMonoidHom.comp up))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hk' : ((e.symm (up a) : R) : U) ∈ Subgroup.center U := hker (MonoidHom.mem_ker.2 ha)
    have hzR : e.symm (up a) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hk' g)
    have hz : up a ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      have h1 : up a = e (e.symm (up a)) := (e.apply_symm_apply _).symm
      rw [h1, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzR y]
    apply CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup.psl_upper_injective
    rw [map_one]
    exact (QuotientGroup.eq_one_iff _).mpr hz
  have hcardM : Nat.card (Multiplicative F) = r ^ k := by
    rw [Nat.card_congr Multiplicative.toAdd, hF]
  have : Finite (Multiplicative F) := Finite.of_equiv F Multiplicative.ofAdd
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime r (n := 2)
    (by rw [hcardM]; exact pow_dvd_pow r hk)
  have hBe : IsElemAbelian r B := by
    refine ⟨⟨⟨fun x y => Subtype.ext (mul_comm (x : Multiplicative F) y)⟩⟩, fun x _ => ?_⟩
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one]
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  refine ⟨B.map φ, hBe.map φ, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hφ, hB]
  · rintro _ ⟨a, -, rfl⟩
    exact ⟨_, (e.symm (up a)).2, rfl⟩

theorem exists_elemAbelian_sq_of_commutes {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) {R S : Subgroup U}
    (hRS : ∀ x ∈ R, ∀ y ∈ S, x * y = y * x)
    (hR2 : ∀ c ∈ R, (∀ y ∈ R, c * y = y * c) → c * c = 1)
    (hS2 : ∀ c ∈ S, (∀ y ∈ S, c * y = y * c) → c * c = 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {a b : U} (ha : a ∈ R) (hb : b ∈ S)
    (hao : orderOf a = ℓ) (hbo : orderOf b = ℓ) :
    ∃ E : Subgroup X, IsElemAbelian ℓ E ∧ Nat.card E = ℓ ^ 2 ∧ E ≤ R.map ψ ⊔ S.map ψ := by
  have hcop : Nat.gcd 2 ℓ = 1 := (Nat.coprime_primes Nat.prime_two hℓ).mpr (Ne.symm hℓ2)
  have key : ∀ {T T' : Subgroup U}, (∀ x ∈ T, ∀ y ∈ T', x * y = y * x) →
      (∀ c ∈ T, (∀ y ∈ T, c * y = y * c) → c * c = 1) →
      ∀ {c : U}, c ∈ T → c ^ ℓ = 1 → ψ c ∈ T'.map ψ → c = 1 := by
    intro T T' hTT' hT2 c hc hcℓ hcT'
    have h2 : c ^ 2 = 1 := by
      rw [sq]
      exact hT2 c hc (commute_of_map_mem_map ψ hker hTT' hc hcT')
    have hd : orderOf c ∣ Nat.gcd 2 ℓ :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hcℓ)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hSR : ∀ x ∈ S, ∀ y ∈ R, x * y = y * x := fun x hx y hy => (hRS y hy x hx).symm
  have haℓ : a ^ ℓ = 1 := hao ▸ pow_orderOf_eq_one a
  have hbℓ : b ^ ℓ = 1 := hbo ▸ pow_orderOf_eq_one b
  have hψa1 : ψ a ≠ 1 := by
    intro h
    have h1 : a = 1 := key hRS hR2 ha haℓ (by rw [h]; exact Subgroup.one_mem _)
    rw [h1, orderOf_one] at hao
    exact hℓ.one_lt.ne hao
  have hψb1 : ψ b ≠ 1 := by
    intro h
    have h1 : b = 1 := key hSR hS2 hb hbℓ (by rw [h]; exact Subgroup.one_mem _)
    rw [h1, orderOf_one] at hbo
    exact hℓ.one_lt.ne hbo
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hψaℓ : ψ a ^ ℓ = 1 := by rw [← map_pow, haℓ, map_one]
  have hψbℓ : ψ b ^ ℓ = 1 := by rw [← map_pow, hbℓ, map_one]
  have hoa : orderOf (ψ a) = ℓ := orderOf_eq_prime hψaℓ hψa1
  have hob : orderOf (ψ b) = ℓ := orderOf_eq_prime hψbℓ hψb1
  have hAB : Subgroup.zpowers (ψ a) ⊓ Subgroup.zpowers (ψ b) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxA
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxB
    have hmem : ψ (a ^ i) ∈ S.map ψ := by
      rw [map_zpow, ← hj]
      exact ⟨b ^ j, S.zpow_mem hb j, map_zpow ψ b j⟩
    have hiℓ : (a ^ i) ^ ℓ = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, haℓ, one_zpow]
    have h1 : a ^ i = 1 := key hRS hR2 (R.zpow_mem ha i) hiℓ hmem
    rw [Subgroup.mem_bot, ← map_zpow, h1, map_one]
  have hc : ∀ x ∈ Subgroup.zpowers (ψ a), ∀ y ∈ Subgroup.zpowers (ψ b), x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hab : Commute (ψ a) (ψ b) := by
      show ψ a * ψ b = ψ b * ψ a
      rw [← map_mul, ← map_mul, hRS a ha b hb]
    exact (hab.zpow_zpow i j).eq
  have hE : IsElemAbelian ℓ (Subgroup.zpowers (ψ a) ⊔ Subgroup.zpowers (ψ b)) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hψaℓ)
      (CFSG.Open.isElemAbelian_zpowers hψbℓ) hc
  have hEc : Nat.card ↥(Subgroup.zpowers (ψ a) ⊔ Subgroup.zpowers (ψ b)) = ℓ ^ 2 := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (Subgroup.zpowers (ψ a))
      (Subgroup.zpowers (ψ b)) hc).1
    rw [hAB, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hob] at h
    rw [h, sq]
  exact ⟨_, hE, hEc, sup_le_sup (Subgroup.zpowers_le.mpr ⟨a, ha, rfl⟩)
    (Subgroup.zpowers_le.mpr ⟨b, hb, rfl⟩)⟩

end ElemAbelian

section FunPair

open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver fundPred isFundamentalOver_map_mulEquiv)


theorem exists_funSet_pair {X : Type} [Group X] [Finite X] {q : ℕ} {U : Type} [Group U]
    (ψ : U →* X) (hker : ψ.ker ≤ Subgroup.center U) {R S : Subgroup U}
    (hRf : IsFundamentalOver q (R.map ψ)) (hSf : IsFundamentalOver q (S.map ψ))
    (hRS : ∀ x ∈ R, ∀ y ∈ S, x * y = y * x)
    (hR2 : ∀ c ∈ R, (∀ y ∈ R, c * y = y * c) → c * c = 1)
    (hS2 : ∀ c ∈ S, (∀ y ∈ S, c * y = y * c) → c * c = 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {a b : U} (ha : a ∈ R) (hb : b ∈ S)
    (hao : orderOf a = ℓ) (hbo : orderOf b = ℓ) (P : Sylow 2 X) :
    ∃ K₁ K₂ : Subgroup X, K₁ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
      K₂ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
      ∃ E : Subgroup X, IsElemAbelian ℓ E ∧ Nat.card E = ℓ ^ 2 ∧ E ≤ K₁ ⊔ K₂ := by
  obtain ⟨E, hE, hEc, hEle⟩ :=
    exists_elemAbelian_sq_of_commutes ψ hker hRS hR2 hS2 hℓ hℓ2 ha hb hao hbo
  have hRS' : ⁅R, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hRS x hx y hy).symm
  have hc : ⁅R.map ψ, S.map ψ⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, hRS', Subgroup.map_bot]
  obtain ⟨g, h1, h2⟩ := exists_conj_pair_mem_funSet (𝔉 := fundPred q)
    (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) hRf hSf hc P
  refine ⟨_, _, h1, h2, E.map (MulAut.conj g).toMonoidHom, hE.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
  · rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hEle

theorem exists_funSet_single {X : Type} [Group X] [Finite X] {q : ℕ} {K : Subgroup X}
    (hK : IsFundamentalOver q K) {ℓ : ℕ} {E : Subgroup X} (hE : IsElemAbelian ℓ E)
    (hEc : Nat.card E = ℓ ^ 2) (hEK : E ≤ K) (P : Sylow 2 X) :
    ∃ K₁ K₂ : Subgroup X, K₁ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
      K₂ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
      ∃ E : Subgroup X, IsElemAbelian ℓ E ∧ Nat.card E = ℓ ^ 2 ∧ E ≤ K₁ ⊔ K₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_funSet (𝔉 := fundPred q)
    (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) hK P
  refine ⟨_, _, hg, hg, E.map (MulAut.conj g).toMonoidHom, hE.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
  · exact (Subgroup.map_mono hEK).trans le_sup_left

end FunPair

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie
