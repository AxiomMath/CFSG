module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Rows
public import CFSG.RankThree.PartTwo.Sec8.Hering418Cfg

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

section Core

variable {G : Type} [Group G] [Finite G]

theorem Cfg.false_of_outer_core {L K : Subgroup G} {a b : G} (c : Cfg L K a b)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinn : ∃ j : ℕ, c.alpha * c.beta ^ j ∈ innBar L)
    (hC : Sec8.barCentralizer (Subgroup.zpowers b) L ≤ Sec8.imageModTheta L K) : False := by
  obtain ⟨j, x, hx⟩ := hinn
  have hab : Commute c.alpha c.beta := c.alpha_mul_beta
  have hcomm : Commute c.alpha (c.beta ^ j) := hab.pow_right j
  have hcomm' : Commute c.beta (c.alpha * c.beta ^ j) :=
    Commute.mul_right hab.symm ((Commute.refl c.beta).pow_right j)
  have hx3 : x ^ 3 = 1 := by
    have h3 : (c.alpha * c.beta ^ j) ^ 3 = 1 := by
      rw [hcomm.mul_pow, c.alpha_pow_three, one_mul, ← pow_mul, mul_comm, pow_mul,
        c.beta_pow_three, one_pow]
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow, hx, h3]
    have hz := mem_center_of_conj_eq_one h1
    rw [hZ] at hz
    exact hz
  have hxC : x ∈ Sec8.barCentralizer (Subgroup.zpowers b) L := by
    rw [KFacts.mem_barCentralizer_zpowers_iff c.hbL]
    have h1 : c.beta * MulAut.conj x * c.beta⁻¹ = MulAut.conj x := by
      rw [hx, hcomm'.eq, mul_inv_cancel_right]
    have h2 : MulAut.conj (c.beta x) = MulAut.conj x := by
      rw [← KFacts.mul_mulAutConj_mul_inv, h1]
    have h3 : c.beta x * x⁻¹ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
      mem_center_of_conj_eq_one (by rw [map_mul, map_inv, h2, mul_inv_cancel])
    rw [hZ, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨k', hk', hk'x⟩ := hC hxC
  have hkK : (k' : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
  have hkL : (k' : G) ∈ L := k'.2
  refine rho_pow_mul_ne c.hKL c.hKb c.ha3 c.haL c.hbL c.haK c.hout (i := 1) (j := j)
    (by norm_num) hkK ?_
  rw [rho_eq_conj L hkL, pow_one]
  change c.alpha * c.beta ^ j = _
  rw [← hx]
  congr 2
  exact hk'x.symm


theorem exists_pow_mul_eq_of_normalizes {S T : Type*} [Group S] [Group T] (c : T →* MulAut S)
    (Φ : MulAut S) (hΦ : ∀ t : T, ∃ t' : T, Φ * c t * Φ⁻¹ = c t') (t : T) (j : ℕ) :
    ∃ t' : T, (c t * Φ) ^ j = c t' * Φ ^ j := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨v, hv⟩ := hΦ u
    refine ⟨t * v, ?_⟩
    rw [pow_succ', hu, map_mul, pow_succ']
    calc c t * Φ * (c u * Φ ^ j) = c t * (Φ * c u * Φ⁻¹) * (Φ * Φ ^ j) := by group
      _ = c t * c v * (Φ * Φ ^ j) := by rw [hv]

theorem exists_conj_mul_inv_eq_of_normalizes {S T : Type*} [Group S] [Group T] (c : T →* MulAut S)
    (Φ : MulAut S) (hΦ : ∀ t : T, ∃ t' : T, Φ * c t * Φ⁻¹ = c t') (t : T) :
    ∃ t' : T, c t * Φ * (c t)⁻¹ = c t' * Φ := by
  obtain ⟨v, hv⟩ := hΦ t⁻¹
  refine ⟨t * v, ?_⟩
  rw [map_mul, ← hv, map_inv]
  group

theorem exists_mul_pow_mem_range_of_normalizes {S Γ T : Type*} [Group S] [Group Γ] [Group T]
    (c : T →* MulAut S) (Φ : Γ →* MulAut S)
    (hΦ : ∀ (σ : Γ) (t : T), ∃ t' : T, Φ σ * c t * (Φ σ)⁻¹ = c t')
    {σ₁ σ₂ : Γ} (hσ : σ₂ = σ₁ ∨ σ₂ = σ₁⁻¹) (h3 : σ₁ ^ 3 = 1) (t₁ t₂ : T) :
    ∃ j : ℕ, c t₁ * Φ σ₁ * (c t₂ * Φ σ₂) ^ j ∈ c.range := by
  rcases hσ with h | h
  · subst h
    obtain ⟨u, hu⟩ := exists_pow_mul_eq_of_normalizes c (Φ σ₂) (hΦ σ₂) t₂ 2
    obtain ⟨v, hv⟩ := hΦ σ₂ u
    have h3' : (Φ σ₂) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    refine ⟨2, t₁ * v, ?_⟩
    rw [hu, map_mul]
    calc c t₁ * c v = c t₁ * (Φ σ₂ * c u * (Φ σ₂)⁻¹) := by rw [hv]
      _ = c t₁ * Φ σ₂ * (c u * Φ σ₂ ^ 2) * (Φ σ₂ ^ 3)⁻¹ := by group
      _ = c t₁ * Φ σ₂ * (c u * Φ σ₂ ^ 2) := by rw [h3', inv_one, mul_one]
  · subst h
    obtain ⟨v, hv⟩ := hΦ σ₁ t₂
    refine ⟨1, t₁ * v, ?_⟩
    rw [pow_one, map_inv, map_mul]
    calc c t₁ * c v = c t₁ * (Φ σ₁ * c t₂ * (Φ σ₁)⁻¹) := by rw [hv]
      _ = c t₁ * Φ σ₁ * (c t₂ * (Φ σ₁)⁻¹) := by group

theorem center_eq_bot_of_isQuasisimple_of_isSimpleGroup {X : Type*} [Group X]
    [IsSimpleGroup X] (hq : IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    haveI : Group.IsPerfect X := hq.1
    have hcomm : ∀ x y : X, x * y = y * x := fun x y => by
      have hx : x ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
    exact Group.IsPerfect.not_isSolvable X (Group.isSolvable_of_comm hcomm)


theorem pow_pow_card_three {K : Type} [Field K] [Finite K] {p m : ℕ} (hK : Nat.card K = p ^ (3 * m))
    (x : K) : (x ^ p ^ (2 * m)) ^ p ^ m = x := by
  have : Fintype K := Fintype.ofFinite K
  rw [← pow_mul, ← pow_add, show 2 * m + m = 3 * m by ring, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem ringAut_order_three_rel {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {σ₁ σ₂ : K ≃+* K} (h₁ : orderOf σ₁ = 3)
    (h₂ : orderOf σ₂ = 3) : σ₂ = σ₁ ∨ σ₂ = σ₁⁻¹ := by
  obtain ⟨⟨m, rfl⟩, hσ₁⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hf hK h₁
  obtain ⟨-, hσ₂⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hf hK h₂
  have e1 : 3 * m / 3 = m := by omega
  have e2 : 2 * (3 * m) / 3 = 2 * m := by omega
  rw [e1, e2] at hσ₁ hσ₂
  rcases hσ₁ with h | h <;> rcases hσ₂ with h' | h'
  · exact Or.inl (RingEquiv.ext fun x => (h' x).trans (h x).symm)
  · refine Or.inr (eq_inv_of_mul_eq_one_right (RingEquiv.ext fun x => ?_))
    change σ₁ (σ₂ x) = x
    rw [h', h, pow_pow_card_three hK]
  · refine Or.inr (eq_inv_of_mul_eq_one_left (RingEquiv.ext fun x => ?_))
    change σ₂ (σ₁ x) = x
    rw [h', h, pow_pow_card_three hK]
  · exact Or.inl (RingEquiv.ext fun x => (h' x).trans (h x).symm)



theorem conj_injective_of_center_eq_bot {X : Type*} [Group X]
    (h : Subgroup.center X = ⊥) : Function.Injective (MulAut.conj : X →* MulAut X) :=
  (MonoidHom.ker_eq_bot_iff _).mp ((ker_conj_eq_center X).trans h)

theorem imageModTheta_le_barCentralizer_of_le {L K : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1) (hKL : K ≤ L)
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G)) :
    Sec8.imageModTheta L K ≤ Sec8.barCentralizer (Subgroup.zpowers b) L := by
  rw [← KFacts.imageModTheta_centralizer_eq hbN ⟨1, by rw [pow_one]; exact hb3⟩]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hKL (Subgroup.mem_subgroupOf.mp hk),
    hKb (Subgroup.mem_subgroupOf.mp hk)⟩), rfl⟩

theorem Cfg.card_rhoK_range_dvd {L K : Subgroup G} {a b : G} (c : Cfg L K a b)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) :
    Nat.card (rhoK c.hKL).range ∣ Nat.card (Sec8.barCentralizer (Subgroup.zpowers b) L) := by
  have hcomp : rhoK c.hKL = (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).comp (Sec8.Item87Res2Proof.toQuot c.hKL) :=
    MonoidHom.ext fun k => rho_eq_conj L (c.hKL k.2)
  have hrange : (rhoK c.hKL).range = (Sec8.imageModTheta L K).map MulAut.conj := by
    rw [hcomp, MonoidHom.range_comp, Sec8.Item87Res2Proof.range_toQuot]
  rw [hrange, Subgroup.card_map_of_injective (conj_injective_of_center_eq_bot hZ)]
  exact Subgroup.card_dvd_of_le
    (imageModTheta_le_barCentralizer_of_le c.hbL c.hb3 c.hKL c.hKb)

omit [Finite G] in
theorem imageModTheta_ne_bot [Finite G] {L K : Subgroup G} (hKL : K ≤ L)
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K)) :
    Sec8.imageModTheta L K ≠ ⊥ := by
  intro h
  have hr : (Sec8.Item87Res2Proof.toQuot hKL).range = ⊥ :=
    (Sec8.Item87Res2Proof.range_toQuot hKL).trans h
  have htop : aschbacherSolvableCore 3 K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    apply Sec8.Item87Res2Proof.ker_toQuot_le hKL
    rw [MonoidHom.mem_ker]
    have : Sec8.Item87Res2Proof.toQuot hKL k ∈ (Sec8.Item87Res2Proof.toQuot hKL).range :=
      ⟨k, rfl⟩
    rw [hr, Subgroup.mem_bot] at this
    exact this
  haveI : Subsingleton (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨x, y, hxy⟩ := hq.2.2
  exact hxy (Subsingleton.elim _ _)

theorem barCentralizer_le_imageModTheta_of_simple {L K : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    (hsimple : IsSimpleGroup ↥(Sec8.barCentralizer (Subgroup.zpowers b) L))
    (hne : Sec8.imageModTheta L K ≠ ⊥) :
    Sec8.barCentralizer (Subgroup.zpowers b) L ≤ Sec8.imageModTheta L K := by
  set M : Subgroup G := L ⊓ Subgroup.centralizer {b} with hM
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set g : ↥M →* L ⧸ aschbacherSolvableCore 3 L := q.comp (Subgroup.inclusion inf_le_left) with hg
  have hrange : g.range = Sec8.barCentralizer (Subgroup.zpowers b) L := by
    rw [← KFacts.imageModTheta_centralizer_eq hbN ⟨1, by rw [pow_one]; exact hb3⟩,
      Sec8.imageModTheta, hg, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hsimple' : IsSimpleGroup ↥g.range := by
    rw [hrange]
    exact hsimple
  obtain ⟨hKM, hKp⟩ := mem_thetaComponentsIn_iff.mp hK
  have hsub : (K.subgroupOf M).IsSubnormal := hKp.2.1
  have hmap : ((K.subgroupOf M).map g.rangeRestrict).IsSubnormal :=
    hsub.map g.rangeRestrict_surjective
  have himg : ((K.subgroupOf M).map g.rangeRestrict).map g.range.subtype =
      Sec8.imageModTheta L K := by
    rw [Subgroup.map_map, Sec8.imageModTheta]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hKM hx⟩, hx, rfl⟩
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple' hmap with h | h
  · exfalso
    apply hne
    rw [← himg, h, Subgroup.map_bot]
  · rw [← hrange, ← himg, h, Subgroup.map_top, Subgroup.range_subtype]

end Core

end CFSG.RankThree.PartTwo.Sec8.Hering418
