module

import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem exists_eq_zpowers_of_card_eq_prime {p : ℕ} (hp : p.Prime) {S : Subgroup G}
    (hS : Nat.card S = p) : ∃ v ∈ S, v ≠ 1 ∧ S = Subgroup.zpowers v := by
  obtain ⟨v, hvS, hv1⟩ : ∃ v ∈ S, v ≠ 1 := by
    by_contra! h
    have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr h
    rw [hbot, Subgroup.card_bot] at hS
    exact hp.one_lt.ne hS
  refine ⟨v, hvS, hv1, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvS) ?_).symm⟩
  rw [hS, Nat.card_zpowers]
  have hdvd : orderOf v ∣ p := hS ▸ Subgroup.orderOf_dvd_natCard S hvS
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hv1
  · exact h.ge

theorem le_of_forall_inf_centralizer_sub_le {p k : ℕ} (hp : p.Prime) {V X M : Subgroup G}
    (hV : CFSG.Assembly.IsElemAbelian p V) (hVk : p ^ (k + 1) ≤ Nat.card V)
    (hVX : V ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X))
    (h : ∀ H : Subgroup G, H ≤ V → Nat.card H = p ^ k →
      X ⊓ Subgroup.centralizer (H : Set G) ≤ M) : X ≤ M := by
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p k hp V X hV hVk
    hVX hX]
  exact iSup₂_le fun H hH => h H hH.1 hH.2

theorem le_of_forall_inf_centralizer_le {p : ℕ} (hp : p.Prime) {V X M : Subgroup G}
    (hV : CFSG.Assembly.IsElemAbelian p V) (hV2 : p ^ 2 ≤ Nat.card V)
    (hVX : V ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X))
    (h : ∀ v ∈ V, v ≠ 1 → X ⊓ Subgroup.centralizer ({v} : Set G) ≤ M) : X ≤ M := by
  refine le_of_forall_inf_centralizer_sub_le (k := 1) hp hV hV2 hVX hX fun H hHV hH => ?_
  obtain ⟨v, hvH, hv1, rfl⟩ := exists_eq_zpowers_of_card_eq_prime hp (by rw [hH, pow_one])
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact h v (hHV (Subgroup.mem_zpowers v)) hv1

theorem card_le_of_le_normalizer (he : CFSG.Assembly.evenRank G = 3) {T E : Subgroup G}
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) : Nat.card E ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hk3 : k ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (T : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨E, hET, hE, hk⟩
  have hloc := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) (Subgroup.normalizer (T : Set G)) ⟨T, hT, hT2, rfl⟩
  have hk' : k ≤ 3 := hk3.trans (hloc.trans he.le)
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk'
    _ = 27 := by norm_num

theorem card_le_of_le_centralizer_involution (he : CFSG.Assembly.evenRank G = 3) {t : G}
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set G)) : Nat.card E ≤ 27 := by
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht
  refine card_le_of_le_normalizer he (T := Subgroup.zpowers t) ?_
    (IsPGroup.of_card (G := Subgroup.zpowers t) (n := 1)
      (by rw [Nat.card_zpowers, hord, pow_one])) hE ?_
  · intro h
    exact ht (by simpa [h] using Subgroup.mem_zpowers t)
  · refine hEt.trans ?_
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)

theorem exists_elemAbelian_le_of_le_pRank {p : ℕ} (hp : p.Prime) {X : Subgroup G} {k : ℕ}
    (hk : k ≤ CFSG.Assembly.pRank p X) :
    ∃ E : Subgroup G, E ≤ X ∧ CFSG.Assembly.IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, hE₀X, hE₀, hcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained p hp X
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p (n := k)
    (by rw [hcard]; exact pow_dvd_pow p hk)
  refine ⟨K.map E₀.subtype, (Subgroup.map_subtype_le K).trans hE₀X, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨x, -, rfl⟩⟩ ⟨_, ⟨y, -, rfl⟩⟩
    apply Subtype.ext
    change (x : G) * y = y * x
    exact congrArg Subtype.val (hE₀.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hE₀.2 x x.2
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]

theorem le_pRank_of_elemAbelian {p : ℕ} (hp : p.Prime) {X E : Subgroup G} {k : ℕ} (hEX : E ≤ X)
    (hE : CFSG.Assembly.IsElemAbelian p E) (hcard : Nat.card E = p ^ k) :
    k ≤ CFSG.Assembly.pRank p X := CFSG.SectionRank.le_pRank hp.one_lt hEX hE hcard

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian p F)
    (hEF : E ≤ F) : CFSG.Assembly.IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF hEF

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
theorem sup_inf_centralizer_le {P B : Subgroup G}
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hB : B ≤ Subgroup.centralizer (B : Set G)) :
    (P ⊔ B) ⊓ Subgroup.centralizer (B : Set G) ≤ (P ⊓ Subgroup.centralizer (B : Set G)) ⊔ B := by
  rintro x ⟨hx, hxB⟩
  have hx' : x ∈ (P : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P B hBP]
    exact hx
  obtain ⟨y, hy, b, hb, rfl⟩ := hx'
  have hyB : y ∈ Subgroup.centralizer (B : Set G) := by
    have : y = (y * b) * b⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hxB (Subgroup.inv_mem _ (hB hb))
  exact Subgroup.mul_mem_sup ⟨hy, hyB⟩ hb

theorem isElemAbelian_sup_zpowers {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) {y : G} (hy : y ∉ A) (hyp : y ^ p = 1)
    (hyA : ∀ a ∈ A, a * y = y * a) :
    CFSG.Assembly.IsElemAbelian p (A ⊔ Subgroup.zpowers y) ∧
      Nat.card (A ⊔ Subgroup.zpowers y : Subgroup G) = Nat.card A * p := by
  obtain ⟨hcomm, hcard⟩ := sup_zpowers_card hA.1 hy hyp hyA
  refine ⟨⟨hcomm, fun x hx => ?_⟩, hcard⟩
  have hle : A ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hyA a ha).symm
  have hx' : x ∈ ((A : Set G) * (Subgroup.zpowers y : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A _ hle]
    exact hx
  obtain ⟨a, ha, z, hz, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hcommaz : Commute a (y ^ k) := Commute.zpow_right (hyA a ha) k
  rw [hcommaz.mul_pow, hA.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hyp, one_zpow]

end CFSG.RankThree.PartTwo.Sec5
