module

public import CFSG.RankThree.PartTwo.Sec18.Item189K0Generic
public import CFSG.RankThree.PartTwo.Sec18.SylowWStar
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

structure K0Setting (G : Type) [Group G] [Finite G] (A B X M : Subgroup G) (c : G) : Prop where
  plane : PlaneQ8 A B X c
  hAM : A ≤ M
  hXM : X ≤ M
  oTwoThree : B ≤ (Sec4.oTwoP 3 M).map M.subtype
  sec4 : SectionFourHyp ↥M
  thm4 : TheoremFourHyp G
  rank : CFSG.Open.pRank 3 M ≤ 3

variable {G : Type} [Group G] [Finite G] {A B X M : Subgroup G} {c : G}

private theorem k0_le_of_plane (hp : PlaneQ8 A B X c) : B ≤ A := by
  rw [hp.eq_sup]
  exact le_sup_right

private theorem k0_card_zpowers_of_plane (hp : PlaneQ8 A B X c) :
    Nat.card (Subgroup.zpowers c) = 3 := by
  have hc3 : c ^ 3 = 1 := hp.isElemAbelian.2 c hp.mem
  have hc1 : c ≠ 1 := by
    intro hc
    exact hp.not_mem (by rw [hc]; exact B.one_mem)
  rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]

private theorem k0_exists_mem_of_plane (hp : PlaneQ8 A B X c) :
    ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1 := by
  have hne : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hB : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    have h9 := hp.card_plane
    rw [hB, Subgroup.card_bot] at h9
    norm_num at h9
  obtain ⟨b, hbB, hb1⟩ := hne
  exact ⟨b, hbB, hb1,
    (CFSG.Open.IsElemAbelian.mono hp.isElemAbelian (k0_le_of_plane hp)).2 b hbB⟩

private theorem k0_conj_eq_of_mem_zpowers {x b g : G} (hxb : x * b = b * x)
    (hg : g ∈ Subgroup.zpowers b) : x * g * x⁻¹ = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h1 : x * b * x⁻¹ = b := by rw [hxb, mul_inv_cancel_right]
  rw [← conj_zpow, h1]

private theorem k0_le_normalizer_of_conj_mem {S V : Subgroup G}
    (hS : ∀ x ∈ S, ∀ v ∈ V, x * v * x⁻¹ ∈ V) : S ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hS x hx g hg, fun hg => ?_⟩
  have h1 := hS x⁻¹ (S.inv_mem hx) (x * g * x⁻¹) hg
  have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
  rw [e] at h1
  exact h1

private theorem k0_pRank_three_top_quotient_theta (Y : Type) [Group Y] [Finite Y] :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨-, -, hndvd, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  have hk : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd
  exact (CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) (QuotientGroup.mk'_surjective _) hk).symm

theorem K0Setting.eq_bot_or_eq (h : K0Setting G A B X M c) {U : Subgroup G} (hUB : U ≤ B)
    (hUX : X ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ ∨ U = B := by
  have hinv : ∀ φ ∈ Sec4.autIn X B, (U.subgroupOf B).map φ.toMonoidHom = U.subgroupOf B := by
    intro φ hφ
    obtain ⟨k, hkN, hkX, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    have hkU := hUX hkX
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨⟨y, hy⟩, hyU, hyx⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hyU
      rw [Subgroup.mem_subgroupOf]
      have hkyx : k * y * k⁻¹ = x := congrArg Subtype.val hyx
      show x ∈ U
      rw [← hkyx]
      exact (Subgroup.mem_normalizer_iff.mp hkU y).mp hyU
    · intro hxU
      rw [Subgroup.mem_subgroupOf] at hxU
      have hxB : k⁻¹ * x * k⁻¹⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) x).mp hx
      refine ⟨⟨k⁻¹ * x * k⁻¹⁻¹, hxB⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkU) x).mp hxU
      · apply Subtype.ext
        show k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ = x
        group
  rcases h.plane.irreducible _ hinv with h1 | h1
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h1
    exact (disjoint_iff.mp h1 ▸ (inf_eq_left.mpr hUB)).symm
  · right
    rw [Subgroup.subgroupOf_eq_top] at h1
    exact le_antisymm hUB h1

theorem K0Setting.inf_centralizer_eq_bot (h : K0Setting G A B X M c) :
    B ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  have hfix : ∀ x ∈ X, ∀ g ∈ B ⊓ Subgroup.centralizer (X : Set G),
      x * g * x⁻¹ ∈ B ⊓ Subgroup.centralizer (X : Set G) := by
    rintro x hx g ⟨hgB, hgC⟩
    have hxg : x * g * x⁻¹ = g := by
      have hc : x * g = g * x := Subgroup.mem_centralizer_iff.mp hgC x hx
      rw [hc, mul_inv_cancel_right]
    rw [hxg]
    exact ⟨hgB, hgC⟩
  rcases h.eq_bot_or_eq (U := B ⊓ Subgroup.centralizer (X : Set G)) inf_le_left
      (k0_le_normalizer_of_conj_mem hfix) with h1 | h1
  · exact h1
  · exfalso
    have hBC : B ≤ Subgroup.centralizer (X : Set G) := by
      intro b hb
      have hb' : b ∈ B ⊓ Subgroup.centralizer (X : Set G) := by
        rw [h1]
        exact hb
      exact hb'.2
    obtain ⟨b, hbB, hb1, hb3⟩ := k0_exists_mem_of_plane h.plane
    have hbX : ∀ x ∈ X, x * b = b * x := fun x hx =>
      Subgroup.mem_centralizer_iff.mp (hBC hbB) x hx
    have hVX : X ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
      k0_le_normalizer_of_conj_mem fun x hx g hg => by
        rw [k0_conj_eq_of_mem_zpowers (hbX x hx) hg]
        exact hg
    have hVB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
    rcases h.eq_bot_or_eq hVB hVX with h2 | h2
    · apply hb1
      have hmem : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
      rw [h2] at hmem
      exact Subgroup.mem_bot.mp hmem
    · have h3 : Nat.card (Subgroup.zpowers b) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
      rw [h2, h.plane.card_plane] at h3
      norm_num at h3

theorem K0Setting.zpowers_eq_of_card_three (h : K0Setting G A B X M c) {D : Subgroup G}
    (hDA : D ≤ A) (hD3 : Nat.card D = 3) (hDB : D ⊓ B = ⊥)
    (hDX : X ≤ Subgroup.normalizer (D : Set G)) : D = Subgroup.zpowers c := by
  have hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    h.plane.isElemAbelian.comm ha ha'
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr h.plane.mem
  have hBA : B ≤ A := k0_le_of_plane h.plane
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) :=
    k0_le_normalizer_of_conj_mem fun x hx v hv => by
      have hxA : x ∈ A := hcA hx
      have hvA : v ∈ A := hBA hv
      rw [hcomm x hxA v hvA, mul_inv_cancel_right]
      exact hv
  have hDle : D ≤ Subgroup.zpowers c := by
    intro d hd
    have hdA : d ∈ Subgroup.zpowers c ⊔ B := by
      rw [← h.plane.eq_sup]
      exact hDA hd
    have hmem : d ∈ (↑(Subgroup.zpowers c ⊔ B) : Set G) := hdA
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hmem
    obtain ⟨y, hy, z, hz, rfl⟩ := hmem
    have hyA : y ∈ A := hcA hy
    have hzA : z ∈ A := hBA hz
    have hzC : ∀ x ∈ X, x * z * x⁻¹ = z := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (D : Set G) := hDX hx
      have hxy : x * y * x⁻¹ = y := k0_conj_eq_of_mem_zpowers (h.plane.commute x hx) hy
      have hgB : x * z * x⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (h.plane.le_normalizer_plane hx) z).mp hz
      have hgA : x * z * x⁻¹ ∈ A := hBA hgB
      have hyg : y * (x * z * x⁻¹) = (x * z * x⁻¹) * y := hcomm y hyA _ hgA
      have hyz : y * z⁻¹ = z⁻¹ * y := hcomm y hyA z⁻¹ (A.inv_mem hzA)
      have key : (x * (y * z) * x⁻¹) * (y * z)⁻¹ = (x * z * x⁻¹) * z⁻¹ := by
        calc (x * (y * z) * x⁻¹) * (y * z)⁻¹
            = (x * y * x⁻¹) * (x * z * x⁻¹) * (z⁻¹ * y⁻¹) := by group
          _ = y * (x * z * x⁻¹) * (z⁻¹ * y⁻¹) := by rw [hxy]
          _ = (x * z * x⁻¹) * (y * z⁻¹) * y⁻¹ := by rw [hyg]; group
          _ = (x * z * x⁻¹) * (z⁻¹ * y) * y⁻¹ := by rw [hyz]
          _ = (x * z * x⁻¹) * z⁻¹ := by group
      have hdD : y * z ∈ D := hd
      have hmemD : (x * (y * z) * x⁻¹) * (y * z)⁻¹ ∈ D :=
        D.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN (y * z)).mp hdD) (D.inv_mem hdD)
      have hmemB : (x * z * x⁻¹) * z⁻¹ ∈ B := B.mul_mem hgB (B.inv_mem hz)
      rw [key] at hmemD
      have hmemI : (x * z * x⁻¹) * z⁻¹ ∈ D ⊓ B := ⟨hmemD, hmemB⟩
      rw [hDB, Subgroup.mem_bot, mul_inv_eq_one] at hmemI
      exact hmemI
    have hz1 : z = 1 := by
      have hzC' : z ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        calc x * z = x * z * x⁻¹ * x := by group
          _ = z * x := by rw [hzC x hx]
      have hzI : z ∈ B ⊓ Subgroup.centralizer (X : Set G) := ⟨hz, hzC'⟩
      rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at hzI
      exact hzI
    rw [hz1]
    show y * 1 ∈ Subgroup.zpowers c
    rw [mul_one]
    exact hy
  exact Subgroup.eq_of_le_of_card_ge hDle (le_of_eq (by rw [k0_card_zpowers_of_plane h.plane, hD3]))

theorem K0Setting.le_A (h : K0Setting G A B X M c) : B ≤ A := k0_le_of_plane h.plane

theorem K0Setting.isElemAbelian_A (h : K0Setting G A B X M c) : CFSG.Open.IsElemAbelian 3 A :=
  h.plane.isElemAbelian

theorem K0Setting.isElemAbelian_B (h : K0Setting G A B X M c) : CFSG.Open.IsElemAbelian 3 B :=
  CFSG.Open.IsElemAbelian.mono h.isElemAbelian_A h.le_A

theorem K0Setting.exists_mem_B (h : K0Setting G A B X M c) : ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1 :=
  k0_exists_mem_of_plane h.plane

theorem K0Setting.card_le_of_isElemAbelian (h : K0Setting G A B X M c) {E : Subgroup G}
    (hEM : E ≤ M) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hE.isPGroup
  have hkM : k ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEM hE hk
  have hk3 : k ≤ 3 := hkM.trans h.rank
  calc Nat.card E = 3 ^ k := hk
    _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

theorem K0Setting.card_le_of_isElemAbelian_quot (h : K0Setting G A B X M c)
    {E : Subgroup (↥M ⧸ aschbacherSolvableCore 3 ↥M)} (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  have hQ : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ aschbacherSolvableCore 3 ↥M)) ≤ 3 := by
    rw [k0_pRank_three_top_quotient_theta ↥M,
      ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) M]
    exact h.rank
  have h27 := CFSG.RankThree.PartTwo.Sec18.card_le_of_isElemAbelian hQ hE
  calc Nat.card E ≤ 3 ^ 3 := h27
    _ = 27 := by norm_num

end CFSG.RankThree.PartTwo.Sec18
