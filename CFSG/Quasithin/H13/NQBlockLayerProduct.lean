module

public import CFSG.Quasithin.H13.NQBlockPRankProduct
public import CFSG.Quasithin.H13.NQBlockSourceRank

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

theorem commute_mk_iff {X : Type*} [Group X] {N : Subgroup X} [N.Normal] (x z : X) :
    Commute (x : X ⧸ N) (z : X ⧸ N) ↔ ⁅x, z⁆ ∈ N := by
  have h : ((⁅x, z⁆ : X) : X ⧸ N) = ⁅(x : X ⧸ N), (z : X ⧸ N)⁆ :=
    map_commutatorElement (QuotientGroup.mk' N) x z
  rw [← QuotientGroup.eq_one_iff, h, commutatorElement_eq_one_iff_mul_comm]
  rfl

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coe_commutatorElement {B : Subgroup G} (x z : ↥B) :
    ((⁅x, z⁆ : ↥B) : G) = ⁅(x : G), (z : G)⁆ :=
  map_commutatorElement B.subtype x z

theorem commuting_product_two_core {K Y : Subgroup G} (hKY : K ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) (hc : ⁅K, Y⁆ ≤ pCoreOf 2 K ⊓ pCoreOf 2 Y)
    (hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a) :
    pCoreOf 2 (K ⊔ Y) = pCoreOf 2 K ⊔ pCoreOf 2 Y ∧
      ∃ φ : (↥K ⧸ CFSG.pCore 2 ↥K) × (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
          (↥(K ⊔ Y) ⧸ CFSG.pCore 2 ↥(K ⊔ Y)),
        ∀ (k : ↥K) (y : ↥Y), φ ((k : ↥K ⧸ CFSG.pCore 2 ↥K), (y : ↥Y ⧸ CFSG.pCore 2 ↥Y)) =
          ((⟨k * y, mul_mem (mem_sup_left k.2) (mem_sup_right y.2)⟩ : ↥(K ⊔ Y)) :
            ↥(K ⊔ Y) ⧸ CFSG.pCore 2 ↥(K ⊔ Y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := K ⊔ Y with hBdef
  set O := pCoreOf 2 B with hOdef
  have hKB : K ≤ B := le_sup_left
  have hYB : Y ≤ B := le_sup_right
  have hBO : B ≤ normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
  have hBK : B ≤ normalizer (K : Set G) := sup_le le_normalizer hYK
  have hBY : B ≤ normalizer (Y : Set G) := sup_le hKY le_normalizer
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
  have hQKO : pCoreOf 2 K ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKB)
    (hBK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hQYO : pCoreOf 2 Y ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYB)
    (hBY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hKO : K ⊓ O ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => mem_normalizer_inf (le_normalizer hg) (hBO (hKB hg))) (hO2.to_le inf_le_right)
  have hYO : Y ⊓ O ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => mem_normalizer_inf (le_normalizer hg) (hBO (hYB hg))) (hO2.to_le inf_le_right)
  have hcen : ∀ k ∈ K, (∀ k' ∈ K, ⁅k, k'⁆ ∈ pCoreOf 2 K) → k ∈ pCoreOf 2 K := by
    intro k hk hkc
    have := hsimple
    have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
    have h1 : ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [mem_center_iff]
      intro z
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective z
      refine ((commute_mk_iff _ _).mpr ?_).symm
      rw [mem_pCore_iff_mem_pCoreOf, coe_commutatorElement]
      exact hkc k' k'.2
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    exact h1
  have key : ∀ k ∈ K, ∀ y ∈ Y, k * y ∈ O → k ∈ pCoreOf 2 K ∧ y ∈ pCoreOf 2 Y := by
    intro k hk y hy ho
    have hkQ : k ∈ pCoreOf 2 K := by
      refine hcen k hk fun k' hk' => hKO (mem_inf.mpr ⟨?_, ?_⟩)
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')
      · rw [commutatorElement_def]
        set a := y⁻¹ * k' * y with hadef
        have haK : a ∈ K := (mem_normalizer_iff.mp (hYK (inv_mem hy)) k').mp hk' |> fun h => by
          rw [hadef]
          simpa only [inv_inv] using h
        have e : k * k' * k⁻¹ * k'⁻¹ = ((k * y) * a * (k * y)⁻¹ * a⁻¹) * (a * k'⁻¹) := by
          rw [hadef]
          group
        rw [e]
        refine mul_mem ?_ (hQKO (mem_inf.mp (hc ?_)).1)
        · have e2 : (k * y) * a * (k * y)⁻¹ * a⁻¹ = (k * y) * (a * (k * y)⁻¹ * a⁻¹) := by group
          rw [e2]
          exact mul_mem ho ((mem_normalizer_iff.mp (hBO (hKB haK)) _).mp (inv_mem ho))
        · have e3 : a * k'⁻¹ = ⁅k', y⁻¹⁆⁻¹ := by
            rw [hadef, commutatorElement_def]
            group
          rw [e3]
          exact inv_mem (commutator_mem_commutator hk' (inv_mem hy))
    refine ⟨hkQ, hYO (mem_inf.mpr ⟨hy, ?_⟩)⟩
    have e : y = k⁻¹ * (k * y) := by group
    rw [e]
    exact mul_mem (inv_mem (hQKO hkQ)) ho
  have hBset : (B : Set G) = (K : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K Y hYK
  have hOeq : O = pCoreOf 2 K ⊔ pCoreOf 2 Y := by
    refine le_antisymm (fun o ho => ?_) (sup_le hQKO hQYO)
    have hoB : o ∈ (B : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 B ho
    rw [hBset] at hoB
    obtain ⟨k, hk, y, hy, rfl⟩ := hoB
    obtain ⟨hkQ, hyQ⟩ := key k hk y hy ho
    exact mul_mem (mem_sup_left hkQ) (mem_sup_right hyQ)
  refine ⟨hOeq, ?_⟩
  have hfK : CFSG.pCore 2 ↥K ≤ (CFSG.pCore 2 ↥B).comap (Subgroup.inclusion hKB) := by
    intro k hk
    rw [mem_comap, mem_pCore_iff_mem_pCoreOf]
    exact hQKO ((mem_pCore_iff_mem_pCoreOf k).mp hk)
  have hfY : CFSG.pCore 2 ↥Y ≤ (CFSG.pCore 2 ↥B).comap (Subgroup.inclusion hYB) := by
    intro y hy
    rw [mem_comap, mem_pCore_iff_mem_pCoreOf]
    exact hQYO ((mem_pCore_iff_mem_pCoreOf y).mp hy)
  set f := QuotientGroup.map _ _ (Subgroup.inclusion hKB) hfK with hfdef
  set g := QuotientGroup.map _ _ (Subgroup.inclusion hYB) hfY with hgdef
  have hcomm : ∀ a b, Commute (f a) (g b) := by
    intro a b
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine (commute_mk_iff (Subgroup.inclusion hKB k) (Subgroup.inclusion hYB y)).mpr ?_
    rw [mem_pCore_iff_mem_pCoreOf, coe_commutatorElement]
    exact hQKO (mem_inf.mp (hc (commutator_mem_commutator k.2 y.2))).1
  set φ₀ := MonoidHom.noncommCoprod f g hcomm with hφ₀def
  have hφ₀ : ∀ (k : ↥K) (y : ↥Y), φ₀ ((k : ↥K ⧸ CFSG.pCore 2 ↥K), (y : ↥Y ⧸ CFSG.pCore 2 ↥Y)) =
      ((⟨k * y, mul_mem (mem_sup_left k.2) (mem_sup_right y.2)⟩ : ↥B) :
        ↥B ⧸ CFSG.pCore 2 ↥B) := fun _ _ => rfl
  have hsurj : Function.Surjective φ₀ := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    have hb : (b : G) ∈ (B : Set G) := b.2
    rw [hBset] at hb
    obtain ⟨k, hk, y, hy, hky⟩ := hb
    refine ⟨(((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K),
      ((⟨y, hy⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y)), ?_⟩
    rw [hφ₀]
    congr 1
    exact Subtype.ext hky
  have hinj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hφ₀, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hab
    obtain ⟨hkQ, hyQ⟩ := key k k.2 y y.2 hab
    refine Prod.ext ?_ ?_
    · change ((k : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
      exact hkQ
    · change ((y : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) = 1
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
      exact hyQ
  exact ⟨MulEquiv.ofBijective φ₀ ⟨hinj, hsurj⟩, fun k y => hφ₀ k y⟩

theorem commuting_product_pRank {K Y : Subgroup G} (hKY : K ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) (hc : ⁅K, Y⁆ ≤ pCoreOf 2 K ⊓ pCoreOf 2 Y)
    (hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pRank p (↥K ⧸ CFSG.pCore 2 ↥K) + CFSG.pRank p ↥Y = CFSG.pRank p ↥(K ⊔ Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : ∀ (X : Type) [Group X] [Finite X], ¬ p ∣ Nat.card ↥(CFSG.pCore 2 X) := by
    intro X _ _ hdvd
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    rw [ha] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨-, φ, -⟩ := commuting_product_two_core hKY hYK hc hsimple hnab
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp (CFSG.pCore 2 ↥Y)
      (hcop ↥Y), ← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (CFSG.pCore 2 ↥(K ⊔ Y)) (hcop ↥(K ⊔ Y)), ← pRank_prod_eq hp, pRank_mulEquiv φ p]

end CFSG.Quasithin.H13.NQBlock
