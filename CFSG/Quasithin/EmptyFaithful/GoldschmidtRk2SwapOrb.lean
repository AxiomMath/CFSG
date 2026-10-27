module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclG
public import CFSG.Quasithin.EmptyFaithful.S151ZB

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Orb

variable {G : Type} [Group G] [Finite G] {Y : Type} [Group Y] [Finite Y]
  {L SL : Subgroup G} {ρ : ↥L →* Y} {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

theorem sl_le_parUp (h : RkData L SL ρ U P) (j : Fin 2) : SL ≤ parUp L ρ (P j) := by
  intro x hx
  have hxL : x ∈ L := h.sylow.1 hx
  refine mem_up.2 ⟨hxL, ?_⟩
  have h1 : ρ ⟨x, hxL⟩ ∈ U := by
    rw [← h.hU]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  exact h.pkg.res.2.1 j h1

theorem parUp_ne_top (h : RkData L SL ρ U P) (j : Fin 2) : parUp L ρ (P j) ≠ L := by
  intro heq
  have h1 : (P j).comap ρ = ⊤ := up_injective (heq.trans up_top.symm)
  apply h.pkg.ne_top j
  rw [← Subgroup.map_comap_eq_self_of_surjective h.surj (P j), h1,
    Subgroup.map_top_of_surjective _ h.surj]

theorem parUp_zero_ne_one (h : RkData L SL ρ U P) : parUp L ρ (P 0) ≠ parUp L ρ (P 1) := by
  intro heq
  have h1 : (P 0).comap ρ = (P 1).comap ρ := up_injective heq
  apply h.pkg.res.1
  rw [← Subgroup.map_comap_eq_self_of_surjective h.surj (P 0), h1,
    Subgroup.map_comap_eq_self_of_surjective h.surj (P 1)]

theorem parUp_coatom (h : RkData L SL ρ U P) (j : Fin 2) {Q : Subgroup G} (hQL : Q ≤ L)
    (hPQ : parUp L ρ (P j) ≤ Q) : Q = parUp L ρ (P j) ∨ Q = L := by
  set X : Subgroup ↥L := Q.subgroupOf L with hX
  have hQX : Q = up L X := (Subgroup.map_subgroupOf_eq_of_le hQL).symm
  have hcomap : (P j).comap ρ ≤ X := by
    have : up L ((P j).comap ρ) ≤ up L X := by
      rw [← hQX]
      exact hPQ
    exact up_le_up_iff.1 this
  have hkerX : ρ.ker ≤ X := (Subgroup.ker_le_comap ρ (P j)).trans hcomap
  have hmapX : P j ≤ X.map ρ := by
    rw [← Subgroup.map_comap_eq_self_of_surjective h.surj (P j)]
    exact Subgroup.map_mono hcomap
  have hcov := h.pkg.covBy j
  by_cases hlt : P j < X.map ρ
  · have htop : X.map ρ = ⊤ := by
      by_contra hnt
      exact hcov.2 hlt (lt_top_iff_ne_top.2 hnt)
    have hXtop : X = ⊤ := by
      rw [← Subgroup.comap_map_eq_self hkerX, htop, Subgroup.comap_top]
    right
    rw [hQX, hXtop, up_top]
  · have heq : X.map ρ = P j := ((hmapX.lt_or_eq).resolve_left hlt).symm
    have hXe : X = (P j).comap ρ := by
      rw [← Subgroup.comap_map_eq_self hkerX, heq]
    left
    rw [hQX, hXe]
    rfl

theorem exists_le_parUp (h : RkData L SL ρ U P)
    (hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ CFSG.Open.pCore 2 ↥L = ⊤)
    (hQ : pCoreOf 2 L ≤ SL) {N : Subgroup G} (hNL : N ≤ L) (hSN : SL ≤ N) (hne : N ≠ L) :
    ∃ j, N ≤ parUp L ρ (P j) := by
  set X : Subgroup ↥L := N.subgroupOf L with hX
  have hNX : N = up L X := (Subgroup.map_subgroupOf_eq_of_le hNL).symm
  have hUX : U ≤ X.map ρ := by
    rw [← h.hU]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.2 (hSN (Subgroup.mem_subgroupOf.1 hx))
  have hQX : CFSG.Open.pCore 2 ↥L ≤ X := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSN (hQ ⟨x, hx, rfl⟩))
  have hρX : X.map ρ ≠ ⊤ := by
    intro htop
    apply hne
    have hdec : ∀ l : ↥L, ∃ k ∈ ρ.ker, ∃ n ∈ X, l = k * n := by
      intro l
      have hl : ρ l ∈ X.map ρ := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnl⟩ := hl
      refine ⟨l * n⁻¹, ?_, n, hn, by simp⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hnl, mul_inv_cancel]
    have hkconj : ∀ k ∈ ρ.ker, ∀ n ∈ X, k * n * k⁻¹ ∈ X := by
      intro k hk n hn
      have e : k * n * k⁻¹ = ⁅k, n⁆ * n := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact X.mul_mem (hQX (h.cent k hk n)) hn
    have hnorm : X.Normal := by
      refine ⟨fun n hn l => ?_⟩
      obtain ⟨k, hk, m, hm, rfl⟩ := hdec l
      have e : k * m * n * (k * m)⁻¹ = k * (m * n * m⁻¹) * k⁻¹ := by group
      rw [e]
      exact hkconj k hk _ (X.mul_mem (X.mul_mem hm hn) (X.inv_mem hm))
    have hm1 : ∀ x ∈ X, QuotientGroup.mk' X x = 1 := fun x hx =>
      (QuotientGroup.eq_one_iff x).2 hx
    have hcomm : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ X := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨k₁, hk₁, n₁, hn₁, rfl⟩ := hdec a
      obtain ⟨k₂, hk₂, n₂, hn₂, rfl⟩ := hdec b
      have ha : QuotientGroup.mk' X (k₁ * n₁) = QuotientGroup.mk' X k₁ := by
        rw [map_mul, hm1 n₁ hn₁, mul_one]
      have hb : QuotientGroup.mk' X (k₂ * n₂) = QuotientGroup.mk' X k₂ := by
        rw [map_mul, hm1 n₂ hn₂, mul_one]
      have h1 : QuotientGroup.mk' X ⁅k₁ * n₁, k₂ * n₂⁆ = 1 := by
        rw [map_commutatorElement, ha, hb, ← map_commutatorElement]
        exact hm1 _ (hQX (h.cent k₁ hk₁ k₂))
      exact (QuotientGroup.eq_one_iff _).1 h1
    have htopX : (⊤ : Subgroup ↥L) ≤ X := by
      rw [← hperf]
      exact sup_le hcomm hQX
    rw [hNX, eq_top_iff.2 htopX, up_top]
  rcases eq_top_or_exists_le_coatom (X.map ρ) with h1 | ⟨b, hb, hXb⟩
  · exact absurd h1 hρX
  · obtain ⟨j, rfl⟩ := (h.pkg.res.2.2.1 b (hUX.trans hXb)).1 (covBy_top_iff.2 hb)
    refine ⟨j, ?_⟩
    rw [hNX]
    exact up_mono (Subgroup.map_le_iff_le_comap.1 hXb)

theorem conj_parUp (h : RkData L SL ρ U P)
    (hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ CFSG.Open.pCore 2 ↥L = ⊤)
    (hQ : pCoreOf 2 L ≤ SL) {s : G} (hsL : s ∈ Subgroup.normalizer (L : Set G))
    (hsSL : s ∈ Subgroup.normalizer (SL : Set G)) (j : Fin 2) :
    ∃ k, B6.conjSub s (parUp L ρ (P j)) = parUp L ρ (P k) := by
  have hSLs : B6.conjSub s SL = SL := B6.conjSub_eq_self hsSL
  have hmax : IsMaxSubgroupIn L (parUp L ρ (P j)) := by
    refine ⟨lt_of_le_of_ne (parUp_le _) (parUp_ne_top h j), fun K hK hKL => ?_⟩
    rcases parUp_coatom h j hKL hK.le with h1 | h1
    · exact absurd h1 (ne_of_gt hK)
    · exact h1
  have hC := zb_isMax_conj hsL hmax
  have hSC : SL ≤ B6.conjSub s (parUp L ρ (P j)) := by
    rw [← hSLs]
    exact (B6.conjSub s).monotone (sl_le_parUp h j)
  obtain ⟨k, hk⟩ := exists_le_parUp h hperf hQ hC.1.le hSC hC.1.ne
  refine ⟨k, ?_⟩
  by_contra hne
  exact parUp_ne_top h k (hC.2 _ (lt_of_le_of_ne hk hne) (parUp_le _))

theorem mem_normalizer_of_conjSub_eq {s : G} {X : Subgroup G} (h : B6.conjSub s X = X) :
    s ∈ Subgroup.normalizer (X : Set G) := by
  refine B6.mem_normalizer_of_conjSub_le h.le ?_
  have : B6.conjSub s⁻¹ X = X := by
    calc B6.conjSub s⁻¹ X = B6.conjSub s⁻¹ (B6.conjSub s X) := by rw [h]
      _ = B6.conjSub (s⁻¹ * s) X := (B6.conjSub_mul _ _ _).symm
      _ = X := by rw [inv_mul_cancel, B6.conjSub_one]
  exact this.le

theorem swap_or_fix (h : RkData L SL ρ U P)
    (hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ CFSG.Open.pCore 2 ↥L = ⊤)
    (hQ : pCoreOf 2 L ≤ SL) {s : G} (hsL : s ∈ Subgroup.normalizer (L : Set G))
    (hsSL : s ∈ Subgroup.normalizer (SL : Set G)) :
    (B6.conjSub s (parUp L ρ (P 0)) = parUp L ρ (P 0) ∧
        B6.conjSub s (parUp L ρ (P 1)) = parUp L ρ (P 1)) ∨
      (B6.conjSub s (parUp L ρ (P 0)) = parUp L ρ (P 1) ∧
        B6.conjSub s (parUp L ρ (P 1)) = parUp L ρ (P 0)) := by
  obtain ⟨k₀, h₀⟩ := conj_parUp h hperf hQ hsL hsSL 0
  obtain ⟨k₁, h₁⟩ := conj_parUp h hperf hQ hsL hsSL 1
  have hne : k₀ ≠ k₁ := by
    intro hk
    subst hk
    exact parUp_zero_ne_one h ((B6.conjSub s).injective (h₀.trans h₁.symm))
  have hfin : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases hfin k₀ with rfl | rfl <;> rcases hfin k₁ with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact absurd rfl hne

end Orb

end CFSG.Quasithin.Rk2
