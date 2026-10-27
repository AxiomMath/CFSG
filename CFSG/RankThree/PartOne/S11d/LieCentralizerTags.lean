module

public import CFSG.RankThree.PartOne.S11d.LieFieldTransfer

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

@[expose] def LieCentralizerComponentT (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p n f : ℕ), p.Prime → 5 ≤ p → 1 ≤ f →
    LieModel T t n 2 (p * f) → ∀ x y : T, x ^ p = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 →
      x * y = y * x →
      ∃ D : Subgroup T, CFSG.IsQuasisimple ↥D ∧ D ≤ Subgroup.centralizer ({x} : Set T) ∧
        (D.subgroupOf (Subgroup.centralizer ({x} : Set T))).IsSubnormal

@[expose] def LieCentralizerComponentFixT (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    CFSG.pRank p T = 1 → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x → ∀ y : T, y ^ 2 = 1 → y ≠ 1 → x * y = y * x →
      ∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D

@[expose] def LieGoodComponentFixT (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    CFSG.pRank p T = 1 → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x → ∀ y : T, y ^ 2 = 1 → y ≠ 1 → x * y = y * x →
      (∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D) ∧
      (∀ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D →
        (∀ g ∈ D, α g ∈ D) →
        (∀ e ∈ D, ¬ ∀ g ∈ D, α g = e * g * e⁻¹) ∧
        (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
          LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
        ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
          (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
        g ∈ inSubgroup layer (Subgroup.centralizer ({x} : Set T))

theorem LieGoodComponentFixT.toExists {t : StatedLieTag} (h : LieGoodComponentFixT t) :
    LieCentralizerComponentFixT t := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  exact (h T p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy).1

theorem LieCentralizerComponentT.toFix {t : StatedLieTag} (h : LieCentralizerComponentT t) :
    LieCentralizerComponentFixT t := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hM _ _ _ _ _ x hxp hx1 _ y hy2 hy1 hxy
  obtain ⟨D, hq, hle, hsub⟩ := h T p n f₀ hp hp5 hf₀ hM x y hxp hx1 hy2 hy1 hxy
  exact ⟨D, hle, hq, hsub⟩

theorem lieCentralizerComponent_of_tags (hOdd : FieldFix.OddCenterLie)
    (hT : ∀ t, LieCentralizerComponentFixT t) : LieCentralizerComponent := by
  intro G _ _ p J u hset hup hrank hpr d hdJ hd1 hdp hud ⟨s, hsmem, hs2⟩
  obtain ⟨hp, hp5, hq, hEven, hrk, hZ, hfa⟩ := hset
  obtain ⟨he, c, hcC, hc1, hcp, huc⟩ := hrank
  have hp2 : p ≠ 2 := by omega
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have huJ : u ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥J := by rw [hπdef, QuotientGroup.ker_mk']
  set α := centerQuotientConj J ⟨u, hu⟩ with hα
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := fieldAutT_of_inducesFieldAut hp hZ hu hup hfa
  have hLR2 := localRankLeTwo_of_evenRank he hp hp2 hZ hcC hc1 hcp
  have hLRA := localRankAut_of_evenRank he hp hp2 hZ hu hup huJ hcC hc1 hcp huc
  have hαp : α ^ p = 1 := centerQuotientConj_pow hu hup
  have hαinn : α ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q', hq'⟩
    exact huJ (mem_sup_of_inner hq.1 hu hq'.symm)
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J) :=
    hOdd ↥J hq t n (p * f₀) (by nlinarith) hM
  have hprT : CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) = 1 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (Subgroup.center ↥J) hZ]
    exact hpr
  have hsC : s ∈ J ∧ s ∈ Subgroup.centralizer ({d} : Set G) := Subgroup.mem_inf.mp hsmem
  have hsd : s * d = d * s := Subgroup.mem_centralizer_singleton_iff.mp hsC.2
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  set sJ : ↥J := ⟨s, hsC.1⟩ with hsJdef
  have hdJp : dJ ^ p = 1 := Subtype.ext hdp
  have hsJ2 : orderOf sJ = 2 := by
    rw [← Subgroup.orderOf_coe sJ]
    exact hs2
  have hsJsq : sJ ^ 2 = 1 := by
    have := pow_orderOf_eq_one sJ
    rwa [hsJ2] at this
  have hy1 : π sJ ≠ 1 := by
    intro h1
    have hc : sJ ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff sJ).mp h1
    have h2 := _root_.orderOf_dvd_natCard (⟨sJ, hc⟩ : Subgroup.center ↥J)
    rw [Subgroup.orderOf_mk, hsJ2] at h2
    exact hZ2 h2
  have hxy : π dJ * π sJ = π sJ * π dJ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hsd.symm)
  have hx1 : π dJ ≠ 1 := by
    intro h1
    apply hd1
    have hc : dJ ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff dJ).mp h1
    have h2 : orderOf (⟨dJ, hc⟩ : Subgroup.center ↥J) ∣ p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hdJp
    have h3 := _root_.orderOf_dvd_natCard (⟨dJ, hc⟩ : Subgroup.center ↥J)
    rcases (Nat.dvd_prime hp).mp h2 with h | h
    · rw [Subgroup.orderOf_mk] at h
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
    · rw [h] at h3
      exact absurd h3 hZ
  have hαx : α (π dJ) = π dJ := by
    rw [hα]
    change centerQuotientConj J ⟨u, hu⟩ (dJ : ↥J ⧸ Subgroup.center ↥J) =
      (dJ : ↥J ⧸ Subgroup.center ↥J)
    rw [centerQuotientConj_mk_apply]
    congr 1
    apply Subtype.ext
    show u * d * u⁻¹ = d
    rw [hud, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨D₀, hcent, hq₀, hsub⟩ := hT t _ p hp hp5 hLR2 hprT n f₀ hf₀ hM α hαp hαinn hLRA hX
    (π dJ) (by rw [← map_pow, hdJp, map_one]) hx1 hαx (π sJ)
    (by rw [← map_pow, hsJsq, map_one]) hy1 hxy
  exact exists_isComponentOf_of_quotient π hπ hker hp hZ hdJ hdp hq₀ hcent hsub

end CFSG.RankThree.PartOne
