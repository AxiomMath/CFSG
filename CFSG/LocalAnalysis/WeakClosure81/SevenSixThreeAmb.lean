module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoHall
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_right_of_le_normalizer {K N : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (K ⊔ N) = N.relIndex K := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hK
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
  exact (Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient K N hK).toEquiv).symm

theorem isPGroup_quotient_of_exp {J Y : Subgroup G} [(J.subgroupOf Y).Normal] {p : ℕ}
    (hexp : ∀ y ∈ Y, y ^ p ∈ J) : IsPGroup p (↥Y ⧸ J.subgroupOf Y) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr (by simpa using hexp y.1 y.2)

theorem hyp76_of_member {V H E J A Y : Subgroup G} {p : ℕ} [(J.subgroupOf Y).Normal]
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsMulCommutative E) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hJ : J ≤ pCoreOf 2 H)
    (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J) (hA : A ∈ omegaSet V H E)
    (hJY : J ≤ Y) (hYH : Y ≤ H) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hfaith : ∀ a ∈ A, (∀ y ∈ Y, ⁅a, y⁆ ∈ J) → a ∈ J) (hexp : ∀ y ∈ Y, y ^ p ∈ J) :
    Hyp76 V H E J A Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg := isPGroup_quotient_of_exp (J := J) (Y := Y) hexp
  refine ⟨hV, hTI, hE, hEH, hEnorm, hOmH, hJ, hJnorm, hIJ, hJY, hYH, hAY, ?_, ?_, hfaith, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    have h1 : J.relIndex Y = Nat.card (↥Y ⧸ J.subgroupOf Y) := Subgroup.index_eq_card _
    rw [h1, hn]
    exact (hp.odd_of_ne_two hp2).pow
  · exact hpg.isNilpotent
  · refine le_antisymm ?_ (iSup₂_le fun U _ => iSup_le fun h => h)
    exact le_iSup₂_of_le A hA (le_iSup_of_le le_rfl le_rfl)
  · exact (isElemAbelian_of_mem_omegaSet hV hA).isPGroup

theorem Hyp76.inf_le_iSub_of_isPGroup {V H E J A X : Subgroup G} [(J.subgroupOf X).Normal]
    (h : Hyp76 V H E J A X) {Y : Subgroup G} (hY : IsHallCompl V H E J X Y) {S : Subgroup G}
    (hS : IsPGroup 2 S) : S ⊓ Y ≤ iSub V H E := by
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun W => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIN : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le_H h.normal_E)
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le h.le_pCore
  have hI2 : IsPGroup 2 (iSub V H E) := hJ2.to_le h.iSub_le
  have hSY : S ⊓ Y ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    inf_le_right.trans (hY.le_X.trans (h.X_le_H.trans hIN))
  have hW2 : IsPGroup 2 ↥((S ⊓ Y) ⊔ iSub V H E) :=
    (hS.to_le inf_le_left).to_sup_of_normal_right' hI2 hSY
  have hIW : iSub V H E ≤ (S ⊓ Y) ⊔ iSub V H E := le_sup_right
  have hWY : (S ⊓ Y) ⊔ iSub V H E ≤ Y := sup_le inf_le_right hY.iSub_le
  have hodd := h.relIndex_odd_of_isHallCompl hY hIW hWY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW2
  have hdvd : (iSub V H E).relIndex ((S ⊓ Y) ⊔ iSub V H E) ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hi0 : i = 0 := by
    rw [hi] at hodd
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  have h1 : (iSub V H E).relIndex ((S ⊓ Y) ⊔ iSub V H E) = 1 := by rw [hi, hi0, pow_zero]
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)

theorem IsHallCompl.relIndex_eq {V H E J X Y : Subgroup G} (hY : IsHallCompl V H E J X Y)
    (hXn : X ≤ Subgroup.normalizer (J : Set G)) :
    (iSub V H E).relIndex Y = J.relIndex X := by
  have hYN : Y ≤ Subgroup.normalizer (J : Set G) := hY.le_X.trans hXn
  have h2 : J.relIndex X = J.relIndex Y := by
    rw [← hY.sup_J]
    exact relIndex_sup_right_of_le_normalizer hYN
  have h3 : J.relIndex Y = (iSub V H E).relIndex Y := by
    rw [← Subgroup.inf_relIndex_left Y J, hY.inf_J]
  rw [h2, h3]

theorem IsHallCompl.le_commutator_sup {V H E J X Y : Subgroup G} (hY : IsHallCompl V H E J X Y)
    (hXn : X ≤ Subgroup.normalizer (J : Set G)) {u : G}
    (huJ : u ∈ Subgroup.normalizer (J : Set G)) (huY : u ∈ Subgroup.normalizer (Y : Set G))
    (hXu : X ≤ ⁅X, Subgroup.zpowers u⁆ ⊔ J) :
    Y ≤ ⁅Y, Subgroup.zpowers u⁆ ⊔ iSub V H E := by
  have hYN : Y ≤ Subgroup.normalizer (J : Set G) := hY.le_X.trans hXn
  have hzn : Subgroup.zpowers u ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.zpowers_le.mpr huJ
  have hCY : ⁅Y, Subgroup.zpowers u⁆ ≤ Y := commutator_zpowers_le huY
  have h1 : ⁅X, Subgroup.zpowers u⁆ ≤ ⁅Y, Subgroup.zpowers u⁆ ⊔ J := by
    rw [Subgroup.commutator_le]
    intro x hx v hv
    have hx' : x ∈ (↑Y : Set G) * (↑J : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y J hYN, hY.sup_J]
      exact hx
    rw [Set.mem_mul] at hx'
    obtain ⟨y, hy, j, hj, rfl⟩ := hx'
    have hvj : v * j⁻¹ * v⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hzn hv) j⁻¹).mp (J.inv_mem hj)
    have hjv : ⁅j, v⁆ ∈ J := by
      rw [show ⁅j, v⁆ = j * (v * j⁻¹ * v⁻¹) by simp only [commutatorElement_def]; group]
      exact J.mul_mem hj hvj
    have hyjv : y * ⁅j, v⁆ * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hYN hy) _).mp hjv
    have hid : ⁅y * j, v⁆ = (y * ⁅j, v⁆ * y⁻¹) * ⁅y, v⁆ := by
      simp only [commutatorElement_def]; group
    rw [hid]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyjv)
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy hv))
  have h2 : Y ≤ ⁅Y, Subgroup.zpowers u⁆ ⊔ J :=
    hY.le_X.trans (hXu.trans (sup_le h1 le_sup_right))
  intro y hy
  have hCN : ⁅Y, Subgroup.zpowers u⁆ ≤ Subgroup.normalizer (J : Set G) := hCY.trans hYN
  have hmem : y ∈ (↑⁅Y, Subgroup.zpowers u⁆ : Set G) * (↑J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ J hCN]
    exact h2 hy
  rw [Set.mem_mul] at hmem
  obtain ⟨c, hc, j, hj, rfl⟩ := hmem
  have hjY : j ∈ Y := by
    have h3 : c⁻¹ * (c * j) ∈ Y := Y.mul_mem (Y.inv_mem (hCY hc)) hy
    simpa using h3
  have hjI : j ∈ iSub V H E := by
    rw [← hY.inf_J]
    exact ⟨hjY, hj⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hjI)

theorem commutator_sup_le_of_le_sup {X J A B : Subgroup G} [(J.subgroupOf X).Normal]
    (hJX : J ≤ X) (hB : B ≤ Subgroup.normalizer (J : Set G)) (hA : A ≤ J ⊔ B) :
    ⁅X, A⁆ ⊔ J ≤ ⁅X, B⁆ ⊔ J := by
  have hXn : X ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).1 inferInstance
  refine sup_le ?_ le_sup_right
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have ha' : a ∈ B ⊔ J := by
    rw [sup_comm]
    exact hA ha
  have ha'' : a ∈ (↑B : Set G) * (↑J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ J hB]
    exact ha'
  rw [Set.mem_mul] at ha''
  obtain ⟨v, hv, j, hj, rfl⟩ := ha''
  have hxj : ⁅x, j⁆ ∈ J := by
    have hmem : x * j * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hXn hx) j).mp hj
    rw [commutatorElement_def]
    exact J.mul_mem hmem (J.inv_mem hj)
  have hvxj : v * ⁅x, j⁆ * v⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hB hv) _).mp hxj
  have hid : ⁅x, v * j⁆ = ⁅x, v⁆ * (v * ⁅x, j⁆ * v⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [hid]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hv))
    (Subgroup.mem_sup_right hvxj)

theorem IsHallCompl.ne_of_faithful {V H E J X Y U : Subgroup G} (hY : IsHallCompl V H E J X Y)
    (hIJ : iSub V H E ≤ J) (hUN : U ≤ Subgroup.normalizer (J : Set G)) (hUJ : ¬ U ≤ J)
    (hfaith : ∀ a ∈ U, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J) : iSub V H E ≠ Y := by
  intro hIY
  apply hUJ
  intro a ha
  apply hfaith a ha
  intro x hx
  have hXJ : X ≤ J := by
    rw [← hY.sup_J, ← hIY]
    exact sup_le hIJ le_rfl
  have hxJ : x ∈ J := hXJ hx
  have h1 : a * x * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hUN ha) x).mp hxJ
  rw [commutatorElement_def]
  exact J.mul_mem h1 (J.inv_mem hxJ)

end CFSG.LocalAnalysis.WeakClosure81
