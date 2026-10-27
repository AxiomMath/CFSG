module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

private theorem gk3_commutator_central_mul {G : Type*} [Group G] {a b u v : G} (hua : Commute u a)
    (hub : Commute u b) (hva : Commute v a) (hvb : Commute v b) (huv : Commute u v) :
    (u * a) * (v * b) * (u * a)⁻¹ * (v * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hX : Commute u (a * v * b * a⁻¹) :=
    ((hua.mul_right huv).mul_right hub).mul_right hua.inv_right
  have hw : Commute v (a * b * a⁻¹ * b⁻¹) :=
    ((hva.mul_right hvb).mul_right hva.inv_right).mul_right hvb.inv_right
  calc (u * a) * (v * b) * (u * a)⁻¹ * (v * b)⁻¹
      = u * (a * v * b * a⁻¹) * u⁻¹ * b⁻¹ * v⁻¹ := by group
    _ = (a * v * b * a⁻¹) * b⁻¹ * v⁻¹ := by rw [hX.mul_inv_cancel]
    _ = (v * a) * b * a⁻¹ * b⁻¹ * v⁻¹ := by rw [hva.symm.eq]
    _ = v * (a * b * a⁻¹ * b⁻¹) * v⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := hw.mul_inv_cancel

private theorem gk3_le_of_not_central {W : Type} [Group W] {J N : Subgroup W}
    (hq : CFSG.Assembly.IsQuasisimple ↥J)
    (hNn : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N)
    (hnc : ∃ m ∈ N ⊓ J, ∃ j ∈ J, m * j ≠ j * m) : J ≤ N := by
  obtain ⟨hperf, hsimple⟩ := hq
  set M : Subgroup ↥J := (N ⊓ J).subgroupOf J with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨hmN, hmJ⟩ := Subgroup.mem_inf.mp hm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa using hNn (g : W) g.2 (m : W) hmN
    · simpa using J.mul_mem (J.mul_mem g.2 hmJ) (J.inv_mem g.2)
  set π := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  haveI hπn : (M.map π).Normal := hMn.map π (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map π) with hbot | htop
  · exfalso
    obtain ⟨m, hm, j, hj, hne⟩ := hnc
    have hmM : (⟨m, hm.2⟩ : ↥J) ∈ M := by rw [hM, Subgroup.mem_subgroupOf]; exact hm
    have h1 : π ⟨m, hm.2⟩ ∈ M.map π := ⟨_, hmM, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff] at h1
    exact hne (congrArg Subtype.val (h1 ⟨j, hj⟩).symm)
  · have hcomm : commutator ↥J ≤ M := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have h1 : π g₁ ∈ M.map π := by rw [htop]; trivial
      have h2 : π g₂ ∈ M.map π := by rw [htop]; trivial
      obtain ⟨m₁, hm₁, hπ₁⟩ := h1
      obtain ⟨m₂, hm₂, hπ₂⟩ := h2
      have hz₁ : g₁ * m₁⁻¹ ∈ Subgroup.center ↥J := by
        have h1 : (m₁ : ↥J ⧸ Subgroup.center ↥J) = (g₁ : ↥J ⧸ Subgroup.center ↥J) := hπ₁
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h1,
          mul_inv_cancel]
      have hz₂ : g₂ * m₂⁻¹ ∈ Subgroup.center ↥J := by
        have h1 : (m₂ : ↥J ⧸ Subgroup.center ↥J) = (g₂ : ↥J ⧸ Subgroup.center ↥J) := hπ₂
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h1,
          mul_inv_cancel]
      have hz₁c := Subgroup.mem_center_iff.mp hz₁
      have hz₂c := Subgroup.mem_center_iff.mp hz₂
      have hg₁ : g₁ = (g₁ * m₁⁻¹) * m₁ := by group
      have hg₂ : g₂ = (g₂ * m₂⁻¹) * m₂ := by group
      have key : ⁅g₁, g₂⁆ = ⁅m₁, m₂⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        conv_lhs => rw [hg₁, hg₂]
        exact gk3_commutator_central_mul (hz₁c m₁).symm (hz₁c m₂).symm (hz₂c m₁).symm (hz₂c m₂).symm
          (hz₁c _).symm
      rw [key]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
    rw [hperf, top_le_iff] at hcomm
    intro j hj
    have : (⟨j, hj⟩ : ↥J) ∈ M := by rw [hcomm]; trivial
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1

private theorem gk3_centralizes_of_central {W : Type} [Group W] {J N : Subgroup W}
    (hq : CFSG.Assembly.IsQuasisimple ↥J)
    (hNn : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N)
    (hc : ∀ m ∈ N ⊓ J, ∀ j ∈ J, m * j = j * m) {y : W} (hyN : y ∈ N)
    (hyJ : ∀ j ∈ J, y * j * y⁻¹ ∈ J) : ∀ j ∈ J, y * j = j * y := by
  obtain ⟨hperf, -⟩ := hq
  have hz : ∀ a ∈ J, (y * a * y⁻¹) * a⁻¹ ∈ N ⊓ J := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨?_, J.mul_mem (hyJ a ha) (J.inv_mem ha)⟩
    have h1 : a * y⁻¹ * a⁻¹ ∈ N := hNn a ha y⁻¹ (N.inv_mem hyN)
    have h2 : y * (a * y⁻¹ * a⁻¹) ∈ N := N.mul_mem hyN h1
    simpa [mul_assoc] using h2
  set S : Subgroup ↥J := (Subgroup.centralizer ({y} : Set W)).comap J.subtype with hS
  have hcomm : commutator ↥J ≤ S := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hza := hz a a.2
    have hzb := hz b b.2
    have hua : Commute ((y * (a : W) * y⁻¹) * (a : W)⁻¹) a := hc _ hza a a.2
    have hub : Commute ((y * (a : W) * y⁻¹) * (a : W)⁻¹) b := hc _ hza b b.2
    have hva : Commute ((y * (b : W) * y⁻¹) * (b : W)⁻¹) a := hc _ hzb a a.2
    have hvb : Commute ((y * (b : W) * y⁻¹) * (b : W)⁻¹) b := hc _ hzb b b.2
    have huv : Commute ((y * (a : W) * y⁻¹) * (a : W)⁻¹) ((y * (b : W) * y⁻¹) * (b : W)⁻¹) :=
      hc _ hza _ hzb.2
    have key := gk3_commutator_central_mul hua hub hva hvb huv
    have hya : ((y * (a : W) * y⁻¹) * (a : W)⁻¹) * (a : W) = y * (a : W) * y⁻¹ := by group
    have hyb : ((y * (b : W) * y⁻¹) * (b : W)⁻¹) * (b : W) = y * (b : W) * y⁻¹ := by group
    rw [hya, hyb] at key
    have hconj : y * ((a : W) * b * (a : W)⁻¹ * (b : W)⁻¹) * y⁻¹ =
        (a : W) * b * (a : W)⁻¹ * (b : W)⁻¹ := by
      calc y * ((a : W) * b * (a : W)⁻¹ * (b : W)⁻¹) * y⁻¹
          = (y * (a : W) * y⁻¹) * (y * (b : W) * y⁻¹) * (y * (a : W) * y⁻¹)⁻¹ *
            (y * (b : W) * y⁻¹)⁻¹ := by group
        _ = _ := key
    rw [hS, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    simp only [Subgroup.subtype_apply, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * ((a : W) * b * (a : W)⁻¹ * (b : W)⁻¹)
        = (y * ((a : W) * b * (a : W)⁻¹ * (b : W)⁻¹) * y⁻¹) * y := by group
      _ = (a : W) * b * (a : W)⁻¹ * (b : W)⁻¹ * y := by rw [hconj]
  rw [hperf, top_le_iff] at hcomm
  intro j hj
  have : (⟨j, hj⟩ : ↥J) ∈ S := by rw [hcomm]; trivial
  rw [hS, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
  exact this y (Set.mem_singleton y)

theorem ggSporK_B7a3 {W : Type} [Group W] [Finite W] (hb : BSevenCentAbelian W) {E : Subgroup W}
    (hE : IsElemAbelian 7 E) (hEcard : Nat.card E = 49) {x : W} (hxE : x ∈ E)
    (hx : orderOf x = 7) {J : Subgroup W} (hJ : IsComponentOf J (Subgroup.centralizer {x}))
    (hJn : ∀ c ∈ Subgroup.centralizer ({x} : Set W), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    {N : Subgroup W} (hNC : N ≤ Subgroup.centralizer {x})
    (hNn : ∀ c ∈ Subgroup.centralizer ({x} : Set W), ∀ n ∈ N, c * n * c⁻¹ ∈ N) {y : W}
    (hyE : y ∈ E) (hyN : y ∈ N) (hyx : y ∉ Subgroup.zpowers x) : J ≤ N := by
  by_contra hJN
  have hq := hJ.2.2
  have hxJ : ∀ j ∈ J, x * j = j * x := fun j hj =>
    Subgroup.mem_centralizer_iff.mp (hJ.1 hj) x (Set.mem_singleton x)
  have hNn' : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N := fun j hj n hn => hNn j (hJ.1 hj) n hn
  have hc : ∀ m ∈ N ⊓ J, ∀ j ∈ J, m * j = j * m := by
    by_contra hnc
    push Not at hnc
    exact hJN (gk3_le_of_not_central hq hNn' hnc)
  have hyJ : ∀ j ∈ J, y * j * y⁻¹ ∈ J := fun j hj => hJn y (hNC hyN) j hj
  have hyc := gk3_centralizes_of_central hq hNn' hc hyN hyJ
  have hS : Subgroup.zpowers x ⊔ Subgroup.zpowers y = E := by
    set S := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hSdef
    have hSE : S ≤ E := sup_le (Subgroup.zpowers_le.mpr hxE) (Subgroup.zpowers_le.mpr hyE)
    have h1 : Nat.card (Subgroup.zpowers x) = 7 := by rw [Nat.card_zpowers, hx]
    have h2 : 7 ∣ Nat.card S := h1 ▸ Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers x ≤ S)
    have h3 : Nat.card S ∣ 49 := hEcard ▸ Subgroup.card_dvd_of_le hSE
    have h4 : Nat.card S ≠ 7 := by
      intro h7
      have heq : Subgroup.zpowers x = S :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h1, h7])
      exact hyx (heq ▸ (le_sup_right : Subgroup.zpowers y ≤ S) (Subgroup.mem_zpowers y))
    have h49 : Nat.card S = 49 := by
      have hmem : Nat.card S ∈ Nat.divisors 49 := Nat.mem_divisors.mpr ⟨h3, by norm_num⟩
      have hdiv : Nat.divisors 49 = {1, 7, 49} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · rw [h] at h2; omega
      · exact absurd h h4
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hSE (by rw [h49, hEcard])
  have hJE : ∀ j ∈ J, j ∈ Subgroup.centralizer (E : Set W) := by
    intro j hj
    have hle : E ≤ Subgroup.centralizer ({j} : Set W) := by
      rw [← hS]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hxJ j hj).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hyc j hj).symm
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hle hg) j (Set.mem_singleton j)).symm
  have hab := hb E hE hEcard
  have hcomm : ∀ a b : ↥J, a * b = b * a := fun a b =>
    Subtype.ext (hab a (hJE a a.2) b (hJE b b.2))
  haveI := hq.2
  obtain ⟨q, hq1⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  apply hq1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro b
  exact hcomm b a

end CFSG.StandardType.SporadicShape
