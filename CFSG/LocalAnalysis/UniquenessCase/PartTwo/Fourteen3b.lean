module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_ge_of_isPGroup {p : ℕ} {K Y : Subgroup G} (hY : IsPGroup p Y)
    (hYK : Y ≤ K) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ Y ≤ P := by
  obtain ⟨Q, hQ⟩ := (hY.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun y hy => ?_⟩
  exact ⟨⟨y, hYK hy⟩, hQ hy, rfl⟩

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem sup_le_M (h : Hyp141 D L₁ L₂ X) : L₁ ⊔ L₂ ≤ D.M :=
  sup_le (CFSG.Quasithin.A3.subnormal_le h.mem₁.1)
    (CFSG.Quasithin.A3.subnormal_le h.mem₂.1)

theorem X_le_M (h : Hyp141 D L₁ L₂ X) : X ≤ D.M :=
  h.sylow.le.trans (sup_le_M h)

theorem exists_isSylowOf_ge (h : Hyp141 D L₁ L₂ X) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M ∧ X ≤ P :=
  exists_isSylowOf_ge_of_isPGroup h.sylow.isPGroup (X_le_M h)

theorem acts_trivially_mul_left (h : Hyp141 D L₁ L₂ X) {a w : G} (ha : a ∈ L₂) :
    (∀ l ∈ L₁, (a * w) * l * (a * w)⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁) ↔
      ∀ l ∈ L₁, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ := by
  set Q := pCoreOf 2 L₁ with hQ
  have haQ : a ∈ normalizer (Q : Set G) :=
    (UC6S846.normalizer_le_normalizer_pCoreOf L₁) (le_normalizer_left h ha)
  have hd_mem : ∀ l ∈ L₁, a * l * a⁻¹ * l⁻¹ ∈ Q := by
    intro l hl
    have hcomm : a * l * a⁻¹ * l⁻¹ ∈ ⁅L₂, L₁⁆ :=
      Subgroup.commutator_mem_commutator ha hl
    rw [Subgroup.commutator_comm] at hcomm
    exact (commutator_le h).trans inf_le_left hcomm
  constructor
  · intro h1 l hl
    have hid : (a * w) * l * (a * w)⁻¹ * l⁻¹ =
        (a * (w * l * w⁻¹ * l⁻¹) * a⁻¹) * (a * l * a⁻¹ * l⁻¹) := by group
    have hprod : (a * (w * l * w⁻¹ * l⁻¹) * a⁻¹) * (a * l * a⁻¹ * l⁻¹) ∈ Q := by
      rw [← hid]
      exact h1 l hl
    have haca : a * (w * l * w⁻¹ * l⁻¹) * a⁻¹ ∈ Q :=
      (Subgroup.mul_mem_cancel_right Q (hd_mem l hl)).1 hprod
    exact (Subgroup.mem_normalizer_iff.1 haQ (w * l * w⁻¹ * l⁻¹)).2 haca
  · intro h2 l hl
    have hc : w * l * w⁻¹ * l⁻¹ ∈ Q := h2 l hl
    have haca : a * (w * l * w⁻¹ * l⁻¹) * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 haQ (w * l * w⁻¹ * l⁻¹)).1 hc
    have hid : (a * w) * l * (a * w)⁻¹ * l⁻¹ =
        (a * (w * l * w⁻¹ * l⁻¹) * a⁻¹) * (a * l * a⁻¹ * l⁻¹) := by group
    rw [hid]
    exact Q.mul_mem haca (hd_mem l hl)

theorem exists_mul_mem_centOverO2 (h : Hyp141 D L₁ L₂ X) {P : Subgroup G} (hP : IsPGroup 3 P)
    (hXP : X ≤ P) (hP₁ : P ≤ normalizer (L₁ : Set G)) (hP₂ : P ≤ normalizer (L₂ : Set G))
    {p : G} (hp : p ∈ P) : ∃ x ∈ X, x⁻¹ * p ∈ F08.CentOverO2 P (L₁ ⊔ L₂) := by
  obtain ⟨a₁, ha₁, h₁⟩ :=
    exists_mem_acts_eq h.shape₁ hP hP₁ (A := X ⊓ L₁) (inf_le_left.trans hXP) inf_le_right
      (card_inf_left h) hp
  have hp'P : a₁⁻¹ * p ∈ P :=
    P.mul_mem (P.inv_mem (hXP (Subgroup.mem_inf.1 ha₁).1)) hp
  obtain ⟨a₂, ha₂, h₂⟩ :=
    exists_mem_acts_eq h.shape₂ hP hP₂ (A := X ⊓ L₂) (inf_le_left.trans hXP) inf_le_right
      (card_inf_right h) hp'P
  have hwP : a₂⁻¹ * (a₁⁻¹ * p) ∈ P :=
    P.mul_mem (P.inv_mem (hXP (Subgroup.mem_inf.1 ha₂).1)) hp'P
  have hw₁ : a₂⁻¹ * (a₁⁻¹ * p) ∈ normalizer (L₁ : Set G) := hP₁ hwP
  have hw₂ : a₂⁻¹ * (a₁⁻¹ * p) ∈ normalizer (L₂ : Set G) := hP₂ hwP
  have hwtriv₁ : ∀ l ∈ L₁,
      (a₂⁻¹ * (a₁⁻¹ * p)) * l * (a₂⁻¹ * (a₁⁻¹ * p))⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ :=
    (acts_trivially_mul_left h (a := a₂⁻¹) (w := a₁⁻¹ * p)
      (Subgroup.inv_mem _ (Subgroup.mem_inf.1 ha₂).2)).2 h₁
  have hwtriv : ∀ l ∈ L₁ ⊔ L₂,
      (a₂⁻¹ * (a₁⁻¹ * p)) * l * (a₂⁻¹ * (a₁⁻¹ * p))⁻¹ * l⁻¹ ∈ pCoreOf 2 (L₁ ⊔ L₂) :=
    (acts_trivially_sup_iff h hw₁ hw₂).2 ⟨hwtriv₁, h₂⟩
  refine ⟨a₁ * a₂, X.mul_mem (Subgroup.mem_inf.1 ha₁).1 (Subgroup.mem_inf.1 ha₂).1, ?_⟩
  have hx : (a₁ * a₂)⁻¹ * p = a₂⁻¹ * (a₁⁻¹ * p) := by group
  rw [hx]
  exact (mem_centOverO2_iff (X := P) (L := L₁ ⊔ L₂)).2 ⟨hwP, hwtriv⟩

theorem centOverO2_le_centralizer (h : Hyp141 D L₁ L₂ X) {P : Subgroup G} (hP : IsPGroup 3 P)
    (hXP : X ≤ P) : F08.CentOverO2 P (L₁ ⊔ L₂) ≤ centralizer (X : Set G) := by
  intro y hy
  obtain ⟨hyP, hy'⟩ := (mem_centOverO2_iff (X := P) (L := L₁ ⊔ L₂)).1 hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxL : x ∈ L₁ ⊔ L₂ := h.sylow.le hx
  have hc : y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (L₁ ⊔ L₂) := hy' x hxL
  have hcP : y * x * y⁻¹ * x⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hyP (hXP hx)) (P.inv_mem hyP)) (P.inv_mem (hXP hx))
  have hcone : y * x * y⁻¹ * x⁻¹ = 1 :=
    UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup Nat.prime_three (by norm_num) hP
      (UC6S846.isPGroup_pCoreOf (L₁ ⊔ L₂)) hcP hc
  exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := y) (g₂ := x)).1 hcone).symm

theorem eq_one_of_acts_trivially {L K : Subgroup G} (hL : IsL3 (Bar2 L) 1)
    (hK : IsPGroup 3 K) {x : G} (hxK : x ∈ K) (hxL : x ∈ L)
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : x = 1 := by
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let x' : ↥L := ⟨x, hxL⟩
  have hsimple := isSimpleGroup_of_isL3 hL
  have hx'center : (QuotientGroup.mk x' : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro ybar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ybar
    have hmem : x' * g * x'⁻¹ * g⁻¹ ∈ Q := by
      have hxL' : x * ↑g * x⁻¹ * ↑g⁻¹ ∈ L :=
        Subgroup.map_subtype_le (CFSG.pCore 2 ↥L) (hx g g.2)
      have h1 : (⟨x * ↑g * x⁻¹ * ↑g⁻¹, hxL'⟩ : ↥L) ∈ (pCoreOf 2 L).subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact hx g g.2
      rw [CFSG.openPCoreOf_subgroupOf 2 L] at h1
      have heq : x' * g * x'⁻¹ * g⁻¹ = (⟨x * ↑g * x⁻¹ * ↑g⁻¹, hxL'⟩ : ↥L) := by
        ext
        simp [x']
      rw [heq]
      exact h1
    have h1 : (QuotientGroup.mk (x' * g * x'⁻¹ * g⁻¹) : Bar2 L) = 1 :=
      (QuotientGroup.eq_one_iff (N := Q) (x' * g * x'⁻¹ * g⁻¹)).2 hmem
    have hab : (QuotientGroup.mk x' : Bar2 L) * QuotientGroup.mk g =
        QuotientGroup.mk g * QuotientGroup.mk x' := by
      let π' : ↥L →* Bar2 L := QuotientGroup.mk' Q
      have h1' : π' (x' * g * x'⁻¹ * g⁻¹) = 1 := by simpa [π'] using h1
      have h2 : π' x' * π' g * (π' x')⁻¹ * (π' g)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using h1'
      have h3 : (π' x' * π' g) * (π' g * π' x')⁻¹ = 1 := by
        rw [show (π' x' * π' g) * (π' g * π' x')⁻¹ =
            π' x' * π' g * (π' x')⁻¹ * (π' g)⁻¹ by group]
        exact h2
      have h4 : π' x' * π' g = π' g * π' x' := mul_inv_eq_one.1 h3
      simpa [π'] using h4
    exact hab.symm
  rw [center_eq_bot_of_isL3 hL, Subgroup.mem_bot] at hx'center
  have hx'Q : x' ∈ Q := (QuotientGroup.eq_one_iff (N := Q) x').1 (by simpa [Q] using hx'center)
  have hxpc : x ∈ pCoreOf 2 L := by
    have hsub : x' ∈ (pCoreOf 2 L).subgroupOf L := by
      rw [CFSG.openPCoreOf_subgroupOf 2 L]
      exact hx'Q
    simpa [x'] using (Subgroup.mem_subgroupOf (H := pCoreOf 2 L) (K := L)).1 hsub
  exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup Nat.prime_three (by norm_num) hK
    (UC6S846.isPGroup_pCoreOf L) hxK hxpc

theorem disjoint_centOverO2 (h : Hyp141 D L₁ L₂ X) {P : Subgroup G} (hP : IsPGroup 3 P)
    (hXP : X ≤ P) : Disjoint X (F08.CentOverO2 P (L₁ ⊔ L₂)) := by
  rw [Subgroup.disjoint_def]
  intro x hx hxY
  obtain ⟨-, hxc⟩ := (mem_centOverO2_iff (X := P) (L := L₁ ⊔ L₂)).1 hxY
  have hxL : x ∈ L₁ ⊔ L₂ := h.sylow.le hx
  have hw₁ : x ∈ normalizer (L₁ : Set G) :=
    (sup_le Subgroup.le_normalizer (le_normalizer_left h)) hxL
  have hw₂ : x ∈ normalizer (L₂ : Set G) :=
    (sup_le (le_normalizer_right h) Subgroup.le_normalizer) hxL
  obtain ⟨htriv₁, htriv₂⟩ := (acts_trivially_sup_iff h hw₁ hw₂).1 hxc
  have hle : X ⊓ L₂ ≤ normalizer ((X ⊓ L₁ : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (Subgroup.mem_inf.1 hy).1,
        le_normalizer_left h (Subgroup.mem_inf.1 hy).2⟩
  have hxmem : x ∈ ((X ⊓ L₁ : Subgroup G) : Set G) * ((X ⊓ L₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (X ⊓ L₁) (X ⊓ L₂) hle]
    rw [← X_eq_sup h]
    exact hx
  rw [Set.mem_mul] at hxmem
  obtain ⟨x₁, hx₁, x₂, hx₂, hx12⟩ := hxmem
  have hcomm12 : x₁ * x₂ = x₂ * x₁ := commute_inf h x₁ hx₁ x₂ hx₂
  have htriv₁' : ∀ l ∈ L₁, x₁ * l * x₁⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ :=
    (acts_trivially_mul_left h (a := x₂) (w := x₁) (Subgroup.mem_inf.1 hx₂).2).1 (by
      intro l hl
      have hxeq : x = x₂ * x₁ := by rw [← hx12, hcomm12]
      rw [← hxeq]
      exact htriv₁ l hl)
  have htriv₂' : ∀ l ∈ L₂, x₂ * l * x₂⁻¹ * l⁻¹ ∈ pCoreOf 2 L₂ :=
    (acts_trivially_mul_left h.symm (a := x₁) (w := x₂) (Subgroup.mem_inf.1 hx₁).2).1 (by
      intro l hl
      rw [hx12]
      exact htriv₂ l hl)
  have hx₁one : x₁ = 1 :=
    eq_one_of_acts_trivially h.shape₁ h.sylow.isPGroup (Subgroup.mem_inf.1 hx₁).1
      (Subgroup.mem_inf.1 hx₁).2 htriv₁'
  have hx₂one : x₂ = 1 :=
    eq_one_of_acts_trivially h.shape₂ h.sylow.isPGroup (Subgroup.mem_inf.1 hx₂).1
      (Subgroup.mem_inf.1 hx₂).2 htriv₂'
  rw [← hx12, hx₁one, hx₂one, one_mul]

end Hyp141

theorem opp_three_eq_self_of_isL3 {M L : Subgroup G} (hL : L ∈ calC M) (hs : IsL3 (Bar2 L) 1) :
    Opp 3 L = L := by
  let J : Subgroup G := Opp 3 L
  have hJL : J ≤ L := by
    change Opp 3 L ≤ L
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact (Subgroup.closure_le L).mpr fun _ hx => hx.1
  have hnorm : L ≤ normalizer (J : Set G) := by
    intro m hm
    rw [UC6S846.mem_normalizer_iff_map_conj]
    have h := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy 3 m L
    have hL' : CFSG.RankThree.PartOne.conjBy m L = L := by
      unfold CFSG.RankThree.PartOne.conjBy
      exact UC6S846.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hm)
    rw [hL'] at h
    simpa [J, Opp, CFSG.RankThree.PartOne.conjBy] using h.symm
  let N : Subgroup ↥L := J.subgroupOf L
  have hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJL).2 hnorm
  letI : N.Normal := hNnormal
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hQ : IsPGroup 2 Q := CFSG.pCore_isPGroup
  let π : ↥L →* Bar2 L := QuotientGroup.mk' Q
  have hsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_of_isL3 hs
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
    Subgroup.map_injective L.subtype_injective (by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hL.2.1])
  have hdvd : 3 ∣ Nat.card (Bar2 L) := by rw [card_eq_of_isL3 hs]; norm_num
  have hdvdL : 3 ∣ Nat.card ↥L :=
    hdvd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' 3 hdvdL
  have hgN : g ∈ N := by
    change g ∈ J.subgroupOf L
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨g.2, 1, by rw [Subgroup.orderOf_coe, hgord]; norm_num⟩
  have hNQ : N ⊔ Q = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
    · exfalso
      have hπg : π g = 1 := by
        have hmem : π g ∈ N.map π := Subgroup.mem_map_of_mem π hgN
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      have hgQ : g ∈ Q :=
        (QuotientGroup.eq_one_iff (N := Q) g).1 (by simpa [π] using hπg)
      obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
      have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h3 : 3 ∣ 2 ^ k := by
        have := orderOf_dvd_of_pow_eq_one hk'
        rwa [hgord] at this
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    · apply top_le_iff.1
      intro y _
      have hmem : π y ∈ N.map π := by rw [htop]; exact Subgroup.mem_top (π y)
      obtain ⟨n, hn, hnπ⟩ := hmem
      have hndiff : n⁻¹ * y ∈ Q := by
        have hπ1 : π (n⁻¹ * y) = 1 := by
          rw [map_mul, map_inv, hnπ, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := Q) (n⁻¹ * y)).1 (by simpa [π] using hπ1)
      have hy : y = n * (n⁻¹ * y) := by group
      rw [hy]
      exact Subgroup.mul_mem_sup hn hndiff
  have hR : IsPGroup 2 (↥L ⧸ N) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ N ⊔ Q := hNQ ▸ Subgroup.mem_top z
    obtain ⟨n, hn, q, hq, hz'⟩ := Subgroup.mem_sup_of_normal_left.1 hz
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : ((n * q : ↥L) : ↥L ⧸ N) = (q : ↥L ⧸ N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
    rw [← hz']
    show (((n * q : ↥L) : ↥L ⧸ N)) ^ 2 ^ k = 1
    rw [h1, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  haveI : Group.IsNilpotent (↥L ⧸ N) := hR.isNilpotent
  have hle : (⊤ : Subgroup ↥L) ≤ N :=
    Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := N) (H := ⊤) hperf
  have hJtop : N = ⊤ := top_le_iff.1 hle
  have hLJ : L ≤ J := by
    intro y hy
    have hmemN : (⟨y, hy⟩ : ↥L) ∈ N := by rw [hJtop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf (H := J) (K := L)).1 (by simpa [N] using hmemN)
  show J = L
  exact le_antisymm hJL hLJ

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem opp_three_eq (h : Hyp141 D L₁ L₂ X) (hperm : PermutesPair D.M L₁ L₂) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (hXP : X ≤ P)
    (hP₁ : P ≤ normalizer (L₁ : Set G)) (hP₂ : P ≤ normalizer (L₂ : Set G))
    (hY : F08.CentOverO2 P (L₁ ⊔ L₂) = ⊥) : L₁ ⊔ L₂ = Opp 3 D.M := by
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPX : P ≤ X := by
    intro p hp
    obtain ⟨x, hx, hxcent⟩ := exists_mul_mem_centOverO2 h hP3 hXP hP₁ hP₂ hp
    have hxp : x⁻¹ * p = 1 := by
      rw [hY, Subgroup.mem_bot] at hxcent
      exact hxcent
    have hp_eq : p = x := (inv_mul_eq_one.1 hxp).symm
    rw [hp_eq]
    exact hx
  have hPL : P ≤ L₁ ⊔ L₂ := hPX.trans h.sylow.le
  have hMN : D.M ≤ normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := M_le_normalizer_sup h hperm
  have hOppM : Opp 3 D.M ≤ L₁ ⊔ L₂ := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le (L₁ ⊔ L₂)).mpr fun x hx => ?_
    obtain ⟨hxM, k, hk⟩ := hx
    let Y : Subgroup G := Subgroup.zpowers x
    have hY3 : IsPGroup 3 Y := by
      rw [IsPGroup.iff_card]
      exact ⟨k, by rw [Nat.card_zpowers, hk]⟩
    have hYM : Y ≤ D.M := by rw [Subgroup.zpowers_le]; exact hxM
    obtain ⟨P', hP', hYP'⟩ := exists_isSylowOf_ge_of_isPGroup hY3 hYM
    obtain ⟨k₀, hk₀M, hconj⟩ := hP.exists_mem_conj hP'
    have hxP' : x ∈ P' := hYP' (Subgroup.mem_zpowers x)
    have hxP : k₀⁻¹ * x * k₀ ∈ P := (hconj x).1 hxP'
    have hzL : k₀⁻¹ * x * k₀ ∈ L₁ ⊔ L₂ := hPL hxP
    have hk₀norm : k₀ ∈ normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := hMN hk₀M
    have hthis := (Subgroup.mem_normalizer_iff.1 hk₀norm (k₀⁻¹ * x * k₀)).1 hzL
    have hx_eq : x = k₀ * (k₀⁻¹ * x * k₀) * k₀⁻¹ := by group
    rw [hx_eq]
    exact hthis
  have hL₁ : L₁ ≤ Opp 3 D.M := by
    rw [← opp_three_eq_self_of_isL3 h.mem₁ h.shape₁]
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.closure_mono
      (fun x hx => ⟨CFSG.Quasithin.A3.subnormal_le h.mem₁.1 hx.1, hx.2⟩)
  have hL₂ : L₂ ≤ Opp 3 D.M := by
    rw [← opp_three_eq_self_of_isL3 h.mem₂ h.shape₂]
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.closure_mono
      (fun x hx => ⟨CFSG.Quasithin.A3.subnormal_le h.mem₂.1 hx.1, hx.2⟩)
  exact le_antisymm (sup_le hL₁ hL₂) hOppM

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
