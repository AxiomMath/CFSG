module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.PCore.InfPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_commutator {N X : Subgroup G} {x : G} (hxN : x ∈ normalizer (N : Set G))
    (hxX : x ∈ normalizer (X : Set G)) {k : G} (hk : k ∈ ⁅N, X⁆) : x * k * x⁻¹ ∈ ⁅N, X⁆ := by
  rw [Subgroup.commutator_def] at hk ⊢
  induction hk using Subgroup.closure_induction with
  | mem k hk =>
    obtain ⟨n, hn, y, hy, rfl⟩ := hk
    refine Subgroup.subset_closure ⟨x * n * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN n).1 hn,
      x * y * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxX y).1 hy, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simpa using Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

theorem comm_le_pCoreOf_of_normalizes {L X N : Subgroup G} (hXL : X ≤ L)
    (hLX : L = X ⊔ pCoreOf 2 L) (hs : IsSimpleGroup (Bar2 L)) (h3 : 3 ∣ Nat.card (Bar2 L))
    (hNL : N ≤ normalizer (L : Set G)) (hXN : X ≤ normalizer (N : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) : ⁅N, X⁆ ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : ⁅N, X⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro n hn x hx
    have h1 : n * x * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hNL hn) x).1 (hXL hx)
    have : ⁅n, x⁆ = (n * x * n⁻¹) * x⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact L.mul_mem h1 (L.inv_mem (hXL hx))
  have hKN : ⁅N, X⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro n hn x hx
    have h1 : x * n⁻¹ * x⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (hXN hx) n⁻¹).1 (N.inv_mem hn)
    have : ⁅n, x⁆ = n * (x * n⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact N.mul_mem hn h1
  set ψ : ↥(⁅N, X⁆ : Subgroup G) →* Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hKL) with hψ
  have hsurj := surjective_mk_inclusion_of_sup hXL hLX
  haveI hnorm : ψ.range.Normal := by
    refine ⟨fun s hs b => ?_⟩
    obtain ⟨k, rfl⟩ := hs
    obtain ⟨x, rfl⟩ := hsurj b
    refine ⟨⟨(x : G) * (k : G) * (x : G)⁻¹, ?_⟩, ?_⟩
    · exact conj_mem_commutator (hXN x.2) (Subgroup.le_normalizer x.2) k.2
    · rw [hψ]
      simp only [MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.range with hbot | htop
  · intro k hk
    have h1 : ψ ⟨k, hk⟩ = 1 := by
      have : ψ ⟨k, hk⟩ ∈ ψ.range := ⟨⟨k, hk⟩, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have h2 : (⟨k, hKL hk⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    exact (CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff _).1 h2
  · exfalso
    have hψs : Function.Surjective ψ := MonoidHom.range_eq_top.1 htop
    exact hN3 (h3.trans ((Subgroup.card_dvd_of_surjective hψs).trans
      (Subgroup.card_dvd_of_le hKN)))

theorem eq_one_of_commute_threePow {B : Type*} [Group B] {u v : B} (huv : Commute u v) {k : ℕ}
    (hu : u ^ 3 ^ k = 1) (hv : v ^ 3 ^ k = 1) (h : ¬ 3 ∣ orderOf (u * v)) : u * v = 1 := by
  have h1 : (u * v) ^ 3 ^ k = 1 := by rw [huv.mul_pow, hu, hv, one_mul]
  have h2 : orderOf (u * v) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime_pow Nat.prime_three).1 h2 with ⟨j, -, hj⟩
  rcases j with _ | j
  · exact orderOf_eq_one_iff.1 (by simpa using hj)
  · exact absurd (hj ▸ dvd_pow_self 3 (Nat.succ_ne_zero j)) h

theorem comm_mem_pCoreOf_of_not_normalizes {D : Data G} {L A : Subgroup G} (hL : L ∈ calC D.M)
    (hAM : A ≤ D.M) (hA3 : ¬ 3 ∣ Nat.card A) {a d : G} (ha : a ∈ A) (hdA : d ∈ normalizer (A : Set G))
    (hdL : d ∈ L) (haL : a ∉ normalizer (L : Set G)) {k : ℕ} (hdk : orderOf d = 3 ^ k) :
    ⁅a, d⁆ ∈ pCoreOf 2 D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := hL.1.le
  have hL' : uniqueFourConj a⁻¹ L ∈ calC D.M :=
    uc22p22u_calC_conj (Subgroup.le_normalizer) hL (D.M.inv_mem (hAM ha))
  have hne : uniqueFourConj a⁻¹ L ≠ L := by
    intro h
    apply haL
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [uniqueFourConj] using h
  have hu : a * d * a⁻¹ ∈ uniqueFourConj a⁻¹ L :=
    Subgroup.mem_map.2 ⟨d, hdL, by simp [MulAut.conj_apply]⟩
  have hcomm := PartTwo.commutator_mem_pCoreOf_of_ne hL' hL hne hu (L.inv_mem hdL)
  set π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) with hπ
  set a' : ↥D.M := ⟨a, hAM ha⟩ with ha'
  set d' : ↥D.M := ⟨d, hLM hdL⟩ with hd'
  have hd3 : d' ^ 3 ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hd', ← hdk]
    exact pow_orderOf_eq_one d
  have hc : Commute (π (a' * d' * a'⁻¹)) (π d'⁻¹) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff]
    simpa [ha', hd', commutatorElement_def] using hcomm
  have hwA : ⁅a, d⁆ ∈ A := by
    have h1 : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [h1]
    exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 hdA a⁻¹).1 (A.inv_mem ha))
  set w' : ↥D.M := ⟨⁅a, d⁆, hAM hwA⟩ with hw'
  have hw : w' = a' * d' * a'⁻¹ * d'⁻¹ := by
    apply Subtype.ext
    simp [hw', ha', hd', commutatorElement_def]
  have hord : ¬ 3 ∣ orderOf (π (a' * d' * a'⁻¹) * π d'⁻¹) := by
    intro h3
    rw [← map_mul, ← hw] at h3
    have h4 : orderOf w' = orderOf (⟨⁅a, d⁆, hwA⟩ : ↥A) := by
      rw [← Subgroup.orderOf_coe w', ← Subgroup.orderOf_coe (⟨⁅a, d⁆, hwA⟩ : ↥A)]
    exact hA3 ((h3.trans ((orderOf_map_dvd π w').trans (dvd_of_eq h4))).trans
      (orderOf_dvd_natCard _))
  have h1 := eq_one_of_commute_threePow hc (k := k) (by
    rw [← map_pow, conj_pow, hd3]; simp) (by
    rw [← map_pow, inv_pow, hd3]; simp) hord
  rw [← map_mul, ← hw, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff] at h1
  exact h1

theorem commutator_mem_of_three_elements {X A B : Subgroup G} (hXB : X ≤ normalizer (B : Set G))
    (h : ∀ d ∈ X, (∃ k : ℕ, orderOf d = 3 ^ k) → ∀ a ∈ A, ⁅a, d⁆ ∈ B) :
    ∀ x ∈ Opp 3 X, ∀ a ∈ A, ⁅a, x⁆ ∈ B := by
  intro x hx
  have key : x ∈ X ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ B := by
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact ⟨hx.1, h x hx.1 hx.2⟩
    | one => exact ⟨X.one_mem, fun a _ => by simpa using B.one_mem⟩
    | mul x y _ _ hx hy =>
      refine ⟨X.mul_mem hx.1 hy.1, fun a ha => ?_⟩
      have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact B.mul_mem (hx.2 a ha) ((Subgroup.mem_normalizer_iff.1 (hXB hx.1) _).1 (hy.2 a ha))
    | inv x _ hx =>
      refine ⟨X.inv_mem hx.1, fun a ha => ?_⟩
      have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hXB (X.inv_mem hx.1)) _).1 (B.inv_mem (hx.2 a ha))
  exact key.2

theorem comm_le_inf_pCoreOf {D : Data G} {L X A : Subgroup G} (hL : L ∈ calC D.M) (hXL : X ≤ L)
    (hX3 : Opp 3 X = X) (hLX : L = X ⊔ pCoreOf 2 L) (hs : IsSimpleGroup (Bar2 L))
    (h3 : 3 ∣ Nat.card (Bar2 L)) (hAM : A ≤ D.M) (hA3 : ¬ 3 ∣ Nat.card A)
    (hXA : X ≤ normalizer (A : Set G)) : ⁅A, X⁆ ≤ A ⊓ pCoreOf 2 D.M := by
  have hLM : L ≤ D.M := hL.1.le
  have hXB : X ≤ normalizer ((A ⊓ pCoreOf 2 D.M : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXA hx,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M (hLM (hXL hx))⟩
  have hXN : X ≤ normalizer ((A ⊓ normalizer (L : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXA hx,
      Subgroup.le_normalizer (Subgroup.le_normalizer (hXL hx))⟩
  have hO : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
    CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hL.1
  have key : ∀ d ∈ X, (∃ k : ℕ, orderOf d = 3 ^ k) → ∀ a ∈ A, ⁅a, d⁆ ∈ A ⊓ pCoreOf 2 D.M := by
    intro d hd ⟨k, hk⟩ a ha
    have hdA : ⁅a, d⁆ ∈ A := by
      have h1 : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [h1]
      exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hXA hd) a⁻¹).1 (A.inv_mem ha))
    refine ⟨hdA, ?_⟩
    by_cases haL : a ∈ normalizer (L : Set G)
    · have hmem : ⁅a, d⁆ ∈ ⁅A ⊓ normalizer (L : Set G), X⁆ :=
        Subgroup.commutator_mem_commutator ⟨ha, haL⟩ hd
      exact hO (comm_le_pCoreOf_of_normalizes hXL hLX hs h3 inf_le_right hXN
        (fun h => hA3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))) hmem)
    · exact comm_mem_pCoreOf_of_not_normalizes hL hAM hA3 ha (hXA hd) (hXL hd) haL hk
  rw [Subgroup.commutator_le]
  intro a ha x hx
  exact commutator_mem_of_three_elements hXB key x (by rw [hX3]; exact hx) a ha

theorem comm_le_pCoreOf {D : Data G} {L X A : Subgroup G} (hL : L ∈ calC D.M) (hXL : X ≤ L)
    (hX3 : Opp 3 X = X) (hLX : L = X ⊔ pCoreOf 2 L) (hs : IsSimpleGroup (Bar2 L))
    (h3 : 3 ∣ Nat.card (Bar2 L)) (hAM : A ≤ D.M) (hA3 : ¬ 3 ∣ Nat.card A)
    (hXA : X ≤ normalizer (A : Set G)) : ⁅A, X⁆ ≤ pCoreOf 2 A :=
  (comm_le_inf_pCoreOf hL hXL hX3 hLX hs h3 hAM hA3 hXA).trans
    (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hAM)

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem isSimpleGroup_bar2_L (S : Slice D L D₃ Y H q) : IsSimpleGroup (Bar2 L) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) S.shape_L

theorem three_dvd_card_bar2_L (S : Slice D L D₃ Y H q) : 3 ∣ Nat.card (Bar2 L) := by
  obtain ⟨e⟩ := S.nonempty_bar2_L_equiv
  rw [Nat.card_congr e.toEquiv]
  exact S.three_dvd_card_bar2

theorem comm_le_pCoreOf (S : Slice D L D₃ Y H q) {A : Subgroup G}
    (hA : A ∈ F09.Inv9' D.M (Opp 3 Y) 3) : ⁅A, Opp 3 Y⁆ ≤ pCoreOf 2 A :=
  PartOne.Section9.comm_le_pCoreOf S.L_mem S.opp_le_L (opp_opp 3 Y) S.L_eq_opp_sup
    S.isSimpleGroup_bar2_L S.three_dvd_card_bar2_L hA.1 hA.2.1 hA.2.2

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
