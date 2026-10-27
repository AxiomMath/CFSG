module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourTIBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOrestSwap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem false_of_trivial_factor_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A F : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hAM : ¬ A ≤ pCoreOf 2 D.M)
    (hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T))
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ 2)
    (hF : F = L ∨ F = K) (hFA : ⁅F, A⁆ ≤ pCoreOf 2 F) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZ := inf_centerOf_wClos_LKT_ne_bot_19 D hSg h hm hN2 hA hAM hAQ hq
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hXM : L ⊔ K ⊔ D.T ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hAX : A ≤ L ⊔ K ⊔ D.T := hA.1.trans le_sup_right
  have hFX : F ≤ L ⊔ K ⊔ D.T := by
    rcases hF with rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have h5F : 5 ∣ Nat.card F := by
    rcases hF with rfl | rfl
    · have h1 := h.hyp.hL.2
      rw [h.p_eq] at h1
      exact h1.2
    · exact UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 h5F
  obtain ⟨v, hvA, hvQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have hvx : v * (x : G) * v⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    have h1 : ⁅v, (x : G)⁆ ∈ ⁅A, F⁆ := Subgroup.commutator_mem_commutator hvA x.2
    rw [Subgroup.commutator_comm] at h1
    rw [← commutatorElement_def]
    exact pCoreOf_le_pCoreOf_LKT_19 h hF (hFA h1)
  exact false_of_commutator_mem_pCoreOf_of_orderOf_19 h.hyp.hyp125 hm hsp hXM hA hAM hAX hZ
    hvA hvQ (hFX x.2) (by rw [Subgroup.orderOf_coe]; exact hx5) hvx

theorem pin_one_swap_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hJA : ¬ ⁅L ⊔ K, A⁆ ≤ pCoreOf 2 D.M)
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) = 1)
    (hAL : ¬ A ≤ normalizer (L : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hLc.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hKc.1
  have hXM : L ⊔ K ⊔ D.T ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hAX : A ≤ L ⊔ K ⊔ D.T := hA.1.trans le_sup_right
  have hLX : L ≤ L ⊔ K ⊔ D.T := le_sup_left.trans le_sup_left
  have hKX : K ≤ L ⊔ K ⊔ D.T := le_sup_right.trans le_sup_left
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA
    have hJN : L ⊔ K ≤ normalizer (pCoreOf 2 D.M : Set G) :=
      (sup_le hLM hKM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅L ⊔ K, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  have hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    intro hle
    have h0 : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) = 0 := by
      rw [inf_eq_left.mpr hle, E3.mQuot_self]
    omega
  have hZ := inf_centerOf_wClos_LKT_ne_bot_19 D hSg h hm hN2 hA hAM hAQ (by omega)
  obtain ⟨s, hsA, hsL, hsQ⟩ : ∃ s ∈ A, s ∉ normalizer (L : Set G) ∧
      s ∉ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    obtain ⟨s₀, hs₀A, hs₀L⟩ := SetLike.not_le_iff_exists.mp hAL
    by_cases hs₀Q : s₀ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T)
    · obtain ⟨v, hvA, hvQ⟩ := SetLike.not_le_iff_exists.mp hAQ
      by_cases hvL : v ∈ normalizer (L : Set G)
      · refine ⟨v * s₀, A.mul_mem hvA hs₀A, fun h1 => hs₀L ?_, fun h1 => hvQ ?_⟩
        · have h2 := (normalizer (L : Set G)).mul_mem
            ((normalizer (L : Set G)).inv_mem hvL) h1
          rwa [inv_mul_cancel_left] at h2
        · have h2 := (pCoreOf 2 (L ⊔ K ⊔ D.T)).mul_mem h1
            ((pCoreOf 2 (L ⊔ K ⊔ D.T)).inv_mem hs₀Q)
          rwa [mul_inv_cancel_right] at h2
      · exact ⟨v, hvA, hvL, hvQ⟩
    · exact ⟨s₀, hs₀A, hs₀L, hs₀Q⟩
  have hmap := (map_pair_of_mem_not_normalizer_19 h hA hsA hsL).1
  have hss : s * s = 1 := by
    obtain ⟨-, gA, hAg, -⟩ := hA
    have hAel : IsElemAbelian 2 A :=
      CFSG.Quasithin.B2F.isElemAbelian_mono hAg
        (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
    simpa [pow_two] using hAel.2 s hsA
  have h5L : 5 ∣ Nat.card L := by
    have h1 := h.hyp.hL.2
    rw [h.p_eq] at h1
    exact h1.2
  obtain ⟨⟨y, hyL⟩, hy5⟩ := exists_prime_orderOf_dvd_card' 5 h5L
  rw [Subgroup.orderOf_mk] at hy5
  have hy'K : s * y * s⁻¹ ∈ K := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨y, hyL, by simp⟩
  have hy'N : s * y * s⁻¹ ∈ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne hy'K
  have hxX : y * (s * y * s⁻¹) ∈ L ⊔ K ⊔ D.T := (L ⊔ K ⊔ D.T).mul_mem (hLX hyL) (hKX hy'K)
  have hcomm : (s * y * s⁻¹) * y * (s * y * s⁻¹)⁻¹ * y⁻¹ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    have h1 := (calC_commutator_le_of_ne hKc hLc hne.symm
      (Subgroup.commutator_mem_commutator hy'K hyL)).1
    rw [commutatorElement_def] at h1
    exact pCoreOf_le_pCoreOf_LKT_19 h (Or.inr rfl) h1
  have hsx : s * (y * (s * y * s⁻¹)) * s⁻¹ * (y * (s * y * s⁻¹))⁻¹ ∈
      pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    have heq : s * (y * (s * y * s⁻¹)) * s⁻¹ * (y * (s * y * s⁻¹))⁻¹ =
        (s * y * s⁻¹) * y * (s * y * s⁻¹)⁻¹ * y⁻¹ := by
      calc s * (y * (s * y * s⁻¹)) * s⁻¹ * (y * (s * y * s⁻¹))⁻¹
          = (s * y * s⁻¹) * ((s * s) * y * (s * s)⁻¹) * (s * y * s⁻¹)⁻¹ * y⁻¹ := by group
        _ = (s * y * s⁻¹) * y * (s * y * s⁻¹)⁻¹ * y⁻¹ := by rw [hss]; group
    rw [heq]
    exact hcomm
  have hLalt : IsAlt (Bar2 L) 5 := isAlt_bar2_left_19 h hLn
  have hxQ : y * (s * y * s⁻¹) ∉ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    intro hxQ
    have hxN : y * (s * y * s⁻¹) ∈ normalizer (L : Set G) :=
      (normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hyL) hy'N
    have h1 : UC6S846.rhoL L ⟨_, hxN⟩ = 1 := UC6S846.rhoL_eq_one_of_mem_pCoreOf hLX hxN hxQ
    have h2 : UC6S846.rhoL L ⟨_, hy'N⟩ = 1 :=
      UC22.R8107Out.rhoL_eq_one_of_mem hLc hKc hne hy'K hy'N
    have hsplit : (⟨y * (s * y * s⁻¹), hxN⟩ : ↥(normalizer (L : Set G))) =
        ⟨y, Subgroup.le_normalizer hyL⟩ * ⟨s * y * s⁻¹, hy'N⟩ := rfl
    rw [hsplit, map_mul, h2, mul_one] at h1
    have hyO : y ∈ pCoreOf 2 L := UC22.F09.mem_pCoreOf_of_rhoL_eq_one hLalt hyL h1
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨y, hyO⟩
    rw [Subgroup.orderOf_mk, hy5] at hi
    have h2 : 2 ∣ 5 := by
      rcases i with _ | i
      · norm_num at hi
      · exact ⟨2 ^ i, by rw [hi, pow_succ, mul_comm]⟩
    omega
  have hx5 : (y * (s * y * s⁻¹)) ^ 5 ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    have hQX : pCoreOf 2 (L ⊔ K ⊔ D.T) ≤ L ⊔ K ⊔ D.T :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hXQ : L ⊔ K ⊔ D.T ≤ normalizer (pCoreOf 2 (L ⊔ K ⊔ D.T) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have : ((pCoreOf 2 (L ⊔ K ⊔ D.T)).subgroupOf (L ⊔ K ⊔ D.T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
    let π : ↥(L ⊔ K ⊔ D.T) →* ↥(L ⊔ K ⊔ D.T) ⧸
        (pCoreOf 2 (L ⊔ K ⊔ D.T)).subgroupOf (L ⊔ K ⊔ D.T) := QuotientGroup.mk' _
    have hπ1 : ∀ a : ↥(L ⊔ K ⊔ D.T), π a = 1 ↔ (a : G) ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
      intro a
      simp only [π, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hπeq : ∀ a b : ↥(L ⊔ K ⊔ D.T),
        π a = π b ↔ (a : G)⁻¹ * b ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
      intro a b
      simp only [π, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv]
    let yX : ↥(L ⊔ K ⊔ D.T) := ⟨y, hLX hyL⟩
    let y'X : ↥(L ⊔ K ⊔ D.T) := ⟨s * y * s⁻¹, hKX hy'K⟩
    have hc : π yX * π y'X = π y'X * π yX := by
      rw [← map_mul, ← map_mul, hπeq]
      show (y * (s * y * s⁻¹))⁻¹ * ((s * y * s⁻¹) * y) ∈ pCoreOf 2 (L ⊔ K ⊔ D.T)
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (hXQ ((L ⊔ K ⊔ D.T).inv_mem hxX)) _).mp hcomm
      rwa [show (y * (s * y * s⁻¹))⁻¹ * ((s * y * s⁻¹) * y * (s * y * s⁻¹)⁻¹ * y⁻¹) *
          (y * (s * y * s⁻¹))⁻¹⁻¹ = (y * (s * y * s⁻¹))⁻¹ * ((s * y * s⁻¹) * y) by group] at h1
    have hy1 : yX ^ 5 = 1 := Subtype.ext (by simp [yX, ← hy5, pow_orderOf_eq_one])
    have hy'1 : y'X ^ 5 = 1 := by
      apply Subtype.ext
      have : (s * y * s⁻¹) ^ 5 = s * y ^ 5 * s⁻¹ := conj_pow
      simp [y'X, this, ← hy5, pow_orderOf_eq_one]
    have hπx : π (yX * y'X) ^ 5 = 1 := by
      rw [map_mul, (Commute.mul_pow hc 5), ← map_pow, ← map_pow, hy1, hy'1, map_one, mul_one]
    rw [← map_pow, hπ1] at hπx
    simpa [yX, y'X] using hπx
  exact false_of_commutator_mem_pCoreOf_19 h.hyp.hyp125 hm hsp hXM hA hAM hAX hZ hsA hsQ hxX
    hxQ hx5 hsx

theorem pin_one_single_twoSided_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLN : (L.subgroupOf D.M).Normal)
    (hLalt : IsAlt (Bar2 L) 5)
    (hqL : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) = 1)
    (hqK : E3.mQuot A (A ⊓ pCoreOf 2 (K ⊔ D.T)) = 1)
    (hLA : ¬ ⁅L, A⁆ ≤ pCoreOf 2 L) (hKA : ¬ ⁅K, A⁆ ≤ pCoreOf 2 K) : False := by
  have hAT : A ≤ D.T := hA.1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hKN : (K.subgroupOf D.M).Normal := normal_right_of_normal_left_19 h hLN
  have hTL : D.T ≤ normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
  have hTK : D.T ≤ normalizer (K : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKN)
  have hAL : A ≤ normalizer (L : Set G) := hAT.trans hTL
  have hAK : A ≤ normalizer (K : Set G) := hAT.trans hTK
  have hLX : L ≤ L ⊔ K ⊔ D.T := le_sup_left.trans le_sup_left
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hLA
    have h1 : ⁅L, A⁆ ≤ L := CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hAL
    have h2 : ⁅L, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer
        (hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
    exact (le_inf h1 ((Subgroup.commutator_mono le_rfl hle).trans h2)).trans
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLM)
  have hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    intro hle
    apply hLA
    have h1 : ⁅L, A⁆ ≤ L := CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hAL
    have h2 : ⁅L, pCoreOf 2 (L ⊔ K ⊔ D.T)⁆ ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer
        (hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ K ⊔ D.T)))
    exact (le_inf h1 ((Subgroup.commutator_mono le_rfl hle).trans h2)).trans
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLX)
  have hq2 : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ 2 := by
    have := mQuot_LKT_le_add_19 h hLN hAT
    omega
  have hZ := inf_centerOf_wClos_LKT_ne_bot_19 D hSg h hm hN2 hA hAM hAQ hq2
  obtain ⟨d, hdL, hdK⟩ := exists_twoSided_19 hAL hAK hLalt h.hKshape hLA hKA
  exact false_of_twoSided_mem_of_isAlt_19 h hm hA hLalt hZ d.2 (hAL d.2) (hAK d.2) hdL hdK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
