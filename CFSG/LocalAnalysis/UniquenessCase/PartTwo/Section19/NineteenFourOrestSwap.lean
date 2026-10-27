module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPinSwap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPFiveTau
import CFSG.GroupTheory.SupZpowersIndexTwo
import CFSG.Quasithin.Background.E6TwentyA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mQuot_le_two_of_swap_normalizes_19 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hAL : A ≤ normalizer (L : Set G))
    (hτ : ¬ E1.tauOf (L ⊔ K ⊔ D.T) D.T A ≤ normalizer (L : Set G)) :
    E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ 2 := by
  classical
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let S : Subgroup G := D.T ⊓ normalizer (L : Set G)
  change E3.mQuot A (A ⊓ Q) ≤ 2
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hLalt : IsAlt (Bar2 L) 5 := isAlt_bar2_left_19 h hLn
  have hAK : A ≤ normalizer (K : Set G) := fun a ha =>
    mem_normalizer_right_19 h (hAM ha) (hAL ha) h.hne.symm
  obtain ⟨t, htτ, htNL⟩ := SetLike.not_le_iff_exists.mp hτ
  have htT : t ∈ D.T := E1.tauOf_le X D.T A htτ
  have htsd : ∀ a ∈ A, ⁅t, a⁆ ∈ Q := (E1.mem_tauOf.mp htτ).2.2
  have hker : ∀ a (ha : a ∈ A), UC6S846.rhoL L ⟨a, hAL ha⟩ = 1 ↔ a ∈ Q := by
    intro a ha
    constructor
    · intro hρ
      exact mem_pCoreOf_of_rhoL_eq_one_of_swap_19 h htT htNL (hAT ha) (hAL ha) (hAK ha)
        (htsd a ha) (Or.inl hρ)
    · intro haQ
      exact UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := X)
        (le_sup_left.trans le_sup_left) (hAL ha) haQ
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hSN : S ≤ normalizer (L : Set G) := inf_le_right
  have hAFS : A ≤ L ⊔ S := fun a ha =>
    Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hAT ha, hAL ha⟩)
  have hm := mQuot_inf_pCoreOf_sup_le_two_19 hLalt hS2 hSN hAel hAc hAFS
  have hFS : L ⊔ S ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSN
  have hkerSub : ((UC6S846.rhoL L).comp (Subgroup.inclusion hFS)).ker =
      (pCoreOf 2 (L ⊔ S)).subgroupOf (L ⊔ S) :=
    ker_rhoL_sup_eq_pCoreOf rfl hLalt hS2 hFS
  have heq : A ⊓ Q = A ⊓ pCoreOf 2 (L ⊔ S) := by
    refine le_antisymm ?_ ?_
    · rintro a ⟨haA, haQ⟩
      have hρ : UC6S846.rhoL L ⟨a, hAL haA⟩ = 1 := (hker a haA).mpr haQ
      have hmem : (⟨a, hAFS haA⟩ : ↥(L ⊔ S)) ∈
          ((UC6S846.rhoL L).comp (Subgroup.inclusion hFS)).ker := hρ
      rw [hkerSub] at hmem
      exact Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_subgroupOf.mp hmem⟩
    · rintro a ⟨haA, haO⟩
      have hρ : UC6S846.rhoL L ⟨a, hAL haA⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := L ⊔ S) le_sup_left
          (hAL haA) haO
      exact Subgroup.mem_inf.mpr ⟨haA, (hker a haA).mp hρ⟩
  rw [heq]
  exact hm

theorem mQuot_inf_normalizer_le_two_of_swap_19 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    {s : G} (hsA : s ∈ A) (hsL : s ∉ normalizer (L : Set G)) :
    E3.mQuot (A ⊓ normalizer (L : Set G))
      ((A ⊓ normalizer (L : Set G)) ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ 2 := by
  classical
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let NL : Subgroup G := normalizer (L : Set G)
  let A₀ : Subgroup G := A ⊓ NL
  let S : Subgroup G := D.T ⊓ NL
  change E3.mQuot A₀ (A₀ ⊓ Q) ≤ 2
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have : IsMulCommutative A := hAel.1
  have hA0el : IsElemAbelian 2 A₀ :=
    CFSG.Quasithin.B2F.isElemAbelian_mono (inf_le_left.trans hAg)
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hA0c : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, (mem_inf.mp ha).1⟩ : A)
      (⟨b, (mem_inf.mp hb).1⟩ : A))
  have hA0T : A₀ ≤ D.T := inf_le_left.trans hAT
  have hA0L : A₀ ≤ NL := inf_le_right
  have hA0M : A₀ ≤ D.M := hA0T.trans D.sylowM.le
  have hA0K : A₀ ≤ normalizer (K : Set G) := fun a ha =>
    mem_normalizer_right_19 h (hA0M ha) (hA0L ha) h.hne.symm
  have hLalt : IsAlt (Bar2 L) 5 := isAlt_bar2_left_19 h hLn
  have hcomm : ∀ a ∈ A₀, ⁅s, a⁆ ∈ Q := by
    intro a ha
    have haA : a ∈ A := (mem_inf.mp ha).1
    have h1 : s * a = a * s :=
      congrArg Subtype.val (mul_comm' (⟨s, hsA⟩ : A) (⟨a, haA⟩ : A))
    have h2 : ⁅s, a⁆ = 1 := by rw [commutatorElement_def, h1]; group
    rw [h2]
    exact (pCoreOf 2 X).one_mem
  have hker : ∀ a (ha : a ∈ A₀), UC6S846.rhoL L ⟨a, hA0L ha⟩ = 1 ↔ a ∈ Q := by
    intro a ha
    constructor
    · intro hρ
      exact mem_pCoreOf_of_rhoL_eq_one_of_swap_19 h (hAT hsA) hsL (hA0T ha)
        (hA0L ha) (hA0K ha)
        (hcomm a ha) (Or.inl hρ)
    · intro haQ
      exact UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := X)
        (le_sup_left.trans le_sup_left) (hA0L ha) haQ
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hSN : S ≤ NL := inf_le_right
  have hAFS : A₀ ≤ L ⊔ S := fun a ha => Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
    ⟨hA0T ha, hA0L ha⟩)
  have hm := mQuot_inf_pCoreOf_sup_le_two_19 hLalt hS2 hSN hA0el hA0c hAFS
  have hFS : L ⊔ S ≤ NL := sup_le Subgroup.le_normalizer hSN
  have hkerSub : ((UC6S846.rhoL L).comp (Subgroup.inclusion hFS)).ker =
      (pCoreOf 2 (L ⊔ S)).subgroupOf (L ⊔ S) :=
    ker_rhoL_sup_eq_pCoreOf rfl hLalt hS2 hFS
  have heq : A₀ ⊓ Q = A₀ ⊓ pCoreOf 2 (L ⊔ S) := by
    refine le_antisymm ?_ ?_
    · rintro a ⟨haA, haQ⟩
      have hρ : UC6S846.rhoL L ⟨a, hA0L haA⟩ = 1 := (hker a haA).mpr haQ
      have hmem : (⟨a, hAFS haA⟩ : ↥(L ⊔ S)) ∈
          ((UC6S846.rhoL L).comp (Subgroup.inclusion hFS)).ker := hρ
      rw [hkerSub] at hmem
      exact Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_subgroupOf.mp hmem⟩
    · rintro a ⟨haA, haO⟩
      have hρ : UC6S846.rhoL L ⟨a, hA0L haA⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := L ⊔ S) le_sup_left
          (hA0L haA) haO
      exact Subgroup.mem_inf.mpr ⟨haA, (hker a haA).mp hρ⟩
  rw [heq]
  exact hm

theorem map_pair_of_mem_not_normalizer_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) {w : G} (hwA : w ∈ A)
    (hwL : w ∉ normalizer (L : Set G)) :
    L.map (MulAut.conj w).toMonoidHom = K ∧ K.map (MulAut.conj w).toMonoidHom = L := by
  obtain ⟨hAT, -, -, -⟩ := hA
  rcases permutesPair_of_ctx19_one h w (hAT.trans D.sylowM.le hwA) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hwL
  · exact ⟨h1, h2⟩

theorem eq_sup_zpowers_of_swap_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    {s : G} (hsA : s ∈ A) (hsL : s ∉ normalizer (L : Set G)) :
    A = (A ⊓ normalizer (L : Set G)) ⊔ Subgroup.zpowers s := by
  have hss : s * s = 1 := by
    obtain ⟨-, gA, hAg, -⟩ := hA
    have hAel : IsElemAbelian 2 A :=
      CFSG.Quasithin.B2F.isElemAbelian_mono hAg
        (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
    simpa [pow_two] using hAel.2 s hsA
  have hswapS := map_pair_of_mem_not_normalizer_19 h hA hsA hsL
  refine le_antisymm ?_ ?_
  · intro a ha
    by_cases haL : a ∈ normalizer (L : Set G)
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨ha, haL⟩)
    · have hasN : a * s ∈ normalizer (L : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hswapA := map_pair_of_mem_not_normalizer_19 h hA ha haL
        calc L.map (MulAut.conj (a * s)).toMonoidHom
            = (L.map (MulAut.conj s).toMonoidHom).map
                (MulAut.conj a).toMonoidHom := (Subgroup.map_conj_map_conj L s a).symm
          _ = K.map (MulAut.conj a).toMonoidHom := by rw [hswapS.1]
          _ = L := hswapA.2
      have hasA : a * s ∈ A := A.mul_mem ha hsA
      have hmem : a * s ∈ A ⊓ normalizer (L : Set G) := Subgroup.mem_inf.mpr ⟨hasA, hasN⟩
      have heq : a = (a * s) * s := by rw [mul_assoc, hss, mul_one]
      rw [heq]
      exact Subgroup.mul_mem_sup hmem (Subgroup.mem_zpowers s)
  · refine sup_le inf_le_left ?_
    exact Subgroup.zpowers_le.mpr hsA

theorem mQuot_eq_three_of_swap_19 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    {s : G} (hsA : s ∈ A) (hsL : s ∉ normalizer (L : Set G))
    (hq : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T))) :
    E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) = 3 := by
  classical
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let NL : Subgroup G := normalizer (L : Set G)
  let A₀ : Subgroup G := A ⊓ NL
  change E3.mQuot A (A ⊓ Q) = 3
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have : IsMulCommutative A := hAel.1
  have hA2 : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
  have hA02 : IsPGroup 2 A₀ := hA2.to_le inf_le_left
  have hss : s * s = 1 := by simpa [pow_two] using hAel.2 s hsA
  have hAeq : A = A₀ ⊔ Subgroup.zpowers s :=
    eq_sup_zpowers_of_swap_19 h hAgamma hsA hsL
  have hsA0 : s ∉ A₀ := fun hs => hsL (Subgroup.mem_inf.mp hs).2
  have hcent : ∀ k ∈ A₀, s * k * s⁻¹ = k := by
    intro k hk
    have hkA : k ∈ A := (Subgroup.mem_inf.mp hk).1
    have h1 : s * k = k * s :=
      congrArg Subtype.val (mul_comm' (⟨s, hsA⟩ : A) (⟨k, hkA⟩ : A))
    rw [h1, mul_assoc]
    simp
  have hidx2 : A₀.relIndex A = 2 := by
    have hle : A₀.relIndex (A₀ ⊔ Subgroup.zpowers s) ≤ 2 :=
      CFSG.GroupTheory.relIndex_sup_zpowers_le_two hss fun p hp => by
        rw [hcent p hp]; exact hp
    rw [← hAeq] at hle
    have hne1 : A₀.relIndex A ≠ 1 := by
      intro h1
      exact hsA0 (Subgroup.relIndex_eq_one.mp h1 hsA)
    have hpos : 0 < A₀.relIndex A := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hmultA : A₀.relIndex A * Nat.card ↥A₀ = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A₀) (K := A)
    rw [show A₀ ⊓ A = A₀ from inf_eq_left.mpr inf_le_left] at h
    exact h
  have hcardA : Nat.card ↥A = 2 * Nat.card ↥A₀ := by rw [← hmultA, hidx2]
  have hK0A0 : A₀ ⊓ Q ≤ A₀ := inf_le_left
  have hK0K : A₀ ⊓ Q ≤ A ⊓ Q := by
    refine le_inf ?_ inf_le_right
    exact inf_le_left.trans inf_le_left
  have hK0card : Nat.card ↥(A₀ ⊓ Q) ≤ Nat.card ↥(A ⊓ Q) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hK0K)
      (Subgroup.inclusion_injective hK0K)
  have hmultK : (A ⊓ Q).relIndex A * Nat.card ↥(A ⊓ Q) = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ Q) (K := A)
    rw [show (A ⊓ Q) ⊓ A = A ⊓ Q from inf_eq_left.mpr inf_le_left] at h
    exact h
  have hmultK0 : (A₀ ⊓ Q).relIndex A₀ * Nat.card ↥(A₀ ⊓ Q) = Nat.card ↥A₀ := by
    have h := Subgroup.relIndex_mul_card (H := A₀ ⊓ Q) (K := A₀)
    rw [show (A₀ ⊓ Q) ⊓ A₀ = A₀ ⊓ Q from inf_eq_left.mpr hK0A0] at h
    exact h
  have hle : (A ⊓ Q).relIndex A ≤ 2 * (A₀ ⊓ Q).relIndex A₀ := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.card ↥(A ⊓ Q)) _ Nat.card_pos
    calc (A ⊓ Q).relIndex A * Nat.card ↥(A ⊓ Q)
        = Nat.card ↥A := hmultK
      _ = 2 * Nat.card ↥A₀ := hcardA
      _ = 2 * ((A₀ ⊓ Q).relIndex A₀ * Nat.card ↥(A₀ ⊓ Q)) := by rw [hmultK0]
      _ = (2 * (A₀ ⊓ Q).relIndex A₀) * Nat.card ↥(A₀ ⊓ Q) := by ring
      _ ≤ (2 * (A₀ ⊓ Q).relIndex A₀) * Nat.card ↥(A ⊓ Q) :=
          Nat.mul_le_mul_left _ hK0card
  have hpow : 2 ^ E3.mQuot A (A ⊓ Q) ≤ 2 ^ (E3.mQuot A₀ (A₀ ⊓ Q) + 1) := by
    have h1 : (A ⊓ Q).relIndex A = 2 ^ E3.mQuot A (A ⊓ Q) :=
      E3.relIndex_eq_two_pow hA2 _
    have h2 : (A₀ ⊓ Q).relIndex A₀ = 2 ^ E3.mQuot A₀ (A₀ ⊓ Q) :=
      E3.relIndex_eq_two_pow hA02 _
    rw [h1, h2] at hle
    calc 2 ^ E3.mQuot A (A ⊓ Q) ≤ 2 * 2 ^ E3.mQuot A₀ (A₀ ⊓ Q) := hle
      _ = 2 ^ (E3.mQuot A₀ (A₀ ⊓ Q) + 1) := by rw [pow_succ]; ring
  have hmle : E3.mQuot A (A ⊓ Q) ≤ E3.mQuot A₀ (A₀ ⊓ Q) + 1 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hq' : 2 < E3.mQuot A (A ⊓ Q) := hq
  have hr0 : E3.mQuot A₀ (A₀ ⊓ Q) ≤ 2 :=
    mQuot_inf_normalizer_le_two_of_swap_19 D h hAgamma hLn hsA hsL
  omega

theorem not_mem_pCoreOf_of_swap_19 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    {s : G} (hsA : s ∈ A) (hsL : s ∉ normalizer (L : Set G))
    (hq : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T))) :
    s ∉ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
  classical
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let NL : Subgroup G := normalizer (L : Set G)
  let A₀ : Subgroup G := A ⊓ NL
  change s ∉ Q
  intro hsQ
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have : IsMulCommutative A := hAel.1
  have hA2 : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
  have hA02 : IsPGroup 2 A₀ := hA2.to_le inf_le_left
  have hss : s * s = 1 := by simpa [pow_two] using hAel.2 s hsA
  have hAeq : A = A₀ ⊔ Subgroup.zpowers s :=
    eq_sup_zpowers_of_swap_19 h hAgamma hsA hsL
  have hsA0 : s ∉ A₀ := fun hs => hsL (Subgroup.mem_inf.mp hs).2
  have hcent : ∀ k ∈ A₀, s * k * s⁻¹ = k := by
    intro k hk
    have hkA : k ∈ A := (Subgroup.mem_inf.mp hk).1
    have h1 : s * k = k * s :=
      congrArg Subtype.val (mul_comm' (⟨s, hsA⟩ : A) (⟨k, hkA⟩ : A))
    rw [h1, mul_assoc]
    simp
  have hidx2 : A₀.relIndex A = 2 := by
    have hle : A₀.relIndex (A₀ ⊔ Subgroup.zpowers s) ≤ 2 :=
      CFSG.GroupTheory.relIndex_sup_zpowers_le_two hss fun p hp => by
        rw [hcent p hp]; exact hp
    rw [← hAeq] at hle
    have hne1 : A₀.relIndex A ≠ 1 := by
      intro h1
      exact hsA0 (Subgroup.relIndex_eq_one.mp h1 hsA)
    have hpos : 0 < A₀.relIndex A := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hcardA : Nat.card ↥A = 2 * Nat.card ↥A₀ := by
    have h := Subgroup.relIndex_mul_card (H := A₀) (K := A)
    rw [show A₀ ⊓ A = A₀ from inf_eq_left.mpr inf_le_left] at h
    rw [← h, hidx2]
  have hsK : s ∈ A ⊓ Q := Subgroup.mem_inf.mpr ⟨hsA, hsQ⟩
  have hKsup : A ⊓ Q = (A ⊓ Q ⊓ A₀) ⊔ Subgroup.zpowers s := by
    refine le_antisymm ?_ ?_
    · intro k hk
      have hkA : k ∈ A := (Subgroup.mem_inf.mp hk).1
      by_cases hkN : k ∈ NL
      · refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hk, Subgroup.mem_inf.mpr
          ⟨hkA, hkN⟩⟩)
      · have hksN : k * s ∈ NL := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          have hkk := map_pair_of_mem_not_normalizer_19 h hAgamma hkA hkN
          have hss' := map_pair_of_mem_not_normalizer_19 h hAgamma hsA hsL
          calc L.map (MulAut.conj (k * s)).toMonoidHom
              = (L.map (MulAut.conj s).toMonoidHom).map
                  (MulAut.conj k).toMonoidHom := (Subgroup.map_conj_map_conj L s k).symm
            _ = K.map (MulAut.conj k).toMonoidHom := by rw [hss'.1]
            _ = L := hkk.2
        have hksA : k * s ∈ A := A.mul_mem hkA hsA
        have hksQ : k * s ∈ Q := Q.mul_mem (Subgroup.mem_inf.mp hk).2 hsQ
        have hksA0 : k * s ∈ A₀ := Subgroup.mem_inf.mpr ⟨hksA, hksN⟩
        have hmem : k * s ∈ A ⊓ Q ⊓ A₀ :=
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hksA, hksQ⟩, hksA0⟩
        have heq : k = (k * s) * s := by rw [mul_assoc, hss, mul_one]
        rw [heq]
        exact Subgroup.mul_mem_sup hmem (Subgroup.mem_zpowers s)
    · refine sup_le inf_le_left ?_
      exact Subgroup.zpowers_le.mpr hsK
  have hsKinf : s ∉ A ⊓ Q ⊓ A₀ := fun hs => hsA0 (Subgroup.mem_inf.mp hs).2
  have hcentK : ∀ k ∈ A ⊓ Q ⊓ A₀, s * k * s⁻¹ = k := by
    intro k hk
    exact hcent k (Subgroup.mem_inf.mp hk).2
  have hidxK : (A ⊓ Q ⊓ A₀).relIndex (A ⊓ Q) = 2 := by
    have hle : (A ⊓ Q ⊓ A₀).relIndex ((A ⊓ Q ⊓ A₀) ⊔ Subgroup.zpowers s) ≤ 2 :=
      CFSG.GroupTheory.relIndex_sup_zpowers_le_two hss fun p hp => by
        rw [hcentK p hp]; exact hp
    rw [← hKsup] at hle
    have hne1 : (A ⊓ Q ⊓ A₀).relIndex (A ⊓ Q) ≠ 1 := by
      intro h1
      apply hsKinf
      exact Subgroup.relIndex_eq_one.mp h1 hsK
    have hpos : 0 < (A ⊓ Q ⊓ A₀).relIndex (A ⊓ Q) :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hKcard : Nat.card ↥(A ⊓ Q) = 2 * Nat.card ↥(A ⊓ Q ⊓ A₀) := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ Q ⊓ A₀) (K := A ⊓ Q)
    rw [show (A ⊓ Q ⊓ A₀) ⊓ (A ⊓ Q) = A ⊓ Q ⊓ A₀ from
      inf_eq_left.mpr inf_le_left] at h
    rw [← h, hidxK]
  have hmultK : (A ⊓ Q).relIndex A * Nat.card ↥(A ⊓ Q) = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ Q) (K := A)
    rw [show (A ⊓ Q) ⊓ A = A ⊓ Q from inf_eq_left.mpr inf_le_left] at h
    exact h
  have hK0eq : A ⊓ Q ⊓ A₀ = A₀ ⊓ Q := by
    ext x
    constructor
    · rintro ⟨⟨-, hxQ⟩, hxA0⟩
      exact ⟨hxA0, hxQ⟩
    · rintro ⟨hxA0, hxQ⟩
      exact ⟨⟨(Subgroup.mem_inf.mp hxA0).1, hxQ⟩, hxA0⟩
  have hmultK0 : (A₀ ⊓ Q).relIndex A₀ * Nat.card ↥(A₀ ⊓ Q) = Nat.card ↥A₀ := by
    have h := Subgroup.relIndex_mul_card (H := A₀ ⊓ Q) (K := A₀)
    rw [show (A₀ ⊓ Q) ⊓ A₀ = A₀ ⊓ Q from
      inf_eq_left.mpr (inf_le_left : A₀ ⊓ Q ≤ A₀)] at h
    exact h
  have hEq : (A ⊓ Q).relIndex A = (A₀ ⊓ Q).relIndex A₀ := by
    have hcalc : (A ⊓ Q).relIndex A * (2 * Nat.card ↥(A₀ ⊓ Q))
        = (A₀ ⊓ Q).relIndex A₀ * (2 * Nat.card ↥(A₀ ⊓ Q)) := by
      calc (A ⊓ Q).relIndex A * (2 * Nat.card ↥(A₀ ⊓ Q))
          = (A ⊓ Q).relIndex A * Nat.card ↥(A ⊓ Q) := by
            rw [hKcard, hK0eq]
        _ = Nat.card ↥A := hmultK
        _ = 2 * Nat.card ↥A₀ := hcardA
        _ = 2 * ((A₀ ⊓ Q).relIndex A₀ * Nat.card ↥(A₀ ⊓ Q)) := by rw [hmultK0]
        _ = (A₀ ⊓ Q).relIndex A₀ * (2 * Nat.card ↥(A₀ ⊓ Q)) := by ring
    exact Nat.mul_right_cancel
      (Nat.mul_pos (by norm_num) (Nat.card_pos (α := ↥(A₀ ⊓ Q)))) hcalc
  have hKrel : (A ⊓ Q).relIndex A = 2 ^ E3.mQuot A (A ⊓ Q) :=
    E3.relIndex_eq_two_pow hA2 _
  have hK0rel : (A₀ ⊓ Q).relIndex A₀ = 2 ^ E3.mQuot A₀ (A₀ ⊓ Q) :=
    E3.relIndex_eq_two_pow hA02 _
  have hq' : 2 < E3.mQuot A (A ⊓ Q) := hq
  have hr0 : E3.mQuot A₀ (A₀ ⊓ Q) ≤ 2 :=
    mQuot_inf_normalizer_le_two_of_swap_19 D h hAgamma hLn hsA hsL
  rw [hKrel, hK0rel] at hEq
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_of_eq hEq)
  omega

theorem mQuot_inf_sup_zpowers_eq_two_of_swap_19 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    {s : G} (hsA : s ∈ A) (hsL : s ∉ normalizer (L : Set G))
    (hq : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T))) :
    E3.mQuot A (A ⊓ (pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s)) = 2 := by
  classical
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  change E3.mQuot A (A ⊓ (Q ⊔ Subgroup.zpowers s)) = 2
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hsQ : s ∉ Q := not_mem_pCoreOf_of_swap_19 D h hAgamma hLn hsA hsL hq
  have hQN : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hNs : Subgroup.zpowers s ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (hQN (Subgroup.mem_sup_right (hAT hsA)))
  have hset : ((Q ⊔ Subgroup.zpowers s : Subgroup G) : Set G) =
      (Q : Set G) * (Subgroup.zpowers s : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q (Subgroup.zpowers s) hNs
  have hKsup : A ⊓ (Q ⊔ Subgroup.zpowers s) = (A ⊓ Q) ⊔ Subgroup.zpowers s := by
    refine le_antisymm ?_ ?_
    · rintro a ⟨haA, haQ⟩
      have ha' : a ∈ (Q : Set G) * (Subgroup.zpowers s : Set G) := by
        rw [← hset]; exact haQ
      obtain ⟨q, hqQ, k, hk, hqk⟩ := ha'
      have hkA : k ∈ A := (Subgroup.zpowers_le.mpr hsA) hk
      have hqA : q ∈ A := by
        have hq : q = a * k⁻¹ := by rw [← hqk]; group
        rw [hq]
        exact A.mul_mem haA (A.inv_mem hkA)
      have hqK : q ∈ A ⊓ Q := Subgroup.mem_inf.mpr ⟨hqA, hqQ⟩
      rw [← hqk]
      exact Subgroup.mul_mem_sup hqK hk
    · refine sup_le ?_ ?_
      · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
      · exact le_inf (Subgroup.zpowers_le.mpr hsA)
          (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
  have hsK : s ∉ A ⊓ Q := fun hs => hsQ (Subgroup.mem_inf.mp hs).2
  have hone : E3.mQuot ((A ⊓ Q) ⊔ Subgroup.zpowers s) (A ⊓ Q) = 1 :=
    CFSG.Quasithin.E6.mQuot_sup_zpowers hAel inf_le_left hsA hsK
  have hsupA : (A ⊓ Q) ⊔ Subgroup.zpowers s ≤ A :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hsA)
  have hadd := E3.mQuot_add (V := A) (U := A ⊓ Q) (U' := (A ⊓ Q) ⊔ Subgroup.zpowers s)
    le_sup_left hsupA
  have hm : E3.mQuot A (A ⊓ Q) = 3 := mQuot_eq_three_of_swap_19 D h hAgamma hLn hsA hsL hq
  rw [hm, hone] at hadd
  rw [hKsup]
  omega

omit [Finite G] in
theorem mem_tauOf_of_commutator_mem_19 {H : Subgroup G} {s x : G} (hss : s * s = 1)
    (hs1 : s ≠ 1) (hxH : x ∈ H) (hxs : ⁅x, s⁆ ∈ pCoreOf 2 H) :
    x ∈ E1.tauOf H H (Subgroup.zpowers s) := by
  have hsord : orderOf s = 2 := orderOf_eq_prime ((pow_two s).trans hss) hs1
  refine (E1.mem_tauOf_of_le le_rfl).mpr ⟨hxH, fun a ha => ?_⟩
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsord).mp ha with rfl | rfl
  · simp
  · exact hxs

theorem inf_centerOf_wClos_two_ne_bot_of_swap_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hJA : ¬ ⁅L ⊔ K, A⁆ ≤ pCoreOf 2 D.M)
    (hq : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)))
    {s : G} (hsA : s ∈ A) (hsL : s ∉ normalizer (L : Set G)) :
    (A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s)) ≠ ⊥) ∧
      (pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s ≤
        E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s)) ∧
      (E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) ≤
        Subgroup.normalizer
          (((pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s : Subgroup G)) : Set G)) ∧
      (A ≤ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s)) := by
  classical
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let H'' : Subgroup G := E1.tauOf X X (Subgroup.zpowers s)
  let Q'' : Subgroup G := Q ⊔ Subgroup.zpowers s
  change (A ⊓ centerOf (E3.wClos V₀ 2 Q'') ≠ ⊥) ∧ Q'' ≤ H'' ∧
    H'' ≤ Subgroup.normalizer (Q'' : Set G) ∧ A ≤ H''
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, hmq0⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have : IsMulCommutative A := hAel.1
  have hss : s * s = 1 := by simpa [pow_two] using hAel.2 s hsA
  have hs1 : s ≠ 1 := fun h1 => hsL (h1 ▸ Subgroup.one_mem _)
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hXM : X ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hH''X : H'' ≤ X := E1.tauOf_le X X _
  have hHM : H'' ≤ D.M := hH''X.trans hXM
  have hQN : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQH'' : Q ≤ H'' := by
    intro q hq
    have hqX : q ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hq
    have hqs : ⁅q, s⁆ ∈ Q := by
      rw [commutatorElement_def]
      have hsX : s ∈ X := Subgroup.mem_sup_right (hAT hsA)
      have h1 : s * q⁻¹ * s⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQN hsX) q⁻¹).mp (Q.inv_mem hq)
      have h3 : q * (s * q⁻¹ * s⁻¹) ∈ Q := Q.mul_mem hq h1
      simpa [mul_assoc] using h3
    exact mem_tauOf_of_commutator_mem_19 hss hs1 hqX hqs
  have hsH'' : s ∈ H'' := by
    refine mem_tauOf_of_commutator_mem_19 hss hs1 (Subgroup.mem_sup_right (hAT hsA)) ?_
    have h1 : ⁅s, s⁆ = 1 := by rw [commutatorElement_def]; group
    rw [h1]
    exact Q.one_mem
  have hQH : Q'' ≤ H'' := sup_le hQH'' (Subgroup.zpowers_le.mpr hsH'')
  have hHQ : H'' ≤ Subgroup.normalizer (Q'' : Set G) := by
    intro hx hxH''
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxX : hx ∈ X := hH''X hxH''
    have hxQmap : Q.map (MulAut.conj hx).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQN hxX)
    have hxs : ⁅hx, s⁆ ∈ Q := (E1.mem_tauOf.mp hxH'').2.2 s (Subgroup.mem_zpowers s)
    have hconj : hx * s * hx⁻¹ ∈ Q ⊔ Subgroup.zpowers s := by
      have h1 : hx * s * hx⁻¹ = ⁅hx, s⁆ * s := by
        rw [commutatorElement_def]; group
      rw [h1]
      exact Subgroup.mul_mem_sup hxs (Subgroup.mem_zpowers s)
    have hsle : Subgroup.zpowers s ≤ Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹) := by
      refine Subgroup.zpowers_le.mpr ?_
      have h1 : ⁅hx, s⁆⁻¹ ∈ Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹) :=
        Subgroup.mem_sup_left (Q.inv_mem hxs)
      have h2 : hx * s * hx⁻¹ ∈ Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      have h3 : ⁅hx, s⁆⁻¹ * (hx * s * hx⁻¹) ∈
          Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹) :=
        (Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹)).mul_mem h1 h2
      have hprod : ⁅hx, s⁆⁻¹ * (hx * s * hx⁻¹) = s := by
        rw [commutatorElement_def]; group
      rwa [hprod] at h3
    have hmap : Q''.map (MulAut.conj hx).toMonoidHom =
        Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹) := by
      change (Q ⊔ Subgroup.zpowers s).map (MulAut.conj hx).toMonoidHom = _
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hxQmap]
      rfl
    have hEq' : Q ⊔ Subgroup.zpowers (hx * s * hx⁻¹) = Q'' := by
      change _ = Q ⊔ Subgroup.zpowers s
      exact le_antisymm (sup_le le_sup_left (Subgroup.zpowers_le.mpr hconj))
        (sup_le le_sup_left hsle)
    exact hmap.trans hEq'
  have hTsyl : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQn : ((pCoreOf 2 X).subgroupOf X).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  have hQT' : Q ≤ D.T :=
    hTsyl.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hQn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hQT : Q'' ≤ D.T := sup_le hQT' (Subgroup.zpowers_le.mpr (hAT hsA))
  have hAH : A ≤ H'' := by
    intro a ha
    have haX : a ∈ X := Subgroup.mem_sup_right (hAT ha)
    have hcomm : a * s = s * a :=
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨s, hsA⟩ : A))
    have hcommQ : ⁅a, s⁆ ∈ Q := by
      have h1 : ⁅a, s⁆ = 1 := by rw [commutatorElement_def, hcomm]; group
      rw [h1]; exact Q.one_mem
    exact mem_tauOf_of_commutator_mem_19 hss hs1 haX hcommQ
  have hV : IsElemAbelian 2 V₀ := h.hyp.hyp125.pairFacts.elemAbelian₀
  have hAW : A ≤ E3.wClos V₀ 2 D.T :=
    E3.le_wClos_of_mQuot_le (V := V₀) hV gA hAT hAg (k := 2)
      (by rw [hmq0]; norm_num) (lt_trans (by norm_num) hm)
  have hC2 : E3.cClos V₀ 2 D.T ≤ H'' := by
    intro c hc
    have hcT : c ∈ D.T := (Subgroup.mem_inf.mp hc).1
    have hcC : c ∈ Subgroup.centralizer (E3.wClos V₀ 2 D.T : Set G) :=
      (Subgroup.mem_inf.mp hc).2
    have hcX : c ∈ X := Subgroup.mem_sup_right hcT
    have hcommQ : ⁅c, s⁆ ∈ Q := by
      have hcomm : c * s = s * c :=
        ((Subgroup.mem_centralizer_iff.mp hcC) s (hAW hsA)).symm
      have h1 : ⁅c, s⁆ = 1 := by rw [commutatorElement_def, hcomm]; group
      rw [h1]; exact Q.one_mem
    exact mem_tauOf_of_commutator_mem_19 hss hs1 hcX hcommQ
  have hq2 : E3.mQuot A (A ⊓ Q'') = 2 :=
    mQuot_inf_sup_zpowers_eq_two_of_swap_19 D h hAgamma hLn hsA hsL hq
  have hAQ : ¬ A ≤ Q'' := by
    intro hle
    have h0 : E3.mQuot A (A ⊓ Q'') = 0 := by
      rw [inf_eq_left.mpr hle, E3.mQuot_self]
    omega
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA
    have hJN : L ⊔ K ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
      (sup_le hLM hKM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅L ⊔ K, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  have hP5 : ∀ N : Subgroup G, N ≤ H'' → H'' ≤ Subgroup.normalizer (N : Set G) →
      ¬ N ≤ Q'' → 5 ∣ Nat.card N := by
    intro N hNH hHN hNQ
    exact five_dvd_of_normal_tau_19 h hLn (hAT hsA)
      (by simpa [pow_two] using hss) hsL hNH hHN hNQ
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  exact ⟨inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hHM hQH hHQ hQT hAH
    hAgamma hAM hAQ (le_of_eq hq2) hC2 hP5, hQH, hHQ, hAH⟩

theorem exists_rhoL_conj_normalizer_trivial_19 {F A : Subgroup G} (hFalt : IsAlt (Bar2 F) 5)
    (hAel : IsElemAbelian 2 A) :
    ∃ (E : Subgroup (MulAut (Bar2 F))) (x : ↥F),
      E = (A.subgroupOf (normalizer (F : Set G))).map (UC6S846.rhoL F) ∧
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E (UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩) :
          Set (MulAut (Bar2 F))) → e = 1) ∧
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E (UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩)⁻¹ :
          Set (MulAut (Bar2 F))) → e = 1) := by
  classical
  let N : Subgroup G := normalizer (F : Set G)
  let φN : ↥N →* MulAut (Bar2 F) := UC6S846.rhoL F
  let E : Subgroup (MulAut (Bar2 F)) := (A.subgroupOf N).map φN
  have hEel : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_iff.mpr (fun x y => ?_), ?_⟩
    · obtain ⟨a, haA, ha⟩ := x.2
      obtain ⟨b, hbA, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut (Bar2 F)) * (y : MulAut (Bar2 F)) =
        (y : MulAut (Bar2 F)) * (x : MulAut (Bar2 F))
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg φN (Subtype.ext (CFSG.Quasithin.B2F.isElemAbelian_comm hAel
        (Subgroup.mem_subgroupOf.mp haA) (Subgroup.mem_subgroupOf.mp hbA)))
    · rintro x ⟨a, haA, ha⟩
      rw [← ha, ← map_pow, show (a : ↥N) ^ 2 = 1 from
        Subtype.ext (hAel.2 a.1 (Subgroup.mem_subgroupOf.mp haA))]
      exact map_one φN
  obtain ⟨e5⟩ := hFalt
  let ee : MulAut (Bar2 F) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr e5).trans CFSG.Quasithin.L139A5.autA5.symm
  let Ep : Subgroup (Equiv.Perm (Fin 5)) := E.map ee.toMonoidHom
  have hEpel : IsElemAbelian 2 Ep := CFSG.SectionRank.isElemAbelian_map hEel ee.toMonoidHom
  obtain ⟨c, hcalt, hcgood, hcgoodinv⟩ := exists_good_conj_perm5_19 Ep hEpel
    (CFSG.ComponentClassification.RankTwoAltFive.card_le_four_of_elemAbelian_perm hEpel)
  obtain ⟨x, hx⟩ := exists_rhoL_eq_19 e5 ⟨c, hcalt⟩
  let d : MulAut (Bar2 F) := UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩
  have hd : ee d = c := hx
  have key : ∀ (z : MulAut (Bar2 F)) (c' : Equiv.Perm (Fin 5)), ee z = c' →
      (∀ e ∈ Ep, e ∈ Subgroup.normalizer (conjSubgroup Ep c' : Set (Equiv.Perm (Fin 5))) →
        e = 1) →
      ∀ e ∈ E, e ∈ Subgroup.normalizer (conjSubgroup E z : Set (MulAut (Bar2 F))) → e = 1 := by
    intro z c' hz hc' e heE heN
    have hmap : (conjSubgroup E z).map ee.toMonoidHom = conjSubgroup Ep c' := by
      have h := Eq.symm <| map_conjSubgroup_hom ee.toMonoidHom E z
      rwa [show ee.toMonoidHom z = c' from hz] at h
    have hnorm : ee e ∈ Subgroup.normalizer (conjSubgroup Ep c' :
        Set (Equiv.Perm (Fin 5))) := by
      have h1 : ee e ∈ Subgroup.normalizer
          ((conjSubgroup E z).map ee.toMonoidHom : Set (Equiv.Perm (Fin 5))) := by
        rw [← Subgroup.map_equiv_normalizer_eq (conjSubgroup E z) ee]
        exact Subgroup.mem_map_of_mem ee.toMonoidHom heN
      rwa [hmap] at h1
    exact ee.injective ((hc' (ee e) (Subgroup.mem_map_of_mem ee.toMonoidHom heE) hnorm).trans
      (map_one ee).symm)
  exact ⟨E, x, rfl, key d c hd hcgood, key d⁻¹ c⁻¹ (by rw [map_inv, hd]) hcgoodinv⟩

theorem rhoL_eq_one_of_conj_eq_19 {L A : Subgroup G} {E : Subgroup (MulAut (Bar2 L))}
    (hEeq : E = ((A ⊓ normalizer (L : Set G)).subgroupOf (normalizer (L : Set G))).map
      (UC6S846.rhoL L))
    {x y a : G} (hxN : x ∈ normalizer (L : Set G))
    (hyN : y ∈ normalizer (L : Set G))
    (hρy : UC6S846.rhoL L ⟨y, hyN⟩ = UC6S846.rhoL L ⟨x, hxN⟩)
    (hgood : ∀ e ∈ E, e ∈ Subgroup.normalizer
      (conjSubgroup E (UC6S846.rhoL L ⟨x, hxN⟩) :
        Set (MulAut (Bar2 L))) → e = 1)
    (haN : a ∈ normalizer (L : Set G)) (haA0 : a ∈ A ⊓ normalizer (L : Set G))
    (hconj : conjSubgroup (conjSubgroup (A ⊓ normalizer (L : Set G)) y) a =
      conjSubgroup (A ⊓ normalizer (L : Set G)) x) :
    UC6S846.rhoL L ⟨a, haN⟩ = 1 := by
  classical
  let N : Subgroup G := normalizer (L : Set G)
  let A₀ : Subgroup G := A ⊓ N
  change a ∈ A₀ at haA0
  change conjSubgroup (conjSubgroup A₀ y) a = conjSubgroup A₀ x at hconj
  change E = (A₀.subgroupOf N).map (UC6S846.rhoL L) at hEeq
  have hA0N : A₀ ≤ N := inf_le_right
  have hSN : conjSubgroup A₀ y ≤ N := by
    intro z hz
    have hzA : y * z * y⁻¹ ∈ A₀ := mem_conjSubgroup_iff.mp hz
    have h : y⁻¹ * (y * z * y⁻¹) * y ∈ N :=
      N.mul_mem (N.mul_mem (N.inv_mem hyN) (Subgroup.mem_inf.mp hzA).2) hyN
    rwa [show y⁻¹ * (y * z * y⁻¹) * y = z by group] at h
  have hSsub : (conjSubgroup A₀ y).subgroupOf N =
      conjSubgroup (A₀.subgroupOf N) ⟨y, hyN⟩ :=
    subgroupOf_conjSubgroup_hom hyN hA0N
  have hTsub : (conjSubgroup A₀ x).subgroupOf N =
      conjSubgroup (A₀.subgroupOf N) ⟨x, hxN⟩ :=
    subgroupOf_conjSubgroup_hom hxN hA0N
  have hconjN : conjSubgroup ((conjSubgroup A₀ y).subgroupOf N) ⟨a, haN⟩ =
      (conjSubgroup A₀ x).subgroupOf N := by
    rw [← subgroupOf_conjSubgroup_hom haN hSN, hconj, hTsub]
  have hmap := congrArg (Subgroup.map (UC6S846.rhoL L)) hconjN
  rw [← map_conjSubgroup_hom (UC6S846.rhoL L) ((conjSubgroup A₀ y).subgroupOf N)
    ⟨a, haN⟩] at hmap
  have hSmap : ((conjSubgroup A₀ y).subgroupOf N).map (UC6S846.rhoL L) =
      conjSubgroup E (UC6S846.rhoL L ⟨x, hxN⟩) := by
    rw [hSsub]
    have h := Eq.symm <| map_conjSubgroup_hom (UC6S846.rhoL L) (A₀.subgroupOf N) ⟨y, hyN⟩
    rw [← hEeq, hρy] at h
    exact h
  have hTmap : ((conjSubgroup A₀ x).subgroupOf N).map (UC6S846.rhoL L) =
      conjSubgroup E (UC6S846.rhoL L ⟨x, hxN⟩) := by
    rw [hTsub]
    have h := Eq.symm <| map_conjSubgroup_hom (UC6S846.rhoL L) (A₀.subgroupOf N) ⟨x, hxN⟩
    rw [← hEeq] at h
    exact h
  rw [hSmap, hTmap] at hmap
  have hnorm : UC6S846.rhoL L ⟨a, haN⟩ ∈
      Subgroup.normalizer (conjSubgroup E (UC6S846.rhoL L ⟨x, hxN⟩) :
        Set (MulAut (Bar2 L))) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hmap
  have heE : UC6S846.rhoL L ⟨a, haN⟩ ∈ E := by
    rw [hEeq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haA0)
  exact hgood _ heE hnorm

theorem orest_LK_swap_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hJA : ¬ ⁅L ⊔ K, A⁆ ≤ pCoreOf 2 D.M)
    (hq : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)))
    (hτ : ¬ E1.tauOf (L ⊔ K ⊔ D.T) D.T A ≤ normalizer (L : Set G)) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  classical
  by_cases hAL : A ≤ normalizer (L : Set G)
  · have h2 := mQuot_le_two_of_swap_normalizes_19 D h hA hLn hAL hτ
    omega
  obtain ⟨s, hsA, hsL⟩ := SetLike.not_le_iff_exists.mp hAL
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  let N : Subgroup G := normalizer (L : Set G)
  let A₀ : Subgroup G := A ⊓ N
  let H'' : Subgroup G := E1.tauOf X X (Subgroup.zpowers s)
  let Q'' : Subgroup G := Q ⊔ Subgroup.zpowers s
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have : IsMulCommutative A := hAel.1
  have hss : s * s = 1 := by simpa [pow_two] using hAel.2 s hsA
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  obtain ⟨hZ, hQH, hHQ, hAH⟩ :=
    inf_centerOf_wClos_two_ne_bot_of_swap_19 D hSg h hm hN2 hAgamma hLn hJA hq hsA hsL
  have hq2 : E3.mQuot A (A ⊓ (pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s)) = 2 :=
    mQuot_inf_sup_zpowers_eq_two_of_swap_19 D h hAgamma hLn hsA hsL hq
  obtain ⟨E, l, hEeq, hgood, hgoodinv⟩ := exists_rhoL_conj_normalizer_trivial_19
    (isAlt_bar2_left_19 h hLn) (CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left hAel :
      IsElemAbelian 2 (A ⊓ normalizer (L : Set G)))
  have hlL : (l : G) ∈ L := l.2
  have hlN : (l : G) ∈ N := Subgroup.le_normalizer hlL
  have hLmap := map_pair_of_mem_not_normalizer_19 h hAgamma hsA hsL
  have hlsK : s * (l : G) * s⁻¹ ∈ K := by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hlL
    rwa [hLmap.1] at h1
  let x : G := (l : G) * (s * (l : G) * s⁻¹)
  have hxLK : x ∈ L ⊔ K :=
    (L ⊔ K).mul_mem (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlsK)
  have hxX : x ∈ X := Subgroup.mem_sup_left hxLK
  have hlsN : s * (l : G) * s⁻¹ ∈ N :=
    calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm hlsK
  have hxNL : x ∈ N := N.mul_mem hlN hlsN
  have hO2LQ : pCoreOf 2 L ≤ Q := by
    have hKL : K ≤ normalizer (L : Set G) :=
      calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm
    have hLJ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ K) :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
        (sup_le Subgroup.le_normalizer hKL)
    have hNM : D.M ≤ Subgroup.normalizer ((S17.Lp D 5 : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (S17.Lp_le_M D 5)).mp
        (s13_Lp_normal D.M 5)
    have hTX : D.T ≤ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) := by
      rw [← h.hLK]
      exact D.sylowM.le.trans hNM
    have hJX : pCoreOf 2 (L ⊔ K) ≤ Q :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
        (sup_le Subgroup.le_normalizer hTX)
    exact hLJ.trans hJX
  have hxsO : ⁅x, s⁆ ∈ pCoreOf 2 L := by
    have hKL : ⁅K, L⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_comm]
      exact (calC_commutator_le_of_ne h.hyp.hL.1 h.hK h.hne.symm).trans inf_le_left
    have hmem : ⁅s * (l : G) * s⁻¹, (l : G)⁻¹⁆ ∈ pCoreOf 2 L :=
      Subgroup.commutator_le.mp hKL _ hlsK _ (L.inv_mem hlL)
    have heq : ⁅x, s⁆ = (l : G) * ⁅s * (l : G) * s⁻¹, (l : G)⁻¹⁆ * (l : G)⁻¹ := by
      rw [hsi, commutatorElement_def, commutatorElement_def]
      simp only [x]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hlL) _).mp hmem
  have hxsQ : ⁅x, s⁆ ∈ Q := hO2LQ hxsO
  have hs1 : s ≠ 1 := fun h1 => hsL (h1 ▸ Subgroup.one_mem _)
  have hxH'' : x ∈ H'' := mem_tauOf_of_commutator_mem_19 hss hs1 hxX hxsQ
  have hxρ : UC6S846.rhoL L ⟨x, hxNL⟩ = UC6S846.rhoL L ⟨(l : G), hlN⟩ := by
    have hxeq : (⟨x, hxNL⟩ : ↥N) =
        (⟨(l : G), hlN⟩ : ↥N) *
          (⟨s * (l : G) * s⁻¹,
            calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm hlsK⟩ : ↥N) :=
      Subtype.ext (by simp [x])
    rw [hxeq, map_mul,
      UC22.R8107Out.rhoL_eq_one_of_mem h.hyp.hL.1 h.hK h.hne.symm hlsK
        (calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm hlsK), mul_one]
  have keycase : ∀ (z : G) (hzN : z ∈ N),
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E (UC6S846.rhoL L ⟨z, hzN⟩) : Set (MulAut (Bar2 L))) → e = 1) →
      ⁅z, s⁆ ∈ pCoreOf 2 L →
      ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A z : Set G) → a ∈ Q'' := by
    intro z hzN hgoodz hzs a haA haNorm
    have hzNconj : conjSubgroup N z = N :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hzN)
    have hAzN : conjSubgroup A z ⊓ N = conjSubgroup A₀ z := by
      rw [show conjSubgroup A₀ z = conjSubgroup (A ⊓ N) z from rfl,
        E3.conjSubgroup_inf, hzNconj]
    by_cases haNL : a ∈ N
    ·
      have haA0 : a ∈ A₀ := Subgroup.mem_inf.mpr ⟨haA, haNL⟩
      have haNorm0 : a ∈ Subgroup.normalizer (conjSubgroup A₀ z : Set G) := by
        have h1 : a ∈ Subgroup.normalizer (conjSubgroup A z : Set G) ⊓
            Subgroup.normalizer (N : Set G) := ⟨haNorm, Subgroup.le_normalizer haNL⟩
        have h2 : a ∈ Subgroup.normalizer ((conjSubgroup A z ⊓ N : Subgroup G) : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_inf (H := conjSubgroup A z) (K := N) h1
        rwa [hAzN] at h2
      have hconj : conjSubgroup (conjSubgroup A₀ z) a = conjSubgroup A₀ z :=
        conjSubgroup_eq_iff_mem_normalizer.mpr haNorm0
      have hρa : UC6S846.rhoL L ⟨a, haNL⟩ = 1 :=
        rhoL_eq_one_of_conj_eq_19 hEeq hzN hzN rfl hgoodz haNL haA0 hconj
      exact Subgroup.mem_sup_left
        (mem_pCoreOf_of_rhoL_eq_one_of_swap_19 h (hAT hsA) hsL (hAT haA) haNL
          (mem_normalizer_right_19 h (hAT.trans D.sylowM.le haA) haNL h.hne.symm)
          (by
            have h1 : s * a = a * s :=
              (congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : A) (⟨s, hsA⟩ : A))).symm
            have h2 : ⁅s, a⁆ = 1 := by rw [commutatorElement_def, h1]; group
            rw [h2]; exact Q.one_mem)
          (Or.inl hρa))
    ·
      have hasN : a * s ∈ N := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have haL := map_pair_of_mem_not_normalizer_19 h hAgamma haA haNL
        calc L.map (MulAut.conj (a * s)).toMonoidHom
            = (L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
              (Subgroup.map_conj_map_conj L s a).symm
          _ = K.map (MulAut.conj a).toMonoidHom := by rw [hLmap.1]
          _ = L := haL.2
      have ha0N : (a * s)⁻¹ ∈ N := N.inv_mem hasN
      have ha0A0 : (a * s)⁻¹ ∈ A₀ :=
        Subgroup.mem_inf.mpr ⟨A.inv_mem (A.mul_mem haA hsA), ha0N⟩
      have hcommSZ : ⁅s, z⁆ ∈ pCoreOf 2 L := by
        rw [← commutatorElement_inv]
        exact (pCoreOf 2 L).inv_mem hzs
      have hyN : s * z * s⁻¹ ∈ N := by
        have h1 : s * z * s⁻¹ = ⁅s, z⁆ * z := by rw [commutatorElement_def]; group
        rw [h1]
        exact N.mul_mem
          (Subgroup.le_normalizer ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hcommSZ)) hzN
      have hρy : UC6S846.rhoL L ⟨s * z * s⁻¹, hyN⟩ =
          UC6S846.rhoL L ⟨z, hzN⟩ := by
        have h1 : (⟨s * z * s⁻¹, hyN⟩ : ↥N) =
            (⟨⁅s, z⁆, Subgroup.le_normalizer
              ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hcommSZ)⟩ : ↥N) * ⟨z, hzN⟩ := by
          apply Subtype.ext
          show (s * z * s⁻¹ : G) = ⁅s, z⁆ * z
          rw [commutatorElement_def]
          group
        rw [h1, map_mul,
          UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := X)
            (le_sup_left.trans le_sup_left)
            (Subgroup.le_normalizer ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hcommSZ))
            (hO2LQ hcommSZ), one_mul]
      have hAs : conjSubgroup A s = A :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hsA)
      have hB : conjSubgroup A (s * z * s⁻¹) = conjSubgroup (conjSubgroup A z) s := by
        rw [show s * z * s⁻¹ = s * (z * s⁻¹) by group, ← conjSubgroup_conjSubgroup,
          hAs, show z * s⁻¹ = z * s by rw [hsi], conjSubgroup_conjSubgroup]
      have hleft : conjSubgroup (conjSubgroup A (s * z * s⁻¹)) ((a * s)⁻¹) =
          conjSubgroup A z := by
        have haInv : a⁻¹ ∈ Subgroup.normalizer (conjSubgroup A z : Set G) :=
          (Subgroup.normalizer (conjSubgroup A z : Set G)).inv_mem haNorm
        calc conjSubgroup (conjSubgroup A (s * z * s⁻¹)) ((a * s)⁻¹)
            = conjSubgroup (conjSubgroup (conjSubgroup A z) s) ((a * s)⁻¹) := by rw [hB]
          _ = conjSubgroup (conjSubgroup A z) (s * (a * s)⁻¹) :=
              conjSubgroup_conjSubgroup (conjSubgroup A z) s ((a * s)⁻¹)
          _ = conjSubgroup (conjSubgroup A z) a⁻¹ := by
              rw [show s * (a * s)⁻¹ = a⁻¹ by group]
          _ = conjSubgroup A z :=
              conjSubgroup_eq_iff_mem_normalizer.mpr haInv
      have hAyN : conjSubgroup A (s * z * s⁻¹) ⊓ N =
          conjSubgroup A₀ (s * z * s⁻¹) := by
        rw [show conjSubgroup A₀ (s * z * s⁻¹) =
          conjSubgroup (A ⊓ N) (s * z * s⁻¹) from rfl, E3.conjSubgroup_inf,
          conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hyN)]
      have hNconj : conjSubgroup N ((a * s)⁻¹) = N :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ha0N)
      have hconj0 : conjSubgroup (conjSubgroup A₀ (s * z * s⁻¹)) ((a * s)⁻¹) =
          conjSubgroup A₀ z := by
        rw [← hAzN, ← hAyN, E3.conjSubgroup_inf, hNconj, hleft]
      have hρa0 : UC6S846.rhoL L ⟨(a * s)⁻¹, ha0N⟩ = 1 :=
        rhoL_eq_one_of_conj_eq_19 hEeq hzN hyN hρy hgoodz ha0N ha0A0 hconj0
      have ha0Q : (a * s)⁻¹ ∈ Q :=
        mem_pCoreOf_of_rhoL_eq_one_of_swap_19 h (hAT hsA) hsL
          (hAT (A.inv_mem (A.mul_mem haA hsA))) ha0N
          (mem_normalizer_right_19 h
            (hAT.trans D.sylowM.le (A.inv_mem (A.mul_mem haA hsA))) ha0N h.hne.symm)
          (by
            have h1 : (a * s)⁻¹ * s = s * (a * s)⁻¹ :=
              congrArg Subtype.val (mul_comm' (⟨(a * s)⁻¹,
                A.inv_mem (A.mul_mem haA hsA)⟩ : A) (⟨s, hsA⟩ : A))
            have h2 : ⁅s, (a * s)⁻¹⁆ = 1 := by
              rw [commutatorElement_def, hsi]
              rw [← h1, inv_inv, mul_assoc ((a * s)⁻¹) s s, hss, mul_one]
              group
            rw [h2]; exact Q.one_mem)
          (Or.inl hρa0)
      have haeq : a = ((a * s)⁻¹)⁻¹ * s := by
        rw [inv_inv, mul_assoc, hss, mul_one]
      rw [haeq]
      exact Subgroup.mul_mem_sup (Q.inv_mem ha0Q) (Subgroup.mem_zpowers s)
  have hN4 : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x : Set G) → a ∈ Q'' := by
    intro a haA haNorm
    exact keycase x hxNL
      (fun e he hN => hgood e he (by rwa [hxρ] at hN)) hxsO a haA haNorm
  have hxinvρ : UC6S846.rhoL L ⟨x⁻¹, N.inv_mem hxNL⟩ =
      (UC6S846.rhoL L ⟨(l : G), hlN⟩)⁻¹ := by
    have h1 : (⟨x⁻¹, N.inv_mem hxNL⟩ : ↥N) = (⟨x, hxNL⟩ : ↥N)⁻¹ := Subtype.ext (by simp)
    rw [h1, map_inv, hxρ]
  have hxsO_inv : ⁅x⁻¹, s⁆ ∈ pCoreOf 2 L := by
    have hcomm : ⁅s, x⁆ ∈ pCoreOf 2 L := by
      rw [← commutatorElement_inv]
      exact (pCoreOf 2 L).inv_mem hxsO
    have h1 : ⁅x⁻¹, s⁆ = x⁻¹ * ⁅s, x⁆ * x := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [h1]
    have h2 := (Subgroup.mem_normalizer_iff.mp
      ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
        (N.inv_mem hxNL)) _).mp hcomm
    simpa using h2
  have hN4inv : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x⁻¹ : Set G) → a ∈ Q'' := by
    intro a haA haNorm
    exact keycase x⁻¹ (N.inv_mem hxNL)
      (fun e he hN => hgoodinv e he (by rwa [hxinvρ] at hN)) hxsO_inv a haA haNorm
  exact exists_inCalO_two_not_one_19 h.hyp.hyp125 hm hQH hHQ hAH hAgamma hq2 hZ hxH'' hN4 hN4inv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
