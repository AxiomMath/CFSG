module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourElevenCommon
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenClosing
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenPGLTwo
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenPermThree
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenLevi
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenFrameSD
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenFrameWR
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenYStep
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenOuterMember

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81.FourEleven
open CFSG.Blueprint (LieModel)

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p : ℕ}

theorem isSylowIn_inf_normalizer_of_isSylowIn_top {K T W : Subgroup Q} [K.Normal]
    (hT : IsSylowIn 2 T ⊤) (hTW : T ≤ normalizer (W : Set Q)) :
    IsSylowIn 2 (T ⊓ (K ⊓ normalizer (W : Set Q))) (K ⊓ normalizer (W : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylK : IsSylowIn 2 (T ⊓ K) K :=
    IsSylowIn.inf_normal hT (N := K) le_top (Subgroup.Normal.subgroupOf inferInstance ⊤)
  have hPeq : T ⊓ (K ⊓ normalizer (W : Set Q)) = T ⊓ K := by
    rw [← inf_assoc]
    exact inf_eq_left.mpr fun x hx => hTW hx.1
  rw [hPeq]
  exact E6.isSylowIn_of_le hSylK (fun x hx => ⟨hx.2, hTW hx.1⟩) inf_le_left

theorem exists_frame_data_sd {K T A : Subgroup Q} [K.Normal] {p : ℕ} {z : Q}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : (LieModel ↥K .PSL 3 p 1 ∧ p % 4 = 3) ∨ (LieModel ↥K .PSU 3 p 1 ∧ p % 4 = 1))
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hAL : A ≤ K) (hA : IsElemAbelian 2 A)
    (hA4 : Nat.card A = 4) (hzA : z ∈ A) (hz2 : orderOf z = 2)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ W : Subgroup Q, W ≤ K ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ z ∈ W ∧
      IsSylowIn 2 (T ⊓ (K ⊓ normalizer (W : Set Q))) (K ⊓ normalizer (W : Set Q)) ∧
      tA T A ≤ normalizer (W : Set Q) ∧ ¬ A ⊓ K ≤ centralizer (W : Set Q) := by
  obtain ⟨u, huA, hu2, huz⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.elementary_four_exists_involution_ne
      A hA hA4 z
  obtain ⟨W, hWL, hW, hW4, hzW, hCT, huNW, hSyl⟩ :=
    exists_frame_four_sd hp hp2 hL hT (hAL hzA) hz2 hzT (hAT huA) (hAL huA) hu2 huz
  have hR : tA T A ≤ normalizer (W : Set Q) := by
    rw [tA_eq_inf_centralizer hO2]
    refine (inf_le_inf le_rfl ?_).trans hCT
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx u huA
  have hAW : ¬ A ⊓ K ≤ centralizer (W : Set Q) := by
    rw [inf_eq_left.mpr hAL]
    intro hle
    exact huNW (hle huA)
  exact ⟨W, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩

theorem exists_frame_data_wr {K : Subgroup Q} (h : FourElevenSetting Q K p) (hp5 : 5 ≤ p)
    {T A₀ : Subgroup Q} {Ω : Set (Subgroup Q)} {z : Q}
    (hL : (LieModel ↥K .PSL 3 p 1 ∧ p % 4 = 1) ∨ (LieModel ↥K .PSU 3 p 1 ∧ p % 4 = 3))
    (hT : IsSylowIn 2 T ⊤) (hΩ : IsOmegaColl Ω) (hA₀Ω : A₀ ∈ Ω) (hA₀L : A₀ ≤ K)
    (hA₀4 : Nat.card A₀ = 4) (hzL : z ∈ K) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ A W : Subgroup Q, A ∈ Ω ∧ A ≤ T ∧ IsElemAbelian 2 A ∧
      W ≤ K ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ z ∈ W ∧
      IsSylowIn 2 (T ⊓ (K ⊓ normalizer (W : Set Q))) (K ⊓ normalizer (W : Set Q)) ∧
      tA T A ≤ normalizer (W : Set Q) ∧ ¬ A ⊓ K ≤ centralizer (W : Set Q) := by
  have : K.Normal := h.normal
  obtain ⟨W, A, hWTL, hW, hW4, hzW, hTW, hATL, hA, hA4, hAW'⟩ :=
    exists_frame_four_wr h.prime hp5 hL hT hzL hz2 hzT
  have hWL : W ≤ K := hWTL.trans inf_le_right
  have hAL : A ≤ K := hATL.trans inf_le_right
  have hAT : A ≤ T := hATL.trans inf_le_left
  have hAΩ : A ∈ Ω :=
    FourElevenSetting.mem_of_four h hΩ hA₀Ω hA₀L hA₀4 hAL hA hA4
  have hSyl : IsSylowIn 2 (T ⊓ (K ⊓ normalizer (W : Set Q))) (K ⊓ normalizer (W : Set Q)) :=
    isSylowIn_inf_normalizer_of_isSylowIn_top hT hTW
  have hR : tA T A ≤ normalizer (W : Set Q) := by
    rw [tA_eq_inf_centralizer h.pCoreOf_two_top]
    exact inf_le_left.trans hTW
  have hAW : ¬ A ⊓ K ≤ centralizer (W : Set Q) := by
    rw [inf_eq_left.mpr hAL]
    exact hAW'
  exact ⟨A, W, hAΩ, hAT, hA, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩

theorem exists_conj_of_monomial_frame {K : Subgroup Q} [K.Normal] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel ↥K .PSL 3 p 1 ∨ LieModel ↥K .PSU 3 p 1) (hidx : K.index ≤ 2)
    {T A W : Subgroup Q} {Ω : Set (Subgroup Q)} {z : Q} (hT : IsSylowIn 2 T ⊤)
    (hAΩ : A ∈ Ω) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hWL : W ≤ K)
    (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) (hzW : z ∈ W) (hz2 : orderOf z = 2)
    (hSyl : IsSylowIn 2 (T ⊓ (K ⊓ normalizer (W : Set Q))) (K ⊓ normalizer (W : Set Q)))
    (hR : tA T A ≤ normalizer (W : Set Q)) (hAW : ¬ A ⊓ K ≤ centralizer (W : Set Q)) :
    ∃ c ∈ genEi 1 T Ω ⊔ T, c * z * c⁻¹ ≠ z ∧ c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
  obtain ⟨hab, h6, X₀, hX₀, hX₀M, hX₀sup⟩ :=
    exists_monomial_frame hp hp2 hL hWL hW hW4
  obtain ⟨X, hX⟩ :=
    exists_permThreeMember_of_frame hT hAT hWL hW hW4 hzW hz2 hab h6 hX₀ hX₀M hX₀sup hSyl hR hAW
  have hK : InCalEi 1 T A (X ⊔ tA T A) :=
    PermThreeMember.inCalEi le_rfl hidx hT hAT hA hX
  have hmem : X ⊔ tA T A ≤ genEi 1 T Ω :=
    CFSG.LocalAnalysis.WeakClosure81.le_genEi_of_inCalEi hAΩ hAT hK
  obtain ⟨c, hcX, hne, hcomm⟩ := hX.exists_conj
  exact ⟨c, ((le_sup_left.trans hmem).trans le_sup_left) hcX, hne, hcomm⟩

theorem FourElevenSetting.levi_le
    (h : FourElevenSetting Q L p) (hp7 : 7 ≤ p) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω) (hcard : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A)
    {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t) :
    ⁅L ⊓ centralizer ({z} : Set Q), L ⊓ centralizer ({z} : Set Q)⁆ ≤ genEi 1 T Ω ⊔ T := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : L.Normal := h.normal
  have hp5 : 5 ≤ p := by omega
  obtain ⟨Y, hY⟩ := exists_leviData h.prime hp5 h.isL3 hzL hz2
  rw [← hY.eq_commutator]
  have hYL : Y ≤ L := by
    rw [hY.eq_commutator]
    exact Subgroup.commutator_le_of_le inf_le_left inf_le_left
  obtain ⟨A₀, hA₀Ω, hA₀T⟩ := hΩ.exists_mem_le hT
  have hA₀ : IsElemAbelian 2 A₀ := hΩ.elemAbelian A₀ hA₀Ω
  have h4 : 4 ≤ Nat.card A₀ := hcard A₀ hA₀Ω hA₀T
  have hAY : ¬ A₀ ≤ centralizer (Y : Set Q) := by
    refine LeviData.not_le_centralizer hY h.index_le_two ?_ hA₀ h4
    intro b hbL hb2
    exact OuterData.not_le_centralizer hp5
      (outerData_of_lieModel h.prime hp5 h.centralizer_eq_bot h.isL3 hbL hb2) hYL hY.sl2
  have hzT' : T ≤ centralizer ({z} : Set Q) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (hzT t ht).symm
  have hYle : Y ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A₀ J}, J :=
    LeviData.le_sup_iSup_calEi hp7 hT hA₀T hA₀ hzT' hY hAY
  have hgen : (⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A₀ J}, J) ≤ genEi 1 T Ω :=
    iSup_calEi_one_le_genEi hA₀Ω hA₀T (j := 1) le_rfl
  calc Y ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A₀ J}, J := hYle
    _ ≤ T ⊔ genEi 1 T Ω := sup_le_sup_left hgen T
    _ = genEi 1 T Ω ⊔ T := sup_comm _ _

theorem FourElevenSetting.exists_conj_of_not_le
    (h : FourElevenSetting Q L p) (hp7 : 7 ≤ p) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω) (hcard : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A)
    {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t)
    (hO : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ L) :
    ∃ c ∈ genEi 1 T Ω ⊔ T, c * z * c⁻¹ ≠ z ∧ c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : L.Normal := h.normal
  have hp5 : 5 ≤ p := by omega
  obtain ⟨A, hAΩ, hAT, hAL⟩ := hO
  have hA : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  obtain ⟨b, hbA, hbL⟩ : ∃ b ∈ A, b ∉ L := by
    by_contra hc
    apply hAL
    intro x hx
    by_contra hxL
    exact hc ⟨x, hx, hxL⟩
  have hb1 : b ≠ 1 := by
    intro hb
    exact hbL (hb ▸ L.one_mem)
  have hb2 : orderOf b = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hA.2 b hbA) hb1
  obtain ⟨g, hA'Ω, hA'T, hSyl⟩ := exists_conj_isSylowIn_centralizer hT hΩ hAΩ hAT hbA
  have hb'A' : g⁻¹ * b * g ∈ conjSubgroup A g := by
    rw [mem_conjSubgroup_iff]
    have hconj : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rw [hconj]
    exact hbA
  have hb'L : g⁻¹ * b * g ∉ L := by
    intro hb'
    apply hbL
    have hconj : g * (g⁻¹ * b * g) * g⁻¹ ∈ L := h.normal.conj_mem _ hb' g
    rwa [show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at hconj
  have hb'2 : orderOf (g⁻¹ * b * g) = 2 := by
    have hsem : SemiconjBy g⁻¹ b (g⁻¹ * b * g) := by
      unfold SemiconjBy
      group
    rw [← SemiconjBy.orderOf_eq g⁻¹ hsem]
    exact hb2
  have hb : OuterData L p (g⁻¹ * b * g) :=
    outerData_of_lieModel h.prime hp5 h.centralizer_eq_bot h.isL3 hb'L hb'2
  have hcardA : 4 ≤ Nat.card A := hcard A hAΩ hAT
  have hcardA' : Nat.card (conjSubgroup A g) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hA'4 : 4 ≤ Nat.card (conjSubgroup A g) := hcardA' ▸ hcardA
  have hA'L : conjSubgroup A g ⊓ L ≠ ⊥ := by
    intro hbot
    have hle := card_le_two_mul_card_inf h.index_le_two (conjSubgroup A g)
    rw [hbot, Subgroup.card_bot] at hle
    omega
  have hA' : IsElemAbelian 2 (conjSubgroup A g) := hΩ.elemAbelian _ hA'Ω
  have hCb : centralizer ({g⁻¹ * b * g} : Set Q) ≤
      T ⊔ ⨆ J ∈ {J : Subgroup Q | InCalEi 1 T (conjSubgroup A g) J}, J :=
    OuterData.centralizer_le_sup_iSup_calEi hp7 h.index_le_two h.pCoreOf_two_top hT hA'T hA'
      hb'A' hb'L hSyl hb hA'L
  have hgen : (⨆ J ∈ {J : Subgroup Q | InCalEi 1 T (conjSubgroup A g) J}, J) ≤
      genEi 1 T Ω := iSup_calEi_one_le_genEi hA'Ω hA'T (j := 1) le_rfl
  have hCbK : centralizer ({g⁻¹ * b * g} : Set Q) ≤ genEi 1 T Ω ⊔ T :=
    hCb.trans ((sup_le_sup_left hgen T).trans_eq (sup_comm _ _))
  have hzH : z ∈ L ⊓ centralizer ({g⁻¹ * b * g} : Set Q) := by
    refine ⟨hzL, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hzT (g⁻¹ * b * g) (hA'T hb'A')
  obtain ⟨e⟩ := hb.pgl2
  obtain ⟨c, hcH, hne, hcomm⟩ :=
    exists_commuting_conj_of_mulEquiv_pgl2 h.ne_two e hzH hz2
  exact ⟨c, (inf_le_right.trans hCbK) hcH, hne, hcomm⟩

theorem FourElevenSetting.exists_conj_of_le (h : FourElevenSetting Q L p) (hp5 : 5 ≤ p)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω)
    (hcard : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A) {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) (hI : ∀ A ∈ Ω, A ≤ T → A ≤ L) :
    ∃ c ∈ genEi 1 T Ω ⊔ T, c * z * c⁻¹ ≠ z ∧ c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : L.Normal := h.normal
  obtain ⟨A₀, hA₀Ω, hA₀T⟩ := hΩ.exists_mem_le hT
  have hA₀ : IsElemAbelian 2 A₀ := hΩ.elemAbelian A₀ hA₀Ω
  have hA₀L : A₀ ≤ L := hI A₀ hA₀Ω hA₀T
  have h4 : 4 ≤ Nat.card A₀ := hcard A₀ hA₀Ω hA₀T
  have hle4 : Nat.card ↥(A₀ ⊓ L) ≤ 4 := card_inf_le_four h.prime h.ne_two h.isL3 hA₀
  have hA₀4 : Nat.card A₀ = 4 := by
    rw [inf_eq_left.mpr hA₀L] at hle4
    omega
  have hzA₀ : z ∈ A₀ :=
    mem_of_commute_of_card_inf_eq_four h.prime h.ne_two h.isL3 hA₀
      (by rw [inf_eq_left.mpr hA₀L]; exact hA₀4) hzL hz2
      fun a ha => hzT a (hA₀T ha)
  have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := h.prime.odd_of_ne_two h.ne_two
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
    · left
      have hp1 : p = 1 + m * 4 := by omega
      rw [hp1]
      simp
    · right
      have hp3 : p = 3 + m * 4 := by omega
      rw [hp3]
      simp
  have hdata : ∃ A W : Subgroup Q, A ∈ Ω ∧ A ≤ T ∧ IsElemAbelian 2 A ∧
      W ≤ L ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ z ∈ W ∧
      IsSylowIn 2 (T ⊓ (L ⊓ normalizer (W : Set Q))) (L ⊓ normalizer (W : Set Q)) ∧
      tA T A ≤ normalizer (W : Set Q) ∧ ¬ A ⊓ L ≤ centralizer (W : Set Q) := by
    rcases h.isL3 with hL3 | hU3
    · rcases hpmod with hp41 | hp43
      · obtain ⟨A, W, hAΩ, hAT, hA, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩ :=
          exists_frame_data_wr h hp5 (Or.inl ⟨hL3, hp41⟩) hT hΩ hA₀Ω hA₀L hA₀4 hzL hz2 hzT
        exact ⟨A, W, hAΩ, hAT, hA, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩
      · obtain ⟨W, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩ :=
          exists_frame_data_sd h.prime h.ne_two (Or.inl ⟨hL3, hp43⟩) hT hA₀T hA₀L hA₀ hA₀4 hzA₀
            hz2 h.pCoreOf_two_top hzT
        exact ⟨A₀, W, hA₀Ω, hA₀T, hA₀, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩
    · rcases hpmod with hp41 | hp43
      · obtain ⟨W, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩ :=
          exists_frame_data_sd h.prime h.ne_two (Or.inr ⟨hU3, hp41⟩) hT hA₀T hA₀L hA₀ hA₀4 hzA₀
            hz2 h.pCoreOf_two_top hzT
        exact ⟨A₀, W, hA₀Ω, hA₀T, hA₀, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩
      · obtain ⟨A, W, hAΩ, hAT, hA, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩ :=
          exists_frame_data_wr h hp5 (Or.inr ⟨hU3, hp43⟩) hT hΩ hA₀Ω hA₀L hA₀4 hzL hz2 hzT
        exact ⟨A, W, hAΩ, hAT, hA, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩
  obtain ⟨A, W, hAΩ, hAT, hA, hWL, hW, hW4, hzW, hSyl, hR, hAW⟩ := hdata
  exact exists_conj_of_monomial_frame h.prime h.ne_two h.isL3 h.index_le_two hT hAΩ hAT hA hWL hW
    hW4 hzW hz2 hSyl hR hAW

theorem fourElevenLarge_holds :
    FourElevenLarge := by
  intro Q _ _ L p h hp7 T hT Ω hΩ hcard
  have : Fact p.Prime := ⟨h.prime⟩
  have : L.Normal := h.normal
  have hp5 : 5 ≤ p := by omega
  have hcard' : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A := by
    intro A hA hAT
    have h := hcard A hA hAT
    simpa using h
  obtain ⟨z, hzL, hz2, hzT⟩ := h.exists_central_involution hT
  have hY := FourElevenSetting.levi_le h hp7 hT hΩ hcard' hzL hz2 hzT
  have hc : ∃ c ∈ genEi 1 T Ω ⊔ T, c * z * c⁻¹ ≠ z ∧
      c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
    by_cases hO : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ L
    · exact FourElevenSetting.exists_conj_of_not_le h hp7 hT hΩ hcard' hzL hz2 hzT hO
    · have hI : ∀ A ∈ Ω, A ≤ T → A ≤ L := by
        intro A hA hAT
        by_contra hAL
        exact hO ⟨A, hA, hAT, hAL⟩
      exact FourElevenSetting.exists_conj_of_le h hp5 hT hΩ hcard' hzL hz2 hzT hI
  obtain ⟨c, hcK, hne, hcomm⟩ := hc
  have hLK : L ≤ genEi 1 T Ω ⊔ T :=
    le_of_commutator_le_of_commuting_conj h.prime hp5 h.isL3 hzL hz2 hY hcK hne hcomm
  exact FourElevenSetting.eq_top_of_le h hT hLK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
