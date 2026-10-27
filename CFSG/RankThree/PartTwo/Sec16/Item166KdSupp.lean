module

public import CFSG.RankThree.PartTwo.Sec16.Item166KdX
import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
import CFSG.RankThree.PartTwo.Sec16.Item166ThetaDich
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic
import CFSG.Sporadic.ON
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem dichotomy_of_mem_thetaComponentsAt {d : G} {Y K : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 d) (hK : K ∈ thetaComponentsAt 3 d) :
    Y ≤ K ∨ (K ≤ Subgroup.normalizer (Y : Set G) ∧
      ⁅Y, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y) :=
  dichotomy_of_mem_thetaComponentsIn (H := Subgroup.centralizer ({d} : Set G)) hY hK

private theorem ne_bot_of_mem_thetaComponentsAt {d : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 d) : Y ≠ ⊥ := by
  intro h
  apply Sec6.theta_ne_of_mem_thetaComponentsAt hY
  rw [h]
  exact le_antisymm (Sec6.theta_le (⊥ : Subgroup G)) bot_le

theorem le_normalizer_and_commutator_le_of_ne {d : G} {Y K : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 d) (hK : K ∈ thetaComponentsAt 3 d) (hne : Y ≠ K) :
    Y ≤ Subgroup.normalizer (K : Set G) ∧ ⁅Y, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
  have hC : ¬ Y ≤ K := fun hle => hne (Sec6.eq_of_mem_thetaComponentsIn_of_le
    (M := Subgroup.centralizer ({d} : Set G)) hY hK
    (Sec6.isPerfect_of_mem_thetaComponentsAt hY) (ne_bot_of_mem_thetaComponentsAt hY)
    le_rfl hle)
  have hC' : ¬ K ≤ Y := fun hle => hne (Sec6.eq_of_mem_thetaComponentsIn_of_le
    (M := Subgroup.centralizer ({d} : Set G)) hK hY
    (Sec6.isPerfect_of_mem_thetaComponentsAt hK) (ne_bot_of_mem_thetaComponentsAt hK)
    le_rfl hle).symm
  refine ⟨?_, ?_⟩
  · rcases dichotomy_of_mem_thetaComponentsAt hK hY with h | h
    · exact absurd h hC'
    · exact h.1
  · rcases dichotomy_of_mem_thetaComponentsAt hY hK with h | h
    · exact absurd h hC
    · exact h.2

theorem theta_le_theta_sSup {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {Y : Subgroup G} (hY : Y ∈ 𝒳) :
    inSubgroup (aschbacherSolvableCore 3) Y ≤
      inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
  have hYd : Y ∈ thetaComponentsAt 3 d := h𝒳 hY
  set X := sSup 𝒳 with hX
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hO
  have hθO : inSubgroup (aschbacherSolvableCore 3) Y ≤ O := Sec14.Res7MemFix.theta_le_of_mem hYd
  have hXC : X ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hX]
    exact sSup_le_centralizer_of_subset h𝒳
  have hXN : X ≤ Subgroup.normalizer (O : Set G) :=
    hXC.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hX3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
  refine (le_inf ((Sec6.theta_le Y).trans (le_sSup hY)) hθO).trans ?_
  exact inf_le_theta_of_types (X := X) (N := O) htypes hXN hX3

private theorem sSup_diff_le_centralizerMod {d : G}
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {J K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d) (hJK : J ≤ K) :
    sSup (𝒳 \ {K}) ≤ CFSG.LocalAnalysis.EvenBN.Tits.N.centralizerMod (sSup 𝒳)
      (inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳)) J := by
  refine sSup_le fun Y hY => ?_
  simp only [Set.mem_diff, Set.mem_singleton_iff] at hY
  obtain ⟨hY𝒳, hYK⟩ := hY
  have hY : Y ∈ thetaComponentsAt 3 d := h𝒳 hY𝒳
  have hYX : Y ≤ sSup 𝒳 := le_sSup hY𝒳
  have hcomm : ⁅Y, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y :=
    (le_normalizer_and_commutator_le_of_ne hY hK hYK).2
  have hθ : inSubgroup (aschbacherSolvableCore 3) Y ≤
      inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := theta_le_theta_sSup h𝒳 htypes hY𝒳
  intro g hg
  refine ⟨hYX hg, (Sec6.le_normalizer_theta (sSup 𝒳)) (hYX hg), fun l hl => ?_⟩
  exact hθ (hcomm (Subgroup.commutator_mem_commutator hg (hJK hl)))

private theorem commutator_mul_mem_theta {X : Subgroup G} {t y l : G}
    (htθ : t ∈ inSubgroup (aschbacherSolvableCore 3) X)
    (hyl : ⁅y, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) X)
    (htl : ⁅t, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) X) :
    ⁅t * y, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
  have htN : t ∈ Subgroup.normalizer
      (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    (Sec6.le_normalizer_theta X) (Sec6.theta_le X htθ)
  have hconj : t * ⁅y, l⁆ * t⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X :=
    (Subgroup.mem_normalizer_iff.mp htN ⁅y, l⁆).1 hyl
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact (inSubgroup (aschbacherSolvableCore 3) X).mul_mem hconj htl

private theorem exists_decomp_of_mem {d : G}
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {J K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hKJ : K = J ⊔ inSubgroup (aschbacherSolvableCore 3) K) (hK𝒳 : K ∈ 𝒳)
    {x : G} (hx : x ∈ sSup 𝒳) :
    ∃ j ∈ J, ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) K, ∃ y ∈ sSup 𝒳,
      x = j * (t * y) ∧ y ∈ sSup (𝒳 \ {K}) ∧
      (∀ l ∈ J, ⁅y, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳)) ∧
      ∀ l ∈ J, ⁅t, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
  classical
  have hJK : J ≤ K := by
    rw [hKJ]
    exact le_sup_left
  set X₁ := sSup (𝒳 \ {K}) with hX₁
  have hX₁X : X₁ ≤ sSup 𝒳 := by
    refine sSup_le fun Y hY => le_sSup (Set.diff_subset hY)
  have hX₁N : X₁ ≤ Subgroup.normalizer (K : Set G) := by
    refine sSup_le fun Y hY => ?_
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hY
    exact (le_normalizer_and_commutator_le_of_ne (h𝒳 hY.1) hK hY.2).1
  have hXle : sSup 𝒳 ≤ K ⊔ X₁ := by
    refine sSup_le fun Y hY => ?_
    by_cases hYK : Y = K
    · rw [hYK]
      exact le_sup_left
    · exact (le_sSup (show Y ∈ 𝒳 \ {K} by simp [hY, hYK])).trans le_sup_right
  have hxmul : x ∈ (K : Set G) * (X₁ : Set G) := by
    have h : x ∈ ((K ⊔ X₁ : Subgroup G) : Set G) := hXle hx
    rwa [Subgroup.coe_mul_of_right_le_normalizer_left K X₁ hX₁N] at h
  obtain ⟨k, hkK, y, hyX₁, hxy⟩ := Set.mem_mul.mp hxmul
  have hJθ : J ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    hJK.trans (Sec6.le_normalizer_theta K)
  have hk' : k ∈ ((J ⊔ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) : Set G) :=
    hKJ ▸ hkK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J
    (inSubgroup (aschbacherSolvableCore 3) K) hJθ] at hk'
  obtain ⟨j, hjJ, t, htθ, hjt⟩ := Set.mem_mul.mp hk'
  refine ⟨j, hjJ, t, htθ, y, hX₁X hyX₁, ?_, hyX₁, ?_, ?_⟩
  · rw [← hxy, ← hjt]
    group
  · exact fun l hl => (sSup_diff_le_centralizerMod h𝒳 htypes hK hJK hyX₁).2.2 l hl
  · intro l hl
    have h1 : l * t⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K :=
      (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta K (hJK hl)) t⁻¹).1
        ((inSubgroup (aschbacherSolvableCore 3) K).inv_mem htθ)
    have h2 : ⁅t, l⁆ = t * (l * t⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact theta_le_theta_sSup h𝒳 htypes hK𝒳
      ((inSubgroup (aschbacherSolvableCore 3) K).mul_mem htθ h1)

theorem supplement_of_mem_thetaComponentsAt {d : G}
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {J K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hKJ : K = J ⊔ inSubgroup (aschbacherSolvableCore 3) K) :
    ∀ x ∈ sSup 𝒳, ∃ j ∈ J, ∃ s ∈ sSup 𝒳, x = j * s ∧
      ∀ l ∈ J, ⁅s, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
  intro x hx
  have hJK : J ≤ K := by
    rw [hKJ]
    exact le_sup_left
  by_cases hK𝒳 : K ∈ 𝒳
  · obtain ⟨j, hjJ, t, htθ, y, hyX, hxjt, _, hyl, htl⟩ :=
      exists_decomp_of_mem h𝒳 htypes hK hKJ hK𝒳 hx
    have htX : t ∈ sSup 𝒳 := (Sec6.theta_le K).trans (le_sSup hK𝒳) htθ
    refine ⟨j, hjJ, t * y, (sSup 𝒳).mul_mem htX hyX, hxjt, fun l hl => ?_⟩
    exact commutator_mul_mem_theta (theta_le_theta_sSup h𝒳 htypes hK𝒳 htθ)
      (hyl l hl) (htl l hl)
  · have hdiff : 𝒳 \ {K} = 𝒳 := Set.diff_singleton_eq_self hK𝒳
    have hTx : x ∈ CFSG.LocalAnalysis.EvenBN.Tits.N.centralizerMod (sSup 𝒳)
        (inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳)) J :=
      (sSup_diff_le_centralizerMod h𝒳 htypes hK hJK) (by rwa [hdiff])
    exact ⟨1, J.one_mem, x, hx, by rw [one_mul], fun l hl => hTx.2.2 l hl⟩

theorem mem_of_perfect_le_sSup {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {J K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d) (hJK : J ≤ K) (hJX : J ≤ sSup 𝒳)
    (hJp : Group.IsPerfect ↥J) (hJ1 : J ≠ ⊥) : K ∈ 𝒳 := by
  classical
  by_contra hK𝒳
  have hdiff : 𝒳 \ {K} = 𝒳 := Set.diff_singleton_eq_self hK𝒳
  have hT := sSup_diff_le_centralizerMod h𝒳 htypes hK hJK
  rw [hdiff] at hT
  have hcomm : ⁅J, J⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (hT (hJX ha)).2.2 b hb
  have hJJ : ⁅J, J⁆ = J := by
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥J) (⊤ : Subgroup ↥J) J.subtype
    rw [← commutator_def, hJp.commutator_eq_top] at h
    have htop : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop] at h
    exact h.symm
  have hJθ : J ≤ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := hJJ ▸ hcomm
  haveI : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳)) :=
    (Sec6.theta_solvable_and_not_dvd (sSup 𝒳)).1
  have hJsolv : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJθ)
  exact hJ1 (CFSG.RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable hJp hJsolv)

private theorem normal_subgroupOf_sSup_of_mem {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {K : Subgroup G} (hK𝒳 : K ∈ 𝒳) :
    (K.subgroupOf (sSup 𝒳)).Normal := by
  have hK : K ∈ thetaComponentsAt 3 d := h𝒳 hK𝒳
  have hKX : K ≤ sSup 𝒳 := le_sSup hK𝒳
  have hXN : sSup 𝒳 ≤ Subgroup.normalizer (K : Set G) := by
    refine sSup_le fun Y hY => ?_
    by_cases hYK : Y = K
    · rw [hYK]
      exact Subgroup.le_normalizer
    · exact (le_normalizer_and_commutator_le_of_ne (h𝒳 hY) hK hYK).1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN

private theorem card_ON_dvd_of_map_eq_top {Q R : Type} [Group Q] [Group R] {V : Subgroup Q}
    (ψ : Q →* R) (φ : R →* CFSG.Blueprint.NativeSporadic.ON)
    (hφ : Function.Injective φ) (htop : (V.map ψ).map φ = ⊤) :
    Nat.card CFSG.Blueprint.NativeSporadic.ON ∣ Nat.card V := by
  have h1 : Nat.card ((V.map ψ).map φ) = Nat.card CFSG.Blueprint.NativeSporadic.ON := by
    rw [htop, Subgroup.card_top]
  have h2 : Nat.card ((V.map ψ).map φ) = Nat.card (V.map ψ) :=
    Subgroup.card_map_of_injective hφ
  rw [← h1, h2]
  exact Subgroup.card_map_dvd V ψ

private theorem exists_thetaQuotMap {K X : Subgroup G} (hKX : K ≤ X)
    (hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ inSubgroup (aschbacherSolvableCore 3) X) :
    ∃ φ : ↥K →* (↥X ⧸ aschbacherSolvableCore 3 ↥X),
      φ.range = (K.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) ∧
      aschbacherSolvableCore 3 ↥K ≤ φ.ker ∧
      (∀ k : ↥K, φ k = (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
        (Subgroup.inclusion hKX k)) ∧
      Nat.card φ.range ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  classical
  let ψ : ↥X →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
  let φ : ↥K →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) := ψ.comp (Subgroup.inclusion hKX)
  have hφrange : φ.range = (K.subgroupOf X).map ψ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hsub : (inSubgroup (aschbacherSolvableCore 3) K).subgroupOf K =
      aschbacherSolvableCore 3 ↥K := by
    rw [inSubgroup, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hker : aschbacherSolvableCore 3 ↥K ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkθ : ((k : ↥K) : G) ∈ inSubgroup (aschbacherSolvableCore 3) X :=
      hθ (Subgroup.mem_subgroupOf.mp (by rwa [← hsub] at hk))
    have hmem : Subgroup.inclusion hKX k ∈ aschbacherSolvableCore 3 ↥X := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hkθ
      rwa [show y = Subgroup.inclusion hKX k from Subtype.ext hyx] at hy
    show ψ (Subgroup.inclusion hKX k) = 1
    rw [show ψ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) from rfl,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  let g : (↥K ⧸ aschbacherSolvableCore 3 ↥K) →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    QuotientGroup.lift (aschbacherSolvableCore 3 ↥K) φ hker
  have hg : g.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)) = φ :=
    QuotientGroup.lift_comp_mk' (aschbacherSolvableCore 3 ↥K) φ hker
  have hgrange : g.range = φ.range := by
    rw [← hg, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact MonoidHom.range_eq_map g
  exact ⟨φ, hφrange, hker, fun _ => rfl, hgrange ▸ Subgroup.card_range_dvd g⟩

private theorem eq_bot_of_range_le_center {d : G} {K X : Subgroup G} (hKX : K ≤ X)
    (hK : K ∈ thetaComponentsAt 3 d)
    (φ : ↥K →* (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hφapply : ∀ k : ↥K, φ k = (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
      (Subgroup.inclusion hKX k))
    (hV : φ.range ≤ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) : K = ⊥ := by
  have hcomm : ⁅K, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    have h1 : φ ⟨k₁, hk₁⟩ ∈ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      hV ⟨⟨k₁, hk₁⟩, rfl⟩
    have h2 : φ ⟨k₂, hk₂⟩ ∈ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      hV ⟨⟨k₂, hk₂⟩, rfl⟩
    have hφ1 : φ ⁅(⟨k₁, hk₁⟩ : ↥K), ⟨k₂, hk₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp h1 (φ ⟨k₂, hk₂⟩)).symm
    have hmem : Subgroup.inclusion hKX (⁅(⟨k₁, hk₁⟩ : ↥K), ⟨k₂, hk₂⟩⁆) ∈
        aschbacherSolvableCore 3 ↥X := by
      have h := (hφapply ⁅(⟨k₁, hk₁⟩ : ↥K), ⟨k₂, hk₂⟩⁆).symm.trans hφ1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have hval : ((Subgroup.inclusion hKX (⁅(⟨k₁, hk₁⟩ : ↥K), ⟨k₂, hk₂⟩⁆) : ↥X) : G) =
        ⁅k₁, k₂⁆ := rfl
    rw [← hval]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hKK : ⁅K, K⁆ = K := by
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥K) (⊤ : Subgroup ↥K) K.subtype
    rw [← commutator_def, (Sec6.isPerfect_of_mem_thetaComponentsAt hK).commutator_eq_top] at h
    have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop] at h
    exact h.symm
  have hKθ : K ≤ inSubgroup (aschbacherSolvableCore 3) X := hKK ▸ hcomm
  haveI : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) X) :=
    (Sec6.theta_solvable_and_not_dvd X).1
  have hKsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKθ)
  exact CFSG.RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable
    (Sec6.isPerfect_of_mem_thetaComponentsAt hK) hKsolv

theorem not_isTripleCover_ON_of_mem {d : G}
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {K : Subgroup G} (hK𝒳 : K ∈ 𝒳)
    (hKA6 : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6))) :
    ¬ Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
      CFSG.Blueprint.NativeSporadic.ON := by
  classical
  intro hQ
  have hK : K ∈ thetaComponentsAt 3 d := h𝒳 hK𝒳
  have hKX : K ≤ sSup 𝒳 := le_sSup hK𝒳
  have hKn : (K.subgroupOf (sSup 𝒳)).Normal := normal_subgroupOf_sSup_of_mem h𝒳 hK𝒳
  have hθ : inSubgroup (aschbacherSolvableCore 3) K ≤
      inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := theta_le_theta_sSup h𝒳 htypes hK𝒳
  obtain ⟨φ, hφrange, -, hφapply, hcard⟩ := exists_thetaQuotMap hKX hθ
  set Q := ↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳) with hQdef
  let V : Subgroup Q := φ.range
  have hVn : V.Normal := by
    rw [show V = (K.subgroupOf (sSup 𝒳)).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(sSup 𝒳))) from hφrange]
    exact hKn.map _ (QuotientGroup.mk'_surjective _)
  have hVdvd : Nat.card V ∣ 1080 := by
    rw [← Sec13.card_eq_of_isTripleCover_six hKA6]
    exact hcard
  obtain ⟨e⟩ := hQ.2
  have hWn : (V.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hVn.map _ (QuotientGroup.mk'_surjective _)
  haveI hW'n : ((V.map (QuotientGroup.mk' (Subgroup.center Q))).map e.toMonoidHom).Normal :=
    hWn.map _ e.surjective
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((V.map (QuotientGroup.mk' (Subgroup.center Q))).map e.toMonoidHom) with hbot | htop
  · have hVleC : V ≤ Subgroup.center Q := by
      have h : V.map (QuotientGroup.mk' (Subgroup.center Q)) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hbot
      have h' : V ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker :=
        (Subgroup.map_eq_bot_iff V).mp h
      rwa [QuotientGroup.ker_mk'] at h'
    exact ne_bot_of_mem_thetaComponentsAt hK
      (eq_bot_of_range_le_center hKX hK φ hφapply hVleC)
  · have h : Nat.card CFSG.Blueprint.NativeSporadic.ON ∣ 1080 :=
      (card_ON_dvd_of_map_eq_top (QuotientGroup.mk' (Subgroup.center Q)) e.toMonoidHom
        e.injective htop).trans hVdvd
    rw [CFSG.Sporadic.ON.card_ON] at h
    exact absurd h (by norm_num)

theorem exists_Kd_isTripleCover
    (h134 : Item134) (h48 : Sec4.Item4_8)
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    ∃ Kd ∈ thetaComponentsAt 3 d,
      Kd = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) Kd ∧
      Sec4.IsTripleCover (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd) (alternatingGroup (Fin 6)) := by
  classical
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD13 : Sec13Data G A c L := h.toSec13Data
  obtain ⟨Kd, hKd, hLdKd, hKdeq, -⟩ :=
    exists_component_at_d h134 h48 h hΩ hJ hdA hd1 hdc
  have hLdEq : lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc
  obtain ⟨hdL, S, hdS, hSd⟩ := id hdc
  obtain ⟨-, -, hθ3L, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hS' := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3L hJ hdL hd1 S hdS hSd
  refine ⟨Kd, hKd, ?_, ?_⟩
  · exact hKdeq.trans (congrArg (fun z => z ⊔ inSubgroup (aschbacherSolvableCore 3) Kd)
      hLdEq.symm)
  · rcases h134 G A c L hD13 hJ d hdA hd1 ⟨_, hS'⟩ Kd hKd hLdKd with
      ⟨-, hA6, -⟩ | ⟨-, hA6, -⟩ | ⟨-, -, -, h12⟩
    · exact hA6
    · exact hA6
    · exfalso
      rw [hΩ, Set.ncard_singleton] at h12
      omega

end CFSG.RankThree.PartTwo.Sec16.Kd166
