module

public import CFSG.RankThree.PartTwo.Sec16.Item166KdNarrow
import CFSG.RankThree.PartTwo.Sec16.Item166KdSupp
import CFSG.RankThree.PartTwo.Sec16.Item166ThetaTripleA6
import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
import CFSG.GroupTheory.PerfectSectionStability

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

@[expose] def Step166ThetaDCommK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ K ∈ thetaComponentsAt 3 d,
      K = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) K →
      Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) →
      A ≤ Subgroup.normalizer (K : Set G) →
      Subgroup.normalizer (Subgroup.zpowers d : Set G) ⊓ L ≤ Subgroup.normalizer (K : Set G) →
      CFSG.Open.pCoreOf 2 K = ⊥ →
      ⁅inSubgroup (aschbacherSolvableCore 3) K, lB A (Subgroup.closure {c, d})⁆ = ⊥

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private def centMod (Q K : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ k ∈ K, ⁅g, k⁆ ∈ Q}
  one_mem' := ⟨one_mem _, fun k _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun k hk => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN _).mp (hh k hk)) (hg k hk)
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun k hk => ?_⟩
    have hgi : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := inv_mem hgN
    have h1 : g⁻¹ * ⁅g, k⁆⁻¹ * g⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hgi _).mp (Q.inv_mem (hg k hk))
    have h2 : ⁅g⁻¹, k⁆ = g⁻¹ * ⁅g, k⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact h1

private theorem commutator_le_of_le_centMod {Q J V : Subgroup G} (hV : V ≤ centMod Q J) :
    ⁅V, J⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro v hv j hj
  exact (hV hv).2 j hj

private theorem commutator_le_of_le_normalizer {Q J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (Q : Set G)) : ⁅Q, J⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq j hj
  have h1 : j * q⁻¹ * j⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hJ hj) q⁻¹).mp (Q.inv_mem hq)
  have h2 : ⁅q, j⁆ = q * (j * q⁻¹ * j⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact Q.mul_mem hq h1

theorem commutator_theta_sSup_le_pCoreOf {d : G}
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    {J K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d) (hK𝒳 : K ∈ 𝒳)
    (hKJ : K = J ⊔ inSubgroup (aschbacherSolvableCore 3) K)
    (hKA6 : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)))
    (hJperf : Group.IsPerfect ↥J)
    (hθK : ⁅inSubgroup (aschbacherSolvableCore 3) K, J⁆ ≤
      CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) K)) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳), J⁆ ≤
      CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳)) := by
  classical
  set θK := inSubgroup (aschbacherSolvableCore 3) K
  set X := sSup 𝒳
  set θX := inSubgroup (aschbacherSolvableCore 3) X
  set P := CFSG.Open.pCoreOf 2 θK with hPdef
  have hJK : J ≤ K := by
    rw [hKJ]
    exact le_sup_left
  have hKX : K ≤ X := le_sSup hK𝒳
  have hXNK : X ≤ Subgroup.normalizer (K : Set G) := by
    refine sSup_le fun Y hY => ?_
    by_cases hYK : Y = K
    · rw [hYK]
      exact Subgroup.le_normalizer
    · exact (le_normalizer_and_commutator_le_of_ne (h𝒳 hY) hK hYK).1
  have hXNθK : X ≤ Subgroup.normalizer (θK : Set G) :=
    hXNK.trans (Sec6.normalizer_le_normalizer_theta K)
  have hXNP : X ≤ Subgroup.normalizer (P : Set G) :=
    hXNθK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 ↥θK))
  have hPθK : P ≤ θK := Subgroup.map_subtype_le _
  have hθKθX : θK ≤ θX := theta_le_theta_sSup h𝒳 htypes hK𝒳
  have hθXX : θX ≤ X := Sec6.theta_le X
  have hPO : P ≤ CFSG.Open.pCoreOf 2 θX :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPθK.trans hθKθX)
      (hθXX.trans hXNP) ((CFSG.pCore_isPGroup (p := 2) (G := ↥θK)).map θK.subtype)
  have hPn : (P.subgroupOf θK).Normal := by
    have hPsub : P.subgroupOf θK = CFSG.pCore 2 ↥θK := by
      rw [hPdef, CFSG.Open.pCoreOf, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective θK.subtype_injective]
    rw [hPsub]
    infer_instance
  have hθKs : Group.IsSolvable ↥θK := (Sec6.theta_solvable_and_not_dvd K).1
  have hDH : ∀ x ∈ θK, ∀ h ∈ J, ⁅x, h⁆ ∈ P := fun x hx h hh =>
    hθK (Subgroup.commutator_mem_commutator hx hh)
  have hcross : ∀ V : Subgroup G, ⁅V, J⁆ ≤ θK → ⁅V, J⁆ ≤ P := fun V hV =>
    CFSG.GroupTheory.commutator_le_of_isPerfect_of_le hJperf hθKs hPθK hPn hθK hV
  set X₁ := sSup (𝒳 \ {K})
  have hX₁X : X₁ ≤ X := sSup_le fun Y hY => le_sSup (Set.diff_subset hY)
  have hX₁C : X₁ ≤ centMod θK J := by
    refine sSup_le fun Y hY => ?_
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hY
    intro y hy
    refine ⟨hXNθK (le_sSup hY.1 hy), fun k hk => ?_⟩
    have hc : ⁅K, Y⁆ ≤ θK :=
      (le_normalizer_and_commutator_le_of_ne hK (h𝒳 hY.1) (Ne.symm hY.2)).2
    have hmem : ⁅k, y⁆ ∈ θK := hc (Subgroup.commutator_mem_commutator (hJK hk) hy)
    have h1 : ⁅y, k⁆ = ⁅k, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact θK.inv_mem hmem
  have hX₁P : ⁅X₁, J⁆ ≤ P := hcross X₁ (commutator_le_of_le_centMod hX₁C)
  have hX₁N : X₁ ≤ Subgroup.normalizer (K : Set G) := hX₁X.trans hXNK
  have hXle : X ≤ K ⊔ X₁ := by
    refine sSup_le fun Y hY => ?_
    by_cases hYK : Y = K
    · rw [hYK]
      exact le_sup_left
    · exact (le_sSup (show Y ∈ 𝒳 \ {K} by simp [hY, hYK])).trans le_sup_right
  have hKθ : K ⊓ θX ≤ θK :=
    inf_le_theta_of_types (X := K) (N := θX) (Or.inr (Or.inl hKA6))
      (hKX.trans (Sec6.le_normalizer_theta X))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (Sec6.theta_solvable_and_not_dvd X).2)
  have hθXJ : ∀ x ∈ θX, ∀ l ∈ J, ⁅x, l⁆ ∈ P := by
    intro x hx l hl
    have hxmul : x ∈ (K : Set G) * (X₁ : Set G) := by
      have h : x ∈ ((K ⊔ X₁ : Subgroup G) : Set G) := hXle (hθXX hx)
      rwa [Subgroup.coe_mul_of_right_le_normalizer_left K X₁ hX₁N] at h
    obtain ⟨k, hkK, y, hyX₁, hxy⟩ := Set.mem_mul.mp hxmul
    have hJθ : J ≤ Subgroup.normalizer (θK : Set G) := hJK.trans (Sec6.le_normalizer_theta K)
    have hk' : k ∈ ((J ⊔ θK : Subgroup G) : Set G) := hKJ ▸ hkK
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J θK hJθ] at hk'
    obtain ⟨j, hjJ, t, htθ, hjt⟩ := Set.mem_mul.mp hk'
    have hxe : x = j * (t * y) := by
      rw [← hxy, ← hjt]
      group
    have hjN : j ∈ Subgroup.normalizer (P : Set G) := hXNP (hKX (hJK hjJ))
    have hm : ∀ l' ∈ J, ⁅t * y, l'⁆ ∈ P := by
      intro l' hl'
      rw [commutatorElement_mul_left_eq_conj_mul]
      have htN : t ∈ Subgroup.normalizer (P : Set G) := hXNP (hθXX (hθKθX htθ))
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp htN _).mp
        (hX₁P (Subgroup.commutator_mem_commutator hyX₁ hl'))) (hDH t htθ l' hl')
    have hsplit : ∀ l' : G, ⁅x, l'⁆ = j * ⁅t * y, l'⁆ * j⁻¹ * ⁅j, l'⁆ := fun l' => by
      rw [hxe, commutatorElement_mul_left_eq_conj_mul]
    have hjθ : ∀ l' ∈ J, ⁅j, l'⁆ ∈ θK := by
      intro l' hl'
      have hconj : j * ⁅t * y, l'⁆ * j⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hjN _).mp (hm l' hl')
      have hxl : ⁅x, l'⁆ ∈ θX := by
        have hlN : l' ∈ Subgroup.normalizer (θX : Set G) :=
          Sec6.le_normalizer_theta X (hKX (hJK hl'))
        have h1 : l' * x⁻¹ * l'⁻¹ ∈ θX :=
          (Subgroup.mem_normalizer_iff.mp hlN _).mp (θX.inv_mem hx)
        have h2 : ⁅x, l'⁆ = x * (l' * x⁻¹ * l'⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [h2]
        exact θX.mul_mem hx h1
      have hjl : ⁅j, l'⁆ ∈ θX := by
        have h3 : ⁅j, l'⁆ = (j * ⁅t * y, l'⁆ * j⁻¹)⁻¹ * ⁅x, l'⁆ := by
          rw [hsplit l']
          group
        rw [h3]
        exact θX.mul_mem (θX.inv_mem (hθKθX (hPθK hconj))) hxl
      have hjlK : ⁅j, l'⁆ ∈ K := by
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem (hJK hjJ) (hJK hl')) (K.inv_mem (hJK hjJ)))
          (K.inv_mem (hJK hl'))
      exact hKθ ⟨hjlK, hjl⟩
    have hjC : Subgroup.zpowers j ≤ centMod θK J :=
      Subgroup.zpowers_le.mpr ⟨hJθ hjJ, hjθ⟩
    have hjP : ⁅j, l⁆ ∈ P :=
      hcross _ (commutator_le_of_le_centMod hjC)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers j) hl)
    rw [hsplit l]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp hjN _).mp (hm l hl)) hjP
  rw [Subgroup.commutator_le]
  intro x hx l hl
  exact hPO (hθXJ x hx l hl)

theorem commutator_theta_le_pCoreOf_of_split {K J : Subgroup G}
    (hS4 : SectionFourHyp ↥K) [Group.IsPerfect ↥K]
    (hKA6 : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)))
    (hJK : J ≤ K)
    (hleaf : CFSG.Open.pCoreOf 2 K = ⊥ →
      ⁅inSubgroup (aschbacherSolvableCore 3) K, J⁆ = ⊥) :
    ⁅inSubgroup (aschbacherSolvableCore 3) K, J⁆ ≤
      CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) K) := by
  by_cases hO2 : CFSG.Open.pCoreOf 2 K = ⊥
  · rw [hleaf hO2]
    exact bot_le
  · have hO2' : CFSG.pCore 2 ↥K ≠ ⊥ := fun hbot =>
      hO2 (by rw [CFSG.Open.pCoreOf, hbot, Subgroup.map_bot])
    have heq := ThetaTripleA6.aschbacherSolvableCore_eq_pCore_two hS4 hKA6 hO2'
    have hθ2 : IsPGroup 2 ↥(inSubgroup (aschbacherSolvableCore 3) K) := by
      unfold inSubgroup
      rw [heq]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype
    exact (commutator_le_of_le_normalizer (hJK.trans (Sec6.le_normalizer_theta K))).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hθ2)

private theorem centralizer_conj_eq {d g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    Subgroup.centralizer ({g * d * g⁻¹} : Set G) = Subgroup.centralizer ({d} : Set G) := by
  have hz : Subgroup.zpowers (g * d * g⁻¹) = Subgroup.zpowers d := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [MonoidHom.map_zpowers] at h
    simpa [MulAut.conj_apply] using h
  rw [← Subgroup.centralizer_closure, ← Subgroup.centralizer_closure ({d} : Set G),
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, hz]

private theorem mem_normalizer_of_mem_thetaComponentsAt {d g : G} {J K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d) (hJK : J ≤ K) (hJperf : Group.IsPerfect ↥J)
    (hJ1 : J ≠ ⊥) (hgd : g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  classical
  set K' := K.map (MulAut.conj g).toMonoidHom
  have hK' : K' ∈ thetaComponentsAt 3 d := by
    have h := CFSG.RankThree.PartTwo.map_mem_thetaComponentsAt (MulAut.conj g) hK
    rw [MulAut.conj_apply, thetaComponentsAt_eq_thetaComponentsIn,
      centralizer_conj_eq hgd] at h
    exact h
  have hJK' : J ≤ K' := by
    have hJmap : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgJ
    rw [← hJmap]
    exact Subgroup.map_mono hJK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hc : ⁅K, K'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
    (le_normalizer_and_commutator_le_of_ne hK hK' (Ne.symm hne)).2
  have hJθ : J ≤ inSubgroup (aschbacherSolvableCore 3) K := by
    have hJJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
    rw [← hJJ]
    exact (Subgroup.commutator_mono hJK hJK').trans hc
  haveI := (Sec6.theta_solvable_and_not_dvd K).1
  have hsol : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJθ)
      (Subgroup.inclusion_injective _)
  haveI : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  exact Group.IsPerfect.not_isSolvable ↥J hsol

private theorem mem_normalizer_inSubgroup_perfectResidual {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (inSubgroup perfectResidual K : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (perfectResidual ↥K) hg

private theorem normalizer_facts_lB
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (lB A (Subgroup.closure {c, d}) : Set G) := by
  have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 := map_centralizer_singleton (MulAut.conj g) d
    rw [MulAut.conj_apply, centralizer_conj_eq hg] at h1
    exact h1
  rw [Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
  exact mem_normalizer_inSubgroup_perfectResidual
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hgL, hgC⟩)

theorem step166ThetaDComm_of_thetaDCommK
    (h134 : Item134) (h48 : Sec4.Item4_8) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hK : Step166ThetaDCommK) : Step166ThetaDComm := by
  intro G _ _ A c L Y₀ h hJ d hdA hd1 hdc 𝒳 h𝒳 _ _ hJX _ htypes
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Proof17Res10.omegaA_eq_of_j2 h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h)
      h.zpowers_mem_omegaA h.mem_lA hJ
  obtain ⟨Kd, hKd, hKdeq, hKdA6⟩ := exists_Kd_isTripleCover h134 h48 h hΩ hJ hdA hd1 hdc
  set LB := lB A (Subgroup.closure {c, d}) with hLB
  have hJK : LB ≤ Kd := by
    rw [hKdeq]
    exact le_sup_left
  have hLBperf : Group.IsPerfect ↥LB := by
    rw [hLB, Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_isPerfect L d
  have hLBne : LB ≠ ⊥ := by
    intro hbot
    have hdJ : d ∈ LB := Ctr166.mem_lB_closure h hJ hdA hd1 hdc
    exact hd1 (Subgroup.mem_bot.mp (hbot ▸ hdJ))
  have htypes3 : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) :=
    Or.inr htypes
  have hKd𝒳 : Kd ∈ 𝒳 := mem_of_perfect_le_sSup h𝒳 htypes3 hKd hJK hJX hLBperf hLBne
  have hAK : A ≤ Subgroup.normalizer (Kd : Set G) := by
    intro a ha
    have had : a ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      have hcomm : Commute a d :=
        congrArg Subtype.val (hD13.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      congr 1
      simp [MulAut.conj_apply, hcomm.eq]
    exact mem_normalizer_of_mem_thetaComponentsAt hKd hJK hLBperf hLBne had
      (normalizer_facts_lB h hJ hdA hd1 hdc had (hD13.le_normalizer ha))
  have hNK : Subgroup.normalizer (Subgroup.zpowers d : Set G) ⊓ L ≤
      Subgroup.normalizer (Kd : Set G) := by
    rintro τ ⟨hτd, hτL⟩
    exact mem_normalizer_of_mem_thetaComponentsAt hKd hJK hLBperf hLBne hτd
      (normalizer_facts_lB h hJ hdA hd1 hdc hτd (Subgroup.le_normalizer hτL))
  have hKtop : Kd ≠ ⊤ := by
    intro htop
    have hKC : Kd ≤ Subgroup.centralizer ({d} : Set G) :=
      Sec14.le_centralizer_of_mem_thetaComponentsAt hKd
    exact Sec14.centralizer_singleton_ne_top hD13.isSimpleGroup hD13.nonabelian hd1
      (top_le_iff.mp (htop ▸ hKC))
  have hS4 : SectionFourHyp ↥Kd := hD13.toTheoremFourHyp.sectionFourHyp hKtop
  haveI : Group.IsPerfect ↥Kd := Sec6.isPerfect_of_mem_thetaComponentsAt hKd
  have hθK := commutator_theta_le_pCoreOf_of_split hS4 hKdA6 hJK
    (hK G A c L Y₀ h hJ d hdA hd1 hdc Kd hKd hKdeq hKdA6 hAK hNK)
  exact commutator_theta_sSup_le_pCoreOf h𝒳 htypes3 hKd hKd𝒳 hKdeq hKdA6 hLBperf hθK

end CFSG.RankThree.PartTwo.Sec16.Kd166
