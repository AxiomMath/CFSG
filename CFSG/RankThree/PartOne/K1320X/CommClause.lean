module

public import CFSG.RankThree.PartOne.K1320X.CommDistinctX
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.K1320.Chain
public import CFSG.RankThree.PartOne.K1320.Members
public import CFSG.RankThree.PartOne.S13K.Comm134

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_kZero_of_isKt {p : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (h : IsKt p E t K) : K ≤ kZero p E t := by
  by_cases hex : ∃ f : ℕ, kExceptional p (kZero p E t) f
  · obtain ⟨f, hf⟩ := hex
    exact (h.1 f hf).1
  · exact (h.2 hex).le

theorem comm_clauseX (hS : SchreierFor InCatalog) (h133 : KF133Two) (hDistX : KFCommDistinctX)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hn8 : ¬ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f)
    {z : MulAut E} (hz : Inverter p E z) {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (hsL : s ∈ torusImage E L) (ht : t ∈ reflectionSet p E) {Ks : Subgroup G}
    (hKs : KtLift p E s Ks) (hq0 : CFSG.IsQuasisimple ↥(kZero p E s)) {g₂ : ℕ}
    (hKt : KFAt p E g₂ t) (hsp : p ∣ 2 ^ g₂ - 1) (hne : s ≠ t) (hcomm : s * t = t * s)
    (hnc : ∀ y ∈ reflectionGroup p E, y * s * y⁻¹ ≠ t) :
    Ks ≤ Subgroup.centralizer (kZero p E t : Set G) ∧ Ks ⊓ kZero p E t = ⊥ := by
  have hp := h.prime
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hLt : KFLiftAt p E t := KFAt.toLiftAt hKt
  have hLt' := hLt
  have hqt := hLt.1
  obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := id hKs
  have hKsK0 : Ks ≤ kZero p E s := le_kZero_of_isKt hKs.1
  have hKsperf : Group.IsPerfect ↥Ks := hKs.2.1.1
  obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := id hLt
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨⟨e, hee⟩, hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hF13.axes s hs t ht)
  have he1 : e ≠ 1 := fun h1 => hne' (Subtype.ext h1)
  have hesE : e ∈ autFixedInG E s := (Subgroup.mem_inf.mp hee).1
  have hetE : e ∈ autFixedInG E t := (Subgroup.mem_inf.mp hee).2
  have heE : e ∈ E := Subgroup.map_subtype_le _ hesE
  obtain ⟨I₁, hI₁, hK0I₁⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hesE
    (kZero_le_centralizer_fixed p E s) (kZero_mem_thetaComponents hp hq0)
  obtain ⟨I₂, hI₂, hKI₂⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hetE
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hqt)
  have hKsI₁ : Ks ≤ I₁ := hKsK0.trans hK0I₁
  by_cases hI : I₁ = I₂
  · subst hI
    have hc := h133 G p A c L E h hF hF13 hT s hs hsL Ks hKs.1 e hesE he1 I₁ hI₁ hKsI₁
    rcases hc with ⟨-, f, hf1, hpf, hmodel4⟩ | ⟨J, hJ, hIJ⟩
    · exact absurd ⟨f, hf1, hpf, hmodel4⟩ hn8
    · have hEI : E ≤ Subgroup.normalizer (I₁ : Set G) :=
        h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI₁
      have hEJ : E ≤ Subgroup.normalizer (J : Set G) := normalizes_of_mem_thetaCompE h hJ.2.1
      have hsJ : Ks ≤ J :=
        isKt_le_of_sectionTenRel hp hE hKs.1 hKsperf hesE hI₁ hKsI₁ hIJ hEI hEJ
      have htJ : kZero p E t ≤ J :=
        isKt_le_of_sectionTenRel hp hE hLt'.isKt hqt.1 hetE hI₁ hKI₂ hIJ hEI hEJ
      have hsJ' : s ∈ torusImage E J :=
        Sec12Three.mem_torusImage_iff.mpr ⟨ks, hsJ hksK, hks, hks_eq⟩
      have htJ' : t ∈ torusImage E J :=
        Sec12Three.mem_torusImage_iff.mpr ⟨kt, htJ hktK, hkt, hkt_eq⟩
      exfalso
      obtain ⟨B, c', h', hF', hc'E, hc'1, hEB, r, hr, hmodel, hW⟩ :=
        member_package hF13 hcard hz hJ
      obtain ⟨x, hx, hxst⟩ := commuting_conj hF13 h' hF' hcard hc'E hr hW hs hsJ' ht htJ' hne hcomm
      exact hnc x (torusImage_le_reflectionGroup hF' hx) hxst
  · have hc : Ks ≤ Subgroup.centralizer (kZero p E t : Set G) :=
      hDistX G p A c L E h hF hF13 hT s hs t ht Ks (kZero p E t) ⟨hKs.1, hKs.2.1, hKs.2.2.1,
        hKs.2.2.2.1, ks, hks, hksK, hks_eq⟩ (ktLift_of_liftAt hLt')
        (Or.inr (Or.inr (hasTwoSub_of_kfAt h hF13 ht hKt hsp))) hcomm e
        (Subgroup.mem_inf.mpr ⟨hesE, hetE⟩) he1 I₁ hI₁ I₂ hI₂ hI hKsI₁ hKI₂
    exact ⟨hc, inf_eq_bot_of_centralizes hc hKs.2.2.1⟩

theorem chain_comm_clauseX (hS : SchreierFor InCatalog)
    (h133 : KF133Two) (hDistX : KFCommDistinctX) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hn8 : ¬ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f)
    {z : MulAut E} (hz : Inverter p E z) {t₁ t₂ t₃ : MulAut E} (hch : Chain3 p E L t₁ t₂ t₃)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hs₁ : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ reflectionSet p E)
    (hs₁L : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ torusImage E L) {K₁ : Subgroup G}
    (hK₁ : KtLift p E (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) (conjBy w K₁))
    (hq0 : CFSG.IsQuasisimple ↥(kZero p E (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹)))
    {g₃ : ℕ} (hK₃ : KFAt p E g₃ t₃) (hsp : p ∣ 2 ^ g₃ - 1) :
    K₁ ≤ Subgroup.centralizer (kZero p E t₃ : Set G) ∧ K₁ ⊓ kZero p E t₃ = ⊥ := by
  have hp := h.prime
  have hs₃ : conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ ∈ reflectionSet p E :=
    conj_mem_reflectionSet hp hch.mem₃ hw
  have hKs₃ : KFAt p E g₃ (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹) := hK₃.conj hw
  have hne : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ≠
      conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ := by
    intro h1
    have h2 : t₁ = t₃ := mul_left_cancel (mul_right_cancel h1)
    have h3 := hch.ord₁₂
    rw [h2, Sec1320.orderOf_mul_comm_reflections hch.mem₂.1 hch.mem₃.1, hch.ord₂₃] at h3
    omega
  have hcomm : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ *
      (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹) =
      conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ *
      (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) := by
    calc conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ * (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹)
        = conjAut E w hw * (t₁ * t₃) * (conjAut E w hw)⁻¹ := by group
      _ = conjAut E w hw * (t₃ * t₁) * (conjAut E w hw)⁻¹ := by rw [hch.comm₁₃]
      _ = _ := by group
  have hnc : ∀ y ∈ reflectionGroup p E, y * (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) * y⁻¹ ≠
      conjAut E w hw * t₃ * (conjAut E w hw)⁻¹ := by
    intro y hy hyst
    have hgW : conjAut E w hw ∈ torusWeyl E := ⟨⟨w, hw⟩, rfl⟩
    have hy' : (conjAut E w hw)⁻¹ * y * conjAut E w hw ∈ reflectionGroup p E := by
      have := Sec1322.conj_mem_reflectionGroup hp ((torusWeyl E).inv_mem hgW) hy
      simpa [mul_assoc] using this
    refine chain_not_conj_one_three hch hz.noconj hy' ?_
    calc (conjAut E w hw)⁻¹ * y * conjAut E w hw * t₁ *
          ((conjAut E w hw)⁻¹ * y * conjAut E w hw)⁻¹
        = (conjAut E w hw)⁻¹ * (y * (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹) * y⁻¹) *
          conjAut E w hw := by group
      _ = (conjAut E w hw)⁻¹ * (conjAut E w hw * t₃ * (conjAut E w hw)⁻¹) *
          conjAut E w hw := by rw [hyst]
      _ = t₃ := by group
  obtain ⟨h1, h2⟩ := comm_clauseX hS h133 hDistX h hF hF13 hT hEA hn8 hz hs₁ hs₁L hs₃ hK₁ hq0
    hKs₃ hsp hne hcomm hnc
  rw [kZero_conj p t₃ hw, Equivariance.centralizer_conjBy] at h1
  rw [kZero_conj p t₃ hw, ← conjBy_inf] at h2
  refine ⟨(conjBy_le_conjBy_iff w).1 h1, le_antisymm ?_ bot_le⟩
  refine (conjBy_le_conjBy_iff w).1 ?_
  rw [h2, conjBy_bot]

end CFSG.RankThree.PartOne.K1320X
