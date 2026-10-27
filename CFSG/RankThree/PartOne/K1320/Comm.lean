module

public import CFSG.RankThree.PartOne.K1320.Members
public import CFSG.RankThree.PartOne.S13K.Comm134
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem comm_clause (hS : SchreierFor InCatalog) (h133 : KF133Two)
    (hDist : KFCommDistinct) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hn8 : ¬ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f)
    {z : MulAut E} (hz : Inverter p E z) {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (hsL : s ∈ torusImage E L) (ht : t ∈ reflectionSet p E) {g₁ g₂ : ℕ} (hKs : KFAt p E g₁ s)
    (hKt : KFAt p E g₂ t) (hsp : p ∣ 2 ^ g₁ - 1) (hne : s ≠ t) (hcomm : s * t = t * s)
    (hnc : ∀ y ∈ reflectionGroup p E, y * s * y⁻¹ ≠ t) :
    kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
      kZero p E s ⊓ kZero p E t = ⊥ := by
  have hp := h.prime
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hLs : KFLiftAt p E s := KFAt.toLiftAt hKs
  have hLt : KFLiftAt p E t := KFAt.toLiftAt hKt
  have hLs' := hLs
  have hLt' := hLt
  have hqs := hLs.1
  have hqt := hLt.1
  have hcs := hLs.2.1
  obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := hLs
  obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hLt
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨⟨e, hee⟩, hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hF13.axes s hs t ht)
  have he1 : e ≠ 1 := fun h1 => hne' (Subtype.ext h1)
  have hesE : e ∈ autFixedInG E s := (Subgroup.mem_inf.mp hee).1
  have hetE : e ∈ autFixedInG E t := (Subgroup.mem_inf.mp hee).2
  have heE : e ∈ E := Subgroup.map_subtype_le _ hesE
  obtain ⟨I₁, hI₁, hKI₁⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hesE
    (kZero_le_centralizer_fixed p E s) (kZero_mem_thetaComponents hp hqs)
  obtain ⟨I₂, hI₂, hKI₂⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hetE
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hqt)
  by_cases hI : I₁ = I₂
  · subst hI
    have hc := h133 G p A c L E h hF hF13 hT s hs hsL (kZero p E s) ((KFAt.toLiftAt hKs).isKt) e
      hesE he1 I₁ hI₁ hKI₁
    rcases hc with ⟨-, f, hf1, hpf, hmodel4⟩ | ⟨J, hJ, hIJ⟩
    · exact absurd ⟨f, hf1, hpf, hmodel4⟩ hn8
    · have hEI : E ≤ Subgroup.normalizer (I₁ : Set G) :=
        h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI₁
      have hEJ : E ≤ Subgroup.normalizer (J : Set G) := normalizes_of_mem_thetaCompE h hJ.2.1
      have hsJ : kZero p E s ≤ J :=
        isKt_le_of_sectionTenRel hp hE hLs'.isKt hqs.1 hesE hI₁ hKI₁ hIJ hEI hEJ
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
  · have hc : kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) :=
      hDist G p A c L E h hF hF13 hT s hs t ht hLs' hLt'
        (Or.inr (Or.inl (K1320X.hasTwoSub_of_kfAt h hF13 hs hKs hsp))) hcomm e
        (Subgroup.mem_inf.mpr ⟨hesE, hetE⟩) he1 I₁ hI₁ I₂ hI₂ hI hKI₁ hKI₂
    exact ⟨hc, inf_eq_bot_of_centralizes hc hcs⟩

end CFSG.RankThree.PartOne.K1320
