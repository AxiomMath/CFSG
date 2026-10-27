module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBSDefs
public import Certificates.Certificate1649001
public import Certificates.Certificate725008
import CFSG.LocalAnalysis.StandardType.GGQTwoSixPoint
import CFSG.LocalAnalysis.StandardType.GGQTwoSixGens
import CFSG.LocalAnalysis.StandardType.GGQTwoSixFarInputs
import CFSG.Certificates.Kernel.Misc.Coset.PGChain
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindowsChart

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem bs5_restrict_far :
    restrictWords (subsetOf 18 chart5) (relsP6 ()) = rels5 () := by
  have h : (farRels.filterMap (renumber (subsetOf 18 chart5))) = [] := by decide +kernel
  have h6 : relsP6 () = relsP ++ farRels := rfl
  rw [h6, rels5]
  change (relsP ++ farRels).filterMap (renumber (subsetOf 18 chart5)) =
    relsP.filterMap (renumber (subsetOf 18 chart5))
  rw [List.filterMap_append, h, List.append_nil]

private theorem bs5_card_P6
    (h5 : Finite (PG 14 (rels5 ())) ∧ Nat.card (PG 14 (rels5 ())) ≤ 528 * 25920)
    (h2016 : (genSub {r : FreeGroup (Fin 18) | r ∈ (relsP6 ()).map FreeGroup.mk}
        (subsetOf 18 chart5)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 18) | r ∈ (relsP6 ()).map FreeGroup.mk}
        (subsetOf 18 chart5)).index ≤ 2016) :
    Finite (PG 18 (relsP6 ())) ∧ Nat.card (PG 18 (relsP6 ())) ≤ 2016 * (528 * 25920) := by
  have h56 : rels5 () = restrictWords (subsetOf 18 chart5) (relsP6 ()) := bs5_restrict_far.symm
  have hr : Finite (PG (subsetOf 18 chart5).length
      (restrictWords (subsetOf 18 chart5) (relsP6 ()))) ∧ Nat.card (PG (subsetOf 18 chart5).length
      (restrictWords (subsetOf 18 chart5) (relsP6 ()))) ≤ 528 * 25920 := by
    rw [← h56]
    exact h5
  exact CFSG.KC.MiscCoset.card_le_of_index_restrict (relsP6 ()) (subsetOf 18 chart5) h2016 hr

private theorem bs5_nativeSu_farRels (hK : Nat.card K = 4) :
    ∀ w ∈ farRels, evalG (nativeSu hK) w = 1 := by
  intro w hw
  simp only [farRels, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (nativeSu_comm hK 10 (by decide) 16 (by decide))
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (nativeSu_comm hK 10 (by decide) 17 (by decide))
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (nativeSu_comm hK 11 (by decide) 16 (by decide))
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (nativeSu_comm hK 11 (by decide) 17 (by decide))

private theorem bs5_nativeSu_rels6 (hK : Nat.card K = 4) :
    ∀ w ∈ relsP6 (), evalG (nativeSu hK) w = 1 := by
  intro w hw
  have h6 : w ∈ relsP ++ farRels := hw
  rcases List.mem_append.mp h6 with hw | hw
  · exact nativeSu_rels hK w hw
  · exact bs5_nativeSu_farRels hK w hw

private noncomputable def bs5_ev6 (hK : Nat.card K = 4) :
    PG 18 (relsP6 ()) →* Su K 2 1 6 :=
  PresentedGroup.toGroup (f := nativeSu hK) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    simpa [FreeGroup.lift_mk, evalG] using bs5_nativeSu_rels6 hK w hw)

private theorem bs5_ev6_of (hK : Nat.card K = 4) (a : Fin 18) :
    bs5_ev6 hK (PresentedGroup.of a) = nativeSu hK a := by
  simp [bs5_ev6, PresentedGroup.toGroup.of]

private theorem bs5_ev6_surjective (hK : Nat.card K = 4) :
    Function.Surjective (bs5_ev6 hK) := by
  rw [← MonoidHom.range_eq_top]
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    (rels := {r : FreeGroup (Fin 18) | r ∈ (relsP6 ()).map FreeGroup.mk}), MonoidHom.map_closure,
    ← Set.range_comp]
  have : (bs5_ev6 hK) ∘ (PresentedGroup.of : Fin 18 → PG 18 (relsP6 ())) = nativeSu hK := by
    funext i
    exact bs5_ev6_of hK i
  rw [this]
  exact nativeSu_closure_top hK

private theorem bs5_ev6_bijective (hK : Nat.card K = 4) :
    Function.Bijective (bs5_ev6 hK) := by
  obtain ⟨hfin, hP⟩ := bs5_card_P6 Certificates.certificate1649001.2.1
    Certificates.certificate725008
  have : Finite (PG 18 (relsP6 ())) := hfin
  have hsurj := bs5_ev6_surjective hK
  have hsu : Nat.card (Su K 2 1 6) ≤ Nat.card (PG 18 (relsP6 ())) :=
    Nat.card_le_card_of_surjective _ hsurj
  rw [card_Su_six hK] at hsu
  refine (Nat.bijective_iff_surjective_and_card (bs5_ev6 hK)).mpr ⟨hsurj, ?_⟩
  rw [card_Su_six hK]
  omega

private noncomputable def bs5_e (hK : Nat.card K = 4) :
    PG 18 (relsP6 ()) ≃* Su K 2 1 6 :=
  MulEquiv.ofBijective (bs5_ev6 hK) (bs5_ev6_bijective hK)

variable {Y : Type} [Group Y]

private structure bs5_Charts (F : QTwoPhanFamily K Y 5) where
  φ : Fin 3 → Su K 2 1 4 →* Y
  two_zero : ∀ s : Fin 3, (φ s).comp (blockEmb K 2 1 4 2 0 (by norm_num)) = F.ι ⟨s.val, by omega⟩
  two_one : ∀ s : Fin 3, (φ s).comp (blockEmb K 2 1 4 2 1 (by norm_num)) =
    F.ι ⟨s.val + 1, by omega⟩
  two_two : ∀ s : Fin 3, (φ s).comp (blockEmb K 2 1 4 2 2 (by norm_num)) =
    F.ι ⟨s.val + 2, by omega⟩
  three_zero : ∀ s : Fin 3, (φ s).comp (blockEmb K 2 1 4 3 0 (by norm_num)) =
    F.θ ⟨s.val, by omega⟩
  three_one : ∀ s : Fin 3, (φ s).comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
    F.θ ⟨s.val + 1, by omega⟩

private theorem bs5_fin_succ_lt_of_lt {n : ℕ} (h : n < 4) :
    ((⟨n, by omega⟩ : Fin 5) : ℕ) + 1 < 5 := by
  change n + 1 < 5
  omega

private theorem bs5_fin_add_two_lt (s : Fin 3) :
    ((⟨s.val, by omega⟩ : Fin 5) : ℕ) + 2 < 5 := by
  change s.val + 2 < 5
  omega

private theorem bs5_fin_succ_lt (s : Fin 3) : ((⟨s.val, by omega⟩ : Fin 5) : ℕ) + 1 < 5 := by
  change s.val + 1 < 5
  omega

private theorem bs5_fin_succ_succ_lt (s : Fin 3) :
    ((⟨s.val + 1, by omega⟩ : Fin 5) : ℕ) + 1 < 5 := by
  change s.val + 1 + 1 < 5
  omega

private theorem bs5_charts_exists (F : QTwoPhanFamily K Y 5) : Nonempty (bs5_Charts F) := by
  choose Θ h0 h1 using fun s : Fin 3 =>
    F.four ⟨s.val, by have := s.isLt; omega⟩ (bs5_fin_add_two_lt s)
  have h2zero : ∀ s : Fin 3,
      (Θ s).comp (blockEmb K 2 1 4 2 0 (by norm_num)) = F.ι ⟨s.val, by omega⟩ := by
    intro s
    have hc : (blockEmb K 2 1 4 3 0 (by norm_num)).comp (blockEmb K 2 1 3 2 0 (by norm_num)) =
        blockEmb K 2 1 4 2 0 (by norm_num) := blockEmb_comp _ _
    rw [← hc, ← MonoidHom.comp_assoc, h0 s, ← embSUid_two_eq_blockEmb]
    exact F.left ⟨s.val, by omega⟩ (bs5_fin_succ_lt s)
  have h2one : ∀ s : Fin 3,
      (Θ s).comp (blockEmb K 2 1 4 2 1 (by norm_num)) = F.ι ⟨s.val + 1, by omega⟩ := by
    intro s
    have hc : (blockEmb K 2 1 4 3 0 (by norm_num)).comp (blockEmb K 2 1 3 2 1 (by norm_num)) =
        blockEmb K 2 1 4 2 1 (by norm_num) := blockEmb_comp _ _
    rw [← hc, ← MonoidHom.comp_assoc, h0 s, ← embSUid_zero_eq_blockEmb]
    exact F.right ⟨s.val, by omega⟩ (bs5_fin_succ_lt s)
  have h2two : ∀ s : Fin 3,
      (Θ s).comp (blockEmb K 2 1 4 2 2 (by norm_num)) = F.ι ⟨s.val + 2, by omega⟩ := by
    intro s
    have hc : (blockEmb K 2 1 4 3 1 (by norm_num)).comp (blockEmb K 2 1 3 2 1 (by norm_num)) =
        blockEmb K 2 1 4 2 2 (by norm_num) := blockEmb_comp _ _
    rw [← hc, ← MonoidHom.comp_assoc, h1 s, ← embSUid_zero_eq_blockEmb]
    exact F.right ⟨s.val + 1, by omega⟩ (bs5_fin_succ_succ_lt s)
  exact ⟨⟨Θ, h2zero, h2one, h2two, h0, h1⟩⟩

private theorem bs5_a01 {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) :
    ∀ x : Su K 2 1 3, C.φ 0 (qTwoSixWin_left (K := K) x) =
      C.φ 1 (qTwoSixWin_right (K := K) x) := by
  intro x
  refine (DFunLike.congr_fun (C.three_one 0) x).trans ?_
  exact (DFunLike.congr_fun (C.three_zero 1) x).symm

private theorem bs5_a12 {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) :
    ∀ x : Su K 2 1 3, C.φ 1 (qTwoSixWin_left (K := K) x) =
      C.φ 2 (qTwoSixWin_right (K := K) x) := by
  intro x
  refine (DFunLike.congr_fun (C.three_one 1) x).trans ?_
  exact (DFunLike.congr_fun (C.three_zero 2) x).symm

private theorem bs5_mem_univ_map {i k : ℕ} (h : i + k ≤ 6) (a : Fin 6) :
    a ∈ (Finset.univ.map (qTwoSixWinEmb h) : Finset (Fin 6)) ↔ i ≤ a.val ∧ a.val < i + k := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, -, rfl⟩
    rw [qTwoSixWinEmb_val]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨a.val - i, by omega⟩, Finset.mem_univ _, ?_⟩
    ext
    rw [qTwoSixWinEmb_val]
    change a.val - i + i = a.val
    omega

private theorem bs5_support_bounds_low (i : Fin 18) (hi : i.val < 10) (a : Fin 6)
    (ha : a ∈ qTwoSixData_support i) : i.val / 2 ≤ a.val ∧ a.val < i.val / 2 + 2 := by
  have h : ∀ i : Fin 18, i.val < 10 → ∀ a : Fin 6, a ∈ qTwoSixData_support i →
      i.val / 2 ≤ a.val ∧ a.val < i.val / 2 + 2 := by decide +kernel
  exact h i hi a ha

private theorem bs5_support_bounds_high (i : Fin 18) (hi : 10 ≤ i.val) (a : Fin 6)
    (ha : a ∈ qTwoSixData_support i) :
    (i.val - 10) / 2 ≤ a.val ∧ a.val < (i.val - 10) / 2 + 3 := by
  have h : ∀ i : Fin 18, 10 ≤ i.val → ∀ a : Fin 6, a ∈ qTwoSixData_support i →
      (i.val - 10) / 2 ≤ a.val ∧ a.val < (i.val - 10) / 2 + 3 := by decide +kernel
  exact h i hi a ha

private theorem bs5_support_card_high (i : Fin 18) (hi : 10 ≤ i.val) :
    (qTwoSixData_support i).card = 3 := by
  have h : ∀ i : Fin 18, 10 ≤ i.val → (qTwoSixData_support i).card = 3 := by decide +kernel
  exact h i hi

private theorem bs5_low_low (a b : Fin 18) (ha : a.val < 10) (hb : b.val < 10)
    (hd : Disjoint (qTwoSixData_support a) (qTwoSixData_support b)) :
    a.val / 2 + 1 < b.val / 2 ∨ b.val / 2 + 1 < a.val / 2 := by
  have h : ∀ a b : Fin 18, a.val < 10 → b.val < 10 →
      Disjoint (qTwoSixData_support a) (qTwoSixData_support b) →
      a.val / 2 + 1 < b.val / 2 ∨ b.val / 2 + 1 < a.val / 2 := by decide +kernel
  exact h a b ha hb hd

private theorem bs5_low_high (a b : Fin 18) (ha : a.val < 10) (hb : 10 ≤ b.val)
    (hd : Disjoint (qTwoSixData_support a) (qTwoSixData_support b)) :
    a.val / 2 + 1 < (b.val - 10) / 2 ∨ (b.val - 10) / 2 + 2 < a.val / 2 := by
  have h : ∀ a b : Fin 18, a.val < 10 → 10 ≤ b.val →
      Disjoint (qTwoSixData_support a) (qTwoSixData_support b) →
      a.val / 2 + 1 < (b.val - 10) / 2 ∨ (b.val - 10) / 2 + 2 < a.val / 2 := by
    decide +kernel
  exact h a b ha hb hd

private theorem bs5_native_mem_low (hK : Nat.card K = 4) (i : Fin 18) (hi : i.val < 10) :
    nativeSu hK i ∈ (blockEmb K 2 1 6 2 (i.val / 2) (by omega)).range := by
  rw [qTwoSixWin_range]
  refine qTwoS34_coordBlockSU_mono ?_ (qTwoSixData_native_mem hK i)
  intro a ha
  rw [bs5_mem_univ_map]
  exact bs5_support_bounds_low i hi a ha

private theorem bs5_native_mem_high (hK : Nat.card K = 4) (i : Fin 18) (hi : 10 ≤ i.val) :
    nativeSu hK i ∈ (blockEmb K 2 1 6 3 ((i.val - 10) / 2) (by omega)).range := by
  rw [qTwoSixWin_range]
  refine qTwoS34_coordBlockSU_mono ?_ (qTwoSixData_native_mem hK i)
  intro a ha
  rw [bs5_mem_univ_map]
  exact bs5_support_bounds_high i hi a ha

private theorem bs5_g_value {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) {hK : Nat.card K = 4}
    {s : Fin 3} {i : Fin 18} (hin : qTwoSixData_inWindow s i)
    {l : ℕ} {μ : Su K 2 1 l →* Y} (c : ℕ) (hc : c + l ≤ 4) (h4 : s.val + c + l ≤ 6)
    (hφc : (C.φ s).comp (blockEmb K 2 1 4 l c hc) = μ)
    {x : Su K 2 1 l} (hx : blockEmb K 2 1 6 l (s.val + c) h4 x = nativeSu hK i) :
    qTwoSixWin_g hK C.φ i = μ x := by
  have hlift := qTwoSixWin_lift_eq hK s i (qTwoSixWin_hs s) hin
  have hcomp : blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s)
      (blockEmb K 2 1 4 l c hc x) = nativeSu hK i := by
    rw [blockEmb_comp_apply]
    exact hx
  have heq : qTwoSixWin_lift hK s i = blockEmb K 2 1 4 l c hc x :=
    blockEmb_injective (qTwoSixWin_hs s) (hlift.trans hcomp.symm)
  rw [qTwoSixWin_g_eq hK (bs5_a01 C) (bs5_a12 C) s i hin, heq]
  exact DFunLike.congr_fun hφc x

private theorem bs5_value_low {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) {hK : Nat.card K = 4}
    (i : Fin 18) (hi : i.val < 10) (h5 : i.val / 2 < 5) (h2 : i.val / 2 + 2 ≤ 6)
    (x : Su K 2 1 2) (hx : blockEmb K 2 1 6 2 (i.val / 2) h2 x = nativeSu hK i) :
    qTwoSixWin_g hK C.φ i = F.ι ⟨i.val / 2, h5⟩ x := by
  fin_cases i
  · exact bs5_g_value C (s := 0) (i := 0) (c := 0) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_zero 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 1) (c := 0) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_zero 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 2) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_one 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 3) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_one 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 4) (c := 2) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_two 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 5) (c := 2) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_two 0) (hx := hx)
  · exact bs5_g_value C (s := 1) (i := 6) (c := 2) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_two 1) (hx := hx)
  · exact bs5_g_value C (s := 1) (i := 7) (c := 2) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_two 1) (hx := hx)
  · exact bs5_g_value C (s := 2) (i := 8) (c := 2) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_two 2) (hx := hx)
  · exact bs5_g_value C (s := 2) (i := 9) (c := 2) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.two_two 2) (hx := hx)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)

private theorem bs5_value_high {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    {hK : Nat.card K = 4} (i : Fin 18) (hi : 10 ≤ i.val) (h5 : (i.val - 10) / 2 < 5)
    (h3 : (i.val - 10) / 2 + 3 ≤ 6) (x : Su K 2 1 3)
    (hx : blockEmb K 2 1 6 3 ((i.val - 10) / 2) h3 x = nativeSu hK i) :
    qTwoSixWin_g hK C.φ i = F.θ ⟨(i.val - 10) / 2, h5⟩ x := by
  fin_cases i
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact bs5_g_value C (s := 0) (i := 10) (c := 0) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_zero 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 11) (c := 0) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_zero 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 12) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_one 0) (hx := hx)
  · exact bs5_g_value C (s := 0) (i := 13) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_one 0) (hx := hx)
  · exact bs5_g_value C (s := 1) (i := 14) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_one 1) (hx := hx)
  · exact bs5_g_value C (s := 1) (i := 15) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_one 1) (hx := hx)
  · exact bs5_g_value C (s := 2) (i := 16) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_one 2) (hx := hx)
  · exact bs5_g_value C (s := 2) (i := 17) (c := 1) (hin := by decide +kernel)
      (hc := by norm_num) (h4 := by norm_num) (hφc := by simpa using C.three_one 2) (hx := hx)

private theorem bs5_mem_low {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    {hK : Nat.card K = 4} (i : Fin 18) (hi : i.val < 10) :
    qTwoSixWin_g hK C.φ i ∈ (F.ι ⟨i.val / 2, by omega⟩).range := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (bs5_native_mem_low hK i hi)
  exact ⟨x, (bs5_value_low C i hi (by omega) (by omega) x hx).symm⟩

private theorem bs5_mem_high {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    {hK : Nat.card K = 4} (i : Fin 18) (hi : 10 ≤ i.val) :
    qTwoSixWin_g hK C.φ i ∈ (F.θ ⟨(i.val - 10) / 2, by omega⟩).range := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK i hi)
  exact ⟨x, (bs5_value_high C i hi (by omega) (by omega) x hx).symm⟩

private theorem bs5_comm (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    (a b : Fin 18) (hd : Disjoint (qTwoSixData_support a) (qTwoSixData_support b))
    (hc : (qTwoSixData_support a ∪ qTwoSixData_support b).card ≤ 5) :
    Commute (qTwoSixWin_g hK C.φ a) (qTwoSixWin_g hK C.φ b) := by
  by_cases ha : a.val < 10
  · by_cases hb : b.val < 10
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (bs5_mem_low C a ha)
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (bs5_mem_low C b hb)
      rw [← hx, ← hy]
      rcases bs5_low_low a b ha hb hd with hlt | hlt
      · exact F.comm ⟨a.val / 2, by omega⟩ ⟨b.val / 2, by omega⟩ hlt x y
      · exact (F.comm ⟨b.val / 2, by omega⟩ ⟨a.val / 2, by omega⟩ hlt y x).symm
    · have hb10 : 10 ≤ b.val := by omega
      have hj := bs5_fin_succ_lt_of_lt (n := (b.val - 10) / 2) (by omega)
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (bs5_mem_low C a ha)
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (bs5_mem_high C b hb10)
      rw [← hx, ← hy]
      exact F.farNodeEdge ⟨a.val / 2, by omega⟩ ⟨(b.val - 10) / 2, by omega⟩
        hj (bs5_low_high a b ha hb10 hd) x y
  · have ha10 : 10 ≤ a.val := by omega
    by_cases hb : b.val < 10
    · have hj := bs5_fin_succ_lt_of_lt (n := (a.val - 10) / 2) (by omega)
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (bs5_mem_low C b hb)
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (bs5_mem_high C a ha10)
      rw [← hx, ← hy]
      exact (F.farNodeEdge ⟨b.val / 2, by omega⟩ ⟨(a.val - 10) / 2, by omega⟩
        hj (bs5_low_high b a hb ha10 hd.symm) y x).symm
    · have hb10 : 10 ≤ b.val := by omega
      have hcard := Finset.card_union_of_disjoint hd
      have h3a := bs5_support_card_high a ha10
      have h3b := bs5_support_card_high b hb10
      omega

private theorem bs5_relsP (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) :
    ∀ w ∈ relsP, evalG (qTwoSixWin_g hK C.φ) w = 1 :=
  qTwoSixRels_evalG_eq_one_data
    (fun s => blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s)) qTwoSixWin_emb_injective
    (nativeSu hK) (nativeSu_rels hK) (qTwoSixWin_lift hK)
    (fun s i hin => qTwoSixWin_lift_eq hK s i (qTwoSixWin_hs s) hin)
    (qTwoSixWin_g hK C.φ) C.φ
    (fun s i hin => qTwoSixWin_g_eq hK (bs5_a01 C) (bs5_a12 C) s i hin)
    (fun a b hd hc => bs5_comm hK C a b hd hc)

private theorem bs5_comm_end (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    {a b : Fin 18} (ha : qTwoSixWin_g hK C.φ a ∈ (F.θ 0).range)
    (hb : qTwoSixWin_g hK C.φ b ∈ (F.θ 3).range) :
    Commute (qTwoSixWin_g hK C.φ a) (qTwoSixWin_g hK C.φ b) := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hb
  rw [← hx, ← hy]
  exact F.farEdgeEdge 0 3 (by norm_num) (by norm_num) x y

private theorem bs5_farRels (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) :
    ∀ w ∈ farRels, evalG (qTwoSixWin_g hK C.φ) w = 1 := by
  intro w hw
  simp only [farRels, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (bs5_comm_end hK C
      (bs5_mem_high C 10 (by decide)) (bs5_mem_high C 16 (by decide)))
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (bs5_comm_end hK C
      (bs5_mem_high C 10 (by decide)) (bs5_mem_high C 17 (by decide)))
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (bs5_comm_end hK C
      (bs5_mem_high C 11 (by decide)) (bs5_mem_high C 16 (by decide)))
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (bs5_comm_end hK C
      (bs5_mem_high C 11 (by decide)) (bs5_mem_high C 17 (by decide)))

private theorem bs5_rels6 (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) :
    ∀ w ∈ relsP6 (), evalG (qTwoSixWin_g hK C.φ) w = 1 := by
  intro w hw
  have h6 : w ∈ relsP ++ farRels := hw
  rcases List.mem_append.mp h6 with hw | hw
  · exact bs5_relsP hK C w hw
  · exact bs5_farRels hK C w hw

private noncomputable def bs5_Pg (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5}
    (C : bs5_Charts F) : PG 18 (relsP6 ()) →* Y :=
  PresentedGroup.toGroup (f := qTwoSixWin_g hK C.φ) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    simpa [FreeGroup.lift_mk, evalG] using bs5_rels6 hK C w hw)

private theorem bs5_Pg_of (hK : Nat.card K = 4) {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    (a : Fin 18) : bs5_Pg hK C (PresentedGroup.of a) = qTwoSixWin_g hK C.φ a := by
  simp [bs5_Pg, PresentedGroup.toGroup.of]

private noncomputable def bs5_psi (hK : Nat.card K = 4)
    {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) :
    Su K 2 1 6 →* Y :=
  (bs5_Pg hK C).comp (bs5_e hK).symm.toMonoidHom

private theorem bs5_psi_native (hK : Nat.card K = 4)
    {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F) (a : Fin 18) :
    bs5_psi hK C (nativeSu hK a) = qTwoSixWin_g hK C.φ a := by
  have h1 : (bs5_e hK) (PresentedGroup.of a) = nativeSu hK a := by
    rw [bs5_e, MulEquiv.ofBijective_apply]
    exact bs5_ev6_of hK a
  have h2 : (bs5_e hK).symm.toMonoidHom (nativeSu hK a) = PresentedGroup.of a := by
    rw [← h1]
    change (bs5_e hK).symm ((bs5_e hK) (PresentedGroup.of a)) = PresentedGroup.of a
    exact MulEquiv.symm_apply_apply (bs5_e hK) _
  rw [bs5_psi, MonoidHom.comp_apply, h2, bs5_Pg_of]

private theorem bs5_gen_pair (hK : Nat.card K = 4) (a b : Fin 18) (q : Fin 5)
    (hq6 : (q : ℕ) + 3 ≤ 6)
    (hnodup : (qTwoSixGen_pattern.map (fun p => evalNative (qTwoSixGen_word a b p))).Nodup)
    (x y : Su K 2 1 3) (hx : blockEmb K 2 1 6 3 q.val hq6 x = nativeSu hK a)
    (hy : blockEmb K 2 1 6 3 q.val hq6 y = nativeSu hK b) :
    Subgroup.closure ({x, y} : Set (Su K 2 1 3)) = ⊤ := by
  have ha : nativeSu hK a ∈ (blockEmb K 2 1 6 3 q.val hq6).range :=
    MonoidHom.mem_range.mpr ⟨x, hx⟩
  have hb : nativeSu hK b ∈ (blockEmb K 2 1 6 3 q.val hq6).range :=
    MonoidHom.mem_range.mpr ⟨y, hy⟩
  have hJ : (Finset.univ.map (qTwoSixWinEmb hq6)).card = 3 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hrange : (blockEmb K 2 1 6 3 q.val hq6).range =
      coordBlockSU K 2 1 (Finset.univ.map (qTwoSixWinEmb hq6)) := qTwoSixWin_range hq6
  have hblock := qTwoSixGen_block_le_of_mem hK hJ a b hnodup
    (by rw [← hrange]; exact ha) (by rw [← hrange]; exact hb)
    (G := Subgroup.closure ({nativeSu hK a, nativeSu hK b} : Set (Su K 2 1 6)))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hmap : (Subgroup.closure ({x, y} : Set (Su K 2 1 3))).map
      (blockEmb K 2 1 6 3 q.val hq6) = (blockEmb K 2 1 6 3 q.val hq6).range := by
    have himg : (blockEmb K 2 1 6 3 q.val hq6) '' ({x, y} : Set (Su K 2 1 3)) =
        ({nativeSu hK a, nativeSu hK b} : Set (Su K 2 1 6)) := by
      rw [Set.image_pair, hx, hy]
    rw [MonoidHom.map_closure, himg]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact ha
      · rw [hz]; exact hb
    · intro z hz
      rw [hrange] at hz
      exact hblock hz
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : blockEmb K 2 1 6 3 q.val hq6 z ∈
      (Subgroup.closure ({x, y} : Set (Su K 2 1 3))).map
        (blockEmb K 2 1 6 3 q.val hq6) := by
    rw [hmap]
    exact ⟨z, rfl⟩
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
  have hwz' : w = z := blockEmb_injective hq6 hwz
  rwa [hwz'] at hw

private theorem bs5_psi_block3_of (hK : Nat.card K = 4)
    {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    (q : Fin 5) (hq6 : (q : ℕ) + 3 ≤ 6) {a b : Fin 18}
    (x y : Su K 2 1 3) (hx : blockEmb K 2 1 6 3 q.val hq6 x = nativeSu hK a)
    (hy : blockEmb K 2 1 6 3 q.val hq6 y = nativeSu hK b)
    (hgen : Subgroup.closure ({x, y} : Set (Su K 2 1 3)) = ⊤)
    (hxa : qTwoSixWin_g hK C.φ a = F.θ q x) (hyb : qTwoSixWin_g hK C.φ b = F.θ q y) :
    (bs5_psi hK C).comp (blockEmb K 2 1 6 3 q.val hq6) = F.θ q := by
  have hxval : bs5_psi hK C (blockEmb K 2 1 6 3 q.val hq6 x) = F.θ q x := by
    rw [hx, bs5_psi_native]
    exact hxa
  have hyval : bs5_psi hK C (blockEmb K 2 1 6 3 q.val hq6 y) = F.θ q y := by
    rw [hy, bs5_psi_native]
    exact hyb
  refine MonoidHom.eq_of_eqOn_dense hgen ?_
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz
  · rw [hz]; exact hxval
  · rw [hz]; exact hyval

private theorem bs5_psi_block3 (hK : Nat.card K = 4)
    {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    (q : Fin 5) (hq : (q : ℕ) + 1 < 5) (hq6 : (q : ℕ) + 3 ≤ 6) :
    (bs5_psi hK C).comp (blockEmb K 2 1 6 3 q.val hq6) = F.θ q := by
  fin_cases q
  · have h6 : (0 : ℕ) + 3 ≤ 6 := by norm_num
    obtain ⟨x, hx₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 10 (by decide))
    obtain ⟨y, hy₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 11 (by decide))
    have hx : blockEmb K 2 1 6 3 0 h6 x = nativeSu hK 10 := hx₀
    have hy : blockEmb K 2 1 6 3 0 h6 y = nativeSu hK 11 := hy₀
    have hgen := bs5_gen_pair hK 10 11 0 h6 qTwoSixGen_nodup012 x y hx hy
    exact bs5_psi_block3_of hK C 0 h6 x y hx hy hgen
      (bs5_value_high C 10 (by decide) (by norm_num) (by norm_num) x hx)
      (bs5_value_high C 11 (by decide) (by norm_num) (by norm_num) y hy)
  · have h6 : (1 : ℕ) + 3 ≤ 6 := by norm_num
    obtain ⟨x, hx₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 12 (by decide))
    obtain ⟨y, hy₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 13 (by decide))
    have hx : blockEmb K 2 1 6 3 1 h6 x = nativeSu hK 12 := hx₀
    have hy : blockEmb K 2 1 6 3 1 h6 y = nativeSu hK 13 := hy₀
    have hgen := bs5_gen_pair hK 12 13 1 h6 qTwoSixGen_nodup123 x y hx hy
    exact bs5_psi_block3_of hK C 1 h6 x y hx hy hgen
      (bs5_value_high C 12 (by decide) (by norm_num) (by norm_num) x hx)
      (bs5_value_high C 13 (by decide) (by norm_num) (by norm_num) y hy)
  · have h6 : (2 : ℕ) + 3 ≤ 6 := by norm_num
    obtain ⟨x, hx₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 14 (by decide))
    obtain ⟨y, hy₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 15 (by decide))
    have hx : blockEmb K 2 1 6 3 2 h6 x = nativeSu hK 14 := hx₀
    have hy : blockEmb K 2 1 6 3 2 h6 y = nativeSu hK 15 := hy₀
    have hgen := bs5_gen_pair hK 14 15 2 h6 qTwoSixGen_nodup234 x y hx hy
    exact bs5_psi_block3_of hK C 2 h6 x y hx hy hgen
      (bs5_value_high C 14 (by decide) (by norm_num) (by norm_num) x hx)
      (bs5_value_high C 15 (by decide) (by norm_num) (by norm_num) y hy)
  · have h6 : (3 : ℕ) + 3 ≤ 6 := by norm_num
    obtain ⟨x, hx₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 16 (by decide))
    obtain ⟨y, hy₀⟩ := MonoidHom.mem_range.mp (bs5_native_mem_high hK 17 (by decide))
    have hx : blockEmb K 2 1 6 3 3 h6 x = nativeSu hK 16 := hx₀
    have hy : blockEmb K 2 1 6 3 3 h6 y = nativeSu hK 17 := hy₀
    have hgen := bs5_gen_pair hK 16 17 3 h6 qTwoSixGensGen_nodup345 x y hx hy
    exact bs5_psi_block3_of hK C 3 h6 x y hx hy hgen
      (bs5_value_high C 16 (by decide) (by norm_num) (by norm_num) x hx)
      (bs5_value_high C 17 (by decide) (by norm_num) (by norm_num) y hy)
  · exact absurd hq (by decide)

private theorem bs5_psi_block2 (hK : Nat.card K = 4)
    {F : QTwoPhanFamily K Y 5} (C : bs5_Charts F)
    (p : Fin 5) (hp2 : (p : ℕ) + 2 ≤ 6) :
    (bs5_psi hK C).comp (blockEmb K 2 1 6 2 p.val hp2) = F.ι p := by
  fin_cases p
  · have h6 : (0 : ℕ) + 3 ≤ 6 := by norm_num
    have hq : ((0 : Fin 5) : ℕ) + 1 < 5 := by norm_num
    have hc2 : (0 : ℕ) + 2 ≤ 3 := by norm_num
    have hb : blockEmb K 2 1 6 2 0 hp2 =
        (blockEmb K 2 1 6 3 0 h6).comp (embSUid (unitaryInvolution K 2 1) 2) := by
      rw [embSUid_two_eq_blockEmb]
      exact (blockEmb_comp (h₁ := h6) (h₂ := hc2)).symm
    have h3 : (bs5_psi hK C).comp (blockEmb K 2 1 6 3 0 h6) = F.θ 0 :=
      bs5_psi_block3 hK C 0 hq h6
    rw [hb, ← MonoidHom.comp_assoc, h3]
    exact F.left 0 hq
  · have h6 : (0 : ℕ) + 3 ≤ 6 := by norm_num
    have hq : ((0 : Fin 5) : ℕ) + 1 < 5 := by norm_num
    have hc2 : (1 : ℕ) + 2 ≤ 3 := by norm_num
    have hb : blockEmb K 2 1 6 2 1 hp2 =
        (blockEmb K 2 1 6 3 0 h6).comp (embSUid (unitaryInvolution K 2 1) 0) := by
      rw [embSUid_zero_eq_blockEmb]
      exact (blockEmb_comp (h₁ := h6) (h₂ := hc2)).symm
    have h3 : (bs5_psi hK C).comp (blockEmb K 2 1 6 3 0 h6) = F.θ 0 :=
      bs5_psi_block3 hK C 0 hq h6
    rw [hb, ← MonoidHom.comp_assoc, h3]
    exact F.right 0 hq
  · have h6 : (1 : ℕ) + 3 ≤ 6 := by norm_num
    have hq : ((1 : Fin 5) : ℕ) + 1 < 5 := by norm_num
    have hc2 : (1 : ℕ) + 2 ≤ 3 := by norm_num
    have hb : blockEmb K 2 1 6 2 2 hp2 =
        (blockEmb K 2 1 6 3 1 h6).comp (embSUid (unitaryInvolution K 2 1) 0) := by
      rw [embSUid_zero_eq_blockEmb]
      exact (blockEmb_comp (h₁ := h6) (h₂ := hc2)).symm
    have h3 : (bs5_psi hK C).comp (blockEmb K 2 1 6 3 1 h6) = F.θ 1 :=
      bs5_psi_block3 hK C 1 hq h6
    rw [hb, ← MonoidHom.comp_assoc, h3]
    exact F.right 1 hq
  · have h6 : (2 : ℕ) + 3 ≤ 6 := by norm_num
    have hq : ((2 : Fin 5) : ℕ) + 1 < 5 := by norm_num
    have hc2 : (1 : ℕ) + 2 ≤ 3 := by norm_num
    have hb : blockEmb K 2 1 6 2 3 hp2 =
        (blockEmb K 2 1 6 3 2 h6).comp (embSUid (unitaryInvolution K 2 1) 0) := by
      rw [embSUid_zero_eq_blockEmb]
      exact (blockEmb_comp (h₁ := h6) (h₂ := hc2)).symm
    have h3 : (bs5_psi hK C).comp (blockEmb K 2 1 6 3 2 h6) = F.θ 2 :=
      bs5_psi_block3 hK C 2 hq h6
    rw [hb, ← MonoidHom.comp_assoc, h3]
    exact F.right 2 hq
  · have h6 : (3 : ℕ) + 3 ≤ 6 := by norm_num
    have hq : ((3 : Fin 5) : ℕ) + 1 < 5 := by norm_num
    have hc2 : (1 : ℕ) + 2 ≤ 3 := by norm_num
    have hb : blockEmb K 2 1 6 2 4 hp2 =
        (blockEmb K 2 1 6 3 3 h6).comp (embSUid (unitaryInvolution K 2 1) 0) := by
      rw [embSUid_zero_eq_blockEmb]
      exact (blockEmb_comp (h₁ := h6) (h₂ := hc2)).symm
    have h3 : (bs5_psi hK C).comp (blockEmb K 2 1 6 3 3 h6) = F.θ 3 :=
      bs5_psi_block3 hK C 3 hq h6
    rw [hb, ← MonoidHom.comp_assoc, h3]
    exact F.right 3 hq

end CFSG.StandardType.QTwo.SixPoint

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.StandardType.QTwo.SixPoint

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoPhanUniversalAt_five
    (hK : Nat.card K = 4) : QTwoPhanUniversalAt K 5 := by
  intro Y _ F
  obtain ⟨C⟩ := bs5_charts_exists (K := K) F
  refine ⟨bs5_psi hK C, fun i => ?_, fun i h => ?_⟩
  · exact bs5_psi_block2 hK C i (by have := i.isLt; omega)
  · exact bs5_psi_block3 hK C i h (by have := i.isLt; omega)

end CFSG.StandardType.QTwo

end
