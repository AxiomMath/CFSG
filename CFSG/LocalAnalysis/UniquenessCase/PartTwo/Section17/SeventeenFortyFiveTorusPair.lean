module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStep
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
public import CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow.IntermediateSylow
import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIIStep4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s17_45_relIndex_inf_normalizer_eq_two {D : Data G} {L : Subgroup G}
    (hc2 : (conjSetOf D.M L).ncard = 2) :
    (D.M ⊓ normalizer (L : Set G)).relIndex D.M = 2 :=
  (CFSG.GH74.QTGen4.DSGen4.dss24_ncard_conj_orbit D.M L).symm.trans hc2

theorem s17_45_normal_subgroupOf_inf_normalizer {D : Data G} {L : Subgroup G}
    (hc2 : (conjSetOf D.M L).ncard = 2) :
    ((D.T ⊓ normalizer (L : Set G)).subgroupOf D.T).Normal := by
  classical
  let NM : Subgroup G := D.M ⊓ normalizer (L : Set G)
  let T1 : Subgroup G := D.T ⊓ normalizer (L : Set G)
  have hidx : NM.relIndex D.M = 2 := s17_45_relIndex_inf_normalizer_eq_two hc2
  have hNMnormal : D.M ≤ normalizer (NM : Set G) := by
    have hsub : (NM.subgroupOf D.M).Normal := Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : NM ≤ D.M)).1 hsub
  have hT1T : T1 ≤ D.T := inf_le_left
  have hT1eq : T1 = D.T ⊓ NM := by
    rw [show T1 = D.T ⊓ normalizer (L : Set G) from rfl]
    show D.T ⊓ normalizer (L : Set G) = D.T ⊓ (D.M ⊓ normalizer (L : Set G))
    rw [← inf_assoc, inf_eq_left.mpr D.sylowM.le]
  have hT1norm : D.T ≤ normalizer (T1 : Set G) := by
    have hTN : D.T ≤ normalizer (NM : Set G) := D.sylowM.le.trans hNMnormal
    have h := (le_inf (Subgroup.le_normalizer (H := D.T)) hTN).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    simpa [hT1eq] using h
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hT1T).2 hT1norm

theorem exists_inPStar_of_pair {D : Data G} {V₀ L : Subgroup G} (hL : L ∈ calC D.M)
    {x : G} (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : conjClosure D.M L ≠ L)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M)
    {A : Subgroup G} (hAL : A ≤ L) (hAcard : Nat.card A = r)
    (hAN : A ≤ normalizer ((D.T ⊓ normalizer (L : Set G) : Subgroup G) : Set G))
    (hZ : Subgroup.center (Bar2 L) = ⊥) :
    ∃ E : Subgroup G, InPStar D V₀ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hK
  set T1 : Subgroup G := D.T ⊓ normalizer (L : Set G) with hT1
  have hc2 : (conjSetOf D.M L).ncard = 2 := ncard_eq_two_of_p42 hL hxM hXsup hne
  obtain ⟨hKcalM, hKne⟩ := conjSubgroup_mem_calC_and_ne hL hxM hXsup hne
  have hLK : L ≠ K := hKne.symm
  have hLmem : L ∈ conjSetOf D.M L := self_mem_conjSetOf D.M L
  have hKmem : K ∈ conjSetOf D.M L := ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  have hpairset : conjSetOf D.M L = {L, K} := by
    have hne' : L.map (MulAut.conj x⁻¹).toMonoidHom ≠ L := by
      intro h
      exact hKne h
    have h := uc22p22d_conjSet_pair (M := D.M) (K := L) (t := x⁻¹)
      (D.M.inv_mem hxM) hne' hc2
    simpa [hK, CFSG.Quasithin.conjSubgroup] using h
  let NM : Subgroup G := D.M ⊓ normalizer (L : Set G)
  letI : MulAction ↥D.M (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp D.M.subtype)
  have hsmulM : ∀ m : ↥D.M, m • L = L.map (MulAut.conj (m : G)).toMonoidHom := by
    intro m
    show (MulAut.conj (m : G)) • L = L.map (MulAut.conj (m : G)).toMonoidHom
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hstabM : MulAction.stabilizer ↥D.M L = NM.subgroupOf D.M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, hsmulM, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    simp
  have horbM : MulAction.orbit ↥D.M L = conjSetOf D.M L := by
    ext K'
    constructor
    · intro h
      rw [MulAction.mem_orbit_iff] at h
      obtain ⟨m, hm⟩ := h
      rw [hsmulM] at hm
      exact ⟨m, m.2, hm.symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, hsmulM ⟨m, hm⟩⟩
  have hidxM : NM.relIndex D.M = 2 := by
    have h := MulAction.index_stabilizer (G := ↥D.M) (x := L)
    rw [horbM, hc2] at h
    rwa [hstabM] at h
  have hNMnormal : D.M ≤ normalizer (NM : Set G) := by
    have hsub : (NM.subgroupOf D.M).Normal := Subgroup.normal_of_index_eq_two hidxM
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : NM ≤ D.M)).1 hsub
  have hT1eq : T1 = D.T ⊓ NM := by
    rw [hT1]
    show D.T ⊓ normalizer (L : Set G) = D.T ⊓ (D.M ⊓ normalizer (L : Set G))
    rw [← inf_assoc, inf_eq_left.mpr D.sylowM.le]
  have hT1T : T1 ≤ D.T := by rw [hT1]; exact inf_le_left
  have hT1T2 : IsPGroup 2 ↥T1 := D.sylowM.isPGroup.to_le hT1T
  have hT1norm : D.T ≤ normalizer (T1 : Set G) := by
    have hTN : D.T ≤ normalizer (NM : Set G) := D.sylowM.le.trans hNMnormal
    have h := (le_inf (Subgroup.le_normalizer (H := D.T)) hTN).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    simpa [hT1eq] using h
  letI : MulAction ↥D.T (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp D.T.subtype)
  have hsmulT : ∀ t : ↥D.T, t • L = L.map (MulAut.conj (t : G)).toMonoidHom := by
    intro t
    show (MulAut.conj (t : G)) • L = L.map (MulAut.conj (t : G)).toMonoidHom
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hstabT : MulAction.stabilizer ↥D.T L = T1.subgroupOf D.T := by
    ext t
    rw [MulAction.mem_stabilizer_iff, hsmulT, Subgroup.mem_subgroupOf, hT1, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    simp
  have hTnotN : ¬ D.T ≤ normalizer (L : Set G) := by
    intro h
    exact (uc22p22a_not_two_dvd_ncard (K := L) D.sylowM h) (by simpa [hc2] using dvd_refl 2)
  have horbTcard : (MulAction.orbit ↥D.T L).ncard = 2 := by
    have hsub : MulAction.orbit ↥D.T L ⊆ conjSetOf D.M L := by
      rintro K' ⟨t, ht⟩
      change t • L = K' at ht
      rw [hsmulT] at ht
      exact ⟨t, D.sylowM.le t.2, ht.symm⟩
    have hle : (MulAction.orbit ↥D.T L).ncard ≤ 2 := by
      rw [← hc2]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hne1 : (MulAction.orbit ↥D.T L).ncard ≠ 1 := by
      intro h1
      apply hTnotN
      intro t ht
      have hidx : (MulAction.stabilizer ↥D.T L).index = 1 := by
        have h := MulAction.index_stabilizer (G := ↥D.T) (x := L)
        rwa [h1] at h
      have htop : MulAction.stabilizer ↥D.T L = ⊤ := Subgroup.index_eq_one.mp hidx
      have hmem : (⟨t, ht⟩ : ↥D.T) ∈ MulAction.stabilizer ↥D.T L := by
        rw [htop]; exact Subgroup.mem_top _
      have hmemN : t ∈ normalizer (L : Set G) := by
        have h := Subgroup.mem_subgroupOf.mp (hstabT ▸ hmem)
        rw [hT1, Subgroup.mem_inf] at h
        simpa using h.2
      exact hmemN
    have hpos : 0 < (MulAction.orbit ↥D.T L).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨L, MulAction.mem_orbit_self L⟩
    omega
  have hT1rel : T1.relIndex D.T = 2 := by
    have h := MulAction.index_stabilizer (G := ↥D.T) (x := L)
    rw [horbTcard] at h
    rwa [hstabT] at h
  obtain ⟨u, huT, huT1, hcover⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hT1rel
  have huN : u ∉ normalizer (L : Set G) := by
    intro h
    exact huT1 (by rw [hT1]; exact Subgroup.mem_inf.mpr ⟨huT, h⟩)
  have hLu : L.map (MulAut.conj u).toMonoidHom = K := by
    have hmem : L.map (MulAut.conj u).toMonoidHom ∈ conjSetOf D.M L :=
      ⟨u, D.sylowM.le huT, rfl⟩
    rw [hpairset] at hmem
    rcases hmem with h | h
    · exact absurd h (fun h' => huN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h'))
    · exact h
  have hu2 : u ^ 2 ∈ T1 := by
    have h : (⟨u, huT⟩ : ↥D.T) ^ 2 ∈ T1.subgroupOf D.T :=
      Subgroup.sq_mem_of_index_two (H := T1.subgroupOf D.T) hT1rel ⟨u, huT⟩
    simpa [pow_two] using (Subgroup.mem_subgroupOf.mp h)
  set v : G := u⁻¹ with hv
  have hvT : v ∈ D.T := D.T.inv_mem huT
  have hvT1 : v ∉ T1 := by
    intro h
    exact huT1 (by simpa [hv] using T1.inv_mem h)
  have hv2 : v ^ 2 ∈ T1 := by
    have h : (u ^ 2)⁻¹ ∈ T1 := T1.inv_mem hu2
    simpa [hv, pow_two] using h
  have hLv : L.map (MulAut.conj v).toMonoidHom = K := by
    have hmem : L.map (MulAut.conj v).toMonoidHom ∈ conjSetOf D.M L :=
      ⟨v, D.sylowM.le hvT, rfl⟩
    rw [hpairset] at hmem
    rcases hmem with h | h
    · exact absurd h (fun h' => hvT1 (by
        rw [hT1]
        exact Subgroup.mem_inf.mpr ⟨hvT, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h'⟩))
    · exact h
  set A' : Subgroup G := A.map (MulAut.conj v).toMonoidHom with hA'
  have hA'K : A' ≤ K := by
    rw [hA']
    exact (Subgroup.map_mono hAL).trans (le_of_eq hLv)
  have hA'card : Nat.card A' = r := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj v).injective, hAcard]
  have hmapT1 : T1.map (MulAut.conj v).toMonoidHom = T1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hT1norm hvT)
  have hA'N : A' ≤ normalizer (T1 : Set G) := by
    have hmapN : (normalizer (T1 : Set G)).map (MulAut.conj v).toMonoidHom =
        normalizer (T1 : Set G) := by
      rw [Subgroup.map_equiv_normalizer_eq, hmapT1]
    rw [hA']
    exact (Subgroup.map_mono hAN).trans (le_of_eq hmapN)
  have hLX : L ≤ conjClosure D.M L := TwelveTwentyThree.le_conjClosure D.M L
  have hKX : K ≤ conjClosure D.M L := by
    rw [hXsup]
    exact le_sup_right
  have hXeq : conjClosure D.M L = L ⊔ K := hXsup
  obtain ⟨hXM, hMX, hCcal⟩ := conjSetOf_subset_calC_conjClosure hL
  have hLXcal : L ∈ calC (conjClosure D.M L) := hCcal L hLmem
  have hKXcal : K ∈ calC (conjClosure D.M L) := hCcal K hKmem
  have hKNL : K ≤ normalizer (L : Set G) :=
    uc22p22u_calC_normalizes hLXcal hKXcal hLK
  have hXNL : conjClosure D.M L ≤ normalizer (L : Set G) := by
    rw [hXeq]
    exact sup_le Subgroup.le_normalizer hKNL
  have hO2T : pCoreOf 2 (conjClosure D.M L) ≤ D.T := by
    have hleM : pCoreOf 2 (conjClosure D.M L) ≤ D.M :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXM
    have hMN : D.M ≤ normalizer (pCoreOf 2 (conjClosure D.M L) : Set G) :=
      hMX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf
        (r := 2) (conjClosure D.M L))
    have hnormal : (pCoreOf 2 (conjClosure D.M L)).subgroupOf D.M |>.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hleM).2 hMN
    have hleCore : pCoreOf 2 (conjClosure D.M L) ≤ pCoreOf 2 D.M :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 hleM hnormal
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact hleCore.trans
      (CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow.pCoreOf_le_sylow D.sylowM)
  have hO2N : pCoreOf 2 (conjClosure D.M L) ≤ normalizer (L : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXNL
  have hO2T1 : pCoreOf 2 (conjClosure D.M L) ≤ T1 := by
    rw [hT1]
    exact le_inf hO2T hO2N
  have hcommAA' : ⁅A, A'⁆ ≤ T1 := by
    refine (Subgroup.commutator_le).2 ?_
    intro a haA b hbA'
    have haX : a ∈ conjClosure D.M L := hLX (hAL haA)
    have hbX : b ∈ conjClosure D.M L := hKX (hA'K hbA')
    have hcomm := uc22p22l_barImage_commute hLXcal hKXcal hLK
      _ (uc22p21c_mem_barImage.2 ⟨⟨a, haX⟩, hAL haA, rfl⟩)
      _ (uc22p21c_mem_barImage.2 ⟨⟨b, hbX⟩, hA'K hbA', rfl⟩)
    exact hO2T1 (uc22p22u_commutator_mem_pCoreOf haX hbX hcomm)
  set P : Subgroup G := A ⊔ A' ⊔ T1 with hP
  have hAP : A ≤ P := by rw [hP]; exact le_sup_of_le_left le_sup_left
  have hA'P : A' ≤ P := by rw [hP]; exact le_sup_of_le_left le_sup_right
  have hT1P : T1 ≤ P := by rw [hP]; exact le_sup_right
  have hPM : P ≤ D.M := by
    rw [hP]
    exact sup_le (sup_le (hAL.trans (CFSG.Quasithin.A3.subnormal_le hL.1))
      (hA'K.trans (CFSG.Quasithin.A3.subnormal_le hKcalM.1))) (hT1T.trans D.sylowM.le)
  have hPN : P ≤ normalizer (T1 : Set G) := by
    rw [hP]
    exact sup_le (sup_le hAN hA'N) Subgroup.le_normalizer
  have hv2P : v * v ∈ P := hT1P (by simpa [pow_two] using hv2)
  have hPconj : P.map (MulAut.conj (v * v)).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.le_normalizer (H := P)) hv2P)
  have hAPconj : A.map (MulAut.conj (v * v)).toMonoidHom ≤ P :=
    (Subgroup.map_mono hAP).trans (le_of_eq hPconj)
  have hPvle : P.map (MulAut.conj v).toMonoidHom ≤ P := by
    rw [hP, Subgroup.map_sup, Subgroup.map_sup, ← hA', hmapT1,
      uc22p22d_map_conj_map_conj]
    exact sup_le (sup_le hA'P hAPconj) hT1P
  have hPv : P.map (MulAut.conj v).toMonoidHom = P := by
    refine Subgroup.eq_of_le_of_card_ge hPvle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]
  have hvN : v ∈ normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPv
  have hT1NP : T1 ≤ normalizer (P : Set G) := hT1P.trans (Subgroup.le_normalizer (H := P))
  have hTP : D.T ≤ normalizer (P : Set G) := by
    intro t ht
    by_cases ht1 : t ∈ T1
    · exact hT1NP ht1
    · have htu : t * u ∈ T1 := (hcover t ht).resolve_right ht1
      have htv : t = (t * u) * v := by simp [hv]
      rw [htv]
      exact Subgroup.mul_mem _ (hT1NP htu) hvN
  let R : Subgroup ↥P := T1.subgroupOf P
  have hRnormal : R.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT1P).2 hPN
  let Q := ↥P ⧸ R
  let π : ↥P →* Q := QuotientGroup.mk' R
  let QA : Subgroup Q := (A.subgroupOf P).map π
  let QA' : Subgroup Q := (A'.subgroupOf P).map π
  have hQAcomm : ∀ x ∈ QA, ∀ y ∈ QA', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hbA' : (b : G) ∈ A' := Subgroup.mem_subgroupOf.mp hb
    have hmem : ⁅(a : G), (b : G)⁆ ∈ T1 :=
      hcommAA' (Subgroup.commutator_mem_commutator haA hbA')
    have hmemP : (⁅a, b⁆ : ↥P) ∈ T1.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      change ⁅(a : G), (b : G)⁆ ∈ T1
      exact hmem
    have hpi : π ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff ⁅a, b⁆).2 hmemP
    calc π a * π b = π (a * b) := (map_mul π a b).symm
      _ = π (⁅a, b⁆ * (b * a)) := by rw [show ⁅a, b⁆ * (b * a) = a * b by group]
      _ = π ⁅a, b⁆ * π (b * a) := map_mul π _ _
      _ = 1 * π (b * a) := by rw [hpi]
      _ = π (b * a) := one_mul _
      _ = π b * π a := map_mul π b a
  have hQAne : QA ≠ QA' := by
    intro heq
    obtain ⟨a, haA, haord⟩ := s13_exists_element_of_dvd A hr (by rw [hAcard])
    have ha1 : a ≠ 1 := by
      intro h
      have hr1 : r = 1 := by simpa [h] using haord.symm
      exact hr.ne_one hr1
    have hmemA' : π ⟨a, hAP haA⟩ ∈ QA' := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr haA)
    obtain ⟨b, hb, hbimg⟩ := Subgroup.mem_map.mp hmemA'
    have hbA' : (b : G) ∈ A' := Subgroup.mem_subgroupOf.mp hb
    have hbImgEq : π b = π ⟨a, hAP haA⟩ := hbimg
    have hb1 : (b : G) ≠ 1 := by
      intro hb0
      have hb0P : b = 1 := Subtype.ext hb0
      have hb0' : π b = 1 := by rw [hb0P]; exact map_one π
      have hpa1 : π ⟨a, hAP haA⟩ = 1 := by rw [← hbImgEq]; exact hb0'
      have hmemT : (⟨a, hAP haA⟩ : ↥P) ∈ T1.subgroupOf P :=
        (QuotientGroup.eq_one_iff _).1 hpa1
      have haT1 : a ∈ T1 := Subgroup.mem_subgroupOf.mp hmemT
      obtain ⟨k, hk⟩ := hT1T2.exists_orderOf_dvd_pow ⟨a, haT1⟩
      have hk' : orderOf a ∣ 2 ^ k := by simpa [Subgroup.orderOf_coe] using hk
      rw [haord] at hk'
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hk'
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact hr.ne_one h
      · exact hr2 h
    have hker : b⁻¹ * ⟨a, hAP haA⟩ ∈ T1.subgroupOf P := by
      rw [← QuotientGroup.eq_one_iff]
      change π (b⁻¹ * ⟨a, hAP haA⟩) = 1
      rw [map_mul, map_inv, hbImgEq, inv_mul_cancel]
    have htT1 : ((b : G)⁻¹ * a) ∈ T1 := by
      simpa using (Subgroup.mem_subgroupOf.mp hker)
    have haX : a ∈ conjClosure D.M L := hLX (hAL haA)
    have hbX : (b : G) ∈ conjClosure D.M L := hKX (hA'K hbA')
    have htX : ((b : G)⁻¹ * a) ∈ conjClosure D.M L :=
      (conjClosure D.M L).mul_mem ((conjClosure D.M L).inv_mem hbX) haX
    let πX : ↥(conjClosure D.M L) →* Bar2 (conjClosure D.M L) :=
      QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L))
    let abar : Bar2 (conjClosure D.M L) := πX ⟨a, haX⟩
    let bbar : Bar2 (conjClosure D.M L) := πX ⟨b, hbX⟩
    let tbar : Bar2 (conjClosure D.M L) := πX ⟨(b : G)⁻¹ * a, htX⟩
    have htbar : tbar = bbar⁻¹ * abar := by
      show πX ⟨(b : G)⁻¹ * a, htX⟩ = πX ⟨b, hbX⟩⁻¹ * πX ⟨a, haX⟩
      rw [show (⟨(b : G)⁻¹ * a, htX⟩ : ↥(conjClosure D.M L)) =
          (⟨b, hbX⟩ : ↥(conjClosure D.M L))⁻¹ * ⟨a, haX⟩ from Subtype.ext rfl]
      rw [map_mul, map_inv]
    have hcommb : Commute abar bbar :=
      uc22p22l_barImage_commute hLXcal hKXcal hLK
        _ (uc22p21c_mem_barImage.2 ⟨⟨a, haX⟩, hAL haA, rfl⟩)
        _ (uc22p21c_mem_barImage.2 ⟨⟨b, hbX⟩, hA'K hbA', rfl⟩)
    have hxord : orderOf (⟨a, haX⟩ : ↥(conjClosure D.M L)) = r := by
      rw [← Subgroup.orderOf_coe (⟨a, haX⟩ : ↥(conjClosure D.M L))]
      exact haord
    have haBarOrder : orderOf abar = r := by
      have hdvd : orderOf abar ∣ r := by
        have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L)))
          (⟨a, haX⟩ : ↥(conjClosure D.M L))
        rw [hxord] at h
        simpa [abar, πX] using h
      have hne : abar ≠ 1 := by
        intro h0
        have hmem : (⟨a, haX⟩ : ↥(conjClosure D.M L)) ∈ CFSG.pCore 2 ↥(conjClosure D.M L) :=
          (QuotientGroup.eq_one_iff _).1 (by simpa [abar, πX] using h0)
        have hmemG : a ∈ pCoreOf 2 (conjClosure D.M L) := ⟨_, hmem, rfl⟩
        obtain ⟨k, hk⟩ :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure D.M L)).exists_orderOf_dvd_pow
            ⟨a, hmemG⟩
        have hk' : orderOf a ∣ 2 ^ k := by simpa using hk
        rw [haord] at hk'
        have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hk'
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact hr.ne_one h
        · exact hr2 h
      rcases (Nat.dvd_prime hr).mp hdvd with h | h
      · exfalso; exact hne (orderOf_eq_one_iff.mp h)
      · exact h
    have hbBarOrder : orderOf bbar = r := by
      have hbdvd : orderOf (b : G) ∣ r := by
        have h := Subgroup.orderOf_dvd_natCard A' hbA'
        rw [hA'card] at h
        exact h
      have hborder : orderOf (b : G) = r := by
        rcases (Nat.dvd_prime hr).mp hbdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hb1
        · exact h
      have hbxord : orderOf (⟨b, hbX⟩ : ↥(conjClosure D.M L)) = r := by
        rw [← Subgroup.orderOf_coe (⟨b, hbX⟩ : ↥(conjClosure D.M L))]
        exact hborder
      have hdvd : orderOf bbar ∣ r := by
        have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L)))
          (⟨b, hbX⟩ : ↥(conjClosure D.M L))
        rw [hbxord] at h
        simpa [bbar, πX] using h
      have hne : bbar ≠ 1 := by
        intro h0
        have hmem : (⟨b, hbX⟩ : ↥(conjClosure D.M L)) ∈ CFSG.pCore 2 ↥(conjClosure D.M L) :=
          (QuotientGroup.eq_one_iff _).1 (by simpa [bbar, πX] using h0)
        have hmemG : (b : G) ∈ pCoreOf 2 (conjClosure D.M L) := ⟨_, hmem, rfl⟩
        obtain ⟨k, hk⟩ :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure D.M L)).exists_orderOf_dvd_pow
            ⟨(b : G), hmemG⟩
        have hk' : orderOf (b : G) ∣ 2 ^ k := by simpa using hk
        rw [hborder] at hk'
        have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hk'
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact hr.ne_one h
        · exact hr2 h
      rcases (Nat.dvd_prime hr).mp hdvd with h | h
      · exfalso; exact hne (orderOf_eq_one_iff.mp h)
      · exact h
    have hdivR : orderOf (bbar⁻¹ * abar) ∣ r := by
      have hcomm : Commute bbar⁻¹ abar := hcommb.symm.inv_left
      have h := hcomm.orderOf_mul_dvd_lcm
      simpa [orderOf_inv, haBarOrder, hbBarOrder] using h
    have h2pow : ∃ k : ℕ, orderOf (bbar⁻¹ * abar) ∣ 2 ^ k := by
      obtain ⟨k, hk⟩ := hT1T2.exists_orderOf_dvd_pow ⟨(b : G)⁻¹ * a, htT1⟩
      have htord : orderOf ((b : G)⁻¹ * a) ∣ 2 ^ k := by simpa using hk
      have htb : orderOf tbar ∣ orderOf ((b : G)⁻¹ * a) := by
        have := orderOf_map_dvd πX (⟨(b : G)⁻¹ * a, htX⟩ : ↥(conjClosure D.M L))
        simpa [tbar, πX] using this
      refine ⟨k, ?_⟩
      rw [← htbar]
      exact htb.trans htord
    have horder1 : orderOf (bbar⁻¹ * abar) = 1 := by
      obtain ⟨k, h2k⟩ := h2pow
      rcases (Nat.dvd_prime hr).mp hdivR with h | h
      · exact h
      · exfalso
        rw [h] at h2k
        have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h2k
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
        · exact hr.ne_one h1
        · exact hr2 h1
    have hbeq : bbar = abar := by
      have h : bbar⁻¹ * abar = 1 := orderOf_eq_one_iff.mp horder1
      exact inv_mul_eq_one.mp h
    have habarK : abar ∈ barImage (conjClosure D.M L) K := hbeq ▸
      (uc22p21c_mem_barImage.2 ⟨⟨b, hbX⟩, hA'K hbA', rfl⟩)
    have hall : (QuotientGroup.mk (Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hLXcal.1)
        ⟨a, hAL haA⟩) : Bar2 (conjClosure D.M L)) ∈ barImage (conjClosure D.M L) K := by
      have hsub : Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hLXcal.1) ⟨a, hAL haA⟩ =
          (⟨a, haX⟩ : ↥(conjClosure D.M L)) := Subtype.ext rfl
      rw [hsub]
      exact habarK
    have hcenter := uc22ine229_mk_mem_center (M := conjClosure D.M L) hLXcal hKXcal hLK
      ⟨a, hAL haA⟩ hall
    rw [hZ, Subgroup.mem_bot] at hcenter
    have hmemCore : a ∈ pCoreOf 2 L := by
      have hmem : (⟨a, hAL haA⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        (QuotientGroup.eq_one_iff _).1 (by simpa [Bar2] using hcenter)
      exact ⟨_, hmem, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_orderOf_dvd_pow
      ⟨a, hmemCore⟩
    have hk' : orderOf a ∣ 2 ^ k := by simpa using hk
    rw [haord] at hk'
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hk'
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact hr.ne_one h
    · exact hr2 h
  have hQAcard : Nat.card QA = r := by
    have hdvd : Nat.card QA ∣ r := by
      have h := Subgroup.card_map_dvd (A.subgroupOf P) π
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAcard] at h
    obtain ⟨a, haA, haord⟩ := s13_exists_element_of_dvd A hr (by rw [hAcard])
    have ha1 : a ≠ 1 := by
      intro h
      have hr1 : r = 1 := by simpa [h] using haord.symm
      exact hr.ne_one hr1
    have hne : QA ≠ ⊥ := by
      intro hbot
      have hmemQA : π ⟨a, hAP haA⟩ ∈ QA :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr haA)
      have hmem : π ⟨a, hAP haA⟩ = 1 := by
        rw [hbot] at hmemQA
        simpa using hmemQA
      have hker : (⟨a, hAP haA⟩ : ↥P) ∈ T1.subgroupOf P := (QuotientGroup.eq_one_iff _).1 hmem
      have haT1 : a ∈ T1 := Subgroup.mem_subgroupOf.mp hker
      obtain ⟨k, hk⟩ := hT1T2.exists_orderOf_dvd_pow ⟨a, haT1⟩
      have hk' : orderOf a ∣ 2 ^ k := by simpa [Subgroup.orderOf_coe] using hk
      rw [haord] at hk'
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hk'
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact hr.ne_one h
      · exact hr2 h
    have hne1 : Nat.card QA ≠ 1 := by
      intro h1
      exact hne (Subgroup.card_eq_one.mp h1)
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exfalso; exact hne1 h
    · exact h
  have hQA'card : Nat.card QA' = r := by
    have hdvd : Nat.card QA' ∣ r := by
      have h := Subgroup.card_map_dvd (A'.subgroupOf P) π
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'P).toEquiv, hA'card] at h
    obtain ⟨a, haA, haord⟩ := s13_exists_element_of_dvd A' hr (by rw [hA'card])
    have ha1 : a ≠ 1 := by
      intro h
      have hr1 : r = 1 := by simpa [h] using haord.symm
      exact hr.ne_one hr1
    have hne : QA' ≠ ⊥ := by
      intro hbot
      have hmemQA' : π ⟨a, hA'P haA⟩ ∈ QA' :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr haA)
      have hmem : π ⟨a, hA'P haA⟩ = 1 := by
        rw [hbot] at hmemQA'
        simpa using hmemQA'
      have hker : (⟨a, hA'P haA⟩ : ↥P) ∈ T1.subgroupOf P := (QuotientGroup.eq_one_iff _).1 hmem
      have haT1 : a ∈ T1 := Subgroup.mem_subgroupOf.mp hker
      obtain ⟨k, hk⟩ := hT1T2.exists_orderOf_dvd_pow ⟨a, haT1⟩
      have hk' : orderOf a ∣ 2 ^ k := by simpa [Subgroup.orderOf_coe] using hk
      rw [haord] at hk'
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hk'
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact hr.ne_one h
      · exact hr2 h
    have hne1 : Nat.card QA' ≠ 1 := by
      intro h1
      exact hne (Subgroup.card_eq_one.mp h1)
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exfalso; exact hne1 h
    · exact h
  have hQAp : IsPGroup r QA :=
    IsPGroup.of_card (n := 1) (by rw [hQAcard, pow_one])
  have hQA'p : IsPGroup r QA' :=
    IsPGroup.of_card (n := 1) (by rw [hQA'card, pow_one])
  have hQAnorm : QA ≤ normalizer (QA' : Set Q) := by
    have hcent : QA ≤ Subgroup.centralizer (QA' : Set Q) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hQAcomm x hx y hy).symm
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hEp : IsPGroup r ↥(QA ⊔ QA') := hQAp.to_sup_of_normal_right' hQA'p hQAnorm
  have hEnc : ¬ IsCyclic ↥(QA ⊔ QA') := by
    intro hcyc
    have := hcyc
    have hcards : Nat.card ↥(QA.subgroupOf (QA ⊔ QA')) =
        Nat.card ↥(QA'.subgroupOf (QA ⊔ QA')) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv,
        hQAcard, hQA'card]
    have heq : QA.subgroupOf (QA ⊔ QA') = QA'.subgroupOf (QA ⊔ QA') :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr hcards
    have heq' : QA = QA' := by
      have h := Subgroup.subgroupOf_inj.mp heq
      rwa [inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right] at h
    exact hQAne heq'
  have hnc : ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r S P → ¬ IsCyclic ↥S := by
    intro S hS
    exact not_isCyclic_of_isSylowOf_of_le_map (N := P) (K := P) (p := r) (f := π)
      le_rfl hS hEp hEnc (by
        rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective]
        · exact le_top
        · exact QuotientGroup.mk'_surjective R)
  have hQeq : (⊤ : Subgroup Q) = QA ⊔ QA' := by
    refine le_antisymm ?_ le_top
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective R x
    let H : Subgroup G := A ⊔ A'
    have hHN : H ≤ normalizer (T1 : Set G) := sup_le hAN hA'N
    have hHP : H ≤ P := by
      show A ⊔ A' ≤ A ⊔ A' ⊔ T1
      exact le_sup_of_le_left le_rfl
    have hPmul : ((P : Subgroup G) : Set G) = (H : Set G) * (T1 : Set G) := by
      rw [hP]
      exact Subgroup.coe_mul_of_left_le_normalizer_right H T1 hHN
    have hp : (p : G) ∈ (H : Set G) * (T1 : Set G) := by
      rw [← hPmul]
      exact p.2
    obtain ⟨y, hyH, t, htT1, hyt⟩ := Set.mem_mul.mp hp
    have hyP : y ∈ P := hHP hyH
    have htP : t ∈ P := hT1P htT1
    have hpi_t : π ⟨t, htP⟩ = 1 := by
      refine (QuotientGroup.eq_one_iff _).2 ?_
      exact Subgroup.mem_subgroupOf.mpr htT1
    have hp_decomp : p = ⟨y, hyP⟩ * ⟨t, htP⟩ := Subtype.ext hyt.symm
    have hx_eq : π p = π ⟨y, hyP⟩ := by
      calc π p = π (⟨y, hyP⟩ * ⟨t, htP⟩) := by rw [hp_decomp]
        _ = π ⟨y, hyP⟩ * π ⟨t, htP⟩ := map_mul π _ _
        _ = π ⟨y, hyP⟩ * 1 := by rw [hpi_t]
        _ = π ⟨y, hyP⟩ := mul_one _
    rw [hx_eq]
    have hy' : π ⟨y, hyP⟩ ∈ QA ⊔ QA' := by
      have hyH' : (⟨y, hyP⟩ : ↥P) ∈ H.subgroupOf P :=
        Subgroup.mem_subgroupOf.mpr hyH
      have hmaps : (H.subgroupOf P).map π ≤ QA ⊔ QA' := by
        have hHsup : H.subgroupOf P = (A.subgroupOf P) ⊔ (A'.subgroupOf P) := by
          show (A ⊔ A').subgroupOf P = _
          exact Subgroup.subgroupOf_sup hAP hA'P
        rw [hHsup, Subgroup.map_sup]
      exact hmaps (Subgroup.mem_map_of_mem π hyH')
    exact hy'
  have hQp : IsPGroup r Q := by
    have hEp' : IsPGroup r ↥(⊤ : Subgroup Q) := hQeq ▸ hEp
    exact hEp'.of_equiv Subgroup.topEquiv
  have hPrelOdd : Odd (T1.relIndex P) := by
    have hcard : T1.relIndex P = Nat.card Q := by
      rw [← Subgroup.index_eq_card (T1.subgroupOf P)]
      rfl
    rw [hcard]
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := r) hQp
    rw [hk]
    exact (Nat.Prime.odd_of_ne_two hr hr2).pow
  obtain ⟨E, hEP, hEp, hEexp, hEncE, hTNE⟩ :=
    exists_noncyclic_exp_le_normalizer_sup (p := r) hr hr2
      (A := D.T) (K := P) (R := T1) D.sylowM.isPGroup hT1T2 hT1P hPN hTP hT1norm
      hPrelOdd hnc
  have hT1normal : (T1.subgroupOf D.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT1T).2 hT1norm
  have : (T1.subgroupOf D.T).Normal := hT1normal
  let Cq := ↥D.T ⧸ T1.subgroupOf D.T
  have hCcard : Nat.card Cq = 2 := by
    rw [← Subgroup.index_eq_card (T1.subgroupOf D.T)]
    exact hT1rel
  have : IsCyclic Cq := isCyclic_of_card_dvd_prime (p := 2) (by rw [hCcard])
  let φ : ↥D.T →* Cq := QuotientGroup.mk' (T1.subgroupOf D.T)
  have hker : ∀ u : ↥D.T, φ u = 1 → (u : G) ∈ T1 := by
    intro u hu
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff u).1 hu)
  exact ⟨E, inPStar_of_strongly_of_le_normalizer_sup (D := D) (V₀ := V₀)
    hr hr2 hstr (X := E) (T₀ := T1) (hEP.trans hPM) hEp hEexp hEncE hT1T hT1norm
    (hEP.trans hPN) hTNE φ hker⟩

theorem s17_45_pair_torus_inPStar {D : Data G}
    {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hn : Odd n)
    (hpair : ∃ x ∈ D.M, X = L ⊔ CFSG.Quasithin.conjSubgroup L x ∧ X ≠ L)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M) :
    ∃ E : Subgroup G, InPStar D V₀ E := by
  classical
  obtain ⟨x, hxM, hXsup, hne⟩ := hpair
  have hn1 : 1 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hr2 : r ≠ 2 := by
    intro h2
    have hodd : Odd (2 ^ n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
    exact hodd.not_two_dvd_nat (h2 ▸ hrdvd)
  have hrd : r ∣ Nat.card (Bar2 L) := by
    rcases hshape with hL2 | hSz
    · rw [card_of_isL2 hL2]
      have hdvd : r ∣ 2 ^ (2 * n) - 1 := by
        have h1 : r ∣ (2 ^ n) ^ 2 - 1 :=
          hrdvd.trans (by
            simpa using Nat.pow_sub_one_dvd_pow_sub_one (2 ^ n) (by norm_num : 1 ∣ 2))
        rwa [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul]; ring_nf] at h1
      exact hdvd.trans (dvd_mul_of_dvd_right (dvd_refl _) (2 ^ n))
    · exact dvd_card_bar2_of_isSz_sub_one hSz hrdvd
  obtain ⟨Y, hYL, hYcard⟩ := s13_exists_subgroup_of_dvd_card_bar hr hrd
  have hCLne : conjClosure D.M L ≠ L := by rw [← ctx.X_eq]; exact hne
  have hc2 : (conjSetOf D.M L).ncard = 2 :=
    ncard_eq_two_of_p42 ctx.mem_calC hxM (by rw [← ctx.X_eq]; exact hXsup) hCLne
  set T1 : Subgroup G := D.T ⊓ normalizer (L : Set G) with hT1
  have hT1T : T1 ≤ D.T := inf_le_left
  have hT1N : T1 ≤ normalizer (L : Set G) := inf_le_right
  have hT12 : IsPGroup 2 ↥T1 := D.sylowM.isPGroup.to_le hT1T
  have hT1normal : (T1.subgroupOf D.T).Normal := by
    have h := s17_45_normal_subgroupOf_inf_normalizer (D := D) (L := L) hc2
    simpa [hT1] using h
  have hSylOf : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    uc22p22r_fo_sylow_inf D.sylowM ctx.mem_calC.1
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T1) L := by
    have hEq : L ⊓ T1 = D.T ⊓ L := by
      rw [hT1, ← inf_assoc,
        inf_eq_left.mpr ((inf_le_left : L ⊓ D.T ≤ L).trans (Subgroup.le_normalizer (H := L))),
        inf_comm]
    rw [hEq]
    exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hSylOf
  have hZ : Subgroup.center (Bar2 L) = ⊥ := by
    rcases hshape with hL2 | hSz
    · have : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
      exact uc22p21k_center_eq_bot ctx.mem_calC.2.2
    · have : IsSimpleGroup (Bar2 L) :=
        CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
      exact uc22p21k_center_eq_bot ctx.mem_calC.2.2
  rcases hshape with hL2 | hSz
  · obtain ⟨g, hgL, hAg⟩ :=
      exists_conj_le_normalizer_T_of_isL2_bar2 (T := T1) (X := Y) (s := n)
        hL2 hT1N hT12 hSyl hn (dvd_refl n) hr hrdvd hYL hYcard
    have hmapL : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := L) hgL)
    refine exists_inPStar_of_pair (D := D) (V₀ := V₀) ctx.mem_calC hxM
      (by rw [← ctx.X_eq]; exact hXsup) hCLne hr hr2 hstr ?_ ?_ hAg hZ
    · exact (Subgroup.map_mono hYL).trans (le_of_eq hmapL)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hYcard]
  · obtain ⟨g, hgL, hAg⟩ :=
      exists_conj_le_normalizer_T_of_isSz_bar2 (T := T1) (X := Y) (s := n)
        hSz hT1N hT12 hSyl hn (dvd_refl n) hr hrdvd hYL hYcard
    have hmapL : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := L) hgL)
    refine exists_inPStar_of_pair (D := D) (V₀ := V₀) ctx.mem_calC hxM
      (by rw [← ctx.X_eq]; exact hXsup) hCLne hr hr2 hstr ?_ ?_ hAg hZ
    · exact (Subgroup.map_mono hYL).trans (le_of_eq hmapL)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hYcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
