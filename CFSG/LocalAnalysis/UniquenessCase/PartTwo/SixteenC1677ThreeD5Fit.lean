module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5CoordCor
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Extract
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_d5_frame [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L)
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8) :
    ∃ (K : Fin 4 → Subgroup (MulAut W)) (Z : Fin 4 → Subgroup W),
      s16e_d5_Frame L K Z ∧ L ≤ A := by
  have hrk6 := s16e_d5_extract hL hrk hconc
  have hrk8 : rk ↥(⊤ : Subgroup W) = 8 := by rwa [hWL] at hrk
  obtain ⟨K, Z, hfr⟩ := s16e_d5_blocks hW hL hWL hrk8 hrk6
  exact ⟨K, Z, hfr, hconc.le⟩

private theorem s168e3_d5_conj_K [Finite W]
    {L : Subgroup (MulAut W)} {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}
    (hfr : s16e_d5_Frame L K Z) {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) {i j : Fin 4}
    (hmap : (Z i).map g.toMonoidHom = Z j) :
    (K i).map (MulAut.conj g).toMonoidHom = K j := by
  let K' : Subgroup (MulAut W) := (K i).map (MulAut.conj g).toMonoidHom
  have hK'le : K' ≤ L := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hkL : k ∈ L := hfr.K_le i hk
    change (MulAut.conj g) k ∈ L
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg k).mp hkL
  have hK'card : Nat.card ↥K' = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hfr.K_card i]
  obtain ⟨j', hj'⟩ := hfr.K_all K' hK'le hK'card
  have hZj : Z j = fixV K' := by
    rw [← hmap, hfr.Z_eq i]
    exact (fixV_map_conj_eq (K i) g).symm
  have hZj' : Z j' = fixV K' := by rw [hfr.Z_eq j', hj']
  have hjj' : j = j' := hfr.Z_inj (hZj.trans hZj'.symm)
  rw [← hjj'] at hj'
  exact hj'

theorem s168e3_d5_inf_cent_eq [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L)
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8)
    (hlt : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) < 27) :
    A ⊓ Subgroup.centralizer (L : Set (MulAut W)) = L := by
  obtain ⟨K, Z, hfr, hLA⟩ := s168e3_d5_frame hW hconc hL hWL hrk
  set B : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hB
  have hB81 : Nat.card ↥B ∣ 81 := by
    rw [hB]
    exact (Subgroup.card_dvd_of_le inf_le_right).trans (s16e_d5_card_cent_dvd hfr)
  have hLB : L ≤ B := by
    rw [hB]
    exact le_inf hLA (s16e_d5_L_le_cent hfr)
  have h9n : 9 ∣ Nat.card ↥B := by
    have h := Subgroup.card_dvd_of_le hLB
    rwa [hfr.card_L] at h
  have hcard : Nat.card ↥B = 9 := by
    have hBpow : Nat.card ↥B ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = 81 by norm_num]
      exact hB81
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hBpow
    have h2k : 2 ≤ k := by
      have h9dvd : (3 : ℕ) ^ 2 ∣ (3 : ℕ) ^ k := by
        rw [← hk, show (3 : ℕ) ^ 2 = 9 by norm_num]
        exact h9n
      exact (Nat.pow_dvd_pow_iff_le_right (show 1 < (3 : ℕ) by norm_num)).mp h9dvd
    have hk3 : k < 3 := by
      have hlt' : (3 : ℕ) ^ k < (3 : ℕ) ^ 3 := by
        rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num]
        exact hlt
      exact (Nat.pow_lt_pow_iff_right (show 1 < (3 : ℕ) by norm_num)).mp hlt'
    have hk2 : k = 2 := by omega
    rw [hk, hk2]
    norm_num
  have hLB' : L = B := Subgroup.eq_of_le_of_card_ge hLB (by rw [hcard, hfr.card_L])
  rw [hB] at hLB'
  exact hLB'.symm

theorem s168e3_d5_card_dvd [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L)
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8)
    (hlt : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) < 27) :
    Nat.card ↥A ∣ 2 ^ 4 * 3 ^ 3 := by
  obtain ⟨K, Z, hfr, hLA⟩ := s168e3_d5_frame hW hconc hL hWL hrk
  have hB := s168e3_d5_inf_cent_eq hW hconc hL hWL hrk hlt
  have h48 : (L.subgroupOf A).index ∣ 48 := by
    have h := s16e_d5_index_dvd_48 (by rw [hfr.card_L]) hLn
    rwa [hB] at h
  have hcardL : Nat.card ↥(L.subgroupOf A) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv).trans hfr.card_L
  have hcard : Nat.card ↥A = 9 * (L.subgroupOf A).index := by
    rw [← Subgroup.card_mul_index (L.subgroupOf A), hcardL]
  calc Nat.card ↥A = 9 * (L.subgroupOf A).index := hcard
    _ ∣ 9 * 48 := mul_dvd_mul_left 9 h48
    _ = 2 ^ 4 * 3 ^ 3 := by norm_num

theorem s168e3_d5_fitting_eq [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L)
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8)
    (hind : IsIndivisible A)
    (hlt : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) < 27) :
    (CFSG.generalizedFitting ↥A).map A.subtype = L := by
  obtain ⟨K, Z, hfr, hLA⟩ := s168e3_d5_frame hW hconc hL hWL hrk
  have hB : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) = L :=
    s168e3_d5_inf_cent_eq hW hconc hL hWL hrk hlt
  have h432 : Nat.card ↥A ∣ 2 ^ 4 * 3 ^ 3 :=
    s168e3_d5_card_dvd hW hconc hLn hL hWL hrk hlt
  haveI hsA : Group.IsSolvable ↥A :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three h432
  rw [CFSG.WholeGroup.generalizedFitting_eq_fittingSubgroup_of_isSolvable]
  set F : Subgroup ↥A := CFSG.fittingSubgroup ↥A with hFdef
  haveI hFnil : Group.IsNilpotent ↥F := by rw [hFdef]; infer_instance
  have hFnorm : F.Normal := by rw [hFdef]; infer_instance
  let Fw : Subgroup (MulAut W) := F.map A.subtype
  have hLnorm : (L.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLA).mpr hLn
  have hcardL : Nat.card ↥(L.subgroupOf A) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv).trans hfr.card_L
  haveI hLnilA : Group.IsNilpotent ↥(L.subgroupOf A) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.isNilpotent (IsPGroup.of_card (p := 3) (n := 2) (by rw [hcardL]; norm_num))
  have hLF : L.subgroupOf A ≤ F := by
    rw [hFdef]
    exact le_sSup ⟨hLnorm, hLnilA⟩
  have hLFw : L ≤ Fw := by
    change L ≤ F.map A.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hLA]
    exact Subgroup.map_mono hLF
  let N : Subgroup ↥F := (L.subgroupOf A).subgroupOf F
  haveI hNnormal : N.Normal := hLnorm.subgroupOf F
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥N = 9 := by
      change Nat.card ↥((L.subgroupOf A).subgroupOf F) = 9
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLF).toEquiv, hcardL]
    rw [hbot, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  have hne : N ⊓ Subgroup.center ↥F ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥F) (H := N) hNne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let z : ↥F := (a : ↥F)
  have hzN : z ∈ N := (Subgroup.mem_inf.mp a.2).1
  have hzcent : z ∈ Subgroup.center ↥F := (Subgroup.mem_inf.mp a.2).2
  have hz1 : z ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext h)
  let zW : MulAut W := ((z : ↥A) : MulAut W)
  have hzL : zW ∈ L := by
    have h1 : (z : ↥A) ∈ L.subgroupOf A := Subgroup.mem_subgroupOf.mp hzN
    show ((z : ↥A) : MulAut W) ∈ L
    exact Subgroup.mem_subgroupOf.mp h1
  have hz3 : zW ^ 3 = 1 := hfr.pow_L zW hzL
  have hzW1 : zW ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  have hcardz : Nat.card ↥(Subgroup.zpowers zW) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz3 hzW1]
  obtain ⟨i, hi⟩ := hfr.K_all (Subgroup.zpowers zW) (Subgroup.zpowers_le.mpr hzL) hcardz
  have hz_cent : ∀ f ∈ Fw, f * zW = zW * f := by
    intro f hf
    obtain ⟨fA, hfA, rfl⟩ := Subgroup.mem_map.mp hf
    have hcz : (⟨fA, hfA⟩ : ↥F) * z = z * ⟨fA, hfA⟩ :=
      (Subgroup.mem_center_iff.mp hzcent) ⟨fA, hfA⟩
    have h := congrArg (fun y : ↥F => ((y : ↥A) : MulAut W)) hcz
    simpa [zW] using h
  have hcent_i : Fw ≤ Subgroup.centralizer ((K i) : Set (MulAut W)) := by
    rw [← hi]
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.zpow_right (hz_cent f hf) n).symm
  have hcent_K : ∀ j, Fw ≤ Subgroup.centralizer ((K j) : Set (MulAut W)) := by
    intro j
    obtain ⟨g, hgA, hmapZ⟩ := hfr.trans hLn hind i j
    have hmapK : (K i).map (MulAut.conj g).toMonoidHom = K j :=
      s168e3_d5_conj_K hfr (hLn g hgA) hmapZ
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← hmapK] at hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    have hconj_mem : (MulAut.conj g⁻¹) f ∈ Fw := by
      obtain ⟨fA, hfA, rfl⟩ := Subgroup.mem_map.mp hf
      refine Subgroup.mem_map.mpr ⟨(⟨g, hgA⟩ : ↥A)⁻¹ * fA * ⟨g, hgA⟩, ?_, ?_⟩
      · exact hFnorm.conj_mem fA hfA (⟨g, hgA⟩ : ↥A)⁻¹
      · show A.subtype ((⟨g, hgA⟩ : ↥A)⁻¹ * fA * ⟨g, hgA⟩) =
          (MulAut.conj g⁻¹) (A.subtype fA)
        simp [MulAut.conj_apply]
    have hcomm : k' * (MulAut.conj g⁻¹) f = (MulAut.conj g⁻¹) f * k' :=
      Subgroup.mem_centralizer_iff.mp (hcent_i hconj_mem) k' hk'
    have hgg : (MulAut.conj g) ((MulAut.conj g⁻¹) f) = f := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have h := congrArg (MulAut.conj g) hcomm
    simp only [map_mul, hgg] at h
    exact h
  have hcentL : Fw ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    · have hx3 : x ^ 3 = 1 := hfr.pow_L x hx
      have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
      obtain ⟨j, hj⟩ := hfr.K_all (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hx) hcardx
      have hxj : x ∈ K j := by rw [← hj]; exact Subgroup.mem_zpowers x
      exact Subgroup.mem_centralizer_iff.mp (hcent_K j hf) x hxj
  have hFwA : Fw ≤ A := by
    intro f hf
    obtain ⟨fA, -, rfl⟩ := Subgroup.mem_map.mp hf
    exact fA.2
  have hFwL : Fw ≤ L := by
    rw [← hB]
    exact le_inf hFwA hcentL
  have hFmap : F.map A.subtype = L := by
    apply le_antisymm hFwL
    calc L = (L.subgroupOf A).map A.subtype := (Subgroup.map_subgroupOf_eq_of_le hLA).symm
      _ ≤ F.map A.subtype := Subgroup.map_mono hLF
  exact hFmap

theorem s168e3_d5_fitting_of_lt_27 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L)
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8)
    (hind : IsIndivisible A)
    (hlt : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) < 27) :
    Nat.card ↥A ∣ 2 ^ 4 * 3 ^ 3 ∧ (CFSG.generalizedFitting ↥A).map A.subtype = L :=
  ⟨s168e3_d5_card_dvd hW hconc hLn hL hWL hrk hlt,
    s168e3_d5_fitting_eq hW hconc hLn hL hWL hrk hind hlt⟩

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
