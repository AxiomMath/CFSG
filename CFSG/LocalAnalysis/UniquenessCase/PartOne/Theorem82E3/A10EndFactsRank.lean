module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFive
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKeySetup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.GroupTheory.ConjTransport
import CFSG.GroupTheory.SubgroupConjBasic
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem exists_fiveCycle_compl {s : Finset (Fin 10)} (hs : s.card = 3) :
    ∃ σ : Equiv.Perm (Fin 10), σ ∈ alternatingGroup (Fin 10) ∧ orderOf σ = 5 ∧
      Disjoint σ.support s := by
  classical
  have hcard : 5 ≤ sᶜ.card := by
    rw [Finset.card_compl, hs, Fintype.card_fin]
    norm_num
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨σ, hσcycleOn, hσsupp_le⟩ := Finset.exists_cycleOn t
  have htnt : (t : Set (Fin 10)).Nontrivial :=
    Finset.nontrivial_coe.mpr
      (Finset.one_lt_card_iff_nontrivial.mp (by rw [ht_card]; norm_num))
  have hσsupp : σ.support = t := by
    refine le_antisymm hσsupp_le ?_
    intro x hx
    exact Equiv.Perm.mem_support.mpr (hσcycleOn.apply_ne htnt hx)
  have hσcycle : σ.IsCycle := by
    rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
    refine ⟨(t : Set (Fin 10)), htnt, hσcycleOn, fun x hx => ?_⟩
    rw [← hσsupp]
    exact Equiv.Perm.mem_support.mpr hx
  have horder : orderOf σ = 5 := by
    rw [hσcycle.orderOf, hσsupp, ht_card]
  have hsign : Equiv.Perm.sign σ = 1 := by
    rw [hσcycle.sign, hσsupp, ht_card]
    norm_num
  refine ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign, horder, ?_⟩
  exact Finset.disjoint_left.mpr fun x hx hxs =>
    (Finset.mem_compl.mp (ht_sub (hσsupp_le hx))) hxs

private theorem exists_five_mem_ker_centralizer_A (F : A10Frame c) :
    ∃ y : ↥D.M, orderOf (y : G) = 5 ∧ F.phiA y = 1 ∧
      (y : G) ∈ Subgroup.centralizer (F.A : Set G) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5dvd : 5 ∣ Nat.card ↥(Subgroup.centralizer (F.A : Set G) ⊓ D.M) :=
    F.five_dvd_card_centralizer_inf (fun x hx h => (F.a10Hom_eq_one_iff hx).mp h)
      (F.three_le_pRank_five) (F.A_le.trans F.P_le_L) F.elemAbelian.isPGroup
  obtain ⟨yC, hyCord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer (F.A : Set G) ⊓ D.M)) 5 h5dvd
  let y : G := (yC : G)
  have hyCent : y ∈ Subgroup.centralizer (F.A : Set G) :=
    (Subgroup.mem_inf.mp yC.2).1
  have hyM : y ∈ D.M := (Subgroup.mem_inf.mp yC.2).2
  let yM : ↥D.M := ⟨y, hyM⟩
  have hyord : orderOf y = 5 := by
    have h := Subgroup.orderOf_coe yC
    rw [hyCord] at h
    exact h
  have hφcent : F.phiA yM ∈
      Subgroup.centralizer (A10Perm.atilde : Set (Equiv.Perm (Fin 10))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← F.map_A_phiA] at hz
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm : Commute a yM := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hyCent (a : G) (Subgroup.mem_subgroupOf.mp haA)
    exact (hcomm.map F.phiA).eq
  rw [A10Perm.centralizer_atilde] at hφcent
  have hyMord : orderOf yM = 5 := by
    rw [← Subgroup.orderOf_coe yM]
    exact hyord
  have hpow : yM ^ 5 = 1 := by
    rw [← hyMord]
    exact pow_orderOf_eq_one yM
  have hφpow : (F.phiA yM) ^ 5 = 1 := by
    rw [← map_pow, hpow, map_one]
  have hdvd5 : orderOf (F.phiA yM) ∣ 5 := orderOf_dvd_of_pow_eq_one hφpow
  have hdvd27 : orderOf (F.phiA yM) ∣ 27 := by
    have h := Subgroup.orderOf_dvd_natCard A10Perm.atilde hφcent
    rwa [A10Perm.card_atilde] at h
  have hone : orderOf (F.phiA yM) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 27) hdvd5 hdvd27
  refine ⟨yM, ?_, orderOf_eq_one_iff.mp hone, hyCent⟩
  rw [Subgroup.orderOf_coe]
  exact hyMord

private theorem map_inf_centralizer_L_eq (F : A10Frame c) {b : G} (hbA : b ∈ F.A) :
    (c.L.subgroupOf D.M ⊓
      Subgroup.centralizer ((Subgroup.zpowers b).subgroupOf D.M : Set ↥D.M)).map F.phiA =
      alternatingGroup (Fin 10) ⊓ Subgroup.centralizer
        (Subgroup.zpowers (F.phiA ⟨b, F.A_le_M hbA⟩) : Set (Equiv.Perm (Fin 10))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbL : b ∈ c.L := F.P_le_L (F.A_le hbA)
  have hbM : b ∈ D.M := F.A_le_M hbA
  have hB3pg : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      simpa using orderOf_dvd_of_pow_eq_one (F.elemAbelian.2 b hbA))
  have hBM3 : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf D.M) := hB3pg.comap_subtype
  have hBM_le : (Subgroup.zpowers b).subgroupOf D.M ≤ c.L.subgroupOf D.M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.zpowers_le.mpr hbL hx
  have hmap := CoprimeImage.map_inf_centralizer_of_coprime_ker
    (p := 3) Nat.prime_three F.phiA F.coprime_card_ker_phiA hBM3 hBM_le
  simpa [CFSG.GroupTheory.zpowers_coe_subgroupOf (⟨b, hbM⟩ : ↥D.M), MonoidHom.map_zpowers,
    F.map_L_phiA] using hmap

private theorem five_dvd_card_inf_centralizer_map (F : A10Frame c) {b : G}
    (hbA : b ∈ F.A) (hbdeg : F.deg (Subgroup.zpowers b) = 3) :
    5 ∣ Nat.card ↥(c.L.subgroupOf D.M ⊓
      Subgroup.centralizer ((Subgroup.zpowers b).subgroupOf D.M : Set ↥D.M)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hbL : b ∈ c.L := F.P_le_L (F.A_le hbA)
  have hbM : b ∈ D.M := F.A_le_M hbA
  have hs : (F.phiA ⟨b, hbM⟩).support.card = 3 := by
    rw [← F.deg_zpowers_eq hbL, hbdeg]
  obtain ⟨σ, hσA, hσord, hσdisj⟩ := exists_fiveCycle_compl hs
  let X : Subgroup ↥D.M := c.L.subgroupOf D.M ⊓
    Subgroup.centralizer ((Subgroup.zpowers b).subgroupOf D.M : Set ↥D.M)
  have hXmap : X.map F.phiA = alternatingGroup (Fin 10) ⊓
      Subgroup.centralizer (Subgroup.zpowers (F.phiA ⟨b, hbM⟩) :
        Set (Equiv.Perm (Fin 10))) := by
    simpa [X] using map_inf_centralizer_L_eq F hbA
  have hσcent : σ ∈ Subgroup.centralizer
      (Subgroup.zpowers (F.phiA ⟨b, hbM⟩) : Set (Equiv.Perm (Fin 10))) := by
    have hσcomm : Commute σ (F.phiA ⟨b, hbM⟩) :=
      (Equiv.Perm.disjoint_iff_disjoint_support.mpr hσdisj).commute
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hσcomm.eq
  have hσmap : σ ∈ X.map F.phiA := by
    rw [hXmap]
    exact Subgroup.mem_inf.mpr ⟨hσA, hσcent⟩
  let g : ↥X →* Equiv.Perm (Fin 10) := F.phiA.comp X.subtype
  have hσrange : σ ∈ g.range := by
    obtain ⟨x, hxX, hxσ⟩ := Subgroup.mem_map.mp hσmap
    exact ⟨⟨x, hxX⟩, hxσ⟩
  have h5 : 5 ∣ Nat.card ↥g.range := by
    have h := Subgroup.orderOf_dvd_natCard g.range hσrange
    rwa [hσord] at h
  rw [← Subgroup.card_ker_mul_card_range g]
  exact dvd_mul_of_dvd_right h5 _

private theorem exists_five_mem_inf_centralizer_not_mem_ker (F : A10Frame c) {b : G}
    (hbA : b ∈ F.A) (hbdeg : F.deg (Subgroup.zpowers b) = 3) :
    ∃ u : ↥D.M, orderOf (u : G) = 5 ∧ u ∈ c.L.subgroupOf D.M ∧
      u ∈ Subgroup.centralizer ((Subgroup.zpowers b).subgroupOf D.M : Set ↥D.M) ∧
      F.phiA u ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let X : Subgroup ↥D.M := c.L.subgroupOf D.M ⊓
    Subgroup.centralizer ((Subgroup.zpowers b).subgroupOf D.M : Set ↥D.M)
  have h5dvd : 5 ∣ Nat.card ↥X := five_dvd_card_inf_centralizer_map F hbA hbdeg
  obtain ⟨uX, huXord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5dvd
  have huord : orderOf (((uX : ↥X) : ↥D.M) : G) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, huXord]
  refine ⟨(uX : ↥D.M), huord, (Subgroup.mem_inf.mp uX.2).1,
    (Subgroup.mem_inf.mp uX.2).2, ?_⟩
  intro hphi
  have huL : (((uX : ↥X) : ↥D.M) : G) ∈ c.L :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp uX.2).1
  have huM_eq : ((uX : ↥X) : ↥D.M) =
      (⟨(((uX : ↥X) : ↥D.M) : G), c.hyp81.1 huL⟩ : ↥D.M) := Subtype.ext rfl
  have huO2 : (((uX : ↥X) : ↥D.M) : G) ∈
      (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype :=
    (F.phiA_eq_one_iff huL).mp (by rwa [huM_eq] at hphi)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot5 : ¬ 5 ∣ Nat.card ↥((CFSG.Open.pCore 2 ↥c.L).map c.L.subtype) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype) Nat.prime_five
      (by norm_num)
  exact hnot5 (huord ▸ Subgroup.orderOf_dvd_natCard _ huO2)

private theorem exists_five_mem_centralizer_not_mem_ker (F : A10Frame c) {b : G}
    (hbA : b ∈ F.A) (hbdeg : F.deg (Subgroup.zpowers b) = 3) :
    ∃ u : ↥D.M, orderOf (u : G) = 5 ∧
      (u : G) ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) ∧ F.phiA u ≠ 1 := by
  obtain ⟨u, huord, _huL, huCent, huphi⟩ :=
    exists_five_mem_inf_centralizer_not_mem_ker F hbA hbdeg
  refine ⟨u, huord, ?_, huphi⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzM : z ∈ D.M :=
    c.hyp81.1 ((F.A_le.trans F.P_le_L) ((Subgroup.zpowers_le.mpr hbA) hz))
  have hzBM : (⟨z, hzM⟩ : ↥D.M) ∈ (Subgroup.zpowers b).subgroupOf D.M := hz
  exact congrArg (fun t : ↥D.M => (t : G))
    (Subgroup.mem_centralizer_iff.mp huCent ⟨z, hzM⟩ hzBM)

private theorem exists_sylow_five_with_ker_element (F : A10Frame c) {b : G}
    (hbA : b ∈ F.A) (hbdeg : F.deg (Subgroup.zpowers b) = 3) :
    ∃ (R : Subgroup G) (y : ↥D.M), CFSG.ABGLocalTools.IsSylowOf 5 R
      (Subgroup.centralizer (Subgroup.zpowers b : Set G) ⊓ D.M) ∧
      (y : G) ∈ R ∧ orderOf (y : G) = 5 ∧ F.phiA y = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers b : Set G) ⊓ D.M
  obtain ⟨yM, hyord, hyphi, hyAcent⟩ := exists_five_mem_ker_centralizer_A F
  have hyCent : (yM : G) ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Subgroup.mem_centralizer_iff.mp hyAcent b hbA
  have hyC : (yM : G) ∈ C := Subgroup.mem_inf.mpr ⟨hyCent, yM.2⟩
  have hy5C : IsPGroup 5 (Subgroup.zpowers (⟨(yM : G), hyC⟩ : ↥C)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨(yM : G), hyC⟩ : ↥C), hyord]
      norm_num)
  obtain ⟨S, hyS⟩ := hy5C.exists_le_sylow
  let R : Subgroup G := (S : Subgroup ↥C).map C.subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 5 R C := ⟨S, rfl⟩
  have hyR : (yM : G) ∈ R :=
    Subgroup.mem_map.mpr ⟨⟨(yM : G), hyC⟩, hyS (Subgroup.mem_zpowers _), rfl⟩
  exact ⟨R, yM, hRsyl, hyR, hyord, hyphi⟩

private theorem exists_mem_sylow_not_mem_ker (F : A10Frame c) {b : G}
    (hbA : b ∈ F.A) (hbdeg : F.deg (Subgroup.zpowers b) = 3) {R : Subgroup G}
    (hRsyl : CFSG.ABGLocalTools.IsSylowOf 5 R
      (Subgroup.centralizer (Subgroup.zpowers b : Set G) ⊓ D.M)) :
    ∃ w : ↥D.M, (w : G) ∈ R ∧ orderOf (w : G) = 5 ∧ F.phiA w ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers b : Set G) ⊓ D.M
  obtain ⟨uM, huord, huCent, huphi⟩ := exists_five_mem_centralizer_not_mem_ker F hbA hbdeg
  have huC : (uM : G) ∈ C := Subgroup.mem_inf.mpr ⟨huCent, uM.2⟩
  have hu5C : IsPGroup 5 (Subgroup.zpowers (⟨(uM : G), huC⟩ : ↥C)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨(uM : G), huC⟩ : ↥C), huord]
      norm_num)
  obtain ⟨T, huT⟩ := hu5C.exists_le_sylow
  let R' : Subgroup G := (T : Subgroup ↥C).map C.subtype
  have hR'syl : CFSG.ABGLocalTools.IsSylowOf 5 R' C := ⟨T, rfl⟩
  have huR' : (uM : G) ∈ R' :=
    Subgroup.mem_map.mpr ⟨⟨(uM : G), huC⟩, huT (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨k, hkC, hkconj⟩ := hRsyl.exists_mem_conj hR'syl
  let w : G := k⁻¹ * (uM : G) * k
  have hwC : w ∈ C := C.mul_mem (C.mul_mem (C.inv_mem hkC) huC) hkC
  have hwR : w ∈ R := (hkconj (uM : G)).mp huR'
  have hword : orderOf w = 5 := by
    have hconj : w = MulAut.conj k⁻¹ (uM : G) := by
      rw [MulAut.conj_apply]
      show k⁻¹ * (uM : G) * k = k⁻¹ * (uM : G) * (k⁻¹)⁻¹
      group
    rw [hconj, MulEquiv.orderOf_eq, huord]
  have hwM : w ∈ D.M := (Subgroup.mem_inf.mp hwC).2
  have hw_notker : F.phiA ⟨w, hwM⟩ ≠ 1 := by
    intro h1
    apply huphi
    have hkM : k ∈ D.M := hkC.2
    have hwu : (⟨w, hwM⟩ : ↥D.M) = (⟨k, hkM⟩ : ↥D.M)⁻¹ * uM * ⟨k, hkM⟩ := by
      apply Subtype.ext
      change w = k⁻¹ * (uM : G) * k
      rfl
    have hconj : F.phiA ⟨w, hwM⟩ =
        (F.phiA ⟨k, hkM⟩)⁻¹ * F.phiA uM * F.phiA ⟨k, hkM⟩ := by
      rw [hwu, map_mul, map_mul, map_inv]
    rw [hconj] at h1
    calc F.phiA uM = F.phiA ⟨k, hkM⟩ *
          ((F.phiA ⟨k, hkM⟩)⁻¹ * F.phiA uM * F.phiA ⟨k, hkM⟩) *
            (F.phiA ⟨k, hkM⟩)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  refine ⟨⟨w, hwM⟩, hwR, ?_, hw_notker⟩
  simpa using hword

private theorem exists_sylow_five_not_isCyclic (F : A10Frame c) {b : G} (hbA : b ∈ F.A)
    (hbdeg : F.deg (Subgroup.zpowers b) = 3) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 5 R
      (Subgroup.centralizer (Subgroup.zpowers b : Set G) ⊓ D.M) ∧ ¬ IsCyclic ↥R := by
  classical
  obtain ⟨R, yM, hRsyl, hyR, hyord, hyphi⟩ :=
    exists_sylow_five_with_ker_element F hbA hbdeg
  obtain ⟨wM, hwR, hword, hwphi⟩ := exists_mem_sylow_not_mem_ker F hbA hbdeg hRsyl
  refine ⟨R, hRsyl, ?_⟩
  intro hcyc
  letI : IsCyclic ↥R := hcyc
  let yR : ↥R := ⟨(yM : G), hyR⟩
  let wR : ↥R := ⟨(wM : G), hwR⟩
  have hyRord : orderOf yR = 5 := by
    rw [← Subgroup.orderOf_coe yR]
    exact hyord
  have hwRord : orderOf wR = 5 := by
    rw [← Subgroup.orderOf_coe wR]
    exact hword
  have heq : Subgroup.zpowers yR = Subgroup.zpowers wR :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hyRord, hwRord])
  have hwRmem : wR ∈ Subgroup.zpowers yR := by
    rw [heq]
    exact Subgroup.mem_zpowers wR
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwRmem
  have hwzpow : (yM : G) ^ n = (wM : G) := by
    have h := congrArg (fun t : ↥R => (t : G)) hn
    simpa [yR, wR] using h
  have hwphi1 : F.phiA wM = 1 := by
    have hsub : wM = yM ^ n := by
      apply Subtype.ext
      simpa using hwzpow.symm
    rw [hsub, map_zpow, hyphi]
    simp
  exact hwphi hwphi1

theorem one_lt_pRank_five_centralizer_inf (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hdeg : F.deg B = 3) :
    1 < CFSG.Open.pRank 5 (Subgroup.centralizer (B : Set G) ⊓ D.M : Subgroup G) := by
  obtain ⟨b, rfl, -⟩ :=
    CFSG.GroupTheory.exists_zpowers_eq_of_card_eq_prime Nat.prime_three hB3
  have hbA : b ∈ F.A := hBA (Subgroup.mem_zpowers b)
  obtain ⟨R, hRsyl, hRnc⟩ := exists_sylow_five_not_isCyclic F hbA hdeg
  by_contra h
  have hle : CFSG.Open.pRank 5
      (Subgroup.centralizer (Subgroup.zpowers b : Set G) ⊓ D.M) ≤ 1 := by omega
  exact hRnc (CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_five (by norm_num)
    hRsyl.isPGroup hRsyl.le hle)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
