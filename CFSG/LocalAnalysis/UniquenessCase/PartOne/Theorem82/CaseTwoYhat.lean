module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoXhat
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11
public import CFSG.GroupTheory.HallHigmanPiCore
import all CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] noncomputable def Yhat : Subgroup t.Xhat :=
  ((c.S.M).subgroupOf t.Xz).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))

theorem normalizer_Zhat_le_Yhat {p : ℕ} (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.normalizer (t.Zhat : Set t.Xhat) ≤ t.Yhat := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : IsPGroup 3 (t.Z.subgroupOf t.Xz) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe t.Z_le_Xz).toEquiv, t.card_Z]
    norm_num
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥t.Xz) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hmap : (Subgroup.normalizer (t.Z.subgroupOf t.Xz : Set ↥t.Xz)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) =
      Subgroup.normalizer (t.Zhat : Set t.Xhat) := by
    simpa only [Zhat] using CFSG.GroupTheory.normal_coprime_quotient_normalizer 3
      (CFSG.pPrimeCore 3 ↥t.Xz) hcop (t.Z.subgroupOf t.Xz) hZ3
  rw [← hmap]
  intro xhat hxhat
  obtain ⟨x, hxnorm, hxπ⟩ := Subgroup.mem_map.mp hxhat
  refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr ?_, hxπ⟩
  have hxN : x ∈ (Subgroup.normalizer (t.Z : Set G)).subgroupOf t.Xz := by
    rw [Subgroup.subgroupOf_normalizer_eq t.Z_le_Xz]
    exact hxnorm
  exact t.normalizer_Z_le hp hN hZ (Subgroup.mem_subgroupOf.mp hxN)

theorem not_isPSolvable_of_ker_le (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {X : Type} [Group X]
    [Finite X] (φ : ↥t.Ky →* X)
    (hφ : φ.ker ≤ (t.Ky ⊓ t.d.N).subgroupOf t.Ky) :
    ¬ CFSG.HallHigman.IsPSolvable 3 X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T : Subgroup ↥t.Ky := (t.Ky ⊓ t.d.N).subgroupOf t.Ky
  have hφT : φ.ker ≤ T := hφ
  have hKyN : t.Ky ≤ Subgroup.normalizer (t.d.N : Set G) := by
    have h := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
    have hdN : t.d.N = CFSG.Open.pCoreOf 2 c.S.M := by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    rw [hdN]
    exact ((t.Ky_le.trans inf_le_left).trans c.hyp81.1).trans h
  have hInfNorm : t.Ky ≤ Subgroup.normalizer ((t.Ky ⊓ t.d.N : Subgroup G) : Set G) := by
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.Ky) (K := t.d.N)
      ⟨Subgroup.le_normalizer hk, hKyN hk⟩
  haveI hTnormal : T.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hInfNorm
  have hZleKy : t.Z ≤ t.Ky :=
    (le_inf (t.Z_le_AA.trans t.d.AA_le_S) t.Z_le_centralizer).trans t.Dz_le_Ky
  have hZdisj : t.Z ⊓ t.d.N = ⊥ := by
    have h2 : IsPGroup 2 ↥(t.Z ⊓ t.d.N) :=
      (SylowThreeData.N_isPGroup t.d).to_le inf_le_right
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdiv : 2 ^ n ∣ 3 := by
      rw [← hn, ← t.card_Z]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hn0 : n = 0 := by
      by_contra hne
      exact absurd ((dvd_pow_self 2 hne).trans hdiv) (by norm_num)
    have hcard : Nat.card ↥(t.Z ⊓ t.d.N) = 1 := by rw [hn, hn0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hcard
  let Zs : Subgroup ↥t.Ky := t.Z.subgroupOf t.Ky
  have hZs_card : Nat.card Zs = 3 := by
    rw [← t.card_Z]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleKy).toEquiv
  have hZs_inf_T : Zs ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases Subgroup.mem_inf.mp hx with ⟨hxZ, hxT⟩
    have hxZ' : (x : G) ∈ t.Z := Subgroup.mem_subgroupOf.mp hxZ
    have hxN : (x : G) ∈ t.d.N := (Subgroup.mem_subgroupOf.mp hxT).2
    have hxbot : (x : G) ∈ t.Z ⊓ t.d.N := Subgroup.mem_inf.mpr ⟨hxZ', hxN⟩
    rw [hZdisj] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  let qT : ↥t.Ky →* ↥t.Ky ⧸ T := QuotientGroup.mk' T
  have hcomp_inj : Function.Injective (qT.comp Zs.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hz
      have hzT : (z : ↥t.Ky) ∈ T := (QuotientGroup.eq_one_iff (z : ↥t.Ky)).mp hz
      have hmem : (z : ↥t.Ky) ∈ Zs ⊓ T := Subgroup.mem_inf.mpr ⟨z.2, hzT⟩
      rw [hZs_inf_T, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hz
      rw [hz]
      simp
  have himg_card : Nat.card (Zs.map qT) = 3 := by
    have hrange : (qT.comp Zs.subtype).range = Zs.map qT := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact Subgroup.mem_map.mpr ⟨z, z.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hcomp_inj).toEquiv, hZs_card]
  have h3dvd : 3 ∣ T.index := by
    have hdvd : Nat.card (Zs.map qT) ∣ T.index := by
      rw [Subgroup.index_eq_card T]
      exact Subgroup.card_subgroup_dvd_card (Zs.map qT)
    rwa [himg_card] at hdvd
  have hmax : ∀ S : Subgroup ↥t.Ky, S.Normal → T ≤ S → S = T ∨ S = ⊤ := by
    intro S hS hTS
    let S' : Subgroup G := S.map t.Ky.subtype
    have hS'le : S' ≤ t.Ky := Subgroup.map_subtype_le S
    have hS'norm : t.Ky ≤ Subgroup.normalizer (S' : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨⟨k, hk⟩ * s * ⟨k, hk⟩⁻¹, hS.conj_mem s hs ⟨k, hk⟩,
            by simp [MulAut.conj_apply, mul_assoc]⟩
      · intro hx
        have hxK : x ∈ t.Ky := by
          have hconjKy : k * x * k⁻¹ ∈ t.Ky := hS'le hx
          have := t.Ky.mul_mem (t.Ky.mul_mem (t.Ky.inv_mem hk) hconjKy) hk
          simpa [mul_assoc] using this
        obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.mp hx
        have hconj : (⟨k, hk⟩ : ↥t.Ky)⁻¹ * s * ⟨k, hk⟩ ∈ S := by
          simpa using hS.conj_mem s hs (⟨k, hk⟩ : ↥t.Ky)⁻¹
        have heq : ((⟨k, hk⟩ : ↥t.Ky)⁻¹ * s * ⟨k, hk⟩ : ↥t.Ky) = ⟨x, hxK⟩ := by
          apply Subtype.ext
          change (k : G)⁻¹ * (s : G) * (k : G) = x
          have hsk' : (s : G) = k * x * k⁻¹ := hsk
          rw [hsk']
          group
        exact Subgroup.mem_map.mpr ⟨_, hconj, by simp [heq]⟩
    rcases t.le_N_or_eq_Ky hK32 hGA hSp hS'le hS'norm with hle | heq
    · left
      refine le_antisymm ?_ hTS
      intro s hs
      have hsS' : (s : G) ∈ S' := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
      have hsN : (s : G) ∈ t.d.N := hle hsS'
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨s.2, hsN⟩)
    · right
      refine le_antisymm le_top ?_
      intro s _
      have hsS' : (s : G) ∈ S' := by rw [heq]; exact s.2
      obtain ⟨s0, hs0, hs0eq⟩ := Subgroup.mem_map.mp hsS'
      have hseq : s0 = s := Subtype.ext hs0eq
      rwa [hseq] at hs0
  have hT_ne_top : T ≠ ⊤ := by
    intro htop
    have h1 : T.index = 1 := by rw [htop, Subgroup.index_top]
    have h3 : 3 ∣ 1 := by rwa [h1] at h3dvd
    norm_num at h3
  have hsimple : IsSimpleGroup (↥t.Ky ⧸ T) :=
    CFSG.HallHigman.isSimpleGroup_quotient_of_maximal hT_ne_top hmax
  haveI hPerfKy : Group.IsPerfect ↥t.Ky :=
    Subgroup.isPerfect_iff.mpr t.commutator_Ky
  have hPerfKyT : Group.IsPerfect (↥t.Ky ⧸ T) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T)
      (QuotientGroup.mk'_surjective T)
  haveI : Group.IsPerfect (↥t.Ky ⧸ T) := hPerfKyT
  let T' : Subgroup (↥t.Ky ⧸ φ.ker) := T.map (QuotientGroup.mk' φ.ker)
  haveI hT'normal : T'.Normal := hTnormal.map _ (QuotientGroup.mk'_surjective φ.ker)
  let e := QuotientGroup.quotientQuotientEquivQuotient (N := φ.ker) (M := T) hφT
  have hT'simple : IsSimpleGroup ((↥t.Ky ⧸ φ.ker) ⧸ T') := by
    have h := (MulEquiv.isSimpleGroup_congr e).mpr hsimple
    simpa [T', e] using h
  have h3dvd' : 3 ∣ T'.index := by
    have h : T'.index = T.index := by
      simpa [T'] using Subgroup.index_map_eq T
        (QuotientGroup.mk'_surjective φ.ker) (by simpa using hφT)
    rwa [h]
  intro hPS
  have hsep : CFSG.HallHigman.IsPiSeparable {q : Nat.Primes | q.val = 3} X :=
    CFSG.HallHigman.isPiSeparable_of_isPSolvable Nat.prime_three hPS
  have hsec := CFSG.HallHigman.IsPiSeparable.section_index (Nat.card X) rfl
    hsep (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ) T' hT'simple
  rcases hsec with hall | hnone
  · have hpos : T'.index ≠ 0 := by
      rw [Subgroup.index_eq_card T']
      exact Nat.card_pos.ne'
    have hpow : T'.index = 3 ^ T'.index.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hpos
        (fun hq hd => hall ⟨_, hq⟩ hd)
    have hcardA : Nat.card ((↥t.Ky ⧸ φ.ker) ⧸ T') =
        3 ^ T'.index.primeFactorsList.length := by
      rw [← Subgroup.index_eq_card T']
      exact hpow
    haveI hP : IsPGroup 3 ((↥t.Ky ⧸ φ.ker) ⧸ T') := IsPGroup.of_card hcardA
    haveI hPerfA : Group.IsPerfect ((↥t.Ky ⧸ φ.ker) ⧸ T') :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hsub : Subsingleton ((↥t.Ky ⧸ φ.ker) ⧸ T') := by
      by_contra hns
      haveI : Nontrivial ((↥t.Ky ⧸ φ.ker) ⧸ T') :=
        not_subsingleton_iff_nontrivial.1 hns
      exact Group.IsPerfect.not_isNilpotent
        (G := ((↥t.Ky ⧸ φ.ker) ⧸ T')) hP.isNilpotent
    exact (not_subsingleton_iff_nontrivial.mpr hT'simple.toNontrivial) hsub
  · exact hnone ⟨3, Nat.prime_three⟩ h3dvd' rfl

theorem not_isPSolvable_Yhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥t.Yhat := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKYX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  let π : ↥t.Xz →* t.Xhat := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)
  let ψ : ↥t.Ky →* t.Xhat := π.comp (Subgroup.inclusion hKYX)
  let φ : ↥t.Ky →* ↥t.Yhat := ψ.codRestrict t.Yhat fun k =>
    Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKYX k,
      Subgroup.mem_subgroupOf.mpr (c.hyp81.1 (t.Ky_le k.2).1), rfl⟩
  refine t.not_isPSolvable_of_ker_le hK32 hGA hSp φ ?_
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hk1 : π ⟨k, hKYX k.2⟩ = 1 := by
    have h := congrArg Subtype.val hk
    change π ⟨k, hKYX k.2⟩ = 1 at h
    exact h
  have hkO : ⟨k, hKYX k.2⟩ ∈ CFSG.pPrimeCore 3 ↥t.Xz :=
    (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥t.Xz) _).mp hk1
  have hkOz : (k : G) ∈ t.Oz :=
    Subgroup.mem_map.mpr ⟨⟨k, hKYX k.2⟩, hkO, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_inf.mpr ⟨k.2, t.Ky_inf_Oz_le hK32 hGA hSp ⟨k.2, hkOz⟩⟩)

theorem Xz_le_of_Yhat_eq_top (hO : t.Oz ≤ c.S.M) (hY : t.Yhat = ⊤) : t.Xz ≤ c.S.M := by
  intro x hx
  have hxY : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz) ⟨x, hx⟩ ∈ t.Yhat := by
    rw [hY]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hπ⟩ := Subgroup.mem_map.mp hxY
  have hmM : (m : G) ∈ c.S.M := Subgroup.mem_subgroupOf.mp hm
  have hker : (m⁻¹ * ⟨x, hx⟩ : ↥t.Xz) ∈ CFSG.pPrimeCore 3 ↥t.Xz := by
    refine (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥t.Xz)
      (m⁻¹ * ⟨x, hx⟩)).mp ?_
    change (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) (m⁻¹ * ⟨x, hx⟩) = 1
    rw [map_mul, map_inv, hπ]
    simp
  have hOz : ((m⁻¹ * ⟨x, hx⟩ : ↥t.Xz) : G) ∈ t.Oz :=
    Subgroup.mem_map.mpr ⟨_, hker, rfl⟩
  have hM : ((m⁻¹ * ⟨x, hx⟩ : ↥t.Xz) : G) ∈ c.S.M := hO hOz
  have hxeq : (x : G) = (m : G) * ((m⁻¹ * ⟨x, hx⟩ : ↥t.Xz) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hxeq]
  exact c.S.M.mul_mem hmM hM

theorem centralizer_y_le_of_K11 (hK11 : K11)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    {p : ℕ} (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) (hO : t.Oz ≤ c.S.M)
    (hX : (∃ ℓ f : ℕ, CFSG.Blueprint.LieModel t.Xhat .PSL 2 ℓ f) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor t.Xhat .J1) :
    Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M := by
  have hY : t.Yhat = ⊤ :=
    hK11 t.Xhat (t.isSimpleGroup_Xhat hK32 hGA hSp hK332 hOut hp hN hZ)
      (fun P hP => t.isCyclic_of_isPGroup_Xhat hK32 hGA hSp hK332 hOut hp hN hZ
        (P := P) hP) hX t.Zhat t.Yhat
      t.card_Zhat (t.normalizer_Zhat_le_Yhat hp hN hZ)
      (t.not_isPSolvable_Yhat hK32 hGA hSp)
  exact (t.centralizer_y_le_iff hK32 hGA hSp hK332 hOut hp hN hZ).mpr
    (t.Xz_le_of_Yhat_eq_top hO hY)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
