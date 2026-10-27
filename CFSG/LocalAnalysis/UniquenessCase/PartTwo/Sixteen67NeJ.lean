module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeH
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem le_centralizer_of_eq_zpowers (h : Cfg1667Ne M V₀ V W₁ W₂) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    V ⊔ conjSubgroup V g ≤ centralizer ({z} : Set G) := by
  have hzmem : z ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hzV : z ∈ V := hzmem.1.1
  have hzVg : z ∈ conjSubgroup V g := hzmem.2.1
  refine sup_le ?_ ?_
  · intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm ⟨v, hv⟩ ⟨z, hzV⟩)
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp
      (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1).is_comm.comm ⟨x, hx⟩ ⟨z, hzVg⟩)

theorem not_centralizer_le (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ centralizer ({z} : Set G) ≤ M := by
  intro hle
  have hle' : conjSubgroup V g ≤ centralizer ({z} : Set G) :=
    le_sup_right.trans (h.le_centralizer_of_eq_zpowers hz)
  exact hg.1.1 (hle'.trans hle)

theorem three_dvd_orderOf_sq (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {t i : G} (ht : t ∈ V) (htU : t ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) : 3 ∣ orderOf ((t * i) ^ 2) := by
  set x : G := t * i with hx
  have hx3 : x ^ 3 ∈ (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) := by
    rw [hx]
    exact cube_mem_K h hs hs' ht htU hi hiB
  have hKM : (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) ≤ M := K_le_M h
  have hx3M : x ^ 3 ∈ M := hKM hx3
  by_contra h3
  have hcop : Nat.Coprime 3 (orderOf (x ^ 2)) :=
    (Nat.prime_three.coprime_iff_not_dvd).2 h3
  have hx2zp : x ^ 2 ∈ Subgroup.zpowers ((x ^ 2) ^ 3) := by
    rw [mem_zpowers_pow_iff]
    exact hcop
  have hx6 : (x ^ 2) ^ 3 = (x ^ 3) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
  have hx2M : x ^ 2 ∈ M := by
    have hpow : (x ^ 3) ^ 2 ∈ M := pow_mem hx3M 2
    have hle : Subgroup.zpowers ((x ^ 2) ^ 3) ≤ M := by
      rw [hx6]
      exact Subgroup.zpowers_le.mpr hpow
    exact hle hx2zp
  have hxM : x ∈ M := by
    have h2 : x ^ 3 * (x ^ 2)⁻¹ ∈ M := M.mul_mem hx3M (M.inv_mem hx2M)
    rwa [show x ^ 3 * (x ^ 2)⁻¹ = x by group] at h2
  have hiM : i ∈ M := by
    have h2 : t⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (h.le_M ht)) hxM
    rw [hx] at h2
    simpa using h2
  exact hiB ⟨hi, hiM⟩

theorem inf_relPPrimeCore_le (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    V ⊓ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) ≤ V ⊓ conjSubgroup M g := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  change V ⊓ K ≤ V ⊓ conjSubgroup M g
  intro y hy
  obtain ⟨hyV, hyK⟩ := Subgroup.mem_inf.mp hy
  by_contra hyU
  have hVgH : conjSubgroup V g ≤ H := le_sup_right.trans (h.le_centralizer_of_eq_zpowers hz)
  have hKH : K ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hKN : (K.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three H
  obtain ⟨i, hiVg, hiB, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := conjSubgroup V g ⊓ M) (K := conjSubgroup V g)).mp (relIndex_B h hs.1)
  have hi2 : i * i = 1 := by
    simpa [pow_two] using (h.conj g).elemAbelian.2 i hiVg
  have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hyi2K : (y * i) ^ 2 ∈ K := by
    have hnorm : i ∈ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKN (hVgH hiVg)
    have hconjK : i * y * i⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hnorm y).1 hyK
    have heq : (y * i) ^ 2 = y * (i * y * i⁻¹) := by
      rw [pow_two, hii]
      group
    rw [heq]
    exact K.mul_mem hyK hconjK
  have hdvdK : orderOf ((y * i) ^ 2) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hyi2K
  have h3 := three_dvd_orderOf_sq h hs hs' hyV hyU hiVg hiB
  have h3K : 3 ∣ Nat.card K := h3.trans hdvdK
  exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop h3K

theorem not_le_relPPrimeCore (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ V ≤ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))
  change ¬ V ≤ K
  intro hVK
  have hinf : V ⊓ K ≤ V ⊓ conjSubgroup M g := inf_relPPrimeCore_le h hs hs' hz
  obtain ⟨t, htV, htU, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := V ⊓ conjSubgroup M g) (K := V)).mp (relIndex_U h hs.1)
  exact htU (hinf (Subgroup.mem_inf.mpr ⟨htV, hVK htV⟩))

theorem V₀_le_relPPrimeCore (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z)
    (hK : (CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))).relIndex V ≤ 2) :
    V₀ ≤ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let A : Subgroup G := V ⊓ K
  change V₀ ≤ K
  have hAU : A ≤ U := inf_relPPrimeCore_le h hs hs' hz
  have hUV : U ≤ V := inf_le_left
  have hArelV : A.relIndex V = K.relIndex V := by
    change (V ⊓ K).relIndex V = K.relIndex V
    exact Subgroup.inf_relIndex_left V K
  have hUVrel : U.relIndex V = 2 := relIndex_U h hs.1
  have hprod : A.relIndex U * 2 = K.relIndex V := by
    calc A.relIndex U * 2 = A.relIndex U * U.relIndex V := by rw [hUVrel]
      _ = A.relIndex V := Subgroup.relIndex_mul_relIndex A U V hAU hUV
      _ = K.relIndex V := hArelV
  have hne : A.relIndex U ≠ 0 := by
    intro h0
    have hcard := Subgroup.relIndex_mul_card (H := A) (K := U)
    rw [h0, zero_mul] at hcard
    exact (Nat.card_pos (α := U)).ne' hcard.symm
  have h1 : A.relIndex U = 1 := by
    have h2 : A.relIndex U * 2 ≤ 2 := hprod.le.trans hK
    have hne' : 0 < A.relIndex U := Nat.pos_of_ne_zero hne
    omega
  have hUA : U ≤ A := Subgroup.relIndex_eq_one.mp h1
  exact (V₀_le_U h hs).trans (hUA.trans inf_le_right)

theorem not_le_sup_relPPrimeCore (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ centralizer ({z} : Set G) ≤
      centralizer ({z} : Set G) ⊓ M ⊔ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  change ¬ H ≤ H ⊓ M ⊔ K
  intro hle
  have hVH : V ≤ H := le_sup_left.trans (h.le_centralizer_of_eq_zpowers hz)
  have hVgH : conjSubgroup V g ≤ H := le_sup_right.trans (h.le_centralizer_of_eq_zpowers hz)
  have hKH : K ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hKN : (K.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hHnormK : H ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKN
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three H
  obtain ⟨t, htV, htU, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := V ⊓ conjSubgroup M g) (K := V)).mp (relIndex_U h hs.1)
  obtain ⟨i, hiVg, hiB, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := conjSubgroup V g ⊓ M) (K := conjSubgroup V g)).mp (relIndex_B h hs.1)
  have hiH : i ∈ H := hVgH hiVg
  have hHMnormK : H ⊓ M ≤ normalizer (K : Set G) := inf_le_left.trans hHnormK
  have hicoe : i ∈ ((H ⊓ M : Subgroup G) : Set G) * (K : Set G) := by
    have hmem : i ∈ (((H ⊓ M) ⊔ K : Subgroup G) : Set G) := hle hiH
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (H ⊓ M) K hHMnormK] at hmem
    exact hmem
  obtain ⟨m, hmHM, k, hkK, hmk⟩ := hicoe
  have hi2 : i * i = 1 := by
    simpa [pow_two] using (h.conj g).elemAbelian.2 i hiVg
  have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hmM : m ∈ M := hmHM.2
  have hmNormV : m ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hmM
  have hmtV : m * t * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hmNormV t).1 htV
  have hvV : t * (m * t * m⁻¹) ∈ V := V.mul_mem htV hmtV
  have hk1K : m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹ ∈ K := by
    have htK : t⁻¹ * k * t ∈ K := by
      have hnorm : t ∈ normalizer (K : Set G) := hHnormK (hVH htV)
      exact (Subgroup.mem_normalizer_iff''.mp hnorm k).1 hkK
    have hprod : (t⁻¹ * k * t) * k⁻¹ ∈ K := K.mul_mem htK (K.inv_mem hkK)
    have hnorm : m ∈ normalizer (K : Set G) := hHnormK hmHM.1
    exact (Subgroup.mem_normalizer_iff.mp hnorm _).1 hprod
  set y : G := (t * i) ^ 2 with hy
  have hy_eq : y = (t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
    have hconj : i * t * i⁻¹ = (m * t * m⁻¹) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
      rw [← hmk]
      group
    calc y = t * (i * t * i⁻¹) := by rw [hy, pow_two, hii]; group
      _ = (t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
        rw [hconj]; group
  have hy2K : y ^ 2 ∈ K := by
    have hv2 : (t * (m * t * m⁻¹)) * (t * (m * t * m⁻¹)) = 1 := by
      simpa [pow_two] using h.elemAbelian.2 (t * (m * t * m⁻¹)) hvV
    have hvinv : (t * (m * t * m⁻¹))⁻¹ = t * (m * t * m⁻¹) :=
      inv_eq_of_mul_eq_one_right hv2
    have hmem : (t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹)
        * (t * (m * t * m⁻¹))⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHnormK (hVH hvV)) _).1 hk1K
    rw [hy_eq]
    have hsq : ((t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹)) ^ 2
        = ((t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹)
            * (t * (m * t * m⁻¹))⁻¹) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
      rw [pow_two, hvinv]
      group
    rw [hsq]
    exact K.mul_mem hmem hk1K
  have hdvdK : orderOf (y ^ 2) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hy2K
  have h3y : 3 ∣ orderOf y := by
    rw [hy]
    exact three_dvd_orderOf_sq h hs hs' htV htU hiVg hiB
  have h3y2 : 3 ∣ orderOf (y ^ 2) := by
    by_contra h3
    have h1 : orderOf y ∣ 2 * orderOf (y ^ 2) := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
      exact pow_orderOf_eq_one (y ^ 2)
    have h3dvd : 3 ∣ 2 * orderOf (y ^ 2) := h3y.trans h1
    have h32 : Nat.Coprime 3 2 := by norm_num
    exact h3 (h32.dvd_of_dvd_mul_left h3dvd)
  have h3K : 3 ∣ Nat.card K := h3y2.trans hdvdK
  exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop h3K

end Cfg1667Ne

theorem s1667ne_pRank_centralizer (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hsit : Sit1665 D V₀ V hV L) {z : G}
    (hzV : z ∈ V) (hz : orderOf z = 2) (hnot : ¬ centralizer ({z} : Set G) ≤ D.M) :
    CFSG.Open.pRank 3 (centralizer ({z} : Set G)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    sixteen_sixtyEight_k D hSg h1219 V₀ V L hV hS hsit
  have h3sig : 3 ∈ D.sig := by
    rw [hsit.1.2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨p, hp, hpv⟩ := h21 V₀ V hS.setting.hyp16
  have hp3 : p = 3 := by
    have h1 : ({p} : Set ℕ) = {3} := hp.symm.trans hsit.1.2.2.2
    exact Set.singleton_eq_singleton_iff.mp h1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← hz]
    exact pow_orderOf_eq_one z
  have h3 : 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({z} : Set G)) := by
    have h4 := hpv z hzV hz1
    rwa [hp3] at h4
  exact pRank_three_centralizer D h61 h3sig hse hz1 hz2 hnot h3

theorem s1667ne_isStronglyPEmbedded (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hsit : Sit1665 D V₀ V hV L) {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hnot : ¬ centralizer ({z} : Set G) ≤ D.M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3
      ((centralizer ({z} : Set G) ⊓ D.M).subgroupOf (centralizer ({z} : Set G))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    sixteen_sixtyEight_k D hSg h1219 V₀ V L hV hS hsit
  obtain ⟨p, hp, hpv⟩ := h21 V₀ V hS.setting.hyp16
  have hp3 : p = 3 := by
    have h1 : ({p} : Set ℕ) = {3} := hp.symm.trans hsit.1.2.2.2
    exact Set.singleton_eq_singleton_iff.mp h1
  have hpv3 : 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({z} : Set G)) := by
    have h4 := hpv z hzV hz1
    rwa [hp3] at h4
  have hdvd : 3 ∣ Nat.card (centralizer ({z} : Set G) ⊓ D.M : Subgroup G) := by
    rw [inf_comm]
    exact CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hpv3
  exact hse.subgroupOf hnot hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
