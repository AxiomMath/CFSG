module

public import CFSG.Quasithin.Vol2.Ch7Faith
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPQ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem isHatON_lbar_of_onan'_wPQ3
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩

theorem inf_centralizer_map_le_center'_wPQ3
    (c : Ctx82E3 D) (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)).subgroupOf c.L).map
        (QuotientGroup.mk' (pCore 2 ↥c.L)) ≤ Subgroup.center c.Lbar := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = (Q.subgroupOf c.L).map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hHat := isHatON_lbar_of_onan'_wPQ3 c hON
  have hcen := (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S).2.2.2
  rintro w ⟨z, hz, rfl⟩
  have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  have hzQ : (z : G) ∈ Q := hzZ.1
  have hzcent := hzZ.2
  have hzY : z ∈ Q.subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]; exact hzQ
  have hzS : π z ∈ (S : Subgroup c.Lbar) := by
    rw [hScoe]
    exact Subgroup.mem_map_of_mem π hzY
  refine hcen (π z) hzS ?_
  intro s hs
  rw [hScoe] at hs
  obtain ⟨q, hqY, rfl⟩ := Subgroup.mem_map.mp hs
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hqY
  exact Subgroup.mem_centralizer_iff.mp hzcent (q : G) hqQ

theorem zSub_le_modCentralizer'
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    zSub P c.L ≤ modCentralizer D.M c.L (inSubgroup (pCore 2) c.L) := by
  classical
  intro z hz
  have hzPL : z ∈ P ⊓ c.L := hz.1
  have hzZ : z ∈ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) := hz.2
  have hzL : z ∈ c.L := hzPL.2
  refine mem_modCentralizer_iff.mpr ⟨hP.le hzPL.1, Subgroup.le_normalizer hzL, ?_⟩
  intro l hl
  have hzcen : QuotientGroup.mk' (pCore 2 ↥c.L) (⟨z, hzL⟩ : ↥c.L) ∈ Subgroup.center c.Lbar := by
    have hZmem : (⟨z, hzL⟩ : ↥c.L) ∈
        (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)).subgroupOf c.L) :=
      Subgroup.mem_subgroupOf.mpr ⟨hzPL, hzZ⟩
    exact inf_centralizer_map_le_center'_wPQ3 c hON hP (Subgroup.mem_map_of_mem _ hZmem)
  have hcomm : QuotientGroup.mk' (pCore 2 ↥c.L) ⁅(⟨z, hzL⟩ : ↥c.L), (⟨l, hl⟩ : ↥c.L)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hzcen _).symm
  have hmemN : ⁅(⟨z, hzL⟩ : ↥c.L), (⟨l, hl⟩ : ↥c.L)⁆ ∈ pCore 2 ↥c.L :=
    (QuotientGroup.eq_one_iff _).mp hcomm
  have hmemO : ((⁅(⟨z, hzL⟩ : ↥c.L), (⟨l, hl⟩ : ↥c.L)⁆ : ↥c.L) : G) ∈
      (pCore 2 ↥c.L).map c.L.subtype :=
    Subgroup.mem_map_of_mem c.L.subtype hmemN
  change ((⁅(⟨z, hzL⟩ : ↥c.L), (⟨l, hl⟩ : ↥c.L)⁆ : ↥c.L) : G) ∈ inSubgroup (pCore 2) c.L
  simpa [inSubgroup] using hmemO

theorem p6_dichotomy' (c : Ctx82E3 D) {P A : Subgroup G} {a : G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJM : J = (J ⊓ D.M) ⊔ theta3 J)
    (hC : zSub P c.L ≤ modCentralizer D.M c.L (inSubgroup (pCore 2) c.L)) :
    zSub P c.L ≤ thetaQuotCentralizer J ∨ A ≤ thetaQuotCentralizer J := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, hL, hLJ⟩ := hJ
  let Cc : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let e₀ : ↥L ≃* ↥(L.map Cc.subtype) :=
    Subgroup.equivMapOfInjective L Cc.subtype Cc.subtype_injective
  let e : ↥L ≃* ↥J := e₀.trans (MulEquiv.subgroupCongr hLJ)
  have hQJ : CFSG.IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 J) := by
    refine (CFSG.RankThree.GroupTheory.SteinbergBY.isQuasisimple_thetaQuotient_iff_of_surjective
      Nat.prime_three hL.1 e.toMonoidHom e.surjective ?_).mp hL.2.2
    rw [show e.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    exact bot_le
  haveI : Group.IsPerfect (↥J ⧸ aschbacherSolvableCore 3 J) := hQJ.1
  let M : Subgroup G := D.M
  let O : Subgroup G := inSubgroup (pCore 2) c.L
  let Cmod : Subgroup G := modCentralizer D.M c.L O
  let J₁ : Subgroup G := J ⊓ M
  let K : Subgroup G := J₁ ⊓ Cmod
  let R : Subgroup G := J₁ ⊓ O
  let θ : Subgroup ↥J := aschbacherSolvableCore 3 J
  let πJ : ↥J →* (↥J ⧸ θ) := QuotientGroup.mk' θ
  let ψ : ↥J₁ →* (↥J ⧸ θ) := πJ.comp (Subgroup.inclusion (inf_le_left : J₁ ≤ J))
  let N : Subgroup (↥J ⧸ θ) := (K.subgroupOf J₁).map ψ
  let NR : Subgroup (↥J ⧸ θ) := (R.subgroupOf J₁).map ψ
  have hconjTheta : ∀ x ∈ J, ∀ t ∈ theta3 J, x * t * x⁻¹ ∈ theta3 J := by
    intro x hx t ht
    obtain ⟨t', ht'θ, rfl⟩ := Subgroup.mem_map.mp ht
    have hθn : (aschbacherSolvableCore 3 J).Normal := inferInstance
    have h := hθn.conj_mem t' ht'θ (⟨x, hx⟩ : ↥J)
    exact Subgroup.mem_map_of_mem J.subtype h
  have hJnormTheta : J ≤ Subgroup.normalizer (theta3 J : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    exact ⟨fun ht => hconjTheta x hx t ht, fun ht => by
      have h := hconjTheta x⁻¹ (J.inv_mem hx) (x * t * x⁻¹) ht
      rwa [show x⁻¹ * (x * t * x⁻¹) * (x⁻¹)⁻¹ = t by group] at h⟩
  have hJ₁normTheta : J₁ ≤ Subgroup.normalizer (theta3 J : Set G) :=
    inf_le_left.trans hJnormTheta
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨j, hjx⟩ := QuotientGroup.mk'_surjective θ x
    have hjmem : (j : G) ∈ J₁ ⊔ theta3 J := hJM ▸ j.2
    rw [sup_comm] at hjmem
    obtain ⟨t, ht, j₁, hj₁, htj⟩ :=
      (CFSG.Walter.W67.mem_sup_iff_of_le_normalizer hJ₁normTheta).1 hjmem
    have hj₁J : j₁ ∈ J := (Subgroup.mem_inf.mp hj₁).1
    have htJ : t ∈ J := Subgroup.map_subtype_le _ ht
    refine ⟨⟨j₁, hj₁⟩, ?_⟩
    rw [← hjx]
    have ht1 : πJ ⟨t, htJ⟩ = 1 := by
      obtain ⟨t', ht'θ, rfl⟩ := Subgroup.mem_map.mp ht
      exact (QuotientGroup.eq_one_iff (N := θ) t').mpr ht'θ
    have hjeq : j = ⟨t, htJ⟩ * ⟨j₁, hj₁J⟩ := Subtype.ext htj.symm
    rw [hjeq, map_mul, ht1, one_mul]
    rfl
  have hMnormL : M ≤ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L
  have hMnormO : M ≤ Subgroup.normalizer (O : Set G) :=
    c.le_normalizer_L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hconjC : ∀ m ∈ M, ∀ x ∈ Cmod, m * x * m⁻¹ ∈ Cmod := by
    intro m hm x hx
    exact conj_mem_modCentralizer hMnormL hMnormO hm hx
  have hKconj : ∀ x ∈ J₁, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    obtain ⟨hkJ₁, hkC⟩ := Subgroup.mem_inf.mp hk
    have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
    exact Subgroup.mem_inf.mpr
      ⟨J₁.mul_mem (J₁.mul_mem hx hkJ₁) (J₁.inv_mem hx), hconjC x hxM k hkC⟩
  have hKnormal : (K.subgroupOf J₁).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : K ≤ J₁)).mpr ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact ⟨fun hk => hKconj x hx k hk, fun hk => by
      have h := hKconj x⁻¹ (J₁.inv_mem hx) (x * k * x⁻¹) hk
      rwa [show x⁻¹ * (x * k * x⁻¹) * (x⁻¹)⁻¹ = k by group] at h⟩
  have hRconj : ∀ x ∈ J₁, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx r hr
    obtain ⟨hrJ₁, hrO⟩ := Subgroup.mem_inf.mp hr
    have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
    exact Subgroup.mem_inf.mpr
      ⟨J₁.mul_mem (J₁.mul_mem hx hrJ₁) (J₁.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hMnormO hxM) r).mp hrO⟩
  have hRnormal : (R.subgroupOf J₁).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : R ≤ J₁)).mpr ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro r
    exact ⟨fun hr => hRconj x hx r hr, fun hr => by
      have h := hRconj x⁻¹ (J₁.inv_mem hx) (x * r * x⁻¹) hr
      rwa [show x⁻¹ * (x * r * x⁻¹) * (x⁻¹)⁻¹ = r by group] at h⟩
  have hR2 : IsPGroup 2 ↥R :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype |>.to_le inf_le_right
  have hNR2 : IsPGroup 2 ↥NR := hR2.comap_subtype.map ψ
  have hNRsolv : Group.IsSolvable ↥NR := by
    haveI : Group.IsNilpotent ↥NR := hNR2.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hNnormal : N.Normal := hKnormal.map ψ hψsurj
  have hNRnormal : NR.Normal := hRnormal.map ψ hψsurj
  have hNRcenter : NR ≤ Subgroup.center (↥J ⧸ θ) := by
    letI : NR.Normal := hNRnormal
    exact le_center_of_normal_isSolvable hQJ.2.1 hNRsolv
  have mem_N : ∀ {g : G} (hgJ₁ : g ∈ J₁) (hgK : g ∈ K),
      πJ ⟨g, (Subgroup.mem_inf.mp hgJ₁).1⟩ ∈ N := by
    intro g hgJ₁ hgK
    exact Subgroup.mem_map.mpr ⟨⟨g, hgJ₁⟩, Subgroup.mem_subgroupOf.mpr hgK, rfl⟩
  have mem_NR : ∀ {g : G} (hgJ₁ : g ∈ J₁) (hgR : g ∈ R),
      πJ ⟨g, (Subgroup.mem_inf.mp hgJ₁).1⟩ ∈ NR := by
    intro g hgJ₁ hgR
    exact Subgroup.mem_map.mpr ⟨⟨g, hgJ₁⟩, Subgroup.mem_subgroupOf.mpr hgR, rfl⟩
  letI : N.Normal := hNnormal
  have hN : N ≤ Subgroup.center (↥J ⧸ θ) ∨ N = ⊤ :=
    CFSG.Quasithin.H13.normal_le_center_or_eq_top_of_quasisimple hQJ N
  rcases hN with hNcent | hNtop
  ·
    left
    intro z hz
    have hzA : z ∈ A := hZA hz
    have hzN : z ∈ Subgroup.normalizer (J : Set G) := hAJ hzA
    have hzC : z ∈ Cmod := hC hz
    have hzM : z ∈ M := (mem_modCentralizer_iff.mp hzC).1
    refine Subgroup.mem_map.mpr ⟨⟨z, hzN⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    let σ : MulAut (↥J ⧸ θ) := thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩)
    have hσ : σ = 1 := by
      refine eq_one_of_mul_inv_mem_center σ ?_
      intro x
      obtain ⟨k, hkx⟩ := hψsurj x
      rw [← hkx]
      have hkJ₁ : (k : G) ∈ J₁ := k.2
      have hkJ : (k : G) ∈ J := (Subgroup.mem_inf.mp hkJ₁).1
      have hkM : (k : G) ∈ M := (Subgroup.mem_inf.mp hkJ₁).2
      have hzkJ : z * (k : G) * z⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hzN (k : G)).mp hkJ
      have hzkM : z * (k : G) * z⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hzM hkM) (M.inv_mem hzM)
      have hzkJ₁ : z * (k : G) * z⁻¹ ∈ J₁ := Subgroup.mem_inf.mpr ⟨hzkJ, hzkM⟩
      have hcommJ₁ : ⁅z, (k : G)⁆ ∈ J₁ := J₁.mul_mem hzkJ₁ (J₁.inv_mem hkJ₁)
      have hcommJ : ⁅z, (k : G)⁆ ∈ J := (Subgroup.mem_inf.mp hcommJ₁).1
      have hkzC : (k : G) * z * (k : G)⁻¹ ∈ Cmod := hconjC (k : G) hkM z hzC
      have hkzcomm : ⁅(k : G), z⁆ ∈ Cmod := Cmod.mul_mem hkzC (Cmod.inv_mem hzC)
      have hcommC : ⁅z, (k : G)⁆ ∈ Cmod := by
        have h : ⁅z, (k : G)⁆ = ⁅(k : G), z⁆⁻¹ := by
          simp [commutatorElement_def]; group
        rw [h]; exact Cmod.inv_mem hkzcomm
      have hcommK : ⁅z, (k : G)⁆ ∈ K := Subgroup.mem_inf.mpr ⟨hcommJ₁, hcommC⟩
      have hπJ_coe : ∀ y : ↥J, πJ y = ((y : ↥J ⧸ θ)) := fun y => QuotientGroup.mk'_apply (N := θ) y
      have hψk : ψ k = ((⟨(k : G), hkJ⟩ : ↥J) : (↥J ⧸ θ)) := rfl
      have hσk : σ (ψ k) = πJ ⟨z * (k : G) * z⁻¹, hzkJ⟩ := by
        rw [hψk, thetaQuotMulAut_mk, hπJ_coe]
        congr 1
      have hstep : σ (ψ k) * (ψ k)⁻¹ = πJ ⟨⁅z, (k : G)⁆, hcommJ⟩ := by
        rw [hσk, hψk, ← hπJ_coe ⟨(k : G), hkJ⟩]
        rw [← map_inv (QuotientGroup.mk' θ), ← map_mul (QuotientGroup.mk' θ)]
        congr 1
      rw [hstep]
      exact hNcent (mem_N hcommJ₁ hcommK)
    exact hσ
  ·
    right
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (J : Set G) := hAJ hb
    have hbPL : b ∈ P ⊓ c.L := hAPL hb
    have hbM : b ∈ M := hP.le hbPL.1
    have hbL : b ∈ c.L := hbPL.2
    refine Subgroup.mem_map.mpr ⟨⟨b, hbN⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    let τ : MulAut (↥J ⧸ θ) := thetaQuotMulAut J (J.normalizerMonoidHom ⟨b, hbN⟩)
    have hτ : τ = 1 := by
      refine eq_one_of_mul_inv_mem_center τ ?_
      intro x
      have hxN : x ∈ N := by rw [hNtop]; exact Subgroup.mem_top x
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hxN
      rw [← hkx]
      have hkJ₁ : (k : G) ∈ J₁ := k.2
      have hkJ : (k : G) ∈ J := (Subgroup.mem_inf.mp hkJ₁).1
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have hkC : (k : G) ∈ Cmod := (Subgroup.mem_inf.mp hkK).2
      have hbkJ : b * (k : G) * b⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hbN (k : G)).mp hkJ
      have hbkM : b * (k : G) * b⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hbM (Subgroup.mem_inf.mp hkJ₁).2) (M.inv_mem hbM)
      have hbkJ₁ : b * (k : G) * b⁻¹ ∈ J₁ := Subgroup.mem_inf.mpr ⟨hbkJ, hbkM⟩
      have hcommJ₁ : ⁅b, (k : G)⁆ ∈ J₁ := J₁.mul_mem hbkJ₁ (J₁.inv_mem hkJ₁)
      have hcommJ : ⁅b, (k : G)⁆ ∈ J := (Subgroup.mem_inf.mp hcommJ₁).1
      have hkbO : ⁅(k : G), b⁆ ∈ O := (mem_modCentralizer_iff.mp hkC).2.2 b hbL
      have hcommO : ⁅b, (k : G)⁆ ∈ O := by
        have h : ⁅b, (k : G)⁆ = ⁅(k : G), b⁆⁻¹ := by
          simp [commutatorElement_def]; group
        rw [h]; exact O.inv_mem hkbO
      have hcommR : ⁅b, (k : G)⁆ ∈ R := Subgroup.mem_inf.mpr ⟨hcommJ₁, hcommO⟩
      have hπJ_coe : ∀ y : ↥J, πJ y = ((y : ↥J ⧸ θ)) := fun y => QuotientGroup.mk'_apply (N := θ) y
      have hψk : ψ k = ((⟨(k : G), hkJ⟩ : ↥J) : (↥J ⧸ θ)) := rfl
      have hτk : τ (ψ k) = πJ ⟨b * (k : G) * b⁻¹, hbkJ⟩ := by
        rw [hψk, thetaQuotMulAut_mk, hπJ_coe]
        congr 1
      have hstep : τ (ψ k) * (ψ k)⁻¹ = πJ ⟨⁅b, (k : G)⁆, hcommJ⟩ := by
        rw [hτk, hψk, ← hπJ_coe ⟨(k : G), hkJ⟩]
        rw [← map_inv (QuotientGroup.mk' θ), ← map_mul (QuotientGroup.mk' θ)]
        congr 1
      rw [hstep]
      exact hNRcenter (mem_NR hcommJ₁ hcommR)
    exact hτ

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
