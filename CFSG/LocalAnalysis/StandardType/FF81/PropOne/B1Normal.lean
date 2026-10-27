module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.IsoTau
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NCore
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NIrr
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NEigen
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NDecomp
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NFix
public import CFSG.Mathlib.GroupTheory.ZStarModular
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aCBY
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aYAbelian
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aYneBot
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aCenYTau
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Dihedral.BrauerSuzuki.Helpers
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aCenEqNor
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aY1Fix
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aZStarFull
public import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

namespace B1Normal

open scoped Pointwise

private theorem bulk {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {s : G} (hsN : s ∈ nB b z)
    (hiso : ∀ g ∈ nB b z,
      g * s * g⁻¹ * s * (g * s * g⁻¹)⁻¹ * s⁻¹ ∈ cB b z → g * s * g⁻¹ * s⁻¹ ∈ cB b z)
    (hpat : (s * b * s⁻¹ = b ∧ ∀ i : Fin 3, s * GGFF.zs z i * s⁻¹ = (GGFF.zs z i)⁻¹) ∨
      (s * b * s⁻¹ = b⁻¹ ∧ ∀ i : Fin 3, s * GGFF.zs z i * s⁻¹ = GGFF.zs z i))
    {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G}
    (hMono : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Mono b (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirrMono : ∀ H : Subgroup G, H ≤ bOne z → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = bOne z)
    (hB1not : ∃ m ∈ nB b z, ∃ y ∈ bOne z, m * y * m⁻¹ ∉ bOne z) : False := by
  classical
  let Bs : Subgroup G := GGFF.Bt b z
  let N : Subgroup G := nB b z
  let K : Subgroup G := cB b z
  have hBK : K ≤ N := by
    simpa [K, N] using (Subgroup.centralizer_le_normalizer (s := (Bs : Set G)))
  let φ : N →* MulAut ↥Bs := Bs.normalizerMonoidHom
  let X : Subgroup (MulAut ↥Bs) := φ.range
  have hs := h.settingCore
  have hE4 : CFSG.RankThree.PartTwo.Sec21.FF79.IsElemAb 3 4 Bs := isElemAb_Bt h
  have hkerφ : φ.ker = K.subgroupOf N := by
    simpa [φ, Bs, K, N] using Bs.normalizerMonoidHom_ker
  have hφ_one : ∀ q : N, φ q = 1 ↔ (q : G) ∈ K := by
    intro q
    rw [← MonoidHom.mem_ker, hkerφ, Subgroup.mem_subgroupOf]
  have hval_gen : ∀ (g : G) (hg : g ∈ N) (a : ↥Bs),
      (((φ ⟨g, hg⟩) a : ↥Bs) : G) = g * (a : G) * g⁻¹ := fun g hg a =>
    normHom_apply_coe g hg a
  have hEA : IsElementaryAbelian 3 ↥Bs := hE4.1
  have hCommB : IsMulCommutative ↥Bs := hE4.1.toIsMulCommutative
  have hCommBs : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with
      mul_comm := fun x y => mul_comm' x y }
  have hpowBs : ∀ x : ↥Bs, x ^ 3 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 ↥Bs) x
  have hgen : Subgroup.closure ({bG, zsG 0, zsG 1, zsG 2} : Set ↥Bs) = ⊤ := closure_four_gens
  have hbGne : (bG : ↥Bs) ≠ 1 := by
    intro h
    exact hs.b_ne_one (congrArg Subtype.val h)
  have hord_bG : orderOf (bG : ↥Bs) = 3 := orderOf_eq_prime (hpowBs bG) hbGne
  have hz0ne : (zsG 0 : ↥Bs) ≠ 1 := by
    intro h1
    have h1' : ((zsG 0 : ↥Bs) : G) = 1 := congrArg Subtype.val h1
    exact h.model.z_ne_one 0 (Subtype.ext (by simpa [zsG] using h1'))
  obtain ⟨sX, hsXeq⟩ : ∃ sX : MulAut ↥Bs, sX = φ ⟨s, hsN⟩ := ⟨_, rfl⟩
  have hSmem : sX ∈ X := by
    rw [hsXeq]
    exact ⟨⟨s, hsN⟩, rfl⟩
  have hsXpat : (sX bG = bG ∧ ∀ i : Fin 3, sX (zsG i) = (zsG i)⁻¹) ∨
      (sX bG = bG⁻¹ ∧ ∀ i : Fin 3, sX (zsG i) = zsG i) := by
    rcases hpat with ⟨hb, hz⟩ | ⟨hb, hz⟩
    · refine Or.inl ⟨?_, fun i => ?_⟩
      · apply Subtype.ext
        simpa [hsXeq, hval_gen s hsN, bG] using hb
      · apply Subtype.ext
        simpa [hsXeq, hval_gen s hsN, zsG] using hz i
    · refine Or.inr ⟨?_, fun i => ?_⟩
      · apply Subtype.ext
        simpa [hsXeq, hval_gen s hsN, bG] using hb
      · apply Subtype.ext
        simpa [hsXeq, hval_gen s hsN, zsG] using hz i
  have hsXsign : ∀ x ∈ ({bG, zsG 0, zsG 1, zsG 2} : Set ↥Bs), sX x = x ∨ sX x = x⁻¹ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hsXpat with ⟨hb, hz⟩ | ⟨hb, hz⟩
    · rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl hb
      · exact Or.inr (hz 0)
      · exact Or.inr (hz 1)
      · exact Or.inr (hz 2)
    · rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr hb
      · exact Or.inl (hz 0)
      · exact Or.inl (hz 1)
      · exact Or.inl (hz 2)
  have hsX2' : sX * sX = 1 := mulAut_mul_self_of_sign_on_gens hgen hsXsign
  have hs2 : s * s ∈ K := by
    have h1 : φ (⟨s, hsN⟩ * ⟨s, hsN⟩) = 1 := by
      rw [map_mul, ← hsXeq]
      exact hsX2'
    exact (hφ_one _).mp h1
  have hsK : s ∉ K := by
    intro hsKmem
    have h1 : sX = 1 := by
      rw [hsXeq]
      exact (hφ_one ⟨s, hsN⟩).mpr hsKmem
    rcases hsXpat with ⟨hb, hz⟩ | ⟨hb, hz⟩
    · have h2 := hz 0
      rw [h1, MulAut.one_apply] at h2
      exact hz0ne (eq_one_of_eq_inv_of_pow_three (hpowBs _) h2)
    · rw [h1, MulAut.one_apply] at hb
      exact hbGne (eq_one_of_eq_inv_of_pow_three (hpowBs _) hb)
  have hKnormal : (K.subgroupOf N).Normal := by
    simpa [K, N, Bs] using
      (Subgroup.normal_subgroupOf_centralizer_normalizer (s := (Bs : Set G)))
  have hCnorm : ∀ n ∈ N, ∀ c ∈ K, n * c * n⁻¹ ∈ K := by
    intro n hn c hc
    have hmem : (⟨n, hn⟩ : N) * (⟨c, hBK hc⟩ : N) * (⟨n, hn⟩ : N)⁻¹ ∈ K.subgroupOf N :=
      hKnormal.conj_mem (⟨c, hBK hc⟩ : N) (Subgroup.mem_subgroupOf.mpr hc) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using hmem
  obtain ⟨Y, hKY, hYN, hYnorm, hYoddIndex, hYW⟩ :=
    CFSG.ZStarModular.exists_odd_normal_of_isolated hBK hCnorm hsN hs2 hsK hiso
  have hmemX : ∀ n : N, φ n ∈ X := fun n => by
    change φ n ∈ φ.range
    exact MonoidHom.mem_range.mpr ⟨n, rfl⟩
  let π : N →* ↥X :=
    { toFun := fun n => ⟨φ n, hmemX n⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b) }
  have hπ_apply : ∀ n : N, ((π n : ↥X) : MulAut ↥Bs) = φ n := fun n => rfl
  have hπ_surj : Function.Surjective π := by
    intro x
    dsimp only [X] at x
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp x.2
    exact ⟨n, Subtype.ext hn⟩
  let YN : Subgroup N := Y.subgroupOf N
  have hYNnormal : YN.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYN]
    intro h k hh hk
    exact hYnorm k hk h hh
  let ΦX : Subgroup ↥X := YN.map π
  have hΦXnormal : ΦX.Normal := hYNnormal.map π hπ_surj
  let gY : ↥Y →* MulAut ↥Bs :=
    { toFun := fun y => φ ⟨y, hYN y.2⟩
      map_one' := by
        apply (hφ_one ⟨(1 : ↥Y), hYN (1 : ↥Y).2⟩).mpr
        simp
      map_mul' := by
        intro y z
        change φ ⟨(y : ↥Y) * (z : ↥Y), hYN ((y : ↥Y) * (z : ↥Y)).2⟩ =
          φ ⟨y, hYN y.2⟩ * φ ⟨z, hYN z.2⟩
        rw [← map_mul]
        congr 1 }
  have hΦcard : Nat.card (gY.range) = K.relIndex Y := by
    have hcard : Nat.card (↥Y ⧸ gY.ker) = Nat.card (gY.range) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange gY).toEquiv
    rw [← hcard]
    have hker : gY.ker = K.subgroupOf Y := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change φ ⟨y, hYN y.2⟩ = 1 ↔ (y : G) ∈ K
      exact hφ_one ⟨y, hYN y.2⟩
    rw [hker]
    rfl
  have hΦodd : Odd (Nat.card (gY.range)) := by
    rw [hΦcard]
    exact hYoddIndex
  have hΦXmap : ΦX.map X.subtype = gY.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp only [ΦX] at hy
      obtain ⟨z, hzY, hzy⟩ := Subgroup.mem_map.mp hy
      have hzY' : (z : G) ∈ Y := Subgroup.mem_subgroupOf.mp hzY
      refine ⟨⟨(z : G), hzY'⟩, ?_⟩
      exact congrArg Subtype.val hzy
    · rintro ⟨a, rfl⟩
      refine ⟨π ⟨(a : G), hYN a.2⟩, ?_, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨⟨(a : G), hYN a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hΦXodd : Odd (Nat.card ΦX) := by
    rw [← Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective, hΦXmap]
    exact hΦodd
  have hΦXleO : ΦX ≤ CFSG.oddCore ↥X :=
    le_sSup ⟨hΦXnormal, hΦXodd⟩
  have hZ : (⊤ : Set ↥X) = (CFSG.oddCore ↥X : Set ↥X) *
      (Subgroup.centralizer ({⟨sX, hSmem⟩} : Set ↥X) : Set ↥X) := by
    apply Set.eq_of_subset_of_subset
    · intro x _
      obtain ⟨q, rfl⟩ := hπ_surj x
      obtain ⟨y, hy, w, hwN, hw, hqyw⟩ := hYW (q : G) q.2
      refine Set.mem_mul.mpr ⟨π ⟨y, hYN hy⟩, hΦXleO (Subgroup.mem_map.mpr
        ⟨⟨y, hYN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩), π ⟨w, hwN⟩, ?_, ?_⟩
      · refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
        change φ ⟨w, hwN⟩ * sX = sX * φ ⟨w, hwN⟩
        have h1 : φ ⟨w, hwN⟩ * sX * (φ ⟨w, hwN⟩)⁻¹ * sX⁻¹ = 1 := by
          have h2 := (hφ_one (⟨w, hwN⟩ * ⟨s, hsN⟩ * ⟨w, hwN⟩⁻¹ * ⟨s, hsN⟩⁻¹ : N)).mpr hw
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hsXeq] at h2
          exact h2
        exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
      · rw [← map_mul]
        congr 1
        exact Subtype.ext hqyw.symm
    · intro _ _
      exact Set.mem_univ _
  have memN_of_mono : ∀ g ∈ ({τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ N := by
    intro g hg
    have h := (hMono.mem g hg).1
    rwa [BB_eq_Bt] at h
  have hι₁N : ι₁ ∈ N := memN_of_mono ι₁ (by simp)
  have hσN : σ₁₂ ∈ N := memN_of_mono σ₁₂ (by simp)
  have hγN : γ ∈ N := memN_of_mono γ (by simp)
  let ιX : MulAut ↥Bs := φ ⟨ι₁, hι₁N⟩
  let σX : MulAut ↥Bs := φ ⟨σ₁₂, hσN⟩
  let γX : MulAut ↥Bs := φ ⟨γ, hγN⟩
  have hιXmem : ιX ∈ X := ⟨⟨ι₁, hι₁N⟩, rfl⟩
  have hσXmem : σX ∈ X := ⟨⟨σ₁₂, hσN⟩, rfl⟩
  have hγXmem : γX ∈ X := ⟨⟨γ, hγN⟩, rfl⟩
  have hιXb : ιX bG = bG := by
    apply Subtype.ext
    simpa [ιX, hval_gen ι₁ hι₁N, bG] using (hMono.mem ι₁ (by simp)).2
  have hιXz0 : ιX (zsG 0) = (zsG 0)⁻¹ := by
    apply Subtype.ext
    simpa [ιX, hval_gen ι₁ hι₁N, zsG] using hMono.s₁.1
  have hιXz1 : ιX (zsG 1) = zsG 1 := by
    apply Subtype.ext
    simpa [ιX, hval_gen ι₁ hι₁N, zsG] using hMono.s₁.2.1
  have hιXz2 : ιX (zsG 2) = zsG 2 := by
    apply Subtype.ext
    simpa [ιX, hval_gen ι₁ hι₁N, zsG] using hMono.s₁.2.2
  have hσXb : σX bG = bG := by
    apply Subtype.ext
    simpa [σX, hval_gen σ₁₂ hσN, bG] using (hMono.mem σ₁₂ (by simp)).2
  have hσXz0 : σX (zsG 0) = zsG 1 := by
    apply Subtype.ext
    simpa [σX, hval_gen σ₁₂ hσN, zsG] using hMono.p₁₂.1
  have hσXz1 : σX (zsG 1) = zsG 0 := by
    apply Subtype.ext
    simpa [σX, hval_gen σ₁₂ hσN, zsG] using hMono.p₁₂.2.1
  have hσXz2 : σX (zsG 2) = zsG 2 := by
    apply Subtype.ext
    simpa [σX, hval_gen σ₁₂ hσN, zsG] using hMono.p₁₂.2.2
  have hγXb : γX bG = bG := by
    apply Subtype.ext
    simpa [γX, hval_gen γ hγN, bG] using (hMono.mem γ (by simp)).2
  have hγXz0 : γX (zsG 0) = zsG 1 := by
    apply Subtype.ext
    simpa [γX, hval_gen γ hγN, zsG] using hMono.cyc.1
  have hγXz2 : γX (zsG 2) = zsG 0 := by
    apply Subtype.ext
    simpa [γX, hval_gen γ hγN, zsG] using hMono.cyc.2.2
  have hγXz1 : γX (zsG 1) = zsG 2 := by
    apply Subtype.ext
    simpa [γX, hval_gen γ hγN, zsG] using hMono.cyc.2.1
  have hιXsign : ∀ x ∈ ({bG, zsG 0, zsG 1, zsG 2} : Set ↥Bs), ιX x = x ∨ ιX x = x⁻¹ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl hιXb
    · exact Or.inr hιXz0
    · exact Or.inl hιXz1
    · exact Or.inl hιXz2
  have hιX2 : ιX * ιX = 1 := mulAut_mul_self_of_sign_on_gens hgen hιXsign
  have hst : sX * ιX = ιX * sX := mulAut_comm_of_sign_on_gens hgen hsXsign hιXsign
  obtain ⟨hker_b, hE, hker_E⟩ := eigen_data h hsXpat ⟨hιXb, hιXz0, hιXz1, hιXz2⟩
  have hmap : ∀ σ : MulAut ↥Bs, σ ∈ X → σ * sX = sX * σ →
      Subgroup.map σ (Subgroup.zpowers (bG : ↥Bs)) = Subgroup.zpowers (bG : ↥Bs) := by
    intro σ _ hcomm
    rcases hker_b with hfix | hinv
    · exact map_kernel_inv_mul (u := sX) (y := σ) hcomm hfix
    · exact map_kernel_mul (u := sX) (y := σ) hcomm hinv
  have hline_of_comm : ∀ g : ↥X, (g : MulAut ↥Bs) * sX = sX * (g : MulAut ↥Bs) →
      (g : MulAut ↥Bs) bG = bG ∨ (g : MulAut ↥Bs) bG = bG⁻¹ := by
    intro g hcomm
    have hmem : (g : MulAut ↥Bs) bG ∈ Subgroup.zpowers bG := by
      rw [← hmap g g.2 hcomm]
      exact Subgroup.mem_map_of_mem (g : MulAut ↥Bs).toMonoidHom (Subgroup.mem_zpowers bG)
    have hgne : (g : MulAut ↥Bs) bG ≠ 1 := by
      intro h
      exact hbGne ((g : MulAut ↥Bs).injective (by rw [h, map_one]))
    exact GGFF.eq_or_eq_inv_of_mem_zpowers hord_bG hmem hgne
  have hline_z : ∀ (g : ↥X) (q : N), (g : MulAut ↥Bs) = φ q →
      ((g : MulAut ↥Bs) bG = bG ∨ (g : MulAut ↥Bs) bG = bG⁻¹) →
      ∀ i : Fin 3, ∃ y ∈ ({zsG 0, zsG 1, zsG 2} : Set ↥Bs), ∃ k : ℤ,
        (g : MulAut ↥Bs) (zsG i) = y ^ k := by
    intro g q hgq hline i
    have hqN : (q : G) ∈ N := q.2
    have hqb : q * b * q⁻¹ ∈ Subgroup.zpowers b := by
      have hbval : (((φ q) bG : ↥Bs) : G) = (q : G) * b * (q : G)⁻¹ := by
        simpa [bG] using hval_gen (q : G) q.2 bG
      have hmemφ : (((φ q) bG : ↥Bs) : G) ∈ Subgroup.zpowers b := by
        have hmapzp : (Subgroup.zpowers bG).map Bs.subtype = Subgroup.zpowers b := by
          rw [MonoidHom.map_zpowers]
          rfl
        rw [← hmapzp, ← hgq]
        rcases hline with h | h
        · rw [h]
          exact Subgroup.mem_map_of_mem Bs.subtype (Subgroup.mem_zpowers bG)
        · rw [h]
          exact Subgroup.mem_map_of_mem Bs.subtype
            ((Subgroup.zpowers bG).inv_mem (Subgroup.mem_zpowers bG))
      simpa [hbval] using hmemφ
    obtain ⟨j, e, he, hqj⟩ := h.facts.stab (q : G) hqN hqb i
    refine ⟨zsG j, ?_, (e : ℤ), ?_⟩
    · fin_cases j <;> simp
    · apply Subtype.ext
      have hval : (((φ q) (zsG i) : ↥Bs) : G) =
          (q : G) * ((zsG i : ↥Bs) : G) * (q : G)⁻¹ := by
        simpa using hval_gen (q : G) hqN (zsG i)
      rw [hgq, hval]
      change (q : G) * GGFF.zs z i * (q : G)⁻¹ = GGFF.zs z j ^ (e : ℤ)
      rw [zpow_natCast]
      exact hqj
  have hCY : ∀ g : ↥X, g ∈ CFSG.oddCore ↥X →
      (g : MulAut ↥Bs) * sX = sX * (g : MulAut ↥Bs) → g = 1 := by
    intro g hg hcomm
    have : (CFSG.oddCore ↥X).Normal := CFSG.oddCore_normal ↥X
    have hgb := hline_of_comm g hcomm
    obtain ⟨q, hq_eq⟩ := hπ_surj g
    have hgq' : (g : MulAut ↥Bs) = φ q := by
      rw [← hq_eq]
      exact hπ_apply q
    have hgl : ∀ x ∈ ({zsG 0, zsG 1, zsG 2} : Set ↥Bs), ∃ y ∈ ({zsG 0, zsG 1, zsG 2} : Set ↥Bs),
        ∃ k : ℤ, (g : MulAut ↥Bs) x = y ^ k := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hline_z g q hgq' hgb 0
      · exact hline_z g q hgq' hgb 1
      · exact hline_z g q hgq' hgb 2
    exact CFSG.MulAut.eq_one_of_mem_oddNormal_of_lines_H0 hpowBs hgen
      CFSG.ABGLocalTools.odd_card_oddCore hιXmem hσXmem hγXmem
      ⟨hιXb, hιXz0, hιXz1, hιXz2⟩
      ⟨hσXb, hσXz0, hσXz1, hσXz2⟩
      ⟨hγXb, hγXz0, hγXz1, hγXz2⟩ hg hgb hgl
  have hirr : ∀ U : Subgroup ↥Bs, (∀ σ : MulAut ↥Bs, σ ∈ X → Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ⊤ := x_irreducible h hMono hirrMono hB1not
  have hYne : CFSG.oddCore ↥X ≠ ⊥ := by
    obtain ⟨σ, hσX, hσmove⟩ := exists_move h
    exact CFSG.RankThree.PartTwo.Sec21.FF81.FF81Hyp.oddCore_ne_bot_of_move hSmem hZ
      (GGFF.SettingCore.b_mem_Bt b z) ⟨σ, hσX, hσmove⟩ hmap
  have hYab : ∀ a b : ↥X, a ∈ CFSG.oddCore ↥X → b ∈ CFSG.oddCore ↥X → a * b = b * a :=
    CFSG.RankThree.PartTwo.Sec21.FF81.FF81Hyp.oddCore_commute_of_CYtau hSmem hsX2'
      (fun g hg hcomm => congrArg Subtype.val (hCY g hg hcomm))
  have hB3 : IsPGroup 3 ↥Bs := IsElementaryAbelian.isPGroup 3 ↥Bs
  have hBnt : Nontrivial ↥Bs := ⟨bG, 1, hbGne⟩
  have h3 : ¬ 3 ∣ Nat.card ↥(CFSG.oddCore ↥X) :=
    CFSG.RankThree.PartTwo.Sec21.FF81.FF81Hyp.not_three_dvd_oddCore hB3 hBnt hirr hYab
  let Yb : Subgroup (MulAut ↥Bs) := (CFSG.oddCore ↥X).map X.subtype
  have hYX : Yb ≤ X := Subgroup.map_subtype_le (CFSG.oddCore ↥X)
  have hYbnorm : ∀ σ : MulAut ↥Bs, σ ∈ X → ∀ y : MulAut ↥Bs, y ∈ Yb → σ * y * σ⁻¹ ∈ Yb := by
    intro σ hσ y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩ * g * ⟨σ, hσ⟩⁻¹,
      (CFSG.oddCore_normal ↥X).conj_mem g hg ⟨σ, hσ⟩, rfl⟩
  have hYne' : Yb ≠ ⊥ := by
    intro hbot
    apply hYne
    have h' : (CFSG.oddCore ↥X).map X.subtype = (⊥ : Subgroup ↥X).map X.subtype := by
      show Yb = (⊥ : Subgroup ↥X).map X.subtype
      rw [hbot, Subgroup.map_bot]
    exact Subgroup.map_injective X.subtype_injective h'
  have hCBY := CFSG.RankThree.PartTwo.Sec21.FF81.FF81Hyp.cen_eq_bot_of_irreducible hYX hYbnorm
    hYne' hirr
  have hcardYb : Nat.card Yb = Nat.card ↥(CFSG.oddCore ↥X) := by
    show Nat.card ((CFSG.oddCore ↥X).map X.subtype) = Nat.card ↥(CFSG.oddCore ↥X)
    rw [Subgroup.card_map_of_injective X.subtype_injective]
  have hYb_odd : Odd (Nat.card Yb) := by
    rw [hcardYb]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  have hYb3 : ¬ 3 ∣ Nat.card Yb := by
    rw [hcardYb]
    exact h3
  have hYb_ab : ∀ a ∈ Yb, ∀ c ∈ Yb, a * c = c * a := by
    intro a ha c hc
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hc
    exact congrArg Subtype.val (hYab g g' hg hg')
  have hYb_free : ∀ y ∈ Yb, y * sX = sX * y → y = 1 := by
    intro y hy hcomm
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg Subtype.val (hCY g hg hcomm)
  have hdec := oddAbelian_decomp (Y := Yb) (sX := sX) (tX := ιX) hYb_odd hYb_ab
    (fun y hy => hYbnorm sX hSmem y hy) (fun y hy => hYbnorm ιX hιXmem y hy)
    hsX2' hιX2 hst hYb_free
  have hfix := y_fixes_z0 h (Y := Yb) (sX := sX) (tX := ιX) hYb_odd hYb3
    ⟨hιXb, hιXz0, hιXz1, hιXz2⟩ hE hker_E hdec
  exact hz0ne (hCBY (zsG 0) hfix)

end B1Normal

theorem b1_normal {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∀ m ∈ nB b z, ∀ y ∈ bOne z, m * y * m⁻¹ ∈ bOne z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ, -, hMono, hirr⟩ := exists_mono_irreducible h
  have hBO : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BO (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) = bOne z := (GGFF.SettingCore.tor_eq_closure z).symm
  rw [hBO] at hirr
  by_cases hinv : ∃ g ∈ nB b z, g * b * g⁻¹ = b⁻¹
  · obtain ⟨t, htN, htb, htz⟩ := exists_t_of_inverts h hinv
    exact B1Normal.bulk h htN (isolated_t h htN htb htz) (Or.inr ⟨htb, htz⟩) hMono hirr hcon
  · push Not at hinv
    obtain ⟨τ₀, c, hτc⟩ := exists_tauC h
    have hτb : τ₀ * b * τ₀⁻¹ = b := by
      rw [h.settingCore.comm_of_mem hτc.tau_mem]
      group
    have hτN : τ₀ ∈ nB b z :=
      GGFF.SettingCore.mem_nor_Bt (by rw [hτb]; exact GGFF.SettingCore.b_mem_Bt b z)
        (fun i => by
          rw [hτc.inv i]
          exact (GGFF.Bt b z).inv_mem (GGFF.SettingCore.zs_mem_Bt b z i))
    exact B1Normal.bulk h hτN (isolated_tau h hτc.tau_mem hτc.tau_sq hτc.inv hinv)
      (Or.inl ⟨hτb, hτc.inv⟩) hMono hirr hcon

end CFSG.StandardType.FF81.PropOne

end
