module

public import CFSG.OddTranspositions.SevenThreeTransitive
public import CFSG.OddTranspositions.SevenThreeQuotient
public import CFSG.OddTranspositions.O4Minus5Pair
public import CFSG.OddTranspositions.A3Bound
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartOne.CTP.StrongPSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OutRows
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import Mathlib.Data.ZMod.QuotientGroup
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.Data.Fintype.Perm
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1Bridge
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Co3
public import CFSG.Sporadic.Presentation.HeExact
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.ONan
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.Sporadic.Th
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Exceptional.Residual
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate10019
public import Certificates.Certificate10019Base
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2153
public import Certificates.Certificate2154
public import Certificates.Certificate2156
public import Certificates.Certificate2157
public import Certificates.Certificate2160
public import Certificates.Certificate2166
public import Certificates.Certificate2173
public import Certificates.Certificate2178
public import Certificates.Certificate2179
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate2195
public import Certificates.Certificate2198
public import Certificates.Certificate2201
public import Certificates.Certificate2207
public import Certificates.Certificate2211
public import Certificates.Certificate2213
public import Certificates.Certificate2215
public import Certificates.Certificate2216
public import Certificates.Certificate2216Base
public import Certificates.Certificate2217
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2225Base
public import Certificates.Certificate2251
public import Certificates.Certificate2254
public import Certificates.Certificate2254Base
public import Certificates.Certificate2255
public import Certificates.Certificate2274
public import Certificates.Certificate2283
public import Certificates.Certificate2288
public import Certificates.Certificate2293
public import Certificates.Certificate2294
public import Certificates.Certificate2304
public import Certificates.Certificate2305
public import Certificates.Certificate2308
public import Certificates.Certificate3046
public import Certificates.Certificate3085Base
public import Certificates.Certificate3157
public import Certificates.Certificate8153
public import Certificates.Certificate8156
public import Certificates.Certificate8157
public import Certificates.Certificate8160
public import Certificates.Certificate9131
public import Certificates.Certificate9131Base
public import Certificates.Certificate9203
public import Certificates.Certificate9204
public import Certificates.Certificate9208
public import Certificates.Certificate9209
public import Certificates.Certificate9210
public import Certificates.Certificate9211
public import Certificates.Certificate9212
public import Certificates.Certificate9214
public import Certificates.Certificate9215
public import Certificates.Certificate9216
public import Certificates.Certificate9217
public import Certificates.Certificate9217Base
public import Certificates.Certificate9218
public import Certificates.Certificate9219
public import Certificates.Certificate9220


public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.EvenSporadicStandard.HSStd.InvCent.Harada commutatorElement Equiv

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_mem_comm_mem {P B Z : Subgroup G} (hP : IsPGroup 2 P)
    (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hZn : (Z.subgroupOf P).Normal)
    (hZB : Z < B) :
    ∃ e ∈ B, e ∉ Z ∧ ∀ x ∈ P, x * e * x⁻¹ * e⁻¹ ∈ Z := by
  classical
  set Z' := Z.subgroupOf P
  set H : Subgroup (P ⧸ Z') := (B.subgroupOf P).map (QuotientGroup.mk' Z')
  have hHn : H.Normal := hBn.map _ (QuotientGroup.mk'_surjective Z')
  obtain ⟨b, hbB, hbZ⟩ := SetLike.exists_of_lt hZB
  have hH : H ≠ ⊥ := by
    intro h
    have : QuotientGroup.mk' Z' ⟨b, hBP hbB⟩ ∈ H := ⟨⟨b, hBP hbB⟩, hbB, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hbZ this
  haveI : Group.IsNilpotent (P ⧸ Z') := (hP.to_quotient Z').isNilpotent
  obtain ⟨q, ⟨hqH, hqc⟩, hq1⟩ := ((H ⊓ Subgroup.center _).bot_or_exists_ne_one).resolve_left
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  obtain ⟨b', hb'B, rfl⟩ := hqH
  refine ⟨b', hb'B, fun h => hq1 ?_, fun x hx => ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact h
  · have hc := Subgroup.mem_center_iff.mp hqc (QuotientGroup.mk' Z' ⟨x, hx⟩)
    have : (⟨x, hx⟩ * b' * (⟨x, hx⟩ : P)⁻¹ * b'⁻¹ : P) ∈ Z' := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      simp only [QuotientGroup.mk'_apply] at hc
      rw [hc]; group
    simpa [Z', Subgroup.mem_subgroupOf] using this

theorem eq_one_or_eq_of_mem_zpowers {z c : G} (hz : z * z = 1) (hc : c ∈ Subgroup.zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [zpow_eq_zpow_emod' k (n := 2) (by rw [pow_two]; exact hz)]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem conj_mem_thirdK_of_commute {D : Set G} (hN : IsNormalSet D) {z s k : G}
    (hs : Commute s z) (hk : k ∈ thirdK D z) : s * k * s⁻¹ ∈ thirdK D z := by
  have hle : thirdK D z ≤ (thirdK D z).comap (MulAut.conj s).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [mem_Delta_iff] at hx
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, SetLike.mem_coe]
    refine Subgroup.subset_closure (mem_Delta_iff.mpr ⟨hN s x hx.1, ?_⟩)
    have h : Commute (s * x * s⁻¹) (s * z * s⁻¹) := hx.2.conj s
    rwa [show s * z * s⁻¹ = z by rw [hs.eq]; group] at h
  simpa [MulAut.conj_apply] using hle hk

theorem normal_centralizer_thirdK {D : Set G} (hN : IsNormalSet D) {S' : Subgroup G} {z : G}
    (hzc : ∀ s ∈ S', Commute s z) :
    ((S' ⊓ Subgroup.centralizer (thirdK D z : Set G)).subgroupOf S').Normal := by
  refine ⟨fun n hn s => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnS, hnC⟩ := Subgroup.mem_inf.mp hn
  refine Subgroup.mem_inf.mpr ⟨by simpa using S'.mul_mem (S'.mul_mem s.2 hnS) (S'.inv_mem s.2), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hnC ⊢
  intro k hk
  have hk' : (s : G)⁻¹ * k * s ∈ thirdK D z := by
    simpa using conj_mem_thirdK_of_commute hN (hzc _ (S'.inv_mem s.2)) hk
  have h := hnC _ hk'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc k * (s * n * (s : G)⁻¹) = s * ((s : G)⁻¹ * k * s * n) * (s : G)⁻¹ := by group
    _ = s * (n * ((s : G)⁻¹ * k * s)) * (s : G)⁻¹ := by rw [h]
    _ = s * n * (s : G)⁻¹ * k := by group

theorem inf_eq_bot_of_mulEquiv_A5 {H O : Subgroup G} (e : H ≃* alternatingGroup (Fin 5))
    (hOn : ∀ h ∈ H, ∀ o ∈ O, h * o * h⁻¹ ∈ O) (hOs : Group.IsSolvable O) : H ⊓ O = ⊥ := by
  classical
  have hn : (O.subgroupOf H).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hOn g g.2 n hn⟩
  set N : Subgroup (alternatingGroup (Fin 5)) := (O.subgroupOf H).map e.toMonoidHom
  haveI hN : N.Normal := hn.map _ e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hmem : e ⟨x, hx.1⟩ ∈ N := ⟨⟨x, hx.1⟩, by simpa [Subgroup.mem_subgroupOf] using hx.2, rfl⟩
    rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
    simpa using congrArg Subtype.val hmem
  · exfalso
    have hmem : ∀ a, ((e.symm a : H) : G) ∈ O := by
      intro a
      obtain ⟨h', hh', hh'e⟩ := (h ▸ Subgroup.mem_top a : a ∈ N)
      have : e.symm a = h' := by rw [← hh'e]; simp
      rw [this]; exact hh'
    let f : alternatingGroup (Fin 5) →* O :=
      { toFun := fun a => ⟨e.symm a, hmem a⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hf : Function.Injective f := fun a b hab => by
      have := congrArg (fun t : O => (t : G)) hab
      exact e.symm.injective (Subtype.ext this)
    haveI := solvable_of_solvable_injective hf
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5))).mpr this
    have hc : Subgroup.center (alternatingGroup (Fin 5)) = ⊤ :=
      Subgroup.eq_top_iff' _ |>.mpr fun g => Subgroup.mem_center_iff.mpr fun h => hcomm h g
    rw [alternatingGroup.center_eq_bot (by simp)] at hc
    exact bot_ne_top hc

theorem sup_zpowers_inf_eq_bot {Y K₁ X₁ O : Subgroup G} {z : G}
    (hOn : ∀ y ∈ Y, ∀ o ∈ O, y * o * y⁻¹ ∈ O) (hOs : Group.IsSolvable O)
    (eK : K₁ ≃* alternatingGroup (Fin 5)) (eX : X₁ ≃* alternatingGroup (Fin 5))
    (hK₁Y : K₁ ≤ Y) (hX₁Y : X₁ ≤ Y) (hz2 : z * z = 1)
    (hK₁z : ∀ k ∈ K₁, Commute k z) (hzX : ∀ k ∈ X₁, z * k * z⁻¹ ∈ X₁)
    (hzX' : z ∉ Subgroup.centralizer (X₁ : Set G)) :
    (K₁ ⊔ Subgroup.zpowers z) ⊓ O = ⊥ := by
  have hK₁O := inf_eq_bot_of_mulEquiv_A5 eK (fun h hh => hOn h (hK₁Y hh)) hOs
  have hX₁O := inf_eq_bot_of_mulEquiv_A5 eX (fun h hh => hOn h (hX₁Y hh)) hOs
  have hzO : z ∉ O := by
    intro hzO
    apply hzX'
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hc : z * k * z⁻¹ * k⁻¹ ∈ X₁ ⊓ O := by
      refine ⟨X₁.mul_mem (hzX k hk) (X₁.inv_mem hk), ?_⟩
      have : k * z⁻¹ * k⁻¹ ∈ O := hOn k (hX₁Y hk) _ (O.inv_mem hzO)
      simpa [mul_assoc] using O.mul_mem hzO this
    rw [hX₁O, Subgroup.mem_bot] at hc
    have : z * k * z⁻¹ = k := by
      calc z * k * z⁻¹ = z * k * z⁻¹ * k⁻¹ * k := by group
        _ = k := by rw [hc, one_mul]
    calc k * z = z * k * z⁻¹ * z := by rw [this]
      _ = z * k := by group
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    have hk : ∀ k, k ∈ K₁ → z * k * z⁻¹ = k := fun k hk => by rw [← (hK₁z k hk).eq]; group
    constructor
    · intro h; rw [hk k h]; exact h
    · intro h
      have h1 := hk _ h
      have h2 : z * k * z⁻¹ = k := by
        calc z * k * z⁻¹ = z⁻¹ * (z * (z * k * z⁻¹) * z⁻¹) * z := by group
          _ = z⁻¹ * (z * k * z⁻¹) * z := by rw [h1]
          _ = k := by group
      exact h2 ▸ h
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxO⟩ := Subgroup.mem_inf.mp hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers z) K₁ hzN
  have hx' : x ∈ ((Subgroup.zpowers z ⊔ K₁ : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hxK
  rw [hset] at hx'
  obtain ⟨c, hc, k, hk, rfl⟩ := hx'
  have hcK : ∀ k₁ ∈ K₁, Commute c k₁ := by
    intro k₁ hk₁
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (hK₁z k₁ hk₁).symm.zpow_left i
  have hxc : ∀ k₁ ∈ K₁, (c * k) * k₁ = k₁ * (c * k) := by
    intro k₁ hk₁
    have hmem : (c * k) * k₁ * (c * k)⁻¹ * k₁⁻¹ ∈ K₁ ⊓ O := by
      refine ⟨?_, ?_⟩
      · have : (c * k) * k₁ * (c * k)⁻¹ = k * k₁ * k⁻¹ := by
          have h1 : c * (k * k₁ * k⁻¹) = (k * k₁ * k⁻¹) * c :=
            hcK _ (K₁.mul_mem (K₁.mul_mem hk hk₁) (K₁.inv_mem hk))
          calc (c * k) * k₁ * (c * k)⁻¹ = c * (k * k₁ * k⁻¹) * c⁻¹ := by group
            _ = k * k₁ * k⁻¹ := by rw [h1]; group
        rw [this]
        exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hk hk₁) (K₁.inv_mem hk)) (K₁.inv_mem hk₁)
      · have : k₁ * (c * k)⁻¹ * k₁⁻¹ ∈ O := hOn k₁ (hK₁Y hk₁) _ (O.inv_mem hxO)
        simpa [mul_assoc] using O.mul_mem hxO this
    rw [hK₁O, Subgroup.mem_bot] at hmem
    calc (c * k) * k₁ = (c * k) * k₁ * (c * k)⁻¹ * k₁⁻¹ * (k₁ * (c * k)) := by group
      _ = k₁ * (c * k) := by rw [hmem, one_mul]
  have hkk : ∀ k₁ ∈ K₁, k₁ * k = k * k₁ := by
    intro k₁ hk₁
    have h1 := hxc k₁ hk₁
    have h2 := (hcK k₁ hk₁).eq
    have : c * (k * k₁) = c * (k₁ * k) := by
      calc c * (k * k₁) = (c * k) * k₁ := by group
        _ = k₁ * (c * k) := h1
        _ = (k₁ * c) * k := by group
        _ = (c * k₁) * k := by rw [h2]
        _ = c * (k₁ * k) := by group
    exact (mul_left_cancel this).symm
  have hkc : eK ⟨k, hk⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := eK.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hkk m m.2)
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
    MulEquiv.map_eq_one_iff] at hkc
  have hk1 : k = 1 := congrArg Subtype.val hkc
  subst hk1
  simp only [mul_one] at hxO ⊢
  rcases eq_one_or_eq_of_mem_zpowers hz2 hc with h | h
  · exact h
  · exact absurd (h ▸ hxO) hzO

def orb (D : Set G) (e y : G) : Set G := {t | ∃ k ∈ thirdK D e, k * y * k⁻¹ = t}

theorem mem_orb_self {D : Set G} {e y : G} : y ∈ orb D e y := ⟨1, one_mem _, by simp⟩

theorem orb_subset_Delta {D : Set G} (hN : IsNormalSet D) {e y : G} (hy : y ∈ Delta D e) :
    orb D e y ⊆ Delta D e := by
  rintro x ⟨k, hk, rfl⟩
  have hke : Commute k e :=
    (Subgroup.mem_centralizer_iff.mp (thirdK_le_centralizer hk) e (by simp)).symm
  have hye : Commute y e := (mem_Delta_iff.mp hy).2
  refine mem_Delta_iff.mpr ⟨hN k y (mem_Delta_iff.mp hy).1, ?_⟩
  exact ((hke.symm.mul_right hye.symm).mul_right hke.symm.inv_right).symm

theorem orb_invariant {D : Set G} {e y : G} :
    ∀ k' ∈ thirdK D e, ∀ x ∈ orb D e y, k' * x * k'⁻¹ ∈ orb D e y := by
  rintro k' hk' x ⟨k, hk, rfl⟩
  exact ⟨k' * k, Subgroup.mul_mem _ hk' hk, by group⟩

theorem disjoint_orb_of_not_mem {D : Set G} {e y x : G} (hx : x ∉ orb D e y) :
    Disjoint (orb D e y) (orb D e x) := by
  rw [Set.disjoint_left]
  rintro t ⟨k, hk, hkt⟩ ⟨k', hk', hkt'⟩
  apply hx
  refine ⟨k'⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hk') hk, ?_⟩
  calc (k'⁻¹ * k) * y * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * y * k⁻¹) * k' := by group
    _ = k'⁻¹ * t * k' := by rw [hkt]
    _ = x := by rw [← hkt']; group

theorem thirdK_transitive_of_commute {D : Set G} (hS : Setup G D) (hL : LocalSecond D)
    {u w v e : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) (hue : Commute u e) (hve : Commute v e)
    (hwe : Commute w e) :
    ∀ x ∈ Delta D e, ∃ k ∈ thirdK D e, k * u * k⁻¹ = x := by
  classical
  have huΔ : u ∈ Delta D e := mem_Delta_iff.mpr ⟨htri.1, hue⟩
  have hvΔ : v ∈ Delta D e := mem_Delta_iff.mpr ⟨htri.2.1, hve⟩
  have hwΔ : w ∈ Delta D e := mem_Delta_iff.mpr ⟨htri.2.2.1, hwe⟩
  have huw : ¬ Commute u w := htri.2.2.2.2.2.1
  have hvw : ¬ Commute v w := htri.2.2.2.2.2.2
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one htri.1
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one htri.2.1
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one htri.2.2.1
  have hodduw : Odd (orderOf (u * w)) := hS.oddT.odd_of_not_commute htri.1 htri.2.2.1 huw
  have hoddvw : Odd (orderOf (v * w)) := hS.oddT.odd_of_not_commute htri.2.1 htri.2.2.1 hvw
  obtain ⟨gu, hgu, hguw⟩ := exists_conj_of_odd_orderOf_mul hu2 hw2 hodduw
  have huwK : Subgroup.closure ({u, w} : Set G) ≤ thirdK D e := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Delta_subset_thirdK huΔ
    · exact Delta_subset_thirdK hwΔ
  have hwO : w ∈ orb D e u := ⟨gu, huwK hgu, hguw⟩
  obtain ⟨gv, hgv, hgvw⟩ := exists_conj_of_odd_orderOf_mul hv2 hw2 hoddvw
  have hvwK : Subgroup.closure ({v, w} : Set G) ≤ thirdK D e := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Delta_subset_thirdK hvΔ
    · exact Delta_subset_thirdK hwΔ
  have hvO : v ∈ orb D e u := by
    refine ⟨gv⁻¹ * gu, Subgroup.mul_mem _ (Subgroup.inv_mem _ (hvwK hgv)) (huwK hgu), ?_⟩
    calc (gv⁻¹ * gu) * u * (gv⁻¹ * gu)⁻¹ = gv⁻¹ * (gu * u * gu⁻¹) * gv := by group
      _ = gv⁻¹ * w * gv := by rw [hguw]
      _ = v := by rw [← hgvw]; group
  intro x hx
  by_cases hxO : x ∈ orb D e u
  · exact hxO
  · exfalso
    have hcomm := thirdK_orbits_commute hS (orb_subset_Delta hS.normal huΔ)
      (orb_subset_Delta hS.normal hx) (orb_invariant (e := e) (y := u))
      (orb_invariant (e := e) (y := x)) (disjoint_orb_of_not_mem hxO)
    have hxu := hcomm u (mem_orb_self) x (mem_orb_self)
    have hxv := hcomm v hvO x (mem_orb_self)
    have hxw := hcomm w hwO x (mem_orb_self)
    have hsec := hL x (mem_Delta_iff.mp hx).1 u w v hxu hxw hxv htri
    rw [hord] at hsec
    obtain ⟨k, hk⟩ := hn
    rw [hk] at hsec
    omega

theorem thirdK_conj {D : Set G} (hN : IsNormalSet D) (g z : G) :
    thirdK D (g * z * g⁻¹) = (thirdK D z).map (MulAut.conj g).toMonoidHom := by
  have hΔ : Delta D (g * z * g⁻¹) = (MulAut.conj g).toMonoidHom '' Delta D z := by
    ext x
    simp only [Set.mem_image, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_Delta_iff]
    constructor
    · rintro ⟨hxD, hxz⟩
      refine ⟨g⁻¹ * x * g, ⟨by simpa using hN g⁻¹ x hxD, ?_⟩, by group⟩
      have := hxz.conj g⁻¹
      simpa [mul_assoc] using this
    · rintro ⟨y, ⟨hyD, hyz⟩, rfl⟩
      exact ⟨hN g y hyD, hyz.conj g⟩
  rw [thirdK, thirdK, hΔ, MonoidHom.map_closure]

theorem commutatorElement_mul_left_of_commute {p a b : G} (ha : Commute p a) (hb : Commute p b) :
    ⁅p * a, b⁆ = ⁅a, b⁆ := by
  have hc : Commute p ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  calc ⁅p * a, b⁆ = p * a * b * a⁻¹ * (p⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    _ = p * a * b * a⁻¹ * (b⁻¹ * p⁻¹) := by rw [(hb.inv_inv).eq]
    _ = p * ⁅a, b⁆ * p⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [hc.eq, mul_inv_cancel_right]

theorem commutator_sup_zpowers_eq {X : Subgroup G} (e : X ≃* alternatingGroup (Fin 5)) {c : G}
    (hc : ∀ x ∈ X, Commute x c) :
    ⁅X ⊔ Subgroup.zpowers c, X ⊔ Subgroup.zpowers c⁆ = X := by
  have hperf := CFSG.GH74.Generic.S45.a5_perfect e
  refine le_antisymm ?_ (hperf.symm.le.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
  have hzN : Subgroup.zpowers c ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    have hk : ∀ k, k ∈ X → c * k * c⁻¹ = k := fun k hk => by rw [← (hc k hk).eq]; group
    constructor
    · intro h; rw [hk k h]; exact h
    · intro h
      have h1 := hk _ h
      have h2 : c * k * c⁻¹ = k := by
        calc c * k * c⁻¹ = c⁻¹ * (c * (c * k * c⁻¹) * c⁻¹) * c := by group
          _ = c⁻¹ * (c * k * c⁻¹) * c := by rw [h1]
          _ = k := by group
      exact h2 ▸ h
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) X hzN
  have hdec : ∀ t ∈ X ⊔ Subgroup.zpowers c, ∃ p ∈ Subgroup.zpowers c, ∃ x ∈ X, p * x = t := by
    intro t ht
    have ht' : t ∈ ((Subgroup.zpowers c ⊔ X : Subgroup G) : Set G) := by
      rw [sup_comm]; exact ht
    rw [hset] at ht'
    obtain ⟨p, hp, x, hx, rfl⟩ := ht'
    exact ⟨p, hp, x, hx, rfl⟩
  have hpc : ∀ p ∈ Subgroup.zpowers c, ∀ x ∈ X, Commute p x := by
    intro p hp x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (hc x hx).symm.zpow_left i
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨p, hp, x, hx, rfl⟩ := hdec g₁ hg₁
  obtain ⟨q, hq, y, hy, rfl⟩ := hdec g₂ hg₂
  have hpq : Commute p q := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    exact Commute.zpow_zpow_self c i j
  rw [commutatorElement_mul_left_of_commute (hpc p hp x hx) (hpq.mul_right (hpc p hp y hy)),
    ← commutatorElement_inv, commutatorElement_mul_left_of_commute (hpc q hq y hy)
      (hpc q hq x hx), commutatorElement_inv]
  rw [← hperf]
  exact Subgroup.commutator_mem_commutator hx hy

theorem conj_mem_of_conj_mem_sup {X : Subgroup G} (e : X ≃* alternatingGroup (Fin 5)) {c s : G}
    (hc : ∀ x ∈ X, Commute x c)
    (hs : ∀ t ∈ X ⊔ Subgroup.zpowers c, s * t * s⁻¹ ∈ X ⊔ Subgroup.zpowers c) :
    ∀ x ∈ X, s * x * s⁻¹ ∈ X := by
  intro x hx
  have hT := commutator_sup_zpowers_eq e hc
  set T := X ⊔ Subgroup.zpowers c
  have hle : T.map (MulAut.conj s).toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩; simpa using hs t ht
  have : (MulAut.conj s).toMonoidHom x ∈ (⁅T, T⁆).map (MulAut.conj s).toMonoidHom :=
    ⟨x, hT.symm ▸ hx, rfl⟩
  rw [Subgroup.map_commutator] at this
  have := Subgroup.commutator_mono hle hle this
  rw [hT] at this
  simpa using this

theorem mem_zpowers_of_commute_A5 {K₁ : Subgroup G} (eK : K₁ ≃* alternatingGroup (Fin 5)) {z x : G}
    (hK₁z : ∀ k ∈ K₁, Commute k z) (hx : x ∈ K₁ ⊔ Subgroup.zpowers z)
    (hxc : ∀ k ∈ K₁, Commute x k) : x ∈ Subgroup.zpowers z := by
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    have hk : ∀ k, k ∈ K₁ → z * k * z⁻¹ = k := fun k hk => by rw [← (hK₁z k hk).eq]; group
    constructor
    · intro h; rw [hk k h]; exact h
    · intro h
      have h1 := hk _ h
      have h2 : z * k * z⁻¹ = k := by
        calc z * k * z⁻¹ = z⁻¹ * (z * (z * k * z⁻¹) * z⁻¹) * z := by group
          _ = z⁻¹ * (z * k * z⁻¹) * z := by rw [h1]
          _ = k := by group
      exact h2 ▸ h
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers z) K₁ hzN
  have hx' : x ∈ ((Subgroup.zpowers z ⊔ K₁ : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hx
  rw [hset] at hx'
  obtain ⟨c, hc, k, hk, rfl⟩ := hx'
  have hcK : ∀ k₁ ∈ K₁, Commute c k₁ := by
    intro k₁ hk₁
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (hK₁z k₁ hk₁).symm.zpow_left i
  have hkk : ∀ k₁ ∈ K₁, k₁ * k = k * k₁ := by
    intro k₁ hk₁
    have h1 := (hxc k₁ hk₁).eq
    have h2 := (hcK k₁ hk₁).eq
    have : c * (k * k₁) = c * (k₁ * k) := by
      calc c * (k * k₁) = (c * k) * k₁ := by group
        _ = k₁ * (c * k) := h1
        _ = (k₁ * c) * k := by group
        _ = (c * k₁) * k := by rw [h2]
        _ = c * (k₁ * k) := by group
    exact (mul_left_cancel this).symm
  have hkc : eK ⟨k, hk⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := eK.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hkk m m.2)
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
    MulEquiv.map_eq_one_iff] at hkc
  have hk1 : k = 1 := congrArg Subtype.val hkc
  subst hk1
  simpa using hc

theorem mem_normalizer_of_conj {X : Subgroup G} {s : G} (h : ∀ x ∈ X, s * x * s⁻¹ ∈ X)
    (h' : ∀ x ∈ X, s⁻¹ * x * s⁻¹⁻¹ ∈ X) : s ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  simpa [mul_assoc] using h' _ hx

structure Config (D : Set G) (u w v z a : G) (K₁ S' : Subgroup G) : Prop where
  setup : Setup G D
  rad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  local2 : LocalSecond D
  center : Subgroup.center G = ⊥
  tri : IsTriangle D u w v
  third : ∃ n : ℕ, Odd n ∧ 1 < n ∧ orderOf (u * v * w) = 2 * n ∧ z = (u * v * w) ^ n
  K_eq : thirdK D z = K₁ ⊔ Subgroup.zpowers z
  K₁_A5 : Nonempty (K₁ ≃* alternatingGroup (Fin 5))
  K₁_comm : K₁ ≤ Subgroup.centralizer ({z} : Set G)
  sylow : IsPGroup 2 S' ∧ ∀ P : Subgroup G, IsPGroup 2 P → S' ≤ P → P = S'
  z_central : z ∈ S' ∧ S' ≤ Subgroup.centralizer ({z} : Set G)
  a_conj : IsConj z a
  a_mem : a ∈ S'
  a_norm : a ∈ Subgroup.normalizer (K₁ : Set G)
  a_outer : ¬ ∃ k ∈ K₁, ∀ x ∈ K₁, a * x * a⁻¹ = k * x * k⁻¹
  a_comm_u : Commute a u
  az_not_conj : ¬ IsConj a (a * z)
  delta_sub : ∀ d ∈ Delta D z, z * d ∈ K₁
  u_pair : ∃ u' ∈ Delta D z, Commute u' a ∧ orderOf (u * u') = 3

namespace Config

variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem z_facts (hQ : Config D u w v z a K₁ S') :
    z * z = 1 ∧ z ≠ 1 ∧ u ∈ Delta D z ∧ v ∈ Delta D z ∧ w ∈ Delta D z ∧ z ∉ D := by
  obtain ⟨n, hn, -, hord, rfl⟩ := hQ.third
  obtain ⟨hz2, hz1, hzu, hzv, hzw, -⟩ :=
    IsTriangle.third_kind hQ.setup.oddT hQ.setup.normal hQ.tri hn hord
  obtain ⟨h1, h2, h3⟩ := vertices_mem_Delta hQ.tri hzu hzv hzw
  exact ⟨hz2, hz1, h1, h2, h3, thirdInv_not_mem hQ.setup hQ.local2 hQ.tri hn hord⟩

theorem conj_data (hQ : Config D u w v z a K₁ S') :
    ∃ X₁ : Subgroup G, Nonempty (X₁ ≃* alternatingGroup (Fin 5)) ∧
      thirdK D a = X₁ ⊔ Subgroup.zpowers a ∧ (∀ x ∈ X₁, Commute x a) ∧
      (∀ d ∈ Delta D a, a * d ∈ X₁) ∧ Nat.card (thirdK D a) = Nat.card (thirdK D z) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hQ.a_conj
  set φ := (MulAut.conj g).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj g).injective
  obtain ⟨eK⟩ := hQ.K₁_A5
  refine ⟨K₁.map φ, ⟨(K₁.equivMapOfInjective φ hφ).symm.trans eK⟩, ?_, ?_, ?_, ?_⟩
  · rw [← hg, thirdK_conj hQ.setup.normal, hQ.K_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
    simp [φ, MulAut.conj_apply]
  · rintro _ ⟨k, hk, rfl⟩
    rw [← hg]
    simpa [φ, MulAut.conj_apply] using
      (show Commute k z from Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hk)).conj g
  · intro d hd
    rw [mem_Delta_iff] at hd
    have hd' : g⁻¹ * d * g ∈ Delta D z := by
      rw [mem_Delta_iff]
      refine ⟨by simpa using hQ.setup.normal g⁻¹ d hd.1, ?_⟩
      have := hd.2.conj g⁻¹
      rw [← hg] at this
      simpa [mul_assoc] using this
    refine ⟨z * (g⁻¹ * d * g), hQ.delta_sub _ hd', ?_⟩
    simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hg]
    group
  · rw [← hg, thirdK_conj hQ.setup.normal]
    exact Subgroup.card_map_of_injective hφ

theorem z_not_mem_centralizer (hQ : Config D u w v z a K₁ S') {X₁ : Subgroup G}
    (hX : thirdK D a = X₁ ⊔ Subgroup.zpowers a)
    (hcard : Nat.card (thirdK D a) = Nat.card (thirdK D z)) :
    z ∉ Subgroup.centralizer (X₁ : Set G) := by
  intro hz
  obtain ⟨eK⟩ := hQ.K₁_A5
  have haz : Commute a z := Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hQ.a_mem)
  have hT : thirdK D a ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hX]
    refine sup_le (fun x hx => ?_) ((Subgroup.zpowers_le).mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr haz.eq))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz x hx
  have hle : thirdK D a ≤ thirdK D z := Subgroup.closure_mono fun d hd => by
    rw [mem_Delta_iff] at hd ⊢
    exact ⟨hd.1, Subgroup.mem_centralizer_singleton_iff.mp
      (hT (Delta_subset_thirdK (mem_Delta_iff.mpr hd)))⟩
  have heq : thirdK D a = thirdK D z := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have ha : a ∈ K₁ ⊔ Subgroup.zpowers z := by
    rw [← hQ.K_eq, ← heq, hX]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hac : ∀ k ∈ K₁, Commute a k := fun k hk => by
    have hkT : k ∈ thirdK D a := by rw [heq, hQ.K_eq]; exact Subgroup.mem_sup_left hk
    exact (show Commute k a from
      Subgroup.mem_centralizer_singleton_iff.mp (thirdK_le_centralizer hkT)).symm
  have hza := mem_zpowers_of_commute_A5 eK
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hk)) ha hac
  apply hQ.a_outer
  refine ⟨1, one_mem _, fun x hx => ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hza
  have : Commute (z ^ i) x :=
    (show Commute x z from Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hx)).symm.zpow_left i
  rw [this.eq]; group

theorem delta_isClass (hQ : Config D u w v z a K₁ S') {e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    ∀ x ∈ Delta D e, ∀ y ∈ Delta D e, ∃ k ∈ thirdK D e, k * x * k⁻¹ = y := by
  intro x hx y hy
  obtain ⟨n, hn, -, hord, rfl⟩ := hQ.third
  obtain ⟨-, -, hzu, hzv, hzw, -⟩ :=
    IsTriangle.third_kind hQ.setup.oddT hQ.setup.normal hQ.tri hn hord
  obtain ⟨huΔ, hvΔ, hwΔ⟩ := vertices_mem_Delta hQ.tri hzu hzv hzw
  have hc : ∀ t ∈ Delta D ((u * v * w) ^ n), Commute t e := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hzK (Delta_subset_thirdK ht))
  have T := thirdK_transitive_of_commute hQ.setup hQ.local2 hQ.tri hn hord (hc u huΔ)
    (hc v hvΔ) (hc w hwΔ)
  obtain ⟨k₁, hk₁, rfl⟩ := T x hx
  obtain ⟨k₂, hk₂, rfl⟩ := T y hy
  exact ⟨k₂ * k₁⁻¹, Subgroup.mul_mem _ hk₂ (Subgroup.inv_mem _ hk₁), by group⟩

theorem thirdK_inf_radical (hQ : Config D u w v z a K₁ S') {e : G} (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    (thirdK D z).subgroupOf (thirdK D e) ⊓ CFSG.solvableRadical (thirdK D e) = ⊥ := by
  classical
  obtain ⟨hz1', -, -, -, -, -⟩ := hQ.z_facts
  obtain ⟨X₁, ⟨eX⟩, hX, hXa, -, hcard⟩ := hQ.conj_data
  obtain ⟨eK⟩ := hQ.K₁_A5
  set Y := thirdK D e
  have hsubY : ∀ c : G, thirdK D c ≤ Subgroup.centralizer ({e} : Set G) → thirdK D c ≤ Y :=
    fun c hc => Subgroup.closure_mono fun d hd => by
      rw [mem_Delta_iff] at hd ⊢
      exact ⟨hd.1, Subgroup.mem_centralizer_singleton_iff.mp
        (hc (Delta_subset_thirdK (mem_Delta_iff.mpr hd)))⟩
  have hK₁Y : K₁ ≤ Y := (hQ.K_eq ▸ le_sup_left : K₁ ≤ thirdK D z).trans (hsubY z hzK)
  have hX₁Y : X₁ ≤ Y := (hX ▸ le_sup_left : X₁ ≤ thirdK D a).trans (hsubY a haK)
  have haz : Commute z a :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hQ.a_mem) : Commute a z).symm
  have hzX : ∀ k ∈ X₁, z * k * z⁻¹ ∈ X₁ := conj_mem_of_conj_mem_sup eX hXa fun t ht => by
    rw [← hX] at ht ⊢; exact conj_mem_thirdK_of_commute hQ.setup.normal haz ht
  set O : Subgroup G := (CFSG.solvableRadical Y).map Y.subtype
  have hOn : ∀ y ∈ Y, ∀ o ∈ O, y * o * y⁻¹ ∈ O := by
    rintro y hy _ ⟨o, ho, rfl⟩
    exact ⟨⟨y, hy⟩ * o * ⟨y, hy⟩⁻¹,
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.instNormalSolvableRadical).conj_mem o ho _,
      by simp⟩
  have hOs : Group.IsSolvable O := by
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := Y)
    let f := ((CFSG.solvableRadical Y).equivMapOfInjective Y.subtype Y.subtype_injective).symm
    exact solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
  have h9 := sup_zpowers_inf_eq_bot hOn hOs eK eX hK₁Y hX₁Y hz1'
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hk)) hzX
    (hQ.z_not_mem_centralizer hX hcard)
  rw [eq_bot_iff]
  rintro y ⟨hy1, hy2⟩
  have : (y : G) ∈ (K₁ ⊔ Subgroup.zpowers z) ⊓ O :=
    ⟨hQ.K_eq ▸ Subgroup.mem_subgroupOf.mp hy1, ⟨y, hy2, rfl⟩⟩
  rw [h9, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

noncomputable def barOmega (D : Set G) (e : G) : Set (thirdK D e ⧸ CFSG.solvableRadical (thirdK D e)) :=
  (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e))) '' {x : thirdK D e | (x : G) ∈ D}

theorem barOmega_eq_image (D : Set G) (e : G) :
    barOmega D e = (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e))) ''
      {x : thirdK D e | (x : G) ∈ D} := by
  unfold barOmega
  rfl

theorem DeltaK_eq_D_of_thirdK_le_centralizer (D : Set G) (e : G) :
    DeltaK D e = {x : thirdK D e | (x : G) ∈ D} := by
  ext x
  change (x : G) ∈ Delta D e ↔ (x : G) ∈ D
  rw [mem_Delta_iff]
  exact ⟨fun h => h.1,
    fun h => ⟨h, Subgroup.mem_centralizer_singleton_iff.mp (thirdK_le_centralizer x.2)⟩⟩

theorem DeltaBar_eq_barOmega (D : Set G) (e : G) :
    DeltaBar D e = barOmega D e := by
  unfold DeltaBar barOmega
  rw [DeltaK_eq_D_of_thirdK_le_centralizer]

theorem thirdK_le_thirdK_of_le_centralizer {z e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G)) :
    thirdK D z ≤ thirdK D e := by
  rw [thirdK, Subgroup.closure_le]
  intro x hx
  exact Delta_subset_thirdK (mem_Delta_iff.mpr
    ⟨(mem_Delta_iff.mp hx).1,
      Subgroup.mem_centralizer_singleton_iff.mp (hzK (Delta_subset_thirdK hx))⟩)

theorem u_mem_Delta_e (hQ : Config D u w v z a K₁ S') {e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G)) : u ∈ Delta D e := by
  obtain ⟨-, -, huΔz, -⟩ := hQ.z_facts
  exact mem_Delta_iff.mpr ⟨hQ.tri.1,
    Subgroup.mem_centralizer_singleton_iff.mp (hzK (Delta_subset_thirdK huΔz))⟩

theorem u_not_mem_radical (hQ : Config D u w v z a K₁ S') {e : G}
    (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    (⟨u, Delta_subset_thirdK (u_mem_Delta_e hQ hzK)⟩ :
      thirdK D e) ∉ CFSG.solvableRadical (thirdK D e) := by
  intro huR
  obtain ⟨-, -, huΔz, -⟩ := hQ.z_facts
  have hKY := thirdK_le_thirdK_of_le_centralizer (D := D) (z := z) (e := e) hzK
  have huY : u ∈ thirdK D e := hKY (Delta_subset_thirdK huΔz)
  have h9 := thirdK_inf_radical hQ he hzK haK
  have hmem : (⟨u, huY⟩ : thirdK D e) ∈
      (thirdK D z).subgroupOf (thirdK D e) ⊓ CFSG.solvableRadical (thirdK D e) :=
    ⟨Subgroup.mem_subgroupOf.mpr (Delta_subset_thirdK huΔz), huR⟩
  rw [h9, Subgroup.mem_bot] at hmem
  exact hQ.setup.oddT.ne_one hQ.tri.1 (congrArg Subtype.val hmem)

theorem DeltaK_class_e (hQ : Config D u w v z a K₁ S') {e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    ∃ d₀ : thirdK D e, DeltaK D e = {x | IsConj d₀ x} := by
  refine ⟨⟨u, Delta_subset_thirdK (u_mem_Delta_e hQ hzK)⟩, ?_⟩
  ext x
  constructor
  · intro hx
    have hxΔ : (x : G) ∈ Delta D e := hx
    obtain ⟨k, hk, hku⟩ :=
      hQ.delta_isClass hzK haK u (u_mem_Delta_e hQ hzK) (x : G) hxΔ
    simp only [Set.mem_setOf_eq]
    rw [isConj_iff]
    exact ⟨⟨k, hk⟩, Subtype.ext hku⟩
  · intro hx
    simp only [Set.mem_setOf_eq] at hx
    rw [isConj_iff] at hx
    obtain ⟨c, hc⟩ := hx
    have hcG : (c : G) * u * (c : G)⁻¹ = (x : G) := by
      simpa using congrArg Subtype.val hc
    change (x : G) ∈ Delta D e
    rw [← hcG]
    exact Delta_conj_mem hQ.setup.normal c.2 (u_mem_Delta_e hQ hzK)

theorem DeltaK_mk_ne_one_e (hQ : Config D u w v z a K₁ S') {e : G}
    (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    ∀ x ∈ DeltaK D e,
      QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) x ≠ 1 := by
  intro x hx hx1
  have hxR : x ∈ CFSG.solvableRadical (thirdK D e) :=
    (QuotientGroup.eq_one_iff x).mp hx1
  obtain ⟨k, hk, hku⟩ :=
    hQ.delta_isClass hzK haK u (u_mem_Delta_e hQ hzK) (x : G) hx
  let kY : thirdK D e := ⟨k, hk⟩
  have hconj : kY⁻¹ * x * kY ∈ CFSG.solvableRadical (thirdK D e) := by
    simpa using (CFSG.SignalizerFunctorTheorem.Nonsolvable.instNormalSolvableRadical).conj_mem
      x hxR kY⁻¹
  have huR : (⟨u, Delta_subset_thirdK (u_mem_Delta_e hQ hzK)⟩ :
      thirdK D e) ∈ CFSG.solvableRadical (thirdK D e) := by
    have hux : (⟨u, Delta_subset_thirdK (u_mem_Delta_e hQ hzK)⟩ : thirdK D e) =
        kY⁻¹ * x * kY := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, kY]
      rw [← hku]
      group
    rwa [hux]
  exact u_not_mem_radical hQ he hzK haK huR

theorem setup_barOmega (hQ : Config D u w v z a K₁ S') {e : G}
    (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    Setup (thirdK D e ⧸ CFSG.solvableRadical (thirdK D e)) (barOmega D e) := by
  obtain ⟨d₀, hclass⟩ := DeltaK_class_e hQ hzK haK
  have hsetup : Setup (thirdK D e ⧸ CFSG.solvableRadical (thirdK D e)) (DeltaBar D e) :=
    { isClass := image_isClass_quotient hclass _
      oddT := image_isOddTransp_quotient _
        (DeltaK_isOddTransp hQ.setup e) (DeltaK_mk_ne_one_e hQ he hzK haK)
      gen := image_closure_eq_top_quotient _ (DeltaK_closure_eq_top e) }
  rwa [DeltaBar_eq_barOmega] at hsetup

theorem localSecond_barOmega (hQ : Config D u w v z a K₁ S') {e : G}
    (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    LocalSecond (barOmega D e) := by
  have h := localSecond_quotient_class (D := D) hQ.setup hQ.local2
    (DeltaK_class_e hQ hzK haK) (DeltaK_mk_ne_one_e hQ he hzK haK)
  rwa [DeltaBar_eq_barOmega] at h

theorem thirdK_e_ne_top (hQ : Config D u w v z a K₁ S') {e : G} (he2 : orderOf e = 2) :
    thirdK D e ≠ ⊤ := by
  intro htop
  have hle : thirdK D e ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [thirdK, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mem_Delta_iff.mp hx).2
  have htopC : Subgroup.centralizer ({e} : Set G) = ⊤ := top_le_iff.mp (htop ▸ hle)
  have heZ : e ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [htopC]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hQ.center, Subgroup.mem_bot] at heZ
  have h1 : orderOf e = 1 := orderOf_eq_one_iff.mpr heZ
  omega

theorem thirdK_z_to_Yb_injective (hQ : Config D u w v z a K₁ S') {e : G}
    (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G)) :
    Function.Injective (fun x : thirdK D z =>
      (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
        ⟨x, thirdK_le_thirdK_of_le_centralizer hzK x.2⟩) := by
  intro a b hab
  have h9 := thirdK_inf_radical hQ he hzK haK
  have hKY := thirdK_le_thirdK_of_le_centralizer (D := D) (z := z) (e := e) hzK
  have hR : ((⟨a, hKY a.2⟩ : thirdK D e)⁻¹ * ⟨b, hKY b.2⟩) ∈
      CFSG.solvableRadical (thirdK D e) :=
    (QuotientGroup.eq_one_iff _).mp (by
      change (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
        ((⟨a, hKY a.2⟩ : thirdK D e)⁻¹ * ⟨b, hKY b.2⟩) = 1
      rw [map_mul, map_inv]
      exact (congrArg (fun z => z⁻¹ *
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e))) ⟨b, hKY b.2⟩) hab).trans
        (inv_mul_cancel _))
  have hmem' : ((⟨a, hKY a.2⟩ : thirdK D e)⁻¹ * ⟨b, hKY b.2⟩) ∈
      (thirdK D z).subgroupOf (thirdK D e) ⊓ CFSG.solvableRadical (thirdK D e) :=
    ⟨Subgroup.mem_subgroupOf.mpr (by
      simpa using (thirdK D z).mul_mem ((thirdK D z).inv_mem a.2) b.2), hR⟩
  rw [h9, Subgroup.mem_bot] at hmem'
  have h1 : (a : G)⁻¹ * (b : G) = 1 := by
    have := congrArg Subtype.val hmem'
    simpa using this
  exact Subtype.ext (inv_mul_eq_one.mp h1)

theorem false_of_connected_of_threeTransposition (hQ : Config D u w v z a K₁ S')
    (hC : HypothesisC D) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {e : G} (he2 : orderOf e = 2) (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G))
    (h3 : ∀ d ∈ barOmega D e, ∀ g ∈ barOmega D e,
      orderOf (d * g) ∈ ({1, 2, 3} : Set ℕ)) : False := by
  classical
  have h9 := thirdK_inf_radical hQ he hzK haK
  have hKY := thirdK_le_thirdK_of_le_centralizer (D := D) (z := z) (e := e) hzK
  obtain ⟨-, -, huΔz, hvΔz, hwΔz, -⟩ := hQ.z_facts
  have huK : u ∈ thirdK D z := Delta_subset_thirdK huΔz
  have hvK : v ∈ thirdK D z := Delta_subset_thirdK hvΔz
  have hwK : w ∈ thirdK D z := Delta_subset_thirdK hwΔz
  let Y := thirdK D e
  let O : Subgroup Y := CFSG.solvableRadical Y
  let mk : Y →* Y ⧸ O := QuotientGroup.mk' O
  let uY : Y := ⟨u, hKY huK⟩
  let vY : Y := ⟨v, hKY hvK⟩
  let wY : Y := ⟨w, hKY hwK⟩
  have huΔe : u ∈ Delta D e := u_mem_Delta_e hQ hzK
  have hvΔe : v ∈ Delta D e := mem_Delta_iff.mpr ⟨hQ.tri.2.1,
    Subgroup.mem_centralizer_singleton_iff.mp (hzK (Delta_subset_thirdK hvΔz))⟩
  have hwΔe : w ∈ Delta D e := mem_Delta_iff.mpr ⟨hQ.tri.2.2.1,
    Subgroup.mem_centralizer_singleton_iff.mp (hzK (Delta_subset_thirdK hwΔz))⟩
  have huΩ : mk uY ∈ barOmega D e := by
    rw [← DeltaBar_eq_barOmega]
    exact ⟨uY, huΔe, rfl⟩
  have hvΩ : mk vY ∈ barOmega D e := by
    rw [← DeltaBar_eq_barOmega]
    exact ⟨vY, hvΔe, rfl⟩
  have hwΩ : mk wY ∈ barOmega D e := by
    rw [← DeltaBar_eq_barOmega]
    exact ⟨wY, hwΔe, rfl⟩
  have hne_uv : mk uY ≠ mk vY := by
    intro hEq
    have hmemO : uY⁻¹ * vY ∈ O := by
      have h1 : mk (uY⁻¹ * vY) = 1 := by
        rw [map_mul, map_inv]
        exact (congrArg (fun z => z⁻¹ * mk vY) hEq).trans (inv_mul_cancel _)
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmemK : uY⁻¹ * vY ∈ (thirdK D z).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      show (uY : G)⁻¹ * (vY : G) ∈ thirdK D z
      simpa using (thirdK D z).mul_mem ((thirdK D z).inv_mem huK) hvK
    have hmemInf : uY⁻¹ * vY ∈ (thirdK D z).subgroupOf Y ⊓ O := ⟨hmemK, hmemO⟩
    rw [h9, Subgroup.mem_bot] at hmemInf
    have h1 : (uY : G)⁻¹ * (vY : G) = 1 := by
      have := congrArg Subtype.val hmemInf
      simpa using this
    exact hQ.tri.2.2.2.1 (by simpa [uY, vY] using inv_mul_eq_one.mp h1)
  have hne_uw : mk uY ≠ mk wY := by
    intro hEq
    have hmemO : uY⁻¹ * wY ∈ O := by
      have h1 : mk (uY⁻¹ * wY) = 1 := by
        rw [map_mul, map_inv]
        exact (congrArg (fun z => z⁻¹ * mk wY) hEq).trans (inv_mul_cancel _)
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmemK : uY⁻¹ * wY ∈ (thirdK D z).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      show (uY : G)⁻¹ * (wY : G) ∈ thirdK D z
      simpa using (thirdK D z).mul_mem ((thirdK D z).inv_mem huK) hwK
    have hmemInf : uY⁻¹ * wY ∈ (thirdK D z).subgroupOf Y ⊓ O := ⟨hmemK, hmemO⟩
    rw [h9, Subgroup.mem_bot] at hmemInf
    have h1 : (uY : G)⁻¹ * (wY : G) = 1 := by
      have := congrArg Subtype.val hmemInf
      simpa using this
    apply hQ.tri.2.2.2.2.2.1
    rw [show u = w by simpa [uY, wY] using inv_mul_eq_one.mp h1]
  have hne_vw : mk vY ≠ mk wY := by
    intro hEq
    have hmemO : vY⁻¹ * wY ∈ O := by
      have h1 : mk (vY⁻¹ * wY) = 1 := by
        rw [map_mul, map_inv]
        exact (congrArg (fun z => z⁻¹ * mk wY) hEq).trans (inv_mul_cancel _)
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmemK : vY⁻¹ * wY ∈ (thirdK D z).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      show (vY : G)⁻¹ * (wY : G) ∈ thirdK D z
      simpa using (thirdK D z).mul_mem ((thirdK D z).inv_mem hvK) hwK
    have hmemInf : vY⁻¹ * wY ∈ (thirdK D z).subgroupOf Y ⊓ O := ⟨hmemK, hmemO⟩
    rw [h9, Subgroup.mem_bot] at hmemInf
    have h1 : (vY : G)⁻¹ * (wY : G) = 1 := by
      have := congrArg Subtype.val hmemInf
      simpa using this
    apply hQ.tri.2.2.2.2.2.2
    rw [show v = w by simpa [vY, wY] using inv_mul_eq_one.mp h1]
  have hcomm_uv : Commute (mk uY) (mk vY) :=
    ((commute_iff_eq _ _).mpr (Subtype.ext hQ.tri.2.2.2.2.1.eq)).map mk
  have hnc_uw : ¬ Commute (mk uY) (mk wY) := by
    intro hc
    have hnc : ¬ Commute uY wY := fun h =>
      hQ.tri.2.2.2.2.2.1 ((commute_iff_eq _ _).mpr (by
        simpa using congrArg Subtype.val h.eq))
    have hodd : Odd (orderOf (uY * wY)) :=
      (DeltaK_isOddTransp hQ.setup e).odd_of_not_commute huΔe hwΔe hnc
    exact hne_uw (eq_of_commute_of_odd (DeltaK_isOddTransp hQ.setup e) huΔe hwΔe hc hodd)
  have hnc_vw : ¬ Commute (mk vY) (mk wY) := by
    intro hc
    have hnc : ¬ Commute vY wY := fun h =>
      hQ.tri.2.2.2.2.2.2 ((commute_iff_eq _ _).mpr (by
        simpa using congrArg Subtype.val h.eq))
    have hodd : Odd (orderOf (vY * wY)) :=
      (DeltaK_isOddTransp hQ.setup e).odd_of_not_commute hvΔe hwΔe hnc
    exact hne_vw (eq_of_commute_of_odd (DeltaK_isOddTransp hQ.setup e) hvΔe hwΔe hc hodd)
  have htriΩ : IsTriangle (barOmega D e) (mk uY) (mk wY) (mk vY) :=
    ⟨huΩ, hvΩ, hwΩ, hne_uv, hcomm_uv, hnc_uw, hnc_vw⟩
  obtain ⟨n, hn, hn1, hord, hzeq⟩ := hQ.third
  let prodK : thirdK D z :=
    ⟨u * v * w, (thirdK D z).mul_mem ((thirdK D z).mul_mem huK hvK) hwK⟩
  have hordY : orderOf prodK = 2 * n := by
    rw [← Subgroup.orderOf_coe]
    simpa [prodK] using hord
  have hprod : mk uY * mk vY * mk wY = mk ⟨prodK, hKY prodK.2⟩ := by
    simp only [mk, map_mul, uY, vY, wY, prodK]
    rfl
  have hord_bar : orderOf (mk uY * mk vY * mk wY) = 2 * n := by
    rw [hprod, orderOf_thirdK_map_quotient hzK h9 prodK, hordY]
  have hoddΩ : IsOddTransp (barOmega D e) := by
    rw [← DeltaBar_eq_barOmega]
    exact image_isOddTransp_quotient _ (DeltaK_isOddTransp hQ.setup e)
      (DeltaK_mk_ne_one_e hQ he hzK haK)
  have hdvd : orderOf (mk uY * mk vY * mk wY) ∣ 4 :=
    orderOf_mul_dvd_four_of_threeTransposition hoddΩ h3 htriΩ
  rw [hord_bar] at hdvd
  have hn2 : n ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
  have hnle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hn2
  have hoddn : Odd n := hn
  rcases hoddn with ⟨k, hk⟩
  omega

end Config

end CFSG.OddTranspositions.QZ
