module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXTheta
import CFSG.HardMathSupport.Lang.D4Three.Outer
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Cent
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.LiftedSchreierData
import CFSG.Certificates.WordSubgroupHom
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Final
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Toolkit.M12Local
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate1000
import Certificates.Certificate1001
import Certificates.Certificate1001Base
import Certificates.Certificate10027
import Certificates.Certificate1004
import Certificates.Certificate1006
import Certificates.Certificate1007
import Certificates.Certificate1007Base
import Certificates.Certificate1008
import Certificates.Certificate1010
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate1011
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate10115
import Certificates.Certificate10115Base
import Certificates.Certificate10116
import Certificates.Certificate10116Base
import Certificates.Certificate10117
import Certificates.Certificate10117Base
import Certificates.Certificate10118
import Certificates.Certificate10118Base
import Certificates.Certificate10119
import Certificates.Certificate10119Base
import Certificates.Certificate10123
import Certificates.Certificate10123Base
import Certificates.Certificate1013
import Certificates.Certificate1014
import Certificates.Certificate1014Base
import Certificates.Certificate1015
import Certificates.Certificate1017
import Certificates.Certificate1018
import Certificates.Certificate1018Base
import Certificates.Certificate1019
import Certificates.Certificate14953
import Certificates.Certificate16018
import Certificates.Certificate16041
import Certificates.Certificate2051
import Certificates.Certificate2053
import Certificates.Certificate2056
import Certificates.Certificate2057
import Certificates.Certificate2058
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2108
import Certificates.Certificate2109
import Certificates.Certificate2130
import Certificates.Certificate2135
import Certificates.Certificate2136
import Certificates.Certificate2139
import Certificates.Certificate2140
import Certificates.Certificate2145
import Certificates.Certificate2160
import Certificates.Certificate2207
import Certificates.Certificate2233
import Certificates.Certificate2233Base
import Certificates.Certificate2234
import Certificates.Certificate2235
import Certificates.Certificate2246
import Certificates.Certificate2293
import Certificates.Certificate2294
import Certificates.Certificate2304
import Certificates.Certificate2305
import Certificates.Certificate2308
import Certificates.Certificate2323
import Certificates.Certificate3037
import Certificates.Certificate3037Base
import Certificates.Certificate3038
import Certificates.Certificate3038Base
import Certificates.Certificate3114
import Certificates.Certificate3148
import Certificates.Certificate3148Base
import Certificates.Certificate3150
import Certificates.Certificate3150Base
import Certificates.Certificate3151
import Certificates.Certificate3151Base
import Certificates.Certificate3152
import Certificates.Certificate3152Base
import Certificates.Certificate3153
import Certificates.Certificate3153Base
import Certificates.Certificate3154
import Certificates.Certificate3154Base
import Certificates.Certificate5133
import Certificates.Certificate6006
import Certificates.Certificate6103
import Certificates.Certificate8166
import Certificates.Certificate8169
import Certificates.Certificate9124

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma center_map_eq_zpowers {C H : Type*} [Group C] [Group H] [Finite C]
    (φ : C →* H) (hφ : Function.Injective φ)
    {T : C} (hT : orderOf T = 3) {P : Subgroup C}
    (hPcard : Nat.card P = 3 ^ (Nat.card C).factorization 3)
    (hcent : ∀ y ∈ P, (∀ p ∈ P, p * y = y * p) → ∃ j : ℕ, φ y = φ T ^ j) :
    (Subgroup.center P).map P.subtype = Subgroup.zpowers T := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := by
    have := (Sylow.ofCard P hPcard).isPGroup'
    rwa [Sylow.coe_ofCard] at this
  have h3dvd : 3 ∣ Nat.card C := by
    rw [← hT]
    exact orderOf_dvd_natCard T
  have hfacpos : 0 < (Nat.card C).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos.ne') h3dvd
  have hcardP1 : 1 < Nat.card P := by
    rw [hPcard]
    exact Nat.one_lt_pow hfacpos.ne' (by norm_num)
  haveI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hcardP1
  have hZnt : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hZle : (Subgroup.center P).map P.subtype ≤ Subgroup.zpowers T := by
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨j, hj⟩ := hcent u u.2 (fun p hp =>
      congrArg P.subtype (Subgroup.mem_center_iff.mp hu ⟨p, hp⟩))
    change (u : C) ∈ Subgroup.zpowers T
    have huj : u = T ^ j := hφ (hj.trans (map_pow φ T j).symm)
    rw [huj]
    exact pow_mem (Subgroup.mem_zpowers T) j
  have hZcard : Nat.card ((Subgroup.center P).map P.subtype) =
      Nat.card (Subgroup.zpowers T) := by
    rw [Nat.card_zpowers, hT]
    have hdvd : Nat.card ((Subgroup.center P).map P.subtype) ∣ 3 := by
      have := Subgroup.card_dvd_of_le hZle
      rwa [Nat.card_zpowers, hT] at this
    have hnt : Nat.card ((Subgroup.center P).map P.subtype) ≠ 1 := by
      have hZc_card : Nat.card ((Subgroup.center P).map P.subtype) =
          Nat.card (Subgroup.center P) :=
        Subgroup.card_map_of_injective P.subtype_injective
      rw [hZc_card]
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne'
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hnt
    · exact h3
  exact Subgroup.eq_of_le_of_card_ge hZle (le_of_eq hZcard.symm)

private lemma commute_of_mem_center_map {C : Type*} [Group C] {P : Subgroup C} {z : C}
    (hz : z ∈ (Subgroup.center P).map P.subtype) {y : C} (hy : y ∈ P) :
    y * z = z * y := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
  exact congrArg P.subtype (Subgroup.mem_center_iff.mp hu ⟨y, hy⟩)

theorem triD4Line_kgX
    {n : ℕ} (K : Type) [Field K] (hev : Even n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n) :
    ∃ (z₀ : GGTriD4R n K) (α : MulAut (GGTriD4R n K)) (σ : K ≃ₐ[k] K)
      (Θ : Subgroup.centralizer {z₀} ≃* TriD4LineX k K),
      orderOf z₀ = 3 ∧ (∃ P : Sylow 3 (GGTriD4R n K),
        z₀ ∈ (P : Subgroup (GGTriD4R n K)) ∧
          ∀ y ∈ (P : Subgroup (GGTriD4R n K)), y * z₀ = z₀ * y) ∧
      α ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut _) ∧ orderOf α = 3 ∧ α z₀ = z₀ ∧
      orderOf σ = 3 ∧
      ∀ (y : Subgroup.centralizer {z₀}) (hy : α y ∈ Subgroup.centralizer {z₀}),
        (Θ ⟨α y, hy⟩ : TriD4LineX k K) = triD4LineSigma k K σ (Θ y) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hK, hn]; norm_num
      have hnt : 1 < Nat.card K :=
        Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
      rw [h1] at hnt
      exact absurd hnt (by norm_num)
    · exact hn
  have h1n : 1 ≤ n := hn
  haveI : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  haveI : Finite k := Finite.of_injective _ (algebraMap k K).injective
  letI : Fintype k := Fintype.ofFinite k
  have hcardk : ∀ a : k, a ^ Nat.card k = a := fun a => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  set σ₀ := iterateFrobeniusEquiv K 2 n with hσ₀def
  have hσ : ∀ c : K, σ₀ c = c ^ 2 ^ n := fun c => by
    rw [hσ₀def, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσ3 : σ₀ ^ 3 = 1 :=
    CFSG.HardMathSupport.Lang.D4Three.sigma_cube (p := 2) (f := n) hK σ₀ hσ
  have h3dvd : 3 ∣ Nat.card k - 1 := by
    rw [hk]
    have hmod : 2 ^ n % 3 = 1 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.two_pow_mod_three]
      simp [hev]
    simpa [hmod] using Nat.dvd_sub_mod (n := 3) (2 ^ n)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ωk, hωk⟩ :=
    exists_prime_orderOf_dvd_card' (G := kˣ) 3 (by rwa [Nat.card_units])
  let ω : Kˣ := Units.map (algebraMap k K).toMonoidHom ωk
  have hωk3 : ωk ^ 3 = 1 := by rw [← hωk]; exact pow_orderOf_eq_one ωk
  have hω3 : ω ^ 3 = 1 := by
    change (Units.map (algebraMap k K).toMonoidHom ωk) ^ 3 = 1
    rw [← map_pow, hωk3, map_one]
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : ωk = 1 := Units.map_injective (algebraMap k K).injective (by
      rw [show (Units.map (algebraMap k K).toMonoidHom) ωk = 1 from h, map_one])
    rw [h1, orderOf_one] at hωk
    exact absurd hωk (by norm_num)
  have hσalg : ∀ a : k, σ₀ (algebraMap k K a) = algebraMap k K a := by
    intro a
    rw [hσ, ← map_pow]
    congr 1
    rw [← hk]
    exact hcardk a
  have hσω : Units.map σ₀.toRingHom.toMonoidHom ω = ω := by
    apply Units.ext
    change σ₀ (algebraMap k K (ωk : k)) = algebraMap k K (ωk : k)
    exact hσalg (ωk : k)
  have hωfix : (ω : K) ∈ trialityFixedField K σ₀.toRingHom := by
    rw [mem_trialityFixedField]
    simpa using congrArg Units.val hσω
  let ζ : (trialityFixedField K σ₀.toRingHom)ˣ :=
    Units.mk0 ⟨(ω : K), hωfix⟩ (by
      intro h
      exact ω.ne_zero (by simpa using congrArg Subtype.val h))
  have hζval : trialityFixedUnit K σ₀ ζ = ω := Units.ext rfl
  have hωord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hζ : orderOf (trialityFixedUnit K σ₀ ζ) = 3 := by rw [hζval, hωord]
  let τ : K ≃ₐ[k] K := AlgEquiv.ofRingEquiv (f := σ₀) hσalg
  have hτ : ∀ c : K, τ c = σ₀ c := fun c => AlgEquiv.ofRingEquiv_apply hσalg c
  have hτ3 : τ ^ 3 = 1 := by
    apply AlgEquiv.ext
    intro c
    change (τ * τ * τ) c = (1 : K ≃ₐ[k] K) c
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    simp only [hτ]
    rw [← ringEquiv_pow_three_apply, hσ3]
    rfl
  have hτ1 : τ ≠ 1 := by
    intro h
    apply CFSG.HardMathSupport.Lang.D4Three.sigma_ne_one (p := 2) (f := n)
      Nat.prime_two h1n hK σ₀ hσ
    ext c
    rw [← hτ c, h]
    rfl
  have hτord : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  obtain ⟨hz, hzord, hzfix, -⟩ :=
    triD4Line_trialityOuterTorus_z0 (K := K) (σ := σ₀) hσ3 ω hω3 hω1
  let z0' : graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom :=
    ⟨trialityOuterTorus K σ₀ ω, hz⟩
  have hz0'ord : orderOf z0' = 3 := hzord
  have hz0'fix : fieldActor (t := TwistTag.D4) σ₀ σ₀ z0' = z0' := hzfix
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv (n := n) h1n K hK σ₀ hσ
  haveI : Finite (GGTriD4R n K) :=
    Finite.of_equiv (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) e.symm.toEquiv
  let z0 : GGTriD4R n K := e.symm z0'
  let φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) :=
    fieldActor (t := TwistTag.D4) σ₀ σ₀
  let α : MulAut (GGTriD4R n K) := MulAut.congr e.symm φ
  have heα : ∀ y : GGTriD4R n K, e (α y) = φ (e y) := by
    intro y
    change e ((MulAut.congr e.symm φ) y) = φ (e y)
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have hz0 : e z0 = z0' := e.apply_symm_apply z0'
  have hz0ord : orderOf z0 = 3 := by
    change orderOf (e.symm z0') = 3
    rw [show orderOf (e.symm z0') = orderOf z0' from
      orderOf_injective e.symm.toMonoidHom e.symm.injective z0']
    exact hz0'ord
  have hφ3 : φ ^ 3 = 1 :=
    CFSG.HardMathSupport.Lang.D4Three.fieldActor_cube (K := K) (σ := σ₀) hσ3
  have hφ_out : φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) :=
    CFSG.HardMathSupport.Lang.D4Three.fieldActor_not_inner (p := 2) (f := n)
      Nat.prime_two h1n hK σ₀ hσ
  have hφ1 : φ ≠ 1 := by
    intro h
    refine hφ_out ?_
    show φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom)
    rw [h]
    exact Subgroup.one_mem _
  have hα1 : α ≠ 1 := by
    intro h
    apply hφ1
    have h2 : (MulAut.congr e.symm) φ = (MulAut.congr e.symm) 1 := by
      rw [map_one]
      exact h
    exact (MulAut.congr e.symm).injective h2
  have hα3 : α ^ 3 = 1 := by
    change (MulAut.congr e.symm φ) ^ 3 = 1
    rw [← map_pow, hφ3, map_one]
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hα_out : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (GGTriD4R n K) := by
    intro hα
    have hmap := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e.symm
    have hmem : α ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom)).map
        (MulAut.congr e.symm).toMonoidHom := by
      rw [hmap]
      exact hα
    obtain ⟨β, hβ, hβeq⟩ := Subgroup.mem_map.mp hmem
    refine hφ_out ?_
    have h2 : (MulAut.congr e.symm) β = (MulAut.congr e.symm) φ := by
      change (MulAut.congr e.symm) β = α
      exact hβeq
    exact (MulAut.congr e.symm).injective h2 ▸ hβ
  have hαz : α z0 = z0 := by
    apply e.injective
    rw [heα, hz0]
    exact hz0'fix
  obtain ⟨P₀, hP₀card, hP₀cent⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item219LieProof.exists_sylow_center (K := K) (σ := σ₀)
      hn hev hK hσ (ζ := ζ) hζ
  rw [hζval] at hP₀cent
  have hZeq := center_map_eq_zpowers
    (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom).subtype
    (Subgroup.subtype_injective (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom))
    hz0'ord hP₀card hP₀cent
  have hz0'Zmap : z0' ∈ (Subgroup.center P₀).map P₀.subtype := by
    rw [hZeq]
    exact Subgroup.mem_zpowers z0'
  have hz0'P : z0' ∈ P₀ := Subgroup.map_subtype_le (Subgroup.center P₀) hz0'Zmap
  let PG : Subgroup (GGTriD4R n K) := P₀.map e.symm.toMonoidHom
  have hPGcard : Nat.card PG = 3 ^ (Nat.card (GGTriD4R n K)).factorization 3 := by
    have h1 : Nat.card PG = Nat.card P₀ := Subgroup.card_map_of_injective e.symm.injective
    have h2 : Nat.card (GGTriD4R n K) =
        Nat.card (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) := Nat.card_congr e.toEquiv
    rw [h1, hP₀card, h2]
  let P : Sylow 3 (GGTriD4R n K) := Sylow.ofCard PG hPGcard
  have hPcoe : (P : Subgroup (GGTriD4R n K)) = PG := Sylow.coe_ofCard PG hPGcard
  have hz0PG : z0 ∈ PG := by
    change z0 ∈ P₀.map e.symm.toMonoidHom
    exact Subgroup.mem_map.mpr ⟨z0', hz0'P, rfl⟩
  have hz0cent : ∀ y ∈ PG, y * z0 = z0 * y := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    change (e.symm y') * z0 = z0 * (e.symm y')
    apply e.injective
    simp only [map_mul, e.apply_symm_apply, hz0]
    exact commute_of_mem_center_map hz0'Zmap hy'
  let ce : Subgroup.centralizer {z0} ≃* Subgroup.centralizer {z0'} :=
    { toFun := fun y => ⟨e y, by
        have hy : y.1 * z0 = z0 * y.1 := Subgroup.mem_centralizer_singleton_iff.mp y.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hz0, ← map_mul, ← map_mul, hy]⟩
      invFun := fun y => ⟨e.symm y, by
        have hy : y.1 * z0' = z0' * y.1 := Subgroup.mem_centralizer_singleton_iff.mp y.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply e.injective
        simp only [map_mul, e.apply_symm_apply, hz0]
        exact hy⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun y y' => Subtype.ext (map_mul e y.1 y'.1) }
  obtain ⟨Θ', hΘ'⟩ :=
    triD4Line_exists_theta (K := K) hK σ₀ hσ k hk τ hτ ω hω3 hω1 hz
  let Θ : Subgroup.centralizer {z0} ≃* TriD4LineX k K := ce.trans Θ'
  refine ⟨z0, α, τ, Θ, hz0ord, ⟨P, ?_, ?_⟩, ?_, hαord, hαz, hτord, ?_⟩
  · rw [hPcoe]
    exact hz0PG
  · intro y hy
    rw [hPcoe] at hy
    exact hz0cent y hy
  · simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hα_out
  · intro y hy
    change Θ' (ce ⟨α y, hy⟩) = triD4LineSigma k K τ (Θ' (ce y))
    have hmem : φ (ce y) ∈ Subgroup.centralizer {z0'} := by
      have hval : (ce ⟨α y, hy⟩ : graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) =
          φ (ce y) := by
        change e (α y) = φ (e y)
        exact heα y
      rw [← hval]
      exact (ce ⟨α y, hy⟩).2
    have hce_alpha : ce ⟨α y, hy⟩ = ⟨φ (ce y), hmem⟩ := by
      apply Subtype.ext
      change e (α y) = φ (e y)
      exact heα y
    rw [hce_alpha]
    exact hΘ' (ce y) hmem

end CFSG.StandardType