module

public import CFSG.LocalAnalysis.StandardType.GGExcCompLiftRestInput
public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGExcSevenTwoTorus
import CFSG.LocalAnalysis.StandardType.GGExcSevenTwoFC
import CFSG.LocalAnalysis.StandardType.GGLangRatCompC
import CFSG.LocalAnalysis.StandardType.GGExcLangPairAt
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGLangRatCompKillsPHolds

public section

namespace CFSG.StandardType.LangSeven

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.LangRat
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

private theorem langSeven2_exists_mem_componentRoots {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    ∃ γ, γ ∈ componentRoots χ i := by
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  exact ⟨γ, hγ, rfl⟩

private theorem langSeven2_forall_pow_eq_one_of_rootDiagUnit
    {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {a : Fin τ.rank → Lˣ} (h : rootDiagUnit τ a ^ p = 1) : ∀ i, a i ^ p = 1 := by
  have key : ∀ n : ℕ, rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]
  have h1 : rootDiagUnit τ (a ^ p) = 1 := by rw [← key p, h]
  have h2 : a ^ p = 1 := rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
  intro i
  have := congrFun h2 i
  simpa using this

private theorem langSeven2_exists_primitiveRoot_seven {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] : ∃ ζ : Lˣ, orderOf ζ = 7 := by
  have h7ne : (7 : L) ≠ 0 := by
    intro h
    have hdvd : (2 : ℕ) ∣ 7 := (CharP.cast_eq_zero_iff L 2 7).mp h
    omega
  haveI : NeZero (7 : L) := ⟨h7ne⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 7 L)
    (by rw [Polynomial.degree_cyclotomic]; norm_num)
  have hζp : IsPrimitiveRoot ζ 7 := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hζunit : IsUnit ζ := hζp.isUnit (by norm_num)
  refine ⟨hζunit.unit, ?_⟩
  have hζpu : IsPrimitiveRoot hζunit.unit 7 :=
    IsPrimitiveRoot.isUnit_unit (by norm_num) hζp
  exact IsPrimitiveRoot.iff_orderOf.mp hζpu

private theorem langSeven2_core
    (hK : LangRatCompKillsP)
    {τ : Tag} {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2)
    {a : ↥(adjointGroup τ K)} (ha7 : a ^ 7 = 1) (ha1 : a ≠ 1)
    {X : Subgroup ↥(adjointGroup τ K)}
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer {a}))
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {S : LangSetup τ L 7} (halg : S.IsAlgebraic)
    (hsyl : ∃ S₀ : Sylow 7 S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ)
    (e : ↥(adjointGroup τ K) ≃* S.Γ)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ 2)
    (hTor : S.D.torus = (fixedCharTuples M Fr).map (rootDiagUnitHom τ L))
    (hFC : ∀ (γ : Fin τ.rank → ℤ), IsRoot τ γ →
      ∃ b' : Fin τ.rank → Lˣ, b' ∈ fixedCharTuples M Fr ∧ (∀ j, b' j ^ 7 = 1) ∧
        rootChar b' γ ≠ 1)
    (hτ : τ = .E7 ∨ τ = .E8) :
    7 ∣ Nat.card X := by
  by_contra hnd
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e', hea, _⟩ := CFSG.StandardType.LangPair.pair_of_sylowSetup S e hsyl ha7 ha7 rfl
  let ι : ↥(adjointGroup τ K) →* ModGL τ L := S.Γ.subtype.comp e'.toMonoidHom
  have hι : Function.Injective ι := (Subgroup.subtype_injective _).comp e'.injective
  have hrange : ι.range = S.Γ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ e'.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hιa_mem : ι a ∈ S.D.torus := hea
  have hmap_mem := hιa_mem
  rw [hTor, Subgroup.mem_map] at hmap_mem
  obtain ⟨a', ha'fix, hmap⟩ := hmap_mem
  have hιa : ι a = rootDiagUnit τ a' := hmap.symm
  have hT : rootDiagUnit τ a' ∈ S.D.torus := by rw [← hιa]; exact hιa_mem
  have hιa7 : (ι a) ^ 7 = 1 := by rw [← map_pow, ha7, map_one]
  have hroot7 : rootDiagUnit τ a' ^ 7 = 1 := by rw [← hιa]; exact hιa7
  have hap : ∀ j, a' j ^ 7 = 1 := langSeven2_forall_pow_eq_one_of_rootDiagUnit hroot7
  have ha1' : rootDiagUnit τ a' ≠ 1 := by
    intro h
    exact ha1 (hι (by rw [hιa, h, map_one]))
  have hp : Nat.Prime 7 := by norm_num
  have hpL : (7 : L) ≠ 0 := by
    intro h
    have hdvd : (2 : ℕ) ∣ 7 := (CharP.cast_eq_zero_iff L 2 7).mp h
    omega
  obtain ⟨i, hqs, hXmap⟩ :=
    langRatComp_of_component S hτ hp hpL ι hι hrange hιa hT hap ha1 hX
  have hndR : ¬ 7 ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a') i) := by
    rw [← hXmap, Subgroup.card_map_of_injective hι]
    exact hnd
  obtain ⟨γ, hγcomp⟩ := langSeven2_exists_mem_componentRoots i
  have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγcomp
  have hγrat : γ ∈ rationalRoots S.ρ (rootCharHom a') i := ⟨0, γ, hγcomp, rfl⟩
  obtain ⟨b', hb'fix, hb'7, hb'ne⟩ := hFC γ hγr
  have hTb : rootDiagUnit τ b' ∈ S.D.torus := by
    rw [hTor]
    exact ⟨b', hb'fix, rfl⟩
  have hkill : rootChar b' γ = 1 :=
    hK τ L 7 S hτ halg 7 hp (by norm_num) a' b' hT hTb hap hb'7 ha1' i hqs hndR γ hγrat
  exact hb'ne hkill

theorem ggExcSevenTwoInput_E7_of_kills
    (hK : LangRatCompKillsP) : GGExcSevenTwoInput .E7 := by
  intro K _ _ _ hKcard a ha7 ha1 X hX
  have hXopen : CFSG.Open.IsComponentOf X (Subgroup.centralizer {a}) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hX
  have hp : Nat.Prime 7 := by norm_num
  have hpK : ¬ 7 ∣ Nat.card K := by rw [hKcard]; norm_num
  have he : orderOf ((Nat.card K : ℕ) : ZMod 7) = 3 := by
    rw [hKcard]
    exact orderOf_eq_prime (p := 3) (by decide) (by decide)
  obtain ⟨L, hL, hLalg, S, hq, halg, hsyl, ⟨e⟩, Fr, hFr, hTor⟩ :=
    langSeven_torus_E7 K hp (le_refl 7) hpK he
  letI : Field L := hL
  letI : IsAlgClosed L := hLalg
  have h2 : (2 : L) = 0 := by
    have hq0 := S.hqpow.2
    rw [hq, hKcard] at hq0
    simpa using hq0
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
  have hFr2 : ∀ c, Fr c = c ^ 2 := by
    intro c
    rw [hFr c, hq, hKcard]
  obtain ⟨ζ, hζ⟩ := langSeven2_exists_primitiveRoot_seven (L := L)
  exact langSeven2_core hK hKcard ha7 ha1 hXopen halg hsyl e hFr2 hTor
    (langSeven_fc_E7 ζ hζ Fr hFr2) (Or.inl rfl)

theorem ggExcSevenTwoInput_E8_of_kills
    (hK : LangRatCompKillsP) : GGExcSevenTwoInput .E8 := by
  intro K _ _ _ hKcard a ha7 ha1 X hX
  have hXopen : CFSG.Open.IsComponentOf X (Subgroup.centralizer {a}) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hX
  have hp : Nat.Prime 7 := by norm_num
  have hpK : ¬ 7 ∣ Nat.card K := by rw [hKcard]; norm_num
  have he : orderOf ((Nat.card K : ℕ) : ZMod 7) = 3 := by
    rw [hKcard]
    exact orderOf_eq_prime (p := 3) (by decide) (by decide)
  obtain ⟨L, hL, hLalg, S, hq, halg, hsyl, ⟨e⟩, Fr, hFr, hTor⟩ :=
    langSeven_torus_E8 K hp (le_refl 7) hpK he
  letI : Field L := hL
  letI : IsAlgClosed L := hLalg
  have h2 : (2 : L) = 0 := by
    have hq0 := S.hqpow.2
    rw [hq, hKcard] at hq0
    simpa using hq0
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
  have hFr2 : ∀ c, Fr c = c ^ 2 := by
    intro c
    rw [hFr c, hq, hKcard]
  obtain ⟨ζ, hζ⟩ := langSeven2_exists_primitiveRoot_seven (L := L)
  exact langSeven2_core hK hKcard ha7 ha1 hXopen halg hsyl e hFr2 hTor
    (langSeven_fc_E8 ζ hζ Fr hFr2) (Or.inr rfl)

theorem ggExcSevenTwoInput_E7_holds
    : GGExcSevenTwoInput .E7 :=
  ggExcSevenTwoInput_E7_of_kills langRatCompKillsP_holds

theorem ggExcSevenTwoInput_E8_holds
    : GGExcSevenTwoInput .E8 :=
  ggExcSevenTwoInput_E8_of_kills langRatCompKillsP_holds

end CFSG.StandardType.LangSeven
