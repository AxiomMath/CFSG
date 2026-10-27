module

public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec17.PropUCover
public import CFSG.GroupTheory.SteinbergCBFTHall
public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ J : Subgroup G}

theorem card_map_inf_eq_nine
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2)) :
    (∀ x ∈ ((A ⊓ L).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)), x ^ 3 = 1) ∧
      Nat.card ↥(((A ⊓ L).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) = 9 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hAL9, -⟩ := Sec14.j2_point_facts h.toSec13Data hJ
  let Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀
  let π : ↥Y₀ →* ↥Y₀ ⧸ Q := QuotientGroup.mk' Q
  let H : Subgroup ↥Y₀ := (A ⊓ L).subgroupOf Y₀
  have hALY : A ⊓ L ≤ Y₀ := inf_le_right.trans h.le_y0
  have hcardH : Nat.card ↥H = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALY).toEquiv, hAL9]
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)
  obtain ⟨n, hn⟩ := hQ2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥Q) := by
    rw [hcardH, hn]
    exact Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 9 2)
  have hker : H ⊓ π.ker = ⊥ := by
    rw [show π.ker = Q from QuotientGroup.ker_mk' Q]
    exact Subgroup.inf_eq_bot_of_coprime hcop
  constructor
  · intro x hx
    obtain ⟨y, hyH, rfl⟩ := hx
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      have hyA : ((y : ↥Y₀) : G) ∈ A := (Subgroup.mem_subgroupOf.mp hyH).1
      simpa using h.isE27.1.2 ((y : ↥Y₀) : G) hyA
    rw [← map_pow, hy3, map_one]
  · rw [← hcardH]
    exact CFSG.card_map_eq_card_of_inf_ker_eq_bot π hker

theorem commutatorElement_mem_pCoreOf_y0 (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) : ∀ y ∈ Y₀, ⁅y, c⁆ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  set P : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hP
  have hPle : P ≤ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀
  have hPN : Y₀ ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := h.le_y0.trans hPN
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hAY : A ≤ Subgroup.normalizer (Y₀ : Set G) := h.mem_y0Star.prop.1.1.2
  have hcP : c ∈ Subgroup.normalizer (P : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀) (hAY hcA)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  have hset : (Y₀ : Set G) = (L : Set G) * (P : Set G) := by
    rw [hY, Subgroup.coe_mul_of_left_le_normalizer_right L P hLP]
  intro y hy
  have hy' : y ∈ (L : Set G) * (P : Set G) := hset ▸ hy
  obtain ⟨l, hlL, p, hpP, rfl⟩ := hy'
  have hpcP : ⁅p, c⁆ ∈ P := by
    have hcp : c * p⁻¹ * c⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hcP p⁻¹).mp (P.inv_mem hpP)
    rw [commutatorElement_def,
      show p * c * p⁻¹ * c⁻¹ = p * (c * p⁻¹ * c⁻¹) by group]
    exact P.mul_mem hpP hcp
  have hconj : l * ⁅p, c⁆ * l⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hLP hlL) _).mp hpcP
  have hlc : ⁅l, c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc hlL)
  rw [commutatorElement_mul_left_eq_conj_mul, hlc, mul_one]
  exact hconj

theorem isPerfect_map_star (hJY : J ≤ Y₀) (hJperf : Group.IsPerfect ↥J) :
    Group.IsPerfect ↥((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) := by
  haveI : Group.IsPerfect ↥(J.subgroupOf Y₀) := by
    haveI := hJperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJY).symm.surjective
  exact Group.IsPerfect.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))

theorem nonempty_map_star_quot_a5 (hJY : J ≤ Y₀)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5))) :
    Nonempty (↥((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) ⧸
      CFSG.pCore 2 ↥((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) ≃*
        alternatingGroup (Fin 5)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀ with hQ
  set JY : Subgroup ↥Y₀ := J.subgroupOf Y₀ with hJYdef
  set π : ↥Y₀ →* ↥Y₀ ⧸ Q := QuotientGroup.mk' Q with hπ
  set Jstar : Subgroup (↥Y₀ ⧸ Q) := JY.map π with hJstar
  set eJY : ↥JY ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJY with heJY
  set ψ : ↥JY →* ↥Jstar := π.subgroupMap JY with hψ
  set φ : ↥J →* ↥Jstar := ψ.comp eJY.symm.toMonoidHom with hφ
  have hψsurj : Function.Surjective ψ := MonoidHom.subgroupMap_surjective π JY
  have hφsurj : Function.Surjective φ := hψsurj.comp eJY.symm.surjective
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)
  have hψker : ψ.ker = Q.subgroupOf JY := by
    rw [hψ, Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have hψker2 : IsPGroup 2 ψ.ker := by
    rw [hψker]
    exact hQ2.comap_subtype
  have hφker : φ.ker = ψ.ker.comap eJY.symm.toMonoidHom := by
    rw [hφ, MonoidHom.comap_ker]
  have hφker2 : IsPGroup 2 φ.ker := by
    rw [hφker]
    exact hψker2.comap_of_injective eJY.symm.toMonoidHom eJY.symm.injective
  have hcomap_le : CFSG.pCore 2 ↥J ≤ (CFSG.pCore 2 ↥Jstar).comap φ := by
    apply Subgroup.map_le_iff_le_comap.mp
    exact le_sSup ⟨Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := ↥J)) φ hφsurj,
      IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) φ⟩
  have hcomap_ge : (CFSG.pCore 2 ↥Jstar).comap φ ≤ CFSG.pCore 2 ↥J := by
    exact le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥Jstar)).comap φ,
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Jstar)).comap_of_ker_isPGroup φ hφker2⟩
  have hcomap_eq : (CFSG.pCore 2 ↥Jstar).comap φ = CFSG.pCore 2 ↥J :=
    le_antisymm hcomap_ge hcomap_le
  let θ : ↥J →* ↥Jstar ⧸ CFSG.pCore 2 ↥Jstar :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Jstar)).comp φ
  have hθsurj : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp hφsurj
  have hθker : θ.ker = CFSG.pCore 2 ↥J := by
    rw [show θ = (QuotientGroup.mk' (CFSG.pCore 2 ↥Jstar)).comp φ from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap_eq]
  have e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃*
      (↥Jstar ⧸ CFSG.pCore 2 ↥Jstar) :=
    (QuotientGroup.quotientMulEquivOfEq hθker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)
  obtain ⟨eA⟩ := hJA5
  exact ⟨e.symm.trans eA⟩

theorem map_inf_le_normalizer_star (hJY : J ≤ Y₀)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    ((A ⊓ L).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) ≤
      Subgroup.normalizer
        (((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
  have hHnorm : (A ⊓ L).subgroupOf Y₀ ≤
      Subgroup.normalizer (J.subgroupOf Y₀ : Set ↥Y₀) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJY]
    exact Subgroup.subgroupOf_mono _ (inf_le_left.trans hAJ)
  exact (Subgroup.map_mono hHnorm).trans
    (Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)))

theorem ks166J2A5_at_star
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    CFSG.pCore 2 ↥((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) = ⊥ ∧
    Group.IsSolvable ↥(Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) ∧
    (∀ α : MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀),
      (∀ k ∈ ((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))), α k = k) →
      ∃ g ∈ Subgroup.centralizer
        ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)),
        α = MulAut.conj g) ∧
    (∀ U : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀),
      U ≤ Subgroup.centralizer
        ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) →
      IsPGroup 2 U →
      ((A ⊓ L).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) ≤
        Subgroup.normalizer (U : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) →
      U = ⊥ ∨ U = CFSG.Open.pCoreOf 2 (Subgroup.centralizer
        ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)))) ∧
    Nonempty (CFSG.Open.pCoreOf 2 (Subgroup.centralizer
        ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    Nonempty (Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer
          ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
            Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀ with hQ
  set JY : Subgroup ↥Y₀ := J.subgroupOf Y₀ with hJYdef
  set π : ↥Y₀ →* ↥Y₀ ⧸ Q := QuotientGroup.mk' Q with hπ
  set Jstar : Subgroup (↥Y₀ ⧸ Q) := JY.map π with hJstar
  set E : Subgroup (↥Y₀ ⧸ Q) := ((A ⊓ L).subgroupOf Y₀).map π with hE
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    CFSG.RankThree.PartTwo.Sec17.PropU.nonempty_quotient_J2 h hJ hY
  have hEstar := card_map_inf_eq_nine h hJ
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    simpa only [E, π, Q] using hEstar.1
  have hEcard : Nat.card E = 9 := by
    simpa only [E, π, Q] using hEstar.2
  have hEnorm : E ≤ Subgroup.normalizer (Jstar : Set (↥Y₀ ⧸ Q)) := by
    simpa only [E, Jstar, π, JY] using map_inf_le_normalizer_star hJY hAJ
  have hKstar := hK (↥Y₀ ⧸ Q) hYJ Jstar (isPerfect_map_star hJY hJperf)
    (nonempty_map_star_quot_a5 hJY hJA5) E hEnorm hE3 hEcard
  simpa only [Jstar, JY, E, π, Q] using hKstar

private theorem pCoreOf_le_pCoreOf_of_pCore_star_eq_bot (hJY : J ≤ Y₀)
    (hpc : CFSG.pCore 2 ↥((J.subgroupOf Y₀).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) = ⊥) :
    CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 Y₀ := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀ with hQ
  set JY : Subgroup ↥Y₀ := J.subgroupOf Y₀ with hJYdef
  set π : ↥Y₀ →* ↥Y₀ ⧸ Q := QuotientGroup.mk' Q with hπ
  set Jstar : Subgroup (↥Y₀ ⧸ Q) := JY.map π with hJstar
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)
  have hLHS : ((CFSG.pCore 2 JY).map JY.subtype).map π = ⊥ := by
    rw [CFSG.GroupTheory.FT63ChII.map_pCore_map_subtype (p := 2) π JY]
    · rw [show JY.map π = Jstar from rfl, hpc, Subgroup.map_bot]
    · rw [show π.ker = Q from QuotientGroup.ker_mk' Q]
      exact hQ2.to_le inf_le_left
  have hPleQ : (CFSG.pCore 2 JY).map JY.subtype ≤ Q := by
    have h := (Subgroup.map_eq_bot_iff (f := π)
      (H := (CFSG.pCore 2 JY).map JY.subtype)).mp hLHS
    rwa [show π.ker = Q from QuotientGroup.ker_mk' Q] at h
  have hmapJY : (JY.map Y₀.subtype) = J := by
    rw [hJYdef]
    exact Subgroup.map_subgroupOf_eq_of_le hJY
  have hPcoreJ : CFSG.Open.pCoreOf 2 J =
      ((CFSG.pCore 2 JY).map JY.subtype).map Y₀.subtype := by
    rw [CFSG.Open.pCoreOf, ← hmapJY]
    exact (CFSG.GroupTheory.FT63ChII.map_pCore_map_subtype (p := 2) Y₀.subtype JY (by
      rw [Subgroup.ker_subtype, bot_inf_eq]
      exact IsPGroup.of_bot)).symm
  calc CFSG.Open.pCoreOf 2 J
      = ((CFSG.pCore 2 JY).map JY.subtype).map Y₀.subtype := hPcoreJ
    _ ≤ Q.map Y₀.subtype := Subgroup.map_mono hPleQ
    _ = CFSG.Open.pCoreOf 2 Y₀ := rfl

theorem pCoreOf_le_pCoreOf_y0
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 Y₀ := by
  exact pCoreOf_le_pCoreOf_of_pCore_star_eq_bot hJY
    (ks166J2A5_at_star h hJ h1523 hK hJY hJperf hJA5 hAJ).1

theorem isSolvable_centralizer_star
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    Group.IsSolvable ↥(Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) := by
  exact (ks166J2A5_at_star h hJ h1523 hK hJY hJperf hJA5 hAJ).2.1

end CFSG.RankThree.PartTwo.Sec16.Ctr166
