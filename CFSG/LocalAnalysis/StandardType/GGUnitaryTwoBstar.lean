module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdCent
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestOuter
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestMult
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdRZMod
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGQ2CentPsuFiveModel
import CFSG.LocalAnalysis.StandardType.GGLtBstarOfInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCU
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.StandardType.LineU

private theorem le_normalizer_of_unitTwo_mark {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L) :
    Bs ≤ Subgroup.normalizer (L : Set G) :=
  GGInnerDiagOn.le_normalizer <|
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hmark

private theorem exists_unitTwo_raw
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L) :
    p = 3 ∧ ∃ (d : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 1 F d)),
      5 ≤ d ∧ ¬ 3 ∣ d ∧ Nat.card F = (2 ^ 1) ^ 2 ∧
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
        (LargeEvenGUSet (Fin d) F (2 ^ 1)),
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) := by
  classical
  have hsplit : GGInnerDiagOnLabel (fun p lab =>
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) ∧ lab.rank = 3) ∨
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) ∧ lab.rank ≠ 3)) p Bs L :=
    hmark.mono_label fun lab hl => by
      by_cases h3 : lab.rank = 3
      · exact Or.inl ⟨hl, h3⟩
      · exact Or.inr ⟨hl, h3⟩
  rcases GGInnerDiagOnLabel.elim_or hsplit with h3 | hne
  · have h4 : GGInnerDiagOnLabel (fun p lab =>
        (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) p Bs L :=
      h3.mono_label fun lab hl => by
        obtain ⟨⟨⟨hrow, hpq⟩, -, -⟩, hr3⟩ := hl
        refine ⟨?_, hr3, hpq⟩
        rcases hrow with ⟨ht, -⟩ | ⟨ht, -⟩
        · exact Or.inl ht
        · exact Or.inr ht
    exact absurd h4 (not_ggInnerDiagOnLabel_unitary_four hcfg)
  · obtain ⟨-, lab, -, hraw⟩ := hne
    obtain ⟨R, iR, I, F₀, hQ⟩ := largeEvenRawDatum_exists hraw
    letI : Group R := iR
    obtain ⟨-, -, θ₀, hP⟩ := hQ
    have hp : p.Prime := hcfg.tableB_facts.1
    obtain ⟨⟨⟨hrow, hpq⟩, hn1, h3nd⟩, hrne⟩ := hP.1
    obtain ⟨hN0, hact⟩ := hP.2
    rw [hn1] at hpq
    have hp3 : p = 3 := by
      have h3 : p ∣ 3 := by simpa using hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    have htag : lab.tag = .twA := by
      rcases hrow with ⟨ht, -⟩ | ⟨ht, hr3⟩
      · exact ht
      · exact absurd hr3 hrne
    have hrank : 4 ≤ lab.rank := by
      rcases hrow with ⟨-, hr⟩ | ⟨-, hr3⟩
      · omega
      · exact absurd hr3 hrne
    obtain ⟨tag, rank, n⟩ := lab
    change tag = .twA at htag
    change 4 ≤ rank at hrank
    subst htag
    subst hn1
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    obtain ⟨F, iF, iFin, hF, -, -, θ, hpred, -, hact'⟩ := hraw
    exact ⟨hp3, rank + 1, F, iF, iFin, θ, by omega, h3nd, hF, hact'⟩

private theorem UnitTB.exists_pair_units {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) :
    ∃ σ : {ij : Fin d × Fin d // ij.1 ≠ ij.2} → Fin d → Kˣ,
      (∀ ij m, (σ ij m) ^ (2 ^ n + 1) = 1) ∧
      (∀ ij m, (σ ij m) ^ p = 1) ∧
      (∀ ij, ∏ m, σ ij m = 1) ∧
      (∀ (i j : Fin d) (hij : i ≠ j), σ ⟨(i, j), hij⟩ i ≠ σ ⟨(i, j), hij⟩ j) := by
  classical
  obtain ⟨ζ, hζ⟩ := IOneUDvdR.exists_isPrimitiveRoot_of_dvd (K := K) hp
    (TableBUE.dvd_card_sub_one hK hpq)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζq : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hζ.pow_eq_one, one_pow]
  let uζ : Kˣ := Units.mk0 ζ hζ0
  have huζq : uζ ^ (2 ^ n + 1) = 1 := Units.ext (by simpa [uζ] using hζq)
  have huζp : uζ ^ p = 1 := Units.ext (by simpa [uζ] using hζ.pow_eq_one)
  let σ : {ij : Fin d × Fin d // ij.1 ≠ ij.2} → Fin d → Kˣ := fun ij =>
    Pi.mulSingle ij.1.1 uζ * Pi.mulSingle ij.1.2 (uζ⁻¹)
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · intro ij m
    simp only [σ, Pi.mul_apply, mul_pow, Pi.mulSingle_apply]
    split_ifs <;> simp [huζq, inv_pow]
  · intro ij m
    simp only [σ, Pi.mul_apply, mul_pow, Pi.mulSingle_apply]
    split_ifs <;> simp [huζp, inv_pow]
  · intro ij
    simp only [σ, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
    simp
  · intro i j hij
    let ij : {ij : Fin d × Fin d // ij.1 ≠ ij.2} := ⟨(i, j), hij⟩
    have hi : σ ij i = uζ := by simp [σ, ij, hij]
    have hj : σ ij j = uζ⁻¹ := by simp [σ, ij, Ne.symm hij]
    rw [hi, hj]
    intro h
    exact hζinv (congrArg Units.val h)

private theorem UnitTB.exists_diagPair_diagSU {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hfield : UnitaryFieldData 2 n K) :
    ∃ (Dfun : {ij : Fin d × Fin d // ij.1 ≠ ij.2} → ↥(unitarySU 2 n K d))
      (u : {ij : Fin d × Fin d // ij.1 ≠ ij.2} → Fin d → K),
      (∀ ij, ((Dfun ij : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (u ij)) ∧
      (∀ ij m, u ij m ^ p = 1) ∧
      (∀ (i j : Fin d) (hij : i ≠ j), ∃ σ : Fin d → Kˣ,
        ((Dfun ⟨(i, j), hij⟩ : GL (Fin d) K) = diagHom d σ ∧ σ i ≠ σ j)) := by
  obtain ⟨σ, hσq, hσp, hσprod, hdist⟩ :=
    UnitTB.exists_pair_units (n := n) (d := d) (p := p) hK hp hp2 hpq
  refine ⟨fun ij => ⟨diagHom d (σ ij),
      TableBUE.diagHom_mem_unitarySU (h := hfield) (hσq ij) (hσprod ij)⟩,
    fun ij m => (σ ij m : K), ?_, ?_, ?_⟩
  · intro ij
    change ((diagHom d (σ ij) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
    rw [coe_diagHom]
  · intro ij m
    exact congrArg Units.val (hσp ij m)
  · intro i j hij
    exact ⟨σ ⟨(i, j), hij⟩, rfl, hdist i j hij⟩

private theorem UnitTB.isPGroup_map_comap_proj {G : Type} [Group G]
    {K : Type} [Field K] [Finite K] {n d : ℕ} {L : Subgroup G}
    {ψ : ↥(unitarySU 2 n K d) →* ↥L} (hM : UnitTB.Model ψ) (hd : 0 < d)
    {U : Subgroup G} (hU : IsPGroup 2 U) :
    IsPGroup 2 (((U.subgroupOf L).comap ψ).map
      (LargeEvenProjMk (unitarySU 2 n K d))) := by
  rintro ⟨_, s, hs, rfl⟩
  obtain ⟨k, hk⟩ := hU ⟨_, Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hs)⟩
  have h1 : ψ (s ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by simpa using congrArg Subtype.val hk)
  refine ⟨k, Subtype.ext ?_⟩
  change LargeEvenProjMk (unitarySU 2 n K d) s ^ 2 ^ k = 1
  rw [← map_pow]
  exact (UnitTB.projMk_eq_one_iff hd).mpr (hM.ker _ h1)

private theorem UnitTB.mem_normalizer_comap {G : Type} [Group G]
    {Bs L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] {n d : ℕ} {ψ : ↥(unitarySU 2 n K d) →* ↥L}
    {U : Subgroup G} (hBsU : Bs ≤ Subgroup.normalizer (U : Set G))
    {x : ↥(unitarySU 2 n K d)} (hx : MulAut.conj (ψ x) ∈ (ggGamma L hN).range) :
    x ∈ Subgroup.normalizer ((U.subgroupOf L).comap ψ) := by
  have hstep : ∀ (y : ↥(unitarySU 2 n K d)),
      MulAut.conj (ψ y) ∈ (ggGamma L hN).range →
      ∀ s ∈ (U.subgroupOf L).comap ψ, y * s * y⁻¹ ∈ (U.subgroupOf L).comap ψ := by
    intro y hy s hs
    rw [Subgroup.mem_comap] at hs ⊢
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    obtain ⟨b, hb⟩ := hy
    have hbU : b * (ψ s : G) * (b : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hBsU b.2) (ψ s : G)).mp hs
    have hψ : ((ψ (y * s * y⁻¹) : ↥L) : G) = (ψ y : G) * (ψ s : G) * (ψ y : G)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have hgg : ((ggGamma L hN b) ⟨(ψ s : G), (ψ s).2⟩ : G) = b * (ψ s : G) * (b : G)⁻¹ :=
      ggGamma_coe L hN b ⟨(ψ s : G), (ψ s).2⟩
    have hconj := congrArg (fun a : MulAut ↥L =>
      ((a ⟨(ψ s : G), (ψ s).2⟩ : ↥L) : G)) hb
    simp only [hgg, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hconj
    rw [hψ, ← hconj]
    exact hbU
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact hstep x hx s
  · intro hs
    have hinv : MulAut.conj (ψ x⁻¹) ∈ (ggGamma L hN).range := by
      rw [map_inv, map_inv]
      exact Subgroup.inv_mem _ hx
    have h1 := hstep x⁻¹ hinv (x * s * x⁻¹) hs
    simpa [mul_assoc] using h1

private theorem UnitTB.le_centralizer_of_proj_eq_bot {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] {n d : ℕ} {L : Subgroup G}
    {ψ : ↥(unitarySU 2 n K d) →* ↥L} (hM : UnitTB.Model ψ) (hd : 0 < d)
    {U : Subgroup G} (hUL : U ≤ L)
    (hVbot : ((U.subgroupOf L).comap ψ).map
      (LargeEvenProjMk (unitarySU 2 n K d)) = ⊥) :
    U ≤ Subgroup.centralizer (L : Set G) := by
  let π := LargeEvenProjMk (unitarySU 2 n K d)
  let Ũ : Subgroup ↥(unitarySU 2 n K d) := (U.subgroupOf L).comap ψ
  let V : Subgroup (LargeEvenProj (unitarySU 2 n K d)) := Ũ.map π
  change V = ⊥ at hVbot
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨s, hs⟩ := hM.surj ⟨u, hUL hu⟩
  obtain ⟨t, ht⟩ := hM.surj ⟨y, hy⟩
  have hsŨ : s ∈ Ũ := by
    rw [Subgroup.mem_comap, hs]
    exact (Subgroup.mem_subgroupOf).mpr hu
  have hπs : π s = 1 := by
    have hmem : π s ∈ V := Subgroup.mem_map.mpr ⟨s, hsŨ, rfl⟩
    rwa [hVbot, Subgroup.mem_bot] at hmem
  obtain ⟨c, hc⟩ := (UnitTB.projMk_eq_one_iff hd).mp hπs
  have hdet : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 :=
    ((mem_unitarySU_iff hM.field).mp s.2).1
  have hcd : c ^ d = 1 := by
    rw [hc, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : d ≠ 0)] at hcd
    exact zero_ne_one hcd
  have hscalar : (s : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hc
  have hcomm : ∀ z : ↥(unitarySU 2 n K d), s * z = z * s := by
    intro z
    have h1 : Commute (z : GL (Fin d) K) (s : GL (Fin d) K) := by
      rw [hscalar]
      exact commute_scalar (Units.mk0 c hc0) (z : GL (Fin d) K)
    exact Subtype.ext h1.eq.symm
  have hsu : (ψ s : G) = u := congrArg Subtype.val hs
  have hty : (ψ t : G) = y := congrArg Subtype.val ht
  rw [← hsu, ← hty]
  calc (ψ t : G) * (ψ s : G) = ((ψ (t * s) : ↥L) : G) := by rw [map_mul]; rfl
    _ = ((ψ (s * t) : ↥L) : G) := by rw [← hcomm t]
    _ = (ψ s : G) * (ψ t : G) := by rw [map_mul]; rfl

private theorem UnitTB.le_centralizer_of_le_one {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] {n d : ℕ} {L : Subgroup G}
    {ψ : ↥(unitarySU 2 n K d) →* ↥L} (hM : UnitTB.Model ψ) (hd1 : d ≤ 1)
    {U : Subgroup G} :
    U ≤ Subgroup.centralizer (L : Set G) := by
  haveI : Subsingleton ↥(unitarySU 2 n K d) :=
    CFSG.ComponentClassification.Burgoyne.C.subsingleton_statedSU_of_le_one hM.field hd1
  have hbot : L = ⊥ := by
    rw [eq_bot_iff]
    rintro l hl
    obtain ⟨s, hs⟩ := hM.surj ⟨l, hl⟩
    have hval : (ψ s : G) = l := by simpa using congrArg Subtype.val hs
    rw [Subgroup.mem_bot, ← hval, Subsingleton.elim s 1, map_one]
    rfl
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hbot] at hy
  have hy1 : y = 1 := Subgroup.mem_bot.mp hy
  rw [hy1, mul_one, one_mul]

theorem UnitTB.le_centralizer_of_isPGroup_two {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {ψ : ↥(unitarySU 2 n K d) →* ↥L} (hM : UnitTB.Model ψ)
    (hsc : GGTorusSelfCent p (ggGamma L hN).range)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, LineU.ActsDiagU ψ a t)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUL : U ≤ L)
    (hBsU : Bs ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Subgroup.centralizer (L : Set G) := by
  classical
  by_cases hd1 : d ≤ 1
  · exact UnitTB.le_centralizer_of_le_one hM hd1
  push Not at hd1
  have hdpos : 0 < d := by omega
  obtain ⟨Dfun, u, hDmat, hσp, hsep⟩ :=
    UnitTB.exists_diagPair_diagSU (n := n) (d := d) (p := p) hK hp hp2 hpq hM.field
  have hconj_spec : ∀ ij, MulAut.conj (ψ (Dfun ij)) ∈ (ggGamma L hN).range :=
    fun ij => UnitTB.conj_mem_of_selfCent hsc hdiag (hDmat ij) (hσp ij)
  let π := LargeEvenProjMk (unitarySU 2 n K d)
  let Ũ : Subgroup ↥(unitarySU 2 n K d) := (U.subgroupOf L).comap ψ
  let V : Subgroup (LargeEvenProj (unitarySU 2 n K d)) := Ũ.map π
  have hDnorm : ∀ ij, Dfun ij ∈ Subgroup.normalizer (Ũ : Set ↥(unitarySU 2 n K d)) :=
    fun ij => UnitTB.mem_normalizer_comap hN hBsU (hconj_spec ij)
  have hseparate : ∀ i j : Fin d, i ≠ j → ∃ x ∈ Subgroup.closure (Set.range Dfun),
      ∃ σ' : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ' ∧ σ' i ≠ σ' j := by
    intro i j hij
    obtain ⟨σ', hD, hne⟩ := hsep i j hij
    exact ⟨Dfun ⟨(i, j), hij⟩, Subgroup.subset_closure ⟨⟨(i, j), hij⟩, rfl⟩, σ', hD, hne⟩
  have hV2 : IsPGroup 2 V := UnitTB.isPGroup_map_comap_proj hM hdpos hU
  have hAV : (Subgroup.closure (Set.range Dfun)).map π ≤ Subgroup.normalizer (V : Set _) := by
    have hAnorm : Subgroup.closure (Set.range Dfun) ≤
        Subgroup.normalizer (Ũ : Set ↥(unitarySU 2 n K d)) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨ij, rfl⟩
      exact hDnorm ij
    exact (Subgroup.map_mono hAnorm).trans (Subgroup.le_normalizer_map π)
  have hVbot : V = ⊥ :=
    TableBUR.eq_bot_of_normalizes_twoSubgroup hM.field hseparate hV2 hAV
  exact UnitTB.le_centralizer_of_proj_eq_bot hM hdpos hUL hVbot

namespace UnitTB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.Assembly

private theorem ker_eq_bot_of_model_four {K : Type} [Field K] [Finite K] {d : ℕ}
    {L' : Type} [Group L'] {ψ : ↥(unitarySU 2 1 K d) →* L'} (hM : Model ψ)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 3 ≤ d) (hd3 : ¬ 3 ∣ d) :
    ψ.ker = ⊥ := by
  classical
  have hSUeq : LargeEvenSUGroup (Fin d) K (2 ^ 1) = unitarySU 2 1 K d := by
    rw [largeEvenSUGroup_eq_statedSU, unitarySU, pow_one]
  have hbot : (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 1 K d) = ⊥ := by
    rw [← hSUeq]
    exact TableBUR.suScalars_eq_bot_four (d := d) hK hd3
  rw [eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  obtain ⟨c, hc⟩ := hM.ker g hg
  have hdet : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 :=
    ((mem_unitarySU_iff hM.field).mp g.2).1
  have hcd : c ^ d = 1 := by
    rw [hc, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : d ≠ 0)] at hcd
    exact zero_ne_one hcd
  have hmem : g ∈ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 1 K d) := by
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hc.symm
  rwa [hbot, Subgroup.mem_bot] at hmem

private theorem center_eq_bot_of_SU_four {K : Type} [Field K] [Finite K] {d : ℕ}
    {L' : Type} [Group L'] {ψ : ↥(unitarySU 2 1 K d) →* L'} (hM : Model ψ)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd3 : ¬ 3 ∣ d) :
    Subgroup.center ↥(unitarySU 2 1 K d) = ⊥ := by
  classical
  have hSUeq : LargeEvenSUGroup (Fin d) K (2 ^ 1) = unitarySU 2 1 K d := by
    rw [largeEvenSUGroup_eq_statedSU, unitarySU, pow_one]
  have hbot : (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 1 K d) = ⊥ := by
    rw [← hSUeq]
    exact TableBUR.suScalars_eq_bot_four (d := d) hK hd3
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hcomm : ∀ g ∈ unitarySU 2 1 K d,
      (z : GL (Fin d) K) * g = g * (z : GL (Fin d) K) := by
    intro g hg
    simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)).symm
  obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_commute hM.field Nat.prime_three
    (by norm_num : 3 ∣ 2 ^ 1 + 1) hcomm
  have hmem : z ∈ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 1 K d) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨c, hc⟩
  rwa [hbot, Subgroup.mem_bot] at hmem

theorem center_eq_bot_of_model_four {K : Type} [Field K] [Finite K] {d : ℕ}
    {L' : Type} [Group L'] {ψ : ↥(unitarySU 2 1 K d) →* L'} (hM : Model ψ)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 3 ≤ d) (hd3 : ¬ 3 ∣ d) :
    Subgroup.center L' = ⊥ := by
  classical
  have hker : ψ.ker = ⊥ := ker_eq_bot_of_model_four hM hK hd hd3
  have hZ : Subgroup.center ↥(unitarySU 2 1 K d) = ⊥ := center_eq_bot_of_SU_four hM hK hd3
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨g, rfl⟩ := hM.surj z
  have hg : g ∈ Subgroup.center ↥(unitarySU 2 1 K d) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hz (ψ t)
  rw [hZ, Subgroup.mem_bot] at hg
  rw [hg, map_one]

end UnitTB

theorem GGConfig.exists_unitaryModel_of_unitTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    p = 3 ∧ ∃ (d : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (ψ : ↥(unitarySU 2 1 F d) →* ↥L),
      5 ≤ d ∧ ¬ 3 ∣ d ∧ Nat.card F = (2 ^ 1) ^ 2 ∧ UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → F, LineU.ActsDiagU ψ a t := by
  obtain ⟨rfl, d, F, iF, iFin, θ, hd5, hd3, hF, hact⟩ := exists_unitTwo_raw hcfg hmark
  letI : Field F := iF
  letI : Finite F := iFin
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by rintro ⟨rfl, -⟩; omega
  have h61 : (d, 1) ≠ (6, 1) := by rintro ⟨rfl, -⟩; exact hd3 (by norm_num)
  have hcov := LineU.unitaryUniversalCover_holds 1 d F hF hd5 h61
  have hlift := ggTorusLift_unitary hF (le_refl 1) (by omega : 3 ≤ d) hdq Nat.prime_three hpq
  have hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
          (LargeEvenGUSet (Fin d) F (2 ^ 1)) := by
    intro b hb
    obtain ⟨φ, hφ, hind⟩ := hact b⁻¹ (Subgroup.inv_mem _ hb)
    have hφeq : φ = ggLAut L θ ⟨b, hN hb⟩ := by
      have h := eq_ggLAut_of_induces L θ (hN (Subgroup.inv_mem _ hb)) hind
      simpa using h
    rwa [← hφeq]
  obtain ⟨hψ, hker, _, hA, hAI, -, -, -⟩ :=
    ggTorusTBGroup_of_L hcfg hmark.1 θ hN hBsI hlift
  obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
    LineU.exists_diagModel_coprime hF (le_refl 1) (by omega : 3 ≤ d) Nat.prime_three hpq hd3
      hcov hψ hker hmark.1 hA hAI
  exact ⟨rfl, d, F, iF, iFin, ψ, hd5, hd3, hF,
    ⟨TableBU.unitaryFieldData_of_card hF (le_refl 1), hψs, hψker⟩, hdiag⟩

theorem GGConfig.le_centralizer_of_isPGroup_two_unitTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUL : U ≤ L)
    (hBsU : Bs ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Subgroup.centralizer (L : Set G) := by
  have hN := le_normalizer_of_unitTwo_mark hmark
  obtain ⟨hp3, d, F, iF, iFin, ψ, hd5, hd3, hF, hM, hdiag⟩ :=
    hcfg.exists_unitaryModel_of_unitTwo hmark hN
  subst hp3
  exact UnitTB.le_centralizer_of_isPGroup_two hN hF Nat.prime_three (by norm_num)
    (by norm_num) hM (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2) hdiag hU hUL hBsU

theorem GGConfig.exists_inner_conj_of_unitTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L) :
    ∀ b ∈ Bs, ∃ a : ↥L, ∀ y ∈ L, b⁻¹ * y * b = (a : G)⁻¹ * y * a := by
  have hN := le_normalizer_of_unitTwo_mark hmark
  obtain ⟨hp3, d, F, iF, iFin, θ, hd5, hd3, hF, hact⟩ := exists_unitTwo_raw hcfg hmark
  subst hp3
  letI : Field F := iF
  letI : Finite F := iFin
  intro b hb
  obtain ⟨φ, hφ, hind⟩ := hact b hb
  have hφeq : φ = ggLAut L θ ⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem (hN hb)⟩ :=
    eq_ggLAut_of_induces L θ (hN hb) hind
  have hbp : (b : G) ^ 3 = 1 := hcfg.2.1.2.1.2 b hb
  have hb3 : (⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem (hN hb)⟩ :
      Subgroup.normalizer (L : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    show (b : G)⁻¹ ^ 3 = 1
    rw [inv_pow, hbp, inv_one]
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφeq, ← map_pow, hb3, map_one]
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by rintro ⟨rfl, -⟩; omega
  obtain ⟨r, hr⟩ := TableBUE.mem_range_conj_of_pow_eq_one
    (h := TableBU.unitaryFieldData_of_card hF (le_refl 1)) (K := F) (n := 1) (d := d) (p := 3)
    hF (by omega : 3 ≤ d) hdq Nat.prime_three (by norm_num : 3 ∣ 2 ^ 1 + 1) hd3 hφ hφ3
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_conj_eq_of_marked_conj (hN hb)
    (Group.IsPerfect.mk hmark.1) (r := r) (by rw [hr]; exact hind)

theorem GGConfig.center_eq_bot_of_unitaryTwo
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L) :
    Subgroup.center ↥L = ⊥ := by
  have hN := le_normalizer_of_unitTwo_mark hmark
  obtain ⟨-, d, F, iF, iFin, ψ, hd5, hd3, hF, hM, -⟩ :=
    hcfg.exists_unitaryModel_of_unitTwo hmark hN
  letI : Field F := iF
  letI : Finite F := iFin
  exact UnitTB.center_eq_bot_of_model_four hM hF (by omega : 3 ≤ d) hd3

theorem GGConfig.lt_bstar_of_unitaryTwo
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) p Bs L) :
    B < Bs := by
  have hN := le_normalizer_of_unitTwo_mark hmark
  have hp3 : p = 3 := (hcfg.exists_unitaryModel_of_unitTwo hmark hN).1
  subst hp3
  refine hcfg.lt_bstar_of_inner ?_ ?_ ?_
  · rw [center_eq_bot_of_unitaryTwo hcfg hmark, Subgroup.card_bot]
    exact Nat.coprime_one_left 3
  · exact hcfg.exists_inner_conj_of_unitTwo hmark
  · intro U hUL hU hBsU
    exact hcfg.le_centralizer_of_isPGroup_two_unitTwo hmark hU hUL hBsU

end CFSG.StandardType

end
