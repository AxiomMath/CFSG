module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1Perf
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanProjection
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.Quasithin.Vol2.Ch4Sec4L443E4Inner
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotNeighbourStandard
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.Timmesfeld.Transvection.PresSp
import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGF4Absorption
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanMemberOut
import CFSG.Quasithin.Vol2.Ch4Sec4L443E3Conj
import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
import CFSG.Quasithin.Vol2.Ch4Sec4W446

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.Quasithin

section Pure

variable {G : Type} [Group G] [Finite G]

private theorem outSolvable_congr' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : OutSolvable A) : OutSolvable B := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  let φ : MulAut A →* MulAut B := (MulAut.congr e).toMonoidHom
  have hφ : Function.Surjective φ := (MulAut.congr e).surjective
  rw [← map_derivedSeries_eq hφ n]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := hn hy
  refine ⟨e a, ?_⟩
  ext b
  simp [φ, MulAut.congr_apply]

theorem ggF4QGeFour_perfectCore_le_of_normalizer {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (hOut : OutSolvable ↥X) (hBsX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hN : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ⊔ Subgroup.centralizer (X : Set G) := by
  set P := ggRankOnePerf Bs r
  have hPle : P ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) := perfectCore_le _
  have hPP : ⁅P, P⁆ = P := perfectCore_perfect _
  have hPX : P ≤ X ⊔ Subgroup.centralizer (X : Set G) :=
    CFSG.Quasithin.H13.Ch4.E443.le_sup_centralizer_of_outSolvable hOut (hPle.trans hN) hPP
  have hHN : ggHyperplane Bs r ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.map_subtype_le _).trans hBsX
  exact (SecFiveRk1C.le_perfectCore_sup_centralizer inf_le_left hPP
    (SecFiveRk1C.le_inf_centralizer_sup_of_perfect hHN hPle hPP hPX)).trans
    (sup_le_sup_right (SecFiveRk1C.perfectCore_le_ggOTwoPrime _) _)

omit [Finite G] in
theorem mem_ggHyperplane_of_mem_ggAutomizer {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer X Bs) {z : G} (hzB : z ∈ Bs)
    (hz : X ≤ Subgroup.centralizer ({z} : Set G)) : z ∈ ggHyperplane Bs r := by
  obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp hr
  refine ⟨⟨z, hzB⟩, ?_, rfl⟩
  apply Subtype.ext
  change ((r ⟨z, hzB⟩ : ↥Bs) : G) = z
  rw [hg ⟨z, hzB⟩]
  have hgz : g * z = z * g := (Subgroup.mem_centralizer_iff.mp (hz hgX) z rfl).symm
  change g * z * g⁻¹ = z
  rw [hgz, mul_inv_cancel_right]

omit [Finite G] in
theorem centralizer_inf_le_centralizer_bstar {p : ℕ} (hp : Odd p) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsX : Bs ≤ Subgroup.normalizer (X : Set G)) {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer X Bs) (hr2 : r ^ 2 = 1) :
    Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp hr
  have hab : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro c hc
  obtain ⟨hcX, hcH⟩ := Subgroup.mem_inf.mp hc
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hrr : r (r ⟨b, hb⟩) = ⟨b, hb⟩ := by
    rw [← MulAut.mul_apply, ← sq, hr2, MulAut.one_apply]
  have hH : b * ((r ⟨b, hb⟩ : ↥Bs) : G) ∈ ggHyperplane Bs r := by
    refine ⟨⟨b, hb⟩ * r ⟨b, hb⟩, ?_, rfl⟩
    apply Subtype.ext
    change ((r (⟨b, hb⟩ * r ⟨b, hb⟩) : ↥Bs) : G) = b * ((r ⟨b, hb⟩ : ↥Bs) : G)
    rw [map_mul, hrr, Subgroup.coe_mul]
    exact hab _ (r ⟨b, hb⟩).2 _ hb
  have hdX : b * ((r ⟨b, hb⟩ : ↥Bs) : G)⁻¹ ∈ X := by
    rw [hg ⟨b, hb⟩]
    have h1 : b * g * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hBsX hb) g).mp hgX
    have h2 : b * (g * b * g⁻¹)⁻¹ = b * g * b⁻¹ * g⁻¹ := by group
    rw [h2]
    exact X.mul_mem h1 (X.inv_mem hgX)
  have hsq : b * ((r ⟨b, hb⟩ : ↥Bs) : G) * (b * ((r ⟨b, hb⟩ : ↥Bs) : G)⁻¹) = b ^ 2 := by
    rw [mul_assoc, ← mul_assoc ((r ⟨b, hb⟩ : ↥Bs) : G), hab _ (r ⟨b, hb⟩).2 _ hb,
      mul_inv_cancel_right, ← sq]
  have hch : Commute c (b * ((r ⟨b, hb⟩ : ↥Bs) : G)) :=
    (Subgroup.mem_centralizer_iff.mp hcH _ hH).symm
  have hcd : Commute c (b * ((r ⟨b, hb⟩ : ↥Bs) : G)⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hcX _ hdX).symm
  have hcb : Commute c (b ^ 2) := hsq ▸ hch.mul_right hcd
  obtain ⟨k, hk⟩ := hp
  have hbk : (b ^ 2) ^ (k + 1) = b := by
    rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hBs.2 b hb, one_mul]
  exact (hbk ▸ hcb.pow_right (k + 1)).eq.symm

omit [Finite G] in
theorem exists_noncyclic_pSubgroup_of_mulEquiv {p : ℕ} {X Y : Subgroup G} (φ : ↥X ≃* ↥Y)
    (h : ∃ S : Subgroup G, S ≤ X ∧ IsPGroup p S ∧ ¬ IsCyclic S) :
    ∃ S : Subgroup G, S ≤ Y ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨S, hSX, hSp, hSnc⟩ := h
  let S₀ : Subgroup ↥X := S.subgroupOf X
  let e₀ : ↥S₀ ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSX
  let T₀ : Subgroup ↥Y := S₀.map φ.toMonoidHom
  let e₁ : ↥S₀ ≃* ↥T₀ := S₀.equivMapOfInjective φ.toMonoidHom φ.injective
  let e₂ : ↥T₀ ≃* ↥(T₀.map Y.subtype) := T₀.equivMapOfInjective Y.subtype Y.subtype_injective
  refine ⟨T₀.map Y.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact hSp.of_equiv (e₀.symm.trans (e₁.trans e₂))
  · intro hcyc
    apply hSnc
    let e : ↥(T₀.map Y.subtype) ≃* ↥S := (e₀.symm.trans (e₁.trans e₂)).symm
    exact isCyclic_of_surjective e.toMonoidHom e.surjective

omit [Finite G] in
open Subgroup in
private theorem refl_mul_inv_mem_zpowers {E : Type*} [Group E] [Finite E] [IsMulCommutative E]
    {p : ℕ} (hp : p.Prime) (hEp : ∀ b : E, b ^ p = 1) {φ : MulAut E}
    (hcard : Nat.card {b : E // φ b = b} * p = Nat.card E) (b v : E) (hb : φ b * b⁻¹ ≠ 1) :
    φ v * v⁻¹ ∈ zpowers (φ b * b⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  let δ : E →* E := MonoidHom.mk' (fun c => φ c * c⁻¹) fun c d => by
    simp only [map_mul, mul_inv_rev]
    calc φ c * φ d * (d⁻¹ * c⁻¹) = φ c * (φ d * d⁻¹) * c⁻¹ := by group
      _ = φ c * (c⁻¹ * (φ d * d⁻¹)) := by rw [mul_assoc, mul_comm' (φ d * d⁻¹) c⁻¹]
      _ = φ c * c⁻¹ * (φ d * d⁻¹) := by group
  have hker : Nat.card δ.ker = Nat.card {b : E // φ b = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => by
      change φ c * c⁻¹ = 1 ↔ φ c = c
      exact mul_inv_eq_one)
  have hmul := card_ker_mul_card_range δ
  have hpos : 0 < Nat.card {b : E // φ b = b} := by
    rw [← hker]; exact Nat.card_pos
  have hrange : Nat.card δ.range = p := by
    rw [hker] at hmul
    exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans hcard.symm)
  have hord : orderOf (φ b * b⁻¹) = p := orderOf_eq_prime (hEp _) hb
  have hle : zpowers (φ b * b⁻¹) ≤ δ.range := zpowers_le.2 ⟨b, rfl⟩
  have hzcard : Nat.card (zpowers (φ b * b⁻¹)) = p := by rw [Nat.card_zpowers, hord]
  have heq : zpowers (φ b * b⁻¹) = δ.range :=
    eq_of_le_of_card_ge hle (by rw [hzcard, hrange])
  rw [heq]
  exact ⟨v, rfl⟩

omit [Finite G] in
private theorem eq_one_of_sq_eq_one_of_pow {E : Type*} [Monoid E] {p : ℕ} (hp : Odd p) {z : E}
    (hz : z ^ p = 1) (h2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨k, rfl⟩ := hp
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at hz

omit [Finite G] in
theorem GGIsReflection.eq_of_commute_of_apply_eq_inv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} [Finite Bs] (hBs : IsElemAbelian p Bs) {r r' : MulAut ↥Bs}
    (hr : GGIsReflection p r) (hr' : GGIsReflection p r') (hc : Commute r r') {e : ↥Bs}
    (he : e ≠ 1) (hre : r e = e⁻¹) (hr'e : r' e = e⁻¹) : r = r' := by
  have : IsMulCommutative ↥Bs := hBs.1
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hEp : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hδe : r e * e⁻¹ ≠ 1 := by
    rw [hre]
    intro h
    apply he
    have h2 : e⁻¹ ^ 2 = 1 := by rw [sq]; exact h
    exact inv_eq_one.mp (eq_one_of_sq_eq_one_of_pow hpo (by rw [inv_pow, hEp, inv_one]) h2)
  have hδ' : r' e * e⁻¹ = r e * e⁻¹ := by rw [hre, hr'e]
  have hz : r (r e * e⁻¹) = (r e * e⁻¹)⁻¹ ∧ r' (r e * e⁻¹) = (r e * e⁻¹)⁻¹ := by
    rw [hre]
    constructor <;> simp [map_mul, map_inv, hre, hr'e]
  have hinv : ∀ z ∈ Subgroup.zpowers (r e * e⁻¹), r z = z⁻¹ ∧ r' z = z⁻¹ := by
    rintro _ ⟨k, rfl⟩
    exact ⟨by simp only [map_zpow, hz.1, inv_zpow], by simp only [map_zpow, hz.2, inv_zpow]⟩
  refine MulEquiv.ext fun c => ?_
  have hd : r c * c⁻¹ ∈ Subgroup.zpowers (r e * e⁻¹) :=
    refl_mul_inv_mem_zpowers hp hEp hr.2 e c hδe
  have hd' : r' c * c⁻¹ ∈ Subgroup.zpowers (r e * e⁻¹) := by
    rw [← hδ']
    exact refl_mul_inv_mem_zpowers hp hEp hr'.2 e c (by rw [hδ']; exact hδe)
  set d := r c * c⁻¹ with hd_def
  set d' := r' c * c⁻¹ with hd'_def
  have hrc : r c = d * c := by rw [hd_def, inv_mul_cancel_right]
  have hr'c : r' c = d' * c := by rw [hd'_def, inv_mul_cancel_right]
  clear_value d d'
  have h1 : r (r' c) = d'⁻¹ * (d * c) := by rw [hr'c, map_mul, (hinv d' hd').1, hrc]
  have h2 : r' (r c) = d⁻¹ * (d' * c) := by rw [hrc, map_mul, (hinv d hd).2, hr'c]
  have h12 : r (r' c) = r' (r c) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hc.eq]
  rw [h1, h2] at h12
  have hsq : (d * d'⁻¹) ^ 2 = 1 := by
    have h3 : d'⁻¹ * d = d⁻¹ * d' := by
      rw [← mul_assoc, ← mul_assoc] at h12
      exact mul_right_cancel h12
    calc (d * d'⁻¹) ^ 2 = d * d'⁻¹ * (d * d'⁻¹) := sq _
      _ = d * (d'⁻¹ * d) * d'⁻¹ := by simp only [mul_assoc]
      _ = d * (d⁻¹ * d') * d'⁻¹ := by rw [h3]
      _ = 1 := by group
  have hdd : d * d'⁻¹ = 1 := eq_one_of_sq_eq_one_of_pow hpo (hEp _) hsq
  rw [hrc, hr'c, mul_inv_eq_one.mp hdd]

omit [Finite G] in
theorem mem_of_apply_eq_inv_of_mem_ggAutomizer {p : ℕ} (hp : Odd p) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsX : Bs ≤ Subgroup.normalizer (X : Set G)) {w : MulAut ↥Bs}
    (hw : w ∈ ggAutomizer X Bs) {b : ↥Bs} (hb : w b = b⁻¹) : (b : G) ∈ X := by
  obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp hw
  have h1 : (b : G) * g * (b : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hBsX b.2) g).mp hgX
  have hgb : g * (b : G) * g⁻¹ = (b : G)⁻¹ := by rw [← hg b, hb, Subgroup.coe_inv]
  have hsq : (b : G) ^ 2 = (b : G) * g * (b : G)⁻¹ * g⁻¹ := by
    have h' : g * (b : G)⁻¹ * g⁻¹ = (b : G) := by
      have := congrArg (·⁻¹) hgb
      simpa [mul_assoc] using this
    calc (b : G) ^ 2 = (b : G) * (g * (b : G)⁻¹ * g⁻¹) := by rw [h', sq]
      _ = (b : G) * g * (b : G)⁻¹ * g⁻¹ := by group
  have h2 : (b : G) ^ 2 ∈ X := by
    rw [hsq]
    exact X.mul_mem h1 (X.inv_mem hgX)
  obtain ⟨k, hk⟩ := hp
  have hbk : ((b : G) ^ 2) ^ (k + 1) = b := by
    rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hBs.2 b b.2, one_mul]
  rw [← hbk]
  exact X.pow_mem h2 _

theorem exists_noncyclic_pSubgroup_of_commute_refl {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) (hBsX : Bs ≤ Subgroup.normalizer (X : Set G))
    {r r' : MulAut ↥Bs} (hrX : r ∈ ggAutomizer X Bs) (hr'X : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) (hr' : GGIsReflection p r') (hc : Commute r r') (hne : r ≠ r') :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  have : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨e, he, hre⟩ := hr.exists_inverted_ne_one hp
  obtain ⟨e', he', hr'e'⟩ := hr'.exists_inverted_ne_one hp
  have hSB : Subgroup.zpowers (e : G) ⊔ Subgroup.zpowers (e' : G) ≤ Bs :=
    sup_le (Subgroup.zpowers_le.2 e.2) (Subgroup.zpowers_le.2 e'.2)
  have hSp : ∀ g ∈ Subgroup.zpowers (e : G) ⊔ Subgroup.zpowers (e' : G), g ^ p = 1 :=
    fun g hg => hBs.2 g (hSB hg)
  have hord : ∀ u : ↥Bs, u ≠ 1 → Nat.card (Subgroup.zpowers (u : G)) = p := by
    intro u hu
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hBs.2 u u.2) (fun h => hu (Subtype.ext h))
  refine ⟨Subgroup.zpowers (e : G) ⊔ Subgroup.zpowers (e' : G), sup_le ?_ ?_,
    fun g => ⟨1, Subtype.ext (by simpa using hSp g g.2)⟩, ?_⟩
  · exact Subgroup.zpowers_le.2 (mem_of_apply_eq_inv_of_mem_ggAutomizer hpo hBs hBsX hrX hre)
  · exact Subgroup.zpowers_le.2 (mem_of_apply_eq_inv_of_mem_ggAutomizer hpo hBs hBsX hr'X hr'e')
  · intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hcardS : Nat.card ↥(Subgroup.zpowers (e : G) ⊔ Subgroup.zpowers (e' : G)) ∣ p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hSp g g.2))
    have hS1 : Subgroup.zpowers (e : G) = Subgroup.zpowers (e : G) ⊔ Subgroup.zpowers (e' : G) := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
      rw [hord e he]
      exact Nat.le_of_dvd hp.pos hcardS
    have hS2 : Subgroup.zpowers (e' : G) =
        Subgroup.zpowers (e : G) ⊔ Subgroup.zpowers (e' : G) := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
      rw [hord e' he']
      exact Nat.le_of_dvd hp.pos hcardS
    have hmem : (e : G) ∈ Subgroup.zpowers (e' : G) := by
      rw [hS2, ← hS1]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := hmem
    have hek : e' ^ k = e := Subtype.ext (by simpa using hk)
    have hr'e : r' e = e⁻¹ := by rw [← hek, map_zpow, hr'e', inv_zpow]
    exact hne (GGIsReflection.eq_of_commute_of_apply_eq_inv hp hp2 hBs hr hr' hc he hre hr'e)

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}

theorem GGF4QGeFourCfg.bstar_le_normalizer (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {X : Subgroup G} (hX : X = L ∨ X = K) : Bs ≤ Subgroup.normalizer (X : Set G) := by
  rcases hX with rfl | rfl
  · exact GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  · exact GGDichotomy.le_normalizer_of_innerDiagOn (hcfg.1.2.2.1.2 y _ hcfg.2.2.2)

theorem ggF4QGeFour_centralizer_le_normalizer_L (ha₀ : GGLNoncyclicInput)
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) :
    Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hxB : x ∈ Bs := hcfg.1.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.1.tableB_facts.2.2.2.1
  have hxH : x ∈ ggHyperplane Bs r := mem_ggHyperplane_of_mem_ggAutomizer hrA hxB hLx
  intro g hg
  refine mem_normalizer_of_sstar hI.2.2.2.2.2.2.1 (ha₀ G p B x L hI) ?_
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact hg h hxH

theorem exists_commute_refl_of_f4Triple {A : Subgroup (MulAut ↥Bs)}
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} {a : Fin 3 → CoxeterMatrix.F₄.Group}
    (ha : ∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (a k))
    (ha02 : orderOf (a 0 * a 2) = 2)
    (haX : ∀ z, z ∈ Subgroup.closure (Set.range a) ↔
      ((e z : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    ∃ r r' : MulAut ↥Bs, r ∈ ggAutomizer X Bs ∧ r' ∈ ggAutomizer X Bs ∧ GGIsReflection p r ∧
      GGIsReflection p r' ∧ Commute r r' ∧ r ≠ r' := by
  have hcoxRefl : ∀ t : CoxeterMatrix.F₄.Group, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection t →
      ((e t : ↥A) : MulAut ↥Bs) ∈ ggCoxRefl CoxeterMatrix.F₄ e := by
    rintro t ⟨u, k, rfl⟩
    exact ⟨u, k, by rw [CoxeterMatrix.toCoxeterSystem_simple]⟩
  have hinv : ∀ k, (a k)⁻¹ = a k := fun k => inv_eq_of_mul_eq_one_right (ha k).mul_self
  have hcomm : a 0 * a 2 = a 2 * a 0 := by
    have h2 : (a 0 * a 2) * (a 0 * a 2) = 1 := by
      rw [← sq, ← ha02]
      exact pow_orderOf_eq_one _
    calc a 0 * a 2 = (a 0 * a 2)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
      _ = a 2 * a 0 := by rw [mul_inv_rev, hinv, hinv]
  refine ⟨((e (a 0) : ↥A) : MulAut ↥Bs), ((e (a 2) : ↥A) : MulAut ↥Bs),
    (haX _).mp (Subgroup.subset_closure ⟨0, rfl⟩), (haX _).mp (Subgroup.subset_closure ⟨2, rfl⟩),
    ggCoxRefl_isReflection hpres.2 (hcoxRefl _ (ha 0)),
    ggCoxRefl_isReflection hpres.2 (hcoxRefl _ (ha 2)), ?_, ?_⟩
  · change ((e (a 0) : ↥A) : MulAut ↥Bs) * ((e (a 2) : ↥A) : MulAut ↥Bs) =
      ((e (a 2) : ↥A) : MulAut ↥Bs) * ((e (a 0) : ↥A) : MulAut ↥Bs)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
  · intro h
    have h' : a 0 = a 2 := e.injective (Subtype.ext h)
    have h1 : orderOf (a 0 * a 2) = 1 := by
      rw [h', (ha 2).mul_self, orderOf_one]
    omega

theorem ggF4QGeFour_centralizer_le_normalizer_K_of_noncyclic
    (hTBF : GGTBFixInput) (hFC : GGResNbrFixCentralizesInput)
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    (hnc : ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer K Bs) :
    Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hNb : GGNbr p B x D J y K := hcfg.2.2.2
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hE, -, -, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact hβ.2.1
  have hJ : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ggAutomizerJoin_singleton L Bs K
  let e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs {K}) :=
    e.trans (MulEquiv.subgroupCongr hJ.symm)
  have hP : GGCoxeterPres p (ggAutomizerJoin L Bs {K}) CoxeterMatrix.F₄ e' :=
    ⟨hpres.1, fun i => hpres.2 i⟩
  have hF4 : GGIsWeylMatrixF4 CoxeterMatrix.F₄ :=
    ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩
  have hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) →
      (b : G) ∈ Subgroup.zpowers x := fun b hb =>
    ((GGSecFiveRestHyp.fixLineComp_L hTBF hRC.1 hRC.2.1).fix_iff b).1 hb
  have hF1 : ∀ y' K', GGNbr p B x D J y' K' → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K' Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K' : Set G) :=
    fun y' K' hn b hb =>
      hFC G p B Bs x L D J y' K'
        ⟨hRC.1.1, hRC.1.2.1, hRC.1.2.2.1, hRC.1.2.2.2.1, hn, hRC.2.1 y' K' hn, Or.inr hRC.2.1⟩ b hb
  have hBB : B = Bs := ggF4_join_B_eq_bstar hRC hP hF4
    (ggF4_join_fix_one hRC hFixL hF1 ⟨K, Finset.mem_singleton_self K⟩)
  have hcen : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    rw [← hBB]
    exact inf_centralizer_eq_zpowers_of_sHat hNb.1
  have hyBs : y ∈ Bs := hc.2.1.1 hNb.1.2.1
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
    rw [hcen, Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hE.2 y hyBs))
  have hcomp := isComponentOf_of_isNeighborOf hc.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hc.2.2 hNb)
  obtain ⟨hBmax, hyB, hy1, -, -, -⟩ := hNb.1
  have hEC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    (hcfg.bstar_le_normalizer (Or.inr rfl)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer K)
  have hS : LargeEvenSStar p B y K :=
    ⟨hBmax, hyB, hy1, hcomp.1, fun S hSle hSp =>
      ggSCNoTV_isCyclic hp2 hE hc.2.1.2.2.2 hcfg.1.2.2.2.1 hEC hcard hSle hSp⟩
  have hyH : y ∈ ggHyperplane Bs r := mem_ggHyperplane_of_mem_ggAutomizer hrA hyBs hcomp.1.1
  intro g hg
  refine mem_normalizer_of_sstar hS hnc ?_
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact hg h hyH

end Pure

section Members

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {y : G} {K : Subgroup G}

theorem ggF4QGeFour_rankOneIn_perfect {row : GGF4QGeFourRow} (hKG : GGF4QGeFourKGPosInput row)
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp row f L K)
    {X : Subgroup G} (hX : X = L ∨ X = K) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hrC : r ∈ ggCoxRefl CoxeterMatrix.F₄ e) :
    ⁅ggRankOneIn X Bs r, ggRankOneIn X Bs r⁆ = ggRankOneIn X Bs r := by
  obtain ⟨F, _, _, θ, -, hθinj, hθrange, -, hS1, hS2⟩ :=
    ggF4QGeFourRk1Input_of_kgPos row hKG G p B Bs x L D J y K hcfg e hpres f hf hp hrow X hX r
      hrA hrC
  have h4f : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard : 4 ≤ Nat.card F := by
    cases row with
    | S1 => rw [hS1 rfl]; exact h4f
    | S2 =>
      rcases hS2 rfl with h | h
      · rw [h]; exact h4f
      · rw [h]
        exact h4f.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, hs⟩ : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hcard)
    exact ⟨s, hs⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (K := F) ⟨s, hs⟩
  have hperfR : Group.IsPerfect ↥θ.range :=
    Group.IsPerfect.ofSurjective (f := θ.rangeRestrict) θ.rangeRestrict_surjective
  rw [← hθrange]
  exact Subgroup.isPerfect_iff.1 hperfR

omit [Finite G] in
theorem nonempty_mulEquiv_of_centralImage_PSp {f : ℕ} {X : Subgroup G}
    (h : GGCentralImage .PSp 3 f X) : Nonempty ((ggU .PSp 3 f).K ≃* ↥X) := by
  obtain ⟨ψ, hadm, hker, hrange⟩ := h
  have hf1 : 1 ≤ f := hadm.2.1
  have : NeZero f := ⟨by omega⟩
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot
      (K := GaloisField 2 f) (n := 3) (by norm_num)).le
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

omit [Finite G] in
theorem outSolvable_of_centralImage_PSp {f : ℕ} {X : Subgroup G}
    (h : GGCentralImage .PSp 3 f X) : OutSolvable ↥X := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_centralImage_PSp h
  have hf1 : 1 ≤ f := h.choose_spec.1.2.1
  have : NeZero f := ⟨by omega⟩
  have hS : OutSolvable ↥(StatedSp 3 (GaloisField 2 f)) :=
    CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
      (CFSG.SeitzReduction.SymplecticPilot.isSolvable_outer_statedSp (n := 3) (by norm_num))
  exact outSolvable_congr' e hS

theorem ggF4QGeFour_centralizer_le_normalizer_K_S1 (ha₀ : GGLNoncyclicInput)
    (hTBF : GGTBFixInput) (hFC : GGResNbrFixCentralizesInput)
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hrow : GGF4QGeFourRowHyp .S1 f L K) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer K Bs) :
    Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨eL⟩ := nonempty_mulEquiv_of_centralImage_PSp hrow.1
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_centralImage_PSp hrow.2
  exact ggF4QGeFour_centralizer_le_normalizer_K_of_noncyclic hTBF hFC hcfg hRC e hpres
    (exists_noncyclic_pSubgroup_of_mulEquiv (eL.symm.trans eK) (ha₀ G p B x L hcfg.1.1.1)) hrA

@[expose] def GGF4QGeFourL1OddInput (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X : Subgroup G, (X = L ∨ X = K) → ∀ r ∈ ggAutomizer X Bs,
        r ∈ ggCoxRefl CoxeterMatrix.F₄ e →
          Odd (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
            Subgroup.centralizer (ggHyperplane Bs r : Set G)))

@[expose] def GGF4QGeFourKGCentInput (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X Y : Subgroup G, (X = L ∧ Y = K ∨ X = K ∧ Y = L) →
        ∀ t : G, (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∈ Subgroup.centralizer (Bs : Set G) →
          t ∈ Subgroup.centralizer (X : Set G) → t ∈ Subgroup.centralizer (Y : Set G)

theorem ggF4QGeFourL1OddInput_of_kgCent (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {row : GGF4QGeFourRow} (hJoin : GGF4QGeFourJoinInput row)
    (hKC : GGF4QGeFourKGCentInput row) : GGF4QGeFourL1OddInput row := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X hX r hrA hrC
  obtain ⟨hpp, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.1.1.2.2.2.2.2.1.2.1
  have hr2 : r ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 hrC).1
  have hCB := centralizer_inf_le_centralizer_bstar (hpp.odd_of_ne_two hp2) hBs
    (hcfg.bstar_le_normalizer hX) hrA hr2
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hcfg.1.1.1 hcfg.1.1.2.2
  have hJX : J ≤ X := by
    rcases hX with hXL | hXK
    · rw [hXL]; exact SecFiveL1Odd.J_le hL hRC hpJ (Or.inl rfl)
    · rw [hXK]; exact SecFiveL1Odd.J_le hL hRC hpJ (Or.inr (Finset.mem_singleton_self _))
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (ggHyperplane Bs r : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htB : (t : G) ∈ Subgroup.centralizer (Bs : Set G) := hCB t.2
  have htX : (t : G) ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp t.2).1
  have h2t : ∃ k : ℕ, (t : G) ^ (2 ^ k) = 1 := ⟨1, by rw [pow_one, ← ht', pow_orderOf_eq_one]⟩
  have hLK : (t : G) ∈ Subgroup.centralizer (L : Set G) ∧
      (t : G) ∈ Subgroup.centralizer (K : Set G) := by
    rcases hX with hXL | hXK
    · have htL : (t : G) ∈ Subgroup.centralizer (L : Set G) := by rw [← hXL]; exact htX
      exact ⟨htL, hKC G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow L K
        (Or.inl ⟨rfl, rfl⟩) t h2t htB htL⟩
    · have htK : (t : G) ∈ Subgroup.centralizer (K : Set G) := by rw [← hXK]; exact htX
      exact ⟨hKC G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow K L
        (Or.inr ⟨rfl, rfl⟩) t h2t htB htK, htK⟩
  set T : Subgroup G := Subgroup.zpowers (t : G) with hTdef
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 : (t : G) = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G) :=
    Subgroup.zpowers_le.mpr ⟨Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (SecFiveL1Odd.le_bstar hRC)) htB,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJX) htX⟩
  have hT0 : T ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
    rw [hJoin G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hLK.1))
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hLK.2))
  exact SecFiveL1Odd.false_of_le_centralizer_ggG0 ha₀ hL hRC hpJ hT2 hT1 hT hT0

theorem ggF4QGeFourL1Input_S1_of_odd (hKG : GGF4QGeFourKGPosInput .S1)
    (ha₀ : GGLNoncyclicInput) (hTBF : GGTBFixInput) (hFC : GGResNbrFixCentralizesInput)
    (hO : GGF4QGeFourL1OddInput .S1) : GGF4QGeFourL1Input .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X hX r hrA hrC
  have hperf := ggF4QGeFour_rankOneIn_perfect hKG hcfg e hpres hf hp hrow hX hrA hrC
  have hN : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    rcases hX with rfl | rfl
    · exact ggF4QGeFour_centralizer_le_normalizer_L ha₀ hcfg hrA
    · exact ggF4QGeFour_centralizer_le_normalizer_K_S1 ha₀ hTBF hFC hcfg hRC e hpres hrow hrA
  have hOut : OutSolvable ↥X := by
    rcases hX with rfl | rfl
    · exact outSolvable_of_centralImage_PSp hrow.1
    · exact outSolvable_of_centralImage_PSp hrow.2
  exact ggRankOnePerf_eq_of_pieces hperf
    (ggF4QGeFour_perfectCore_le_of_normalizer hOut (hcfg.bstar_le_normalizer hX) hN)
    (hO G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X hX r hrA hrC)

open CFSG.LieType.RootSystem in
theorem exists_noncyclic_pSubgroup_K_S2 (hKG : GGF4QGeFourKGPosInput .S2)
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp .S2 f L K) :
    ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨-, hK⟩ : GGTableBPosImage p Bs .POmegaMinus 4 f L ∧
      (GGTableBPosImage p Bs .PSU 6 f K ∨ GGTableBPosImage p Bs .POmegaMinus 4 f K) :=
    hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  obtain ⟨b, hb, -, -, hb02, hbK⟩ : ∃ b : Fin 3 → CoxeterMatrix.F₄.Group,
      (∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (b k)) ∧
      orderOf (b 0 * b 1) = 3 ∧ orderOf (b 1 * b 2) = 4 ∧ orderOf (b 0 * b 2) = 2 ∧
      ∀ z, z ∈ Subgroup.closure (Set.range b) ↔
        ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer K Bs := by
    rcases hK with hK | hK
    · obtain ⟨-, -, -, εK, hεK, -⟩ := hK
      obtain ⟨σK, -, hMK⟩ := exists_coxeterMatrix_PSU_six (f := f) (by omega)
      exact exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK σK hMK
    · obtain ⟨-, -, -, εK, hεK, -⟩ := hK
      have hML : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
          ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
        intro k l
        rw [coxeterMatrix_POmegaMinus_four]
        rfl
      exact exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK
        (Equiv.refl _) hML
  obtain ⟨r, r', hrK, hr'K, hr, hr', hc, hne⟩ := exists_commute_refl_of_f4Triple hpres hb hb02 hbK
  exact exists_noncyclic_pSubgroup_of_commute_refl hpp hp2 hEl
    (hcfg.bstar_le_normalizer (Or.inr rfl)) hrK hr'K hr hr' hc hne

theorem ggF4QGeFourL1Input_S2_of_odd (hKG : GGF4QGeFourKGPosInput .S2)
    (ha₀ : GGLNoncyclicInput) (hTBF : GGTBFixInput) (hFC : GGResNbrFixCentralizesInput)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hO : GGF4QGeFourL1OddInput .S2) : GGF4QGeFourL1Input .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X hX r hrA hrC
  have hperf := ggF4QGeFour_rankOneIn_perfect hKG hcfg e hpres hf hp hrow hX hrA hrC
  have hN : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    rcases hX with rfl | rfl
    · exact ggF4QGeFour_centralizer_le_normalizer_L ha₀ hcfg hrA
    · exact ggF4QGeFour_centralizer_le_normalizer_K_of_noncyclic hTBF hFC hcfg hRC e hpres
        (exists_noncyclic_pSubgroup_K_S2 hKG hcfg e hpres hf hp hrow) hrA
  have hOut : OutSolvable ↥X := by
    refine ggSecFive_outSolvable_of_member hSch hRC ?_
    rcases hX with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨y, hcfg.2.2.2⟩
  exact ggRankOnePerf_eq_of_pieces hperf
    (ggF4QGeFour_perfectCore_le_of_normalizer hOut (hcfg.bstar_le_normalizer hX) hN)
    (hO G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow X hX r hrA hrC)

end Members

end CFSG.StandardType

end
