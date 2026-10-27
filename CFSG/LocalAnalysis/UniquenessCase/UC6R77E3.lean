module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R77E2
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Key
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6R77

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (P65N2.exists_elemSec P65N2.ElemSec.card_eq
  P65N2.ElemSec.eq_iff P65N2.actEquiv P65N2.card_le_of_range P65N2.eq_of_trivial_on_quotient_pElt
  P65N2.commutator_le_self P65N2.normalizer_le_normalizer_commutator P65N2.exists_rank_bound)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank (ZA628.commutator_pow_le_frattini)

variable {G : Type} [Group G] [Finite G]

section Bounds

theorem exists_card_le_pow_mul_card_inf_centralizer {p r : ℕ} [hr : Fact r.Prime] (hp : p.Prime)
    (hpr : p ≠ r) {X P : Subgroup G} (hX : IsPGroup r X) (hexp : ∀ x ∈ X, x ^ r = 1)
    (hPX : P ≤ normalizer (X : Set G)) (hPel : IsElemAbelian p P) :
    ∃ d : ℕ, Nat.card X = Nat.card (⁅X, X⁆ : Subgroup G) * r ^ d ∧
      Nat.card P ≤ p ^ d * Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) := by
  have hle : (⁅X, X⁆ : Subgroup G) ≤ X := P65N2.commutator_le_self X
  have hMn : ∀ x ∈ X, ∀ m ∈ (⁅X, X⁆ : Subgroup G), x * m * x⁻¹ ∈ (⁅X, X⁆ : Subgroup G) :=
    fun x hx m hm => (mem_normalizer_iff.mp
      (P65N2.normalizer_le_normalizer_commutator X (le_normalizer hx)) m).mp hm
  obtain ⟨W, _, _, _, π, ρ, hs⟩ := P65N2.exists_elemSec (f := r) (Y := X) (M := ⁅X, X⁆)
    (G := P) hle hMn (fun x hx y hy => commutator_mem_commutator hx hy)
    (fun x hx => by rw [hexp x hx]; exact one_mem _)
    hPX (fun g hg => P65N2.normalizer_le_normalizer_commutator X (hPX hg))
  haveI : Finite W := Module.finite_of_finite (ZMod r)
  refine ⟨Module.finrank (ZMod r) W, ?_, ?_⟩
  · rw [hs.card_eq hle, Module.natCard_eq_pow_finrank (K := ZMod r) (V := W), Nat.card_zmod]
  have hrK : ((p : ℕ) : ZMod r) ≠ 0 := by
    intro h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hr.out hp).mp ((ZMod.natCast_eq_zero_iff p r).mp h)).symm
  have hfr : (⁅X, X⁆).subgroupOf X ≤ frattini ↥X := by
    have := ZA628.commutator_pow_le_frattini (f := r) (C := X) hX
    exact fun x hx => this (mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx)))
  have hker : ∀ a : ↥P, P65N2.actEquiv ρ (inclusion le_rfl a) = 1 →
      (a : G) ∈ centralizer (X : Set G) := by
    intro a h1
    rw [mem_centralizer_iff]
    intro x hx
    refine (P65N2.eq_of_trivial_on_quotient_pElt (n := 1) hp hpr hX hle hMn hfr
      (by rw [pow_one]; exact hPel.2 a a.2) (hPX a.2)
      (P65N2.normalizer_le_normalizer_commutator X (hPX a.2)) (fun y hy => ?_) x hx).symm
    have hay : (a : G) * y * (a : G)⁻¹ ∈ X := (mem_normalizer_iff.mp (hPX a.2) y).mp hy
    refine (hs.eq_iff hy hay).mp ?_
    have h2 := hs.act a y hy
    have h3 : ρ a (π y) = π y := LinearEquiv.congr_fun h1 (π y)
    rw [h3] at h2
    exact h2
  haveI : Finite ((P65N2.actEquiv ρ).comp (inclusion (le_refl P))).range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  refine P65N2.card_le_of_range (P65N2.actEquiv ρ) le_rfl hker ?_
  refine CFSG.RankThree.PartOne.LIT.card_le_pow_finrank_sub hp hrK _ ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hPel.comm a.2 b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (by simpa using hPel.2 a a.2)
    rw [this, map_one]

theorem card_le_pow_three_mul_card_inf_centralizer {p r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hp : p.Prime) (hpr : p ≠ r) {X P : Subgroup G} (hX : IsPGroup r X)
    (hPX : P ≤ normalizer (X : Set G)) (hPel : IsElemAbelian p P)
    (hrank : CFSG.Open.pRank r X ≤ 3) :
    Nat.card P ≤ p ^ 3 * Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) := by
  obtain ⟨χ, hχ⟩ := P65N2.exists_rank_bound hr2 hp hpr hX hPX fun E hEX hEc hEe => by
    obtain ⟨k, hk⟩ := (hX.to_le hEX).exists_card_eq
    have hEel : IsElemAbelian r E := ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, hEe⟩
    have hk3 : k ≤ 3 := (CFSG.SectionRank.le_pRank hr.out.one_lt hEX hEel hk).trans hrank
    rw [hk]
    exact Nat.pow_le_pow_right hr.out.pos hk3
  set E : Subgroup G := χ.ker.map P.subtype with hE
  have hEP : E ≤ P := map_subtype_le _
  have h1 := hχ E hEP (fun a ha b hb => hPel.comm (hEP ha) (hEP hb))
    (fun a ha => hPel.2 a (hEP ha)) (by
      rintro _ ⟨b, hb, rfl⟩
      exact MonoidHom.mem_ker.mp hb)
  have hrange : Nat.card χ.range ≤ p := by
    refine card_le_of_isCyclic hp.pos fun x => ?_
    obtain ⟨a, ha⟩ := x.2
    have hap : a ^ p = 1 := Subtype.ext (by simpa using hPel.2 a a.2)
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← ha, ← map_pow, hap, map_one, OneMemClass.coe_one]
  have hPE : Nat.card P ≤ Nat.card E * p := by
    have h := (show Nat.card χ.ker * Nat.card χ.range = Nat.card P by
      rw [← index_ker, card_mul_index])
    rw [← h, show Nat.card E = Nat.card χ.ker from card_map_of_injective P.subtype_injective]
    exact Nat.mul_le_mul_left _ hrange
  calc Nat.card P ≤ Nat.card E * p := hPE
    _ ≤ p ^ 2 * Nat.card (E ⊓ centralizer (X : Set G) : Subgroup G) * p :=
        Nat.mul_le_mul_right _ h1
    _ ≤ p ^ 2 * Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) * p :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (card_le_of_le (inf_le_inf_right _ hEP)))
    _ = p ^ 3 * Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) := by ring

end Bounds

section Normalizers

theorem centralizer_le_normalizer_zpowers (w : G) :
    centralizer ({w} : Set G) ≤ normalizer (zpowers w : Set G) := by
  have h : centralizer ({w} : Set G) = centralizer (zpowers w : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [h]
  exact centralizer_le_normalizer _

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem normalizer_le_normalizer_inf_centralizer (X : Subgroup G) :
    normalizer (X : Set G) ≤
      normalizer ((X ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun z hz => mem_inf.2 ⟨(mem_normalizer_iff.mp hg z).mp
    (mem_inf.1 hz).1, mem_centralizer_iff.2 fun h hh => ?_⟩
  have hh' : g⁻¹ * h * g ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    rwa [inv_inv] at this
  have hzh := mem_centralizer_iff.1 (mem_inf.1 hz).2 _ hh'
  calc h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hzh]
    _ = g * z * g⁻¹ * h := by group

theorem normalizer_zpowers_le_rankThreeGamma {r : ℕ} [hr : Fact r.Prime] {A : Subgroup G}
    {y : G} (hyA : y ∈ A) (hyr : y ^ r = 1) (hy1 : y ≠ 1) :
    normalizer (zpowers y : Set G) ≤ rankThreeGamma 1 r A :=
  CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (zpowers_le.mpr hyA)
    (CFSG.SectionRank.le_pRank hr.out.one_lt le_rfl (isElemAbelian_zpowers hyr)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hyr hy1, pow_one]))

theorem rankThreeGamma_le_of_forall_normalizer_zpowers_le {p r : ℕ} [Fact p.Prime]
    [hr : Fact r.Prime] {M A : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (hA : IsPGroup r A) {c : G} (hcA : c ∈ centralizer (A : Set G)) (hc : orderOf c = p)
    (h : ∀ y ∈ A, y ≠ 1 → normalizer (zpowers y : Set G) ≤ M) : rankThreeGamma 1 r A ≤ M := by
  refine hM.rankThreeGamma_one_le hA fun L hLA hLcard => ?_
  haveI : IsCyclic L := isCyclic_of_prime_card (p := r) hLcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L)
  have hgo : orderOf (g : G) = r := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hLcard]
  have hgL : zpowers (g : G) = L := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr g.2) ?_
    rw [Nat.card_zpowers, hgo, hLcard]
  have hg1 : (g : G) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hgo
    exact hr.out.one_lt.ne hgo
  refine ⟨hgL ▸ h g (hLA g.2) hg1, ?_⟩
  have hcN : c ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer _ (centralizer_le hLA hcA)
  have := orderOf_dvd_natCard (⟨c, hcN⟩ : normalizer (L : Set G))
  rwa [Subgroup.orderOf_mk, hc] at this

end Normalizers

section Hyperplane

theorem exists_hyperplane_centralizes_noncentral {p : ℕ} [hp : Fact p.Prime] {P X : Subgroup G}
    (hPel : IsElemAbelian p P) (hP1 : P ≠ ⊥) (hPX : P ≤ normalizer (X : Set G))
    (hpX : ¬ p ∣ Nat.card X) {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a) :
    ∃ H : Subgroup G, H ≤ P ∧ Nat.card H * p = Nat.card P ∧
      ∃ u ∈ X, (∀ h ∈ H, h * u = u * h) ∧ ∃ y ∈ X, u * y ≠ y * u := by
  classical
  haveI : CFSG.IsElementaryAbelian p P := hPel.isElementaryAbelian
  haveI : Nontrivial P := by
    obtain ⟨x, hx, hx1⟩ := (bot_or_exists_ne_one P).resolve_left hP1
    exact ⟨⟨⟨x, hx⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  let _ : MulDistribMulAction P X := Subgroup.conjMulDistribMulActionOfLeNormalizer P X hPX
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := P) (H := X) hpX
  by_contra hcon
  push Not at hcon
  have hle : ⨆ (B : Subgroup P) (_ : B.index = p), CFSG.fixedPointSubgroup B X ≤ center X := by
    refine iSup₂_le fun B hB => ?_
    intro x hx
    rw [mem_center_iff]
    intro y
    have hBcard : Nat.card (B.map P.subtype) * p = Nat.card P := by
      rw [card_map_of_injective P.subtype_injective, ← hB, card_mul_index]
    have h := hcon (B.map P.subtype) (map_subtype_le B) hBcard x x.2 (by
      rintro _ ⟨b, hb, rfl⟩
      have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
      change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
      calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (x : G) * (b : G) := by rw [hbx]) y y.2
    exact Subtype.ext h.symm
  rw [hgen, top_le_iff] at hle
  have hac : (⟨a, ha⟩ : X) ∈ center X := hle ▸ mem_top _
  exact hab (congrArg Subtype.val ((mem_center_iff.mp hac) ⟨b, hb⟩)).symm

end Hyperplane

section AutPow

variable {r : ℕ} [hr : Fact r.Prime] {E : Subgroup G}

theorem nonempty_mulAut_mulEquiv_GL_pow (hE : IsElemAbelian r E) {n : ℕ}
    (hEcard : Nat.card E = r ^ n) : Nonempty (MulAut E ≃* GL (Fin n) (ZMod r)) := by
  haveI : IsMulCommutative E := hE.1
  obtain ⟨φ⟩ := CFSG.Sporadic.RuSchreier.ru_nonempty_mulEquiv_of_elementary (p := r)
    (fun a b : E => mul_comm' a b) (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hEcard
  exact ⟨(MulAut.congr φ).trans (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL n)⟩

theorem card_le_pow_of_mulAut {p : ℕ} (hp : p.Prime) (hpr : p ≠ r) (hE : IsElemAbelian r E)
    {n : ℕ} (hEcard : Nat.card E = r ^ n) {B : Subgroup (MulAut E)} (hB : IsElemAbelian p B) :
    Nat.card B ≤ p ^ n := by
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_GL_pow hE hEcard
  have hpK : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq hr.out hp).1 h).symm
  have h := CFSG.RankThree.PartOne.LIT.card_le_pow_card_gl (K := ZMod r) (ι := Fin n) hp hpK
    (B.map e.toMonoidHom) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hB.comm ha hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hB.2 a ha, map_one])
  rwa [card_map_of_injective e.injective, Fintype.card_fin] at h

theorem isCyclic_of_mulAut_three {p : ℕ} [Fact p.Prime] (hpr : p ≠ r) (hpr1 : ¬ p ∣ r - 1)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 3) {B : Subgroup (MulAut E)}
    (hB : IsPGroup p B) : IsCyclic B := by
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_GL_pow hE hEcard
  haveI := CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_GL_three (k := ZMod r) (r := p)
    (by
      rw [Nat.card_zmod]
      exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq Fact.out hr.out).1 h))
    (by rwa [Nat.card_zmod]) (R := B.map e.toMonoidHom) (hB.map e.toMonoidHom)
  let e' : B ≃* B.map e.toMonoidHom := B.equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

end AutPow

end CFSG.LocalAnalysis.UniquenessCase.UC6R77
