module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCoreGood
import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
import CFSG.LieType.Chevalley.TwistMap
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
import CFSG.LocalAnalysis.StandardType.GGFinModelRat
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.GGFinModel

open scoped Pointwise commutatorElement


private theorem exists_fixed_index (t : TwistTag) : ∃ i : Fin t.tag.rank, t.perm i = i := by
  cases t
  · refine ⟨(1 : Fin 6), ?_⟩
    show (Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) 1 = 1
    decide
  · refine ⟨(2 : Fin 4), ?_⟩
    show (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 2 = 2
    decide

private theorem order_pos (t : TwistTag) : 0 < t.order := by cases t <;> decide

private theorem step_conj_g0_inv {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    (x : ModGL τ L) :
    D.step (D.g0⁻¹ * x * D.g0) = D.g0⁻¹ * D.Φ x * D.g0 := by
  rw [LangDatum.step, MonoidHom.comp_apply]
  change D.n * D.Φ (D.g0⁻¹ * x * D.g0) * D.n⁻¹ = D.g0⁻¹ * D.Φ x * D.g0
  simp only [map_mul, map_inv, D.lang]
  group

theorem rckPairCoreGood_tw (t : TwistTag) (S : LangSetup t.tag GGL 5)
    (hΦ : ∃ Fr : GGL →+* GGL, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom t GGL Fr) :
    RCKPairCoreGood S := by
  classical
  obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
  obtain ⟨i, hi⟩ := exists_fixed_index t
  let γ0 : Fin t.tag.rank → ℤ := Pi.single i 1
  have hγ0root : IsRoot t.tag γ0 := by
    change IsRoot t.tag (Pi.single i 1)
    exact IsRoot.basis i
  have hγ0perm : permLattice t.perm γ0 = γ0 := by
    change permLattice t.perm (Pi.single i 1) = Pi.single i 1
    rw [permLattice_single, hi]
  have hnegperm : permLattice t.perm (-γ0) = -γ0 := by
    change permLattice t.perm (-Pi.single i 1) = -Pi.single i 1
    rw [permLattice_neg_single, hi]
  let z0 : ModGL t.tag GGL := S.D.g0⁻¹
  have hz0eq : z0 = S.D.g0⁻¹ := rfl
  have hz0mem : z0 ∈ adjointGroup t.tag GGL := by
    rw [hz0eq]
    exact (adjointGroup t.tag GGL).inv_mem S.D.g0_mem
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let n : ℕ := t.order * e
  have hn : n ≠ 0 := (Nat.mul_pos (order_pos t) he).ne'
  let K : Type := GaloisField 2 n
  letI : Algebra K GGL := (ggRatEmb n).toAlgebra
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := charP_of_injective_algebraMap (algebraMap K GGL).injective 2
  have hr2 : r = 2 := CharP.eq GGL hchar (inferInstance : CharP GGL 2)
  have hq2 : S.D.q = 2 ^ e := by rw [hq, hr2]
  have hFrsurj : Function.Surjective Fr := (S.frobenius_bijective hFr).2
  have hFr2 : ∀ c : GGL, Fr c = c ^ (2 ^ e) := fun c => by rw [hFr, hq2]
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  have hKcard : Nat.card K = (2 ^ e) ^ t.order := by
    change Nat.card (GaloisField 2 n) = (2 ^ e) ^ t.order
    rw [GaloisField.card 2 n hn]
    change 2 ^ n = (2 ^ e) ^ t.order
    rw [show n = t.order * e from rfl, Nat.mul_comm t.order e, pow_mul]
  let σ : K →+* K := iterateFrobenius K 2 e
  have hσ : ∀ c : K, σ c = c ^ (2 ^ e) := fun c => iterateFrobenius_def 2 e c
  have hamb := exceptional_ambient_twisted_Frobenius_fixed_normalizer t (p := 2) (f := e)
    Nat.prime_two (by omega : 1 ≤ e) K hKcard σ hσ GGL Fr hFr2
  have hmap := map_baseChangeGL_graphFixedRootGroup_eq t (p := 2) (f := e) Nat.prime_two
    (by omega : 1 ≤ e) K hKcard σ hσ (algebraMap K GGL) hFr2 hFrsurj
  have hdecomp : (twistedFixedGroup t GGL Fr : Set (ModGL t.tag GGL)) =
      (graphFixedTorus t GGL Fr : Set (ModGL t.tag GGL)) *
        (graphFixedRootGroup t GGL Fr : Set (ModGL t.tag GGL)) := by
    rw [hamb.1, hmap]
  have hder : ⁅twistedFixedGroup t GGL Fr, twistedFixedGroup t GGL Fr⁆ =
      graphFixedRootGroup t GGL Fr := by
    rw [hamb.2.2.2.2.1, hmap]
  have hfixR : S.D.fix = twistedFixedGroup t GGL Fr := by
    unfold LangDatum.fix twistedFixedGroup
    rw [hΦeq]
  have hmapΓ : ⁅twistedFixedGroup t GGL Fr, twistedFixedGroup t GGL Fr⁆ =
      S.D.Γ.map (MulAut.conj S.D.g0).toMonoidHom := by
    simpa [hfixR] using (LangDatum.map_conj_Γ S.D).symm
  refine ⟨γ0, z0, hγ0root, hz0mem, ?_, ?_, fun r hr => ?_⟩
  ·
    show ((rootSubgroup t.tag GGL γ0).map (MulAut.conj z0).toMonoidHom).map S.D.step =
      (rootSubgroup t.tag GGL γ0).map (MulAut.conj z0).toMonoidHom
    have hcomp : S.D.step.comp (MulAut.conj z0).toMonoidHom =
        ((MulAut.conj z0).toMonoidHom).comp S.D.Φ := by
      refine MonoidHom.ext fun x => ?_
      change S.D.step (z0 * x * z0⁻¹) = z0 * S.D.Φ x * z0⁻¹
      rw [hz0eq]
      exact step_conj_g0_inv S.D x
    calc ((rootSubgroup t.tag GGL γ0).map (MulAut.conj z0).toMonoidHom).map S.D.step
        = (rootSubgroup t.tag GGL γ0).map (S.D.step.comp (MulAut.conj z0).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = (rootSubgroup t.tag GGL γ0).map (((MulAut.conj z0).toMonoidHom).comp S.D.Φ) := by
          rw [hcomp]
      _ = ((rootSubgroup t.tag GGL γ0).map S.D.Φ).map (MulAut.conj z0).toMonoidHom := by
          rw [Subgroup.map_map]
      _ = (rootSubgroup t.tag GGL γ0).map (MulAut.conj z0).toMonoidHom := by
          rw [hΦeq, map_twistHom_rootSubgroup t GGL hFrsurj hγ0root, hγ0perm]
  ·
    show ((rootSubgroup t.tag GGL (-γ0)).map (MulAut.conj z0).toMonoidHom).map S.D.step =
      (rootSubgroup t.tag GGL (-γ0)).map (MulAut.conj z0).toMonoidHom
    have hcomp : S.D.step.comp (MulAut.conj z0).toMonoidHom =
        ((MulAut.conj z0).toMonoidHom).comp S.D.Φ := by
      refine MonoidHom.ext fun x => ?_
      change S.D.step (z0 * x * z0⁻¹) = z0 * S.D.Φ x * z0⁻¹
      rw [hz0eq]
      exact step_conj_g0_inv S.D x
    calc ((rootSubgroup t.tag GGL (-γ0)).map (MulAut.conj z0).toMonoidHom).map S.D.step
        = (rootSubgroup t.tag GGL (-γ0)).map (S.D.step.comp (MulAut.conj z0).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = (rootSubgroup t.tag GGL (-γ0)).map (((MulAut.conj z0).toMonoidHom).comp S.D.Φ) := by
          rw [hcomp]
      _ = ((rootSubgroup t.tag GGL (-γ0)).map S.D.Φ).map (MulAut.conj z0).toMonoidHom := by
          rw [Subgroup.map_map]
      _ = (rootSubgroup t.tag GGL (-γ0)).map (MulAut.conj z0).toMonoidHom := by
          rw [hΦeq, map_twistHom_rootSubgroup t GGL hFrsurj (IsRoot.neg hγ0root), hnegperm]
  ·
    have hxfix : S.D.g0 * r * S.D.g0⁻¹ ∈ S.D.fix := by
      rw [← LangDatum.map_conj_model S.D]
      exact ⟨r, hr, by simp [MulAut.conj_apply]⟩
    have hxR : S.D.g0 * r * S.D.g0⁻¹ ∈ twistedFixedGroup t GGL Fr := hfixR ▸ hxfix
    have hxprod : S.D.g0 * r * S.D.g0⁻¹ ∈
        (graphFixedTorus t GGL Fr : Set (ModGL t.tag GGL)) *
          (graphFixedRootGroup t GGL Fr : Set (ModGL t.tag GGL)) := by
      rw [← hdecomp]
      exact hxR
    obtain ⟨d, hdT, h, hhH, hdh⟩ := Set.mem_mul.mp hxprod
    have hdTorus : d ∈ torusGroup t.tag GGL := hdT.1
    have hdR : d ∈ twistedFixedGroup t GGL Fr := hdT.2
    have hhComm : h ∈ ⁅twistedFixedGroup t GGL Fr, twistedFixedGroup t GGL Fr⁆ :=
      hder.symm ▸ hhH
    have hconjR : d * h * d⁻¹ ∈
        ⁅twistedFixedGroup t GGL Fr, twistedFixedGroup t GGL Fr⁆ := by
      simpa using rckConj_mem_commutator (M := twistedFixedGroup t GGL Fr) (h := d⁻¹)
        ((twistedFixedGroup t GGL Fr).inv_mem hdR) hhComm
    have hconjMap : d * h * d⁻¹ ∈ S.D.Γ.map (MulAut.conj S.D.g0).toMonoidHom :=
      hmapΓ ▸ hconjR
    obtain ⟨u, huΓ, hu_eq⟩ := Subgroup.mem_map.mp hconjMap
    let t' : ModGL t.tag GGL := S.D.g0⁻¹ * d * S.D.g0
    let u1 : ModGL t.tag GGL := S.D.g0⁻¹ * (d * h * d⁻¹) * S.D.g0
    have hu1eq : u1 = u := by
      change S.D.g0⁻¹ * (d * h * d⁻¹) * S.D.g0 = u
      rw [← hu_eq]
      change S.D.g0⁻¹ * (S.D.g0 * u * S.D.g0⁻¹) * S.D.g0 = u
      group
    have hu1Γ : u1 ∈ S.Γ := by
      change u1 ∈ S.D.Γ
      rw [hu1eq]
      exact huΓ
    have hr_eq : r = u1 * t' := by
      have hx : d * h = S.D.g0 * r * S.D.g0⁻¹ := hdh
      rw [show r = S.D.g0⁻¹ * (d * h) * S.D.g0 by rw [hx]; group]
      change S.D.g0⁻¹ * (d * h) * S.D.g0 =
        (S.D.g0⁻¹ * (d * h * d⁻¹) * S.D.g0) * (S.D.g0⁻¹ * d * S.D.g0)
      group
    have hu1invr : u1⁻¹ * r = t' := by
      rw [hr_eq]
      group
    have hdNγ : d ∈ Subgroup.normalizer
        ((rootSubgroup t.tag GGL γ0 : Subgroup (ModGL t.tag GGL)) : Set (ModGL t.tag GGL)) :=
      RootCentExc.torusGroup_le_normalizer_rootSubgroup (K := GGL) hγ0root hdTorus
    have hdNneg : d ∈ Subgroup.normalizer
        ((rootSubgroup t.tag GGL (-γ0) : Subgroup (ModGL t.tag GGL)) : Set (ModGL t.tag GGL)) :=
      RootCentExc.torusGroup_le_normalizer_rootSubgroup (K := GGL) (IsRoot.neg hγ0root) hdTorus
    have ht'γ : t' ∈ Subgroup.normalizer
        (conjSub z0 (rootSubgroup t.tag GGL γ0) : Set (ModGL t.tag GGL)) := by
      have hAB : conjSub S.D.g0 (conjSub z0 (rootSubgroup t.tag GGL γ0)) =
          rootSubgroup t.tag GGL γ0 := by
        rw [hz0eq, conjSub_conjSub_inv]
      exact rckMem_normalizer_of_conjSub_eq hAB hdNγ
    have ht'neg : t' ∈ Subgroup.normalizer
        (conjSub z0 (rootSubgroup t.tag GGL (-γ0)) : Set (ModGL t.tag GGL)) := by
      have hAB : conjSub S.D.g0 (conjSub z0 (rootSubgroup t.tag GGL (-γ0))) =
          rootSubgroup t.tag GGL (-γ0) := by
        rw [hz0eq, conjSub_conjSub_inv]
      exact rckMem_normalizer_of_conjSub_eq hAB hdNneg
    refine ⟨u1, hu1Γ, ?_, ?_⟩
    · rw [hu1invr]
      exact ht'γ
    · rw [hu1invr]
      exact ht'neg

end CFSG.StandardType.RCKRP
