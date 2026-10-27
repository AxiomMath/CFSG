module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def HessF {K : Type} [Group K] (c y : K) (F : Subgroup K) : Prop :=
  CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ c ∈ F ∧
    y ∈ Subgroup.normalizer (F : Set K) ∧
    (∀ f ∈ F, y * f * y⁻¹ * f⁻¹ ∈ Subgroup.zpowers c) ∧
    (∃ f ∈ F, y * f * y⁻¹ * f⁻¹ ≠ 1) ∧
    (∀ f ∈ F, f ≠ 1 → ∃ n ∈ Subgroup.normalizer (F : Set K), n * c * n⁻¹ = f) ∧
    Nonempty (Sec4.autIn (⊤ : Subgroup K) F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

section Transport

variable {K K' : Type} [Group K] [Group K']

theorem HessF.map (e : K ≃* K') {c y : K} {F : Subgroup K} (h : HessF c y F) :
    HessF (e c) (e y) (F.map e.toMonoidHom) := by
  obtain ⟨hab, hcard, hcF, hyN, hcomm, hnt, htrans, hAut⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 e.toMonoidHom F hab
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · exact Subgroup.mem_map_of_mem _ hcF
  · rw [← Subgroup.map_normalizer_eq_of_bijective F e.bijective]
    exact Subgroup.mem_map_of_mem _ hyN
  · rintro _ ⟨f, hf, rfl⟩
    have h2 : e.toMonoidHom (y * f * y⁻¹ * f⁻¹) ∈
        (Subgroup.zpowers c).map e.toMonoidHom := Subgroup.mem_map_of_mem _ (hcomm f hf)
    rw [MonoidHom.map_zpowers] at h2
    simpa using h2
  · obtain ⟨f, hf, hne⟩ := hnt
    refine ⟨e f, Subgroup.mem_map_of_mem _ hf, fun h1 => hne ?_⟩
    apply e.injective
    simpa using h1
  · rintro _ ⟨f, hf, rfl⟩ hf1
    have hf1' : f ≠ 1 := fun h1 => hf1 (by simp [h1])
    obtain ⟨n, hn, hnf⟩ := htrans f hf hf1'
    refine ⟨e n, ?_, ?_⟩
    · rw [← Subgroup.map_normalizer_eq_of_bijective F e.bijective]
      exact Subgroup.mem_map_of_mem _ hn
    · simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_inv, ← map_mul, hnf]
  · obtain ⟨φ⟩ := hAut
    exact ⟨(Sec4.Sporadic.autInTopCongr e F).symm.trans φ⟩

end Transport

open CFSG.Assembly.RankThreeEven (projSL)

structure PairData {K : Type} [Group K] (c y : K) : Prop where
  c3 : c ^ 3 = 1
  y3 : y ^ 3 = 1
  c1 : c ≠ 1
  y1 : y ≠ 1
  comm : y * c = c * y
  X : ∃ Xk : Subgroup K, Xk ≤ Subgroup.centralizer ({y} : Set K) ∧ Group.IsPerfect Xk ∧
    (Xk.subgroupOf (Subgroup.centralizer ({y} : Set K))).IsSubnormal ∧ c ∈ Xk ∧
    ∃ (p m : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ m ∧
      ∃ φ : Xk →* projSL 2 (GaloisField p m), Function.Surjective φ

section Std


open CFSG.RankThree.PartTwo.Sec19 (C0 Asub Bsub D4Par asubEquiv bsubEquiv)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof (sl2Three)
open CFSG.LieType.Chevalley (fixSubfield)

@[expose] noncomputable def zStd {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}
    (P : D4Par n X σ) : C0 σ :=
  ((asubEquiv P (sl2Three X) : Asub σ) : C0 σ)

@[expose] noncomputable def tStd {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}
    (P : D4Par n X σ) : C0 σ :=
  ((bsubEquiv P (sl2Three (fixSubfield σ)) : Bsub σ) : C0 σ)

@[expose] def KF_D4_HESS : Prop :=
  ∀ (n : ℕ) (X : Type) [Field X] [Finite X] (σ : X ≃+* X) (P : D4Par n X σ),
    ∃ F : Subgroup (C0 σ), HessF (zStd P) (tStd P) F

end Std

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
