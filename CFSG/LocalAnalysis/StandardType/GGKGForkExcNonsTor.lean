module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNSylow
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.SylowFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.StandardType

namespace ExcNons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

private lemma ggKGNt_mul_pow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x y : G}
    (hcomm : Commute x y) {a b : ℕ} (hx : x ^ p ^ a = 1) (hy : y ^ p ^ b = 1) :
    (x * y) ^ p ^ (a + b) = 1 := by
  have hx' : x ^ p ^ (a + b) = 1 := by
    rw [show p ^ (a + b) = p ^ a * p ^ b from pow_add p a b, pow_mul, hx, one_pow]
  have hy' : y ^ p ^ (a + b) = 1 := by
    rw [show p ^ (a + b) = p ^ b * p ^ a by rw [pow_add, mul_comm], pow_mul, hy, one_pow]
  rw [hcomm.mul_pow (p ^ (a + b)), hx', hy', mul_one]

private lemma ggKGNt_inv_pow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x : G} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x⁻¹ ^ p ^ k = 1 := by
  rw [inv_pow, hx, inv_one]

private def ggKGNt_pTorsion {G : Type*} [Group G] (p : ℕ) (TF : Subgroup G)
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) : Subgroup G where
  carrier := {x | x ∈ TF ∧ ∃ k : ℕ, x ^ p ^ k = 1}
  one_mem' := ⟨TF.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxT, k, hxk⟩ ⟨hyT, l, hyl⟩
    exact ⟨TF.mul_mem hxT hyT, k + l,
      ggKGNt_mul_pow_pow_eq_one (hcomm x hxT y hyT) hxk hyl⟩
  inv_mem' := by
    rintro x ⟨hxT, k, hxk⟩
    exact ⟨TF.inv_mem hxT, k, ggKGNt_inv_pow_pow_eq_one hxk⟩

private lemma ggKGNt_pTorsion_le {G : Type*} [Group G] {p : ℕ} {TF : Subgroup G}
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) :
    ggKGNt_pTorsion p TF hcomm ≤ TF := fun _ hx => hx.1

private lemma ggKGNt_pTorsion_isPGroup {G : Type*} [Group G] {p : ℕ} {TF : Subgroup G}
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) :
    IsPGroup p (ggKGNt_pTorsion p TF hcomm) := by
  intro x
  obtain ⟨-, k, hk⟩ := x.2
  exact ⟨k, Subtype.ext hk⟩

private def ggKGNt_pTorsionSub {G : Type*} [Group G] (p : ℕ) (TF : Subgroup G)
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) : Subgroup G where
  carrier := {x | x ^ p = 1 ∧ x ∈ TF}
  one_mem' := ⟨by simp, TF.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxp, hxT⟩ ⟨hyp, hyT⟩
    refine ⟨?_, TF.mul_mem hxT hyT⟩
    rw [(hcomm x hxT y hyT).mul_pow, hxp, hyp, mul_one]
  inv_mem' := by
    rintro x ⟨hxp, hxT⟩
    exact ⟨by rw [inv_pow, hxp, inv_one], TF.inv_mem hxT⟩

theorem exists_nons_frame_conj_into_torus {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1)
    (hord : (Nat.card (adjointGroup τ K)).factorization p ≤
      τ.rank * padicValNat p (Nat.card K + 1) + 1) {m : ℕ}
    (hW : ∀ {C : Type} [CommGroup C], Nat.card C = p → ∀ {w : WeylGroup τ}, orderOf w = p →
      Nat.card {a : Fin τ.rank → C // mactC (Atw w) a = a} ≤ p ^ m)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) (hr : p ^ (m + 2) ≤ Nat.card E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g0 : ModGL τ (AlgebraicClosure K))
      (w : WeylGroup τ) (y : adjointGroup τ K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup τ (AlgebraicClosure K) ∧ ExcIsLongest τ w ∧
      Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
      ∀ x ∈ E,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y⁻¹ * x * y : adjointGroup τ K) : ModGL τ K) * g0 ∈
          twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
            (Units.map (entrywiseHom Fr)) := by
  classical
  have hp3 : 3 < p := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  set a : ℕ := padicValNat p (Nat.card K + 1) with ha
  obtain ⟨w0, hw0⟩ : ∃ w0 : WeylGroup τ, ∀ u : Fin τ.rank → ℤ, w0 • u = -u := by
    rcases hτ with rfl | rfl
    · exact exists_weyl_neg_E7
    · exact exists_weyl_neg_E8
  obtain ⟨d, hτ'⟩ : ∃ d : ℕ, (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1) := by
    rcases hτ with rfl | rfl
    · exact ⟨2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have hw0longest : ExcIsLongest τ w0 := by
    intro α _ hpos i
    rw [hw0]
    show -α i ≤ 0
    exact neg_nonpos.2 (hpos i)
  set M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := -1 with hM
  have hw0M : ∀ u, w0 • u = M.mulVec u := by
    intro u
    rw [hw0, hM, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hMfac : (M.charpoly.eval (Nat.card K : ℤ)).natAbs = (Nat.card K + 1) ^ τ.rank := by
    rw [hM, CFSG.LieType.SeitzGeneration.natAbs_eval_charpoly]
    exact natAbs_det_negOne_sub τ.rank (Nat.card K)
  have hMsq : M ^ 2 = 1 := by rw [hM]; exact negOne_sq τ.rank
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [← Int.natAbs_ne_zero, hMfac]
    exact pow_ne_zero _ (Nat.succ_ne_zero _)
  have hMp : ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p = τ.rank * a := by
    rw [hMfac, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [Nat.factorization_def (Nat.card K + 1) hp, ← ha]
  by_cases hord0 : (Nat.card (adjointGroup τ K)).factorization p ≤ τ.rank * a
  · have hordS : (Nat.card (adjointGroup τ K)).factorization p ≤
        ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p := by
      rw [hMp]; exact hord0
    obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.exists_langFrame_untwisted_sylow
        d hτ' K hp hp3 w0 hw0M (by norm_num : 2 ≠ 0) hMsq hev hordS
    obtain ⟨c, hc⟩ := hconj E (fun x hx => hE.2 x hx)
    refine ⟨Fr, g0, w0, c⁻¹, hFr, hg0C, hw0longest, hg0, ?_⟩
    intro x hx
    have hx' := hc x hx
    rw [Subgroup.mem_map] at hx'
    obtain ⟨t, ht, htx⟩ := hx'
    change g0 * t * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) at htx
    have hgoal : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((c⁻¹)⁻¹ * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 ∈
        twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w0)
          (Units.map (entrywiseHom Fr)) := by
      rw [inv_inv]
      rw [show g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 = t by
          rw [← htx]; group]
      exact ht
    exact hgoal
  · have hfact : (Nat.card (adjointGroup τ K)).factorization p = τ.rank * a + 1 := by omega
    have hordS : (Nat.card (adjointGroup τ K)).factorization p ≤
        ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p + 1 := by
      rw [hMp]; omega
    obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_langFrame_untwisted
        d hτ' K hp hp3 w0 hw0M (by norm_num : 2 ≠ 0) hMsq hev hordS
    let L := AlgebraicClosure K
    let φ : adjointGroup τ K →* ModGL τ L :=
      (MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype)
    let TF : Subgroup (adjointGroup τ K) :=
      (twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
        (Units.map (entrywiseHom Fr))).comap φ
    have hTF_mem : ∀ x : adjointGroup τ K, x ∈ TF ↔
        g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0 ∈
          twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
            (Units.map (entrywiseHom Fr)) := by
      intro x
      show ((MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) (x : ModGL τ K)) ∈
          twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
            (Units.map (entrywiseHom Fr))) ↔ _
      rw [MulAut.conj_apply, inv_inv]
    haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
    haveI hTcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
        (Units.map (entrywiseHom Fr))) :=
      isMulCommutative_twistedTorusOf Fr w0 hw0
    have hφinj : Function.Injective φ :=
      (MulAut.conj g0⁻¹).injective.comp
        ((baseChangeGL_injective (algebraMap K L)).comp (Subgroup.subtype_injective _))
    have hcommTF : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y := by
      intro x hx y hy
      show x * y = y * x
      apply hφinj
      rw [map_mul, map_mul]
      exact setLike_mul_comm ((hTF_mem x).1 hx) ((hTF_mem y).1 hy)
    let Q : Subgroup (adjointGroup τ K) := ggKGNt_pTorsion p TF hcommTF
    have hQpg : IsPGroup p Q := ggKGNt_pTorsion_isPGroup hcommTF
    have hQle : Q ≤ TF := ggKGNt_pTorsion_le hcommTF
    let ET : Subgroup (adjointGroup τ K) := ggKGNt_pTorsionSub p TF hcommTF
    have hET_mem : ∀ x : adjointGroup τ K, x ∈ ET ↔ x ^ p = 1 ∧
        g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0 ∈
          twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
            (Units.map (entrywiseHom Fr)) := by
      intro x
      show (x ^ p = 1 ∧ x ∈ TF) ↔ (x ^ p = 1 ∧ _)
      rw [hTF_mem x]
    obtain ⟨S⟩ : Nonempty (Sylow p (adjointGroup τ K)) := inferInstance
    obtain ⟨c, E0, hE0S, hE0card, hE0torus⟩ := hconj (S : Subgroup (adjointGroup τ K)) S.isPGroup'
    have hScard : Nat.card (S : Subgroup (adjointGroup τ K)) = p ^ (τ.rank * a + 1) := by
      have h1 := Sylow.card_eq_multiplicity S
      rw [hfact] at h1
      exact h1
    have hE0card_ge : p ^ (τ.rank * a) ≤ Nat.card E0 := by
      rw [hScard, pow_succ'] at hE0card
      exact Nat.le_of_mul_le_mul_left hE0card hp.pos
    have hE0pg : IsPGroup p E0 := S.isPGroup'.to_le hE0S
    have hE1Q : ∀ x ∈ E0, c * x * c⁻¹ ∈ Q := by
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [hTF_mem]
        have hx' := hE0torus x hx
        rw [Subgroup.mem_map] at hx'
        obtain ⟨t, ht, htx⟩ := hx'
        change g0 * t * g0⁻¹ = baseChangeGL (algebraMap K L)
          ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) at htx
        rw [show g0⁻¹ * baseChangeGL (algebraMap K L)
              ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 = t by
            rw [← htx]; group]
        exact ht
      · obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hE0pg ⟨x, hx⟩
        have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
        refine ⟨k, ?_⟩
        have hm : (MulAut.conj c) (x ^ p ^ k) = 1 := by rw [hk', map_one]
        rw [map_pow] at hm
        simpa [MulAut.conj_apply] using hm
    have hQcard_ge : p ^ (τ.rank * a) ≤ Nat.card Q := by
      have hinj : Function.Injective (fun x : E0 =>
          (⟨c * (x : adjointGroup τ K) * c⁻¹, hE1Q (x : adjointGroup τ K) x.2⟩ : Q)) := by
        intro x y hxy
        have h := congrArg (fun z : Q => (z : adjointGroup τ K)) hxy
        have hx' : c⁻¹ * (c * (x : adjointGroup τ K) * c⁻¹) * c = (x : adjointGroup τ K) := by
          group
        have hy' : c⁻¹ * (c * (y : adjointGroup τ K) * c⁻¹) * c = (y : adjointGroup τ K) := by
          group
        have h3 := congrArg (fun z => c⁻¹ * z * c) h
        rw [hx', hy'] at h3
        exact Subtype.ext h3
      have hle : Nat.card E0 ≤ Nat.card Q := Nat.card_le_card_of_injective _ hinj
      exact hE0card_ge.trans hle
    obtain ⟨P, hQleP⟩ := IsPGroup.exists_le_sylow hQpg
    have hPpg : IsPGroup p (P : Subgroup (adjointGroup τ K)) := Sylow.isPGroup' P
    have hPcard : Nat.card (P : Subgroup (adjointGroup τ K)) = p ^ (τ.rank * a + 1) := by
      have h1 := Sylow.card_eq_multiplicity P
      rw [hfact] at h1
      exact h1
    obtain ⟨Se, hESe⟩ := IsPGroup.exists_le_sylow hE.isPGroup
    haveI : MulAction.IsPretransitive (adjointGroup τ K) (Sylow p (adjointGroup τ K)) :=
      Sylow.isPretransitive_of_finite
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (adjointGroup τ K) P Se
    have hSmap : (Se : Subgroup (adjointGroup τ K)) =
        (P : Subgroup (adjointGroup τ K)).map (MulAut.conj y).toMonoidHom := by
      rw [← hy, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hconjE : ∀ x ∈ E, y⁻¹ * x * y ∈ (P : Subgroup (adjointGroup τ K)) := by
      intro x hx
      have hxSe : x ∈ (Se : Subgroup (adjointGroup τ K)) := hESe hx
      rw [hSmap, Subgroup.mem_map] at hxSe
      obtain ⟨z, hzP, hzx⟩ := hxSe
      have hzx' : y * z * y⁻¹ = x := by simpa [MulAut.conj_apply] using hzx
      have hz : y⁻¹ * x * y = z := by rw [← hzx']; group
      rwa [hz]
    let E' : Subgroup (adjointGroup τ K) := E.map (MulAut.conj y⁻¹).toMonoidHom
    have hE'_P : E' ≤ (P : Subgroup (adjointGroup τ K)) := by
      intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      simpa [MulAut.conj_apply] using hconjE e he
    have hE'card : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
    have hE'el : IsElemAbelian p E' := IsElemAbelian.map hE (MulAut.conj y⁻¹).toMonoidHom
    have hE'_Q : E' ≤ Q := by
      by_contra hcon
      obtain ⟨u, huE', huQ⟩ := Set.not_subset.1 hcon
      have huP : u ∈ (P : Subgroup (adjointGroup τ K)) := hE'_P huE'
      have hQP : Q ≠ (P : Subgroup (adjointGroup τ K)) := by
        intro hEq
        exact hcon (hE'_P.trans (le_of_eq hEq.symm))
      have hrel_mul : (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).index * Nat.card Q =
          Nat.card (P : Subgroup (adjointGroup τ K)) := by
        have h := (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).card_mul_index
        rw [show Nat.card (Q.subgroupOf (P : Subgroup (adjointGroup τ K))) = Nat.card Q from
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleP).toEquiv] at h
        rw [mul_comm]
        exact h
      have hidx_dvd : (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).index ∣
          p ^ (τ.rank * a + 1) :=
        ⟨Nat.card Q, (hrel_mul.trans hPcard).symm⟩
      obtain ⟨k, _hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).1 hidx_dvd
      have hidx_ne1 : (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).index ≠ 1 := by
        intro h1
        apply hQP
        have hle' : (P : Subgroup (adjointGroup τ K)) ≤ Q := by
          have htop : Q.subgroupOf (P : Subgroup (adjointGroup τ K)) = ⊤ :=
            Subgroup.index_eq_one.1 h1
          intro p hp
          have hp' : (⟨p, hp⟩ : (P : Subgroup (adjointGroup τ K))) ∈
              Q.subgroupOf (P : Subgroup (adjointGroup τ K)) := by rw [htop]; trivial
          exact (Subgroup.mem_subgroupOf).1 hp'
        exact le_antisymm hQleP hle'
      have hk_ne0 : k ≠ 0 := by
        intro hk0
        apply hidx_ne1
        rw [hk_eq, hk0, pow_zero]
      have hk_le1 : k ≤ 1 := by
        have hmul := hrel_mul
        rw [hk_eq, hPcard] at hmul
        have hD_pos : 0 < p ^ (τ.rank * a) := by positivity
        have h2 : p ^ k * p ^ (τ.rank * a) ≤ p ^ 1 * p ^ (τ.rank * a) := by
          calc p ^ k * p ^ (τ.rank * a)
              ≤ p ^ k * Nat.card Q := Nat.mul_le_mul_left _ hQcard_ge
            _ = p ^ (τ.rank * a + 1) := hmul
            _ = p ^ 1 * p ^ (τ.rank * a) := by rw [pow_succ', pow_one]
        exact (Nat.pow_le_pow_iff_right hp.one_lt).1
          (Nat.le_of_mul_le_mul_right h2 hD_pos)
      have hk1 : k = 1 := by omega
      have hidxp : (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).index = p := by
        rw [hk_eq, hk1, pow_one]
      have hQPrel : Q.relIndex (P : Subgroup (adjointGroup τ K)) = p := by
        rw [show Q.relIndex (P : Subgroup (adjointGroup τ K)) =
              (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).index from rfl, hidxp]
      have hQnorm : (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).Normal := by
        apply Subgroup.normal_of_index_eq_minFac_card
        rw [hidxp, hPcard]
        rw [show (p ^ (τ.rank * a + 1)).minFac = p from by
          rw [Nat.pow_minFac (by omega : τ.rank * a + 1 ≠ 0), hp.minFac_eq]]
      have hPnormQ : (P : Subgroup (adjointGroup τ K)) ≤
          Subgroup.normalizer (Q : Set (adjointGroup τ K)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQleP).1 hQnorm
      have hET_le_Q : ET ≤ Q := by
        intro x hx
        have hx' : x ^ p = 1 ∧ x ∈ TF := hx
        exact ⟨hx'.2, ⟨1, by rw [pow_one]; exact hx'.1⟩⟩
      have hstep : ∀ v ∈ Subgroup.normalizer (Q : Set (adjointGroup τ K)),
          ∀ e ∈ ET, v * e * v⁻¹ ∈ ET := by
        intro v hv e he
        have heQ : e ∈ Q := hET_le_Q he
        have hmemQ : v * e * v⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hv e).1 heQ
        have hep : e ^ p = 1 := ((show e ∈ ET ↔ e ^ p = 1 ∧ e ∈ TF from Iff.rfl).1 he).1
        refine ⟨?_, hQle hmemQ⟩
        have hm : (MulAut.conj v) (e ^ p) = 1 := by rw [hep, map_one]
        rw [map_pow] at hm
        simpa [MulAut.conj_apply] using hm
      have hu_norm_ET : u ∈ Subgroup.normalizer (ET : Set (adjointGroup τ K)) := by
        have huPnormQ : u ∈ Subgroup.normalizer (Q : Set (adjointGroup τ K)) := hPnormQ huP
        rw [Subgroup.mem_normalizer_iff]
        intro e
        constructor
        · exact hstep u huPnormQ e
        · intro he
          have h := hstep u⁻¹
            ((Subgroup.normalizer (Q : Set (adjointGroup τ K))).inv_mem huPnormQ)
            (u * e * u⁻¹) he
          simpa [mul_assoc] using h
      have hupQ : u ^ p ∈ Q := by
        haveI : (Q.subgroupOf (P : Subgroup (adjointGroup τ K))).Normal := hQnorm
        have hmem := Subgroup.pow_index_mem (Q.subgroupOf (P : Subgroup (adjointGroup τ K)))
          (⟨u, huP⟩ : (P : Subgroup (adjointGroup τ K)))
        rw [hidxp] at hmem
        exact (Subgroup.mem_subgroupOf).1 (by simpa using hmem)
      have hup_cent : u ^ p ∈ Subgroup.centralizer (ET : Set (adjointGroup τ K)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact ((hcommTF (u ^ p) (hQle hupQ) e (hQle (hET_le_Q he))).eq).symm
      have hnc : u ∉ Subgroup.centralizer (ET : Set (adjointGroup τ K)) := by
        intro huc
        let F : ExcFrame τ K p ET := {
          D := LangDatum.ofFrobenius Fr (Nat.card K) hFr w0 hg0C hg0
          w := w0
          q_eq := rfl
          frob := ⟨Fr, hFr, fun _ => rfl⟩
          n_eq := rfl
          mem_iff := hET_mem }
        have hτ4 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
          rcases hτ with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
        have hwF : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨
            (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w) :=
          Or.inr ⟨hpq, hw0longest⟩
        have hcent := ggKGExc_centralizer_eq (τ := τ) (K := K) (p := p) (E := ET)
          hτ4 hp (by omega) (fun _ => hp5) F hwF u
        have huTF : u ∈ TF := (hTF_mem u).2 (hcent.1 huc)
        have huQ' : u ∈ Q := by
          refine ⟨huTF, ?_⟩
          obtain ⟨j, hj⟩ := IsPGroup.exists_pow_pow_eq_one hPpg ⟨u, huP⟩
          exact ⟨j, by simpa using congrArg Subtype.val hj⟩
        exact huQ huQ'
      have hfix := card_fixed_le_pow_nons (τ := τ) hτ (K := K) (p := p) hp hp5 hpq
        (m := m) hW Fr hFr g0 hg0C w0 hw0longest hg0 hET_mem hu_norm_ET hup_cent hnc
      have hcard_inf_le : Nat.card ↥(E' ⊓ Q) ≤ p ^ m := by
        have hval : ∀ x : ↥(E' ⊓ Q),
            (x : adjointGroup τ K) ∈ ET ∧ u * (x : adjointGroup τ K) = (x : adjointGroup τ K)
              * u := by
          intro x
          refine ⟨?_, ?_⟩
          · have hxE' : (x : adjointGroup τ K) ∈ E' := x.2.1
            have hxp : (x : adjointGroup τ K) ^ p = 1 := hE'el.2 _ hxE'
            exact ⟨hxp, hQle x.2.2⟩
          · have hcomm : (x : adjointGroup τ K) * u = u * (x : adjointGroup τ K) := by
              have := (isMulCommutative_iff.1 hE'el.1)
                ⟨(x : adjointGroup τ K), x.2.1⟩ ⟨u, huE'⟩
              simpa using congrArg Subtype.val this
            exact hcomm.symm
        have hinj : Function.Injective (fun x : ↥(E' ⊓ Q) =>
            (⟨(x : adjointGroup τ K), (hval x).1, (hval x).2⟩ :
              {e : adjointGroup τ K // e ∈ ET ∧ u * e = e * u})) := by
          intro x z hxz
          exact Subtype.ext (by simpa using congrArg Subtype.val hxz)
        exact (Nat.card_le_card_of_injective _ hinj).trans hfix
      have hrel_le : (E' ⊓ Q).relIndex E' ≤ p := by
        have h1 : (E' ⊓ Q).relIndex E' = Q.relIndex E' := by
          rw [inf_comm, Subgroup.inf_relIndex_right]
        rw [h1]
        have hQpos : Q.relIndex (P : Subgroup (adjointGroup τ K)) ≠ 0 := by
          rw [hQPrel]; exact hp.pos.ne'
        have h2 := Subgroup.relIndex_le_of_le_right (H := Q) (K := E')
          (L := (P : Subgroup (adjointGroup τ K))) hE'_P hQpos
        rwa [hQPrel] at h2
      have hcard_index : Nat.card E' ≤ p * Nat.card ↥(E' ⊓ Q) := by
        have hmul := Subgroup.relIndex_mul_card (H := E' ⊓ Q) (K := E')
        have hmul' : (E' ⊓ Q).relIndex E' * Nat.card ↥(E' ⊓ Q) = Nat.card E' := by
          rw [show (E' ⊓ Q) ⊓ E' = E' ⊓ Q from inf_eq_left.2 inf_le_left] at hmul
          exact hmul
        rw [← hmul']
        exact Nat.mul_le_mul_right _ hrel_le
      have hE'card_le : Nat.card E' ≤ p ^ (m + 1) := by
        calc Nat.card E' ≤ p * Nat.card ↥(E' ⊓ Q) := hcard_index
          _ ≤ p * p ^ m := Nat.mul_le_mul_left p hcard_inf_le
          _ = p ^ (m + 1) := by rw [pow_succ']
      have hr' : p ^ (m + 2) ≤ Nat.card E' := by rw [hE'card]; exact hr
      exact absurd (hr'.trans hE'card_le)
        (Nat.not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by omega)))
    have hE'_TF : E' ≤ TF := hE'_Q.trans hQle
    refine ⟨Fr, g0, w0, y, hFr, hg0C, hw0longest, hg0, ?_⟩
    intro x hx
    have hxE' : y⁻¹ * x * y ∈ E' := by
      rw [Subgroup.mem_map]
      refine ⟨x, hx, ?_⟩
      change y⁻¹ * x * (y⁻¹)⁻¹ = y⁻¹ * x * y
      rw [inv_inv]
    exact (hTF_mem _).1 (hE'_TF hxE')

end ExcNons

end CFSG.StandardType

end
