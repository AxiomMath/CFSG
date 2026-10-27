module

public import CFSG.Sporadic.SuzI301.Spec
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs

public noncomputable section

namespace CFSG.Sporadic.SuzI301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.HardMathSupport.Dickson.I271 CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.LieType.Multipliers.U43 (X₀)

private def pp3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

private theorem valid_twistedA_three : (TauCeti.LieTypeIndex.twistedA 3 pp3).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨⟨by norm_num, fun h => absurd h (by norm_num)⟩, id⟩

theorem catalogIs_isU4of_three {T : Type} [Group T] (e : T ≃* X₀) :
    catalogIs T (isU4of 3) := by
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 pp3 valid_twistedA_three
    (G := (TauCeti.CFSGIndex.lie ⟨.twistedA 3 pp3, valid_twistedA_three⟩).Group) (MulEquiv.refl _)
  obtain ⟨b⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ (Or.inl ⟨by decide, hc⟩)
  refine ⟨.lie ⟨.twistedA 3 pp3, valid_twistedA_three⟩, ?_, ⟨e.trans b.symm⟩⟩
  show pp3.card = 3
  rw [TauCeti.PrimePower.card_def]
  norm_num [pp3]


@[expose] def Q1 : Subgroup (Equiv.Perm (Fin 1782)) := coord_qVec.Q

private theorem Q1_le_suzM : Q1 ≤ suzM :=
  fun _ hg => (invE_le_centM (by norm_num) (Q_le_invE hg)).2

private theorem B1_le_invE : B1 ≤ invE 1 := by
  obtain ⟨hd, hb2, hb3, -⟩ := gens_mem
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  exacts [hd, hb2, hb3]

private theorem B1_le_suzM : B1 ≤ suzM :=
  fun _ hg => (invE_le_centM (by norm_num) (B1_le_invE hg)).2

theorem row_hR : IsExtraSpec2 (Q1.subgroupOf suzM) ∧
    Nat.card (Q1.subgroupOf suzM) = 2 ^ Row.suz.rexp := by
  have e : ↥(Q1.subgroupOf suzM) ≃* ↥Q1 := Subgroup.subgroupOfEquivOfLe Q1_le_suzM
  obtain ⟨h2, hc, hf, hz⟩ := CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv e.symm
    coord_qVec.isExtraspecialPGroup_Q.1
  refine ⟨⟨h2, hc.trans hf.symm, hf, hz⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact coord_qVec.card_Q

theorem row_hB : IsElemAbelian Row.suz.prime (B1.subgroupOf suzM) ∧
    Nat.card (B1.subgroupOf suzM) = Row.suz.prime ^ (Row.suz.rank - 1) := by
  obtain ⟨hdb2, hdb3, hb23, -⟩ := commute_facts
  obtain ⟨hd3, hb2, hb3⟩ := pow_facts
  obtain ⟨⟨hcomm, hpow⟩, hcard⟩ :=
    isElemAbelian_closure_three hdb2 hdb3 hb23 hd3 hb2 hb3 indep_facts
  haveI : IsMulCommutative ↥B1 := hcomm
  have e : ↥(B1.subgroupOf suzM) ≃* ↥B1 := Subgroup.subgroupOfEquivOfLe B1_le_suzM
  refine ⟨⟨isMulCommutative_iff.2 fun a b => e.injective ?_, fun g hg => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_comm' (e a) (e b)
  · show g ^ 3 = 1
    have h : (g : Equiv.Perm (Fin 1782)) ^ 3 = 1 := hpow _ hg
    exact Subtype.ext (by simpa using h)
  · exact (Nat.card_congr e.toEquiv).trans hcard

theorem row_hBN : B1.subgroupOf suzM ≤
    Subgroup.normalizer ((Q1.subgroupOf suzM : Subgroup ↥suzM) : Set ↥suzM) := by
  intro b hb
  have hbN := (invE_le (B1_le_invE (Subgroup.mem_subgroupOf.1 hb))).1
  exact Subgroup.mem_normalizer_iff.2 fun q => Subgroup.mem_normalizer_iff.1 hbN q

theorem row_hd (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    x ∈ B1.subgroupOf suzM ∧ x ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Subgroup.mem_subgroupOf, hx]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have h1 : dP ^ 1 * b2P ^ 0 * b3P ^ 0 = 1 := by
      rw [pow_one, pow_zero, pow_zero, mul_one, mul_one, ← hx, h, OneMemClass.coe_one]
    exact one_ne_zero (indep_facts 1 0 0 (by norm_num) (by norm_num) (by norm_num) h1).1

section Centralizer


private theorem nonempty_centD_equiv_aSub (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    Nonempty (↥(Subgroup.centralizer ({x} : Set ↥suzM)) ≃* ↥aSub) := by
  have hφx : MulAut.conj (⟨hP, hP_mem⟩ : ↥suzM) ⟨fuseXA, fuseXA_mem⟩ = x :=
    Subtype.ext (by rw [hx, dP_eq]; rfl)
  have hmapx := map_centralizer_singleton (MulAut.conj (⟨hP, hP_mem⟩ : ↥suzM))
    (⟨fuseXA, fuseXA_mem⟩ : ↥suzM)
  rw [hφx] at hmapx
  have hmapA : (Subgroup.centralizer ({(⟨fuseXA, fuseXA_mem⟩ : ↥suzM)} : Set ↥suzM)).map
      suzM.subtype = aSub := by
    rw [map_centralizer_subtype' suzM _]
    exact aSub_eq.symm
  exact ⟨(MulEquiv.subgroupCongr hmapx).symm.trans
    (((MulAut.conj (⟨hP, hP_mem⟩ : ↥suzM)).subgroupMap _).symm.trans
      (((Subgroup.centralizer _).equivMapOfInjective suzM.subtype suzM.subtype_injective).trans
        (MulEquiv.subgroupCongr hmapA)))⟩

theorem centD_facts (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set ↥suzM)) ∧
      Nat.card (Subgroup.center ↥(Subgroup.centralizer ({x} : Set ↥suzM))) = 3 ∧
      Nonempty ((↥(Subgroup.centralizer ({x} : Set ↥suzM)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({x} : Set ↥suzM))) ≃* X₀) ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set ↥suzM)) = 9797760 := by
  obtain ⟨e⟩ := nonempty_centD_equiv_aSub x hx
  obtain ⟨hq, hcen, ⟨eT⟩⟩ := aSub_quasisimple
  have hz3 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
  have hz1 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ≠ 1 := fun h => fuseXA_ne_one (congrArg Subtype.val h)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := orderOf_eq_prime hz3 hz1
  refine ⟨CFSG.HardMathSupport.Timmesfeld.Proving.isQuasisimple_of_mulEquiv' e.symm hq, ?_,
    ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans eT⟩, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcen, Nat.card_zpowers, hord]
  · rw [Nat.card_congr e.toEquiv, card_aSub]

private theorem centD_layer (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    GLAPPrimeCore 3 ↥(Subgroup.centralizer ({x} : Set ↥suzM)) = ⊥ ∧
      GLAPLayer 3 (Subgroup.centralizer ({x} : Set ↥suzM)) =
        Subgroup.centralizer ({x} : Set ↥suzM) := by
  obtain ⟨hq, hz, -, hcard⟩ := centD_facts x hx
  set C := Subgroup.centralizer ({x} : Set ↥suzM)
  have hCn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hp3 : 3 ∣ Nat.card ↥C := by
    rw [hcard]
    norm_num
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (C : Set ↥suzM)) := by
    intro c
    refine ⟨1, ?_⟩
    have hc := Subgroup.mem_inf.1 c.2
    have hcZ : (⟨(c : ↥suzM), hc.1⟩ : ↥C) ∈ Subgroup.center ↥C :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 g g.2)
    have h3 : (⟨⟨(c : ↥suzM), hc.1⟩, hcZ⟩ : ↥(Subgroup.center ↥C)) ^ 3 = 1 := by
      rw [← hz]
      exact pow_card_eq_one'
    have h4 := congrArg (fun y : ↥(Subgroup.center ↥C) => ((y : ↥C) : ↥suzM)) h3
    rw [pow_one]
    apply Subtype.ext
    simpa using h4
  have hcore :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three le_rfl hCn hq hp3 hcent
  exact ⟨hcore, glaPLayer_eq_of_unique_glaPComponent
    (glaPComponent_of_normal_quasisimple le_rfl hCn hq hcore) fun J hJ =>
      eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three le_rfl hCn hq hcore hcent hJ⟩

theorem row_I (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    rowIOf Row.suz.prime x = Subgroup.centralizer ({x} : Set ↥suzM) :=
  (centD_layer x hx).2

theorem row_hI (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    RowI .suz Row.suz.prime (rowIOf Row.suz.prime x) := by
  rw [row_I x hx]
  show IsTypeWithCenter 3 (Subgroup.centralizer ({x} : Set ↥suzM)) (isU4of 3) 3
  obtain ⟨-, hz, ⟨eT⟩, -⟩ := centD_facts x hx
  let e : PQuot 3 (Subgroup.centralizer ({x} : Set ↥suzM)) ≃*
      ↥(Subgroup.centralizer ({x} : Set ↥suzM)) :=
    (QuotientGroup.quotientMulEquivOfEq (centD_layer x hx).1).trans QuotientGroup.quotientBot
  refine ⟨catalogIs_isU4of_three ((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    eT), ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hz]

end Centralizer

end CFSG.Sporadic.SuzI301
