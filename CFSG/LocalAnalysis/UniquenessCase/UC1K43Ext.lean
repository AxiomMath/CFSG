module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K43

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def NoAbelianD {G : Type} [Group G] (D : Subgroup G) : Prop :=
  ∀ A : Subgroup G, IsPGroup 2 A → A ≠ ⊥ → IsMulCommutative ↥A →
    D ≤ normalizer (A : Set G) → ⁅D, A⁆ = A → False

theorem centralizes {D T A : Subgroup G} (hDT : D ≤ normalizer (T : Set G))
    (hTA : T ≤ normalizer (A : Set G)) (hTD : ⁅D, T⁆ = T)
    (hc : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d) : ∀ t ∈ T, ∀ a ∈ A, t * a = a * t := by
  have hle : ⁅D, T⁆ ≤ centralizer (A : Set G) := by
    rw [Subgroup.commutator_le]
    intro d hd t ht
    rw [mem_centralizer_iff]
    intro a ha
    have htn : ∀ s ∈ T, ∀ b ∈ A, s * b * s⁻¹ ∈ A := fun s hs b hb =>
      (mem_normalizer_iff.1 (hTA hs) b).1 hb
    have ha1 : t⁻¹ * a * t ∈ A := by
      have := htn t⁻¹ (T.inv_mem ht) a ha
      simpa using this
    have h1 : d⁻¹ * (t⁻¹ * a * t) = (t⁻¹ * a * t) * d⁻¹ := hc d⁻¹ (D.inv_mem hd) _ ha1
    have h2 : d * a = a * d := hc d hd a ha
    have h3 : t * (t⁻¹ * a * t) * t⁻¹ = a := by group
    have key : ⁅d, t⁆ * a = a * ⁅d, t⁆ := by
      rw [commutatorElement_def]
      calc d * t * d⁻¹ * t⁻¹ * a
          = d * t * (d⁻¹ * (t⁻¹ * a * t)) * t⁻¹ := by group
        _ = d * t * ((t⁻¹ * a * t) * d⁻¹) * t⁻¹ := by rw [h1]
        _ = d * (t * (t⁻¹ * a * t) * t⁻¹) * (t * d⁻¹ * t⁻¹) := by group
        _ = d * a * (t * d⁻¹ * t⁻¹) := by rw [h3]
        _ = a * d * (t * d⁻¹ * t⁻¹) := by rw [h2]
        _ = a * (d * t * d⁻¹ * t⁻¹) := by group
    exact key.symm
  intro t ht a ha
  have := hle (hTD ▸ ht)
  exact ((mem_centralizer_iff.1 this) a ha).symm

theorem fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
    {D A : Type} [Group D] [Group A] [Finite D] [Finite A] [MulDistribMulAction D A]
    (hD : Nat.card D = 3) (hA2 : IsPGroup 2 A) (hAc : IsMulCommutative A)
    (hcomm : commutatorAction (A := D) (G := A) = ⊤) :
    fixedPointSubgroup D A = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA2
  have hcop : Nat.Coprime (Nat.card D) (Nat.card A) := by
    rw [hD, hn]
    exact Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)
  have hsup : fixedPointSubgroup D A ⊔ commutatorAction (A := D) (G := A) = ⊤ := by
    rw [hcomm, sup_top_eq]
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
      (G := A) (A := D) hsup hcop hAc
  have hinf : fixedPointSubgroup D A ⊓ commutatorAction (A := D) (G := A) = ⊥ :=
    hcompl.disjoint.eq_bot
  rw [hcomm, inf_top_eq] at hinf
  exact hinf

theorem NoAbelianD.centralizes_abelian {D A : Subgroup G} (hNo : NoAbelianD D)
    (hD : Nat.card D = 3) (hA2 : IsPGroup 2 A) (hAc : IsMulCommutative ↥A)
    (hDA : D ≤ normalizer (A : Set G)) :
    ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA2
  have hcop : Nat.Coprime (Nat.card D) (Nat.card A) := by
    rw [hD, hn]
    exact Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)
  set A0 : Subgroup G := ⁅A, D⁆ with hA0
  by_cases hbot : A0 = ⊥
  · intro d hd a ha
    have hmem : ⁅d, a⁆ ∈ (⊥ : Subgroup G) := by
      have h1 : ⁅d, a⁆ ∈ ⁅D, A⁆ := Subgroup.commutator_mem_commutator hd ha
      rwa [Subgroup.commutator_comm, ← hA0, hbot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  · exfalso
    have hA0le : A0 ≤ A := by
      rw [hA0]
      exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hDA
    have hA02 : IsPGroup 2 ↥A0 :=
      hA2.of_injective (Subgroup.inclusion hA0le) (Subgroup.inclusion_injective hA0le)
    have hA0c : IsMulCommutative ↥A0 := by
      refine IsMulCommutative.of_comm (fun a b : ↥A0 => ?_)
      have h := mul_comm' (⟨(a : G), hA0le a.2⟩ : ↥A) (⟨(b : G), hA0le b.2⟩ : ↥A)
      exact Subtype.ext (congrArg (fun x : ↥A => (x : G)) h)
    have hDA0 : D ≤ normalizer (A0 : Set G) := by
      rw [hA0]
      exact Subgroup.normalizer_commutator_ge_right A D
    have hle : A0 ≤ ⁅A0, D⁆ := by
      rw [hA0]
      exact CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime A D hDA hcop
    have hself : ⁅D, A0⁆ = A0 := by
      refine le_antisymm ((Subgroup.le_normalizer_iff_commutator_le_right).mp hDA0) ?_
      rw [Subgroup.commutator_comm]
      exact hle
    exact hNo A0 hA02 hbot hA0c hDA0 hself

theorem commutatorElement_mul_right_central {P : Type} [Group P] {a x b : P}
    (h : ⁅a, b⁆ * x⁻¹ = x⁻¹ * ⁅a, b⁆) : ⁅a, x * b⁆ = ⁅a, x⁆ * ⁅a, b⁆ := by
  calc ⁅a, x * b⁆ = a * x * a⁻¹ * (⁅a, b⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, x⁆ * ⁅a, b⁆ := by rw [h]; simp only [commutatorElement_def]; group

abbrev infCentralizer {P : Type} [Group P] (C : Subgroup P) : Subgroup P :=
  C ⊓ centralizer (C : Set P)

scoped instance instCommGroupInfCentralizer {P : Type} [Group P] (C : Subgroup P)
    [hZ : Fact (infCentralizer C ≤ Subgroup.center P)] : CommGroup ↥(infCentralizer C) :=
  { (inferInstance : Group ↥(infCentralizer C)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZ.out b.2) a) }

noncomputable def commutatorPairing {P : Type} [Group P] {C : Subgroup P}
    (hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ infCentralizer C)
    (hZcen : infCentralizer C ≤ Subgroup.center P) (t : P) :
    C →* infCentralizer C where
  toFun c := ⟨⁅t, (c : P)⁆, hPC (Subgroup.commutator_mem_commutator (Subgroup.mem_top t) c.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' c1 c2 := by
    apply Subtype.ext
    have hc : (⁅t, (c2 : P)⁆ : P) ∈ Subgroup.center P :=
      hZcen (hPC (Subgroup.commutator_mem_commutator (Subgroup.mem_top t) c2.2))
    have hcomm : (⁅t, (c2 : P)⁆ : P) * ((c1 : P))⁻¹ = ((c1 : P))⁻¹ * ⁅t, (c2 : P)⁆ :=
      (Subgroup.mem_center_iff.mp hc ((c1 : P))⁻¹).symm
    show ⁅t, ((c1 * c2 : C) : P)⁆ = ⁅t, (c1 : P)⁆ * ⁅t, (c2 : P)⁆
    rw [Subgroup.coe_mul]
    exact commutatorElement_mul_right_central (a := t) (x := (c1 : P)) (b := (c2 : P)) hcomm

theorem subgroupOf_inf_centralizer_le_center {P : Type} [Group P] {C : Subgroup P}
    (hZcen : infCentralizer C ≤ Subgroup.center P) :
    (infCentralizer C).subgroupOf C ≤ Subgroup.center C := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hZcen hz) (y : P)

theorem subgroupOf_inf_centralizer_le_commutatorPairing_ker {P : Type} [Group P] {C : Subgroup P}
    (hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ infCentralizer C)
    (hZcen : infCentralizer C ≤ Subgroup.center P) (t : P) :
    (infCentralizer C).subgroupOf C ≤ (commutatorPairing hPC hZcen t).ker := by
  intro c hc
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hZcen hc) t)

noncomputable def commutatorQuotientPairing {P : Type} [Group P] {C : Subgroup P}
    (hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ infCentralizer C)
    (hZcen : infCentralizer C ≤ Subgroup.center P)
    [((infCentralizer C).subgroupOf C).Normal]
    [Fact (infCentralizer C ≤ Subgroup.center P)] :
    P →* (C ⧸ (infCentralizer C).subgroupOf C →* infCentralizer C) where
  toFun t := QuotientGroup.lift _ (commutatorPairing hPC hZcen t)
      (subgroupOf_inf_centralizer_le_commutatorPairing_ker hPC hZcen t)
  map_one' := by
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      rw [QuotientGroup.lift_mk]
      apply Subtype.ext
      change ⁅(1 : P), (c : P)⁆ = 1
      simp
  map_mul' t1 t2 := by
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      simp only [MonoidHom.mul_apply, QuotientGroup.lift_mk]
      apply Subtype.ext
      change ⁅t1 * t2, (c : P)⁆ = ⁅t1, (c : P)⁆ * ⁅t2, (c : P)⁆
      have hc : (⁅t2, (c : P)⁆ : P) ∈ Subgroup.center P :=
        hZcen (hPC (Subgroup.commutator_mem_commutator (Subgroup.mem_top t2) c.2))
      rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp hc t1,
        mul_inv_cancel_right]
      exact Subgroup.mem_center_iff.mp
        (hZcen (hPC (Subgroup.commutator_mem_commutator (Subgroup.mem_top t1) c.2)))
        ⁅t2, (c : P)⁆

theorem commutatorQuotientPairing_ker_le {P : Type} [Group P] {C : Subgroup P}
    (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C)
    (hZcen : infCentralizer C ≤ Subgroup.center P)
    [((infCentralizer C).subgroupOf C).Normal]
    [Fact (infCentralizer C ≤ Subgroup.center P)] :
    (commutatorQuotientPairing hC.2.2.1 hZcen).ker ≤ infCentralizer C := by
  intro t ht
  rw [MonoidHom.mem_ker] at ht
  change t ∈ C ⊓ centralizer (C : Set P)
  rw [← hC.2.2.2]
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h1 : commutatorPairing hC.2.2.1 hZcen t ⟨c, hc⟩ = 1 := by
    have := congrArg (fun f : C ⧸ (infCentralizer C).subgroupOf C →*
        infCentralizer C => f (QuotientGroup.mk' _ ⟨c, hc⟩)) ht
    change (QuotientGroup.lift ((infCentralizer C).subgroupOf C)
        (commutatorPairing hC.2.2.1 hZcen t)
        (subgroupOf_inf_centralizer_le_commutatorPairing_ker hC.2.2.1 hZcen t))
      ((⟨c, hc⟩ : C) : C ⧸ (infCentralizer C).subgroupOf C) = 1 at this
    rwa [QuotientGroup.lift_mk] at this
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h1)).symm

theorem commutatorQuotientPairing_target_sq {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hCΦ : (frattini C).map C.subtype ≤ infCentralizer C)
    (hP : IsPGroup 2 P)
    [((infCentralizer C).subgroupOf C).Normal]
    [Fact (infCentralizer C ≤ Subgroup.center P)]
    (g : C ⧸ (infCentralizer C).subgroupOf C →* infCentralizer C) :
    g ^ 2 = 1 := by
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H c =>
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply]
    have hc2 : QuotientGroup.mk' ((infCentralizer C).subgroupOf C) (c ^ 2) = 1 := by
      change ((c ^ 2 : C) : C ⧸ (infCentralizer C).subgroupOf C) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hCΦ (Subgroup.mem_map_of_mem C.subtype
        (CFSG.SectionRank.Ccomm.pow_mem_frattini (hP.to_subgroup C) c))
    calc g (QuotientGroup.mk' _ c) * g (QuotientGroup.mk' _ c)
        = g ((QuotientGroup.mk' _ c) * (QuotientGroup.mk' _ c)) := (map_mul g _ _).symm
      _ = g (QuotientGroup.mk' _ (c * c)) := by rw [← map_mul]
      _ = g (QuotientGroup.mk' _ (c ^ 2)) := by rw [pow_two]
      _ = g 1 := by rw [hc2]
      _ = 1 := map_one g

theorem class_two_of_thompson_critical {P : Type} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {C : Subgroup P} (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C)
    (hZcen : C ⊓ centralizer (C : Set P) ≤ Subgroup.center P) :
    commutator P ≤ Subgroup.center P ∧ ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ((infCentralizer C).subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_inf_centralizer_le_center hZcen)
  haveI : Fact (infCentralizer C ≤ Subgroup.center P) := ⟨hZcen⟩
  obtain ⟨hCchar, hCΦ, hPC, hCcen⟩ := hC
  have hker : (commutatorQuotientPairing hPC hZcen).ker ≤ C ⊓ centralizer (C : Set P) :=
    commutatorQuotientPairing_ker_le ⟨hCchar, hCΦ, hPC, hCcen⟩ hZcen
  have hcomm_le : commutator P ≤ C ⊓ centralizer (C : Set P) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm' (commutatorQuotientPairing hPC hZcen x) (commutatorQuotientPairing hPC hZcen y))
  refine ⟨hcomm_le.trans hZcen, fun x => hZcen (hker ?_)⟩
  rw [MonoidHom.mem_ker, map_pow]
  exact commutatorQuotientPairing_target_sq hCΦ hP (commutatorQuotientPairing hPC hZcen x)

theorem le_normalizer_map_subtype_of_characteristic {D T : Subgroup G}
    (hN : D ≤ normalizer (T : Set G)) {K : Subgroup ↥T} [K.Characteristic] :
    D ≤ normalizer ((K.map T.subtype : Subgroup G) : Set G) := by
  haveI : Subgroup.Normalizes D T := ⟨hN⟩
  haveI : IsInvariant ↥D ↥T K := isInvariant_of_characteristic K
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    have hinv : (⟨d, hd⟩ : ↥D) • c ∈ K :=
      (IsInvariant.invariant (A := ↥D) (G := ↥T) (H := K) ⟨d, hd⟩ c).1 hc
    refine Subgroup.mem_map.mpr ⟨(⟨d, hd⟩ : ↥D) • c, hinv, ?_⟩
    rfl
  · intro hz
    obtain ⟨c', hc', hc'e⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨(⟨d⁻¹, D.inv_mem hd⟩ : ↥D) • c', ?_, ?_⟩
    · exact (IsInvariant.invariant (A := ↥D) (G := ↥T) (H := K)
        ⟨d⁻¹, D.inv_mem hd⟩ c').1 hc'
    · change (d : G)⁻¹ * ((c' : ↥T) : G) * ((d : G)⁻¹)⁻¹ = z
      rw [show ((c' : ↥T) : G) = (d : G) * z * (d : G)⁻¹ from hc'e]
      group

theorem inf_centralizer_le_center_of_noAbelianD {D T : Subgroup G} (hD : Nat.card D = 3)
    (hT2 : IsPGroup 2 T) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    (hNo : NoAbelianD D) {C : Subgroup ↥T} (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C) :
    C ⊓ centralizer (C : Set ↥T) ≤ Subgroup.center ↥T := by
  haveI : Subgroup.Normalizes D T := ⟨hN⟩
  haveI : C.Characteristic := hC.1
  haveI : (centralizer (C : Set ↥T)).Characteristic :=
    CFSG.SectionRank.Ccomm.characteristic_centralizer (K := C)
  set Z : Subgroup ↥T := C ⊓ centralizer (C : Set ↥T) with hZdef
  have hZchar : Z.Characteristic := by
    rw [hZdef]
    exact CFSG.SectionRank.Ccomm.characteristic_inf (H := C) (K := centralizer (C : Set ↥T))
  haveI : Z.Characteristic := hZchar
  set Zg : Subgroup G := Z.map T.subtype with hZg
  have hZg2 : IsPGroup 2 Zg := (hT2.to_subgroup Z).map T.subtype
  have hZgc : IsMulCommutative ↥Zg := by
    have hZc : IsMulCommutative ↥Z := by
      refine IsMulCommutative.of_comm (fun a b : ↥Z => ?_)
      exact Subtype.ext (mem_centralizer_iff.mp a.2.2 (b : ↥T) b.2.1).symm
    letI : IsMulCommutative ↥Z := hZc
    exact Subgroup.map_isMulCommutative (f := T.subtype) (H := Z)
  have hDZg : D ≤ normalizer (Zg : Set G) :=
    le_normalizer_map_subtype_of_characteristic hN (K := Z)
  have hZgsub : Zg.subgroupOf T = Z := by
    apply Subgroup.map_subtype_inj.mp
    calc (Zg.subgroupOf T).map T.subtype = Zg :=
          Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le Z)
      _ = Z.map T.subtype := hZg
  have hTZg : T ≤ normalizer (Zg : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le Z), hZgsub]
    infer_instance
  have hZle_center : Z ≤ Subgroup.center ↥T := by
    have hDcentZg := hNo.centralizes_abelian hD hZg2 hZgc hDZg
    have hTcentZg := centralizes hN hTZg hDT hDcentZg
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hTcentZg (y : ↥T) y.2 (T.subtype z) (Subgroup.mem_map_of_mem T.subtype hz)
  exact hZdef ▸ hZle_center

theorem class_two {D T : Subgroup G} (hD : Nat.card D = 3) (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥)
    (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T) (hZ : IsCyclic ↥(center ↥T))
    (hNo : NoAbelianD D) :
    commutator ↥T ≤ center ↥T ∧ ∀ x : ↥T, x ^ 2 ∈ center ↥T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨C, hC⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup (P := ↥T) (p := 2) hT2
  exact class_two_of_thompson_critical hT2 hC
    (inf_centralizer_le_center_of_noAbelianD hD hT2 hN hDT hNo hC)

theorem commutatorAction_quotient_commutator_eq_top {D T : Subgroup G}
    (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    [Subgroup.Normalizes D T]
    [IsInvariant ↥D ↥T (commutator ↥T)]
    [((commutator ↥T) : Subgroup ↥T).Normal] :
    @commutatorAction ↥D (↥T ⧸ commutator ↥T) _ _
      (quotientMulDistribMulAction (A := ↥D) (G := ↥T) (commutator ↥T) inferInstance) = ⊤ := by
  haveI : MulAction.QuotientAction ↥D (commutator ↥T) :=
    quotientAction_of_isInvariant (A := ↥D) _ inferInstance
  letI : MulDistribMulAction ↥D (↥T ⧸ commutator ↥T) :=
    quotientMulDistribMulAction (A := ↥D) (G := ↥T) (commutator ↥T) inferInstance
  have hcommT : commutatorAction (A := ↥D) (G := ↥T) = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [commutatorAction_subgroup_conj_map_eq_commutator T D hN, Subgroup.commutator_comm, hDT,
      Subgroup.map_top, Subgroup.range_subtype]
  have hmap_le : (commutatorAction (A := ↥D) (G := ↥T)).map (QuotientGroup.mk' (commutator ↥T)) ≤
      commutatorAction (A := ↥D) (G := ↥T ⧸ commutator ↥T) := by
    rw [commutatorAction_eq_closure (G := ↥T), MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro q ⟨x, hx, rfl⟩
    rcases hx with ⟨a, u, hxeq⟩
    refine ⟨a, QuotientGroup.mk' (commutator ↥T) u, ⟨Subgroup.mem_top u, ?_⟩⟩
    have hsmul : a • (QuotientGroup.mk' (commutator ↥T) u)
        = QuotientGroup.mk' (commutator ↥T) (a • u) :=
      MulAction.Quotient.smul_mk (H := commutator ↥T) a u
    calc QuotientGroup.mk' (commutator ↥T) x
        = QuotientGroup.mk' (commutator ↥T) (u⁻¹ * (a • u)) := by rw [hxeq]
      _ = (QuotientGroup.mk' (commutator ↥T) u)⁻¹
            * QuotientGroup.mk' (commutator ↥T) (a • u) := by rw [map_mul, map_inv]
      _ = (QuotientGroup.mk' (commutator ↥T) u)⁻¹
            * (a • QuotientGroup.mk' (commutator ↥T) u) := by rw [hsmul]
  have hsurj : (⊤ : Subgroup ↥T).map (QuotientGroup.mk' (commutator ↥T)) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (commutator ↥T))
  rw [hcommT] at hmap_le
  rw [hsurj] at hmap_le
  exact top_le_iff.mp hmap_le

theorem center_le_commutator_of_extraspecial {D T : Subgroup G} (hD : Nat.card D = 3)
    (hT2 : IsPGroup 2 T) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    (hNo : NoAbelianD D) : Subgroup.center ↥T ≤ commutator ↥T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Subgroup.Normalizes D T := ⟨hN⟩
  set Zmap : Subgroup G := (Subgroup.center ↥T).map T.subtype with hZmap
  have hZmap2 : IsPGroup 2 Zmap := (hT2.to_subgroup (Subgroup.center ↥T)).map T.subtype
  have hZmapc : IsMulCommutative ↥Zmap := by
    letI : IsMulCommutative ↥(Subgroup.center ↥T) := inferInstance
    exact Subgroup.map_isMulCommutative (f := T.subtype) (H := Subgroup.center ↥T)
  have hDcentZmap := hNo.centralizes_abelian hD hZmap2 hZmapc
    (le_normalizer_map_subtype_of_characteristic hN (K := Subgroup.center ↥T))
  haveI : (commutator ↥T).Characteristic := inferInstance
  haveI : IsInvariant ↥D ↥T (commutator ↥T) := isInvariant_of_characteristic _
  haveI : MulAction.QuotientAction ↥D (commutator ↥T) :=
    quotientAction_of_isInvariant (A := ↥D) _ inferInstance
  letI : MulDistribMulAction ↥D (↥T ⧸ commutator ↥T) :=
    quotientMulDistribMulAction (A := ↥D) (G := ↥T) (commutator ↥T) inferInstance
  have hcomm := commutatorAction_quotient_commutator_eq_top hN hDT
  have hA2 : IsPGroup 2 (↥T ⧸ commutator ↥T) := hT2.to_quotient (commutator ↥T)
  have hAc : IsMulCommutative (↥T ⧸ commutator ↥T) := inferInstance
  have hfix := fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
    (D := ↥D) (A := ↥T ⧸ commutator ↥T) (by simpa using hD) hA2 hAc hcomm
  have hZmap_fix : (Subgroup.center ↥T).map (QuotientGroup.mk' (commutator ↥T)) ≤
      fixedPointSubgroup ↥D (↥T ⧸ commutator ↥T) := by
    intro q hq
    obtain ⟨z, hz, hzq⟩ := Subgroup.mem_map.mp hq
    rw [← hzq]
    intro d
    rw [show (d : ↥D) • (QuotientGroup.mk' (commutator ↥T) z)
        = QuotientGroup.mk' (commutator ↥T) ((d : ↥D) • z) from
      MulAction.Quotient.smul_mk (H := commutator ↥T) d z]
    congr 1
    apply Subtype.ext
    have hcent : (d : G) * (z : G) = (z : G) * (d : G) :=
      hDcentZmap d d.2 (T.subtype z) (Subgroup.mem_map_of_mem T.subtype hz)
    change (d : G) * (z : G) * (d : G)⁻¹ = (z : G)
    rw [hcent, mul_assoc, mul_inv_cancel, mul_one]
  have hbot : (Subgroup.center ↥T).map (QuotientGroup.mk' (commutator ↥T)) = ⊥ := by
    apply le_bot_iff.mp
    rw [hfix] at hZmap_fix
    exact hZmap_fix
  rw [Subgroup.map_eq_bot_iff] at hbot
  rwa [QuotientGroup.ker_mk'] at hbot

theorem center_card_two_of_extraspecial {D T : Subgroup G} (hD : Nat.card D = 3)
    (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    (hNo : NoAbelianD D) (hclass : commutator ↥T ≤ Subgroup.center ↥T)
    (hsq : ∀ x : ↥T, x ^ 2 ∈ Subgroup.center ↥T) (hZ : IsCyclic ↥(center ↥T)) :
    Nat.card ↥(Subgroup.center ↥T) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT0
  have hZT' : Subgroup.center ↥T = commutator ↥T :=
    le_antisymm (center_le_commutator_of_extraspecial hD hT2 hN hDT hNo) hclass
  have hsq_comm : ∀ x y : ↥T, ⁅x, y⁆ ^ 2 = 1 := by
    intro x y
    have hz : ⁅x, y⁆ ∈ Subgroup.center ↥T :=
      hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
    have hcommxy : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hz x
    rw [hcommxy.commutatorElement_pow_left 2]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hsq x) y).symm
  have hT'_sq : ∀ w ∈ commutator ↥T, w ^ 2 = 1 := by
    intro w hw
    rw [_root_.commutator_def, Subgroup.commutator_def] at hw
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hw
    · rintro x ⟨a, -, b, -, rfl⟩
      exact hsq_comm a b
    · rintro x ⟨a, -, b, -, rfl⟩
      rw [inv_pow, hsq_comm a b, inv_one]
    · simp
    · intro x y hx hy hpx hpy
      have hxT' : x ∈ commutator ↥T := by
        rw [_root_.commutator_def, Subgroup.commutator_def]
        exact hx
      have hcommxy : Commute x y := (Subgroup.mem_center_iff.mp (hclass hxT') y).symm
      rw [hcommxy.mul_pow, hpx, hpy, mul_one]
  have hcenter_sq : ∀ z : ↥(Subgroup.center ↥T), z ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    change (z : ↥T) ^ 2 = 1
    exact hT'_sq (z : ↥T) (by rw [← hZT']; exact z.2)
  have hexp : Monoid.exponent ↥(Subgroup.center ↥T) ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hcenter_sq
  have hcard_dvd : Nat.card ↥(Subgroup.center ↥T) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card (α := ↥(Subgroup.center ↥T))]
    exact hexp
  haveI : Nontrivial ↥(Subgroup.center ↥T) := hT2.center_nontrivial
  have hcard_ge : 2 ≤ Nat.card ↥(Subgroup.center ↥T) := by
    have := Finite.one_lt_card (α := ↥(Subgroup.center ↥T))
    omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hcard_dvd with h | h
  · omega
  · exact h

theorem quotient_center_elementary_abelian_of_extraspecial {T : Subgroup G}
    (hclass : commutator ↥T ≤ Subgroup.center ↥T)
    (hsq : ∀ x : ↥T, x ^ 2 ∈ Subgroup.center ↥T) :
    IsElementaryAbelian 2 (↥T ⧸ Subgroup.center ↥T) := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hclass
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [show (QuotientGroup.mk x : ↥T ⧸ Subgroup.center ↥T) ^ 2 =
          QuotientGroup.mk (x ^ 2) from
        (map_pow (QuotientGroup.mk' (Subgroup.center ↥T)) x 2).symm,
        QuotientGroup.eq_one_iff]
      exact hsq x

theorem extraspecial {D T : Subgroup G} (hD : Nat.card D = 3) (hT2 : IsPGroup 2 T)
    (hT0 : T ≠ ⊥) (hN : D ≤ normalizer (T : Set G)) (hDT : ⁅D, T⁆ = T)
    (hZ : IsCyclic ↥(center ↥T)) (hNo : NoAbelianD D) : CFSG.IsExtraspecial 2 ↥T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Subgroup.Normalizes D T := ⟨hN⟩
  obtain ⟨hclass, hsq⟩ := class_two hD hT2 hT0 hN hDT hZ hNo
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT0
  have hcenter_ne_top : Subgroup.center ↥T ≠ ⊤ := by
    intro htop
    have hcomm : IsMulCommutative ↥T := by
      refine IsMulCommutative.of_comm (fun a b => ?_)
      have ha : a ∈ Subgroup.center ↥T := by rw [htop]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    exact hNo T hT2 hT0 hcomm hN hDT
  exact { center_order_p := center_card_two_of_extraspecial hD hT2 hT0 hN hDT hNo hclass hsq hZ
          quotient_elementary_abelian :=
            quotient_center_elementary_abelian_of_extraspecial hclass hsq
          quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr hcenter_ne_top }

end CFSG.LocalAnalysis.UniquenessCase.UCK.K43
