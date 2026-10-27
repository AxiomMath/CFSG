module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub3B
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogOut
public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.Background.F9Fourteen
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Setup
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TShape
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSpecial
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub2
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Sub
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Walter.J1
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem comm_mem_of_sq_mem {N : Subgroup D} {p q : D} (hq : q ∈ Subgroup.normalizer (N : Set D))
    (hp2 : p * p ∈ N) (hq2 : q * q ∈ N) (hpq2 : (p * q) * (p * q) ∈ N) :
    p * q * p⁻¹ * q⁻¹ ∈ N := by
  have h1 : q⁻¹ * (p * p)⁻¹ * q ∈ N := by
    have := (Subgroup.mem_normalizer_iff''.mp hq _).mp (N.inv_mem hp2)
    exact this
  have e : p * q * p⁻¹ * q⁻¹ =
      ((p * q) * (p * q)) * (q⁻¹ * (p * p)⁻¹ * q) * (q * q)⁻¹ := by group
  rw [e]
  exact N.mul_mem (N.mul_mem hpq2 h1) (N.inv_mem hq2)

section QBU

variable (B V)

instance normal_UQ : ((conjClosure V B).subgroupOf (pCoreOf 2 B)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgB : (g : D) ∈ B := pCoreOf_le 2 B g.2
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B hgB) (n : D)).mp hn
    simpa using this⟩

abbrev QBU : Type _ := ↥(pCoreOf 2 B) ⧸ (conjClosure V B).subgroupOf (pCoreOf 2 B)

abbrev mkQ : ↥(pCoreOf 2 B) →* QBU B V := QuotientGroup.mk' _

variable {B V}

theorem mkQ_eq_one_iff {q : ↥(pCoreOf 2 B)} : mkQ B V q = 1 ↔ (q : D) ∈ conjClosure V B := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mkQ_eq_iff {p q : ↥(pCoreOf 2 B)} :
    mkQ B V p = mkQ B V q ↔ (p : D)⁻¹ * q ∈ conjClosure V B := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem QBU.mul_comm_of_sq (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)
    (u v : QBU B V) : u * v = v * u := by
  have hsqG : ∀ w : QBU B V, w * w = 1 := by
    intro w
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
    show mkQ B V (q * q) = 1
    rw [mkQ_eq_one_iff]
    exact hsq (q : D) q.2
  have hinv : ∀ w : QBU B V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hsqG w)
  calc u * v = (u * v)⁻¹ := (hinv _).symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev _ _
    _ = v * u := by rw [hinv, hinv]

theorem QBU.mul_mul_mul_comm_of_sq (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)
    (a b c d : QBU B V) : a * b * (c * d) = a * c * (b * d) := by
  let _ : CommGroup (QBU B V) :=
    { (inferInstance : Group (QBU B V)) with mul_comm := QBU.mul_comm_of_sq hsq }
  exact mul_mul_mul_comm a b c d

end QBU


section Nu

variable (B)

@[expose] def conjQ (b : D) (hb : b ∈ B) : ↥(pCoreOf 2 B) →* ↥(pCoreOf 2 B) where
  toFun q := ⟨b * q * b⁻¹,
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hb) q).mp q.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by
    show b * ((p : D) * q) * b⁻¹ = (b * p * b⁻¹) * (b * q * b⁻¹)
    group)

variable {B}

theorem conjQ_coe (b : D) (hb : b ∈ B) (q : ↥(pCoreOf 2 B)) :
    ((conjQ B b hb q : ↥(pCoreOf 2 B)) : D) = b * q * b⁻¹ := rfl

variable (V)

@[expose] def nuHom (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B) {x : D} (hx : x ∈ B) :
    ↥(pCoreOf 2 B) →* QBU B V :=
  MonoidHom.mk' (fun q => mkQ B V q * mkQ B V (conjQ B x hx q) *
      mkQ B V (conjQ B x hx (conjQ B x hx q))) (by
    intro p q
    simp only [map_mul]
    rw [QBU.mul_mul_mul_comm_of_sq hsq (mkQ B V p) (mkQ B V q),
      QBU.mul_mul_mul_comm_of_sq hsq (mkQ B V p * mkQ B V (conjQ B x hx p))
        (mkQ B V q * mkQ B V (conjQ B x hx q))])

variable {V}

theorem nuHom_apply (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B) {x : D} (hx : x ∈ B)
    (q : ↥(pCoreOf 2 B)) :
    nuHom V hsq hx q = mkQ B V q * mkQ B V (conjQ B x hx q) *
      mkQ B V (conjQ B x hx (conjQ B x hx q)) := rfl

end Nu


section NBProps

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)
  (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

include g

omit [Finite D] in
theorem Gen3.conjQ_cube (q : ↥(pCoreOf 2 B)) :
    conjQ B x g.x_mem (conjQ B x g.x_mem (conjQ B x g.x_mem q)) = q := by
  apply Subtype.ext
  show x * (x * (x * (q : D) * x⁻¹) * x⁻¹) * x⁻¹ = q
  calc x * (x * (x * (q : D) * x⁻¹) * x⁻¹) * x⁻¹
      = (x * x * x) * (q : D) * (x * x * x)⁻¹ := by group
    _ = q := by rw [g.x_cube]; group

omit [Finite D] in
theorem Gen3.nuHom_conjQ (q : ↥(pCoreOf 2 B)) :
    nuHom V hsq g.x_mem (conjQ B x g.x_mem q) = nuHom V hsq g.x_mem q := by
  rw [nuHom_apply, nuHom_apply, g.conjQ_cube]
  rw [QBU.mul_comm_of_sq hsq (mkQ B V (conjQ B x g.x_mem q) *
    mkQ B V (conjQ B x g.x_mem (conjQ B x g.x_mem q))) (mkQ B V q), ← mul_assoc]

@[expose] def Gen3.NB : Subgroup D := (nuHom V hsq g.x_mem).ker.map (pCoreOf 2 B).subtype

omit [Finite D] in
theorem Gen3.mem_NB {q : D} : q ∈ g.NB hsq ↔
    ∃ h : q ∈ pCoreOf 2 B, nuHom V hsq g.x_mem ⟨q, h⟩ = 1 := by
  constructor
  · rintro ⟨q', hq', rfl⟩
    exact ⟨q'.2, hq'⟩
  · rintro ⟨h, h1⟩
    exact ⟨⟨q, h⟩, h1, rfl⟩

omit [Finite D] in
theorem Gen3.NB_le_QB : g.NB hsq ≤ pCoreOf 2 B := by
  rintro q ⟨q', -, rfl⟩
  exact q'.2

theorem Gen3.U_le_NB : conjClosure V B ≤ g.NB hsq := by
  intro u hu
  have huQ : u ∈ pCoreOf 2 B := g.U_le_QB hu
  have hU1 : ∀ w ∈ conjClosure V B, x * w * x⁻¹ ∈ conjClosure V B := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B g.x_mem) w).mp hw
  refine (g.mem_NB hsq).mpr ⟨huQ, ?_⟩
  rw [nuHom_apply]
  have e1 : mkQ B V ⟨u, huQ⟩ = 1 := mkQ_eq_one_iff.mpr hu
  have e2 : mkQ B V (conjQ B x g.x_mem ⟨u, huQ⟩) = 1 := mkQ_eq_one_iff.mpr (hU1 u hu)
  have e3 : mkQ B V (conjQ B x g.x_mem (conjQ B x g.x_mem ⟨u, huQ⟩)) = 1 :=
    mkQ_eq_one_iff.mpr (hU1 _ (hU1 u hu))
  rw [e1, e2, e3]
  simp

omit [Finite D] in
theorem Gen3.NB_conj_x {n : D} (hn : n ∈ g.NB hsq) : x * n * x⁻¹ ∈ g.NB hsq := by
  obtain ⟨hnQ, h1⟩ := (g.mem_NB hsq).mp hn
  refine (g.mem_NB hsq).mpr ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B g.x_mem)
    n).mp hnQ, ?_⟩
  have := g.nuHom_conjQ hsq ⟨n, hnQ⟩
  rw [h1] at this
  exact this

omit [Finite D] in
theorem Gen3.x_mem_normalizer_NB : x ∈ Subgroup.normalizer ((g.NB hsq : Subgroup D) : Set D) :=
  mem_normalizer_of_cube g.x_cube fun _ hn => g.NB_conj_x hsq hn

omit [Finite D] in
theorem Gen3.NB_conj_Q {p n : D} (hp : p ∈ pCoreOf 2 B) (hn : n ∈ g.NB hsq) :
    p * n * p⁻¹ ∈ g.NB hsq := by
  obtain ⟨hnQ, h1⟩ := (g.mem_NB hsq).mp hn
  refine (g.mem_NB hsq).mpr ⟨(pCoreOf 2 B).mul_mem ((pCoreOf 2 B).mul_mem hp hnQ)
    ((pCoreOf 2 B).inv_mem hp), ?_⟩
  have e : (⟨p * n * p⁻¹, (pCoreOf 2 B).mul_mem ((pCoreOf 2 B).mul_mem hp hnQ)
      ((pCoreOf 2 B).inv_mem hp)⟩ : ↥(pCoreOf 2 B)) = ⟨p, hp⟩ * ⟨n, hnQ⟩ * ⟨p, hp⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]

end NBProps


theorem comm_mem_U_of_sq (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B) {p q : D}
    (hp : p ∈ pCoreOf 2 B) (hq : q ∈ pCoreOf 2 B) : p * q * p⁻¹ * q⁻¹ ∈ conjClosure V B :=
  comm_mem_of_sq_mem (le_normalizer_conjClosure V B (pCoreOf_le 2 B hq)) (hsq p hp) (hsq q hq)
    (hsq (p * q) ((pCoreOf 2 B).mul_mem hp hq))

section NBT

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)
  (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

include g

omit [Finite D] in
theorem Gen3.nuHom_conjQ_t {t : D} (htB : t ∈ B) (h1 : t⁻¹ * x * t * x ∈ pCoreOf 2 B)
    (h2 : t⁻¹ * (x * x) * t * (x * x) ∈ pCoreOf 2 B) {q : ↥(pCoreOf 2 B)}
    (hq : nuHom V hsq g.x_mem q = 1) : nuHom V hsq g.x_mem (conjQ B t htB q) = 1 := by
  have hUt : ∀ u ∈ conjClosure V B, t * u * t⁻¹ ∈ conjClosure V B := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B htB) u).mp hu
  have hcube : ∀ p : D, (x * x)⁻¹ * p * (x * x) = x * p * x⁻¹ ∧
      x⁻¹ * p * x = x * (x * p * x⁻¹) * x⁻¹ := by
    intro p
    constructor
    · calc (x * x)⁻¹ * p * (x * x) = (x * x * x)⁻¹ * (x * p * x⁻¹) * (x * x * x) := by group
        _ = x * p * x⁻¹ := by rw [g.x_cube]; group
    · calc x⁻¹ * p * x = (x * x * x) * (x⁻¹ * p * x) * (x * x * x)⁻¹ := by rw [g.x_cube]; group
        _ = x * (x * p * x⁻¹) * x⁻¹ := by group
  have I1 : mkQ B V (conjQ B x g.x_mem (conjQ B t htB q)) =
      mkQ B V (conjQ B t htB (conjQ B x g.x_mem (conjQ B x g.x_mem q))) := by
    rw [mkQ_eq_iff]
    show (x * (t * (q : D) * t⁻¹) * x⁻¹)⁻¹ * (t * (x * (x * (q : D) * x⁻¹) * x⁻¹) * t⁻¹) ∈ _
    obtain ⟨q₁, hq₁⟩ : ∃ q₁, q₁ = t⁻¹ * x * t * x := ⟨_, rfl⟩
    obtain ⟨r, hrdef⟩ : ∃ r, r = x * (x * (q : D) * x⁻¹) * x⁻¹ := ⟨_, rfl⟩
    have hq₁Q : q₁ ∈ pCoreOf 2 B := hq₁ ▸ h1
    have hrQ : r ∈ pCoreOf 2 B := hrdef ▸ (conjQ B x g.x_mem (conjQ B x g.x_mem q)).2
    have hA : x * (t * (q : D) * t⁻¹) * x⁻¹ = t * (q₁ * r * q₁⁻¹) * t⁻¹ := by
      rw [hq₁, hrdef, ← (hcube q).2]; group
    rw [← hrdef, hA]
    have e : (t * (q₁ * r * q₁⁻¹) * t⁻¹)⁻¹ * (t * r * t⁻¹) =
        t * (q₁ * r⁻¹ * q₁⁻¹ * r⁻¹⁻¹) * t⁻¹ := by group
    rw [e]
    exact hUt _ (comm_mem_U_of_sq hsq hq₁Q ((pCoreOf 2 B).inv_mem hrQ))
  have I2 : mkQ B V (conjQ B x g.x_mem (conjQ B x g.x_mem (conjQ B t htB q))) =
      mkQ B V (conjQ B t htB (conjQ B x g.x_mem q)) := by
    rw [mkQ_eq_iff]
    show (x * (x * (t * (q : D) * t⁻¹) * x⁻¹) * x⁻¹)⁻¹ * (t * (x * (q : D) * x⁻¹) * t⁻¹) ∈ _
    obtain ⟨q₂, hq₂⟩ : ∃ q₂, q₂ = t⁻¹ * (x * x) * t * (x * x) := ⟨_, rfl⟩
    obtain ⟨s, hsdef⟩ : ∃ s, s = x * (q : D) * x⁻¹ := ⟨_, rfl⟩
    have hq₂Q : q₂ ∈ pCoreOf 2 B := hq₂ ▸ h2
    have hsQ : s ∈ pCoreOf 2 B := hsdef ▸ (conjQ B x g.x_mem q).2
    have hA : x * (x * (t * (q : D) * t⁻¹) * x⁻¹) * x⁻¹ = t * (q₂ * s * q₂⁻¹) * t⁻¹ := by
      rw [hq₂, hsdef, ← (hcube q).1]; group
    rw [← hsdef, hA]
    have e : (t * (q₂ * s * q₂⁻¹) * t⁻¹)⁻¹ * (t * s * t⁻¹) =
        t * (q₂ * s⁻¹ * q₂⁻¹ * s⁻¹⁻¹) * t⁻¹ := by group
    rw [e]
    exact hUt _ (comm_mem_U_of_sq hsq hq₂Q ((pCoreOf 2 B).inv_mem hsQ))
  have hmk : mkQ B V (q * conjQ B x g.x_mem (conjQ B x g.x_mem q) * conjQ B x g.x_mem q) = 1 := by
    rw [map_mul, map_mul]
    have := hq
    rw [nuHom_apply] at this
    rw [mul_assoc, QBU.mul_comm_of_sq hsq (mkQ B V (conjQ B x g.x_mem (conjQ B x g.x_mem q)))
      (mkQ B V (conjQ B x g.x_mem q)), ← mul_assoc]
    exact this
  have hU1 := mkQ_eq_one_iff.mp hmk
  have hU2 : mkQ B V (conjQ B t htB (q * conjQ B x g.x_mem (conjQ B x g.x_mem q) *
      conjQ B x g.x_mem q)) = 1 := by
    rw [mkQ_eq_one_iff, conjQ_coe]
    exact hUt _ hU1
  rw [nuHom_apply, I1, I2]
  simp only [map_mul] at hU2
  exact hU2

end NBT


theorem orderOf_sq_eq_three {x : D} (hx : orderOf x = 3) : orderOf (x * x) = 3 := by
  rw [← pow_two, Nat.Coprime.orderOf_pow (by rw [hx]; decide), hx]

section NBT2

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)
  (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

include g

theorem Gen3.NB_conj_T {t n : D} (ht : t ∈ A ⊓ B) (hn : n ∈ g.NB hsq) :
    t * n * t⁻¹ ∈ g.NB hsq := by
  by_cases htQ : t ∈ pCoreOf 2 B
  · exact g.NB_conj_Q hsq htQ hn
  · have htB : t ∈ B := ht.2
    have hv := g.hyp.gold.vertex_right
    have htinv : t⁻¹ ∈ A ⊓ B := (A ⊓ B).inv_mem ht
    have htinvQ : t⁻¹ ∉ pCoreOf 2 B := fun h => htQ (by simpa using (pCoreOf 2 B).inv_mem h)
    have h1 : t⁻¹ * x * t * x ∈ pCoreOf 2 B := by
      have := conj_inv_mem_of_vertex hv g.orderOf_x g.x_mem htinv htinvQ
      simpa using this
    have h2 : t⁻¹ * (x * x) * t * (x * x) ∈ pCoreOf 2 B := by
      have := conj_inv_mem_of_vertex hv (orderOf_sq_eq_three g.orderOf_x) g.x2_mem htinv htinvQ
      simpa using this
    obtain ⟨hnQ, h1'⟩ := (g.mem_NB hsq).mp hn
    refine (g.mem_NB hsq).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B htB) n).mp hnQ
    · exact g.nuHom_conjQ_t hsq htB h1 h2 h1'

theorem Gen3.B_le_normalizer_NB :
    B ≤ Subgroup.normalizer ((g.NB hsq : Subgroup D) : Set D) :=
  GoldAmN.le_normalizer_of_mem_vTriple g.hyp.gold.amalgam.toIsGoldschmidtVTriple g.x_mem g.orderOf_x
    (le_normalizer_of_conj_mem fun _ ht _ hn => g.NB_conj_T hsq ht hn)
    (g.x_mem_normalizer_NB hsq)

theorem Gen3.psi_norm (hU : Nat.card (conjClosure V B) = 8) (b : ↥(pCoreOf 2 B)) :
    psi g (b * g.xc b * g.xc (g.xc b)) = 1 := by
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  rw [map_mul, map_mul, rot (g.xc b), rot b]
  generalize psi g b = w
  obtain ⟨w₀, w₁⟩ := w
  rcases g.zpowers_elem_cases w₀ with rfl | rfl <;>
    rcases g.zpowers_elem_cases w₁ with rfl | rfl <;> simp [hzz]

theorem Gen3.nu_mem_K (hU : Nat.card (conjClosure V B) = 8) (b : ↥(pCoreOf 2 B)) :
    ((b * conjQ B x g.x_mem b * conjQ B x g.x_mem (conjQ B x g.x_mem b) : ↥(pCoreOf 2 B)) : D) ∈
      coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  have h2 := (g.mem_ker_psi hU (b * g.xc b * g.xc (g.xc b))).mp
    (MonoidHom.mem_ker.mpr (g.psi_norm hU b))
  rw [← g.hyp.pCoreOf_inf_centralizer_eq_coreIn]
  exact h2

end NBT2


section NBCard

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)
  (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

local notation "𝐊" => coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B
local notation "𝐔" => conjClosure V B

include g

theorem Gen3.index_ker_nu (hU : Nat.card 𝐔 = 8) (hK : Nat.card ↥𝐊 = 16) :
    (nuHom V hsq g.x_mem).ker.index = 2 := by
  have hKQ : 𝐊 ≤ pCoreOf 2 B := (coreIn_le_right _ _).trans inf_le_right
  have h2 : 𝐔.relIndex 𝐊 = 2 := by
    have h1 := card_eq_relIndex_mul g.hyp.conjClosure_le_coreIn
    rw [hK, hU] at h1
    omega
  have hKsq : ∀ k ∈ 𝐊, k * k ∈ 𝐔 := fun k hk =>
    (Subgroup.zpowers_le.mpr g.z_mem_U) (g.K_sq_mem hU h2 hk)
  obtain ⟨k₀, hk₀K, hk₀U⟩ : ∃ k₀ ∈ 𝐊, k₀ ∉ 𝐔 := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (H := 𝐊) (K := 𝐔) (fun k hk => hall k hk)
    omega
  have hinvU : ∀ k : D, k ∉ 𝐔 → k⁻¹ ∉ 𝐔 := fun k hk h => hk (by simpa using 𝐔.inv_mem h)
  have hconj : ∀ k ∈ 𝐊, k ∉ 𝐔 →
      x * k * x⁻¹ ∈ 𝐊 ∧ x * k * x⁻¹ ∉ 𝐔 ∧ (x * k * x⁻¹)⁻¹ * k ∈ 𝐔 := by
    intro k hk hkU
    have hxk : x * k * x⁻¹ ∈ 𝐊 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ g.x_mem) k).mp hk
    have hxkU : x * k * x⁻¹ ∉ 𝐔 := fun h =>
      hkU ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B g.x_mem) k).mpr h)
    refine ⟨hxk, hxkU, ?_⟩
    have := mul_inv_mem_of_relIndex_two h2 (𝐊.inv_mem hxk) (𝐊.inv_mem hk) (hinvU _ hxkU)
      (hinvU _ hkU)
    rwa [inv_inv] at this
  have hmk : ∀ (k : D) (hkK : k ∈ 𝐊), k ∉ 𝐔 →
      mkQ B V (conjQ B x g.x_mem ⟨k, hKQ hkK⟩) = mkQ B V ⟨k, hKQ hkK⟩ := by
    intro k hkK hkU
    rw [mkQ_eq_iff]
    exact (hconj k hkK hkU).2.2
  set a₀ : ↥(pCoreOf 2 B) := ⟨k₀, hKQ hk₀K⟩ with ha₀
  have hm1 : mkQ B V a₀ ≠ 1 := fun h => hk₀U (mkQ_eq_one_iff.mp h)
  have hm2 : mkQ B V a₀ * mkQ B V a₀ = 1 := by
    rw [← map_mul, mkQ_eq_one_iff]
    exact hKsq k₀ hk₀K
  have hν : ∀ b : ↥(pCoreOf 2 B), nuHom V hsq g.x_mem b = mkQ B V
      (b * conjQ B x g.x_mem b * conjQ B x g.x_mem (conjQ B x g.x_mem b)) := fun b => by
    rw [nuHom_apply, map_mul, map_mul]
  have hA₀ : nuHom V hsq g.x_mem a₀ = mkQ B V a₀ := by
    obtain ⟨h1K, h1U, -⟩ := hconj k₀ hk₀K hk₀U
    have e1 : mkQ B V (conjQ B x g.x_mem a₀) = mkQ B V a₀ := hmk k₀ hk₀K hk₀U
    have e2 : mkQ B V (conjQ B x g.x_mem (conjQ B x g.x_mem a₀)) = mkQ B V a₀ :=
      (hmk _ h1K h1U).trans e1
    rw [nuHom_apply, e1, e2, hm2, one_mul]
  have hval : ∀ b : ↥(pCoreOf 2 B),
      nuHom V hsq g.x_mem b = 1 ∨ nuHom V hsq g.x_mem b = mkQ B V a₀ := by
    intro b
    rw [hν]
    have hbK := g.nu_mem_K hU b
    by_cases hbU : ((b * conjQ B x g.x_mem b * conjQ B x g.x_mem (conjQ B x g.x_mem b) :
        ↥(pCoreOf 2 B)) : D) ∈ 𝐔
    · left
      exact mkQ_eq_one_iff.mpr hbU
    · right
      rw [mkQ_eq_iff]
      have := mul_inv_mem_of_relIndex_two h2 (𝐊.inv_mem hbK) (𝐊.inv_mem hk₀K) (hinvU _ hbU)
        (hinvU _ hk₀U)
      rwa [inv_inv] at this
  rw [Subgroup.index_eq_two_iff]
  refine ⟨a₀, fun b => ?_⟩
  rcases hval b with hb | hb
  · right
    refine ⟨MonoidHom.mem_ker.mpr hb, fun h => hm1 ?_⟩
    rw [MonoidHom.mem_ker, map_mul, hb, hA₀, one_mul] at h
    exact h
  · left
    refine ⟨?_, fun h => hm1 ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hb, hA₀]
      exact hm2
    · rw [MonoidHom.mem_ker] at h
      rw [← hb]
      exact h

theorem Gen3.card_NB (hU : Nat.card 𝐔 = 8) (hK : Nat.card ↥𝐊 = 16)
    (hQ : Nat.card ↥(pCoreOf 2 B) = 64) : Nat.card ↥(g.NB hsq) = 32 := by
  have h1 := Subgroup.card_mul_index (nuHom V hsq g.x_mem).ker
  rw [g.index_ker_nu hsq hU hK, hQ] at h1
  have h2 : Nat.card ↥(g.NB hsq) = Nat.card ↥(nuHom V hsq g.x_mem).ker :=
    Subgroup.card_map_of_injective (pCoreOf 2 B).subtype_injective
  omega

end NBCard


section SqQB

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.sq_mem_of_comm (hsqA : ∀ q ∈ pCoreOf 2 A, q * q ∈ V) {b : D} (hb : b ∈ B) {q : D}
    (hq : q ∈ pCoreOf 2 B) (hc : (b * a * b⁻¹) * q = q * (b * a * b⁻¹)) :
    q * q ∈ conjClosure V B := by
  have hq' : b⁻¹ * q * b ∈ pCoreOf 2 B := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B (B.inv_mem hb)) q).mp hq
    simpa using this
  have hq'B : b⁻¹ * q * b ∈ B := pCoreOf_le 2 B hq'
  have hqa : a * (b⁻¹ * q * b) = (b⁻¹ * q * b) * a := by
    calc a * (b⁻¹ * q * b) = b⁻¹ * ((b * a * b⁻¹) * q) * b := by group
      _ = b⁻¹ * (q * (b * a * b⁻¹)) * b := by rw [hc]
      _ = (b⁻¹ * q * b) * a := by group
  have hqV : ∀ v ∈ V, v * (b⁻¹ * q * b) = (b⁻¹ * q * b) * v := by
    intro v hv
    rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact (g.z_comm hq'B).symm
    · exact hqa
    · calc z * a * (b⁻¹ * q * b) = z * (a * (b⁻¹ * q * b)) := by group
        _ = z * ((b⁻¹ * q * b) * a) := by rw [hqa]
        _ = (z * (b⁻¹ * q * b)) * a := by group
        _ = ((b⁻¹ * q * b) * z) * a := by rw [(g.z_comm hq'B).symm]
        _ = (b⁻¹ * q * b) * (z * a) := by group
  have hqA : b⁻¹ * q * b ∈ pCoreOf 2 A := by
    rw [← g.hyp.natural.centralizer_eq]
    exact ⟨(g.hyp.gold.pCoreOf_right_le hq').1,
      Subgroup.mem_centralizer_iff.mpr fun v hv => hqV v hv⟩
  have h1 := hsqA _ hqA
  have h2 := mem_conjClosure hb h1
  have e : b * ((b⁻¹ * q * b) * (b⁻¹ * q * b)) * b⁻¹ = q * q := by group
  rwa [e] at h2

theorem Gen3.sq_mem_U_QB (hU : Nat.card (conjClosure V B) = 8)
    (hsqA : ∀ q ∈ pCoreOf 2 A, q * q ∈ V) {q : D} (hq : q ∈ pCoreOf 2 B) :
    q * q ∈ conjClosure V B := by
  have hw₀ := g.hyp.commutator_mem a g.a_mem_U q hq
  have hw₁ := g.hyp.commutator_mem a₁ g.a₁_mem_U q hq
  have h₂ := g.comm_a₂ hU ⟨q, hq⟩
  have hzz := g.z_mul_z
  rcases zpowers_cases g.hyp hw₀ with e0 | e0
  · refine g.sq_mem_of_comm hsqA B.one_mem hq ?_
    simp only [one_mul, inv_one, mul_one]
    calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
      _ = q * a := by rw [e0, one_mul]
  · rcases zpowers_cases g.hyp hw₁ with e1 | e1
    · refine g.sq_mem_of_comm hsqA g.x_mem hq ?_
      rw [← g.a₁_eq]
      calc a₁ * q = (a₁ * q * a₁⁻¹ * q⁻¹) * (q * a₁) := by group
        _ = q * a₁ := by rw [e1, one_mul]
    · refine g.sq_mem_of_comm hsqA g.x2_mem hq ?_
      rw [← g.a₂_eq]
      have e2 : a₂ * q * a₂⁻¹ * q⁻¹ = 1 := by
        have := h₂
        change a₂ * q * a₂⁻¹ * q⁻¹ = _ at this
        rw [this, e0, e1, hzz]
      calc a₂ * q = (a₂ * q * a₂⁻¹ * q⁻¹) * (q * a₂) := by group
        _ = q * a₂ := by rw [e2, one_mul]

end SqQB

end GoldAmL3c

end F6

end CFSG.Quasithin
