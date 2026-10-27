module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre

import CFSG.GroupTheory.SL2SylowTwo
import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace CFSG.Quasithin.St84

open Matrix Multiplicative
open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

private theorem toAdd_eq_zero_iff_ker {E N : Subgroup G} {F : Type} [Field F]
    {β : ↥E →* Multiplicative (Fin 2 → F)} (hker : β.ker = N.subgroupOf E) (e : ↥E) :
    toAdd (β e) = 0 ↔ (e : G) ∈ N := by
  rw [toAdd_eq_zero, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

private theorem toAdd_conj_eq {E V Z : Subgroup G} {F : Type} [Field F] (hZV : Z ≤ V)
    (hcent : ⁅E, V⁆ ≤ Z) {β₂ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₂ker : β₂.ker = Z.subgroupOf V) (a : ↥E) (z : ↥V)
    (hmem : (a : G) * (z : G) * (a : G)⁻¹ ∈ V) :
    toAdd (β₂ ⟨(a : G) * (z : G) * (a : G)⁻¹, hmem⟩) = toAdd (β₂ z) := by
  have hZ : ⁅(a : G), (z : G)⁆ ∈ Z :=
    hcent (Subgroup.commutator_mem_commutator a.2 z.2)
  have hker : (⟨⁅(a : G), (z : G)⁆, hZV hZ⟩ : ↥V) ∈ β₂.ker := by
    rw [hβ₂ker, Subgroup.mem_subgroupOf]
    exact hZ
  have heq : (⟨(a : G) * (z : G) * (a : G)⁻¹, hmem⟩ : ↥V) =
      (⟨⁅(a : G), (z : G)⁆, hZV hZ⟩ : ↥V) * z := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [heq, map_mul, toAdd_mul, MonoidHom.mem_ker.mp hker, toAdd_one, zero_add]

private theorem commutator_mul_mem {V : Subgroup G} {x u v : G} (hv : v ∈ V)
    (hxv : x * v * x⁻¹ ∈ V) (hxu : ⁅x, u⁆ ∈ V) : ⁅x, v * u⁆ ∈ V := by
  have h1 : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by rw [commutatorElement_def]
  have h2 : ⁅x, v * u⁆ = ((x * v * x⁻¹) * ⁅x, u⁆) * v⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj, h1]
    group
  rw [h2]
  exact V.mul_mem (V.mul_mem hxv hxu) (V.inv_mem hv)

private noncomputable def commPair {E V : Subgroup G} {F : Type} [Field F]
    (β₂ : ↥V →* Multiplicative (Fin 2 → F)) (hEE : ⁅E, E⁆ ≤ V) (a b : G) : Fin 2 → F :=
  @dite (Fin 2 → F) (a ∈ E ∧ b ∈ E) (Classical.propDecidable (a ∈ E ∧ b ∈ E))
    (fun h => toAdd (β₂ ⟨⁅a, b⁆, hEE (Subgroup.commutator_mem_commutator h.1 h.2)⟩))
    (fun _ => 0)

private theorem commPair_of_mem {E V : Subgroup G} {F : Type} [Field F]
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} {hEE : ⁅E, E⁆ ≤ V}
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    commPair β₂ hEE a b =
      toAdd (β₂ ⟨⁅a, b⁆, hEE (Subgroup.commutator_mem_commutator ha hb)⟩) :=
  dif_pos ⟨ha, hb⟩

private theorem exists_eq_mul_of_mem_upperUnipotent {L T : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hUpper : (T.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F)
    {x : ↥L} (hx : α x ∈ CFSG.Timmesfeld.upperUnipotent F) :
    ∃ t ∈ T, ∃ k ∈ pCoreOf 2 L, (x : G) = t * k := by
  rw [← hUpper] at hx
  obtain ⟨y, hy, hαy⟩ := Subgroup.mem_map.mp hx
  have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
  have hmem : y⁻¹ * x ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαy, inv_mul_cancel]
  have hk : ((y⁻¹ * x : ↥L) : G) ∈ pCoreOf 2 L := by
    have h1 : y⁻¹ * x ∈ (pCoreOf 2 L).subgroupOf L := by rw [← hker]; exact hmem
    exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨(y : G), hyT, ((y⁻¹ * x : ↥L) : G), hk, ?_⟩
  show (x : G) = (y : G) * ((y⁻¹ * x : ↥L) : G)
  rw [show ((y⁻¹ * x : ↥L) : G) = (y : G)⁻¹ * (x : G) from rfl]
  group

private theorem commutator_mul_eq_conj_mul {L E V T : Subgroup G}
    (hVnorm : L ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ L)
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ V)
    {t k c : G} (ht : t ∈ T) (hk : k ∈ pCoreOf 2 L) (hc : c ∈ E) :
    ⁅t * k, c⁆ = (t * ⁅k, c⁆ * t⁻¹) * ⁅t, c⁆ ∧ t * ⁅k, c⁆ * t⁻¹ ∈ V := by
  refine ⟨by rw [commutatorElement_mul_left_eq_conj_mul], ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hVnorm (hTL ht)) _).mp (hcore k hk c hc)

private theorem commutator_mem_of_mem_upperUnipotent {L E V T : Subgroup G} (hEL : E ≤ L)
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hVnorm : L ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ L) (hVE : V ≤ E)
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ V)
    (hquad : ∀ t ∈ T, ∀ t' ∈ T, ∀ e ∈ E, ⁅t, ⁅t', e⁆⁆ ∈ V)
    {F : Type} [Field F] {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hUpper : (T.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F) :
    ∀ x x' : ↥L, α x ∈ CFSG.Timmesfeld.upperUnipotent F →
      α x' ∈ CFSG.Timmesfeld.upperUnipotent F →
      ∀ c ∈ E.subgroupOf L, ⁅x', ⁅x, c⁆⁆ ∈ V.subgroupOf L := by
  intro x x' hx hx' c hc
  obtain ⟨t, ht, k, hk, hxk⟩ := exists_eq_mul_of_mem_upperUnipotent hker hUpper hx
  obtain ⟨t', ht', k', hk', hx'k'⟩ := exists_eq_mul_of_mem_upperUnipotent hker hUpper hx'
  have hcE : (c : G) ∈ E := Subgroup.mem_subgroupOf.mp hc
  obtain ⟨hstep, hmemV⟩ := commutator_mul_eq_conj_mul hVnorm hTL hcore ht hk hcE
  have htcE : ⁅t, (c : G)⁆ ∈ E := by
    have h1 : t * (c : G) * t⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hLE (hTL ht)) (c : G)).mp hcE
    rw [show ⁅t, (c : G)⁆ = (t * (c : G) * t⁻¹) * (c : G)⁻¹ from by
      rw [commutatorElement_def]]
    exact E.mul_mem h1 (E.inv_mem hcE)
  have hxcE : ⁅(x : G), (c : G)⁆ ∈ E := by
    rw [hxk, hstep]
    exact E.mul_mem (hVE hmemV) htcE
  have hinner : ⁅t', ⁅(x : G), (c : G)⁆⁆ ∈ V := by
    rw [hxk, hstep]
    exact commutator_mul_mem hmemV
      ((Subgroup.mem_normalizer_iff.mp (hVnorm (hTL ht')) _).mp hmemV)
      (hquad t' ht' t ht (c : G) hcE)
  have hk'w : ⁅k', ⁅(x : G), (c : G)⁆⁆ ∈ V := hcore k' hk' _ hxcE
  rw [Subgroup.mem_subgroupOf]
  have hout : ⁅(x' : G), ⁅(x : G), (c : G)⁆⁆ ∈ V := by
    rw [hx'k', commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVnorm (hTL ht')) _).mp hk'w) hinner
  simpa [commutatorElement_def] using hout

private theorem commutator_mem_of_mem_relCent {L E V T : Subgroup G}
    (hVnorm : L ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ L)
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ V)
    {F : Type} [Field F] {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L)
    (hUpper : (T.subgroupOf L).map α = CFSG.Timmesfeld.upperUnipotent F) :
    ∀ c ∈ (relCent E V T).subgroupOf L, ∀ x : ↥L,
      α x ∈ CFSG.Timmesfeld.upperUnipotent F → ⁅x, c⁆ ∈ V.subgroupOf L := by
  intro c hc x hx
  obtain ⟨t, ht, k, hk, hxk⟩ := exists_eq_mul_of_mem_upperUnipotent hker hUpper hx
  obtain ⟨hcE, -, hcT⟩ := Subgroup.mem_subgroupOf.mp hc
  obtain ⟨hstep, hmemV⟩ := commutator_mul_eq_conj_mul hVnorm hTL hcore ht hk hcE
  have htc : ⁅t, (c : G)⁆ ∈ V := by
    simpa [commutatorElement_inv] using V.inv_mem (hcT t ht)
  rw [Subgroup.mem_subgroupOf]
  rw [show ((⁅x, c⁆ : ↥L) : G) = ⁅(x : G), (c : G)⁆ from by simp [commutatorElement_def]]
  rw [hxk, hstep]
  exact V.mul_mem hmemV htc

private theorem le_relCent {L E V T : Subgroup G} (hEL : E ≤ L) (hVE : V ≤ E)
    (hVnorm : L ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ L) : V ≤ relCent E V T := by
  intro v hv
  rw [mem_relCent (hEL.trans hVnorm)]
  refine ⟨hVE hv, fun a ha => ?_⟩
  have hav : ⁅a, v⁆ ∈ V := by
    rw [commutatorElement_def]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVnorm (hTL ha)) v).mp hv) (V.inv_mem hv)
  simpa [commutatorElement_inv] using V.inv_mem hav

private theorem section_facts {L E V : Subgroup G} (hEL : E ≤ L)
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hVnorm : L ≤ Subgroup.normalizer (V : Set G)) (hEE : ⁅E, E⁆ ≤ V)
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ V) (hfix : relCent E V L = V)
    {F : Type} [Field F] {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hker : α.ker = (pCoreOf 2 L).subgroupOf L) :
    (∀ z : ↥L, ∀ c ∈ E.subgroupOf L, z * c * z⁻¹ ∈ E.subgroupOf L) ∧
      (∀ z : ↥L, ∀ l ∈ V.subgroupOf L, z * l * z⁻¹ ∈ V.subgroupOf L) ∧
      (∀ a ∈ E.subgroupOf L, ∀ b ∈ E.subgroupOf L, ⁅a, b⁆ ∈ V.subgroupOf L) ∧
      (∀ z : ↥L, α z = 1 → ∀ c ∈ E.subgroupOf L, ⁅z, c⁆ ∈ V.subgroupOf L) ∧
      (∀ c ∈ E.subgroupOf L, (∀ z : ↥L, ⁅z, c⁆ ∈ V.subgroupOf L) → c ∈ V.subgroupOf L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z c hc
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hLE z.2) (c : G)).mp hc
  · intro z l hl
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hVnorm z.2) (l : G)).mp hl
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using
      hEE (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))
  · intro z hz c hc
    have hzO : (z : G) ∈ pCoreOf 2 L := by
      have h1 : z ∈ α.ker := hz
      rw [hker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using
      hcore (z : G) hzO (c : G) (Subgroup.mem_subgroupOf.mp hc)
  · intro c hc h
    have hcE : (c : G) ∈ E := Subgroup.mem_subgroupOf.mp hc
    rw [Subgroup.mem_subgroupOf, ← hfix, mem_relCent (hEL.trans hVnorm)]
    refine ⟨hcE, fun a ha => ?_⟩
    have h1 : ⁅a, (c : G)⁆ ∈ V := Subgroup.mem_subgroupOf.mp (h ⟨a, ha⟩)
    simpa [commutatorElement_inv] using V.inv_mem h1

private theorem commPair_add_left {L E V Z : Subgroup G} {F : Type} [Field F]
    (hEE : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V) :
    ∀ a ∈ E.subgroupOf L, ∀ a' ∈ E.subgroupOf L, ∀ b ∈ E.subgroupOf L,
      commPair β₂ hEE (a * a') b = commPair β₂ hEE a b + commPair β₂ hEE a' b := by
  intro a ha a' ha' b hb
  have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
  have ha'E : (a' : G) ∈ E := Subgroup.mem_subgroupOf.mp ha'
  have hbE : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
  show commPair β₂ hEE ((a : G) * (a' : G)) (b : G) =
    commPair β₂ hEE (a : G) (b : G) + commPair β₂ hEE (a' : G) (b : G)
  have h1 : ⁅(a : G) * (a' : G), (b : G)⁆ ∈ V :=
    hEE (Subgroup.commutator_mem_commutator (E.mul_mem haE ha'E) hbE)
  have h2 : ⁅(a : G), (b : G)⁆ ∈ V := hEE (Subgroup.commutator_mem_commutator haE hbE)
  have h3 : ⁅(a' : G), (b : G)⁆ ∈ V := hEE (Subgroup.commutator_mem_commutator ha'E hbE)
  have hmem : (a : G) * ⁅(a' : G), (b : G)⁆ * (a : G)⁻¹ ∈ V := by
    rw [show (a : G) * ⁅(a' : G), (b : G)⁆ * (a : G)⁻¹ =
        ⁅(a : G), ⁅(a' : G), (b : G)⁆⁆ * ⁅(a' : G), (b : G)⁆ from by
      rw [commutatorElement_def]; group]
    exact V.mul_mem (hZV (hcent (Subgroup.commutator_mem_commutator haE h3))) h3
  rw [commPair_of_mem (E.mul_mem haE ha'E) hbE, commPair_of_mem haE hbE,
    commPair_of_mem ha'E hbE]
  have heq : (⟨⁅(a : G) * (a' : G), (b : G)⁆, h1⟩ : ↥V) =
      (⟨(a : G) * ⁅(a' : G), (b : G)⁆ * (a : G)⁻¹, hmem⟩ : ↥V) *
        ⟨⁅(a : G), (b : G)⁆, h2⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [heq, map_mul, toAdd_mul,
    toAdd_conj_eq hZV hcent hβ₂ker ⟨(a : G), haE⟩ ⟨⁅(a' : G), (b : G)⁆, h3⟩ hmem]
  exact add_comm _ _

private theorem commPair_add_right {L E V Z : Subgroup G} {F : Type} [Field F]
    (hEE : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V) :
    ∀ a ∈ E.subgroupOf L, ∀ b ∈ E.subgroupOf L, ∀ b' ∈ E.subgroupOf L,
      commPair β₂ hEE a (b * b') = commPair β₂ hEE a b + commPair β₂ hEE a b' := by
  intro a ha b hb b' hb'
  have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
  have hbE : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
  have hb'E : (b' : G) ∈ E := Subgroup.mem_subgroupOf.mp hb'
  show commPair β₂ hEE (a : G) ((b : G) * (b' : G)) =
    commPair β₂ hEE (a : G) (b : G) + commPair β₂ hEE (a : G) (b' : G)
  have h1 : ⁅(a : G), (b : G) * (b' : G)⁆ ∈ V :=
    hEE (Subgroup.commutator_mem_commutator haE (E.mul_mem hbE hb'E))
  have h2 : ⁅(a : G), (b : G)⁆ ∈ V := hEE (Subgroup.commutator_mem_commutator haE hbE)
  have h3 : ⁅(a : G), (b' : G)⁆ ∈ V := hEE (Subgroup.commutator_mem_commutator haE hb'E)
  have hmem : (b : G) * ⁅(a : G), (b' : G)⁆ * (b : G)⁻¹ ∈ V := by
    rw [show (b : G) * ⁅(a : G), (b' : G)⁆ * (b : G)⁻¹ =
        ⁅(b : G), ⁅(a : G), (b' : G)⁆⁆ * ⁅(a : G), (b' : G)⁆ from by
      rw [commutatorElement_def]; group]
    exact V.mul_mem (hZV (hcent (Subgroup.commutator_mem_commutator hbE h3))) h3
  rw [commPair_of_mem haE (E.mul_mem hbE hb'E), commPair_of_mem haE hbE,
    commPair_of_mem haE hb'E]
  have heq : (⟨⁅(a : G), (b : G) * (b' : G)⁆, h1⟩ : ↥V) =
      ⟨⁅(a : G), (b : G)⁆, h2⟩ *
        ⟨(b : G) * ⁅(a : G), (b' : G)⁆ * (b : G)⁻¹, hmem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [heq, map_mul, toAdd_mul,
    toAdd_conj_eq hZV hcent hβ₂ker ⟨(b : G), hbE⟩ ⟨⁅(a : G), (b' : G)⁆, h3⟩ hmem]

private theorem commPair_eq_zero_of_mem {L E V Z : Subgroup G} {F : Type} [Field F]
    (hEE : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hVE : V ≤ E) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V) :
    (∀ l ∈ V.subgroupOf L, ∀ b ∈ E.subgroupOf L, commPair β₂ hEE (l : G) (b : G) = 0) ∧
      (∀ a ∈ E.subgroupOf L, ∀ l ∈ V.subgroupOf L, commPair β₂ hEE (a : G) (l : G) = 0) := by
  constructor
  · intro l hl b hb
    have hlV : (l : G) ∈ V := Subgroup.mem_subgroupOf.mp hl
    have hbE : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
    have h1 : ⁅(b : G), (l : G)⁆ ∈ Z := hcent (Subgroup.commutator_mem_commutator hbE hlV)
    rw [commPair_of_mem (hVE hlV) hbE]
    exact (toAdd_eq_zero_iff_ker hβ₂ker _).mpr
      (by simpa [commutatorElement_inv] using Z.inv_mem h1)
  · intro a ha l hl
    have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hlV : (l : G) ∈ V := Subgroup.mem_subgroupOf.mp hl
    have h1 : ⁅(a : G), (l : G)⁆ ∈ Z := hcent (Subgroup.commutator_mem_commutator haE hlV)
    rw [commPair_of_mem haE (hVE hlV)]
    exact (toAdd_eq_zero_iff_ker hβ₂ker _).mpr h1

private theorem commPair_conj {L E V : Subgroup G} {F : Type} [Field F]
    (hEE : ⁅E, E⁆ ≤ V) (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hVnorm : L ≤ Subgroup.normalizer (V : Set G))
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₂act : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u)) :
    ∀ z : ↥L, ∀ a ∈ E.subgroupOf L, ∀ b ∈ E.subgroupOf L,
      commPair β₂ hEE ((z * a * z⁻¹ : ↥L) : G) ((z * b * z⁻¹ : ↥L) : G) =
        (α z : Matrix (Fin 2) (Fin 2) F) *ᵥ commPair β₂ hEE (a : G) (b : G) := by
  intro z a ha b hb
  have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
  have hbE : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
  have hazE : ((z * a * z⁻¹ : ↥L) : G) ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hLE z.2) (a : G)).mp haE
  have hbzE : ((z * b * z⁻¹ : ↥L) : G) ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hLE z.2) (b : G)).mp hbE
  have hcomm_a : ⁅(a : G), (b : G)⁆ ∈ V := hEE (Subgroup.commutator_mem_commutator haE hbE)
  have hconj : ⁅((z * a * z⁻¹ : ↥L) : G), ((z * b * z⁻¹ : ↥L) : G)⁆ =
      (z : G) * ⁅(a : G), (b : G)⁆ * (z : G)⁻¹ := by
    rw [show ((z * a * z⁻¹ : ↥L) : G) = (z : G) * (a : G) * (z : G)⁻¹ from rfl,
      show ((z * b * z⁻¹ : ↥L) : G) = (z : G) * (b : G) * (z : G)⁻¹ from rfl,
      conjugate_commutatorElement]
  rw [commPair_of_mem hazE hbzE, commPair_of_mem haE hbE]
  exact hβ₂act z ⟨⁅(a : G), (b : G)⁆, hcomm_a⟩ _ hconj

private theorem eq_subgroupOf_of_invariant {L E V T : Subgroup G} (hEL : E ≤ L) (hVL : V ≤ L)
    (hgen : ∀ Y : Subgroup G, V ≤ Y → Y ≤ E →
      L ≤ Subgroup.normalizer (Y : Set G) → relCent E V T ≤ Y → Y = E)
    (S : Subgroup ↥L) (hVS : V.subgroupOf L ≤ S) (hSE : S ≤ E.subgroupOf L)
    (hSn : ∀ z : ↥L, ∀ s ∈ S, z * s * z⁻¹ ∈ S)
    (hC₁S : (relCent E V T).subgroupOf L ≤ S) : S = E.subgroupOf L := by
  have hY : S.map L.subtype = E := by
    refine hgen (S.map L.subtype) ?_ ?_ ?_ ?_
    · intro v hv
      exact Subgroup.mem_map.mpr ⟨⟨v, hVL hv⟩, hVS (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_subgroupOf.mp (hSE hy)
    · rw [Subgroup.le_normalizer_iff]
      intro z hz x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨⟨z, hz⟩ * y * ⟨z, hz⟩⁻¹, hSn ⟨z, hz⟩ y hy, rfl⟩
    · intro g hg
      have hgL : g ∈ L := hEL hg.1
      exact Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, hC₁S (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  have hEimg : (E.subgroupOf L).map L.subtype = E := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEL]
  exact Subgroup.map_injective (Subgroup.subtype_injective L) (by rw [hY, hEimg])

theorem comm_le_of_quadratic {G : Type} [Group G] {P L E V Z T : Subgroup G} [Finite ↥P]
    {n : ℕ} (hn : 2 ≤ n) (hEL : E ≤ L) (hsec : IsElemSec V E)
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ V)
    (hfix : relCent E V L = V) (hT : IsSylowTwoOf T L)
    (hquad : ∀ t ∈ T, ∀ t' ∈ T, ∀ e ∈ E, ⁅t, ⁅t', e⁆⁆ ∈ V)
    (hgen : ∀ Y : Subgroup G, V ≤ Y → Y ≤ E →
      L ≤ Subgroup.normalizer (Y : Set G) → relCent E V T ≤ Y → Y = E)
    (hV : NatPre P L V Z n) (hVZ : NatQuot L V Z n)
    (hcent : ⁅E, V⁆ ≤ Z) : ⁅E, E⁆ ≤ Z := by
  classical
  have hVE : V ≤ E := hsec.1
  have hVL : V ≤ L := hVZ.E_le
  have hZV : Z ≤ V := hVZ.Z_le
  have hVnorm : L ≤ Subgroup.normalizer (V : Set G) := hVZ.normal.trans inf_le_left
  have hVP : V ≤ P := hVL.trans hV.le
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion hV.le) (Subgroup.inclusion_injective hV.le)
  obtain ⟨α, hαsurj, hαker, hUpper⟩ :=
    CFSG.GroupTheory.exists_SL2_hom_map_sylowTwo_eq_upperUnipotent hV.quot hT
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  have hK : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨β₂, -, hβ₂ker, hβ₂act⟩ :=
    NatPre.isNatSecOf (P := P) hn hF hαsurj hαker hV hVP hT (by rw [hVZ.line T hT])
  obtain ⟨hCn, hLn, hcomm', hker', hfix'⟩ :=
    section_facts hEL hLE hVnorm hsec.2.1 hcore hfix hαker
  have hLC₁ : V.subgroupOf L ≤ (relCent E V T).subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_relCent hEL hVE hVnorm hT.1 (Subgroup.mem_subgroupOf.mp hx))
  have hC₁C : (relCent E V T).subgroupOf L ≤ E.subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
  have hquad' := commutator_mem_of_mem_upperUnipotent hEL hLE hVnorm hT.1 hVE hcore hquad
    hαker hUpper
  have hL' := commutator_mem_of_mem_relCent (T := T) hVnorm hT.1 hcore hαker hUpper
  have hβ₁ := commPair_add_left (L := L) (E := E) (V := V) (Z := Z) (β₂ := β₂)
    hsec.2.1 hZV hcent hβ₂ker
  have hβ₂ := commPair_add_right (L := L) (E := E) (V := V) (Z := Z) (β₂ := β₂)
    hsec.2.1 hZV hcent hβ₂ker
  obtain ⟨hβL₁, hβL₂⟩ := commPair_eq_zero_of_mem (L := L) (E := E) (V := V) (Z := Z)
    (β₂ := β₂) hsec.2.1 hZV hVE hcent hβ₂ker
  have hβeq := commPair_conj (L := L) (E := E) (V := V) (α := α) (β₂ := β₂)
    hsec.2.1 hLE hVnorm hβ₂act
  have hgen' := eq_subgroupOf_of_invariant hEL hVL hgen
  have hmain := CFSG.RankThree.GF2n.Tim79.eq_zero_of_equivariant_pairing
    (Γ := ↥L) (K := GaloisField 2 n) hK α hαsurj (E.subgroupOf L) (V.subgroupOf L)
    ((relCent E V T).subgroupOf L) hLC₁ hC₁C hCn hLn hcomm' hker' hfix' hquad' hL' hgen'
    (fun a b => commPair β₂ hsec.2.1 (a : G) (b : G)) hβ₁ hβ₂ hβL₁ hβL₂ hβeq
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxL : x ∈ L := hEL hx
  have hyL : y ∈ L := hEL hy
  have hzero : commPair β₂ hsec.2.1 x y = 0 :=
    hmain ⟨x, hxL⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hyL⟩ (Subgroup.mem_subgroupOf.mpr hy)
  rw [commPair_of_mem hx hy] at hzero
  exact (toAdd_eq_zero_iff_ker hβ₂ker _).mp hzero

end CFSG.Quasithin.St84

end
