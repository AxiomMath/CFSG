module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.H13.NQBlockOddResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE2

open Subgroup CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem xiP_eq_map (L : Subgroup G) (p : ℕ) :
    xiP L p = (closure {e : ↥L | e ∈ (closure {c : ↥L ⧸ CFSG.pCore 2 ↥L |
      c ∈ CFSG.pCore p (↥L ⧸ CFSG.pCore 2 ↥L) ∧ c ^ p = 1}).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∧ Odd (orderOf e)}).map L.subtype := by
  rw [xiP, oTwoUpper, preimageModTwoCore, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨hg, hodd⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨e, ⟨he, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hodd⟩, rfl⟩
  · rintro ⟨e, ⟨he, hodd⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ he, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]⟩

theorem mem_map_iff {L : Subgroup G} {Xq : Subgroup ↥L} {g : G} :
    g ∈ Xq.map L.subtype ↔ ∃ x : ↥Xq, ((x : ↥L) : G) = g := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

theorem pCoreOf_map {L : Subgroup G} (Xq : Subgroup ↥L) :
    pCoreOf 2 (Xq.map L.subtype) = ((CFSG.pCore 2 ↥Xq).map Xq.subtype).map L.subtype := by
  set eX : ↥Xq ≃* ↥(Xq.map L.subtype) := Xq.equivMapOfInjective L.subtype L.subtype_injective
  have hpc : (CFSG.pCore 2 ↥Xq).map (eX : ↥Xq →* ↥(Xq.map L.subtype)) =
      CFSG.pCore 2 ↥(Xq.map L.subtype) := CFSG.pCore_map_iso 2 eX
  rw [pCoreOf, ← hpc, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem pow_mem_pCoreOf {L : Subgroup G} {Xq : Subgroup ↥L} {p : ℕ}
    (hexp : Monoid.exponent (↥Xq ⧸ CFSG.pCore 2 ↥Xq) = p) {g : G}
    (hg : g ∈ Xq.map L.subtype) : g ^ p ∈ pCoreOf 2 (Xq.map L.subtype) := by
  obtain ⟨x, rfl⟩ := mem_map_iff.mp hg
  rw [pCoreOf_map]
  have h1 : ((x ^ p : ↥Xq) : ↥Xq ⧸ CFSG.pCore 2 ↥Xq) = 1 := by
    rw [QuotientGroup.mk_pow, ← hexp, Monoid.pow_exponent_eq_one]
  have h2 : x ^ p ∈ CFSG.pCore 2 ↥Xq := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨((x ^ p : ↥Xq) : ↥L), ⟨x ^ p, h2, rfl⟩, rfl⟩

theorem relIndex_map {L : Subgroup G} (Xq : Subgroup ↥L) :
    (pCoreOf 2 (Xq.map L.subtype)).relIndex (Xq.map L.subtype) =
      Nat.card (↥Xq ⧸ CFSG.pCore 2 ↥Xq) := by
  set X := Xq.map L.subtype
  set eX : ↥Xq ≃* ↥X := Xq.equivMapOfInjective L.subtype L.subtype_injective
  have hpc : (CFSG.pCore 2 ↥Xq).map (eX : ↥Xq →* ↥X) = CFSG.pCore 2 ↥X :=
    CFSG.pCore_map_iso 2 eX
  have h1 : (pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X := by
    rw [pCoreOf]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [Subgroup.relIndex, h1, Subgroup.index]
  exact (Nat.card_congr (QuotientGroup.congr _ _ eX hpc).toEquiv).symm

theorem not_commutator_le {L : Subgroup G} {Xq : Subgroup ↥L}
    (h : ¬ IsMulCommutative (↥Xq ⧸ CFSG.pCore 2 ↥Xq)) :
    ¬ ⁅Xq.map L.subtype, Xq.map L.subtype⁆ ≤ pCoreOf 2 (Xq.map L.subtype) := by
  intro hle
  apply h
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hxy := hle (Subgroup.commutator_mem_commutator (mem_map_iff.mpr ⟨x, rfl⟩)
    (mem_map_iff.mpr ⟨y, rfl⟩))
  rw [pCoreOf_map] at hxy
  obtain ⟨l, ⟨c, hc, rfl⟩, hl⟩ := hxy
  have hc' : c = ⁅x, y⁆ := Subtype.ext (Subtype.ext hl)
  have h1 : ((⁅x, y⁆ : ↥Xq) : ↥Xq ⧸ CFSG.pCore 2 ↥Xq) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hc' ▸ hc)
  rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
  calc (x : ↥Xq ⧸ CFSG.pCore 2 ↥Xq) * y =
        ((x : ↥Xq ⧸ CFSG.pCore 2 ↥Xq) * y * (x : ↥Xq ⧸ CFSG.pCore 2 ↥Xq)⁻¹ *
          (y : ↥Xq ⧸ CFSG.pCore 2 ↥Xq)⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem frattini_le_commutator {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p Q) (hexp : Monoid.exponent Q = p) : frattini Q ≤ commutator Q := by
  have : Fact (IsPGroup p Q) := ⟨hQ⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p), Subgroup.closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · exact hx
  · show y ^ p ∈ (commutator Q : Set Q)
    rw [← hexp, Monoid.pow_exponent_eq_one]
    exact (commutator Q).one_mem

theorem mem_commutator_sup_of_mem_frattini {L : Subgroup G} {Xq : Subgroup ↥L} {p : ℕ}
    [Fact p.Prime] [Finite ↥Xq] (hpg : IsPGroup p (↥Xq ⧸ CFSG.pCore 2 ↥Xq))
    (hexp : Monoid.exponent (↥Xq ⧸ CFSG.pCore 2 ↥Xq) = p) (x : ↥Xq)
    (hx : (x : ↥Xq ⧸ CFSG.pCore 2 ↥Xq) ∈ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq)) :
    ((x : ↥L) : G) ∈ ⁅Xq.map L.subtype, Xq.map L.subtype⁆ ⊔ pCoreOf 2 (Xq.map L.subtype) := by
  have hc := frattini_le_commutator hpg hexp hx
  have hcm : commutator (↥Xq ⧸ CFSG.pCore 2 ↥Xq) =
      (commutator ↥Xq).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Xq)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  rw [hcm] at hc
  obtain ⟨c, hcX, hcx⟩ := hc
  have hd : c⁻¹ * x ∈ CFSG.pCore 2 ↥Xq := QuotientGroup.eq.mp hcx
  have e1 : (commutator ↥Xq).map (L.subtype.comp Xq.subtype) =
      ⁅Xq.map L.subtype, Xq.map L.subtype⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have h1 : ((c : ↥L) : G) ∈ ⁅Xq.map L.subtype, Xq.map L.subtype⁆ :=
    e1 ▸ Subgroup.mem_map_of_mem _ hcX
  have h2 : (((c⁻¹ * x : ↥Xq) : ↥L) : G) ∈ pCoreOf 2 (Xq.map L.subtype) := by
    rw [pCoreOf_map]
    exact ⟨_, ⟨_, hd, rfl⟩, rfl⟩
  have e2 : ((x : ↥L) : G) = ((c : ↥L) : G) * (((c⁻¹ * x : ↥Xq) : ↥L) : G) := by simp
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

theorem eq_or_eq_of_residual {L : Subgroup G} (Xq : Subgroup ↥L) [Xq.Characteristic] {p : ℕ}
    [Fact p.Prime] [Finite ↥Xq] (hpg : IsPGroup p (↥Xq ⧸ CFSG.pCore 2 ↥Xq))
    (hexp : Monoid.exponent (↥Xq ⧸ CFSG.pCore 2 ↥Xq) = p) {T : Subgroup G}
    (hirr : ∀ M : Subgroup ((↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq)),
      (∀ s : ↥L, (s : G) ∈ T → ∀ w ∈ M, H13.NQBlock.residualAction Xq s w ∈ M) →
        M = ⊥ ∨ M = ⊤)
    {Y : Subgroup G}
    (hY1 : ⁅Xq.map L.subtype, Xq.map L.subtype⁆ ⊔ pCoreOf 2 (Xq.map L.subtype) ≤ Y)
    (hY2 : Y ≤ Xq.map L.subtype) (hYT : T ≤ normalizer (Y : Set G)) :
    Y = ⁅Xq.map L.subtype, Xq.map L.subtype⁆ ⊔ pCoreOf 2 (Xq.map L.subtype) ∨
      Y = Xq.map L.subtype := by
  set π : ↥Xq →* (↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq) :=
    (QuotientGroup.mk' (frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Xq))
  set M := (Y.comap (L.subtype.comp Xq.subtype)).map π
  have hMinv : ∀ s : ↥L, (s : G) ∈ T → ∀ w ∈ M, H13.NQBlock.residualAction Xq s w ∈ M := by
    rintro s hs _ ⟨y, hy, rfl⟩
    refine ⟨MulAut.conjNormal s y, ?_, rfl⟩
    show (s : G) * ((y : ↥L) : G) * (s : G)⁻¹ ∈ Y
    exact (Subgroup.mem_normalizer_iff.mp (hYT hs) _).mp hy
  have hπ1 : ∀ x : ↥Xq, π x = 1 →
      ((x : ↥L) : G) ∈ ⁅Xq.map L.subtype, Xq.map L.subtype⁆ ⊔ pCoreOf 2 (Xq.map L.subtype) :=
    fun x hx => mem_commutator_sup_of_mem_frattini hpg hexp x ((QuotientGroup.eq_one_iff _).mp hx)
  rcases hirr M hMinv with h0 | ht
  · left
    refine le_antisymm (fun g hg => ?_) hY1
    obtain ⟨x, rfl⟩ := mem_map_iff.mp (hY2 hg)
    have hxM : π x ∈ M := ⟨x, hg, rfl⟩
    rw [h0, Subgroup.mem_bot] at hxM
    exact hπ1 x hxM
  · right
    refine le_antisymm hY2 (fun g hg => ?_)
    obtain ⟨x, rfl⟩ := mem_map_iff.mp hg
    obtain ⟨y, hy, hyx⟩ : π x ∈ M := ht ▸ Subgroup.mem_top _
    have h1 : π (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have e : ((x : ↥L) : G) = ((y : ↥L) : G) * (((y⁻¹ * x : ↥Xq) : ↥L) : G) := by simp
    rw [e]
    exact Y.mul_mem hy (hY1 (hπ1 _ h1))

end CFSG.Quasithin.Vol2.Ch11.OE2
