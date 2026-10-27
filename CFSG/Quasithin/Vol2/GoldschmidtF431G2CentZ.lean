module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentC
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Perf

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Scalars

variable (K : Type) [Field K]

@[expose] def XcScalars : Subgroup (ModGL Tag.G2 K) where
  carrier := {p | ∃ l : K, l ≠ 0 ∧ ∀ s : K, p * gX rC s * p⁻¹ = gX rC (l * s)}
  mul_mem' := by
    rintro p q ⟨l, hl, hp⟩ ⟨m, hm, hq⟩
    refine ⟨l * m, mul_ne_zero hl hm, fun s => ?_⟩
    calc p * q * gX rC s * (p * q)⁻¹ = p * (q * gX rC s * q⁻¹) * p⁻¹ := by group
      _ = p * gX rC (m * s) * p⁻¹ := by rw [hq]
      _ = gX rC (l * (m * s)) := hp _
      _ = gX rC (l * m * s) := by rw [mul_assoc]
  one_mem' := ⟨1, one_ne_zero, fun s => by simp⟩
  inv_mem' := by
    rintro p ⟨l, hl, hp⟩
    refine ⟨l⁻¹, inv_ne_zero hl, fun s => ?_⟩
    have h := hp (l⁻¹ * s)
    rw [mul_inv_cancel_left₀ hl] at h
    calc p⁻¹ * gX rC s * p⁻¹⁻¹ = p⁻¹ * (p * gX rC (l⁻¹ * s) * p⁻¹) * p := by rw [h, inv_inv]
      _ = gX rC (l⁻¹ * s) := by group

variable {K}

theorem mem_XcScalars {p : ModGL Tag.G2 K} :
    p ∈ XcScalars K ↔ ∃ l : K, l ≠ 0 ∧ ∀ s : K, p * gX rC s * p⁻¹ = gX rC (l * s) := Iff.rfl

end Scalars

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem isRoot_rC' : IsRoot Tag.G2 rC := (pos_TC rC (Set.mem_singleton _)).1

theorem torusGroup_le_XcScalars : torusGroup Tag.G2 K ≤ XcScalars K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact ⟨((t ^ ∑ j, Tag.G2.cartan i j * rC j : Kˣ) : K), Units.ne_zero _, fun s =>
    CFSG.Quasithin.H13.Sec53F.G2.conj_torus i isRoot_rC' t s⟩

theorem posUnipotent_le_XcScalars : posUnipotent Tag.G2 K ≤ XcScalars K := by
  intro q hq
  refine ⟨1, one_ne_zero, fun s => ?_⟩
  have hc : Commute q (gX rC s) :=
    rootSpan_commute (T := {α | IsRoot Tag.G2 α ∧ 0 < height α}) (fun β hβ c => by
      obtain h | h | h | h | h | h := isRoot_pos_iff.1 hβ <;> rw [h]
      · exact comm_ac c s
      · exact comm_rc c s
      · exact comm_uc c s
      · exact comm_vc c s
      · exact comm_bc c s
      · exact gX_comm_self _ c s) hq
  rw [one_mul]
  exact mul_inv_eq_iff_eq_mul.2 hc.eq

theorem weylElt_r_mem_XcScalars : weylElt Tag.G2 K i1 1 ∈ XcScalars K :=
  ⟨1, one_ne_zero, fun s => by rw [weylElt_conj_gX i1 isRoot_rC' s, reflect_r_c, one_mul]⟩

theorem parabolic_r_le_XcScalars : parabolicSubgroup Tag.G2 K {i1} ≤ XcScalars K :=
  sup_le (sup_le torusGroup_le_XcScalars posUnipotent_le_XcScalars)
    ((Subgroup.closure_le _).2 (by
      rintro _ ⟨j, hj, rfl⟩
      rw [Set.mem_singleton_iff.1 hj]
      exact weylElt_r_mem_XcScalars))

theorem commutator_mem_centralizer {p q : ModGL Tag.G2 K} (hp : p ∈ XcScalars K)
    (hq : q ∈ XcScalars K) (s : K) : ⁅p, q⁆ * gX rC s * ⁅p, q⁆⁻¹ = gX rC s := by
  obtain ⟨l, hl, hp⟩ := hp
  obtain ⟨m, hm, hq⟩ := hq
  have hpi : ∀ s : K, p⁻¹ * gX rC s * p = gX rC (l⁻¹ * s) := by
    intro s
    have h := hp (l⁻¹ * s)
    rw [mul_inv_cancel_left₀ hl] at h
    calc p⁻¹ * gX rC s * p = p⁻¹ * (p * gX rC (l⁻¹ * s) * p⁻¹) * p := by rw [h]
      _ = gX rC (l⁻¹ * s) := by group
  have hqi : ∀ s : K, q⁻¹ * gX rC s * q = gX rC (m⁻¹ * s) := by
    intro s
    have h := hq (m⁻¹ * s)
    rw [mul_inv_cancel_left₀ hm] at h
    calc q⁻¹ * gX rC s * q = q⁻¹ * (q * gX rC (m⁻¹ * s) * q⁻¹) * q := by rw [h]
      _ = gX rC (m⁻¹ * s) := by group
  calc ⁅p, q⁆ * gX rC s * ⁅p, q⁆⁻¹
      = p * (q * (p⁻¹ * (q⁻¹ * gX rC s * q) * p) * q⁻¹) * p⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = gX rC (l * (m * (l⁻¹ * (m⁻¹ * s)))) := by rw [hqi, hpi, hq, hp]
    _ = gX rC s := by
        congr 1
        field_simp

theorem perfectCore_commute {y : ModGL Tag.G2 K}
    (hy : y ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1})) (s : K) :
    y * gX rC s = gX rC s * y := by
  have h1 : y ∈ ⁅parabolicSubgroup Tag.G2 K {i1}, parabolicSubgroup Tag.G2 K {i1}⁆ :=
    (iInf_le (fun n => derivedSeriesOf (parabolicSubgroup Tag.G2 K {i1}) n) 1) hy
  have h2 : ⁅parabolicSubgroup Tag.G2 K {i1}, parabolicSubgroup Tag.G2 K {i1}⁆ ≤
      Subgroup.centralizer ({gX rC s} : Set (ModGL Tag.G2 K)) := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    exact mul_inv_eq_iff_eq_mul.1 (commutator_mem_centralizer (parabolic_r_le_XcScalars hp)
      (parabolic_r_le_XcScalars hq) s)
  exact Subgroup.mem_centralizer_singleton_iff.1 (h2 h1)

variable [Finite K]

theorem Xc_le_centerOf_perfectCore_Pr (hK4 : 4 ≤ Nat.card K) :
    Xc K ≤ centerOf (perfectCore (Pr K)) := by
  rintro _ ⟨s, rfl⟩
  have hPC : parabolicSubgroup Tag.G2 K {i1} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup Tag.G2 K {i1}
  refine (CFSG.Quasithin.H13.Sec53F.G2.mem_centerOf_perfectCore_subgroupOf hPC (xc s)).2
    ⟨?_, fun y hy => perfectCore_commute hy s⟩
  exact CFSG.Quasithin.H13.Sec53F.G2.radical_le_perfectCore_one hK4
    (mem_one (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) s)

end Main

end CFSG.Quasithin.H13.F431.G2.Cent
