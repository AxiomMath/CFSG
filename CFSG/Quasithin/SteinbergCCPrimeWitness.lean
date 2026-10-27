module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

@[expose] noncomputable def coreQuotConj (X : Subgroup H) [X.Normal] :
    H →* MulAut (X ⧸ CFSG.pCore 2 X) :=
  (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 X)).comp MulAut.conjNormal

theorem coreQuotConj_mk (X : Subgroup H) [X.Normal] (h : H) (x : X) :
    coreQuotConj X h (x : X ⧸ CFSG.pCore 2 X) =
      ((MulAut.conjNormal h x : X) : X ⧸ CFSG.pCore 2 X) :=
  rfl

@[expose] noncomputable def frattiniQuotConj (X : Subgroup H) [X.Normal] :
    H →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  (CFSG.SectionRank.Ccomm.autQuotient (frattini (X ⧸ CFSG.pCore 2 X))).comp (coreQuotConj X)

theorem frattiniQuotConj_mk (X : Subgroup H) [X.Normal] (h : H) (v : X ⧸ CFSG.pCore 2 X) :
    frattiniQuotConj X h (v : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
      ((coreQuotConj X h v : X ⧸ CFSG.pCore 2 X) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

theorem le_pCore_of_normal_of_isPGroup {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    (hN : N.Normal) (hNp : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup ⟨hN, hNp⟩

theorem conj_mem_commutator_left {X Y : Subgroup H} {z : H} (hz : z ∈ X) {c : H}
    (hc : c ∈ ⁅X, Y⁆) : z * c * z⁻¹ ∈ ⁅X, Y⁆ := by
  have hle : ⁅X, Y⁆ ≤ ⁅X, Y⁆.comap (MulAut.conj z).toMonoidHom := by
    rw [commutator_le]
    intro x hx y hy
    rw [mem_comap]
    change z * ⁅x, y⁆ * z⁻¹ ∈ ⁅X, Y⁆
    have e : z * ⁅x, y⁆ * z⁻¹ = ⁅z * x, y⁆ * ⁅z, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (commutator_mem_commutator (mul_mem hz hx) hy)
      (inv_mem (commutator_mem_commutator hz hy))
  exact hle hc

theorem conj_mem_commutator_right {X Y : Subgroup H} {z : H} (hz : z ∈ Y) {c : H}
    (hc : c ∈ ⁅X, Y⁆) : z * c * z⁻¹ ∈ ⁅X, Y⁆ := by
  have hle : ⁅X, Y⁆ ≤ ⁅X, Y⁆.comap (MulAut.conj z).toMonoidHom := by
    rw [commutator_le]
    intro x hx y hy
    rw [mem_comap]
    change z * ⁅x, y⁆ * z⁻¹ ∈ ⁅X, Y⁆
    have e : z * ⁅x, y⁆ * z⁻¹ = ⁅x, z⁆⁻¹ * ⁅x, z * y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (commutator_mem_commutator hx hz))
      (commutator_mem_commutator hx (mul_mem hz hy))
  exact hle hc

theorem commutator_eq_of_irreducible_frattini [Finite H] (X : Subgroup H) [X.Normal]
    (Y : Subgroup H) (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y ∈ Y, ∀ u ∈ U, frattiniQuotConj X y u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ y ∈ Y, ∃ w, frattiniQuotConj X y w ≠ w) : ⁅X, Y⁆ = X := by
  have hZX : ⁅X, Y⁆ ≤ X := commutator_le_left X Y
  have : (⁅X, Y⁆.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact conj_mem_commutator_left g.2 hn⟩
  let π := QuotientGroup.mk' (CFSG.pCore 2 X)
  let σ := QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))
  let U := ((⁅X, Y⁆.subgroupOf X).map π).map σ
  have hUY : ∀ y ∈ Y, ∀ u ∈ U, frattiniQuotConj X y u ∈ U := by
    rintro y hy _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨π (MulAut.conjNormal y z), ⟨MulAut.conjNormal y z, ?_, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
    exact conj_mem_commutator_right hy (mem_subgroupOf.mp hz)
  have hUne : U ≠ ⊥ := by
    obtain ⟨y, hy, w, hw⟩ := hnt
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (frattini (X ⧸ CFSG.pCore 2 X)) w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) v
    intro hbot
    apply hw
    have hc : (MulAut.conjNormal y x * x⁻¹ : X) ∈ ⁅X, Y⁆.subgroupOf X := by
      rw [mem_subgroupOf, Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
      have e : (y : H) * x * y⁻¹ * (x : H)⁻¹ = ⁅(x : H), y⁆⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def]
      rw [e]
      exact inv_mem (commutator_mem_commutator x.2 hy)
    have h1 : σ (π (MulAut.conjNormal y x * x⁻¹)) ∈ U := ⟨_, ⟨_, hc, rfl⟩, rfl⟩
    rw [hbot, mem_bot, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hUtop : U = ⊤ := (hirr U hUY).resolve_left hUne
  have hsup : (⁅X, Y⁆.subgroupOf X).map π ⊔ frattini (X ⧸ CFSG.pCore 2 X) = ⊤ := by
    have h := congrArg (Subgroup.comap σ) hUtop
    rwa [comap_map_eq, comap_top, QuotientGroup.ker_mk'] at h
  have hπZ : (⁅X, Y⁆.subgroupOf X).map π = ⊤ := frattini_nongenerating hsup
  have h2 : IsPGroup 2 (X ⧸ ⁅X, Y⁆.subgroupOf X) := by
    refine CFSG.pCore_isPGroup.of_surjective
      ((QuotientGroup.mk' (⁅X, Y⁆.subgroupOf X)).comp (CFSG.pCore 2 X).subtype) ?_
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    have hx : π x ∈ (⁅X, Y⁆.subgroupOf X).map π := hπZ ▸ mem_top _
    obtain ⟨z, hz, hzx⟩ := hx
    have hk : z⁻¹ * x ∈ CFSG.pCore 2 X := QuotientGroup.eq.mp hzx
    refine ⟨⟨z⁻¹ * x, hk⟩, ?_⟩
    change ((z⁻¹ * x : X) : X ⧸ ⁅X, Y⁆.subgroupOf X) = (x : X ⧸ ⁅X, Y⁆.subgroupOf X)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z⁻¹).mpr (inv_mem hz), one_mul]
  have h3 := hX2 (⁅X, Y⁆.subgroupOf X) h2
  refine le_antisymm hZX fun x hx => ?_
  have h4 : (⟨x, hx⟩ : X) ∈ ⁅X, Y⁆.subgroupOf X := h3 ▸ mem_top _
  exact mem_subgroupOf.mp h4

end CFSG.Quasithin.SteinbergCC
