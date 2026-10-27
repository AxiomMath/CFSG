module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Bar

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar

variable {Y : Type} [Group Y] {G : Type} [Group G]

@[expose] noncomputable def indHom (L : Subgroup Y) (e : Qbar L ≃* G) :
    ↥(normalizer (L : Set Y)) →* MulAut G :=
  (MulAut.congr e).toMonoidHom.comp (barHom L)

variable {L : Subgroup Y} (e : Qbar L ≃* G)

theorem indHom_apply (b : ↥(normalizer (L : Set Y))) (q : Qbar L) :
    indHom L e b (e q) = e (barHom L b q) := by
  simp [indHom, MulAut.congr_apply]

theorem indHom_eq_one_iff (hperf : Group.IsPerfect ↥L) (b : ↥(normalizer (L : Set Y))) :
    indHom L e b = 1 ↔ ∀ x : ↥L, (b : Y) * x = x * b := by
  rw [← barHom_eq_one_iff hperf]
  constructor
  · intro h
    refine MulEquiv.ext fun q => e.injective ?_
    have := indHom_apply e b q
    rw [h] at this
    exact this.symm
  · intro h
    refine MulEquiv.ext fun g => ?_
    obtain ⟨q, rfl⟩ := e.surjective g
    rw [indHom_apply, h]
    rfl

@[expose] def InvSet (D : Subgroup G) : Set (MulAut G) :=
  {β | β ≠ 1 ∧ β * β = 1 ∧ ∀ d ∈ D, β * MulAut.conj d = MulAut.conj d * β}

@[expose] def imgBar (L P : Subgroup Y) : Subgroup (Qbar L) :=
  (P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))

theorem mem_imgBar {P : Subgroup Y} {q : Qbar L} :
    q ∈ imgBar L P ↔ ∃ x : ↥L, (x : Y) ∈ P ∧ (QuotientGroup.mk x : Qbar L) = q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem indHom_fix {P : Subgroup Y} (b : ↥(normalizer (L : Set Y)))
    (hb : ∀ p ∈ P, (b : Y) * p = p * b) (g : G) (hg : g ∈ (imgBar L P).map e.toMonoidHom) :
    indHom L e b g = g := by
  obtain ⟨q, hq, rfl⟩ := hg
  obtain ⟨x, hx, rfl⟩ := mem_imgBar.1 hq
  rw [MulEquiv.coe_toMonoidHom, indHom_apply, barHom_mk_of_comm b x (hb x hx)]

theorem indHom_commute {P : Subgroup Y} {D : Subgroup G}
    (hD : (imgBar L P).map e.toMonoidHom = D) (b : ↥(normalizer (L : Set Y)))
    (hb : ∀ p ∈ P, (b : Y) * p = p * b) (d : G) (hd : d ∈ D) :
    indHom L e b * MulAut.conj d = MulAut.conj d * indHom L e b := by
  have hfix := indHom_fix e b hb d (hD ▸ hd)
  refine MulEquiv.ext fun g => ?_
  change indHom L e b (d * g * d⁻¹) = d * indHom L e b g * d⁻¹
  rw [map_mul, map_mul, map_inv, hfix]

structure AltModel (G : Type) [Group G] (D : Subgroup G) : Prop where
  encard_le : (InvSet D).encard ≤ 3
  gen : ⨆ β ∈ InvSet D, fixedSub β = ⊤
  cases : ∀ β ∈ InvSet D, Group.IsSolvable ↥(fixedSub β) ∨
    ∃ N : Subgroup G, N ≤ fixedSub β ∧ Nat.card N = 60 ∧
      ∀ H : Subgroup G, H ≤ fixedSub β → Group.IsPerfect ↥H → H ≤ N

end CFSG.Quasithin.E6.Alt
