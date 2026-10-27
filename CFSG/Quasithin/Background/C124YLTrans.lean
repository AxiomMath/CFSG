module

public import CFSG.Quasithin.Background.C124YLBase
public import CFSG.Quasithin.Background.B4Models

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open

variable {W : Type*} [CommGroup W] {Q : Type*} [CommGroup Q]

structure IsCoord (U Z : Subgroup W) (c : ↥U →* Q) : Prop where
  Z_le : Z ≤ U
  surj : Function.Surjective c
  ker : ∀ u : ↥U, c u = 1 ↔ (u : W) ∈ Z

@[expose] def fixImg (U Z : Subgroup W) (c : ↥U →* Q) (B : Subgroup (MulAut W)) : Subgroup Q :=
  ((liftFix U Z B).subgroupOf U).map c

section Card

variable {U Z : Subgroup W} {c : ↥U →* Q}

theorem IsCoord.ker_eq (h : IsCoord U Z c) : c.ker = Z.subgroupOf U := by
  ext u
  rw [MonoidHom.mem_ker, h.ker, Subgroup.mem_subgroupOf]

theorem IsCoord.card_U (h : IsCoord U Z c) : Nat.card U = Nat.card Z * Nat.card Q := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective h.surj
  have h2 : Nat.card c.ker = Nat.card Z := by
    rw [h.ker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le).toEquiv
  rw [← h1, h2]

theorem mem_fixImg {B : Subgroup (MulAut W)} {q : Q} :
    q ∈ fixImg U Z c B ↔ ∃ u : ↥U, c u = q ∧ ∀ b ∈ B, b (u : W) * (u : W)⁻¹ ∈ Z := by
  unfold fixImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rfl, (mem_liftFix.1 (Subgroup.mem_subgroupOf.1 hu)).2⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨u, Subgroup.mem_subgroupOf.2 (mem_liftFix.2 ⟨u.2, hu⟩), rfl⟩

variable [Finite W]

theorem IsCoord.card_liftFix (h : IsCoord U Z c) {B : Subgroup (MulAut W)}
    (hZB : Z ≤ liftFix U Z B) :
    Nat.card (liftFix U Z B) = Nat.card Z * Nat.card (fixImg U Z c B) := by
  set F := (liftFix U Z B).subgroupOf U with hF
  have h1 : c.ker.relIndex F = Nat.card (F.map c) := Subgroup.relIndex_ker F c
  have h1' : F.map c = fixImg U Z c B := rfl
  rw [h1'] at h1
  have h2 := Subgroup.relIndex_mul_card c.ker F
  have hker : c.ker ≤ F := by
    rw [h.ker_eq]
    intro z hz
    exact Subgroup.mem_subgroupOf.2 (hZB (Subgroup.mem_subgroupOf.1 hz))
  rw [inf_eq_left.2 hker, h1] at h2
  have h3 : Nat.card c.ker = Nat.card Z := by
    rw [h.ker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le).toEquiv
  have h4 : Nat.card F = Nat.card (liftFix U Z B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (liftFix_le U Z B)).toEquiv
  rw [h3] at h2
  rw [← h4, ← h2, mul_comm]

theorem IsCoord.woff_iff (h : IsCoord U Z c) {B : Subgroup (MulAut W)}
    (hZB : Z ≤ liftFix U Z B) :
    WOff U Z B ↔ B ≠ ⊥ ∧ IsElemAbelian2 B ∧
      Nat.card Q ≤ Nat.card B * Nat.card (fixImg U Z c B) := by
  unfold WOff
  rw [h.card_U, h.card_liftFix hZB]
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have e : Nat.card B * (Nat.card Z * Nat.card (fixImg U Z c B)) =
      Nat.card Z * (Nat.card B * Nat.card (fixImg U Z c B)) := by ring
  rw [e]
  exact and_congr_right fun _ => and_congr_right fun _ => Nat.mul_le_mul_left_iff hZpos

end Card

section Equivariant

variable {U Z : Subgroup W} {c : ↥U →* Q} {M : Type*} [Group M] (φ : M →* MulAut W)
  (act : M → Q → Q)

theorem IsCoord.mem_fixImg_map (h : IsCoord U Z c) (hφ : ∀ γ, ∀ u ∈ U, φ γ u ∈ U)
    (hc : ∀ γ (u : ↥U), c ⟨φ γ u, hφ γ u u.2⟩ = act γ (c u)) (B : Subgroup M) (q : Q) :
    q ∈ fixImg U Z c (B.map φ) ↔ ∀ γ ∈ B, act γ q = q := by
  have key : ∀ γ (u : ↥U), φ γ (u : W) * (u : W)⁻¹ ∈ Z ↔ act γ (c u) = c u := by
    intro γ u
    have h1 := h.ker (⟨φ γ u, hφ γ u u.2⟩ * u⁻¹)
    rw [map_mul, map_inv, hc γ u, mul_inv_eq_one] at h1
    exact h1.symm
  rw [mem_fixImg]
  constructor
  · rintro ⟨u, rfl, hu⟩ γ hγ
    exact (key γ u).1 (hu _ (Subgroup.mem_map_of_mem φ hγ))
  · intro hq
    obtain ⟨u, rfl⟩ := h.surj q
    refine ⟨u, rfl, ?_⟩
    rintro b ⟨γ, hγ, rfl⟩
    exact (key γ u).2 (hq γ hγ)

end Equivariant

section Realizes

theorem coord_of_realizes {V : Type*} [CommGroup V] {D : FFModel} (hsec : ∀ m : D.Amb, m ∈ D.sec)
    (hker : ∀ m ∈ D.ker, m = 1) {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    ∃ c : ↥U →* D.Amb, IsCoord U Z c ∧ ∀ γ (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        c ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = D.act γ (c u) := by
  obtain ⟨-, hZU, -, -, -, hs, -, β, hβs, hβk, hβ⟩ := h
  have hN : D.ker.subgroupOf D.sec = ⊥ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    exact ⟨fun hx => Subtype.ext (hker _ hx), fun hx => by rw [hx]; exact D.ker.one_mem⟩
  let e1 : (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≃* ↥D.sec :=
    (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
  let e2 : ↥D.sec ≃* D.Amb :=
    MulEquiv.ofBijective D.sec.subtype ⟨Subtype.val_injective, fun a => ⟨⟨a, hsec a⟩, rfl⟩⟩
  let e : (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≃* D.Amb := e1.trans e2
  have he : ∀ m : ↥D.sec, e (QuotientGroup.mk m) = (m : D.Amb) := fun m => rfl
  refine ⟨e.toMonoidHom.comp β, ⟨hZU, ?_, ?_⟩, ?_⟩
  · intro a
    obtain ⟨q, hq⟩ := hβs (e.symm a)
    exact ⟨q, by simpa using congrArg e hq⟩
  · intro u
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hβk u]
    exact ⟨fun h1 => e.injective (by simpa using h1), fun h1 => by rw [h1]; simp⟩
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβ γ u m hu (hs γ m m.2) hm.symm
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, ← hm]
    rfl

end Realizes

end CFSG.Quasithin.C124.YL
