module

public import CFSG.Quasithin.H13.AS91Sec7Zfix
public import CFSG.Quasithin.H13.AS91Sec7Geom

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem E_fix_line {e : G} (he : e ∈ c.E) {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) :
    e • m = m := by
  obtain ⟨h, rfl⟩ := c.exists_G1_smul_l0 hm
  have hc : (h : G)⁻¹ * e * (h : G) ∈ c.E := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem h.2) e).mp he
    rwa [inv_inv] at h1
  have hstab : stabilizer G c.l0 = c.G2 := stabilizer_mk_one c.G2
  have hfix : ((h : G)⁻¹ * e * (h : G)) • c.l0 = c.l0 := by
    rw [← mem_stabilizer_iff, hstab]
    exact c.E_le_G2 hc
  have key : e * (h : G) = (h : G) * ((h : G)⁻¹ * e * (h : G)) := by group
  rw [← mul_smul, key, mul_smul, hfix]

@[expose] def Eker (m : G ⧸ c.G2) : Subgroup G where
  carrier := {e | e ∈ c.E ∧ ∀ a, c.OnL a m → e • a = a}
  mul_mem' := by
    rintro e₁ e₂ ⟨he₁, h₁⟩ ⟨he₂, h₂⟩
    refine ⟨c.E.mul_mem he₁ he₂, fun a ha => ?_⟩
    rw [mul_smul, h₂ a ha, h₁ a ha]
  one_mem' := ⟨c.E.one_mem, fun a _ => one_smul G a⟩
  inv_mem' := by
    rintro e ⟨he, h⟩
    refine ⟨c.E.inv_mem he, fun a ha => ?_⟩
    rw [inv_smul_eq_iff, h a ha]

theorem mem_Eker {m : G ⧸ c.G2} {e : G} :
    e ∈ c.Eker m ↔ e ∈ c.E ∧ ∀ a, c.OnL a m → e • a = a :=
  Iff.rfl

theorem E_inf_stab_eq_Eker {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) {y : G ⧸ c.G1} (hy : c.OnL y m)
    (hyx : y ≠ c.x0) : c.E ⊓ stabilizer G y = c.Eker m := by
  ext e
  rw [Subgroup.mem_inf, mem_stabilizer_iff, mem_Eker]
  constructor
  · rintro ⟨he, hey⟩
    refine ⟨he, fun a ha => ?_⟩
    by_cases hax : a = c.x0
    · rw [hax]
      exact c.smul_x0_of_mem (c.E_le_G1 he)
    · exact c.E_fix_all_of_fix hm he hy hyx ha hax hey
  · rintro ⟨he, hfix⟩
    exact ⟨he, hfix y hy⟩

private theorem ncard_onL_diff {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) :
    ({a | c.OnL a m} \ {c.x0}).ncard = 4 := by
  have hx : c.x0 ∈ {a | c.OnL a m} := hm
  rw [Set.ncard_diff_singleton_of_mem hx, c.ncard_onL m]

theorem card_Eker {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) : Nat.card (c.Eker m) = 2 ^ 9 := by
  have hne : ({a | c.OnL a m} \ {c.x0}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [c.ncard_onL_diff hm]; norm_num)
  obtain ⟨y, hyL, hyx⟩ : ∃ y, c.OnL y m ∧ y ≠ c.x0 := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy.1, hy.2⟩
  have horb : MulAction.orbit ↥c.E y = {a | c.OnL a m} \ {c.x0} := by
    ext a
    constructor
    · rintro ⟨⟨e, he⟩, rfl⟩
      have hfix := c.E_fix_line he hm
      have hyL' : c.OnL (e • y) m := by
        have h1 := (cInc_smul c.G1 c.G2 e y m).mpr hyL
        rw [hfix] at h1
        exact h1
      refine ⟨hyL', ?_⟩
      intro h
      have h' : e • y = c.x0 := h
      exact hyx (MulAction.injective e (h'.trans (c.smul_x0_of_mem (c.E_le_G1 he)).symm))
    · rintro ⟨ha, hax⟩
      obtain ⟨e, he, hea⟩ := c.E_transitive_line hm hyL hyx ha hax
      exact ⟨⟨e, he⟩, hea⟩
  have h4 : (MulAction.orbit ↥c.E y).ncard = 4 := by
    rw [horb, c.ncard_onL_diff hm]
  have hidx : (stabilizer ↥c.E y).index = 4 := by
    rw [MulAction.index_stabilizer, h4]
  have hrel : (stabilizer G y).relIndex c.E = 4 := by
    rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf]
    exact hidx
  have hmul := Subgroup.relIndex_mul_card (H := stabilizer G y) (K := c.E)
  rw [hrel, inf_comm, c.E_inf_stab_eq_Eker hm hyL hyx, c.card_E] at hmul
  norm_num at hmul ⊢
  omega

theorem conj_mem_Eker_iff (h : ↥c.G1) {m : G ⧸ c.G2} {e : G} :
    (h : G) * e * (h : G)⁻¹ ∈ c.Eker ((h : G) • m) ↔ e ∈ c.Eker m := by
  rw [mem_Eker, mem_Eker]
  constructor
  · rintro ⟨hE, hfix⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h.2 e).mpr hE, fun b hb => ?_⟩
    have hb' : c.OnL ((h : G) • b) ((h : G) • m) := (cInc_smul c.G1 c.G2 (h : G) b m).mpr hb
    have h1 := hfix _ hb'
    rw [mul_smul, mul_smul, inv_smul_smul] at h1
    exact MulAction.injective (h : G) h1
  · rintro ⟨hE, hfix⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h.2 e).mp hE, fun a ha => ?_⟩
    have hb : c.OnL ((h : G)⁻¹ • a) m := by
      have h1 := (cInc_smul c.G1 c.G2 (h : G)⁻¹ a ((h : G) • m)).mpr ha
      rwa [inv_smul_smul] at h1
    have h2 := hfix _ hb
    rw [mul_smul, mul_smul, h2, smul_inv_smul]

@[expose] def Epl (σ : G ⧸ c.G3) : Subgroup G where
  carrier := {e | e ∈ c.E ∧ ∀ m, c.OnL c.x0 m → c.LnP m σ → e ∈ c.Eker m}
  mul_mem' := by
    rintro e₁ e₂ ⟨he₁, h₁⟩ ⟨he₂, h₂⟩
    exact ⟨c.E.mul_mem he₁ he₂, fun m hm hmσ => (c.Eker m).mul_mem (h₁ m hm hmσ) (h₂ m hm hmσ)⟩
  one_mem' := ⟨c.E.one_mem, fun m _ _ => (c.Eker m).one_mem⟩
  inv_mem' := by
    rintro e ⟨he, h⟩
    exact ⟨c.E.inv_mem he, fun m hm hmσ => (c.Eker m).inv_mem (h m hm hmσ)⟩

theorem mem_Epl {σ : G ⧸ c.G3} {e : G} :
    e ∈ c.Epl σ ↔ e ∈ c.E ∧ ∀ m, c.OnL c.x0 m → c.LnP m σ → e ∈ c.Eker m :=
  Iff.rfl

end Loc49

end CFSG.Quasithin.H13.AS91
