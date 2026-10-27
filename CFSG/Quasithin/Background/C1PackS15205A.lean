module

public import CFSG.Quasithin.EmptyFaithful.S152Y02

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

variable {G : Type} [Group G] [Finite G]

structure Std5 (T Mc M : Subgroup G) : Prop where
  hs : Setting152 T Mc M
  c1515 : Lemma1515Concl T Mc M
  c1521 : Lemma15201Concl T Mc M
  c1522 : ∀ X : Subgroup G, T ≤ X → X ≤ M →
    ((m0Of T Mc M : Set G) ⊆ (X : Set G) *
        ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) ∨
      (m0Of T Mc M : Set G) ⊆ (X : Set G) *
        ((M ⊓ Subgroup.normalizer
          ((quasithinOmegaOneCenter T ⊓ V154 T Mc M : Subgroup G) : Set G) : Subgroup G) :
            Set G)) →
    IsUniqueM X M
  c1523 : Lemma15203Concl T Mc M

structure Ctr5 (T Mc M M₁ : Subgroup G) : Prop where
  std : Std5 T Mc M
  inM₁ : InM T M₁
  ne : M₁ ≠ M
  ne_c : M₁ ≠ Mc

namespace Std5

variable {T Mc M : Subgroup G}

theorem data (s : Std5 T Mc M) : S152Y.Data T Mc M := ⟨s.hs.qtfe, s.hs.mf, s.c1515, s.c1521⟩

end Std5

namespace Ctr5

variable {T Mc M M₁ : Subgroup G} (c : Ctr5 T Mc M M₁)

include c

theorem qtfe : quasithinQTFE14Cat G T Mc := c.std.hs.qtfe

theorem T_le_M : T ≤ M := c.std.hs.mf.1.1.2

theorem T_le_M₁ : T ≤ M₁ := c.inM₁.2

theorem T_le_H : T ≤ M₁ ⊓ M := le_inf c.T_le_M₁ c.T_le_M

theorem ordLE : OrdLE T M₁ M := c.std.hs.mf.2.2 M₁ c.inM₁ c.ne_c

theorem isHv : IsHv T M₁ := by
  obtain ⟨S, hS⟩ := c.qtfe.exists_sylow
  have := isHv_of_inM c.qtfe.qtke.2.1 S (hS ▸ c.inM₁)
  rwa [hS] at this

theorem C₁_le_Mc : M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) ≤ Mc := fun _ hx =>
  c.qtfe.centralizer_le_mc (Subgroup.centralizer_le (le_conjClosure _ _) hx.2)

theorem not_M₁_le_Mc : ¬ M₁ ≤ Mc := fun hle =>
  c.ne_c (c.inM₁.1.2 Mc c.qtfe.mc_max.1 hle).symm

theorem exists_mul (x : G) (hx : x ∈ M₁) :
    ∃ a ∈ M₁ ⊓ M, ∃ k ∈ M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G), x = a * k :=
  c.ordLE x hx

theorem not_H_le_Mc : ¬ M₁ ⊓ M ≤ Mc := by
  intro hH
  apply c.not_M₁_le_Mc
  intro x hx
  obtain ⟨a, ha, k, hk, rfl⟩ := c.exists_mul x hx
  exact Mc.mul_mem (hH ha) (c.C₁_le_Mc hk)

theorem not_forall_mul_Mc :
    ¬ ∀ x ∈ M₁ ⊓ M, ∃ a ∈ M ⊓ Mc, ∃ k ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G),
      x = a * k := by
  intro h
  apply c.not_H_le_Mc
  intro x hx
  obtain ⟨a, ha, k, hk, rfl⟩ := h x hx
  exact Mc.mul_mem ha.2 (c.std.c1515.centralizer_le hk.2)

theorem not_m0_subset :
    ¬ ((m0Of T Mc M : Set G) ⊆ ((M₁ ⊓ M : Subgroup G) : Set G) *
      ((M ⊓ Subgroup.normalizer
        ((quasithinOmegaOneCenter T ⊓ V154 T Mc M : Subgroup G) : Set G) : Subgroup G) :
          Set G)) := by
  intro hsub
  have hU := c.std.c1522 (M₁ ⊓ M) c.T_le_H inf_le_right (Or.inr hsub)
  exact c.ne (hU.2 M₁ ⟨c.inM₁.1, inf_le_left⟩)

end Ctr5

omit [Finite G] in
theorem exists_mul_of_conjAct_mem {M V N : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hNM : N ≤ M) {x : G} (hxM : x ∈ M) (h : conjAct V ⟨x, hMV hxM⟩ ∈ autOn N V) :
    ∃ a ∈ N, ∃ k ∈ M ⊓ Subgroup.centralizer (V : Set G), x = a * k := by
  obtain ⟨y, hyN, hyN', hyx⟩ := mem_autOn_iff_exists.mp h
  have h2 : conjAct V ((⟨y, hyN⟩ : Subgroup.normalizer (V : Set G))⁻¹ * ⟨x, hMV hxM⟩) = 1 := by
    rw [map_mul, map_inv, hyx]
    exact inv_mul_cancel _
  have h3 : y⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp h2
  exact ⟨y, hyN', y⁻¹ * x, ⟨M.mul_mem (M.inv_mem (hNM hyN')) hxM, h3⟩, by group⟩

omit [Finite G] in
theorem exists_mul_of_autOn_le {M V X N : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hXM : X ≤ M) (hNM : N ≤ M) (h : autOn X V ≤ autOn N V) :
    ∀ x ∈ X, ∃ a ∈ N, ∃ k ∈ M ⊓ Subgroup.centralizer (V : Set G), x = a * k := fun x hx =>
  exists_mul_of_conjAct_mem hMV hNM (hXM hx)
    (h (mem_autOn_iff_exists.mpr ⟨x, hMV (hXM hx), hx, rfl⟩))

end C1Pack5

end CFSG.Quasithin
