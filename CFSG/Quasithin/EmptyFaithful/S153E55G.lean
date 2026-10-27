module

public import CFSG.Quasithin.EmptyFaithful.S153E55F
public import CFSG.Quasithin.EmptyFaithful.S153E55E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E55

open CFSG.Quasithin.S153E

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem eq_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨y₀, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).mp hK
  have h1 : (⟨x, hx⟩ : ↥K) = y₀ := hu _ (fun e => hx1 (congrArg Subtype.val e))
  have h2 : (⟨y, hy⟩ : ↥K) = y₀ := hu _ (fun e => hy1 (congrArg Subtype.val e))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem card_conj_Z (cx : Ctx15350 T Mc M V₁ V₂ t) (g : G) :
    Nat.card ↥(conjSubgroup (quasithinOmegaOneCenter T) g) = 2 := by
  have h : Nat.card ↥(conjSubgroup (quasithinOmegaOneCenter T) g) =
      Nat.card ↥(quasithinOmegaOneCenter T) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [h]
  exact cx.c.hyp.lemma_15_3_2_two.2

theorem conj_centerOf_U_inf_U (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) :
    ∀ x ∈ conjSubgroup (centerOf (UH153 T M V₁ Mc)) g, x ∈ UH153 T M V₁ Mc → x = 1 := by
  intro x hxZ hxU
  have hV := cx.c.hyp.elemAbelian
  have h1 := c.h51.one
  have h52 := c.h52
  obtain ⟨B₁, B₂, hB₁, hB₂, hUU⟩ := c.h54.three_perp
  have hxUg : x ∈ conjSubgroup (UH153 T M V₁ Mc) g := by
    rw [mem_conjSubgroup_iff] at hxZ ⊢
    exact hxZ.1
  have hxB : x ∈ B₁ ⊓ B₂ := by
    rw [← hUU]
    exact ⟨hxU, hxUg⟩
  obtain ⟨hxV, hxorth⟩ := (hB₁ x).1 hxB.1
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) := YU_le_normalizer_V cx (Y_le_YU c.hg)
  have hgxV : g * x * g⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hgN x).mp hxV
  rw [mem_conjSubgroup_iff] at hxZ
  have hgxZ : g * x * g⁻¹ ∈ quasithinOmegaOneCenter T :=
    centralizer_U_le_Z cx h1 h52 hgxV (fun u hu => (centerOf_U_comm hxZ hu).symm)
  have hxZg : x ∈ conjSubgroup (quasithinOmegaOneCenter T) g := mem_conjSubgroup_iff.2 hgxZ
  by_contra hx1
  refine c.hgZ ?_
  intro z hz z' hz'
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hz
  by_cases hz'1 : z' = 1
  · subst hz'1
    exact ⟨hzV, (VZ T M).one_mem, quadPolar_one_right (qW_spec cx).1 (IntMod.mk hV ⟨z, hzV⟩)⟩
  · have := eq_of_card_two (card_conj_Z cx g) hz' hxZg hz'1 hx1
    rw [this]
    exact hxorth z hz

theorem isExtraspecial_of_centerOf_eq (cx : Ctx15350 T Mc M V₁ V₂ t) (h52 : Concl15352 cx)
    (hZu : centerOf (UH153 T M V₁ Mc) = quasithinOmegaOneCenter T) :
    CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc) := by
  have hZU : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc :=
    (Z_le_centerOf_U cx).trans inf_le_left
  have hcenter : Subgroup.center ↥(UH153 T M V₁ Mc) =
      (quasithinOmegaOneCenter T).subgroupOf (UH153 T M V₁ Mc) := by
    ext x
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : (x : G) ∈ centerOf (UH153 T M V₁ Mc) :=
        ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun u hu => by
          have := congrArg Subtype.val (hx ⟨u, hu⟩)
          exact this⟩
      rwa [hZu] at this
    · intro hx g
      rw [← hZu] at hx
      exact Subtype.ext (centerOf_U_comm hx g.2).symm
  have hcard : Nat.card ↥(Subgroup.center ↥(UH153 T M V₁ Mc)) = 2 := by
    rw [hcenter]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv]
    exact cx.c.hyp.lemma_15_3_2_two.2
  have hcomm : ∀ a b : ↥(UH153 T M V₁ Mc),
      (QuotientGroup.mk a : ↥(UH153 T M V₁ Mc) ⧸ Subgroup.center ↥(UH153 T M V₁ Mc)) *
        QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a := by
    intro a b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hcenter,
      Subgroup.mem_subgroupOf]
    have h := commutator_U_mem cx ((UH153 T M V₁ Mc).inv_mem b.2) ((UH153 T M V₁ Mc).inv_mem a.2)
    simpa [mul_assoc] using h
  have _hQcomm : IsMulCommutative (↥(UH153 T M V₁ Mc) ⧸ Subgroup.center ↥(UH153 T M V₁ Mc)) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b => exact hcomm a b
  have hQexp : Monoid.exponent
      (↥(UH153 T M V₁ Mc) ⧸ Subgroup.center ↥(UH153 T M V₁ Mc)) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hcenter, Subgroup.mem_subgroupOf]
      have := sq_U_mem cx a.2
      simpa [pow_two] using this
  have hnt : Nontrivial (↥(UH153 T M V₁ Mc) ⧸ Subgroup.center ↥(UH153 T M V₁ Mc)) := by
    obtain ⟨a, ha, b, hb, hne⟩ := h52
    refine ⟨⟨QuotientGroup.mk ⟨a, ha⟩, 1, fun h => hne ?_⟩⟩
    have h1 : (⟨a, ha⟩ : ↥(UH153 T M V₁ Mc)) ∈ Subgroup.center ↥(UH153 T M V₁ Mc) :=
      (QuotientGroup.eq_one_iff _).1 h
    have h2 := Subgroup.mem_center_iff.1 h1 ⟨b, hb⟩
    exact (congrArg Subtype.val h2).symm
  exact { center_order_p := hcard, quotient_elementary_abelian := ⟨hQexp⟩, quotient_nontrivial := hnt }

end Final

end S153E55

namespace S153E

open CFSG.Quasithin.S153E55

section Lemma

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_55 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) :
    Concl15355 cx g := by
  have hI := c.h54.one
  have h52 := c.h52
  have hZuP : centerOf (UH153 T M V₁ Mc) ≤ Pgp153 T M V₁ Mc g := fun z hz =>
    centralizer_le_P hI cx ⟨U_le_YU hz.1, centerOf_U_le_centralizer cx h52 hz⟩
  have hgP : g ∈ Subgroup.normalizer (Pgp153 T M V₁ Mc g : Set G) :=
    YU_le_normalizer_P hI (Y_le_YU c.hg)
  have hZuCP : centerOf (UH153 T M V₁ Mc) ≤
      Pgp153 T M V₁ Mc g ⊓ Subgroup.centralizer (Pgp153 T M V₁ Mc g : Set G) :=
    Zu_le_centerP inf_le_left (fun z hz u hu => centerOf_U_comm hz hu)
      (normalizer_le_normalizer_centerOf _) c.h54.two_prod c.h54.five_norm hgP hZuP
      (conj_centerOf_U_inf_U cx c)
  have hVeq : VZ T M = centerOf (Pgp153 T M V₁ Mc g) :=
    le_antisymm c.h54.two_center (centerOf_P_le_V h113 cx c)
  have hZu : centerOf (UH153 T M V₁ Mc) = quasithinOmegaOneCenter T := by
    refine le_antisymm (fun z hz => ?_) (Z_le_centerOf_U cx)
    have hzV : z ∈ VZ T M := centerOf_P_le_V h113 cx c (hZuCP hz)
    exact centralizer_U_le_Z cx c.h51.one h52 hzV (fun u hu => (centerOf_U_comm hz hu).symm)
  exact ⟨isExtraspecial_of_centerOf_eq cx h52 hZu, hVeq⟩

end Lemma

end S153E

end CFSG.Quasithin
