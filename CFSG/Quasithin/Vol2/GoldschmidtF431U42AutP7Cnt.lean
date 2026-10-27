module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7ZC
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Sub

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

section Elt


noncomputable def eltOfL (l : PL) : Ah :=
  if h : l ∈ Thl then Classical.choose (exists_That_of_mem_Thl h) else 1

theorem eltOfL_mem {l : PL} (h : l ∈ Thl) : eltOfL l ∈ That := by
  simp only [eltOfL, h, ↓reduceDIte]
  exact (Classical.choose_spec (exists_That_of_mem_Thl h)).1

theorem repL_eltOfL {l : PL} (h : l ∈ Thl) : RepL l (eltOfL l : P45) := by
  simp only [eltOfL, h, ↓reduceDIte]
  exact (Classical.choose_spec (exists_That_of_mem_Thl h)).2

noncomputable def eltB (l : PL) : Bh :=
  if h : l ∈ Thl then ⟨eltOfL l, That_le_Bh (eltOfL_mem h)⟩ else 1

theorem coe_eltB {l : PL} (h : l ∈ Thl) : (eltB l : Ah) = eltOfL l := by
  simp only [eltB, h, ↓reduceDIte]

end Elt

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G} {z : G}

theorem Om_conjSub (γ : G) (X : Subgroup G) :
    Om (B6.conjSub γ X) z = (fun u => γ * u * γ⁻¹) '' Om X z := by
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨γ⁻¹ * u * γ, ⟨B6.mem_conjSub.1 hu, ?_⟩, by group⟩
    obtain ⟨c0, hc0⟩ := isConj_iff.1 hc
    exact isConj_iff.2 ⟨c0 * γ, by rw [← hc0]; group⟩
  · rintro ⟨v, ⟨hv, hc⟩, rfl⟩
    refine ⟨B6.mem_conjSub.2 (by simpa [mul_assoc] using hv), ?_⟩
    obtain ⟨c0, hc0⟩ := isConj_iff.1 hc
    exact isConj_iff.2 ⟨c0 * γ⁻¹, by rw [← hc0]; group⟩

theorem ncard_Om_conjSub (γ : G) (X : Subgroup G) :
    (Om (B6.conjSub γ X) z).ncard = (Om X z).ncard := by
  rw [Om_conjSub]
  exact Set.ncard_image_of_injective _ fun a b h => by simpa using h

variable [Finite G]

theorem ncard_Om_imgG (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) {Kl : List PL} {h1 : idL ∈ Kl}
    {hmul : ∀ a ∈ Kl, ∀ b ∈ Kl, comp a b ∈ Kl} (hT : ∀ l ∈ Kl, l ∈ Thl) (hnd : Kl.Nodup) :
    (Om (c.iso.imgG (listSub Kl h1 hmul)) z).ncard =
      (Kl.filter fun l => ZCl.contains l).length := by
  set X := listSub Kl h1 hmul with hX
  have hXT : X ≤ That := listSub_le_That hT
  set S := Kl.filter fun l => ZCl.contains l with hS
  let gOf : PL → G := fun l => c.iso.toG (eltB l)
  have hSmem : ∀ l, l ∈ S ↔ l ∈ Kl ∧ l ∈ ZCl := by
    intro l
    rw [hS, List.mem_filter]
    simp
  have himg : Om (c.iso.imgG X) z = gOf '' {l | l ∈ S} := by
    ext u
    constructor
    · rintro ⟨hu, hc⟩
      obtain ⟨b, hbX, rfl⟩ := c.iso.mem_imgG.1 hu
      obtain ⟨l, hl, hrep⟩ := hbX
      obtain ⟨l', hl', hrep'⟩ := (hZ (hXT ⟨l, hl, hrep⟩)).1 hc
      have hll : l' = l := repL_unique hrep' hrep
      subst hll
      refine ⟨l', (hSmem l').2 ⟨hl, hl'⟩, ?_⟩
      have : eltB l' = b := Subtype.ext (by
        rw [coe_eltB (hT l' hl)]
        exact Subtype.ext (eq_of_repL (repL_eltOfL (hT l' hl)) hrep))
      simp only [gOf, this]
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨hlK, hlZ⟩ := (hSmem l).1 hl
      have hlT := hT l hlK
      have hrep : RepL l (eltB l : P45) := by
        rw [coe_eltB hlT]
        exact repL_eltOfL hlT
      refine ⟨c.iso.mem_imgG.2 ⟨eltB l, ⟨l, hlK, hrep⟩, rfl⟩, ?_⟩
      exact (hZ (hXT ⟨l, hlK, hrep⟩)).2 ⟨l, hlZ, hrep⟩
  have hinj : Set.InjOn gOf {l | l ∈ S} := by
    intro l hl l' hl' h
    obtain ⟨hlK, -⟩ := (hSmem l).1 hl
    obtain ⟨hlK', -⟩ := (hSmem l').1 hl'
    have hb : eltB l = eltB l' := c.iso.toG_injective h
    have hc := congrArg (fun x : Bh => (x : Ah)) hb
    simp only [coe_eltB (hT l hlK), coe_eltB (hT l' hlK')] at hc
    exact repL_unique (repL_eltOfL (hT l hlK)) (hc ▸ repL_eltOfL (hT l' hlK'))
  rw [himg, hinj.ncard_image]
  have : {l | l ∈ S} = ↑S.toFinset := by
    ext l
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter _)]

theorem ncard_Om_A1 (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) :
    (Om (c.iso.imgG A1h) z).ncard = 5 := by
  have := ncard_Om_imgG c hZ (h1 := A1_check.1) (hmul := A1_check.2.1) A1_check.2.2.2.1
    A1_check.2.2.2.2.2.2.1
  rw [A1h, this]
  exact cnt_check.1

theorem ncard_Om_A2 (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) :
    (Om (c.iso.imgG A2h) z).ncard = 9 := by
  have := ncard_Om_imgG c hZ (h1 := A2_check.1) (hmul := A2_check.2.1) A2_check.2.2.2.1
    A2_check.2.2.2.2.2.2.1
  rw [A2h, this]
  exact cnt_check.2.1

omit [Finite G] in
theorem VA_eq_listSub : VA = listSub Vl Vl_special.1 Vl_mul := by
  ext g
  exact mem_VA_iff g

theorem ncard_Om_VA (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) :
    (Om (c.iso.imgG VA) z).ncard = 5 := by
  have := ncard_Om_imgG c hZ (h1 := Vl_special.1) (hmul := Vl_mul) Vl_mem_Thl Vl_nodup
  rw [VA_eq_listSub, this]
  exact cnt_check.2.2.1

end CFSG.Quasithin.H13.F431.U42Aut
