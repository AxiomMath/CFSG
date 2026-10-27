module

public import CFSG.Quasithin.EmptyFaithful.FLc3Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem exists_mul_of_mem_sup_comm4 {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := (h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

variable {G : Type} [Group G] [Finite G]

theorem input15129ZOrder_holds : Input15129ZOrder := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc
  have hF := facts_of_ctx hc.base
  have hS := hc.base.ctx.setting
  have hq := hc.base.ctx.qtfe
  have hM := hc.base.ctx.mf
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.base.hL.comp
  have hVab := hS.V_isElemAbelian hq hM
  have hcomm : ∀ a ∈ Z₁, ∀ b ∈ Z₂, a * b = b * a := by
    intro a ha b hb
    have := hVab.1
    exact setLike_mul_comm (hS.z1_le_V ha) (hS.z2_le_V hb)
  have hZ12 : ∀ z ∈ quasithinOmegaOneCenter T, ∃ a ∈ Z₁, ∃ b ∈ Z₂, z = a * b := by
    intro z hz
    have : z ∈ Z₁ ⊔ Z₂ := hS.vE_sup.2 hz
    exact exists_mul_of_mem_sup_comm4 hcomm this
  choose a ha b hb hzab using hZ12
  choose u hu hcu using hF.decomp
  have hZ1cent : ∀ x ∈ Z₁, ∀ l ∈ L, l * x = x * l := fun x hx l hl =>
    (Subgroup.mem_centralizer_iff.1 (hLG hl) x hx).symm
  have hcmem : ∀ (z : G) (hz : z ∈ quasithinOmegaOneCenter T),
      b z hz * u (b z hz) (hb z hz) ∈ uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G) := by
    intro z hz
    refine ⟨(uOf1527 Z₂ L).mul_mem (hF.ZU (hb z hz)) (hF.ULU (hu _ _)),
      Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have := hcu (b z hz) (hb z hz) l hl
    calc l * (b z hz * u (b z hz) (hb z hz)) =
        (l * (b z hz * u (b z hz) (hb z hz)) * l⁻¹) * l := by group
      _ = (b z hz * u (b z hz) (hb z hz)) * l := by rw [this]
  have hinZU : ∀ (z : G) (hz : z ∈ quasithinOmegaOneCenter T),
      (u (b z hz) (hb z hz))⁻¹ ∈ zUOf1528 Z₂ L := by
    intro z hz
    refine ⟨?_, (uLOf1527 Z₂ L).inv_mem (hu _ _)⟩
    have h1 : (u (b z hz) (hb z hz))⁻¹ =
        (b z hz * u (b z hz) (hb z hz))⁻¹ * b z hz := by group
    rw [h1]
    exact (Z₂ ⊔ uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G)).mul_mem
      (Subgroup.mem_sup_right
        ((uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G)).inv_mem (hcmem z hz)))
      (Subgroup.mem_sup_left (hb z hz))
  let f : ↥(quasithinOmegaOneCenter T) → ↥(zUOf1528 Z₂ L) := fun z =>
    ⟨(u (b z.1 z.2) (hb z.1 z.2))⁻¹, hinZU z.1 z.2⟩
  have hinj : Function.Injective f := by
    intro z z' hzz
    have hu_eq : u (b z.1 z.2) (hb z.1 z.2) = u (b z'.1 z'.2) (hb z'.1 z'.2) := by
      have := congrArg (fun w : ↥(zUOf1528 Z₂ L) => (w : G)) hzz
      exact inv_injective this
    have hz1 := hzab z.1 z.2
    have hz2 := hzab z'.1 z'.2
    have hc1 := (hcmem z.1 z.2).2
    have hc2 := (hcmem z'.1 z'.2).2
    have hha1 := ha z.1 z.2
    have hha2 := ha z'.1 z'.2
    have hhb1 := hb z.1 z.2
    have hhb2 := hb z'.1 z'.2
    have hcomm12 := hcomm (a z'.1 z'.2)⁻¹ (Z₁.inv_mem hha2)
      (b z.1 z.2 * (b z'.1 z'.2)⁻¹) (Z₂.mul_mem hhb1 (Z₂.inv_mem hhb2))
    set a₁ := a z.1 z.2
    set a₂ := a z'.1 z'.2
    set b₁ := b z.1 z.2
    set b₂ := b z'.1 z'.2
    set u₁ := u b₁ hhb1
    set u₂ := u b₂ hhb2
    have hbb : b₁ * b₂⁻¹ = (b₁ * u₁) * (b₂ * u₂)⁻¹ := by
      rw [← hu_eq]
      group
    have hw : z.1 * z'.1⁻¹ = (a₁ * a₂⁻¹) * ((b₁ * u₁) * (b₂ * u₂)⁻¹) := by
      rw [← hbb]
      calc z.1 * z'.1⁻¹ = (a₁ * b₁) * (a₂ * b₂)⁻¹ := by rw [← hz1, ← hz2]
        _ = a₁ * (b₁ * b₂⁻¹ * a₂⁻¹) := by group
        _ = a₁ * (a₂⁻¹ * (b₁ * b₂⁻¹)) := by rw [← hcomm12]
        _ = a₁ * a₂⁻¹ * (b₁ * b₂⁻¹) := by group
    have hwcent : (z.1 * z'.1⁻¹) ∈ Subgroup.centralizer (L : Set G) := by
      rw [hw]
      refine (Subgroup.centralizer (L : Set G)).mul_mem ?_ ?_
      · refine (Subgroup.centralizer (L : Set G)).mul_mem ?_ ?_
        · exact Subgroup.mem_centralizer_iff.2 fun l hl => hZ1cent _ hha1 l hl
        · refine (Subgroup.centralizer (L : Set G)).inv_mem ?_
          exact Subgroup.mem_centralizer_iff.2 fun l hl => hZ1cent _ hha2 l hl
      · exact (Subgroup.centralizer (L : Set G)).mul_mem hc1
          ((Subgroup.centralizer (L : Set G)).inv_mem hc2)
    by_contra hne
    have hw1 : z.1 * z'.1⁻¹ ≠ 1 := fun h1 => hne (Subtype.ext (mul_inv_eq_one.1 h1))
    have hwZ : z.1 * z'.1⁻¹ ∈ quasithinOmegaOneCenter T :=
      (quasithinOmegaOneCenter T).mul_mem z.2 ((quasithinOmegaOneCenter T).inv_mem z'.2)
    have h6 := hc.base.h18.six _ hwZ hw1
    have hLM : L ≤ mZ1516 Mc Z₁ := fun l hl => ⟨hLG hl, h6.centralizer_z_le (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hwcent l hl)⟩
    exact hc.base.hL.not_le hLM
  have hle : Nat.card (quasithinOmegaOneCenter T) ≤ Nat.card (zUOf1528 Z₂ L) :=
    Nat.card_le_card_of_injective f hinj
  have h2 := hc.h28.2.1
  have hne : quasithinOmegaOneCenter T ≠ ⊥ := hq.omegaOneCenter_ne_bot
  have h1 : 1 < Nat.card (quasithinOmegaOneCenter T) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  omega

end CFSG.Quasithin
