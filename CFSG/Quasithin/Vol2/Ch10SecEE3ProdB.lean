module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Prod
public import CFSG.Quasithin.Vol2.Ch10SecEProd
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

structure ProdSetting (W₁ W₂ : Subgroup W) (P₁ P₂ : Subgroup (MulAut W)) : Prop where
  inf_W : W₁ ⊓ W₂ = ⊥
  comm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a
  inf_P : P₁ ⊓ P₂ = ⊥
  pres₁ : ∀ a ∈ P₁, ∀ w ∈ W₁, a w ∈ W₁
  pres₂ : ∀ b ∈ P₂, ∀ w ∈ W₂, b w ∈ W₂
  triv₁ : ∀ a ∈ P₁, ∀ w ∈ W₂, a w = w
  triv₂ : ∀ b ∈ P₂, ∀ w ∈ W₁, b w = w

namespace ProdSetting

variable {W₁ W₂ : Subgroup W} {P₁ P₂ : Subgroup (MulAut W)}

theorem symm (h : ProdSetting W₁ W₂ P₁ P₂) : ProdSetting W₂ W₁ P₂ P₁ :=
  ⟨by rw [inf_comm]; exact h.inf_W, fun b hb a ha => (h.comm a ha b hb).symm,
    by rw [inf_comm]; exact h.inf_P, h.pres₂, h.pres₁,
    h.triv₂, h.triv₁⟩

noncomputable def projHom (h : ProdSetting W₁ W₂ P₁ P₂) : ↥(P₁ ⊔ P₂) →* ↥P₂ :=
  (MonoidHom.snd _ _).comp (prodEquivSup h.comm h.inf_P).symm.toMonoidHom

noncomputable def projTwo (h : ProdSetting W₁ W₂ P₁ P₂) (X : Subgroup (MulAut W)) :
    Subgroup (MulAut W) :=
  ((X.subgroupOf (P₁ ⊔ P₂)).map h.projHom).map P₂.subtype

variable (h : ProdSetting W₁ W₂ P₁ P₂)
include h

theorem projTwo_le (X : Subgroup (MulAut W)) : h.projTwo X ≤ P₂ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem exists_eq_mul (x : ↥(P₁ ⊔ P₂)) :
    ∃ a ∈ P₁, (x : MulAut W) = a * (h.projHom x : MulAut W) :=
  ⟨_, ((prodEquivSup h.comm h.inf_P).symm x).1.2, eq_mul_prodEquivSup_symm h.comm h.inf_P x⟩

theorem projHom_eq {a b : MulAut W} (ha : a ∈ P₁) (hb : b ∈ P₂) (x : ↥(P₁ ⊔ P₂))
    (hx : (x : MulAut W) = a * b) : (h.projHom x : MulAut W) = b := by
  obtain ⟨a', ha', hx'⟩ := h.exists_eq_mul x
  rw [hx] at hx'
  exact ((eq_of_mul_eq_mul h.inf_P ha ha' hb (h.projHom x).2 hx').2).symm

theorem mem_projTwo_iff {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂) {b : MulAut W} :
    b ∈ h.projTwo X ↔ b ∈ P₂ ∧ ∃ a ∈ P₁, a * b ∈ X := by
  constructor
  · rintro ⟨y, ⟨x, hxX, rfl⟩, rfl⟩
    obtain ⟨a, ha, hxa⟩ := h.exists_eq_mul x
    refine ⟨(h.projHom x).2, a, ha, ?_⟩
    rw [Subgroup.coe_subtype, ← hxa]
    exact Subgroup.mem_subgroupOf.mp hxX
  · rintro ⟨hb, a, ha, habX⟩
    refine ⟨⟨b, hb⟩, ⟨⟨a * b, hX habX⟩, Subgroup.mem_subgroupOf.mpr habX, ?_⟩, rfl⟩
    exact Subtype.ext (h.projHom_eq ha hb _ rfl)

theorem apply_eq_projHom (x : ↥(P₁ ⊔ P₂)) {w : W} (hw : w ∈ W₂) :
    (x : MulAut W) w = (h.projHom x : MulAut W) w := by
  obtain ⟨a, ha, hxa⟩ := h.exists_eq_mul x
  rw [hxa, MulAut.mul_apply, h.triv₁ a ha _ (h.pres₂ _ (h.projHom x).2 w hw)]

theorem fixV_inf_two {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂) :
    fixV X ⊓ W₂ = fixV (h.projTwo X) ⊓ W₂ := by
  ext w
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hf, hw⟩
    refine ⟨?_, hw⟩
    rintro _ ⟨y, ⟨x, hxX, rfl⟩, rfl⟩
    rw [Subgroup.coe_subtype, ← h.apply_eq_projHom x hw]
    exact hf _ (Subgroup.mem_subgroupOf.mp hxX)
  · rintro ⟨hf, hw⟩
    refine ⟨fun x hxX => ?_, hw⟩
    rw [show x = ((⟨x, hX hxX⟩ : ↥(P₁ ⊔ P₂)) : MulAut W) from rfl, h.apply_eq_projHom _ hw]
    exact hf _ ⟨_, ⟨⟨x, hX hxX⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩, rfl⟩

theorem projHom_eq_one_iff (x : ↥(P₁ ⊔ P₂)) : h.projHom x = 1 ↔ (x : MulAut W) ∈ P₁ := by
  constructor
  · intro h1
    obtain ⟨a, ha, hxa⟩ := h.exists_eq_mul x
    rw [hxa, h1, Subgroup.coe_one, mul_one]
    exact ha
  · intro hx
    exact Subtype.ext (h.projHom_eq hx P₂.one_mem x (mul_one _).symm)

theorem card_eq_card_inf_mul_card_projTwo [Finite W] {X : Subgroup (MulAut W)}
    (hX : X ≤ P₁ ⊔ P₂) : Nat.card X = Nat.card ↥(X ⊓ P₁) * Nat.card ↥(h.projTwo X) := by
  set X' := X.subgroupOf (P₁ ⊔ P₂)
  set φ : ↥X' →* ↥P₂ := h.projHom.comp X'.subtype
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have hX' : Nat.card ↥X' = Nat.card ↥X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hrange : Nat.card ↥φ.range = Nat.card ↥(h.projTwo X) := by
    have e : φ.range = X'.map h.projHom := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ P₂.subtype P₂.subtype_injective).toEquiv
  have hker : Nat.card ↥φ.ker = Nat.card ↥(X ⊓ P₁) := by
    set f : ↥X' →* MulAut W := (P₁ ⊔ P₂).subtype.comp X'.subtype
    have hf : Function.Injective f :=
      (P₁ ⊔ P₂).subtype_injective.comp X'.subtype_injective
    have e : φ.ker.map f = X ⊓ P₁ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' := (h.projHom_eq_one_iff (x : ↥(P₁ ⊔ P₂))).mp hx
        exact ⟨Subgroup.mem_subgroupOf.mp x.2, hx'⟩
      · rintro ⟨hyX, hyP⟩
        refine ⟨⟨⟨y, hX hyX⟩, Subgroup.mem_subgroupOf.mpr hyX⟩, ?_, rfl⟩
        exact (h.projHom_eq_one_iff _).mpr hyP
    rw [← e]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ f hf).toEquiv
  rw [← hX', ← h1, hker, hrange]

theorem fixV_inf_sup_eq {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂) :
    fixV X ⊓ (W₁ ⊔ W₂) = (fixV X ⊓ W₁) ⊔ (fixV X ⊓ W₂) := by
  refine le_antisymm (fun w ⟨hw, hwW⟩ => ?_)
    (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  have hc : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a _ b _ => mul_comm a b
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := exists_mul_of_mem_sup hc hwW
  have key : ∀ x ∈ X, x w₁ = w₁ ∧ x w₂ = w₂ := by
    intro x hxX
    obtain ⟨a, ha, hxa⟩ := h.exists_eq_mul ⟨x, hX hxX⟩
    set b := (h.projHom ⟨x, hX hxX⟩ : MulAut W)
    have hb : b ∈ P₂ := (h.projHom ⟨x, hX hxX⟩).2
    have hx : x = a * b := hxa
    have h1 : x w₁ = a w₁ := by rw [hx, MulAut.mul_apply, h.triv₂ b hb w₁ hw₁]
    have h2 : x w₂ = b w₂ := by rw [hx, MulAut.mul_apply, h.triv₁ a ha _ (h.pres₂ b hb w₂ hw₂)]
    have h3 : x w₁ * x w₂ = w₁ * w₂ := by rw [← map_mul]; exact hw x hxX
    rw [h1, h2] at h3 ⊢
    exact eq_of_mul_eq_mul h.inf_W (h.pres₁ a ha w₁ hw₁) hw₁ (h.pres₂ b hb w₂ hw₂) hw₂ h3
  exact Subgroup.mul_mem_sup ⟨fun x hx => (key x hx).1, hw₁⟩ ⟨fun x hx => (key x hx).2, hw₂⟩

theorem card_fixV_inf_sup [Finite W] {X : Subgroup (MulAut W)} (hX : X ≤ P₁ ⊔ P₂) :
    Nat.card ↥(fixV X ⊓ (W₁ ⊔ W₂)) = Nat.card ↥(fixV X ⊓ W₁) * Nat.card ↥(fixV X ⊓ W₂) := by
  have hc : ∀ a ∈ fixV X ⊓ W₁, ∀ b ∈ fixV X ⊓ W₂, a * b = b * a := fun a _ b _ => mul_comm a b
  have hi : (fixV X ⊓ W₁) ⊓ (fixV X ⊓ W₂) = ⊥ := by
    rw [eq_bot_iff, ← h.inf_W]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [← Nat.card_prod, Nat.card_congr (prodEquivSup hc hi).toEquiv, ← h.fixV_inf_sup_eq hX]

theorem card_sup [Finite W] : Nat.card ↥(W₁ ⊔ W₂) = Nat.card W₁ * Nat.card W₂ := by
  have hc : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a _ b _ => mul_comm a b
  rw [← Nat.card_prod, Nat.card_congr (prodEquivSup hc h.inf_W).toEquiv]

end ProdSetting

end CFSG.Quasithin.Vol2.Ch10.SecE
