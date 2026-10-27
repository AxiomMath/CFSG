module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tt

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative commutatorElement

variable {Γ : Type} [Group Γ]

section Proj

variable {V W₁ W₂ U : Subgroup Γ} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem mul_comm_of_mem (hV : IsMulCommutative ↥V) {x y : Γ} (hx : x ∈ V) (hy : y ∈ V) :
    x * y = y * x :=
  congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)

theorem exists_mul_of_mem_sup (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) {x : Γ} (hx : x ∈ W₁ ⊔ W₂) :
    ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = x := by
  have e : W₁ ⊔ W₂ = (W₁.subgroupOf V ⊔ W₂.subgroupOf V).map V.subtype := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left h₁, inf_of_le_left h₂]
  rw [e] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy
  exact ⟨a, ha, b, hb, rfl⟩

omit [IsMulCommutative ↥V] in
theorem eq_of_mul_eq (h : W₁ ⊓ W₂ = ⊥) {a a' b b' : Γ} (ha : a ∈ W₁) (ha' : a' ∈ W₁)
    (hb : b ∈ W₂) (hb' : b' ∈ W₂) (hab : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ W₁ ⊓ W₂ :=
    ⟨W₁.mul_mem (W₁.inv_mem ha') ha, h1 ▸ W₂.mul_mem hb' (W₂.inv_mem hb)⟩
  rw [h, Subgroup.mem_bot] at h2
  have e1 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  subst e1
  exact ⟨rfl, mul_left_cancel hab⟩

variable (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (hU : U ≤ W₁ ⊔ W₂)

@[expose] noncomputable def projFun (x : ↥U) : ↥W₁ :=
  ⟨Classical.choose (exists_mul_of_mem_sup h₁ h₂ (hU x.2)),
    (Classical.choose_spec (exists_mul_of_mem_sup h₁ h₂ (hU x.2))).1⟩

theorem projFun_spec (x : ↥U) : ∃ b ∈ W₂, ((projFun h₁ h₂ hU x : ↥W₁) : Γ) * b = x :=
  (Classical.choose_spec (exists_mul_of_mem_sup h₁ h₂ (hU x.2))).2

variable {h₁ h₂ hU}

theorem projFun_eq (h : W₁ ⊓ W₂ = ⊥) {x : ↥U} {a b : Γ} (ha : a ∈ W₁) (hb : b ∈ W₂)
    (hx : a * b = x) : ((projFun h₁ h₂ hU x : ↥W₁) : Γ) = a := by
  obtain ⟨b', hb', hx'⟩ := projFun_spec h₁ h₂ hU x
  exact (eq_of_mul_eq h (projFun h₁ h₂ hU x).2 ha hb' hb (hx'.trans hx.symm)).1

variable (h₁ h₂ hU) in
@[expose] noncomputable def proj (h : W₁ ⊓ W₂ = ⊥) : ↥U →* ↥W₁ where
  toFun := projFun h₁ h₂ hU
  map_one' := Subtype.ext (projFun_eq h W₁.one_mem W₂.one_mem (mul_one 1))
  map_mul' x y := by
    obtain ⟨b, hb, hx⟩ := projFun_spec h₁ h₂ hU x
    obtain ⟨c, hc, hy⟩ := projFun_spec h₁ h₂ hU y
    apply Subtype.ext
    refine projFun_eq h (W₁.mul_mem (projFun h₁ h₂ hU x).2 (projFun h₁ h₂ hU y).2)
      (W₂.mul_mem hb hc) ?_
    have hc' := mul_comm_of_mem (V := V) inferInstance (h₂ hb) (h₁ (projFun h₁ h₂ hU y).2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
    calc ((projFun h₁ h₂ hU x : ↥W₁) : Γ) * (projFun h₁ h₂ hU y : ↥W₁) * (b * c)
        = (projFun h₁ h₂ hU x : ↥W₁) * ((projFun h₁ h₂ hU y : ↥W₁) * b) * c := by group
      _ = (projFun h₁ h₂ hU x : ↥W₁) * (b * (projFun h₁ h₂ hU y : ↥W₁)) * c := by rw [hc']
      _ = (projFun h₁ h₂ hU x : ↥W₁) * b * ((projFun h₁ h₂ hU y : ↥W₁) * c) := by group

theorem proj_eq (h : W₁ ⊓ W₂ = ⊥) {x : ↥U} {a b : Γ} (ha : a ∈ W₁) (hb : b ∈ W₂)
    (hx : a * b = x) : ((proj h₁ h₂ hU h x : ↥W₁) : Γ) = a :=
  projFun_eq (h₁ := h₁) (h₂ := h₂) (hU := hU) h ha hb hx

theorem proj_conj (h : W₁ ⊓ W₂ = ⊥) {g : Γ} (gU : g ∈ Subgroup.normalizer (U : Set Γ))
    (g₁ : g ∈ Subgroup.normalizer (W₁ : Set Γ)) (g₂ : g ∈ Subgroup.normalizer (W₂ : Set Γ))
    (x : ↥U) :
    ((proj h₁ h₂ hU h ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp gU x).mp x.2⟩ : ↥W₁) : Γ) =
      g * (proj h₁ h₂ hU h x : ↥W₁) * g⁻¹ := by
  obtain ⟨b, hb, hx⟩ := projFun_spec h₁ h₂ hU x
  refine proj_eq (h₁ := h₁) (h₂ := h₂) (hU := hU) h
    ((Subgroup.mem_normalizer_iff.mp g₁ _).mp (projFun h₁ h₂ hU x).2)
    ((Subgroup.mem_normalizer_iff.mp g₂ _).mp hb) ?_
  show _ = g * (x : Γ) * g⁻¹
  rw [← hx]
  change g * ((projFun h₁ h₂ hU x : ↥W₁) : Γ) * g⁻¹ * (g * b * g⁻¹) = _
  group

end Proj

section Map

variable [Finite Γ] {J L R U W : Subgroup Γ} (hJU : J ≤ Subgroup.normalizer (U : Set Γ))
  {φ : ↥U →* ↥W}

@[expose] def IsEquivJ (φ : ↥U →* ↥W) : Prop :=
  ∀ (g : Γ) (hg : g ∈ J) (u : ↥U),
    ((φ ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJU hg) u).mp u.2⟩ : ↥W) : Γ) =
      g * φ u * g⁻¹

variable {hJU}

omit [Finite Γ] in
theorem mem_normalizer_map_of_equiv (hφ : IsEquivJ hJU φ) {X : Subgroup Γ} {g : Γ} (hgJ : g ∈ J)
    (hgX : g ∈ Subgroup.normalizer (X : Set Γ)) :
    g ∈ Subgroup.normalizer ((((X.subgroupOf U).map φ).map W.subtype : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ J, g ∈ Subgroup.normalizer (X : Set Γ) → ∀ y : Γ,
      y ∈ ((X.subgroupOf U).map φ).map W.subtype →
        g * y * g⁻¹ ∈ ((X.subgroupOf U).map φ).map W.subtype := by
    rintro g hgJ hgX _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJU hgJ) u).mp u.2⟩,
      (Subgroup.mem_normalizer_iff.mp hgX u).mp hu, rfl⟩, ?_⟩
    exact hφ g hgJ u
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hgJ hgX y, fun hy => ?_⟩
  have := key g⁻¹ (J.inv_mem hgJ) (Subgroup.inv_mem _ hgX) _ hy
  simpa [mul_assoc] using this

theorem validX_map (hφ : IsEquivJ hJU φ) {X : Subgroup Γ} {q : ℕ} (hLJ : L ≤ J)
    (hX : ValidX J L R U q X) : ValidX J L R W q (((X.subgroupOf U).map φ).map W.subtype) := by
  set X' := ((X.subgroupOf U).map φ).map W.subtype with hX'
  have hmem : ∀ u : ↥U, (u : Γ) ∈ X → ((φ u : ↥W) : Γ) ∈ X' := fun u hu => ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have hnL : L ≤ Subgroup.normalizer (X' : Set Γ) := fun l hl =>
    mem_normalizer_map_of_equiv hφ (hLJ hl) (hX.nL hl)
  have hcomm : ∀ (a : ↥U) (l : Γ) (hl : l ∈ L) (h : ⁅(a : Γ), l⁆ ∈ U),
      ((φ ⟨⁅(a : Γ), l⁆, h⟩ : ↥W) : Γ) = ⁅((φ a : ↥W) : Γ), l⁆ := by
    intro a l hl h
    have hlU := hJU (hLJ hl)
    have e : (⟨⁅(a : Γ), l⁆, h⟩ : ↥U) =
        a * (⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlU a).mp a.2⟩ : ↥U)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hφ l (hLJ hl) a,
      commutatorElement_def]
    group
  refine ⟨Subgroup.map_subtype_le _, fun g hg => mem_normalizer_map_of_equiv hφ hg.2 (hX.nR hg),
    hnL, le_antisymm ?_ ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro y hy l hl
    have h1 : l * y⁻¹ * l⁻¹ ∈ X' :=
      (Subgroup.mem_normalizer_iff.mp (hnL hl) _).mp (X'.inv_mem hy)
    have e : ⁅y, l⁆ = y * (l * y⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact X'.mul_mem hy h1
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    set S := {g : Γ | ∃ g₁ ∈ X, ∃ g₂ ∈ L, ⁅g₁, g₂⁆ = g} with hS
    have hle : Subgroup.closure S ≤ U := by
      rw [← Subgroup.commutator_def]
      exact hX.comm.le.trans hX.le
    have key : ∀ z (hz : z ∈ Subgroup.closure S), ((φ ⟨z, hle hz⟩ : ↥W) : Γ) ∈ ⁅X', L⁆ := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz' =>
        obtain ⟨a, ha, l, hl, rfl⟩ := hz'
        rw [hcomm ⟨a, hX.le ha⟩ l hl]
        exact Subgroup.commutator_mem_commutator (hmem ⟨a, hX.le ha⟩ ha) hl
      | one =>
        rw [show (⟨1, hle (Subgroup.one_mem _)⟩ : ↥U) = 1 from rfl, map_one]
        exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, hle (Subgroup.mul_mem _ hx hy)⟩ : ↥U) = ⟨x, hle hx⟩ * ⟨y, hle hy⟩ from
          rfl, map_mul, Subgroup.coe_mul]
        exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ihx =>
        rw [show (⟨x⁻¹, hle (Subgroup.inv_mem _ hx)⟩ : ↥U) = (⟨x, hle hx⟩)⁻¹ from rfl, map_inv,
          Subgroup.coe_inv]
        exact Subgroup.inv_mem _ ihx
    have hu' : (u : Γ) ∈ Subgroup.closure S := by
      rw [← Subgroup.commutator_def, hX.comm]
      exact hu
    exact key _ hu'
  · intro o ho
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hoJ : o ∈ J := hLJ (CFSG.LieType.BorelTits.pCoreOf_le 2 L ho)
    have h1 := hφ o hoJ u
    have hou : (u : Γ) * o = o * u := Subgroup.mem_centralizer_iff.mp (hX.cO ho) (u : Γ) hu
    have h2 : (⟨o * (u : Γ) * o⁻¹, (Subgroup.mem_normalizer_iff.mp (hJU hoJ) u).mp u.2⟩ : ↥U) =
        u := Subtype.ext (show o * (u : Γ) * o⁻¹ = u by rw [← hou, mul_inv_cancel_right])
    rw [h2] at h1
    calc ((φ u : ↥W) : Γ) * o = o * (φ u : ↥W) * o⁻¹ * o := by rw [← h1]
      _ = o * (φ u : ↥W) := by group
  ·
    set f : ↥X →* Γ := W.subtype.comp (φ.comp (Subgroup.inclusion hX.le)) with hf
    have hfX : ∀ x, f x ∈ X' := fun x => hmem _ x.2
    set φX : ↥X →* ↥X' := f.codRestrict X' hfX with hφX
    have hsurj : Function.Surjective φX := by
      rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    have hmap : ((Subgroup.centralizer (L : Set Γ) ⊓ X).subgroupOf X).map φX ≤
        (Subgroup.centralizer (L : Set Γ) ⊓ X').subgroupOf X' := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, (φX x).2⟩
      show ((φX x : ↥X') : Γ) ∈ Subgroup.centralizer (L : Set Γ)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hφ l (hLJ hl) (Subgroup.inclusion hX.le x)
      have hxl : (x : Γ) * l = l * x := (Subgroup.mem_centralizer_iff.mp hx.1 l hl).symm
      have h2 : (⟨l * ((Subgroup.inclusion hX.le x : ↥U) : Γ) * l⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hJU (hLJ hl)) _).mp
            (Subgroup.inclusion hX.le x).2⟩ : ↥U) = Subgroup.inclusion hX.le x :=
        Subtype.ext (by
          show l * (x : Γ) * l⁻¹ = x
          rw [← hxl, mul_inv_cancel_right])
      rw [h2] at h1
      show l * ((φ (Subgroup.inclusion hX.le x) : ↥W) : Γ) =
        ((φ (Subgroup.inclusion hX.le x) : ↥W) : Γ) * l
      calc l * ((φ (Subgroup.inclusion hX.le x) : ↥W) : Γ)
          = l * (φ (Subgroup.inclusion hX.le x) : ↥W) * l⁻¹ * l := by group
        _ = _ := by rw [← h1]
    have h1 := Subgroup.index_map_dvd ((Subgroup.centralizer (L : Set Γ) ⊓ X).subgroupOf X) hsurj
    have h2 := Subgroup.index_dvd_of_le hmap
    have hne : ((Subgroup.centralizer (L : Set Γ) ⊓ X).subgroupOf X).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    calc (Subgroup.centralizer (L : Set Γ) ⊓ X').relIndex X'
        ≤ ((Subgroup.centralizer (L : Set Γ) ⊓ X).subgroupOf X).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (h2.trans h1)
      _ ≤ q ^ 2 := hX.card

end Map

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
