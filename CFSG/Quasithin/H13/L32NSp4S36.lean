module

public import CFSG.Quasithin.H13.L32NSp4Cases
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

theorem finite_gl {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun γ : V ≃ₗ[ZMod 2] V => (γ : V → V))
    (fun _ _ hab => LinearEquiv.ext (congrFun hab))

theorem mem_of_contains {l : List (List ℕ)} {x : List ℕ} (h : l.contains x = true) : x ∈ l := by
  simpa using h

theorem closed_of_closedB {l : List (List ℕ)} (h : closedB l = true) :
    ∀ x ∈ l, ∀ y ∈ l, mulC x y ∈ l := by
  intro x hx y hy
  exact mem_of_contains (List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy)

section Facts

variable [Sp4Data]

theorem a36_one : oneC4 ∈ specK.a36.1 :=
  mem_of_contains (specialOk_get (c := specK.a36.1.contains oneC4) (by simp [specialChecks]))

theorem b36_one : oneC4 ∈ specK.b36.1 :=
  mem_of_contains (specialOk_get (c := specK.b36.1.contains oneC4) (by simp [specialChecks]))

theorem p9_one : oneC4 ∈ p9C.1 :=
  mem_of_contains (specialOk_get (c := p9C.1.contains oneC4) (by simp [specialChecks]))

theorem a36_mul : ∀ x ∈ specK.a36.1, ∀ y ∈ specK.a36.1, mulC x y ∈ specK.a36.1 :=
  closed_of_closedB (specialOk_get (c := closedB specK.a36.1) (by simp [specialChecks]))

theorem b36_mul : ∀ x ∈ specK.b36.1, ∀ y ∈ specK.b36.1, mulC x y ∈ specK.b36.1 :=
  closed_of_closedB (specialOk_get (c := closedB specK.b36.1) (by simp [specialChecks]))

theorem p9_mul : ∀ x ∈ p9C.1, ∀ y ∈ p9C.1, mulC x y ∈ p9C.1 :=
  closed_of_closedB (specialOk_get (c := closedB p9C.1) (by simp [specialChecks]))

theorem a36_nodup : specK.a36.1.Nodup := by
  simpa using specialOk_get (c := decide specK.a36.1.Nodup) (by simp [specialChecks])

theorem b36_nodup : specK.b36.1.Nodup := by
  simpa using specialOk_get (c := decide specK.b36.1.Nodup) (by simp [specialChecks])

theorem p9_nodup : p9C.1.Nodup := by
  simpa using specialOk_get (c := decide p9C.1.Nodup) (by simp [specialChecks])

theorem a36_len : specK.a36.1.length = 6 := by
  simpa using specialOk_get (c := specK.a36.1.length == 6) (by simp [specialChecks])

theorem b36_len : specK.b36.1.length = 6 := by
  simpa using specialOk_get (c := specK.b36.1.length == 6) (by simp [specialChecks])

theorem p9_len : p9C.1.length = 9 := by
  simpa using specialOk_get (c := p9C.1.length == 9) (by simp [specialChecks])

theorem sub_s36_of_memM {l : List (List ℕ)} (hv : ∀ x ∈ l, ValidC4 x)
    (h : l.all (memM specK.s36.2) = true) : ∀ x ∈ l, x ∈ specK.s36.1 := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  rw [specK_s36_mask] at this
  exact mem_of_memM_maskOf specK_s36_valid (hv x hx) this

theorem a36_sub : ∀ x ∈ specK.a36.1, x ∈ specK.s36.1 :=
  sub_s36_of_memM specK_a36_valid
    (specialOk_get (c := specK.a36.1.all (memM specK.s36.2)) (by simp [specialChecks]))

theorem b36_sub : ∀ x ∈ specK.b36.1, x ∈ specK.s36.1 :=
  sub_s36_of_memM specK_b36_valid
    (specialOk_get (c := specK.b36.1.all (memM specK.s36.2)) (by simp [specialChecks]))

theorem p9_sub : ∀ x ∈ p9C.1, x ∈ specK.s36.1 := by
  intro x hx
  have := specialOk_get (c := p9C.1.all (fun x => specK.s36.1.contains x)) (by simp [specialChecks])
  exact mem_of_contains (List.all_eq_true.mp this x hx)

theorem a36_nonab : ∃ x ∈ specK.a36.1, ∃ y ∈ specK.a36.1, mulC x y ≠ mulC y x := by
  have := specialOk_get
    (c := specK.a36.1.any (fun x => specK.a36.1.any fun y => mulC x y != mulC y x))
    (by simp [specialChecks])
  simpa using this

theorem b36_nonab : ∃ x ∈ specK.b36.1, ∃ y ∈ specK.b36.1, mulC x y ≠ mulC y x := by
  have := specialOk_get
    (c := specK.b36.1.any (fun x => specK.b36.1.any fun y => mulC x y != mulC y x))
    (by simp [specialChecks])
  simpa using this

theorem ab_comm : ∀ x ∈ specK.a36.1, ∀ y ∈ specK.b36.1, mulC x y = mulC y x := by
  have := specialOk_get
    (c := specK.a36.1.all (fun x => specK.b36.1.all fun y => mulC x y == mulC y x))
    (by simp [specialChecks])
  simpa using this

theorem ab_meet : ∀ x ∈ specK.a36.1, x ∈ specK.b36.1 → x = oneC4 := by
  have := specialOk_get (c := specK.a36.1.all (fun x => !memM specK.b36.2 x || x == oneC4))
    (by simp [specialChecks])
  intro x hx hxb
  have h := List.all_eq_true.mp this x hx
  rw [specK_b36_mask, memM_maskOf_of_mem hxb] at h
  simpa using h

theorem p9_norm : ∀ g ∈ specK.s36.1, ∀ x ∈ p9C.1, ∃ y ∈ p9C.1, mulC g x = mulC y g := by
  have := specialOk_get
    (c := specK.s36.1.all (fun g => p9C.1.all fun x => p9C.1.any fun y => mulC g x == mulC y g))
    (by simp [specialChecks])
  simpa using this

theorem p9_ord3 : ∀ x ∈ specK.s36.1, ord3 x = true → x ∈ p9C.1 := by
  have := specialOk_get (c := specK.s36.1.all (fun x => !(ord3 x) || p9C.1.contains x))
    (by simp [specialChecks])
  intro x hx h3
  have h := List.all_eq_true.mp this x hx
  rw [h3] at h
  simpa using h

theorem p9C_comm : ∀ x ∈ p9C.1, ∀ y ∈ p9C.1, mulC x y = mulC y x := by
  have := specialOk_get (c := p9C.1.all (fun x => p9C.1.all fun y => mulC x y == mulC y x))
    (by simp [specialChecks])
  simpa using this

theorem p9_cube : ∀ x ∈ p9C.1, mulC x (mulC x x) = oneC4 := by
  have := specialOk_get (c := p9C.1.all (fun x => mulC x (mulC x x) == oneC4))
    (by simp [specialChecks])
  simpa using this

theorem sp_no9 : ∀ x ∈ spElsC, powC x 9 = oneC4 → mulC x (mulC x x) = oneC4 := by
  have := specialOk_get
    (c := spElsC.all (fun x => powC x 9 != oneC4 || mulC x (mulC x x) == oneC4))
    (by simp [specialChecks])
  intro x hx h9
  have h := List.all_eq_true.mp this x hx
  rw [h9] at h
  simpa using h

end Facts

theorem cf_pow {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) (n : ℕ) :
    cf b (γ ^ n) = powC (cf b γ) n := by
  induction n with
  | zero => rw [pow_zero, cf_one]; rfl
  | succ n ih => rw [pow_succ, cf_mul, ih]; rfl

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {b : Module.Basis (Fin 4) (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {s : Node}

@[expose] def listSub (b : Module.Basis (Fin 4) (ZMod 2) V) (l : List (List ℕ))
    (h1 : oneC4 ∈ l) (hmul : ∀ x ∈ l, ∀ y ∈ l, mulC x y ∈ l) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {γ | cf b γ ∈ l}
  mul_mem' {γ δ} hγ hδ := by
    show cf b (γ * δ) ∈ l
    rw [cf_mul]
    exact hmul _ hγ _ hδ
  one_mem' := by
    show cf b 1 ∈ l
    rw [cf_one]
    exact h1
  inv_mem' {γ} hγ := by
    have := finite_gl (V := V)
    have hpow : ∀ n : ℕ, cf b (γ ^ n) ∈ l := by
      intro n
      induction n with
      | zero => rw [pow_zero, cf_one]; exact h1
      | succ n ih => rw [pow_succ, cf_mul]; exact hmul _ ih _ hγ
    have hinv : γ⁻¹ = γ ^ (orderOf γ - 1) := by
      have hpos := orderOf_pos γ
      symm
      rw [← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    show cf b γ⁻¹ ∈ l
    rw [hinv]
    exact hpow _

theorem mem_listSub {l : List (List ℕ)} {h1 : oneC4 ∈ l} {hmul : ∀ x ∈ l, ∀ y ∈ l, mulC x y ∈ l}
    {γ : V ≃ₗ[ZMod 2] V} : γ ∈ listSub b l h1 hmul ↔ cf b γ ∈ l := Iff.rfl

theorem listSub_le (h : IsNodeOf b Γ s) {l : List (List ℕ)} {h1 : oneC4 ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, mulC x y ∈ l} (hl : ∀ x ∈ l, x ∈ s.els) :
    listSub b l h1 hmul ≤ Γ :=
  fun γ hγ => (h.mem γ).mpr (hl _ hγ)

theorem card_listSub (h : IsNodeOf b Γ s) {l : List (List ℕ)} {h1 : oneC4 ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, mulC x y ∈ l} (hnd : l.Nodup) (hl : ∀ x ∈ l, x ∈ s.els) :
    Nat.card (listSub b l h1 hmul) = l.length := by
  classical
  have hle := listSub_le h (h1 := h1) (hmul := hmul) hl
  have h2 := h.card_filter (fun x => l.contains x) (listSub b l h1 hmul) fun γ _ => by
    rw [mem_listSub]
    simp
  rw [inf_eq_right.mpr hle] at h2
  rw [h2, ← List.toFinset_card_of_nodup (h.nodup.filter _), ← List.toFinset_card_of_nodup hnd]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, List.contains_iff_mem]
  exact ⟨fun hx => hx.2, fun hx => ⟨hl x hx, hx⟩⟩

section S36

variable [Sp4Data]

@[expose] def factA (b : Module.Basis (Fin 4) (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  listSub b specK.a36.1 a36_one a36_mul

@[expose] def factB (b : Module.Basis (Fin 4) (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  listSub b specK.b36.1 b36_one b36_mul

@[expose] def p9Sub (b : Module.Basis (Fin 4) (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  listSub b p9C.1 p9_one p9_mul

variable (h : IsNodeOf b Γ s) (h36 : ∀ x, x ∈ s.els ↔ x ∈ specK.s36.1)
include h h36

theorem S36.factA_le : factA b ≤ Γ := listSub_le h fun x hx => (h36 x).mpr (a36_sub x hx)

theorem S36.factB_le : factB b ≤ Γ := listSub_le h fun x hx => (h36 x).mpr (b36_sub x hx)

theorem S36.p9_le : p9Sub b ≤ Γ := listSub_le h fun x hx => (h36 x).mpr (p9_sub x hx)

theorem S36.card_factA : Nat.card (factA b) = 6 :=
  (card_listSub h a36_nodup fun x hx => (h36 x).mpr (a36_sub x hx)).trans a36_len

theorem S36.card_factB : Nat.card (factB b) = 6 :=
  (card_listSub h b36_nodup fun x hx => (h36 x).mpr (b36_sub x hx)).trans b36_len

theorem S36.card_p9 : Nat.card (p9Sub b) = 9 :=
  (card_listSub h p9_nodup fun x hx => (h36 x).mpr (p9_sub x hx)).trans p9_len

omit h h36 in
theorem S36.comm {α β : V ≃ₗ[ZMod 2] V} (hα : α ∈ factA b) (hβ : β ∈ factB b) :
    α * β = β * α := by
  apply cf_injective b
  rw [cf_mul, cf_mul]
  exact ab_comm _ hα _ hβ

omit h h36 in
theorem S36.inf_eq : factA b ⊓ factB b = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot, ← cf_eq_oneC4_iff b]
  exact ab_meet _ hγ.1 hγ.2

theorem S36.nonab_A : ∃ α ∈ factA b, ∃ β ∈ factA b, α * β ≠ β * α := by
  obtain ⟨x, hx, y, hy, hxy⟩ := a36_nonab
  obtain ⟨α, -, rfl⟩ := h.surj x ((h36 x).mpr (a36_sub x hx))
  obtain ⟨β, -, rfl⟩ := h.surj y ((h36 y).mpr (a36_sub y hy))
  refine ⟨α, hx, β, hy, fun he => hxy ?_⟩
  rw [← cf_mul, ← cf_mul, he]

theorem S36.nonab_B : ∃ α ∈ factB b, ∃ β ∈ factB b, α * β ≠ β * α := by
  obtain ⟨x, hx, y, hy, hxy⟩ := b36_nonab
  obtain ⟨α, -, rfl⟩ := h.surj x ((h36 x).mpr (b36_sub x hx))
  obtain ⟨β, -, rfl⟩ := h.surj y ((h36 y).mpr (b36_sub y hy))
  refine ⟨α, hx, β, hy, fun he => hxy ?_⟩
  rw [← cf_mul, ← cf_mul, he]

omit [Finite V] in
theorem S36.card_eq : Nat.card Γ = 36 := by
  rw [h.card_eq]
  have := specialOk_get (c := specK.s36.1.length == 36) (by simp [specialChecks])
  have hl : specK.s36.1.length = 36 := by simpa using this
  rw [← hl]
  have hnd : specK.s36.1.Nodup := by
    simpa using specialOk_get (c := decide specK.s36.1.Nodup) (by simp [specialChecks])
  rw [← List.toFinset_card_of_nodup h.nodup, ← List.toFinset_card_of_nodup hnd]
  congr 1
  ext x
  simp only [List.mem_toFinset]
  exact h36 x

omit h h36 in
@[expose] noncomputable def S36.mulHom : factA b × factB b →* V ≃ₗ[ZMod 2] V :=
  MonoidHom.noncommCoprod (factA b).subtype (factB b).subtype fun a c =>
    S36.comm a.2 c.2

omit h h36 in
theorem S36.mulHom_injective : Function.Injective (S36.mulHom (b := b)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, c⟩ he
  have he' : (a : V ≃ₗ[ZMod 2] V) * c = 1 := he
  have ha : (a : V ≃ₗ[ZMod 2] V) = (c : V ≃ₗ[ZMod 2] V)⁻¹ := eq_inv_of_mul_eq_one_left he'
  have hab : (a : V ≃ₗ[ZMod 2] V) ∈ factA b ⊓ factB b := ⟨a.2, by rw [ha]; exact (factB b).inv_mem c.2⟩
  rw [S36.inf_eq, Subgroup.mem_bot] at hab
  have hc : (c : V ≃ₗ[ZMod 2] V) = 1 := by
    rw [hab, one_mul] at he'
    exact he'
  exact Prod.ext (Subtype.ext hab) (Subtype.ext hc)

theorem S36.mulHom_mem (x : factA b × factB b) : S36.mulHom (b := b) x ∈ Γ :=
  Γ.mul_mem (S36.factA_le h h36 x.1.2) (S36.factB_le h h36 x.2.2)

theorem S36.codRestrict_bijective :
    Function.Bijective ((S36.mulHom (b := b)).codRestrict Γ (S36.mulHom_mem h h36)) := by
  have := finite_gl (V := V)
  have hinj : Function.Injective ((S36.mulHom (b := b)).codRestrict Γ (S36.mulHom_mem h h36)) :=
    fun x y hxy => S36.mulHom_injective (congrArg Subtype.val hxy)
  refine hinj.bijective_of_nat_card_le ?_
  rw [S36.card_eq h h36, Nat.card_prod, S36.card_factA h h36, S36.card_factB h h36]

theorem S36.exists_mul {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) :
    ∃ α ∈ factA b, ∃ β ∈ factB b, α * β = γ := by
  obtain ⟨⟨α, β⟩, he⟩ := (S36.codRestrict_bijective h h36).2 ⟨γ, hγ⟩
  exact ⟨α, α.2, β, β.2, congrArg Subtype.val he⟩

theorem S36.normal_A : Γ ≤ Subgroup.normalizer (factA b : Set (V ≃ₗ[ZMod 2] V)) := by
  have hconj : ∀ γ ∈ Γ, ∀ a ∈ factA b, γ * a * γ⁻¹ ∈ factA b := by
    intro γ hγ a ha
    obtain ⟨α, hα, β, hβ, rfl⟩ := S36.exists_mul h h36 hγ
    have hc : β * a * β⁻¹ = a := by rw [← S36.comm ha hβ, mul_inv_cancel_right]
    rw [show α * β * a * (α * β)⁻¹ = α * (β * a * β⁻¹) * α⁻¹ by group, hc]
    exact (factA b).mul_mem ((factA b).mul_mem hα ha) ((factA b).inv_mem hα)
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨hconj γ hγ a, fun ha => ?_⟩
  have := hconj γ⁻¹ (Γ.inv_mem hγ) _ ha
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

theorem S36.normal_B : Γ ≤ Subgroup.normalizer (factB b : Set (V ≃ₗ[ZMod 2] V)) := by
  have hconj : ∀ γ ∈ Γ, ∀ c ∈ factB b, γ * c * γ⁻¹ ∈ factB b := by
    intro γ hγ c hc
    obtain ⟨α, hα, β, hβ, rfl⟩ := S36.exists_mul h h36 hγ
    have hc' : α * c * α⁻¹ = c := by rw [S36.comm hα hc, mul_inv_cancel_right]
    rw [show α * β * c * (α * β)⁻¹ = α * (β * c * β⁻¹) * α⁻¹ by group]
    have hβc : β * c * β⁻¹ ∈ factB b :=
      (factB b).mul_mem ((factB b).mul_mem hβ hc) ((factB b).inv_mem hβ)
    rw [show α * (β * c * β⁻¹) * α⁻¹ = β * c * β⁻¹ by
      rw [S36.comm hα hβc, mul_inv_cancel_right]]
    exact hβc
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hconj γ hγ c, fun hc => ?_⟩
  have := hconj γ⁻¹ (Γ.inv_mem hγ) _ hc
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

theorem S36.mulEquiv : Nonempty (↥Γ ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  have := finite_gl (V := V)
  let f := (S36.mulHom (b := b)).codRestrict Γ (S36.mulHom_mem h h36)
  have hf : Function.Bijective f := S36.codRestrict_bijective h h36
  obtain ⟨eA⟩ := SBd.nonempty_mulEquiv_perm_three_of_card_six (S36.card_factA h h36) (by
    obtain ⟨α, hα, β, hβ, hne⟩ := S36.nonab_A h h36
    exact ⟨⟨α, hα⟩, ⟨β, hβ⟩, fun he => hne (congrArg Subtype.val he)⟩)
  obtain ⟨eB⟩ := SBd.nonempty_mulEquiv_perm_three_of_card_six (S36.card_factB h h36) (by
    obtain ⟨α, hα, β, hβ, hne⟩ := S36.nonab_B h h36
    exact ⟨⟨α, hα⟩, ⟨β, hβ⟩, fun he => hne (congrArg Subtype.val he)⟩)
  exact ⟨(MulEquiv.ofBijective f hf).symm.trans (MulEquiv.prodCongr eA eB)⟩

theorem S36.p9_normal : Γ ≤ Subgroup.normalizer (p9Sub b : Set (V ≃ₗ[ZMod 2] V)) := by
  have hconj : ∀ γ ∈ Γ, ∀ π ∈ p9Sub b, γ * π * γ⁻¹ ∈ p9Sub b := by
    intro γ hγ π hπ
    obtain ⟨y, hy, hyx⟩ := p9_norm (cf b γ) ((h36 _).mp (h.mem_els hγ)) (cf b π) hπ
    obtain ⟨ρ, -, rfl⟩ := h.surj y ((h36 y).mpr (p9_sub y hy))
    have he : γ * π = ρ * γ := by
      apply cf_injective b
      rw [cf_mul, cf_mul]
      exact hyx
    rw [he, mul_inv_cancel_right]
    exact hy
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro π
  constructor
  · exact hconj γ hγ π
  · intro hπ
    have := hconj γ⁻¹ (Γ.inv_mem hγ) _ hπ
    rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
      mul_one] at this

omit h h36 in
theorem S36.p9_comm {π ρ : V ≃ₗ[ZMod 2] V} (hπ : π ∈ p9Sub b) (hρ : ρ ∈ p9Sub b) :
    π * ρ = ρ * π := by
  apply cf_injective b
  rw [cf_mul, cf_mul]
  exact p9C_comm _ hπ _ hρ

theorem S36.mem_p9 {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) (h3 : γ ^ 3 = 1) :
    γ ∈ p9Sub b :=
  p9_ord3 _ ((h36 _).mp (h.mem_els hγ)) ((ord3_cf b γ).mpr ⟨h1, h3⟩)

end S36

theorem perm_three_center : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → ∃ τ : Equiv.Perm (Fin 3),
    σ * τ ≠ τ * σ := by decide

theorem eq_of_le_card_six {G : Type*} [Group G] [Finite G] {A N : Subgroup G}
    (hA : Nat.card A = 6) (hnc : ∃ α ∈ A, ∃ β ∈ A, α * β ≠ β * α) (hNA : N ≤ A)
    (hnorm : A ≤ Subgroup.normalizer (N : Set G)) {z : G} (hz : z ∈ N) (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) : N = A := by
  have hdvd : Nat.card N ∣ 6 := hA ▸ Subgroup.card_dvd_of_le hNA
  have hoz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have h2 : 2 ∣ Nat.card N := by
    rw [← hoz]
    exact Subgroup.orderOf_dvd_natCard N hz
  have hcases : Nat.card N = 2 ∨ Nat.card N = 6 := by
    have : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card N <;> simp_all
  rcases hcases with h2' | h6
  · exfalso
    have hNz : N = Subgroup.zpowers z := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
      rw [h2', Nat.card_zpowers, hoz]
    have hmemN : ∀ x ∈ N, x = 1 ∨ x = z := by
      intro x hx
      classical
      rw [hNz, mem_zpowers_iff_mem_range_orderOf, hoz] at hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      interval_cases k <;> simp
    have hcent : ∀ a ∈ A, a * z = z * a := by
      intro a ha
      have hc := (Subgroup.mem_normalizer_iff.mp (hnorm ha) z).mp hz
      rcases hmemN _ hc with h1 | h1
      · exfalso
        apply hz1
        calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
      · calc a * z = a * z * a⁻¹ * a := by group
          _ = z * a := by rw [h1]
    obtain ⟨e⟩ := SBd.nonempty_mulEquiv_perm_three_of_card_six hA (by
      obtain ⟨α, hα, β, hβ, hne⟩ := hnc
      exact ⟨⟨α, hα⟩, ⟨β, hβ⟩, fun he => hne (congrArg Subtype.val he)⟩)
    have hzA : z ∈ A := hNA hz
    obtain ⟨τ, hτ⟩ := perm_three_center (e ⟨z, hzA⟩) (by
      rw [Ne, MulEquiv.map_eq_one_iff]
      exact fun h => hz1 (congrArg Subtype.val h))
    apply hτ
    obtain ⟨a, rfl⟩ := e.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcent a a.2).symm
  · exact Subgroup.eq_of_le_of_card_ge hNA (by rw [h6, hA])

end CFSG.Quasithin.H13.Sp4Cert
