module

public import CFSG.Monster.VisQuot.Monomial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel

@[expose] def ΩIn (D : Submodule (ZMod 2) (Fin 24 → ZMod 2)) : Submodule (ZMod 2) D :=
  (Submodule.span (ZMod 2) {Ω}).comap D.subtype

theorem mem_span_Ω_iff {x : Fin 24 → ZMod 2} :
    x ∈ Submodule.span (ZMod 2) {Ω} ↔ x = 0 ∨ x = Ω := by
  rw [Submodule.mem_span_singleton]
  have hs : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  constructor
  · rintro ⟨s, rfl⟩
    rcases hs s with rfl | rfl
    · exact .inl (zero_smul _ _)
    · exact .inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem mem_ΩIn {D : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {a : D} :
    a ∈ ΩIn D ↔ (a : Fin 24 → ZMod 2) = 0 ∨ (a : Fin 24 → ZMod 2) = Ω :=
  mem_span_Ω_iff

structure MonoHyp (D : Submodule (ZMod 2) (Fin 24 → ZMod 2)) (Q : Subgroup AutPerm) : Prop where
  le_C : D ≤ C
  Ω_mem : Ω ∈ D
  preserves : ∀ p ∈ Q, ∀ a ∈ D, permWord p a ∈ D

variable {D : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {Q : Subgroup AutPerm}

theorem permWord_one' (x : Fin 24 → ZMod 2) : permWord 1 x = x := by
  funext i
  simp [permWord]

@[expose] def permCD (h : MonoHyp D Q) (p : Q) : D ≃ₗ[ZMod 2] D where
  toFun a := ⟨permWord p a, h.preserves p p.2 a a.2⟩
  invFun a := ⟨permWord (p⁻¹ : Q) a, h.preserves _ (p⁻¹).2 a a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := Subtype.ext (by
    change permWord ((p⁻¹ : Q) : AutPerm) (permWord (p : AutPerm) a) = a
    rw [← permWord_mul]
    have : (((p⁻¹ : Q) : AutPerm) : Equiv.Perm (Fin 24)) * ((p : AutPerm) : Equiv.Perm (Fin 24)) =
        1 := by
      rw [Subgroup.coe_inv, Subgroup.coe_inv, inv_mul_cancel]
    rw [this, permWord_one'])
  right_inv a := Subtype.ext (by
    change permWord (p : AutPerm) (permWord ((p⁻¹ : Q) : AutPerm) a) = a
    rw [← permWord_mul]
    have : ((p : AutPerm) : Equiv.Perm (Fin 24)) * (((p⁻¹ : Q) : AutPerm) : Equiv.Perm (Fin 24)) =
        1 := by
      rw [Subgroup.coe_inv, Subgroup.coe_inv, mul_inv_cancel]
    rw [this, permWord_one'])

theorem coe_permCD (h : MonoHyp D Q) (p : Q) (a : D) :
    ((permCD h p a : D) : Fin 24 → ZMod 2) = permWord p a := rfl

theorem permWord_zero (p : Equiv.Perm (Fin 24)) : permWord p 0 = 0 := rfl

theorem permWord_Ω (p : Equiv.Perm (Fin 24)) : permWord p Ω = Ω := rfl

theorem permWord_injective (p : Equiv.Perm (Fin 24)) : Function.Injective (permWord p) := by
  intro x y hxy
  funext i
  have := congrFun hxy (p i)
  rwa [permWord_apply, permWord_apply] at this

theorem permCD_mem_ΩIn (h : MonoHyp D Q) (p : Q) {a : D} :
    permCD h p a ∈ ΩIn D ↔ a ∈ ΩIn D := by
  rw [mem_ΩIn, mem_ΩIn, coe_permCD]
  constructor
  · rintro (e | e)
    · exact .inl (permWord_injective _ (e.trans (permWord_zero _).symm))
    · exact .inr (permWord_injective _ (e.trans (permWord_Ω _).symm))
  · rintro (e | e)
    · left; rw [e]; rfl
    · right; rw [e]; rfl

theorem map_permCD_ΩIn (h : MonoHyp D Q) (p : Q) :
    (ΩIn D).map (permCD h p : D →ₗ[ZMod 2] D) = ΩIn D := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (permCD_mem_ΩIn h p).2 hb
  · intro ha
    refine ⟨(permCD h p).symm a, ?_, (permCD h p).apply_symm_apply a⟩
    change (permCD h p).symm a ∈ ΩIn D
    rw [← permCD_mem_ΩIn h p, LinearEquiv.apply_symm_apply]
    exact ha

@[expose] def permQD (h : MonoHyp D Q) (p : Q) : (D ⧸ ΩIn D) ≃ₗ[ZMod 2] (D ⧸ ΩIn D) :=
  Submodule.Quotient.equiv (ΩIn D) (ΩIn D) (permCD h p) (map_permCD_ΩIn h p)

theorem permQD_mk (h : MonoHyp D Q) (p : Q) (a : D) :
    permQD h p (Submodule.Quotient.mk a) = Submodule.Quotient.mk (permCD h p a) := rfl

theorem multQD_induction {P : Multiplicative (D ⧸ ΩIn D) → Prop}
    (h : ∀ a : D, P (Multiplicative.ofAdd (Submodule.Quotient.mk a))) (x) : P x := by
  induction x using Multiplicative.rec with
  | ofAdd x =>
    induction x using Submodule.Quotient.induction_on with
    | H a => exact h a

@[expose] def permActD (h : MonoHyp D Q) : Q →* MulAut (Multiplicative (D ⧸ ΩIn D)) where
  toFun p := AddEquiv.toMultiplicative (permQD h p).toAddEquiv
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using multQD_induction with
    | h a =>
      show Multiplicative.ofAdd (permQD h 1 (Submodule.Quotient.mk a)) =
        Multiplicative.ofAdd (Submodule.Quotient.mk a)
      rw [permQD_mk]
      congr 2
  map_mul' p q := by
    refine MulEquiv.ext fun x => ?_
    induction x using multQD_induction with
    | h a =>
      show Multiplicative.ofAdd (permQD h (p * q) (Submodule.Quotient.mk a)) =
        Multiplicative.ofAdd (permQD h p (permQD h q (Submodule.Quotient.mk a)))
      rw [permQD_mk, permQD_mk, permQD_mk]
      congr 2

theorem permActD_mk (h : MonoHyp D Q) (p : Q) (a : D) :
    permActD h p (Multiplicative.ofAdd (Submodule.Quotient.mk a)) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (permCD h p a)) := rfl

abbrev SDD (h : MonoHyp D Q) : Type := Multiplicative (D ⧸ ΩIn D) ⋊[permActD h] Q

theorem ΩIn_le_comap (h : MonoHyp D Q) :
    ΩIn D ≤ ΩLine.comap (Submodule.inclusion h.le_C) := by
  intro a ha
  rw [Submodule.mem_comap, mem_ΩLine_iff]
  rcases mem_ΩIn.1 ha with e | e
  · exact .inl (Subtype.ext e)
  · exact .inr (Subtype.ext e)

@[expose] def inclQ (h : MonoHyp D Q) :
    Multiplicative (D ⧸ ΩIn D) →* Multiplicative (C ⧸ ΩLine) :=
  AddMonoidHom.toMultiplicative
    (Submodule.mapQ (ΩIn D) ΩLine (Submodule.inclusion h.le_C) (ΩIn_le_comap h)).toAddMonoidHom

theorem inclQ_mk (h : MonoHyp D Q) (a : D) :
    inclQ h (Multiplicative.ofAdd (Submodule.Quotient.mk a)) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (Submodule.inclusion h.le_C a)) := rfl

theorem inclQ_injective (h : MonoHyp D Q) : Function.Injective (inclQ h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using multQD_induction with
  | h a =>
    rw [inclQ_mk] at hx
    have h1 : (Submodule.Quotient.mk (Submodule.inclusion h.le_C a) : C ⧸ ΩLine) = 0 :=
      congrArg Multiplicative.toAdd hx
    rw [Submodule.Quotient.mk_eq_zero, mem_ΩLine_iff] at h1
    show Multiplicative.ofAdd (Submodule.Quotient.mk a) = Multiplicative.ofAdd 0
    congr 1
    rw [Submodule.Quotient.mk_eq_zero, mem_ΩIn]
    rcases h1 with e | e
    · exact .inl (congrArg Subtype.val e)
    · exact .inr (congrArg Subtype.val e)

@[expose] def inclSD (h : MonoHyp D Q) : SDD h →* MonoSD :=
  SemidirectProduct.map (inclQ h) Q.subtype fun p => MonoidHom.ext fun x => by
    induction x using multQD_induction with
    | h a => rfl

theorem inclSD_mk (h : MonoHyp D Q) (a : D) (p : Q) :
    inclSD h ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ =
      ⟨Multiplicative.ofAdd (Submodule.Quotient.mk (Submodule.inclusion h.le_C a)), p⟩ := rfl

theorem inclSD_injective (h : MonoHyp D Q) : Function.Injective (inclSD h) := by
  intro x y hxy
  have h1 := congrArg SemidirectProduct.left hxy
  have h2 := congrArg SemidirectProduct.right hxy
  exact SemidirectProduct.ext (inclQ_injective h h1) (Subtype.ext h2)

@[expose] def monoD (h : MonoHyp D Q) : SDD h →* OLq := monoQ.comp (inclSD h)

theorem monoD_mk (h : MonoHyp D Q) (a : D) (p : Q) :
    monoD h ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ =
      QuotientGroup.mk (gO (Submodule.inclusion h.le_C a) * PO (p : AutPerm)⁻¹) := rfl

theorem monoD_injective (h : MonoHyp D Q) : Function.Injective (monoD h) :=
  monoQ_injective.comp (inclSD_injective h)

@[expose] def monoSub (h : MonoHyp D Q) : Subgroup OLq := (monoD h).range

theorem mem_monoSub_iff (h : MonoHyp D Q) {x : OLq} :
    x ∈ monoSub h ↔ ∃ a : C, (a : Fin 24 → ZMod 2) ∈ D ∧ ∃ p ∈ Q,
      x = QuotientGroup.mk (gO a * PO p) := by
  constructor
  · rintro ⟨⟨n, p⟩, rfl⟩
    induction n using multQD_induction with
    | h a =>
      exact ⟨Submodule.inclusion h.le_C a, a.2, (p : AutPerm)⁻¹, Q.inv_mem p.2, monoD_mk h a p⟩
  · rintro ⟨a, ha, p, hp, rfl⟩
    refine ⟨⟨Multiplicative.ofAdd (Submodule.Quotient.mk ⟨a, ha⟩), ⟨p, hp⟩⁻¹⟩, ?_⟩
    rw [monoD_mk]
    rfl

theorem mk_mem_monoSub (h : MonoHyp D Q) {a : C} (ha : (a : Fin 24 → ZMod 2) ∈ D)
    {p : AutPerm} (hp : p ∈ Q) : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ monoSub h :=
  (mem_monoSub_iff h).2 ⟨a, ha, p, hp, rfl⟩

@[expose] def monoSubEquiv (h : MonoHyp D Q) : SDD h ≃* monoSub h :=
  MonoidHom.ofInjective (monoD_injective h)

theorem coe_monoSubEquiv (h : MonoHyp D Q) (x : SDD h) :
    (monoSubEquiv h x : OLq) = monoD h x := rfl

theorem natCard_monoSub (h : MonoHyp D Q) :
    Nat.card (monoSub h) = Nat.card (D ⧸ ΩIn D) * Nat.card Q := by
  rw [← Nat.card_congr (monoSubEquiv h).toEquiv, SemidirectProduct.card]
  rfl

theorem monoSub_le_stabQ (h : MonoHyp D Q) : monoSub h ≤ stabQ := by
  intro x hx
  obtain ⟨a, -, p, -, rfl⟩ := (mem_monoSub_iff h).1 hx
  exact mem_stabQ_iff.2 ⟨a, p, rfl⟩

theorem monoSub_mono {D' : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {Q' : Subgroup AutPerm}
    (h : MonoHyp D Q) (h' : MonoHyp D' Q') (hD : D ≤ D') (hQQ : Q ≤ Q') :
    monoSub h ≤ monoSub h' := by
  intro x hx
  obtain ⟨a, ha, p, hp, rfl⟩ := (mem_monoSub_iff h).1 hx
  exact mk_mem_monoSub h' (hD ha) (hQQ hp)

theorem finrank_ΩIn (h : MonoHyp D Q) : Module.finrank (ZMod 2) (ΩIn D) = 1 := by
  have e : ΩIn D = Submodule.span (ZMod 2) {(⟨Ω, h.Ω_mem⟩ : D)} := by
    ext a
    rw [mem_ΩIn, Submodule.mem_span_singleton]
    have hs : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
    constructor
    · rintro (e | e)
      · exact ⟨0, Subtype.ext (by rw [zero_smul, e]; rfl)⟩
      · exact ⟨1, Subtype.ext (by rw [one_smul, e])⟩
    · rintro ⟨s, rfl⟩
      rcases hs s with rfl | rfl
      · left; rw [zero_smul]; rfl
      · right; rw [one_smul]
  rw [e]
  refine finrank_span_singleton fun h0 => ?_
  have h1 : (Ω : Fin 24 → ZMod 2) = 0 := congrArg Subtype.val h0
  exact absurd (congrFun h1 0) (by decide)

theorem natCard_quot_ΩIn (h : MonoHyp D Q) :
    Nat.card (D ⧸ ΩIn D) = 2 ^ (Module.finrank (ZMod 2) D - 1) := by
  have h1 := Submodule.finrank_quotient_add_finrank (ΩIn D)
  rw [finrank_ΩIn h] at h1
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  omega

@[expose] noncomputable def monoProj (h : MonoHyp D Q) : monoSub h →* Q :=
  SemidirectProduct.rightHom.comp (monoSubEquiv h).symm.toMonoidHom

theorem monoProj_surjective (h : MonoHyp D Q) : Function.Surjective (monoProj h) :=
  SemidirectProduct.rightHom_surjective.comp (monoSubEquiv h).symm.surjective

theorem monoProj_monoSubEquiv (h : MonoHyp D Q) (x : SDD h) :
    monoProj h (monoSubEquiv h x) = x.right := by
  change SemidirectProduct.rightHom ((monoSubEquiv h).symm (monoSubEquiv h x)) = x.right
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem monoProj_mk (h : MonoHyp D Q) (a : D) (p : Q) :
    monoProj h ⟨QuotientGroup.mk (gO (Submodule.inclusion h.le_C a) * PO (p : AutPerm)⁻¹),
      ⟨⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩, rfl⟩⟩ = p :=
  monoProj_monoSubEquiv h ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩

theorem natCard_ker_monoProj [Finite Q] (h : MonoHyp D Q) :
    Nat.card (monoProj h).ker = Nat.card (D ⧸ ΩIn D) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (monoProj h).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (monoProj_surjective h)).toEquiv, natCard_monoSub] at h1
  have hQ : 0 < Nat.card Q := Nat.card_pos
  rw [mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left hQ h1).symm

end CFSG.Monster.B.TwoA
