module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrB
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open Equiv

variable {Q : Type*} [Group Q]

noncomputable def piTwoEquiv {q₀ : Q} (hq₀ : q₀ ≠ 1) (hq : ∀ z : Q, z ≠ 1 → z = q₀) :
    (Q → AFive) ≃* AFive × AFive := by
  classical
  exact
  { toFun := fun g => (g 1, g q₀)
    invFun := fun p z => if z = 1 then p.1 else p.2
    left_inv := fun g => by
      funext z
      by_cases hz : z = 1
      · simp [hz]
      · simp [hq z hz, hq₀]
    right_inv := fun p => by simp [hq₀]
    map_mul' := fun _ _ => rfl }

theorem exists_ne_one_of_natCard_two [Finite Q] (hQ : Nat.card Q = 2) :
    ∃ q₀ : Q, q₀ ≠ 1 ∧ ∀ z : Q, z ≠ 1 → z = q₀ := by
  obtain ⟨q₀, hq₀, hu⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
  exact ⟨q₀, hq₀, fun z hz => hu z hz⟩

theorem wrAut_bijective [Finite Q] (hQ : Nat.card Q = 2) :
    Function.Bijective (wrAut (Q := Q)) := by
  obtain ⟨q₀, hq₀, hq⟩ := exists_ne_one_of_natCard_two hQ
  have : Finite (MulAut (Q → AFive)) :=
    Finite.of_injective (fun φ : MulAut (Q → AFive) => (φ : (Q → AFive) → Q → AFive))
      DFunLike.coe_injective
  refine wrAut_injective.bijective_of_nat_card_le ?_
  rw [card_wr hQ, Nat.card_congr (MulAut.congr (piTwoEquiv hq₀ hq)).toEquiv]
  exact card_mulAut_prod_le

section Internal

variable {P : Type*} [Group P] {Y₁ Y₂ : Subgroup P}

@[expose] noncomputable def aFivePairHom (e₁ : ↥Y₁ ≃* AFive) (e₂ : ↥Y₂ ≃* AFive)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) : AFive × AFive →* P :=
  MonoidHom.noncommCoprod (Y₁.subtype.comp e₁.symm.toMonoidHom)
    (Y₂.subtype.comp e₂.symm.toMonoidHom) fun a b => hcomm _ (e₁.symm a).2 _ (e₂.symm b).2

theorem aFivePairHom_apply (e₁ : ↥Y₁ ≃* AFive) (e₂ : ↥Y₂ ≃* AFive)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) (p : AFive × AFive) :
    aFivePairHom e₁ e₂ hcomm p = (e₁.symm p.1 : P) * (e₂.symm p.2 : P) := rfl

theorem aFivePairHom_injective (e₁ : ↥Y₁ ≃* AFive) (e₂ : ↥Y₂ ≃* AFive)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) (hinf : Y₁ ⊓ Y₂ = ⊥) :
    Function.Injective (aFivePairHom e₁ e₂ hcomm) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [aFivePairHom_apply] at h
  have h1 : (e₁.symm a : P) ∈ Y₁ ⊓ Y₂ :=
    ⟨(e₁.symm a).2, by rw [eq_inv_of_mul_eq_one_left h]; exact Y₂.inv_mem (e₂.symm b).2⟩
  rw [hinf, Subgroup.mem_bot] at h1
  have ha : e₁.symm a = 1 := Subtype.ext h1
  have hb : (e₂.symm b : P) = 1 := by rwa [h1, one_mul] at h
  rw [MulEquiv.symm_apply_eq, map_one] at ha
  rw [ha, show b = e₂ 1 from (MulEquiv.symm_apply_eq e₂).mp (Subtype.ext hb), map_one]
  rfl

theorem range_aFivePairHom (e₁ : ↥Y₁ ≃* AFive) (e₂ : ↥Y₂ ≃* AFive)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) :
    (aFivePairHom e₁ e₂ hcomm).range = Y₁ ⊔ Y₂ := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [aFivePairHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (e₁.symm p.1).2)
      (Subgroup.mem_sup_right (e₂.symm p.2).2)
  · refine sup_le (fun y hy => ⟨(e₁ ⟨y, hy⟩, 1), ?_⟩) (fun y hy => ⟨(1, e₂ ⟨y, hy⟩), ?_⟩)
    · rw [aFivePairHom_apply, MulEquiv.symm_apply_apply, map_one, Subgroup.coe_one, mul_one]
    · rw [aFivePairHom_apply, MulEquiv.symm_apply_apply, map_one, Subgroup.coe_one, one_mul]

end Internal

theorem nonempty_mulEquiv_wr {P : Type*} [Group P] [Finite P] {Y₁ Y₂ : Subgroup P}
    (e₁ : ↥Y₁ ≃* AFive) (e₂ : ↥Y₂ ≃* AFive) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hinf : Y₁ ⊓ Y₂ = ⊥) [(Y₁ ⊔ Y₂).Normal]
    (hC : Subgroup.centralizer ((Y₁ ⊔ Y₂ : Subgroup P) : Set P) = ⊥)
    (hcard : 28800 ≤ Nat.card P) [Finite Q] (hQ : Nat.card Q = 2) :
    Nonempty (P ≃* Perm (Fin 5) ≀ᵣ Q) := by
  obtain ⟨q₀, hq₀, hq⟩ := exists_ne_one_of_natCard_two hQ
  set c : P →* MulAut ↥(Y₁ ⊔ Y₂) := MulAut.conjNormal with hc
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer ((Y₁ ⊔ Y₂ : Subgroup P) : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := congrArg (fun φ : MulAut ↥(Y₁ ⊔ Y₂) => ((φ ⟨y, hy⟩ : ↥(Y₁ ⊔ Y₂)) : P)) hg
      simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hC, Subgroup.mem_bot] at hgC
    exact hgC
  set ι : AFive × AFive ≃* ↥(Y₁ ⊔ Y₂) := (MonoidHom.ofInjective
    (aFivePairHom_injective e₁ e₂ hcomm hinf)).trans
      (MulEquiv.subgroupCongr (range_aFivePairHom e₁ e₂ hcomm))
  set θ : MulAut ↥(Y₁ ⊔ Y₂) ≃* MulAut (Q → AFive) :=
    MulAut.congr (ι.symm.trans (piTwoEquiv hq₀ hq).symm)
  set ω : Perm (Fin 5) ≀ᵣ Q ≃* MulAut (Q → AFive) :=
    MulEquiv.ofBijective wrAut (wrAut_bijective hQ)
  set f : P →* Perm (Fin 5) ≀ᵣ Q := ω.symm.toMonoidHom.comp (θ.toMonoidHom.comp c)
  have hfinj : Function.Injective f := ω.symm.injective.comp (θ.injective.comp hcinj)
  have : Finite (Perm (Fin 5) ≀ᵣ Q) :=
    Nat.finite_of_card_ne_zero (by rw [card_wr hQ]; norm_num)
  exact ⟨MulEquiv.ofBijective f (hfinj.bijective_of_nat_card_le (by rw [card_wr hQ]; exact hcard))⟩

theorem nonempty_mulEquiv_symFiveWrTwo {P : Type*} [Group P] [Finite P] {Y₁ Y₂ : Subgroup P}
    (e₁ : ↥Y₁ ≃* AFive) (e₂ : ↥Y₂ ≃* AFive) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hinf : Y₁ ⊓ Y₂ = ⊥) [(Y₁ ⊔ Y₂).Normal]
    (hC : Subgroup.centralizer ((Y₁ ⊔ Y₂ : Subgroup P) : Set P) = ⊥)
    (hcard : 28800 ≤ Nat.card P) : Nonempty (P ≃* SymFiveWrTwo) :=
  nonempty_mulEquiv_wr e₁ e₂ hcomm hinf hC hcard natCard_qTwo

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
