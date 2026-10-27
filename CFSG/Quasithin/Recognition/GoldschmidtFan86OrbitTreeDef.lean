module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeBasic

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V]

@[expose] def orbitGraph (Γ : SimpleGraph V) (A : Set V) : SimpleGraph ↥A where
  Adj u v := u.1 ≠ v.1 ∧ ∃ w, Γ.Adj u.1 w ∧ Γ.Adj v.1 w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ hw => ⟨hw.2, hw.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[expose] def OrbitLoc (Γ : SimpleGraph V) (H : Subgroup G) (A : Set V) : Prop :=
  ∀ u ∈ A, ∀ v w, Γ.Adj u v → Γ.Adj u w → ∃ h ∈ H, h • u = u ∧ h • v = w

@[expose] def OrbitPartner (Γ : SimpleGraph V) (A : Set V) : Prop :=
  ∀ u ∈ A, ∀ w, Γ.Adj u w → ∃! u', u' ∈ A ∧ u' ≠ u ∧ Γ.Adj u' w

@[expose] def OrbitConn (Γ : SimpleGraph V) (A : Set V) : Prop :=
  ∀ S : Set V, S ⊆ A → S.Nonempty →
    (∀ u ∈ S, ∀ u' ∈ A, (u' ≠ u ∧ ∃ w, Γ.Adj u' w ∧ Γ.Adj u w) → u' ∈ S) → S = A

variable {Γ : SimpleGraph V} {A : Set V}

theorem common_nbr_unique (hT : Γ.IsTree) {u u' w₁ w₂ : V} (hne : u ≠ u') (h₁ : Γ.Adj u w₁)
    (h₁' : Γ.Adj u' w₁) (h₂ : Γ.Adj u w₂) (h₂' : Γ.Adj u' w₂) : w₁ = w₂ := by
  by_contra hne'
  let P : Arc Γ 3 :=
    { vert := fun i => match i with | 0 => u | 1 => w₁ | 2 => u' | _ => w₂
      adj := fun i hi => by
        rcases i with _ | _ | _ | i
        · exact h₁
        · exact h₁'.symm
        · exact h₂'
        · omega
      nb := fun i hi => by
        rcases i with _ | _ | i
        · exact hne
        · exact hne'
        · omega }
  have h3 := Arc.dist_eq hT P 3 le_rfl
  have h1 : Γ.dist u w₂ = 1 := dist_eq_one_iff_adj.mpr h₂
  have h3' : Γ.dist u w₂ = 3 := h3
  omega

namespace OrbitPartner

noncomputable def partner (hP : OrbitPartner Γ A) {u : V} (hu : u ∈ A) {w : V}
    (hw : Γ.Adj u w) : V :=
  (hP u hu w hw).exists.choose

theorem partner_spec (hP : OrbitPartner Γ A) {u : V} (hu : u ∈ A) {w : V} (hw : Γ.Adj u w) :
    partner hP hu hw ∈ A ∧ partner hP hu hw ≠ u ∧ Γ.Adj (partner hP hu hw) w :=
  (hP u hu w hw).exists.choose_spec

theorem eq_partner (hP : OrbitPartner Γ A) {u : V} (hu : u ∈ A) {w : V} (hw : Γ.Adj u w) {u' : V}
    (h : u' ∈ A ∧ u' ≠ u ∧ Γ.Adj u' w) : u' = partner hP hu hw :=
  (hP u hu w hw).unique h (partner_spec hP hu hw)

end OrbitPartner

theorem card_neighborSet_orbitGraph (hT : Γ.IsTree) (hP : OrbitPartner Γ A) (u : ↥A) :
    Nat.card ((orbitGraph Γ A).neighborSet u) = Nat.card (Γ.neighborSet u.1) := by
  let f : Γ.neighborSet u.1 → (orbitGraph Γ A).neighborSet u := fun w =>
    ⟨⟨OrbitPartner.partner hP u.2 w.2, (OrbitPartner.partner_spec hP u.2 w.2).1⟩,
      (OrbitPartner.partner_spec hP u.2 w.2).2.1.symm, w.1, w.2,
      (OrbitPartner.partner_spec hP u.2 w.2).2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro w₁ w₂ h
      have hp := congrArg (fun x : (orbitGraph Γ A).neighborSet u => x.1.1) h
      simp only [f] at hp
      apply Subtype.ext
      refine common_nbr_unique hT (u := u.1) (u' := OrbitPartner.partner hP u.2 w₁.2)
        (OrbitPartner.partner_spec hP u.2 w₁.2).2.1.symm w₁.2
        (OrbitPartner.partner_spec hP u.2 w₁.2).2.2 w₂.2 ?_
      rw [hp]
      exact (OrbitPartner.partner_spec hP u.2 w₂.2).2.2
    · rintro ⟨v, hne, w, hw, hvw⟩
      refine ⟨⟨w, hw⟩, Subtype.ext (Subtype.ext ?_)⟩
      exact (OrbitPartner.eq_partner hP u.2 hw ⟨v.2, hne.symm, hvw⟩).symm
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end CFSG.Quasithin.Fan86
