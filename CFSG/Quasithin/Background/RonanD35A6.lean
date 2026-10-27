module

public import CFSG.Quasithin.Background.RonanD35
public import CFSG.Quasithin.Background.G64SymSec
public import CFSG.Quasithin.EmptyFaithful.F918C10

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin

@[expose] def a6g₁ : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6g₂ : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6K : Finset ↥(alternatingGroup (Fin 6)) := {1, a6g₁, a6g₂, a6g₁ * a6g₂}

theorem a6K_mul : ∀ a ∈ a6K, ∀ b ∈ a6K, a * b ∈ a6K := by decide +kernel

theorem a6K_comm : ∀ a ∈ a6K, ∀ b ∈ a6K, a * b = b * a := by decide +kernel

theorem a6K_sq : ∀ a ∈ a6K, a * a = 1 := by decide +kernel

theorem a6K_card : a6K.card = 4 := by decide +kernel

@[expose] def a6A₀ : Subgroup ↥(alternatingGroup (Fin 6)) where
  carrier := ↑a6K
  one_mem' := show (1 : ↥(alternatingGroup (Fin 6))) ∈ a6K by decide +kernel
  mul_mem' := fun {a b} ha hb => a6K_mul a ha b hb
  inv_mem' := fun {a} ha => by
    rw [inv_eq_of_mul_eq_one_right (a6K_sq a ha)]
    exact ha

theorem a6A₀_comm : ∀ a ∈ a6A₀, ∀ b ∈ a6A₀, a * b = b * a :=
  fun a ha b hb => a6K_comm a ha b hb

theorem a6A₀_sq : ∀ a ∈ a6A₀, a * a = 1 := fun a ha => a6K_sq a ha

theorem a6A₀_card : Nat.card ↥a6A₀ = 4 := by
  rw [← a6K_card, ← Nat.card_eq_finsetCard]
  rfl

theorem a6A₀_ne_bot : a6A₀ ≠ ⊥ := by
  intro h
  have h1 : a6g₁ ∈ a6A₀ := show a6g₁ ∈ a6K by decide +kernel
  rw [h, Subgroup.mem_bot] at h1
  exact absurd h1 (by decide +kernel)

theorem a6A₀_le {H : Subgroup ↥(alternatingGroup (Fin 6))} (h₁ : a6g₁ ∈ H) (h₂ : a6g₂ ∈ H) :
    a6A₀ ≤ H := by
  intro a ha
  have ha' : a ∈ a6K := ha
  simp only [a6K, Finset.mem_insert, Finset.mem_singleton] at ha'
  rcases ha' with rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact h₁
  · exact h₂
  · exact H.mul_mem h₁ h₂

abbrev a6Q : Type :=
  ↥(G6.coreMod 6) ⧸ (Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)

theorem a6Q_card : Nat.card a6Q = 16 := card_D6

theorem a6_sum_single : ∀ i j : Fin 6,
    ∑ k, (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin 6 → ZMod 2) k = 0 := by
  decide +kernel

@[expose] def a6ev (i j : Fin 6) : ↥(G6.coreMod 6) :=
  ⟨Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1), by
    rw [G6.mem_coreMod]
    exact a6_sum_single i j⟩

@[expose] def a6E (i j : Fin 6) : a6Q := QuotientGroup.mk (a6ev i j)

@[expose] def a6P : Subgroup a6Q := Subgroup.closure {a6E 0 1, a6E 2 3}

theorem a6_allOnes_mem : G6.allOnes 6 ∈ G6.coreMod 6 := by
  rw [G6.mem_coreMod, Fin.sum_univ_six]
  simp only [G6.allOnes, toAdd_ofAdd]
  decide

theorem a6_allOnes_sq : G6.allOnes 6 ^ 2 = 1 := by decide +kernel

theorem a6_mk_eq_iff {x y : ↥(G6.coreMod 6)} :
    (QuotientGroup.mk x : a6Q) = QuotientGroup.mk y ↔
      (x : G6.PermMod 6)⁻¹ * y = 1 ∨ (x : G6.PermMod 6)⁻¹ * y = G6.allOnes 6 := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  change (x : G6.PermMod 6)⁻¹ * y ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 ↔ _
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨h, -⟩
    exact G64.eq_one_or_eq_of_mem_zpowers' a6_allOnes_sq h
  · rintro (h | h) <;> rw [h]
    · exact ⟨one_mem _, one_mem _⟩
    · exact ⟨Subgroup.mem_zpowers _, a6_allOnes_mem⟩

@[expose] def a6r : Fin 4 → ↥(G6.coreMod 6) := ![1, a6ev 0 1, a6ev 2 3, a6ev 0 1 * a6ev 2 3]

theorem a6r_inj : ∀ i j : Fin 4,
    ((a6r i : G6.PermMod 6)⁻¹ * a6r j = 1 ∨ (a6r i : G6.PermMod 6)⁻¹ * a6r j = G6.allOnes 6) →
      i = j := by
  decide +kernel

theorem a6r_mem (i : Fin 4) : (QuotientGroup.mk (a6r i) : a6Q) ∈ a6P := by
  have h01 : a6E 0 1 ∈ a6P := Subgroup.subset_closure (Set.mem_insert _ _)
  have h23 : a6E 2 3 ∈ a6P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  fin_cases i
  · exact a6P.one_mem
  · exact h01
  · exact h23
  · exact a6P.mul_mem h01 h23

theorem a6_four_le_card_P : 4 ≤ Nat.card ↥a6P := by
  haveI : Finite a6Q := Nat.finite_of_card_ne_zero (by rw [a6Q_card]; norm_num)
  have hf : Function.Injective
      (fun i : Fin 4 => (⟨QuotientGroup.mk (a6r i), a6r_mem i⟩ : ↥a6P)) := by
    intro i j hij
    exact a6r_inj i j (a6_mk_eq_iff.mp (congrArg Subtype.val hij))
  have h := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_fin] at h

theorem a6_index_le : a6P.index ≤ 4 := by
  have h1 : Nat.card ↥a6P * a6P.index = 16 := (Subgroup.card_mul_index a6P).trans a6Q_card
  have h2 : 4 * a6P.index ≤ 4 * 4 := by
    calc 4 * a6P.index ≤ Nat.card ↥a6P * a6P.index := Nat.mul_le_mul_right _ a6_four_le_card_P
      _ = 4 * 4 := h1
  omega

section Lift

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V Z : Subgroup W}
  {π : ↥(alternatingGroup (Fin 6)) →* ↥L}

theorem a6_exists_comm (β : ↥V →* a6Q) (hβs : Function.Surjective β)
    (hβe : ∀ (γ : ↥(alternatingGroup (Fin 6))) (u : ↥V) (m : ↥(G6.coreMod 6))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V)
      (hm : G6.permAct 6 (γ : Equiv.Perm (Fin 6)) m ∈ G6.coreMod 6),
      β u = QuotientGroup.mk m →
        β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          QuotientGroup.mk ⟨G6.permAct 6 (γ : Equiv.Perm (Fin 6)) m, hm⟩)
    {g : ↥(alternatingGroup (Fin 6))} (haV : ∀ v ∈ V, ((π g : ↥L) : MulAut W) v ∈ V)
    (m q : ↥(G6.coreMod 6))
    (h : (G6.permAct 6 (g : Equiv.Perm (Fin 6)) m * (m : G6.PermMod 6)⁻¹)⁻¹ * q = 1 ∨
      (G6.permAct 6 (g : Equiv.Perm (Fin 6)) m * (m : G6.PermMod 6)⁻¹)⁻¹ * q = G6.allOnes 6) :
    ∃ u : ↥V, β ⟨((π g : ↥L) : MulAut W) u, haV u u.2⟩ * (β u)⁻¹ = QuotientGroup.mk q := by
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
  refine ⟨u, ?_⟩
  rw [hβe g u m (haV u u.2) (G6.permAct_mem_coreMod (g : Equiv.Perm (Fin 6)) m.2) hu, hu,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  exact a6_mk_eq_iff.mpr h

theorem a6_mem_fixSub (hW : ∀ w : W, w * w = 1) (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) (β : ↥V →* a6Q) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : ↥(alternatingGroup (Fin 6))) (u : ↥V) (m : ↥(G6.coreMod 6))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V)
      (hm : G6.permAct 6 (γ : Equiv.Perm (Fin 6)) m ∈ G6.coreMod 6),
      β u = QuotientGroup.mk m →
        β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          QuotientGroup.mk ⟨G6.permAct 6 (γ : Equiv.Perm (Fin 6)) m, hm⟩)
    {g : ↥(alternatingGroup (Fin 6))} (hg : g * g = 1) (m₁ m₂ : ↥(G6.coreMod 6))
    (h₁ : (G6.permAct 6 (g : Equiv.Perm (Fin 6)) m₁ * (m₁ : G6.PermMod 6)⁻¹)⁻¹ * a6ev 0 1 = 1 ∨
      (G6.permAct 6 (g : Equiv.Perm (Fin 6)) m₁ * (m₁ : G6.PermMod 6)⁻¹)⁻¹ * a6ev 0 1 =
        G6.allOnes 6)
    (h₂ : (G6.permAct 6 (g : Equiv.Perm (Fin 6)) m₂ * (m₂ : G6.PermMod 6)⁻¹)⁻¹ * a6ev 2 3 = 1 ∨
      (G6.permAct 6 (g : Equiv.Perm (Fin 6)) m₂ * (m₂ : G6.PermMod 6)⁻¹)⁻¹ * a6ev 2 3 =
        G6.allOnes 6) :
    g ∈ fixSub π {w | ∃ hw : w ∈ V, β ⟨w, hw⟩ ∈ a6P} := by
  rw [mem_fixSub]
  rintro p ⟨hp, hpP⟩
  have ha2 : ((π g : ↥L) : MulAut W) * ((π g : ↥L) : MulAut W) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hg, map_one, Subgroup.coe_one]
  have haV : ∀ v ∈ V, ((π g : ↥L) : MulAut W) v ∈ V := fun v hv => ((hLs (π g).2) v).2 hv
  refine apply_eq_of_lift_closure (p := ⟨p, hp⟩) (S := {a6E 0 1, a6E 2 3}) hW ha2 (hZ _ (π g).2)
    haV β hβk ?_ hpP
  rintro q (rfl | rfl)
  · exact a6_exists_comm β hβs hβe haV m₁ _ h₁
  · exact a6_exists_comm β hβs hβe haV m₂ _ h₂

end Lift

theorem isFFModule_of_altDn6 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} {V Z : Subgroup W} (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) {π : ↥(alternatingGroup (Fin 6)) →* ↥L}
    (hπ : (FFModel.altDn 6).RealizesVia L V Z π) : IsFFModule (autSub L V) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := id hπ
  have h₁ := a6_mem_fixSub hW hLs hZ β hβs hβk hβe (g := a6g₁) (by decide +kernel)
    (a6ev 0 4) (a6ev 2 4) (by decide +kernel) (by decide +kernel)
  have h₂ := a6_mem_fixSub hW hLs hZ β hβs hβk hβe (g := a6g₂) (by decide +kernel)
    (a6ev 0 2) (a6ev 0 4) (by decide +kernel) (by decide +kernel)
  refine isFFModule_of_realizesVia (G64.altDn_faithful (n := 6) (by norm_num)) hLs hπ β hβs a6A₀
    a6A₀_comm a6A₀_sq a6A₀_ne_bot a6P (a6_index_le.trans a6A₀_card.ge) ?_
  intro v hv a ha
  exact mem_fixSub.mp (a6A₀_le h₁ h₂ ha) v ⟨v.2, hv⟩

end CFSG.Quasithin.RonanD35
