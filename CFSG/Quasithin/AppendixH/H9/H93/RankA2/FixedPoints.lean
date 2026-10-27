module

public import CFSG.Quasithin.AppendixH.H9.H93.RankA2.Coordinates
public import CFSG.Quasithin.AppendixH.H9.H93.RankGeneric

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

namespace A2Coords

theorem mem_fixV_range_inf_iff {W : Type*} [CommGroup W] {d : ℕ}
    (ρ : Multiplicative (Fin d → ZMod 2) →* MulAut W) (L : Subgroup (MulAut W))
    (P : (Fin d → ZMod 2) → Prop)
    (hL : ∀ ε, ρ (Multiplicative.ofAdd ε) ∈ L ↔ P ε) (w : W) :
    w ∈ fixV (ρ.range ⊓ L) ↔ ∀ ε, P ε → ρ (Multiplicative.ofAdd ε) w = w := by
  constructor
  · intro h ε hε
    exact h _ (Subgroup.mem_inf.2 ⟨⟨Multiplicative.ofAdd ε, rfl⟩, (hL ε).2 hε⟩)
  · intro h g hg
    obtain ⟨⟨m, rfl⟩, hgL⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective m
    exact h ε ((hL ε).1 hgL)

variable {ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4)}

theorem apply_pairVec_eq_iff
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (ε a b : Fin 4 → ZMod 2) :
    ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec a b ↔ A2Fixes ε a b := by
  rw [hact, pairVec_inj]
  rfl

theorem card_fixers_pairVec
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (a b : Fin 4 → ZMod 2) :
    Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec a b} =
      Fintype.card {ε : Fin 4 → ZMod 2 // A2Fixes ε a b} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun ε => apply_pairVec_eq_iff hact ε a b)

theorem apply_pairVec_of_eps3_eq_one
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    {ε : Fin 4 → ZMod 2} (h3 : ε 3 = 1) (a b : Fin 4 → ZMod 2) :
    ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2vec ε b) (A2vec ε a) := by
  rw [hact, A2fst_of_eps3_eq_one ε h3, A2snd_of_eps3_eq_one ε h3]

theorem pairVec_mem_fixV_range_inf_iff
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (hL : ∀ ε : Fin 4 → ZMod 2, ρ (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0)
    (a b : Fin 4 → ZMod 2) :
    pairVec a b ∈ fixV (ρ.range ⊓ Lg 4) ↔ A2Fixed a ∧ A2Fixed b :=
  (mem_fixV_range_inf_iff ρ (Lg 4) (fun ε => ε 3 = 0) hL _).trans
    ((forall_congr' fun ε => imp_congr_right fun _ => apply_pairVec_eq_iff hact ε a b).trans
      (forall_A2Fixes_of_eps3_eq_zero_iff a b))

theorem pairVec_mem_fixV_range_iff
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (a b : Fin 4 → ZMod 2) :
    pairVec a b ∈ fixV ρ.range ↔ A2Fixed a ∧ a = b :=
  (mem_fixV_range ρ _).trans
    ((forall_congr' fun ε => apply_pairVec_eq_iff hact ε a b).trans (forall_A2Fixes_iff a b))

theorem pairVec_mem_fixV_zpowers_iff
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    {ε₁ : Fin 4 → ZMod 2} (h3 : ε₁ 3 = 1) (a b : Fin 4 → ZMod 2) :
    pairVec a b ∈ fixV (Subgroup.zpowers (ρ (Multiplicative.ofAdd ε₁))) ↔ A2vec ε₁ b = a :=
  (mem_fixV_zpowers _ _).trans
    ((apply_pairVec_eq_iff hact ε₁ a b).trans (A2Fixes_iff_of_eps3_eq_one ε₁ h3 a b))

theorem pairVec_mem_sup_iff
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (hL : ∀ ε : Fin 4 → ZMod 2, ρ (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0)
    {ε₁ : Fin 4 → ZMod 2} (h3 : ε₁ 3 = 1) (X Y : Fin 4 → ZMod 2) :
    pairVec X Y ∈ fixV (ρ.range ⊓ Lg 4) ⊔ fixV (Subgroup.zpowers (ρ (Multiplicative.ofAdd ε₁))) ↔
      A2Fixed (X + A2vec ε₁ Y) := by
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    obtain ⟨a, b, rfl⟩ := pairVec_surj y
    obtain ⟨c, d, rfl⟩ := pairVec_surj z
    obtain ⟨ha, hb⟩ := (pairVec_mem_fixV_range_inf_iff hact hL a b).1 hy
    have hc : A2vec ε₁ d = c := (pairVec_mem_fixV_zpowers_iff hact h3 c d).1 hz
    obtain ⟨rfl, rfl⟩ := pairVec_inj.1 ((pairVec_mul a b c d).symm.trans hyz)
    subst hc
    exact A2Fixed_add_A2vec_add ha hb d ε₁
  · intro hX
    refine ⟨pairVec (X + A2vec ε₁ Y) 0,
      (pairVec_mem_fixV_range_inf_iff hact hL _ _).2 ⟨hX, A2Fixed_zero⟩,
      pairVec (A2vec ε₁ Y) Y, (pairVec_mem_fixV_zpowers_iff hact h3 _ _).2 rfl, ?_⟩
    refine (pairVec_mul _ _ _ _).trans (pairVec_inj.2 ⟨?_, zero_add Y⟩)
    rw [add_assoc, A2_add_self, add_zero]

theorem gammaCheck_two_range_eq_sup
    (hinj : Function.Injective ρ)
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (hL : ∀ ε : Fin 4 → ZMod 2, ρ (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0)
    {ε₁ : Fin 4 → ZMod 2} (h3 : ε₁ 3 = 1) :
    E3.gammaCheck 2 ρ.range =
      fixV (ρ.range ⊓ Lg 4) ⊔ fixV (Subgroup.zpowers (ρ (Multiplicative.ofAdd ε₁))) := by
  refine (gammaCheck_two_range (W := PairN 4) ρ hinj).trans (le_antisymm ?_ ?_)
  · refine (Subgroup.closure_le _).2 ?_
    intro w hw
    obtain ⟨X, Y, rfl⟩ := pairVec_surj w
    exact (pairVec_mem_sup_iff hact hL h3 X Y).2
      (A2Fixed_of_four_le_card X Y (le_of_le_of_eq hw (card_fixers_pairVec hact X Y)) ε₁ h3)
  · refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨X, Y, rfl⟩ := pairVec_surj w
      obtain ⟨hX, hY⟩ := (pairVec_mem_fixV_range_inf_iff hact hL X Y).1 hw
      exact Subgroup.subset_closure
        (le_of_le_of_eq (four_le_card_A2Fixes_of_A2Fixed X Y hX hY)
          (card_fixers_pairVec hact X Y).symm)
    · obtain ⟨X, Y, rfl⟩ := pairVec_surj w
      have hX : A2vec ε₁ Y = X := (pairVec_mem_fixV_zpowers_iff hact h3 X Y).1 hw
      subst hX
      exact Subgroup.subset_closure
        (le_of_le_of_eq (four_le_card_A2Fixes_A2vec ε₁ h3 Y) (card_fixers_pairVec hact _ Y).symm)

theorem fixV_range_set_eq
    (hact : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A2fst ε a b) (A2snd ε a b))
    (hL : ∀ ε : Fin 4 → ZMod 2, ρ (Multiplicative.ofAdd ε) ∈ Lg 4 ↔ ε 3 = 0)
    {ε₁ : Fin 4 → ZMod 2} (h3 : ε₁ 3 = 1) :
    ((fixV ρ.range : Subgroup (PairN 4)) : Set (PairN 4)) =
      {x | ∃ w ∈ V1n 4 ⊓ fixV (ρ.range ⊓ Lg 4), x = w * ρ (Multiplicative.ofAdd ε₁) w} := by
  ext x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  constructor
  · intro h
    obtain ⟨ha, rfl⟩ := (pairVec_mem_fixV_range_iff hact a b).1 h
    refine ⟨pairVec a 0, Subgroup.mem_inf.2 ⟨pairVec_mem_V1n a,
      (pairVec_mem_fixV_range_inf_iff hact hL a 0).2 ⟨ha, A2Fixed_zero⟩⟩, ?_⟩
    rw [apply_pairVec_of_eps3_eq_one hact h3, A2vec_zero, A2vec_of_A2Fixed ε₁ a ha,
      pairVec_mul, add_zero, zero_add]
  · rintro ⟨w, hw, hx⟩
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨c, d, rfl⟩ := pairVec_surj w
    have hd : d = 0 := Multiplicative.ofAdd.injective (mem_V1n.1 hw1)
    subst hd
    obtain ⟨hc, -⟩ := (pairVec_mem_fixV_range_inf_iff hact hL c 0).1 hw2
    rw [apply_pairVec_of_eps3_eq_one hact h3, A2vec_zero, A2vec_of_A2Fixed ε₁ c hc,
      pairVec_mul, add_zero, zero_add] at hx
    rw [hx]
    exact (pairVec_mem_fixV_range_iff hact _ _).2 ⟨hc, rfl⟩

end A2Coords

end CFSG.ASVolI.ChH
