module

public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint.NativeSporadic

@[expose] def OverSylow2M24Cov : Prop :=
  ∀ X S : Subgroup (Carrier .M24), IsPGroup 2 S → Nat.card S = 1024 → S ≤ X →
    5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → X = ⊤

@[expose] def OverSylow2HeCov : Prop :=
  ∀ X S : Subgroup (Carrier .He), IsPGroup 2 S → Nat.card S = 1024 → S ≤ X →
    5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → X = ⊤

theorem false_of_overgroup_transport_cv {Q C : Type} [Group Q] [Group C] (e : Q ≃* C) (N : ℕ) (hN : 9 ∣ N)
    (hC : Nat.card C = N)
    (hov : ∀ X S : Subgroup C, IsPGroup 2 S → Nat.card S = 1024 → S ≤ X →
      5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → X = ⊤)
    (P S : Subgroup Q) (hS : IsPGroup 2 S) (hS1024 : Nat.card S = 1024) (hSP : S ≤ P)
    (h5 : 5 ∣ Nat.card P) (h9 : ¬ 9 ∣ Nat.card P) : False := by
  let f : Q →* C := e.toMonoidHom
  have hf : Function.Injective f := e.injective
  have hcardP' : Nat.card (P.map f) = Nat.card P := Subgroup.card_map_of_injective hf
  have hcardS' : Nat.card (S.map f) = 1024 := by
    rw [Subgroup.card_map_of_injective hf]
    exact hS1024
  have hS'2 : IsPGroup 2 (S.map f) := IsPGroup.of_card (n := 10) (by rw [hcardS']; norm_num)
  have hSP' : S.map f ≤ P.map f := Subgroup.map_mono hSP
  have htop : P.map f = ⊤ :=
    hov (P.map f) (S.map f) hS'2 hcardS' hSP' (by rw [hcardP']; exact h5)
      (by rw [hcardP']; exact h9)
  apply h9
  rw [← hcardP', htop, Subgroup.card_top, hC]
  exact hN

theorem false_of_M24_cover_cv (hov : OverSylow2M24Cov)
    {Q : Type} [Group Q] (hQ : Nonempty (Q ≃* Carrier .M24))
    (P S : Subgroup Q) (hS : IsPGroup 2 S) (hS1024 : Nat.card S = 1024) (hSP : S ≤ P)
    (h5 : 5 ∣ Nat.card P) (h9 : ¬ 9 ∣ Nat.card P) : False := by
  obtain ⟨e⟩ := hQ
  have hcard : Nat.card (Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  exact false_of_overgroup_transport_cv e 244823040 (by norm_num) hcard hov P S hS hS1024 hSP h5 h9

theorem false_of_He_cover_cv (hov : OverSylow2HeCov)
    {Q : Type} [Group Q] (hQ : Nonempty (Q ≃* Carrier .He))
    (P S : Subgroup Q) (hS : IsPGroup 2 S) (hS1024 : Nat.card S = 1024) (hSP : S ≤ P)
    (h5 : 5 ∣ Nat.card P) (h9 : ¬ 9 ∣ Nat.card P) : False := by
  obtain ⟨e⟩ := hQ
  have hcard : Nat.card (Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  exact false_of_overgroup_transport_cv e 4030387200 (by norm_num) hcard hov P S hS hS1024 hSP h5 h9

end CFSG.Quasithin.H13
