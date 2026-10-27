module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.Quasithin

theorem card_evenWeight (m : ℕ) (hm : 0 < m) : Nat.card ↥(evenWeight m) = 2 ^ (m - 1) := by
  let f : (Fin m → ZMod 2) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i) (fun _ _ => Finset.sum_add_distrib)
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Pi.single ⟨0, hm⟩ c, ?_⟩
    simp [f]
  have hrange : f.range = ⊤ := AddMonoidHom.range_eq_top.2 hsurj
  have h1 := AddSubgroup.index_ker f
  rw [hrange] at h1
  have h2 := AddSubgroup.index_mul_card (H := f.ker)
  have hcard : Nat.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Nat.card_fun]
    simp
  have hidx : f.ker.index = 2 := by
    rw [h1]
    simp
  rw [hidx, hcard] at h2
  have hker : evenWeight m = f.ker := rfl
  rw [hker]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ] at h2
  simp only [Nat.add_sub_cancel]
  omega

theorem card_altHeart_seven : Nat.card (AltHeart 7) = 2 ^ 6 := by
  have hbot : constWeight 7 = ⊥ := constWeight_eq_bot_of_odd (by decide)
  have h2 : Nat.card (AltHeart 7) = (constWeight 7).index := rfl
  rw [h2, hbot, AddSubgroup.index_bot, card_evenWeight 7 (by norm_num)]

theorem card_constWeight_six : Nat.card (constWeight 6) = 2 := by
  have hsum : ∀ c : ZMod 2, ∑ _i : Fin 6, c = 0 := by decide
  have hmem : ∀ c : ZMod 2, (fun _ : Fin 6 => c) ∈ evenWeight 6 := fun c => by
    show ∑ _i : Fin 6, c = 0
    exact hsum c
  let e : ZMod 2 ≃ constWeight 6 :=
    { toFun := fun c => ⟨⟨fun _ => c, hmem c⟩, fun _ _ => rfl⟩
      invFun := fun x => (x.1 : Fin 6 → ZMod 2) 0
      left_inv := fun c => rfl
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact x.2 0 i }
  rw [← Nat.card_congr e]
  simp

theorem card_altHeart_six : Nat.card (AltHeart 6) = 2 ^ 4 := by
  have h1 : (constWeight 6).index * Nat.card (constWeight 6) = Nat.card ↥(evenWeight 6) :=
    AddSubgroup.index_mul_card (constWeight 6)
  rw [card_constWeight_six, card_evenWeight 6 (by norm_num)] at h1
  have h2 : Nat.card (AltHeart 6) = (constWeight 6).index := rfl
  rw [h2]
  omega

end CFSG.Quasithin.H23P4
