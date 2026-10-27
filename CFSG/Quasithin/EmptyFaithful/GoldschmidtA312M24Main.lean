module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1d
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z3c
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z4c
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z6c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem isSporadic_top : IsSporadic .M24 ↥(⊤ : Subgroup G24) := ⟨Subgroup.topEquiv⟩

theorem case_of_c14 {B L : Subgroup G24} (h : A312C14 B L) : A312Case B L :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem false_of_card_pq [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {j : ℕ} (hj : j < 13) {B : Subgroup G24}
    (hB : B ∈ lFamily m24CtxE.S) (hY : B ⊔ m24CtxE.S = m24CtxE.Y j) {a b : ℕ}
    (h : memIdx[j]! * 2 ^ 10 = 2 ^ a * 3 ^ b) : False :=
  A312S.not_isSolvable_sup hB (hY ▸ A312S.isSolvable_of_card_pq Nat.prime_two Nat.prime_three
    (by norm_num) ((m24_card_Y j (by simpa [memIdx] using hj)).trans h))

theorem a312For_M24 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (hq : CFSG.IsQuasisimple G24) : A312For G24 := by
  refine A312S.a312For_of_members hq m24_S_sylow' m24_all fun j hj B hB hY => ?_
  have hj13 : j < 13 := by simpa [memIdx] using hj
  have hd : ∀ a b : ℕ, memIdx[j]! * 2 ^ 10 = 2 ^ a * 3 ^ b → False := fun a b h =>
    false_of_card_pq hj13 hB hY h
  have hZ46 : ∀ i, i = 4 ∨ i = 6 → m24CtxE.Y i = Z4 ∨ m24CtxE.Y i = Z6 := by
    obtain ⟨-, a, ha, hZa⟩ := Z4_eq
    obtain ⟨-, b, hb, hZb⟩ := Z6_eq
    have hab : a ≠ b := fun h => Z4_ne_Z6 (hZa.trans (h ▸ hZb.symm))
    intro i hi
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hi with rfl | rfl <;>
      first
        | exact absurd rfl hab
        | with_reducible exact Or.inl hZa.symm
        | with_reducible exact Or.inr hZb.symm
  interval_cases j
  · exact (hd 10 0 (by decide)).elim
  · exact case_of_c14 ⟨Or.inl (isExt_Z1 hB (hY.trans Z1_eq_Y1.2.symm)), isSporadic_top⟩
  · exact (false_Z2 hB (hY.trans Z2_eq_Y2.2.symm)).elim
  · exact case_of_c14 ⟨Or.inr (Or.inr (Or.inr (isExt_Z3 hB (hY.trans Z3_eq_Y3.2.symm)))),
      isSporadic_top⟩
  · rcases hZ46 4 (Or.inl rfl) with h | h
    · exact case_of_c14 ⟨Or.inr (Or.inr (Or.inl (isExt_Z4 hB (hY.trans h)))), isSporadic_top⟩
    · exact case_of_c14 ⟨Or.inr (Or.inl (isExt_Z6 hB (hY.trans h))), isSporadic_top⟩
  · exact (hd 10 2 (by decide)).elim
  · rcases hZ46 6 (Or.inr rfl) with h | h
    · exact case_of_c14 ⟨Or.inr (Or.inr (Or.inl (isExt_Z4 hB (hY.trans h)))), isSporadic_top⟩
    · exact case_of_c14 ⟨Or.inr (Or.inl (isExt_Z6 hB (hY.trans h))), isSporadic_top⟩
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 2 (by decide)).elim
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 2 (by decide)).elim

theorem famM24_holds [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    FamM24 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  let e' : X ≃* G24 := e
  exact A312For.of_mulEquiv e' (a312For_M24 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

end CFSG.Quasithin.A312M24
