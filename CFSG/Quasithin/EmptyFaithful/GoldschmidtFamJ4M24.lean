module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Main
public import CFSG.Quasithin.Background.A312SporGen

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.Quasithin.A312M24

theorem forall_lFamily_of_members {Γ : Type} [Group Γ] [Finite Γ] (P : Subgroup Γ → Prop)
    (hq : CFSG.IsQuasisimple Γ) {S : Subgroup Γ} {L : Array ℕ} {Y : ℕ → Subgroup Γ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hmem : ∀ j < L.size, ∀ B ∈ lFamily S, B ⊔ S = Y j → P B) :
    ∀ B ∈ lFamily S, B ≠ ⊤ → P B := by
  intro B hB hBtop
  obtain ⟨j, hj, hjZ⟩ := hall (B ⊔ S) le_sup_right
  by_cases hjL : j < L.size
  · rw [memberOrTop, ite_eq_left hjL] at hjZ
    exact hmem j hjL B hB hjZ
  · exfalso
    rw [memberOrTop, ite_eq_right hjL] at hjZ
    have hB' : B ∈ cComp (B ⊔ S) := hB
    rw [hjZ] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')

theorem a312C14_of_lFamily_S [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (hq : CFSG.IsQuasisimple G24) :
    ∀ B ∈ lFamily m24CtxE.S, B ≠ ⊤ → A312C14 B ⊤ := by
  refine forall_lFamily_of_members (fun B => A312C14 B ⊤) hq (Y := m24CtxE.Y) (L := memIdx) m24_all
    fun j hj B hB hY => ?_
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
  · exact ⟨Or.inl (isExt_Z1 hB (hY.trans Z1_eq_Y1.2.symm)), isSporadic_top⟩
  · exact (false_Z2 hB (hY.trans Z2_eq_Y2.2.symm)).elim
  · exact ⟨Or.inr (Or.inr (Or.inr (isExt_Z3 hB (hY.trans Z3_eq_Y3.2.symm)))), isSporadic_top⟩
  · rcases hZ46 4 (Or.inl rfl) with h | h
    · exact ⟨Or.inr (Or.inr (Or.inl (isExt_Z4 hB (hY.trans h)))), isSporadic_top⟩
    · exact ⟨Or.inr (Or.inl (isExt_Z6 hB (hY.trans h))), isSporadic_top⟩
  · exact (hd 10 2 (by decide)).elim
  · rcases hZ46 6 (Or.inr rfl) with h | h
    · exact ⟨Or.inr (Or.inr (Or.inl (isExt_Z4 hB (hY.trans h)))), isSporadic_top⟩
    · exact ⟨Or.inr (Or.inl (isExt_Z6 hB (hY.trans h))), isSporadic_top⟩
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 2 (by decide)).elim
  · exact (hd 10 1 (by decide)).elim
  · exact (hd 10 2 (by decide)).elim

theorem a312C14_of_lFamily [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (hq : CFSG.IsQuasisimple G24) {T : Subgroup G24}
    (hT : IsSylowTwoOf T ⊤) {B : Subgroup G24} (hB : B ∈ lFamily T) (hBtop : B ≠ ⊤) :
    A312C14 B ⊤ := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf m24_S_sylow' hT
  let e : G24 ≃* G24 := (MulAut.conj g).symm
  have hT' : T.map e.toMonoidHom = m24CtxE.S := by
    rw [← hg]
    exact map_map_symm (MulAut.conj g) m24CtxE.S
  have hB' : B.map e.toMonoidHom ∈ lFamily m24CtxE.S := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup, hT'] at h1
    exact h1
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  exact A312C14.of_equiv (mapEquiv e B) (topMapEquiv e) (a312C14_of_lFamily_S hq _ hB' hne)

end CFSG.Quasithin.J4Fam
