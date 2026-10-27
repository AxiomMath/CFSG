module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z6b
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Idx2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24L3

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped Pointwise commutatorElement

theorem rho6_gens_check :
    ∀ i : Fin 5, indTab actSetSet L6m (gens6T.getD i []) = M6tab.getD i [] := by
  decide +kernel

theorem gens6T_getD : ∀ t ∈ gens6T, ∃ i : Fin 5, t = gens6T.getD i [] := by decide

theorem rho6_le_range :
    rho6.range ≤ (Seven.rho Seven.lab8).range := by
  refine range_le_of_gens {g | g ∈ gens6} rho6 _ ?_
  intro g hg
  have ht : tab 24 g ∈ gens6T := by rw [← gens6_tab]; exact List.mem_map_of_mem hg
  obtain ⟨i, hi⟩ := gens6T_getD _ ht
  refine ⟨M6sl i, ?_⟩
  symm
  refine listHom_eq_of_tab actSetSet hact_setset Z6 L6m L6m_nodup Z6_inv ⟨g, _⟩ _ ?_
  show indTab actSetSet L6m (tab 24 g) = tab 7 (Seven.rho Seven.lab8 (M6sl i))
  rw [hi, tab_rho_M6, rho6_gens_check]

theorem rho6_card [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card rho6.range = 168 ∧ Nat.card rho6.ker = 2 * 2 ^ 6 := by
  have hle : Nat.card rho6.range ≤ 168 :=
    (Subgroup.card_le_of_le rho6_le_range).trans card_rho8_range.le
  have h1 : Nat.card rho6.range = 168 :=
    Nat.le_antisymm hle (Nat.le_of_dvd Nat.card_pos rho6_dvd)
  refine ⟨h1, ?_⟩
  have h := card_ker_mul rho6
  rw [Z6_eq.1, h1] at h
  omega

theorem isExt_Z6 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z6) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have := Seven.slThree_isSimple
  let f : ↥Z6 →* Equiv.Perm (Fin 7) := rho6
  obtain ⟨e⟩ := sl3_quotient_of_range f rho6_le_range rho6_card.1.ge
  let σ : ↥Z6 →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' f.ker)
  have hσs : Function.Surjective σ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hσk : σ.ker = rho6.ker := by
    ext z
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' f.ker z) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  refine isExt_e2_of_index_two m24_S_isPGroup hB hY Seven.slThree_nonabelian σ hσs
    V6_le_Z6 ?_ Z6_normalizes_V6 V6_comm_all V6_sq card_V6 ?_ y6_mem (m := 7) (by norm_num) y6_pow
    V6_comm Z6_not_perfect (fun V W _ _ e h => IsPSL.of_mulEquiv e h)
    (Seven.isPSL_three_two (MulEquiv.refl _))
  · rw [hσk]
    exact fun z hz => listHom_eq_one_of_fix Z6 L6m L6m_nodup Z6_inv z (V6_fix z.1 hz)
  · rw [hσk]
    exact rho6_card.2

end CFSG.Quasithin.A312M24
