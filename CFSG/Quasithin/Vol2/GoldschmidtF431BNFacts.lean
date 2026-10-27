module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNPoly
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Ctx

public section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.F45

section Main

variable {X : Type} [Group X] [Finite X] {n : ℕ} (R : RankTwoSystem X n)

theorem xdatum_of_labelling (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D] (hfin : Finite D)
    (hn : 3 ≤ n) (e : X ≃* D) (A : LieAmalgamExt D) (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (b : Bool)
    (h1 : A.P1 = (P R b).map e.toMonoidHom) (h2 : A.P2 = (P R (!b)).map e.toMonoidHom) :
    XDatum (A.setting hfin n hn) (phiG0 A hfin n hn (innHom A hgen e.symm)) (Γ R) (v R b)
      (v R (!b)) := by
  have hmap : ∀ (c : Bool),
      ((P R c).map e.toMonoidHom).map e.symm.toMonoidHom = P R c := by
    intro c
    rw [Subgroup.map_map]
    ext x
    simp
  have hP1 : A.P1.map e.symm.toMonoidHom = Subgroup.normalizer (Q R b : Set X) := by
    rw [h1, hmap, normalizer_Q R hU]
  have hP2 : A.P2.map e.symm.toMonoidHom = Subgroup.normalizer (Q R (!b) : Set X) := by
    rw [h2, hmap, normalizer_Q R hU]
  have hc1 : pCoreOf 2 (Subgroup.normalizer (Q R b : Set X)) = Q R b := by
    rw [normalizer_Q R hU]
    rfl
  have hc2 : pCoreOf 2 (Subgroup.normalizer (Q R (!b) : Set X)) = Q R (!b) := by
    rw [normalizer_Q R hU]
    rfl
  have s1 : ∀ y : X, y • v R b = v R b ↔ y ∈ Subgroup.normalizer (Q R b : Set X) := by
    intro y
    rw [normalizer_Q R hU]
    cases b
    · exact (stab_v R).2 y
    · exact (stab_v R).1 y
  have s2 : ∀ y : X, y • v R (!b) = v R (!b) ↔ y ∈ Subgroup.normalizer (Q R (!b) : Set X) := by
    intro y
    rw [normalizer_Q R hU]
    cases b
    · exact (stab_v R).1 y
    · exact (stab_v R).2 y
  have hdisj : ∀ y z : X, y • v R b ≠ z • v R (!b) := by
    intro y z
    cases b
    · exact fun h => disj R z y h.symm
    · exact disj R y z
  have hno1 : ∀ y z : X, ¬ (Γ R).Adj (y • v R b) (z • v R b) := by
    cases b
    · exact noadj_false R
    · exact noadj_true R
  have hno2 : ∀ y z : X, ¬ (Γ R).Adj (y • v R (!b)) (z • v R (!b)) := by
    cases b
    · exact noadj_true R
    · exact noadj_false R
  have hadj : (Γ R).Adj (v R b) (v R (!b)) := by
    cases b
    · exact (adj_v R).symm
    · exact adj_v R
  exact xdatum_of_inn A hfin n hn e.symm hgen hcen hP1 hP2 hc1 hc2 (Γ R) (v R b) (v R (!b))
    s1 s2 hdisj hno1 hno2 hadj

theorem xdatum_aux (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D] (hfin : Finite D)
    (hn : 3 ≤ n) (e : X ≃* D) (A : LieAmalgamExt D) (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (b : Bool)
    (h1 : A.P1 = (P R b).map e.toMonoidHom) (h2 : A.P2 = (P R (!b)).map e.toMonoidHom) :
    (A.setting hfin n hn).Facts45L :=
  facts45L_of_model (xdatum_of_labelling R hU hfin hn e A hcen hgen b h1 h2) (isGenPolygon R)
    (three_le_card_neighborSet R _) (three_le_card_neighborSet R _) _ _ rfl rfl
    (modelBase R hU b) (modelBase R hU (!b))

omit [Finite X] in
include R in
theorem center_eq_bot_of_rankTwo [IsSimpleGroup X] {D : Type} [Group D] (e : X ≃* D) :
    Subgroup.center D = ⊥ := by
  have hX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := not_comm R
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  refine (Subgroup.eq_bot_iff_forall _).2 fun d hd => ?_
  have hc : e.symm d ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := Subgroup.mem_center_iff.mp hd (e x)
    apply e.injective
    simpa using this
  rw [hX] at hc
  have := Subgroup.mem_bot.mp hc
  simpa using congrArg e this

theorem exists_xdatum [IsSimpleGroup X] (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D]
    (hfin : Finite D) (hn : 3 ≤ n) (e : X ≃* D) (A : LieAmalgamExt D) :
    ∃ (b : Bool) (e' : X ≃* D) (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K),
      XDatum (A.setting hfin n hn) (phiG0 A hfin n hn (innHom A hgen e'.symm)) (Γ R) (v R b)
        (v R (!b)) := by
  have hcen := center_eq_bot_of_rankTwo R e
  have hgen := range_conj_le_of_rankTwo R hU e A
  obtain ⟨e', -, hP | hP⟩ := exists_iso_of_yam R hU e A
  · exact ⟨true, e', hgen, xdatum_of_labelling R hU hfin hn e' A hcen hgen true hP.1 hP.2⟩
  · exact ⟨false, e', hgen, xdatum_of_labelling R hU hfin hn e' A hcen hgen false hP.1 hP.2⟩

theorem facts45L_of_rankTwo [IsSimpleGroup X] (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D]
    (hfin : Finite D) (hn : 3 ≤ n) (e : X ≃* D) (A : LieAmalgamExt D) :
    (A.setting hfin n hn).Facts45L := by
  have hcen := center_eq_bot_of_rankTwo R e
  have hgen := range_conj_le_of_rankTwo R hU e A
  obtain ⟨e', -, hP | hP⟩ := exists_iso_of_yam R hU e A
  · exact xdatum_aux R hU hfin hn e' A hcen hgen true hP.1 hP.2
  · exact xdatum_aux R hU hfin hn e' A hcen hgen false hP.1 hP.2

end Main

end CFSG.Quasithin.H13.F431.BN
