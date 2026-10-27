module

public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem isAlt_of_center_quotient {n : ℕ} {X : Type} [Group X] [Finite X]
    (hZ2 : IsPGroup 2 (Subgroup.center X))
    (hc : Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3)
    (φ : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin n)) : IsAlt n X := by
  have h1 : Nat.card (Subgroup.center X) = 1 := by
    rcases hc with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ2
      rw [h] at hk
      rcases k with _ | k
      · simp at hk
      · have : 2 ∣ 3 := ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
        omega
  have hbot : Subgroup.center X = ⊥ := (Subgroup.card_eq_one).1 h1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans φ⟩

theorem exists_lemma115Cases (hlist : Lemma115_3_List) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁)) :
    ∃ z : G, Lemma115Cases L z := by
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ctx.qtfe.omegaOneCenter_ne_bot
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hyp := hc.h18.six z hzZ hz1
  have hLin : IsComponentIn L (g1_1516 Z₁) := DoubleA3.isComponentIn_iff_open.mpr hcomp
  have := hc.ctx.qtfe.simple
  have hcore := qtkeCore_of_cat hc.ctx.qtfe.nonabelian hc.ctx.qtfe.qtke
  exact ⟨z, hlist G hc.ctx.qtfe.simple hc.ctx.qtfe.nonabelian hcore (g1_1516 Z₁) (s1516 T Z₁) Mc z
    hyp L hLin⟩

theorem compList_of_exclusions (hlist : Lemma115_3_List)
    (xL32 : CompListNoL32) (xA6 : CompListNoA6) (xA7 : CompListNoA7) (xG2 : CompListNoG2)
    (x3D4 : CompListNo3D4) (x2F4 : CompListNo2F4) (xJ4 : CompListNoJ4)
    (xL33 : CompListNoL33) (xL2p : CompListNoL2p) : Input15120CompList := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx
  obtain ⟨z, hcases⟩ := exists_lemma115Cases hlist hc hcomp
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  have nL32 := xL32 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have nA6 := xA6 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx
  have nA7 := xA7 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx
  have nG2 := xG2 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have n3D4 := x3D4 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have n2F4 := x2F4 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have nJ4 := xJ4 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have nL33 := xL33 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have nL2p := xL2p G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  rcases hcases with ⟨-, hlie, -⟩ | ⟨-, -, h34, -⟩ | ⟨φ, σ, hcard, -, -⟩ | ⟨φ, σ, hcard, -, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hs, ⟨e⟩⟩, -⟩
  ·
    rcases hlie with (⟨⟨f, hf⟩ | hTits⟩ | ⟨n, hn45, hmod⟩) | hA6 | hU33
    · rcases hf with ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h1, hm⟩ |
        ⟨h1, h2, hm⟩ | ⟨h1, h2, hm⟩
      · exact Or.inl (Or.inl (Or.inl ⟨f, h2, hm⟩))
      · by_cases hf1 : f = 1
        · subst hf1
          exact (nL32 (Or.inl hm)).elim
        · exact Or.inr (Or.inl (Or.inl ⟨f, by omega, hm⟩))
      · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨f, h2, hm⟩)))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨f, h2, hm⟩)))
      · exact (nG2.1 f h2 hm).elim
      · by_cases hf1 : f = 1
        · subst hf1
          exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hm))))
        · exact (n3D4 f (by omega) hm).elim
      · exact (n2F4 f h1 h2 hm).elim
      · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨f, hm⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hTits))))
    · rcases hn45 with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmod))))
    · exact (nA6 (hA6)).elim
    · exact Or.inr (Or.inr (Or.inl (Or.inl hU33)))
  ·
    rcases h34 with h | h
    · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
    · exact (nG2.2 h).elim
  ·
    exact (nA6 (isAlt_of_center_quotient hZ2 hcard φ)).elim
  ·
    exact (nA7 (isAlt_of_center_quotient hZ2 hcard φ)).elim
  ·
    rcases hE with h33 | ⟨p, hp, hpm⟩
    · exact (nL33 h33).elim
    · by_cases hp7 : 7 < p
      · exact (nL2p p hp hp7 hpm).elim
      · obtain ⟨⟨hpp, -, -, h22, h23⟩, K, hKf, hKfin, hK, ⟨eK⟩⟩ := hpm
        have hp7' : p ≤ 7 := by omega
        obtain rfl | rfl : p = 5 ∨ p = 7 := by
          have h2 : p ≠ 2 := fun h => h22 (by simp [h])
          have h3 : p ≠ 3 := fun h => h23 (by simp [h])
          have h0 : p ≠ 0 := fun h => by subst h; norm_num at hpp
          have h1 : p ≠ 1 := fun h => by subst h; norm_num at hpp
          have h4 : p ≠ 4 := fun h => by subst h; norm_num at hpp
          have h6 : p ≠ 6 := fun h => by subst h; norm_num at hpp
          omega
        ·
          obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
            K (Or.inr (by simpa using hK))
          exact Or.inl (Or.inl (Or.inl ⟨2, le_rfl,
            statedClassicalModel_psl_two_four_of_alternating_five ↥L ⟨eK.trans e5⟩⟩))
        · exact (nL32 (Or.inr ⟨⟨hpp, by norm_num, le_rfl, h22, h23⟩, K, hKf, hKfin, hK,
            ⟨eK⟩⟩)).elim
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨e⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨e⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨e⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨e⟩)))))))))
    · exact (nJ4 ⟨e⟩).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨e⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨e⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr ⟨e⟩)))))))))))

end CFSG.Quasithin
