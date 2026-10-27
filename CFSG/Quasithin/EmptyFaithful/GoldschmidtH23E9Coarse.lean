module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Types
public import CFSG.Quasithin.EmptyFaithful.S151CLRed

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem compListCoarse_of_exclusions (hlist : Lemma115_3_List)
    (xL32 : CompListNoL32) (xG2 : CompListNoG2)
    (x3D4 : CompListNo3D4) (x2F4 : CompListNo2F4) (xJ4 : CompListNoJ4)
    (xL33 : CompListNoL33) (xL2p : CompListNoL2p) : Input15120CompListCoarse := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  obtain ⟨z, hcases⟩ := exists_lemma115Cases hlist hc hcomp
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  have nL32 := xL32 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
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
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hmod)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hmod)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA6)))))
    · exact Or.inr (Or.inr (Or.inl (Or.inl hU33)))
  ·
    rcases h34 with h | h
    · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
    · exact (nG2.2 h).elim
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isAlt_of_center_quotient hZ2 hcard φ))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isAlt_of_center_quotient hZ2 hcard φ))))))
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

end CFSG.Quasithin.E9
