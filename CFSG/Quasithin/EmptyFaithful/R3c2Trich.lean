module

public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem input27Trichotomy_of_facts
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hE : Ch11.SecA.FactA318Excl) : Input27Trichotomy := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hlist hnorm
  obtain ⟨hLJ, -, -, -, hXq, hQ⟩ := c.conc
  have hI := c.ctx.inH
  have hFacts := c.facts
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLJ
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hSQ : SQTKGroup ↥I :=
    sqtkGroup_of_pCoreOf_ne_bot c.ctx.hyp.hyp.qtfe.qtke c.ctx.hyp.hyp.qtfe.simple
      c.ctx.hyp.hyp.qtfe.nonabelian hI.1.2
  have hrank : CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Star153 T I L)) :=
    pRank_three_eq_star hI hFacts hLI
  have hexcl : A318Exclusion ↥(Star153 T I L) → L = thetaOf I := fun hS =>
    eq_thetaOf_of_star_exclusion hF h36 h38 hSQ hI hFacts hLc hnorm hQ (MulEquiv.refl _) hS
  rcases hlist with ⟨n, K, _, _, hKn, ⟨e⟩⟩ | ⟨n, K, _, _, hKn, ⟨e⟩⟩ | ⟨n, K, _, _, hKn, ⟨e⟩⟩ |
    ⟨n, K, _, _, hKn, ⟨e⟩⟩ | he6 | he7 | hhat | ⟨K, _, _, h2, ⟨e⟩⟩ | he4 | he5
  ·
    refine Or.inl ⟨?_, Or.inl ⟨n, K, inferInstance, inferInstance, hKn, ⟨e⟩⟩⟩
    rw [hrank, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e,
      pRank_three_statedSL_two hKn]
  ·
    rcases Nat.even_or_odd n with hn | hn
    · exact Or.inr (Or.inr ⟨n, hn, K, inferInstance, inferInstance, hKn, ⟨e⟩⟩)
    · refine Or.inl ⟨?_, Or.inr ⟨n, hn, K, inferInstance, inferInstance, hKn, ⟨e⟩⟩⟩
      rw [hrank, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e,
        R3c.pRank_three_statedSL_three_odd hn hKn]
  · exact Or.inr (Or.inl (hexcl (exclusion_sp4 hE hKn e hXq)))
  · exact Or.inr (Or.inl (hexcl (exclusion_g2 hE hKn e hXq)))
  · obtain ⟨e⟩ := he6
    exact Or.inr (Or.inl (hexcl (exclusion_of_mulEquiv e.symm hK.alt6)))
  · obtain ⟨e⟩ := he7
    exact Or.inr (Or.inl (hexcl (exclusion_of_mulEquiv e.symm hK.alt7)))
  · exact Or.inr (Or.inl (eq_thetaOf_of_star_hat hF h36 h38 hSQ hI hFacts hLc hnorm hQ hhat))
  · exact Or.inr (Or.inl (hexcl (exclusion_g2Derived hK h2 e)))
  · obtain ⟨e⟩ := he4
    exact Or.inr (Or.inl (hexcl (hK.l42 _ (isPSL_two_of_statedSL (by norm_num) e))))
  · obtain ⟨e⟩ := he5
    exact Or.inr (Or.inl (hexcl (hK.l52 _ (isPSL_two_of_statedSL (by norm_num) e))))

end CFSG.Quasithin.R3c2
