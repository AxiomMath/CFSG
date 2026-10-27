module

public import CFSG.RankThree.GF2n.Tim79aSec34Torus
public import CFSG.RankThree.GF2n.Tim79aCitedSp

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

@[expose] def Sec34CentreSmallStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → CentreClause V H → ∀ n : ℕ, (n = 2 ∨ n = 3) →
      Nonempty (StatedSp n (GaloisField 2 1) ≃* XbarZ V H) → Subgroup.center (Xbar V H) = ⊥

theorem sec34CentreTrivialStatement_of_griess (hG : GriessSpMultiplierStatement)
    (hS : Sec34CentreSmallStatement) : Sec34CentreTrivialStatement := by
  intro G _ _ M V Q P H hs h3 hcc
  obtain ⟨f, hf, -, hT⟩ := id h3
  obtain ⟨n, hn, Φ, hΦ, -⟩ := hT
  by_cases hsmall : (n = 2 ∨ n = 3) ∧ f = 1
  · obtain ⟨hn23, hf1⟩ := hsmall
    subst hf1
    exact hS G M V Q P H hs h3 hcc n hn23 ⟨MulEquiv.ofBijective Φ hΦ⟩
  · set e : StatedSp n (GaloisField 2 f) ≃* XbarZ V H := MulEquiv.ofBijective Φ hΦ with he
    let φ : Xbar V H →* StatedSp n (GaloisField 2 f) := e.symm.toMonoidHom.comp (projZ V H)
    have hsurj : Function.Surjective φ :=
      e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : φ.ker = Subgroup.center (Xbar V H) := by
      ext x
      rw [MonoidHom.mem_ker]
      show e.symm (projZ V H x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    have hne1 : (n, f) ≠ (2, 1) := fun h => hsmall ⟨Or.inl (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
    have hne2 : (n, f) ≠ (3, 1) := fun h => hsmall ⟨Or.inr (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
    have hn1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
    have hne3 : (n, f) ≠ (1, 1) := fun h => Nat.ne_of_gt hn1 (Prod.mk.inj h).1
    have hne4 : (n, f) ≠ (1, 2) := fun h => Nat.ne_of_gt hn1 (Prod.mk.inj h).1
    have := hG n f (le_of_lt hn1) hf hne3 hne4 hne1 hne2 (Xbar V H) φ hsurj (by rw [hker])
      (by rw [hker]; exact hcc)
    rwa [hker] at this

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

theorem sec34SummandStatement_of_griess (hG : GriessSpMultiplierStatement)
    (hS : Sec34CentreSmallStatement) : Sec34SummandStatement :=
  sec34SummandStatement_of_line (sec34LineStatement_of_torus (sec34TorusStatement_of_parts
    (sec34CentreTrivialStatement_of_griess hG hS)
    ))

end CFSG.RankThree.GF2n.Tim79a
