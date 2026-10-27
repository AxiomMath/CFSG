module

public import CFSG.Quasithin.Background.SzG11G64Fix
public import CFSG.Quasithin.Background.G64Proof

public section

namespace CFSG.Quasithin

namespace SzG11

open CFSG.Quasithin.G64 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem isHSubmodule_commV (K : Subgroup (MulAut V)) : G6.IsHSubmodule K (commV K) :=
  fun _ hh _ hu => G6.apply_mem_commV (X := K)
    (fun _ hx => K.mul_mem (K.mul_mem hh hx) (K.inv_mem hh)) hu

theorem g64Decomposition_of_conclusion [Finite V] {X : Subgroup (MulAut V)} {a : MulAut V} {s : ℕ}
    {Ks : Fin s → Subgroup (MulAut V)} (hs2 : s ≤ 2)
    (hsup : (⨆ i, Ks i) = conjClosure (Subgroup.zpowers a) X) (hindep : iSupIndep Ks)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Ks i, ∀ y ∈ Ks j, x * y = y * x)
    (hVsup : (⨆ i, commV (Ks i)) = ⊤) (hfix : ∀ i j, i ≠ j → commV (Ks j) ≤ fixV (Ks i))
    (hpos : 0 < s) (ha : a ∈ Ks ⟨0, hpos⟩)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Ks i).map (MulAut.conj g).toMonoidHom = Ks j)
    (htrans : ∀ i j, ∃ g ∈ X, (Ks i).map (MulAut.conj g).toMonoidHom = Ks j)
    (hmod : ∀ i, G64.ModuleType (Ks i) (commV (Ks i)))
    (hfac : s = 2 → ∀ i, G64.FactorType (Ks i)) : G6.G64Decomposition X a Ks := by
  have hperm' : ∀ g ∈ X, ∀ i, ∃ j, conjSubgroup (Ks i) g = Ks j := fun g hg i =>
    hperm g⁻¹ (X.inv_mem hg) i
  have htrans' : ∀ i j, ∃ g ∈ X, conjSubgroup (Ks i) g = Ks j := by
    intro i j
    obtain ⟨g, hg, hgj⟩ := htrans i j
    refine ⟨g⁻¹, X.inv_mem hg, ?_⟩
    simpa [conjSubgroup] using hgj
  have hcentral : ∀ i j, i ≠ j → Ks i ≤ Subgroup.centralizer (Ks j : Set (MulAut V)) := by
    intro i j hij x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm i j hij x hx y hy).symm
  have hcomm0 : ∀ i j, i ≠ j → G6.commOn (Ks i) (commV (Ks j)) = ⊥ := by
    intro i j hij
    rw [eq_bot_iff, G6.commOn_le_iff]
    intro x hx u hu
    have : x u = u := hfix i j hij hu x hx
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hVind : iSupIndep fun i => commV (Ks i) := by
    obtain rfl | rfl : s = 1 ∨ s = 2 := by omega
    · exact iSupIndep_subsingleton _
    · have hdisj : Disjoint (commV (Ks 0)) (commV (Ks 1)) := by
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx0, hx1⟩
        have hfix01 : x ∈ fixV (Ks 0) := hfix 0 1 (by decide) hx1
        exact Subgroup.mem_bot.2 (fixed_eq_one_of_moduleType (hmod 0) (hfac rfl 0) x hx0
          (fun l hl => mem_fixV.1 hfix01 l hl))
      exact (iSupIndep_pair (by decide : (0 : Fin 2) ≠ 1) (by decide)).2 hdisj
  exact ⟨⟨hpos, hs2, hsup, hindep, hcentral, hVsup, hVind, hcomm0,
    fun i => isHSubmodule_commV _, fun i => isG64Type_of_moduleType (hmod i),
    fun hs i => isSmallG64Type_of_factorType (hfac hs i)⟩, ⟨hpos, ha⟩, hperm', htrans'⟩

theorem lemma_G64_of_b5 (h56 : AsB56) [Finite V] {X : Subgroup (MulAut V)} {a : MulAut V}
    (h : G6.Hypothesis61 X a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    (∃ Ks : Fin 1 → Subgroup (MulAut V), G6.G64Decomposition X a Ks ∧
        X = G6.classClosure X a) ∨
    (∃ Ks : Fin 2 → Subgroup (MulAut V), G6.G64Decomposition X a Ks ∧ G6.IsSmallG64Type (Ks 0) ∧
      G6.IsSmallG64Type (Ks 1) ∧ ∃ t ∈ X, t * t = 1 ∧
        X = G6.classClosure X a ⊔ Subgroup.zpowers t ∧ conjSubgroup (Ks 0) t = Ks 1) := by
  have hconc := lemmaG64_of_b5 h56 V h.sq_eq_one X a (hyp61_of_hypothesis61 h) htr
  obtain ⟨s, Ks, hs2, hsup, hindep, hcomm, hVsup, hfix, ⟨hpos, ha⟩, hperm, htrans, hmod, h3, -⟩ :=
    hconc
  have hdec := g64Decomposition_of_conclusion hs2 hsup hindep hcomm hVsup hfix hpos ha hperm htrans
    hmod (fun hs => by rcases h3 with ⟨h1, -⟩ | ⟨-, hf, -⟩ <;> [omega; exact hf])
  rcases h3 with ⟨rfl, hGK⟩ | ⟨rfl, hfac, t, htG, ht1, ht2, hGt, htconj⟩
  · exact Or.inl ⟨Ks, hdec, hGK⟩
  · have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
    refine Or.inr ⟨Ks, hdec, isSmallG64Type_of_factorType (hfac 0),
      isSmallG64Type_of_factorType (hfac 1), t, htG, ht2', hGt, ?_⟩
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
    have := htconj 0 1 (by decide)
    simpa [conjSubgroup, hinv] using this

theorem lemma_G64_all_of_b5 (h56 : AsB56) [Finite V] {X : Subgroup (MulAut V)} {a : MulAut V}
    (h : G6.Hypothesis61 X a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)), G6.G64Decomposition X a Ks ∧
      (∀ T : Subgroup (MulAut V), CFSG.QuasithinUnique.IsSylowTwoOf T X → a ∈ T →
        (∀ t ∈ T, t * a = a * t) →
        s = 1 ∧ X = G6.classClosure X a ∧
          ((∃ n, 2 ≤ n ∧ n ≤ 5 ∧ Nonempty (↥X ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2))) ∨
            Nonempty (↥X ≃* Equiv.Perm (Fin 6)) ∨ Nonempty (↥X ≃* Equiv.Perm (Fin 7)))) := by
  have hconc := lemmaG64_of_b5 h56 V h.sq_eq_one X a (hyp61_of_hypothesis61 h) htr
  obtain ⟨s, Ks, hs2, hsup, hindep, hcomm, hVsup, hfix, ⟨hpos, ha⟩, hperm, htrans, hmod, h3, h4⟩ :=
    hconc
  refine ⟨s, Ks, g64Decomposition_of_conclusion hs2 hsup hindep hcomm hVsup hfix hpos ha hperm
    htrans hmod (fun hs => by rcases h3 with ⟨h1, -⟩ | ⟨-, hf, -⟩ <;> [omega; exact hf]),
    fun T hT haT hcent => ?_⟩
  obtain ⟨hs1, hGK, hct⟩ := h4 ⟨T, hT, haT, hcent⟩
  refine ⟨hs1, hGK, ?_⟩
  rcases hct with ⟨n, h2, h5, ⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
  · exact Or.inl ⟨n, h2, h5, ⟨e.trans (statedSLEquivGL n)⟩⟩
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

end SzG11

end CFSG.Quasithin
