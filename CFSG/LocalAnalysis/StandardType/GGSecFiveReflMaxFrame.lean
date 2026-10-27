module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.RootSystem CFSG.LieType.Universal

theorem ggRM_frame_L
    (hFix : GGSecFiveFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL := by
  obtain ⟨t, n, f, ψ, hloc, _hstd, htab⟩ :=
    s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hsplit
  simp only [GGTableBPos] at htab
  obtain ⟨ε, hrefl, _hrankone, htoral⟩ := htab
  obtain ⟨hp, _hp2, hadm, h3rank⟩ := hloc.1
  obtain ⟨_hker, _hrange, ht, _hpf⟩ := hloc.2.1
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨_hp', hBs_ea, hxBs, _hLx, _h4⟩ := hconf.tableB_facts
  have hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p := by
    have hle : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers x := by
      intro b hb
      obtain ⟨hbBs, hbC⟩ := hb
      have hfix : ∀ φ ∈ ggAutomizer L Bs, φ ⟨b, hbBs⟩ = ⟨b, hbBs⟩ := by
        intro φ hφ
        obtain ⟨g, hgL, _hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
        apply Subtype.ext
        rw [hgφ]
        have hcomm : g * b = b * g := (Subgroup.mem_centralizer_iff.mp hbC) g hgL
        rw [hcomm]
        group
      exact hFix G p B Bs x L D J 𝒦 hcfg hsplit ⟨b, hbBs⟩ hfix
    calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G))
        ≤ Nat.card ↥(Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      _ = orderOf x := Nat.card_zpowers x
      _ ≤ p := by
          refine Nat.le_of_dvd hp.pos (orderOf_dvd_iff_pow_eq_one.mpr ?_)
          exact hBs_ea.2 x hxBs
  have hrank : 3 ≤ Fintype.card (Fin (ggU t n f).D.rank) := by
    rw [Fintype.card_fin, lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3rank]
    exact h3rank
  have htype : GGIsWeylMatrixAD (coxeterMatrix (ggU t n f).D.isFiniteType) ∨
      GGIsWeylMatrixE (coxeterMatrix (ggU t n f).D.isFiniteType) := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_psl (n := n) (f := f) hadm
      exact Or.inl (Or.inl ⟨n - 1, e, by simpa only [bnRank] using h3rank, he⟩)
    · have hn4 : 4 ≤ n := by
        have h := hadm
        simp only [StatedLieAdmissible] at h
        exact h.2.2
      obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_D (n := n) (f := f) hadm
      exact Or.inl (Or.inr ⟨n, e, hn4, he⟩)
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_E (n := n) (f := f)
      exact Or.inr (Or.inl ⟨e, he⟩)
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_E7 (n := n) (f := f)
      exact Or.inr (Or.inr (Or.inl ⟨e, he⟩))
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_E8 (n := n) (f := f)
      exact Or.inr (Or.inr (Or.inr ⟨e, he⟩))
  have hbound : Nat.card ↥Bs ≤ p ^ (Fintype.card (Fin (ggU t n f).D.rank) + 1) := by
    calc Nat.card ↥Bs
        ≤ p ^ (ggU t n f).D.rank *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := htoral
      _ ≤ p ^ (ggU t n f).D.rank * p := Nat.mul_le_mul_left _ hcardC
      _ = p ^ (ggU t n f).D.rank.succ := (pow_succ p _).symm
      _ = p ^ (Fintype.card (Fin (ggU t n f).D.rank) + 1) := by rw [Fintype.card_fin]
  exact ⟨Fin (ggU t n f).D.rank, inferInstance,
    coxeterMatrix (ggU t n f).D.isFiniteType, htype, ⟨ε, hrefl⟩, hbound, hrank⟩

end CFSG.StandardType

end
