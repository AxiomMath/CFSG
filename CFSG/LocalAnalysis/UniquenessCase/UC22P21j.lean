module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22p21j_normal_of_conjClosure_eq {M L : Subgroup G} (hLM : L ≤ M) (h : L = conjClosure M L) :
    (L.subgroupOf M).Normal := by
  have hle : ∀ g ∈ M, L.map (MulAut.conj g).toMonoidHom ≤ L := fun g hg =>
    calc L.map (MulAut.conj g).toMonoidHom ≤ conjClosure M L :=
          le_iSup₂_of_le (L.map (MulAut.conj g).toMonoidHom) ⟨g, hg, rfl⟩ le_rfl
      _ = L := h.symm
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle g hg ⟨y, hy, rfl⟩
  · intro hy
    have := hle g⁻¹ (M.inv_mem hg) ⟨g * y * g⁻¹, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

@[expose] def S21_Normal (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M,
    ((∃ n : ℕ, IsSp4 (BarInf L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n)) → (L.subgroupOf D.M).Normal

@[expose] def SpU3NotList (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ((∃ n : ℕ, IsSp4 (BarInf L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n)) →
    (∀ m : ℕ, ¬ IsL2 (Bar2 L) m) ∧ (∀ m : ℕ, ¬ IsSz (Bar2 L) m) ∧ ¬ IsJ1 (Bar2 L)

theorem uc22p21j_normal_of_s21_17 (D : Data G) (Ch : Choice2011 G) (h17 : S21_17 D Ch)
    (hn : SpU3NotList D) : S21_Normal D Ch := by
  intro h1930 c L hL hshape
  have hLM : L ≤ D.M := hL.1.le
  rcases h17 h1930 c L hL with h | ⟨_, n', _, hL2 | hSz⟩ | ⟨_, hJ1, _⟩
  · exact uc22p21j_normal_of_conjClosure_eq hLM h
  · exact absurd hL2 ((hn L hL hshape).1 n')
  · exact absurd hSz ((hn L hL hshape).2.1 n')
  · exact absurd hJ1 (hn L hL hshape).2.2

theorem uc22p21j_normal_of_sp4 (D : Data G) (Ch : Choice2011 G) (hN : S21_Normal D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hsp : IsSp4 ↥(mbarImage D.M c.V K) n) (hodd : Odd n) : (K.subgroupOf D.M).Normal :=
  hN h1930 c.toCtx21 K hKC (Or.inl ⟨n, uc22p22a_shape_sp4 D c hKC hsp⟩)

theorem uc22p21j_normal_of_su3 (D : Data G) (Ch : Choice2011 G) (hN : S21_Normal D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hsu : IsSU3 ↥(mbarImage D.M c.V K) n) (hmod : n ≡ 1 [MOD 6]) : (K.subgroupOf D.M).Normal :=
  hN h1930 c.toCtx21 K hKC (Or.inr ⟨n, uc22p22a_shape_su3 D c hKC hsu⟩)

theorem uc22p21j_s22_15_of (D : Data G) (Ch : Choice2011 G) (hK147 : K147) (h22V : S22_V D Ch)
    (h9 : S22_9 D Ch) (h14 : S22_14 D Ch) (hN : S21_Normal D Ch)
    (hJ1 : uc22p22d_J1Nontrivial) : S22_15 D Ch := by
  intro h1930 c p hp K n hK
  have hKC : K ∈ calC D.M := hK.1
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have hred : TwoReduced D.M c.V := (h22V h1930 c).1.2.2
  have hel : CFSG.Open.IsElemAbelian 2 c.V := (h22V h1930 c).1.1.1.2.2.2
  have hn : c.n ≤ n := h14 h1930 c p hp K n hK
  have h9' : ¬ MBarGT D.M ⊥ c.V (c.n + 1) := h9 h1930 c
  haveI := uc22p22d_nontrivial hJ1 hK
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
      ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hpc : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have hcomp := uc22br4_isComponentOf_mbarImage D.M c.V K c.hVM hpc hKC hKV
  rcases hK.2.2 with ⟨hsp, hodd, ht⟩ | ⟨hsu, hmod⟩ | ⟨h3, hnum⟩ | ⟨hyp, hU | hL, -⟩
  · have hnorm := uc22p21j_normal_of_sp4 D Ch hN h1930 c hKC hsp hodd
    have hlg := uc22p22d_lgConj_of_normal c.V hKM hnorm
    have h2 := uc22p22a_two_le_of_isSp4 hsp
    refine uc22p22d_isL2_of_case147 hK147 D c hred hel hKC hKV (by omega)
      (Or.inl ⟨by omega, hodd, ?_, ?_⟩) h9' hn
    · rw [hlg]; exact hsp
    · obtain ⟨t, -, ht⟩ := ht
      rw [hlg]
      exact ⟨_, ht⟩
  · have hnorm := uc22p21j_normal_of_su3 D Ch hN h1930 c hKC hsu hmod
    have hlg := uc22p22d_lgConj_of_normal c.V hKM hnorm
    have h2 := uc22p22a_two_le_of_isU3 hsu.2
    refine uc22p22d_isL2_of_case147 hK147 D c hred hel hKC hKV h2
      (Or.inr (Or.inl ?_)) h9' hn
    rw [hlg]; exact hsu
  · have hnum' : F05.numConj (mbarImage D.M c.V K) ≤ 2 :=
      (uc22br4_numConj_mbarImage_le D.M c.V K).trans hnum.le
    have hn2 : 2 ≤ n := by
      rcases h3 with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · omega
    exact uc22p22d_isL2_of_case147 hK147 D c hred hel hKC hKV hn2 (Or.inr (Or.inr ⟨h3, hnum'⟩))
      h9' hn
  · have hnorm := (hyp.2.1 K hKC).1
    have hlg := uc22p22d_lgConj_of_normal c.V hKM hnorm
    have h2 := uc22p22a_two_le_of_isU3 hU
    refine uc22p22d_isL2_of_case147 hK147 D c hred hel hKC hKV h2
      (Or.inr (Or.inl ?_)) h9' hn
    rw [hlg]
    exact uc22p22d_isSU3_of_isU3 hcomp.2.2 hU
  · exact hL

theorem uc22p21j_s22_17_of (D : Data G) (Ch : Choice2011 G) (hK147 : K147) (h22V : S22_V D Ch)
    (h9 : S22_9 D Ch) (h14 : S22_14 D Ch) (hN : S21_Normal D Ch)
    (hJ1 : uc22p22d_J1Nontrivial) : S22_17 D Ch := by
  intro h1930 c p hp K n hK t htT htK Vmod _ _ _ e ρ hc
  have hKC : K ∈ calC D.M := hK.1
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have htM : t ∈ D.M := D.sylowM.le htT
  have hnn : ¬ (K.subgroupOf D.M).Normal := fun hn =>
    htK (((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hn) htM)
  have h3 : (((2 < n ∧ (IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n)) ∨
      (IsJ1 ↥(mbarImage D.M c.V K) ∧ n = 3)) ∧ (conjSetOf D.M K).ncard = 2) := by
    rcases hK.2.2 with ⟨hsp, hodd, -⟩ | ⟨hsu, hmod⟩ | h3 | ⟨hyp, -, -⟩
    · exact (hnn (uc22p21j_normal_of_sp4 D Ch hN h1930 c hKC hsp hodd)).elim
    · exact (hnn (uc22p21j_normal_of_su3 D Ch hN h1930 c hKC hsu hmod)).elim
    · exact h3
    · exact (hnn (hyp.2.1 K hKC).1).elim
  have hred : TwoReduced D.M c.V := (h22V h1930 c).1.2.2
  have hn : c.n ≤ n := h14 h1930 c p hp K n hK
  have h9' : ¬ MBarGT D.M ⊥ c.V (c.n + 1) := h9 h1930 c
  haveI := uc22p22d_nontrivial hJ1 hK
  have hnt : mbarImage D.M c.V K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    hnt ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hnum : F05.numConj (mbarImage D.M c.V K) ≤ 2 :=
    (uc22br4_numConj_mbarImage_le D.M c.V K).trans h3.2.le
  have hcase : Case147 (mbarImage D.M c.V K) n := Or.inr (Or.inr ⟨h3.1, hnum⟩)
  have hconcl := uc22br4_k147_apply_ctx hK147 D c hred e ρ hc hKC hKV hcase h9' hn
  have hne' : K.map (MulAut.conj t).toMonoidHom ≠ K := fun h =>
    htK (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ CFSG.Quasithin.cComp D.M :=
    uc22p20b_cj_mem_cComp (uc22p20e_cComp_of_calC hKC) htM
  have hbarne : mbarImage D.M c.V K ≠ mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom) :=
    uc22p22d_mbarImage_ne D.M c.V hKC hKt hne'.symm hnt
  have hKt' : mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom) =
      (mbarImage D.M c.V K).map
        (MulAut.conj (QuotientGroup.mk (⟨t, htM⟩ : ↥D.M) : MBar D.M c.V)).toMonoidHom :=
    uc22br4_mbarImage_map_conj D.M c.V K ⟨t, htM⟩
  have hclosure : conjClosure D.M K = K ⊔ K.map (MulAut.conj t).toMonoidHom :=
    uc22p22d_conjClosure_pair htM hne' h3.2
  have hlg : lgConj (mbarImage D.M c.V K) =
      mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom) := by
    rw [uc22br4_lgConj_mbarImage D.M c.V K hKM, hclosure]
  rcases hconcl with ⟨hA, hB⟩ | hOm
  · right
    have hirr : ρ.IsIrreducible :=
      (uc22br4_isIrreducible_iff D.M c.V c.hVM e ρ hc).2 ⟨c.hVne, c.hVirr⟩
    have hfaith : Function.Injective ρ := uc22br4_injective D.M c.V c.hVM e ρ hc
    set gb : MBar D.M c.V := QuotientGroup.mk (⟨t, htM⟩ : ↥D.M)
    have hgn : gb ∉ normalizer
        ((mbarImage D.M c.V K : Subgroup (MBar D.M c.V)) : Set (MBar D.M c.V)) := by
      intro h
      have := Subgroup.mem_normalizer_iff_map_conj_eq.1 h
      exact hbarne (by rw [hKt']; exact this.symm)
    have hconj : ∀ h : MBar D.M c.V,
        (mbarImage D.M c.V K).map (MulAut.conj h).toMonoidHom = mbarImage D.M c.V K ∨
        (mbarImage D.M c.V K).map (MulAut.conj h).toMonoidHom =
          (mbarImage D.M c.V K).map (MulAut.conj gb).toMonoidHom := by
      intro h
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective h
      have hm : K.map (MulAut.conj (m : G)).toMonoidHom ∈ conjSetOf D.M K := ⟨m, m.2, rfl⟩
      rw [uc22p22d_conjSet_pair htM hne' h3.2] at hm
      rcases hm with hm | hm
      · left
        rw [← uc22br4_mbarImage_map_conj D.M c.V K m, hm]
      · right
        rw [← uc22br4_mbarImage_map_conj D.M c.V K m, hm, hKt']
    obtain ⟨hs, hi⟩ := uc22p22d_split ρ hirr hfaith hnt gb
      (fun h => hbarne (by rw [hKt']; exact h.symm)) hconj (hA gb hgn)
    refine ⟨?_, ?_, ?_⟩
    · rw [hKt']; exact hs
    · rw [hKt']; exact hi
    · rcases hB with h | h | ⟨h3, -, h8⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h3, h8⟩)
  · left
    rw [← hlg]
    exact hOm

theorem uc22p21j_s22_end_of_steps (D : Data G) (Ch : Choice2011 G) (hsig : D.sig.Nonempty)
    (hN : S21_Normal D Ch)
    (h22_13 : S22_13 D Ch) (h22_16 : S22_16 D Ch) (h22_18 : S22_18 D Ch) (hfin : S22_fin D Ch) :
    S22_end D Ch := by
  intro h1930 c
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨K, n, hK⟩ := h22_13 h1930 c p hp
  have hnn : ¬ (K.subgroupOf D.M).Normal := h22_16 h1930 c p hp K n hK
  have hKC : K ∈ calC D.M := hK.1
  rcases hK.2.2 with ⟨hsp, hodd, -⟩ | ⟨hsu, hmod⟩ | ⟨-, hconj⟩ | ⟨hyp, -, -⟩
  · exact (hnn (uc22p21j_normal_of_sp4 D Ch hN h1930 c hKC hsp hodd)).elim
  · exact (hnn (uc22p21j_normal_of_su3 D Ch hN h1930 c hKC hsu hmod)).elim
  · obtain ⟨t, ht, htK⟩ : ∃ t ∈ D.T, t ∉ normalizer (K : Set G) := by
      by_contra hcon
      push Not at hcon
      have h2 : 2 ∣ (conjSetOf D.M K).ncard := by rw [hconj]
      exact uc22p22a_not_two_dvd_ncard D.sylowM (fun t ht => hcon t ht) h2
    exact hfin h1930 c p hp K n hK t ht htK (h22_18 h1930 c p hp K n hK t ht htK)
  · exact (hnn (hyp.2.1 K hKC).1).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
