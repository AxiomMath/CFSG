module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem412
public import CFSG.Quasithin.Vol2.Ch4Sec4Hyp

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

structure Setting443 (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G) : Prop where
  hyp : Hyp4_4_1Orbit G T M L B Tp VB
  not_concl : ¬ Concl4_4_3 G T M L B VB

@[expose] def Lemma446One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
    Setting443 G T M L B Tp VB →
      IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
        (Tp ⊓ Subgroup.normalizer (B : Set G))) M

@[expose] def Lemma448 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
    Setting443 G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M →
      oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G)

@[expose] def Lemma443End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
    Setting443 G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M →
    oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G) → False

variable {G : Type} [Group G] [Finite G]

namespace Setting443

variable {T M L B Tp VB : Subgroup G} (s : Setting443 G T M L B Tp VB)
include s

theorem not_normalizer_le : ¬ Subgroup.normalizer (B : Set G) ≤ M :=
  fun h => s.not_concl (Or.inl h)

theorem sup_le_normalizer :
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
        (Tp ⊓ Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G) := by
  have hLT : conjClosure L T ≤ M :=
    conjClosure_le fun t ht l hl => by
      have hTN : T ≤ Subgroup.normalizer (M : Set G) := fun x hx => Subgroup.le_normalizer
        (s.hyp.T_le hx)
      exact (Subgroup.mem_normalizer_iff.mp (hTN ht) l).mp (s.hyp.L_le hl)
  refine _root_.sup_le (le_inf ((perfectCore_le _).trans (inf_le_left.trans hLT)) ?_)
    (inf_le_inf_right _ (s.hyp.Tp_le.trans s.hyp.T_le))
  exact (perfectCore_le _).trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))

theorem normalizer_VB_le (hU : IsUniqueM (perfectCore (conjClosure L T ⊓
    Subgroup.centralizer (B : Set G)) ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G))) M) :
    Subgroup.normalizer (VB : Set G) ≤ M := by
  have hVT : VB ≤ T := fun v hv =>
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le s.hyp.sylow le_sup_right)
      (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).1
  refine isUniqueM_normalizer_le hU s.hyp.VB_ne_bot (s.hyp.sylow.1.to_le hVT) ?_
  refine _root_.sup_le ((perfectCore_le _).trans (inf_le_left.trans
    (le_sup_left.trans s.hyp.VB_normalized))) ?_
  exact inf_le_left.trans (s.hyp.Tp_le.trans (le_sup_right.trans s.hyp.VB_normalized))

theorem pCoreOf_normalizer_eq_bot (hU : IsUniqueM (perfectCore (conjClosure L T ⊓
    Subgroup.centralizer (B : Set G)) ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G))) M) :
    pCoreOf 2 (Subgroup.normalizer (B : Set G)) = ⊥ := by
  by_contra hne
  have hN := isUniqueM_normalizer_le hU hne (pCoreOf_isPGroup 2 _)
    (s.sup_le_normalizer.trans (inf_le_right.trans (le_normalizer_pCoreOf 2 _)))
  exact s.not_normalizer_le ((le_normalizer_pCoreOf 2 _).trans hN)

theorem le_of_isTwoLocal (hU : IsUniqueM (perfectCore (conjClosure L T ⊓
    Subgroup.centralizer (B : Set G)) ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G))) M)
    {P : Subgroup G} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (hMP : M ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G) ≤
      M ⊓ Subgroup.normalizer (B : Set G) := by
  have hN := isUniqueM_normalizer_le hU hP hP2 (s.sup_le_normalizer.trans hMP)
  exact fun x hx => ⟨hN hx.2, hx.1⟩

end Setting443

theorem stmt4_4_3Orbit_of_steps (h446 : Lemma446One) (h448 : Lemma448) (hEnd : Lemma443End) :
    Stmt4_4_3Orbit := by
  rw [stmt4_4_3Orbit_iff]
  intro G _ _ T M L B Tp VB hH
  by_contra hc
  have s : Setting443 G T M L B Tp VB := ⟨hH, hc⟩
  have hU := h446 G T M L B Tp VB s
  exact hEnd G T M L B Tp VB s hU (h448 G T M L B Tp VB s hU)

theorem stmt4_4_3_of_steps (h446 : Lemma446One) (h448 : Lemma448) (hEnd : Lemma443End) :
    Stmt4_4_3 :=
  stmt4_4_3_of_orbit (stmt4_4_3Orbit_of_steps h446 h448 hEnd)

end CFSG.Quasithin.H13.Ch4
