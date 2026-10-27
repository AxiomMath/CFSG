module

public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11SecBBasic
public import CFSG.Quasithin.Vol2.Ch11SecBFacts24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem nParam_cases36 (hNF : NatFacts) (h1102 : Stmt11_0_2) (h1121 : Stmt11_2_1)
    (h1122 : Stmt11_2_2) (h1133 : Stmt11_3_3) (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H) (hnot : ¬ Concl11_3_2 T L I n V₁ H) :
    E1.nParam H = n ∨ ((n : ℕ∞) < E1.nParam H ∧ Case11_2_1Two T L I n H) := by
  obtain ⟨-, V₂, -, -, hV₂, -⟩ := exists_isVi hNF h1102 hyp
  have hW := h1133 G T L I n V₁ H hyp hV₁ h31 hnot
  have hVab := isElemAbelian_fsuV hyp
  have hk := sParam_le_nParam hyp h31 hW hVab
  have hsn : (n : ℕ∞) ≤ E3.sParam hVab := by
    by_cases hG2 : KindG2 L (fsuV T I) n
    · rw [(h1122 G T L I n (2 * n) V₁ V₂ hyp hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.1 hVab]
      exact_mod_cast (by omega : n ≤ 2 * n)
    · rw [(h1122 G T L I n n V₁ V₂ hyp hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.2.1 hVab]
  rcases eq_or_lt_of_le (hsn.trans hk) with h | h
  · exact Or.inl h.symm
  · refine Or.inr ⟨h, ?_⟩
    rcases h1121 G T L I n hyp H h31.hstar with h' | h'
    · exact absurd h' (not_le.2 h)
    · exact h'

theorem isTwoReducedIn_VM (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) :
    IsTwoReducedIn (Subgroup.normalizer (L : Set G)) (VM T L I) := by
  obtain ⟨⟨hVLT, hVred⟩, -⟩ := h1103 G T L I n hyp
  exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩

theorem VM_le_T (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) : VM T L I ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := isTwoReducedIn_VM h1103 hyp
  have hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hyp.normal
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR.1 hR.2.1
    (B2F.isPGroup_of_isElemAbelian hR.2.2.1)).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hTS)

theorem VM_ne_bot (hyp : Hyp11 G T L I n) : VM T L I ≠ ⊥ := fun h =>
  fsuV_ne_bot hyp (le_bot_iff.mp (h ▸ le_conjClosure _ _))

theorem sup_le_normalizer_VM (hyp : Hyp11 G T L I n) :
    L ⊔ T ≤ Subgroup.normalizer (VM T L I : Set G) :=
  (sup_le Subgroup.le_normalizer hyp.normal).trans (le_normalizer_conjClosure _ _)

theorem normalizer_VM_le (h331 : Stmt3_3_1) (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) :
    Subgroup.normalizer (VM T L I : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  normalizer_le_of_isPGroup h331 hyp
    (B2F.isPGroup_of_isElemAbelian (isTwoReducedIn_VM h1103 hyp).2.2.1) (VM_ne_bot hyp)
    (sup_le_normalizer_VM hyp)

theorem hypE61_VM (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (hyp : Hyp11 G T L I n) : E6.HypE61 T (Subgroup.normalizer (L : Set G)) (VM T L I) := by
  have hR := isTwoReducedIn_VM h1103 hyp
  have hLT := sup_le_normalizer_VM hyp
  have hLTQ := le_normalizer_inf_centralizer h1102 hyp (le_conjClosure _ _) hLT
  have hLTM : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hyp.normal
  refine ⟨hyp.fsu.simple, hyp.fsu.nonabelian, hyp.fsu.qtke, hyp.fsu.sylow,
    ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩, VM_ne_bot hyp, hR.2.2.1, VM_le_T h1103 hyp,
    hyp.normal.trans hR.2.1, ⟨hR.1, fun g hg hgN => absurd (hR.2.1 hg) hgN⟩, ?_⟩
  refine ⟨⟨isMaxTwoLocal_M h331 hyp, inf_le_right.trans inf_le_left⟩, fun M' hM' => ?_⟩
  exact (isUniqueM_LT h331 hyp).2 M' ⟨hM'.1, (le_inf hLTQ (le_inf hLTM hLT)).trans hM'.2⟩

theorem flag24_of (hNF : NatFacts) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (hyp : Hyp11 G T L I n) {V₁ V₂ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    Flag24 L (fsuV T I) ⊤ T V₁ V₂ n := by
  obtain ⟨U₁, U₂, -, hU₁, hU₂, -, h12, -, hu1, hu2, -⟩ := exists_isVi hNF h1102 hyp
  have e1 : V₁ = U₁ := hu1 V₁ hV₁
  have e2 : V₂ = U₂ := hu2 V₂ hV₂
  rw [← e1, ← e2] at h12
  exact
    { elem := isElemAbelian_fsuV hyp
      two_le := hyp.one_lt
      le_normalizer := L_le_normalizer_fsuV hyp
      commutator_eq := commutator_fsuV_eq_self hyp
      nat := natModuleOf_fsuV h1102 hyp
      kind := hk
      cL_two := isPGroup_cL_fsuV h1102 hyp
      le_X := le_top
      normalizer_le := inf_le_right.trans (normalizer_fsuV_le h331 hyp)
      sylow := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
      T_le_V := T_le_normalizer_fsuV T I
      T_le_L := hyp.normal
      cV_le := IsVi.cV_le hV₁
      le₁₂ := h12
      le₂ := IsVi.le_fsuV hV₂
      stable₁ := IsVi.isEndStable hV₁
      stable₂ := IsVi.isEndStable hV₂
      index₁ := by rw [IsVi.relIndex_eq hV₁, mul_one]
      index₂ := IsVi.relIndex_eq hV₂
      T_le_V₁ := IsVi.le_normalizer hV₁
      T_le_V₂ := IsVi.le_normalizer hV₂ }

end CFSG.Quasithin.Vol2.Ch11.SecB
