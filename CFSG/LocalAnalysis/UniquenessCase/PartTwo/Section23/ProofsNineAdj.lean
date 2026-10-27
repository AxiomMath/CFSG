module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotLarge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem Hinf_inf_L_ne_bot_of_not_barImage_le_rep_ker (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (d : S23_9_A0Data D Ch c)
    (hnot : ¬ barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker) :
    Hinf (D.M ⊓ c.L) ≠ ⊥ := by
  intro hbot
  refine hnot ?_
  rw [hbot]
  simp [barImage]

theorem map_Hinf_inf_ne_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hne : Hinf (D.M ⊓ c.L) ≠ ⊥) :
    ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) ≠ ⊥ := by
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  have hKL : K ≤ c.L :=
    (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  intro hbot
  have hKle : K ≤ ((c.phiL hV).ker).map c.L.subtype := by
    intro x hx
    have hxsub : (⟨x, hKL hx⟩ : ↥c.L) ∈ K.subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxmap : c.phiL hV ⟨x, hKL hx⟩ ∈ (K.subgroupOf c.L).map (c.phiL hV) :=
      Subgroup.mem_map_of_mem _ hxsub
    rw [hbot, Subgroup.mem_bot] at hxmap
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hKL hx⟩, (by rw [MonoidHom.mem_ker]; exact hxmap), rfl⟩
  haveI hkerSolv : Group.IsSolvable ↥(c.phiL hV).ker := phiL_ker_isSolvable c hV hK hnat
  let g : ↥(c.phiL hV).ker →*
      ↥(c.L.subtype.comp (c.phiL hV).ker.subtype).range :=
    ((c.L.subtype.comp (c.phiL hV).ker.subtype)).rangeRestrict
  have hg : Function.Surjective g := MonoidHom.rangeRestrict_surjective _
  have hrange : (c.L.subtype.comp (c.phiL hV).ker.subtype).range =
      ((c.phiL hV).ker).map c.L.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hmapSolv : Group.IsSolvable ↥(((c.phiL hV).ker).map c.L.subtype) := by
    rw [← hrange]
    exact Group.isSolvable_of_surjective (f := g) hg
  haveI : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKle)
      (Subgroup.inclusion_injective hKle)
  have hKperf : ⁅K, K⁆ = K := by
    simpa [K] using uc22p21c_Hinf_perfect (D.M ⊓ c.L)
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr (by simpa [K] using hne)
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance

theorem n_eq_pRank_of_pointStab (c : Ctx23L D Ch) (h52 : S23_5_2 D Ch)
    (hPS : S23_9_PointStab D Ch) (h1930 : H1930 D)
    (hKne : Hinf (D.M ⊓ c.L) ≠ ⊥) :
    c.n = CFSG.Open.pRank 2 D.Z := by
  rcases h52 h1930 c with h | ⟨-, hOm, -⟩
  · exact h
  · exact absurd ((hPS h1930 c).2.2 _ hOm) hKne

theorem a1_disj_of_cn_eq (c : Ctx23L D Ch) {n r : ℕ} (hcn : c.n = n)
    (h : (∃ s : ℕ, s ∣ c.n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, c.n = 2 ^ k ∧ r = 3)) :
    (∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, n = 2 ^ k ∧ r = 3) := by
  simpa [hcn] using h

theorem Hinf_stabilizer_sylowStar_eq_map_Hinf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)))) =
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  rw [show ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
      Set (c.W hV)) = ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) by rw [hℓ]]
  exact (c.map_Hinf_inf_eq hV h4 h1930).symm

theorem phiL_mem_Y0_of_mem_B0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {b : G} (hb : b ∈ c.B0) : c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈ c.Y0 hV :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (c.hB0.1 hb))

theorem phiL_ne_one_of_mem_B0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {b : G}
    (hb : b ∈ c.B0) (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) :
    c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ≠ 1 := by
  intro h1
  have hbV : b ∈ Subgroup.centralizer (c.V : Set G) :=
    (c.phiL_eq_one_iff hV ⟨b, c.hL0L (c.hB0.1 hb)⟩).1 h1
  have hZV : D.Z ≤ c.V := by
    rw [Ctx23L.V, conjClosure]
    exact le_iSup₂_of_le D.Z ⟨1, c.N.one_mem, by ext; simp⟩ le_rfl
  exact hbZ (Subgroup.centralizer_le hZV hbV)

theorem phiL_mem_stabilizer_of_mem_B0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) {b : G} (hb : b ∈ c.B0) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈ MulAction.stabilizer ↥(c.H hV)
      (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  exact (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 ⟨b, c.hL0L (c.hB0.1 hb)⟩).2 (c.hBM hb)

theorem phiL_mem_Y0_inf_stabilizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) {b : G} (hb : b ∈ c.B0) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈ c.Y0 hV ⊓ MulAction.stabilizer ↥(c.H hV)
      (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  exact Subgroup.mem_inf.mpr
    ⟨c.phiL_mem_Y0_of_mem_B0 hV hb, c.phiL_mem_stabilizer_of_mem_B0 hV h4 h1930 hb⟩

theorem orderOf_phiL_eq_of_mem_B0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {b : G}
    (hb : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hborder : orderOf b = r)
    (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) :
    orderOf (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩) = r := by
  have htne : c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ≠ 1 :=
    c.phiL_ne_one_of_mem_B0 hV hb hbZ
  have hbL : b ∈ c.L := c.hL0L (c.hB0.1 hb)
  have hdvd : orderOf (c.phiL hV ⟨b, hbL⟩) ∣ r := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow]
    have hbpow : (⟨b, hbL⟩ : ↥c.L) ^ r = 1 := by
      apply Subtype.ext
      show b ^ r = 1
      simpa [hborder] using pow_orderOf_eq_one b
    rw [hbpow, map_one]
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
  · exact absurd (orderOf_eq_one_iff.mp h1) htne
  · exact hr'

theorem phiL_not_mem_fixingSubgroup (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {b : G}
    (hb : b ∈ c.B0) (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∉
      fixingSubgroupOf ↥(c.H hV) (c.W hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  intro h
  have hCH : c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈ c.CH hV := h
  exact hbZ ((c.phiL_mem_CH_iff hV ⟨b, c.hL0L (c.hB0.1 hb)⟩).1 hCH)

theorem exists_KAdj_data_of (c : Ctx23L D Ch) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h52 : S23_5_2 D Ch) (hPS : S23_9_PointStab D Ch)
    (h209 : S20_9 D) (hK : KOrdNatural) (hA : KTab23a)
    (h1930 : H1930 D) (hn : 3 ≤ CFSG.Open.pRank 2 D.Z) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hnot : ¬ barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker)
    {b : G} (hb : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hborder : orderOf b = r) (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G))
    (hcase : (∃ s : ℕ, s ∣ c.n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, c.n = 2 ^ k ∧ r = 3))
    (hKAdj : KAdj) :
    ∃ m : ℕ, (m = CFSG.Open.pRank 2 D.Z ∨ m = 2 * CFSG.Open.pRank 2 D.Z ∨
      (CFSG.Open.pRank 2 D.Z = 2 * m ∧ IsSUn ↥(c.H hV) 4 m ∧
        NatSUn (c.H hV) ⊤ ⊥ 4 m)) ∧
    ∃ X₁ X₂ : Subgroup ↥(c.H hV),
      X₁ ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) ∧
      X₂ ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) ∧
      (∀ N : Subgroup ↥(c.H hV), N ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) →
        ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) ≤
          Subgroup.normalizer (N : Set ↥(c.H hV)) → X₁ ≤ N → X₂ ≤ N →
        N = ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV)) ∧
      ∀ X : Subgroup ↥(c.H hV), (X = X₁ ∨ X = X₂) →
        IsSLn ↥X 2 m ∧
          c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ ∈
            Subgroup.normalizer (X : Set ↥(c.H hV)) ∧
          ∃ u ∈ X, orderOf u = r ∧ ∀ x ∈ X,
            c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩ * x *
                (c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩)⁻¹ = u * x * u⁻¹ := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) := by
    rcases Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c with ⟨_, h⟩
    exact h
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  have hKstar_eq : Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)))) = ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) :=
    c.Hinf_stabilizer_sylowStar_eq_map_Hinf hV hA h4 h1930 hnat
  have hKne := c.Hinf_inf_L_ne_bot_of_not_barImage_le_rep_ker hV d hnot
  have hmapne := c.map_Hinf_inf_ne_bot hV hK hnat hKne
  have hKstar_ne : Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)))) ≠ ⊥ := fun h => hmapne (hKstar_eq ▸ h)
  have hcn : c.n = CFSG.Open.pRank 2 D.Z :=
    c.n_eq_pRank_of_pointStab h52 hPS h1930 hKne
  have hcase' : (∃ s : ℕ, s ∣ CFSG.Open.pRank 2 D.Z ∧ Odd s ∧ 1 < s ∧
      r ∣ 2 ^ s - 1) ∨ (∃ k : ℕ, CFSG.Open.pRank 2 D.Z = 2 ^ k ∧ r = 3) :=
    c.a1_disj_of_cn_eq hcn hcase
  let t : ↥(c.H hV) := c.phiL hV ⟨b, c.hL0L (c.hB0.1 hb)⟩
  have htmem : t ∈ c.Y0 hV ⊓ MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV))) := by
    simpa only [t, hℓ] using c.phiL_mem_Y0_inf_stabilizer hV h4 h1930 hb
  have htord : orderOf t = r := c.orderOf_phiL_eq_of_mem_B0 hV hb hr hborder hbZ
  have htnot : t ∉ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV))) := by
    simpa only [t, hℓ] using c.phiL_not_mem_fixingSubgroup hV hb hbZ
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L c.hL.1 c.L0).1 ⟨c.hL0, c.hL0L⟩
  have hmin := c.minimal_good_Pstar hV hA h4 h1930 hnat P hP
  have hY0 : Hinf (Ctx23L.Pstar c hV P) = c.Y0 hV := c.Hinf_Pstar hV P hP hL0P
  obtain ⟨m, hm, X₁, X₂, hX₁, hX₂, hNclause, hXprop⟩ :=
    hKAdj (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV) hn
      (c.sylowStar hV) hKstar_ne (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
      (c.sylowStar_le_Tstar hV) (Ctx23L.Pstar c hV P) hmin
      r hr hr2 hcase' t (hY0 ▸ htmem) htord htnot
  refine ⟨m, hm, X₁, X₂, ?_, ?_, ?_, ?_⟩
  · rwa [hKstar_eq] at hX₁
  · rwa [hKstar_eq] at hX₂
  · intro N hN hnorm h1 h2
    have hN' : N ≤ Hinf (MulAction.stabilizer ↥(c.H hV)
        (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
          Set (c.W hV)))) := by rwa [hKstar_eq]
    have hnorm' : Hinf (MulAction.stabilizer ↥(c.H hV)
        (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
          Set (c.W hV)))) ≤ Subgroup.normalizer (N : Set ↥(c.H hV)) := by
      rwa [hKstar_eq]
    have := hNclause N hN' hnorm' h1 h2
    rwa [hKstar_eq] at this
  · intro X hX
    exact hXprop X hX

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
