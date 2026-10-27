module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs
public import CFSG.Quasithin.EmptyFaithful.S141
public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

section General

variable {G : Type*} [Group G]

private theorem le_centralizer_omegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp
    (((Subgroup.closure_le _).mpr fun _ hz => hz.1 :
      quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G)).trans inf_le_right)

private theorem le_normalizer_inf_centralizer {M V : Subgroup G}
    (hV : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
    have h := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * v := by group
  intro g hg
  refine Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hg, ?_⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g (hV hg) c hc, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem (hV hg)) _ hc

variable [Finite G]

theorem exists_mem_cComp_of_not_isSolvable {H : Subgroup G} (hH : ¬ Group.IsSolvable H) :
    ∃ L : Subgroup G, L ∈ cComp H := by
  have hne : perfectCore H ≠ ⊥ := fun h => hH ((isSolvable_iff_perfectCore_eq_bot H).mpr h)
  obtain ⟨L, hL⟩ := (Set.toFinite
    {K : Subgroup G | K ≠ ⊥ ∧ perfectCore K = K ∧ IsSubnormal K H}).exists_minimal
    ⟨perfectCore H, hne, perfectCore_eq_self_of_perfect (perfectCore_perfect H),
      A3.subnormal_perfectCore (IsSubnormal.refl H)⟩
  exact ⟨L, mem_cComp_iff_minimal.mpr hL⟩

theorem quasithinIsLocal_of_mem_cComp (T : Sylow 2 G) {H L : Subgroup G}
    (hH : InH (T : Subgroup G) H) (hL : L ∈ cComp H) : quasithinIsLocal (T : Subgroup G) L := by
  have hLTH : L ⊔ (T : Subgroup G) ≤ H := sup_le (le_of_mem_cComp hL) hH.1
  refine ⟨T.isPGroup', cComp_subset_lFamily hH.1 hL, fun h2 => T.not_dvd_index
    (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right)), ?_⟩
  exact (inH_of_le T le_sup_right hLTH hH).2

end General

theorem stmt1542One_of (h1413 : Input1413) (h1273 : Input127Three)
    {G : Type} [Group G] [Finite G] {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) :
    Stmt1542One G T := by
  intro L hL
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  obtain ⟨Ls, hLs⟩ :=
    (Set.toFinite {K : Subgroup G | quasithinIsLocal (S : Subgroup G) K}).exists_maximal ⟨L, hL⟩
  have hloc : quasithinIsLocal (S : Subgroup G) Ls := hLs.1
  have hLsmax : quasithinIsMaximalLocal (S : Subgroup G) Ls :=
    ⟨hloc, fun K hK hLsK => le_antisymm (hLs.2 hK hLsK) hLsK⟩
  have hH : InH (S : Subgroup G) (Ls ⊔ S) := ⟨le_sup_right, hloc.2.2.2⟩
  have hU : IsTwoReducedIn (Ls ⊔ S) (VZ (S : Subgroup G) (Ls ⊔ S)) :=
    isTwoReducedIn_conjClosure _ S le_sup_right (charTwo_of_inH hyp.qtke.2.1 S hH) le_rfl
  have hcore := h1413 G _ hyp.simple hyp.qtke hyp.sylow hyp.faithful_empty _ hH _ hU
  have hLsC : Ls ≤ Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G) :=
    (le_perfectCore_of_perfect le_sup_left hloc.2.1.2.1).trans
      (hcore.trans (Subgroup.centralizer_le (le_conjClosure _ _)))
  have hHC : Ls ⊔ (S : Subgroup G) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G) :=
    sup_le hLsC (le_centralizer_omegaOneCenter _)
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hCM₁, hCM₂⟩ := hyp.two_centralizer_maximal
  have huniq := h1273 G _ hyp.simple hyp.nonabelian hyp.qtke hyp.sylow Ls hLsmax
  exact hne ((huniq.2 M₁ ⟨hM₁, hHC.trans hCM₁⟩).trans (huniq.2 M₂ ⟨hM₂, hHC.trans hCM₂⟩).symm)

theorem stmt1542Two_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h1 : Stmt1542One G T) : Stmt1542Two G T := by
  intro M hM
  by_contra hns
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  obtain ⟨L, hL⟩ := exists_mem_cComp_of_not_isSolvable hns
  exact h1 L (quasithinIsLocal_of_mem_cComp S (inH_of_inM hM) hL)

theorem stmt15411_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h8 : Stmt1548 G T) (h6 : Stmt1546 G T) :
    Stmt15411 G T := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G) = S := h8
  have hmax : ∀ M : Subgroup G, InM (S : Subgroup G) M → IsOrdMaximal (S : Subgroup G) M :=
    fun M hM => ⟨hM, fun M' hM' hle =>
      hM.1.2 M' hM'.1.1 (le_of_ordLE_of_centralizer_le hle (hCZ.le.trans hM'.2))⟩
  have hnogr : ¬ ∃ M₀ : Subgroup G, InM (S : Subgroup G) M₀ ∧
      ∀ M' : Subgroup G, InM (S : Subgroup G) M' → OrdLE (S : Subgroup G) M' M₀ := by
    rintro ⟨M₀, hM₀, hgr⟩
    obtain ⟨M₁, M₂, hne, hM₁, hM₂, hCM₁, hCM₂⟩ := hyp.two_centralizer_maximal
    have hI₁ : InM (S : Subgroup G) M₁ := ⟨hM₁, hCZ.ge.trans hCM₁⟩
    have hI₂ : InM (S : Subgroup G) M₂ := ⟨hM₂, hCZ.ge.trans hCM₂⟩
    exact hne (((hmax M₁ hI₁).2 M₀ hM₀ (hgr M₁ hI₁)).symm.trans
      ((hmax M₂ hI₂).2 M₀ hM₀ (hgr M₂ hI₂)))
  intro M hM
  have hF : CFSG.QuasithinUnique.CharTwo M := hyp.qtke.2.1 M hM.1.1 ⟨S, hM.2⟩
  refine ⟨le_antisymm (le_inf (pCoreOf_le 2 M) ?_) ?_, hmax M hM, hnogr,
    fun hJ => hnogr ⟨M, hM, h6 M (hmax M hM) hJ⟩⟩
  ·
    exact Subgroup.le_centralizer_iff.mp
      ((conjClosure_le_centerOf_pCoreOf M S hM.2 hF le_rfl).1.trans inf_le_right)
  ·
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf_centralizer (le_normalizer_conjClosure _ M)) ?_
    exact S.isPGroup'.to_le (inf_le_right.trans
      ((Subgroup.centralizer_le (le_conjClosure _ M)).trans hCZ.le))

end CFSG.Quasithin.EmptyFaithfulMultiple
