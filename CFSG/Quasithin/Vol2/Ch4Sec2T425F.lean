module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C
public import CFSG.Quasithin.Vol2.Ch4Sec2T425U

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem normal (c : Inp425 G) : M ≤ Subgroup.normalizer (L : Set G) :=
  (s.lemma_4_2_6_one c).2

theorem le_normalizer_C (c : Inp425 G) :
    M ≤ Subgroup.normalizer (centralizerSection M L (pCoreOf 2 L) : Set G) :=
  le_normalizer_centralizerSection' (s.normal c)

theorem pCoreOf_M_le_C (c : Inp425 G) :
    pCoreOf 2 M ≤ centralizerSection M L (pCoreOf 2 L) := by
  refine (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr ⟨pCoreOf_le 2 M, ?_⟩
  have h1 : ⁅L, pCoreOf 2 M⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((pCoreOf_le 2 M).trans (s.normal c))
  have h2 : ⁅L, pCoreOf 2 M⁆ ≤ pCoreOf 2 M := Subgroup.le_normalizer_iff_commutator_le_right.mp
    (s.hyp.L_le.trans (le_normalizer_pCoreOf 2 M))
  refine (le_inf h1 h2).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 M).to_le inf_le_right))
  exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 M (s.hyp.L_le hx)⟩

theorem pCoreOf_C_ne_bot (c : Inp425 G) :
    pCoreOf 2 (centralizerSection M L (pCoreOf 2 L)) ≠ ⊥ := by
  intro h0
  have hle : pCoreOf 2 M ≤ pCoreOf 2 (centralizerSection M L (pCoreOf 2 L)) :=
    le_pCoreOf_of_le_normalizer 2 (s.pCoreOf_M_le_C c)
      ((centralizerSection_le_left _ _ _).trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  rw [h0] at hle
  exact pCoreOf_ne_bot_of_isTwoLocal s.hyp.maxTwoLocal.1 (le_bot_iff.mp hle)

theorem K_le_C (c : Inp425 G) {K : Subgroup G} (hK : K ∈ cComp M) (hKH : ¬ K ≤ H) :
    K ≤ centralizerSection M L (pCoreOf 2 L) := by
  have hne : K ≠ L := fun he => hKH (he ▸ (s.lemma_4_2_7_one c).2.1)
  have hc := (lemma_1_2_1_two s.hyp.qtke s.hyp.simple s.hyp.nonabelian c.a37
    (pCoreOf_ne_bot_of_isTwoLocal s.hyp.maxTwoLocal.1) hK (s.hyp.mem_cComp c.a37 c.a39) hne).1
  refine (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr ⟨le_of_mem_cComp hK, ?_⟩
  rw [Subgroup.commutator_comm]
  exact hc.trans inf_le_right

theorem J_le_C (c : Inp425 G) {h : G} (hh : h ∈ H) (hhM : h ∉ M) :
    L.map (MulAut.conj h).toMonoidHom ≤ centralizerSection M L (pCoreOf 2 L) := by
  obtain ⟨hJc, hJne, hJH0⟩ := s.conj_h c hh hhM
  have hc := (lemma_1_2_1_two s.hyp.qtke s.hyp.simple s.hyp.nonabelian c.a37
    (pCoreOf_ne_bot_of_isTwoLocal s.inM.1.1) (s.lemma_4_2_7_one c).2.2 hJc (Ne.symm hJne)).1
  exact (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr
    ⟨hJH0.trans ((s.H0_le c).trans inf_le_right), hc.trans inf_le_left⟩

theorem pRank_M_le_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : CFSG.Open.pRank p M ≤ 2 := by
  have h := sqt_iff.mp s.hypC23.sqtk.1 p Fact.out hp2
  rwa [pRank_top_subtype] at h

theorem pRank_C_le_one {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card L) :
    CFSG.Open.pRank p (centralizerSection M L (pCoreOf 2 L)) ≤ 1 := by
  obtain ⟨E, hEC, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank hpf.out.one_lt (centralizerSection M L (pCoreOf 2 L))
  have h1 := T425.succ_le_pRank hp2 s.hyp.perfect hpL hE hcard
    (hEC.trans fun x hx => (mem_centralizerSection.mp hx).2.1)
    (fun x hx l hl => by
      have h := (mem_centralizerSection.mp (hEC hx)).2.2.2 l hl
      have e : x * l * x⁻¹ * l⁻¹ = (l * x * l⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 L).inv_mem h)
    (hEC.trans (centralizerSection_le_left _ _ _)) s.hyp.L_le
  have h2 := s.pRank_M_le_two hp2
  omega

theorem H0_le_sup (c : Inp425 G) {h : G} (hh : h ∈ H) (hhM : h ∉ M) :
    conjClosure L H ≤ L ⊔ L.map (MulAut.conj h).toMonoidHom := by
  have hN : ∀ g ∈ H ⊓ M, g ∈ Subgroup.normalizer (L : Set G) := fun g hg => by
    rw [s.inf_eq c] at hg
    exact hg.2
  have hidx : ((H ⊓ M).subgroupOf H).index = 2 := s.relIndex_eq c
  refine CFSG.Quasithin.conjClosure_le fun g hg l hl => ?_
  by_cases hgM : g ∈ M
  · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hN g ⟨hg, hgM⟩) l).mp hl)
  ·
    have hm : (⟨h, hh⟩ : ↥H)⁻¹ * ⟨g, hg⟩ ∈ (H ⊓ M).subgroupOf H := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      constructor
      · intro hi
        have h1 : (h⁻¹ : G) ∈ M := by simpa using (Subgroup.mem_subgroupOf.mp hi).2
        exact absurd (by simpa using M.inv_mem h1) hhM
      · intro hi
        exact absurd (Subgroup.mem_subgroupOf.mp hi).2 hgM
    set m := h⁻¹ * g with hmdef
    have hmM : m ∈ H ⊓ M :=
      ⟨H.mul_mem (H.inv_mem hh) hg, by simpa using (Subgroup.mem_subgroupOf.mp hm).2⟩
    have hml : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hN m hmM) l).mp hl
    have e : g * l * g⁻¹ = h * (m * l * m⁻¹) * h⁻¹ := by rw [hmdef]; group
    rw [e]
    exact Subgroup.mem_sup_right ⟨m * l * m⁻¹, hml, rfl⟩

end Set425

end CFSG.Quasithin.H13.Ch4
