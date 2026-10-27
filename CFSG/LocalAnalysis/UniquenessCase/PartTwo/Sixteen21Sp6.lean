module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

theorem nonempty_lStar_equiv_lBar (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    Nonempty (↥(lStar D.M V₀ V hV L) ≃* ↥(lBar V₀ V hV L)) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hLs : L ≤ stabTil V₀ V := h.le.trans hMs
  have hLs₁ : L ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    h.le.trans (s15_T7_le_stabTil_v1Sub h)
  let ψ₀ : ↥L →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hLs)
  let ψ₁ : ↥L →* MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV) :=
    (actTil (v1Sub D.M V₀ V hV L) V hV).comp (Subgroup.inclusion hLs₁)
  have hr₀ : ψ₀.range = barSub V₀ V hV L := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLs x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  have hr₁ : ψ₁.range = barSub (v1Sub D.M V₀ V hV L) V hV L := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLs₁ x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  have hker₀ : ψ₀.ker = (F11.CTilde D.M V₀ V).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hx
      exact ⟨h.le x.2, hLs x.2,
        by simpa [ψ₀, MonoidHom.comp_apply, Subgroup.inclusion] using hx⟩
    · rintro ⟨-, hh, h1⟩
      simpa [ψ₀, MonoidHom.comp_apply, Subgroup.inclusion] using h1
  have hker₁ : ψ₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hx
      exact ⟨h.le x.2, hLs₁ x.2,
        by simpa [ψ₁, MonoidHom.comp_apply, Subgroup.inclusion] using hx⟩
    · rintro ⟨-, hh, h1⟩
      simpa [ψ₁, MonoidHom.comp_apply, Subgroup.inclusion] using h1
  have hker : ψ₀.ker = ψ₁.ker := by
    rw [hker₀, hker₁, ← fifteen_two_cent D h1217 h hV]
  exact ⟨(MulEquiv.subgroupCongr hr₁).symm.trans
    ((QuotientGroup.quotientKerEquivRange ψ₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        ((QuotientGroup.quotientKerEquivRange ψ₀).trans (MulEquiv.subgroupCongr hr₀))))⟩

theorem exists_orderOf_fix_of_index_lt {U : Type*} [Group U] [Finite U]
    {X : Subgroup (MulAut U)} {p : ℕ} (hp : p.Prime)
    (hX : ∀ H : Subgroup X, H.index < Nat.card U → p ∣ Nat.card H) (hU : 1 < Nat.card U)
    (u : U) : ∃ φ ∈ X, orderOf φ = p ∧ φ u = u := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp hU
  haveI : Finite X := inferInstance
  have horbit : (MulAction.orbit X u).ncard < Nat.card U := by
    refine Set.ncard_lt_card ?_
    intro huniv
    rcases eq_or_ne u 1 with rfl | hu
    · obtain ⟨w, hw⟩ := exists_ne (1 : U)
      have hwmem : w ∈ MulAction.orbit X (1 : U) := by rw [huniv]; exact Set.mem_univ w
      rw [MulAction.mem_orbit_iff] at hwmem
      obtain ⟨φ, hφ⟩ := hwmem
      exact hw (by simpa [Subgroup.smul_def, MulAut.smul_def] using hφ.symm)
    · have h1mem : (1 : U) ∈ MulAction.orbit X u := by rw [huniv]; exact Set.mem_univ 1
      rw [MulAction.mem_orbit_iff] at h1mem
      obtain ⟨φ, hφ⟩ := h1mem
      have hφ' : ((φ : X) : MulAut U) u = 1 := hφ
      exact hu (((φ : X) : MulAut U).injective (by rw [hφ', map_one]))
  have hidx : (MulAction.stabilizer X u).index < Nat.card U := by
    rw [MulAction.index_stabilizer X u]
    exact horbit
  have hdvd : p ∣ Nat.card (MulAction.stabilizer X u) := hX _ hidx
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((s : X) : MulAut U), (s : X).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe (H := X) (a := (s : X)),
      Subgroup.orderOf_coe (H := MulAction.stabilizer X u) (a := s), hs]
  · have hsfix : s • u = u := MulAction.mem_stabilizer_iff.mp s.2
    simpa [Subgroup.smul_def, MulAut.smul_def] using hsfix

theorem card_vStar_of_case8 {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Case167_8 D V₀ V hV L) : Nat.card (vStar D.M V₀ V hV L) = 2 ^ 8 := by
  have hsq : ∀ w : ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)), w ^ 2 = 1 := by
    intro w
    refine Subtype.ext ?_
    simpa using s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
      (w : vStar D.M V₀ V hV L)
  have hcard :=
    CFSG.Quasithin.card_eq_two_pow_rk (V := ↥(⊤ : Subgroup (vStar D.M V₀ V hV L))) hsq
  rw [← Subgroup.card_top (G := vStar D.M V₀ V hV L), hcard, hc.2.1]

theorem forall_fix_vStar_of_case8 (hSp : RSp6SmallIndex) {D : Data G} (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h151 : Hyp151 D V₀ V L)
    (hc : Case167_8 D V₀ V hV L) :
    ∀ w : vStar D.M V₀ V hV L, ∃ φ ∈ lStar D.M V₀ V hV L, orderOf φ = 3 ∧ φ w = w := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e₂⟩⟩ := hc.1
  letI := hKfield
  letI := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨e₁⟩ := nonempty_lStar_equiv_lBar D h1217 h151 hV
  have e₂' : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 K) := e₂
  let e : ↥(lStar D.M V₀ V hV L) ≃* ↥(StatedSp 3 K) := e₁.trans e₂'
  intro w
  refine exists_orderOf_fix_of_index_lt (U := vStar D.M V₀ V hV L)
    (X := lStar D.M V₀ V hV L) (p := 3) Nat.prime_three ?_ ?_ w
  · intro H hH
    have hH' : H.index < 256 := by
      rwa [card_vStar_of_case8 hV hc] at hH
    have hle : (H.map (e : ↥(lStar D.M V₀ V hV L) →* ↥(StatedSp 3 K))).index ≤ 255 := by
      rw [Subgroup.index_map_equiv H e]
      omega
    have hdvd := hSp K hK2 (H.map (e : ↥(lStar D.M V₀ V hV L) →* ↥(StatedSp 3 K))) hle
    rwa [Subgroup.card_map_of_injective (K := H) e.injective] at hdvd
  · rw [card_vStar_of_case8 hV hc]
    norm_num

theorem one_le_pRank_of_case8 (hSp : RSp6SmallIndex) {D : Data G} (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h16 : Hyp16 D V₀ V)
    (h151 : Hyp151 D V₀ V L) (hc : Case167_8 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  have h3 : 3 ∈ D.sig := by rw [hc.2.2.1]; simp
  exact one_le_pRank_of_forall_fix_vStar hV h16 h151 Nat.prime_three (by norm_num)
    (D.sig_rank 3 h3) (forall_fix_vStar_of_case8 hSp h1217 hV h151 hc)

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
