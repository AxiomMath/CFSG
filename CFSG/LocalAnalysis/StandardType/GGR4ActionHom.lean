module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType

open CFSG.Assembly

private noncomputable def ahm_rho {G : Type} [Group G] {L : Subgroup G} {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp
    ((MulAut.mapQuotient (Subgroup.center ↥L)).comp (Subgroup.normalizerMonoidHom L))

private theorem ahm_rho_mk {G : Type} [Group G] {L : Subgroup G} {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (n : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    ahm_rho θ n (θ (QuotientGroup.mk l)) =
      θ (QuotientGroup.mk ((Subgroup.normalizerMonoidHom L n) l)) := by
  show (MulAut.congr θ) (MulAut.mapQuotient (Subgroup.center ↥L)
      (Subgroup.normalizerMonoidHom L n)) (θ (QuotientGroup.mk l)) = _
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mapQuotient_mk]

private theorem ahm_x_centralizer {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hCfg : GGConfig 3 B Bs x L D J) :
    x ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hCfg.tableB_facts.2.2.2.1 hl)

theorem ggR4_actionHom {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hCfg : GGConfig 3 B Bs x L D J) (hperf : commutator ↥L = ⊤)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut R,
      (∀ (b : G) (hb : b ∈ Bs), ρ ⟨b, hBsN hb⟩ ∈ I) ∧
        (∀ l : ↥L, ρ ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
          MulAut.conj (θ (QuotientGroup.mk l))) ∧
        ∀ (b : G) (hb : b ∈ Bs), ρ ⟨b, hBsN hb⟩ = 1 ↔ b ∈ Subgroup.zpowers x := by
  refine ⟨ahm_rho θ, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hBs3 b⁻¹ (Bs.inv_mem hb)
    have hρφ : ahm_rho θ ⟨b, hBsN hb⟩ = φ := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      rw [ahm_rho_mk]
      symm
      apply hφ
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp
    rwa [hρφ]
  · intro l
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hnm : Subgroup.normalizerMonoidHom L ⟨(l : G), Subgroup.le_normalizer l.2⟩ m
        = l * m * l⁻¹ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L
        ⟨(l : G), Subgroup.le_normalizer l.2⟩ m)
    rw [ahm_rho_mk, hnm, MulAut.conj_apply]
    have hmk : (QuotientGroup.mk (l * m * l⁻¹) : ↥L ⧸ Subgroup.center ↥L)
        = QuotientGroup.mk l * QuotientGroup.mk m * (QuotientGroup.mk l)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hmk, map_mul, map_mul, map_inv]
  · intro b hb
    constructor
    · intro hρ
      have h1 : MulAut.mapQuotient (Subgroup.center ↥L)
          (Subgroup.normalizerMonoidHom L ⟨b, hBsN hb⟩) = 1 := by
        apply (MulAut.congr θ).injective
        change ahm_rho θ ⟨b, hBsN hb⟩ = (MulAut.congr θ) 1
        rw [hρ, map_one]
      have hnm : Subgroup.normalizerMonoidHom L ⟨b, hBsN hb⟩ = 1 :=
        CFSG.LocalAnalysis.GLTheoremA.T2021.eq_one_of_mapQuotient_center_eq_one
          hperf _ h1
      have hcent : b ∈ Subgroup.centralizer (L : Set G) := by
        have hmem : ⟨b, hBsN hb⟩ ∈ (Subgroup.normalizerMonoidHom L).ker := by
          rw [MonoidHom.mem_ker]
          exact hnm
        rw [Subgroup.normalizerMonoidHom_ker] at hmem
        exact Subgroup.mem_subgroupOf.mp hmem
      have hthis : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hb, hcent⟩
      rwa [hCfg.bstar_inf_centralizer_L] at hthis
    · intro hbz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
      have hxBs : x ∈ Bs := hCfg.tableB_facts.2.2.1
      have hnmx : Subgroup.normalizerMonoidHom L ⟨x, hBsN hxBs⟩ = 1 := by
        ext l
        have hcomm : (l : G) * x = x * (l : G) :=
          (Subgroup.mem_centralizer_iff.mp (ahm_x_centralizer hCfg)) (l : G) l.2
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply, ← hcomm]
        simp
      have hρx : ahm_rho θ ⟨x, hBsN hxBs⟩ = 1 := by
        change (MulAut.congr θ) (MulAut.mapQuotient (Subgroup.center ↥L)
          (Subgroup.normalizerMonoidHom L ⟨x, hBsN hxBs⟩)) = 1
        rw [hnmx, map_one, map_one]
      have hb_eq : (⟨b, hBsN hb⟩ : ↥(Subgroup.normalizer (L : Set G)))
          = (⟨x, hBsN hxBs⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ k := by
        ext
        simpa using hk.symm
      rw [hb_eq, map_zpow, hρx]
      simp

end CFSG.StandardType

end
