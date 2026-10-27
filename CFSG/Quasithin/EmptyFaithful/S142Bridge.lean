module

public import CFSG.Quasithin.Vol2.Ch12Sec8Setup
public import CFSG.Quasithin.EmptyFaithful.S14118RestStar
public import CFSG.Quasithin.Background.G2
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
private theorem s142b_conjAct_mul (V : Subgroup G) {x y : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x * y, Subgroup.mul_mem _ hx hy⟩ = conjAct V ⟨x, hx⟩ * conjAct V ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

omit [Finite G] in
private theorem s142b_normalizer_le_normalizer_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
    simpa using this
  have hcv := (Subgroup.mem_centralizer_iff.mp hc) _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcv]
    _ = g * c * g⁻¹ * v := by group

namespace Hyp1421

theorem isMf (h : Hyp1421 G T M) :
    IsMf T (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) M :=
  ⟨h.m_max, h.ne_centralizer, fun M' hM' _ => h.m_greatest M' hM'⟩

theorem hyp14118 (h11 : StageLemma14111) (h : Hyp1421 G T M) :
    Hyp14118 T (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) M :=
  ⟨h.toQTFE14, h11 G T _ h.toQTFE14, h.isMf, h.rank_two⟩

theorem inf_centralizer_eq_pCoreOf (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp1421 G T M) :
    (yOfL22 T M ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) = pCoreOf 2 (yOfL22 T M ⊔ T) := by
  have hyp := h.hyp14118 h11
  set V := VZ T M with hVdef
  set Y := yOfL22 T M with hYdef
  obtain ⟨P, -, -, hP3, hPT, hYP, hYC, -⟩ := hyp.s3_data h113 rfl rfl
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hyp.le_normalizer
  have hTM : T ≤ M := hyp.inM.2
  have hYM : Y ≤ M := yOfL22_le T M
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTM.trans (le_normalizer_yOfL22 T M)
  have hXM : Y ⊔ T ≤ M := sup_le hYM hTM
  have hT2 := hyp.card_autOn_T
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hsylM : IsSylowTwoOf T M := by
    have := isSylowTwoOf_of_sylow S (hS ▸ hTM)
    rwa [hS] at this
  have hOMT : pCoreOf 2 M ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylM
  have hinf : P ⊓ autOn T V = ⊥ := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ autOn T V ≤ P)
    have h2 := Subgroup.card_dvd_of_le (inf_le_right : P ⊓ autOn T V ≤ autOn T V)
    rw [hP3] at h1
    rw [hT2] at h2
    have : Nat.card ↥(P ⊓ autOn T V) = 1 := by
      have h3 : Nat.card ↥(P ⊓ autOn T V) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
      simpa using h3
    exact Subgroup.eq_bot_of_card_eq _ this
  apply le_antisymm
  ·
    have hCT : (Y ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
      rintro x ⟨hx, hxC⟩
      have hx' : x ∈ ((T ⊔ Y : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right T Y hTY] at hx'
      obtain ⟨t, ht, y, hy, rfl⟩ := hx'
      have htN : t ∈ Subgroup.normalizer (V : Set G) := hMV (hTM ht)
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := hMV (hYM hy)
      have h1 : conjAct V ⟨t * y, Subgroup.mul_mem _ htN hyN⟩ = 1 :=
        A4.conjAct_eq_one_iff.mpr hxC
      rw [s142b_conjAct_mul V htN hyN] at h1
      have hyT : conjAct V ⟨y, hyN⟩ ∈ P ⊓ autOn T V := by
        refine ⟨hYP ▸ mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩, ?_⟩
        have : conjAct V ⟨y, hyN⟩ = (conjAct V ⟨t, htN⟩)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact Subgroup.inv_mem _ (mem_autOn_iff_exists.mpr ⟨t, htN, ht, rfl⟩)
      rw [hinf, Subgroup.mem_bot] at hyT
      have hyC : y ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp hyT
      exact T.mul_mem ht (hOMT (hYC y hy hyC))
    have hC2 : IsPGroup 2 ↥((Y ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) :=
      h.sylow.1.to_le hCT
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hC2
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, s142b_normalizer_le_normalizer_centralizer V (hMV (hXM hx))⟩
  ·
    set R := pCoreOf 2 (Y ⊔ T) with hRdef
    have hRX : R ≤ Y ⊔ T := pCoreOf_le 2 _
    have hRN : R ≤ Subgroup.normalizer (V : Set G) := (hRX.trans hXM).trans hMV
    have hXtop : autOn (Y ⊔ T) V = ⊤ := by
      rw [eq_top_iff, ← hPT, ← hYP]
      exact sup_le (A4.autOn_mono le_sup_left) (A4.autOn_mono le_sup_right)
    have hQ2 : IsPGroup 2 (autOn R V) := by
      unfold autOn
      exact ((pCoreOf_isPGroup 2 (Y ⊔ T)).of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm).map _
    have hQn : autOn M V ≤ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) := by
      rw [hyp.autOn_eq_top, ← hXtop]
      refine le_normalizer_of_conj_mem fun σ hσ τ hτ => ?_
      obtain ⟨g, hgN, hgX, rfl⟩ := mem_autOn_iff_exists.mp hσ
      obtain ⟨r, hrN, hrR, rfl⟩ := mem_autOn_iff_exists.mp hτ
      have hgr : g * r * g⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (Y ⊔ T) hgX) r).mp hrR
      refine mem_autOn_iff_exists.mpr ⟨g * r * g⁻¹, hRN hgr, hgr, ?_⟩
      have e : (⟨g * r * g⁻¹, hRN hgr⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨g, hgN⟩ * ⟨r, hrN⟩ * (⟨g, hgN⟩ : Subgroup.normalizer (V : Set G))⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    have hQ := hyp.eq_bot_of_normal_isPGroup (A4.autOn_mono (hRX.trans hXM)) hQn hQ2
    intro r hr
    refine ⟨hRX hr, ?_⟩
    have hmem : conjAct V ⟨r, hRN hr⟩ ∈ autOn R V := mem_autOn_iff_exists.mpr ⟨r, hRN hr, hr, rfl⟩
    rw [hQ, Subgroup.mem_bot] at hmem
    exact A4.conjAct_eq_one_iff.mp hmem

theorem nonempty_oTwoQuot_mulEquiv (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp1421 G T M) :
    Nonempty (OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3)) := by
  have hyp := h.hyp14118 h11
  set V := VZ T M with hVdef
  set X := yOfL22 T M ⊔ T with hXdef
  obtain ⟨P, -, -, -, hPT, hYP, -, -⟩ := hyp.s3_data h113 rfl rfl
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hyp.le_normalizer
  have hXM : X ≤ M := sup_le (yOfL22_le T M) hyp.inM.2
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXM.trans hMV
  have hC := h.inf_centralizer_eq_pCoreOf h11 h113
  set φ : ↥X →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hXN) with hφ
  have hXtop : autOn X V = ⊤ := by
    rw [eq_top_iff, ← hPT, ← hYP]
    exact sup_le (A4.autOn_mono le_sup_left) (A4.autOn_mono le_sup_right)
  have hsurj : Function.Surjective φ := by
    intro σ
    have hσ : σ ∈ autOn X V := by rw [hXtop]; exact Subgroup.mem_top σ
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_autOn_iff_exists.mp hσ
    exact ⟨⟨x, hxX⟩, rfl⟩
  have hker : CFSG.Open.pCore 2 ↥X = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxO : (x : G) ∈ pCoreOf 2 X := ⟨x, hx, rfl⟩
      rw [← hC] at hxO
      exact A4.conjAct_eq_one_iff.mpr hxO.2
    · intro hx
      have hxC : (x : G) ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp hx
      have hxO : (x : G) ∈ pCoreOf 2 X := by
        rw [← hC]
        exact ⟨x.2, hxC⟩
      obtain ⟨y, hy, hyx⟩ := hxO
      have hyx' : y = x := Subtype.ext hyx
      rwa [← hyx']
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_perm_three hyp.twoReduced.2.2.1 h.rank_two
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)).trans e⟩

theorem hyp1281Two_of_inputs (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp1421 G T M) : Hyp1281Two G T M (yOfL22 T M) :=
  h.hyp1281Two (lemma_14_1_18_four h113 (h.hyp14118 h11) rfl rfl)
    (h.inf_centralizer_eq_pCoreOf h11 h113) (h.nonempty_oTwoQuot_mulEquiv h11 h113)

end Hyp1421

end CFSG.Quasithin
