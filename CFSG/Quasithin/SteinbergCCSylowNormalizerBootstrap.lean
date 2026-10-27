module

public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.SteinbergCCPerfectCentralization
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_of_isSylowOf_of_le {p : ℕ} [Fact p.Prime] {P K B : Subgroup G}
    (hP : IsSylowOf p P K) (hBK : B ≤ K) (hB : IsPGroup p B) (hPB : P ≤ B) : B = P := by
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  have hB' : IsPGroup p (B.subgroupOf K) := hB.of_equiv (subgroupOfEquivOfLe hBK).symm
  have h := S.is_maximal' hB' (by
    rw [hS]
    exact fun x hx => mem_subgroupOf.mpr (hPB (mem_subgroupOf.mp hx)))
  rw [hS] at h
  have h2 := congrArg (Subgroup.map K.subtype) h
  rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hBK,
    inf_of_le_left (hPB.trans hBK)] at h2

variable [Finite G]

theorem prime_residual_sylow_normalizer_core_bootstrap {p : ℕ} (hp : p.Prime)
    {M X : Subgroup G} (hXM : X ≤ M) (hXn : (X.subgroupOf M).Normal)
    (_hX : ∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤)
    {T : Subgroup G} (hT : IsSylowOf p T M)
    (hconf : normalizer (((CFSG.pCore p (X ⊔ T : Subgroup G)).map
      (X ⊔ T).subtype : Subgroup G) : Set G) ≤ M) :
    let Q := (CFSG.pCore p X).map X.subtype
    let R := (CFSG.pCore p (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype
    let CG := ((CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore p X)).comp
      X.normalizerMonoidHom).ker.map (normalizer (X : Set G)).subtype
    let CM := M ⊓ CG
    (∀ g, g ∈ CG ↔ g ∈ normalizer (X : Set G) ∧ ∀ x ∈ X, ⁅x, g⁆ ∈ Q) ∧
      (∀ m, m ∈ CM ↔ m ∈ M ∧ ∀ x ∈ X, ⁅x, m⁆ ∈ Q) ∧
      R = T ⊓ CM ∧ IsSylowOf p R CM ∧ IsSylowOf p R CG ∧
      R = (CFSG.pCore p (normalizer (R : Set G) : Subgroup G)).map
        (normalizer (R : Set G)).subtype ∧
      IsSylowOf p R (⨆ m ∈ M, CFSG.conjugate R m) ∧ X ≤ normalizer (R : Set G) ∧
      ∀ B : Subgroup G, IsPGroup p B → X ≤ normalizer (B : Set G) → R ≤ B → B = R := by
  intro Q R CG CM
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hMN : M ≤ normalizer (X : Set G) := (normal_subgroupOf_iff_le_normalizer hXM).mp hXn
  obtain ⟨hTM, hTp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hQX : Q ≤ X := map_subtype_le _
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup.map _
  have hmemQ : ∀ x : X, (x : G) ∈ Q ↔ x ∈ CFSG.pCore p X := fun x =>
    mem_map_iff_mem (subtype_injective X)
  have hNQ : ∀ g ∈ normalizer (X : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    rintro g hg _ ⟨a, ha, rfl⟩
    have h1 := characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore p X).Characteristic) (X.normalizerMonoidHom ⟨g, hg⟩)
    refine ⟨X.normalizerMonoidHom ⟨g, hg⟩ a, ?_, rfl⟩
    rw [← h1]
    exact mem_map_of_mem _ ha
  have hCG : ∀ g, g ∈ CG ↔ g ∈ normalizer (X : Set G) ∧ ∀ x ∈ X, ⁅x, g⁆ ∈ Q := by
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n.2, fun x hx => ?_⟩
      have h1 := (CFSG.SectionRank.Ccomm.mem_ker_autQuotient (CFSG.pCore p X)).mp
        (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hn)) ⟨x⁻¹, inv_mem hx⟩
      have e : (((⟨x⁻¹, inv_mem hx⟩ : X)⁻¹ * X.normalizerMonoidHom n ⟨x⁻¹, inv_mem hx⟩ : X) :
          G) = ⁅x, (n : G)⁆ := by
        change (x⁻¹)⁻¹ * ((n : G) * x⁻¹ * (n : G)⁻¹) = ⁅x, (n : G)⁆
        rw [commutatorElement_def]
        group
      change ⁅x, (n : G)⁆ ∈ Q
      rw [← e]
      exact (hmemQ _).mpr h1
    · rintro ⟨hg, h⟩
      refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      refine MonoidHom.mem_ker.mp ((CFSG.SectionRank.Ccomm.mem_ker_autQuotient
        (CFSG.pCore p X)).mpr fun x => ?_)
      apply (hmemQ _).mp
      change (x : G)⁻¹ * (g * x * g⁻¹) ∈ Q
      have e : (x : G)⁻¹ * (g * x * g⁻¹) = ⁅(x : G)⁻¹, g⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact h _ (inv_mem x.2)
  have hCM : ∀ m, m ∈ CM ↔ m ∈ M ∧ ∀ x ∈ X, ⁅x, m⁆ ∈ Q := by
    intro m
    rw [mem_inf, hCG]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hMN h.1, h.2⟩⟩
  have hMCM : M ≤ normalizer (CM : Set G) := by
    refine le_normalizer_of_conj_mem fun g hg c hc => ?_
    obtain ⟨hcM, hc⟩ := (hCM c).mp hc
    refine (hCM _).mpr ⟨mul_mem (mul_mem hg hcM) (inv_mem hg), fun x hx => ?_⟩
    have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ X := (mem_normalizer_iff.mp (hMN (inv_mem hg)) x).mp hx
    rw [inv_inv] at hy
    have h1 := hNQ g (hMN hg) _ (hc _ hy)
    have e : g * ⁅g⁻¹ * x * g, c⁆ * g⁻¹ = ⁅x, g * c * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  have hQT : Q ≤ T := by
    have h := eq_of_isSylowOf_of_le hT (sup_le hTM (hQX.trans hXM))
      (hTp.to_sup_of_normal_right' hQp (le_normalizer_of_conj_mem fun t ht q hq =>
        hNQ t (hMN (hTM ht)) q hq)) le_sup_left
    rw [← h]
    exact le_sup_right
  have hQCM : Q ≤ CM := fun q hq => (hCM q).mpr ⟨hXM (hQX hq), fun x hx => by
    rw [commutatorElement_def]
    exact mul_mem (hNQ x (le_normalizer hx) q hq) (inv_mem hq)⟩
  have hXTM : X ⊔ T ≤ M := sup_le hXM hTM
  have hRXT : R ≤ X ⊔ T := map_subtype_le _
  have hRp : IsPGroup p R := CFSG.pCore_isPGroup.map _
  have hRsub : R.subgroupOf (X ⊔ T) = CFSG.pCore p (X ⊔ T : Subgroup G) :=
    comap_map_eq_self_of_injective (subtype_injective _) _
  have hXTR : X ⊔ T ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRXT).mp (by rw [hRsub]; infer_instance)
  have hXR : X ≤ normalizer (R : Set G) := le_sup_left.trans hXTR
  have hloc : ∀ B₀ : Subgroup G, B₀ ≤ M → IsPGroup p B₀ → X ≤ normalizer (B₀ : Set G) →
      B₀ ≤ CM := by
    intro B₀ hB₀M hB₀p hXB₀
    have hXB : X ⊓ B₀ ≤ Q := by
      have hn : ((X ⊓ B₀).subgroupOf X).Normal :=
        (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
          (le_normalizer_of_conj_mem fun g hg z hz => mem_inf.mpr
            ⟨mul_mem (mul_mem hg (mem_inf.mp hz).1) (inv_mem hg),
              (mem_normalizer_iff.mp (hXB₀ hg) z).mp (mem_inf.mp hz).2⟩)
      have h2 : IsPGroup p ((X ⊓ B₀).subgroupOf X) :=
        (hB₀p.to_le inf_le_right).of_equiv (subgroupOfEquivOfLe inf_le_left).symm
      have h3 := le_pCore_of_normal_of_isPGroup hn h2
      intro z hz
      exact ⟨⟨z, (mem_inf.mp hz).1⟩, h3 (mem_subgroupOf.mpr hz), rfl⟩
    intro b hb
    refine (hCM b).mpr ⟨hB₀M hb, fun x hx => hXB (mem_inf.mpr ⟨?_, ?_⟩)⟩
    · rw [commutatorElement_def, mul_assoc x b, mul_assoc x]
      exact mul_mem hx ((mem_normalizer_iff.mp (hMN (hB₀M hb)) _).mp (inv_mem hx))
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (hXB₀ hx) b).mp hb) (inv_mem hb)
  have hSR : T ⊓ CM ≤ R := by
    have hSXT : T ⊓ CM ≤ X ⊔ T := inf_le_left.trans le_sup_right
    have hXS : ∀ x ∈ X, ∀ s ∈ T ⊓ CM, x * s * x⁻¹ ∈ T ⊓ CM := by
      intro x hx s hs
      have hc : ⁅x, s⁆ ∈ Q := ((hCM s).mp (mem_inf.mp hs).2).2 x hx
      rw [show x * s * x⁻¹ = ⁅x, s⁆ * s by rw [commutatorElement_def]; group]
      exact mul_mem (mem_inf.mpr ⟨hQT hc, hQCM hc⟩) hs
    have hTS : ∀ t ∈ T, ∀ s ∈ T ⊓ CM, t * s * t⁻¹ ∈ T ⊓ CM := fun t ht s hs =>
      mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hs).1) (inv_mem ht),
        (mem_normalizer_iff.mp (hMCM (hTM ht)) s).mp (mem_inf.mp hs).2⟩
    have hSn : ((T ⊓ CM).subgroupOf (X ⊔ T)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hSXT).mpr
        (sup_le (le_normalizer_of_conj_mem hXS) (le_normalizer_of_conj_mem hTS))
    have hS2 : IsPGroup p ((T ⊓ CM).subgroupOf (X ⊔ T)) :=
      (hTp.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hSXT).symm
    have h1 := le_pCore_of_normal_of_isPGroup hSn hS2
    intro s hs
    exact ⟨⟨s, hSXT hs⟩, h1 (mem_subgroupOf.mpr hs), rfl⟩
  have hRCM : R ≤ CM := hloc R (hRXT.trans hXTM) hRp hXR
  have hRT : R ≤ T := by
    have h := eq_of_isSylowOf_of_le hT (sup_le hTM (hRXT.trans hXTM))
      (hTp.to_sup_of_normal_right' hRp (le_sup_right.trans hXTR)) le_sup_left
    rw [← h]
    exact le_sup_right
  have hR : R = T ⊓ CM := le_antisymm (le_inf hRT hRCM) hSR
  have hRsylM : IsSylowOf p R CM := by
    rw [hR]
    exact hT.inf_of_le_normalizer inf_le_left hMCM
  have hmaxM : ∀ B₀ : Subgroup G, B₀ ≤ M → IsPGroup p B₀ → X ≤ normalizer (B₀ : Set G) →
      R ≤ B₀ → B₀ = R := fun B₀ hB₀M hB₀p hXB₀ hRB₀ =>
    eq_of_isSylowOf_of_le hRsylM (hloc B₀ hB₀M hB₀p hXB₀) hB₀p hRB₀
  have hmax : ∀ B : Subgroup G, IsPGroup p B → X ≤ normalizer (B : Set G) → R ≤ B → B = R := by
    intro B hBp hXB hRB
    have hNB : B ⊓ normalizer (R : Set G) = R := by
      refine hmaxM _ (inf_le_right.trans hconf) (hBp.to_le inf_le_left) ?_
        (le_inf hRB le_normalizer)
      refine le_normalizer_of_conj_mem fun x hx z hz => mem_inf.mpr
        ⟨(mem_normalizer_iff.mp (hXB hx) z).mp (mem_inf.mp hz).1, ?_⟩
      exact mul_mem (mul_mem (hXR hx) (mem_inf.mp hz).2) (inv_mem (hXR hx))
    by_contra hne
    have hBp' : IsPGroup p B := hBp
    have hlt : R.subgroupOf B < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm (fun b hb => ?_) hRB)
      have h1 : (⟨b, hb⟩ : B) ∈ R.subgroupOf B := htop ▸ mem_top _
      exact mem_subgroupOf.mp h1
    have h1 := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition
      (hBp'.of_equiv (MulEquiv.refl _)) hlt
    rw [← subgroupOf_normalizer_eq hRB] at h1
    have h2 : (normalizer (R : Set G)).subgroupOf B = R.subgroupOf B := by
      rw [← inf_subgroupOf_left, hNB]
    exact absurd h1 (by rw [h2]; exact lt_irrefl _)
  have hRO : R = (CFSG.pCore p (normalizer (R : Set G) : Subgroup G)).map
      (normalizer (R : Set G)).subtype := by
    set O := (CFSG.pCore p (normalizer (R : Set G) : Subgroup G)).map
      (normalizer (R : Set G)).subtype with hO
    have hON : O ≤ normalizer (R : Set G) := map_subtype_le _
    have hOsub : O.subgroupOf (normalizer (R : Set G)) =
        CFSG.pCore p (normalizer (R : Set G) : Subgroup G) :=
      comap_map_eq_self_of_injective (subtype_injective _) _
    have hNO : normalizer (R : Set G) ≤ normalizer (O : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hON).mp (by rw [hOsub]; infer_instance)
    have hRO : R ≤ O := by
      have hn : (R.subgroupOf (normalizer (R : Set G))).Normal :=
        (normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl
      have h1 := le_pCore_of_normal_of_isPGroup hn
        (hRp.of_equiv (subgroupOfEquivOfLe le_normalizer).symm)
      intro r hr
      exact ⟨⟨r, le_normalizer hr⟩, h1 (mem_subgroupOf.mpr hr), rfl⟩
    exact (hmaxM O (hON.trans hconf) (CFSG.pCore_isPGroup.map _) (hXR.trans hNO) hRO).symm
  have hCMCG : CM ≤ CG := inf_le_right
  have hRsylG : IsSylowOf p R CG := by
    obtain ⟨S, hS⟩ := (hRp.of_equiv (subgroupOfEquivOfLe (hRCM.trans hCMCG)).symm :
      IsPGroup p (R.subgroupOf CG)).exists_le_sylow
    have hQR : Q ≤ R := hR ▸ le_inf hQT hQCM
    have hRS : R ≤ (S : Subgroup CG).map CG.subtype := fun r hr =>
      ⟨⟨r, hRCM.trans hCMCG hr⟩, hS (mem_subgroupOf.mpr hr), rfl⟩
    have hXS : X ≤ normalizer (((S : Subgroup CG).map CG.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_of_conj_mem fun x hx y hy => ?_
      obtain ⟨y', hy', rfl⟩ := hy
      have hc : ⁅x, (y' : G)⁆ ∈ Q := ((hCG y').mp y'.2).2 x hx
      change x * (y' : G) * x⁻¹ ∈ _
      rw [show x * (y' : G) * x⁻¹ = ⁅x, (y' : G)⁆ * y' by rw [commutatorElement_def]; group]
      exact mul_mem (hRS (hQR hc)) ⟨y', hy', rfl⟩
    have h1 := hmax _ (S.isPGroup'.map _) hXS hRS
    rw [← h1]
    exact ⟨S, rfl⟩
  have hJ : IsSylowOf p R (⨆ m ∈ M, CFSG.conjugate R m) := by
    refine hRsylM.of_le ?_ (iSup₂_le fun m hm => ?_)
    · have h1 : CFSG.conjugate R 1 = R := by
        ext z
        rw [CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem, one_mul, inv_one,
          mul_one]
      calc R = CFSG.conjugate R 1 := h1.symm
        _ ≤ ⨆ m ∈ M, CFSG.conjugate R m :=
          le_iSup₂ (f := fun m (_ : m ∈ M) => CFSG.conjugate R m) (1 : G) (one_mem M)
    · intro z hz
      rw [CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem] at hz
      have h1 := (mem_normalizer_iff.mp (hMCM (inv_mem hm)) _).mp (hRCM hz)
      rwa [show m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z by group] at h1
  exact ⟨hCG, hCM, hR, hRsylM, hRsylG, hRO, hJ, hXR, hmax⟩

end CFSG.Quasithin.SteinbergCC
