module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFF2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin
public import CFSG.Milestones.ASVolI.B5

public section

namespace CFSG.Quasithin.H13.T614.FFStep

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

@[expose] def TitsNotB55Fact : Prop :=
  ∀ (Y X : Type) [Group Y] [Group X], CFSG.Quasithin.IsTits Y → Nonempty (X ≃* Y) →
    ¬ CFSG.ASVolI.ChB.IsB55Group X

section Offenders

variable {V : Type} [CommGroup V]

theorem ffJ_conj_le {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) :
    (ffJ X).map (MulAut.conj g).toMonoidHom ≤ ffJ X := by
  unfold ffJ
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun A hA => ?_
  exact B6.le_ffJ (isFFStarOffender_map_conj hA hg)

theorem le_normalizer_ffJ {X : Subgroup (MulAut V)} :
    X ≤ Subgroup.normalizer (ffJ X : Set (MulAut V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := ffJ_conj_le hg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa [MulAut.conj_apply] using this
  · intro hx
    have hg' : g⁻¹ ∈ X := X.inv_mem hg
    have := ffJ_conj_le hg' (Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hx, rfl⟩)
    have e : (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x := by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
    rwa [e] at this

end Offenders

section Preimage

variable {G : Type} [Group G] [Finite G]

noncomputable def preSet {R : Subgroup G} (hV : IsElemAbelian 2 R)
    (S : Subgroup (MulAut (IntMod R hV))) (H : Subgroup G) : Subgroup G :=
  (S.comap (convI hV)).map (Subgroup.normalizer (R : Set G)).subtype ⊓ H

theorem mem_preSet {R H : Subgroup G} (hV : IsElemAbelian 2 R)
    {S : Subgroup (MulAut (IntMod R hV))} {g : G} :
    g ∈ preSet hV S H ↔ g ∈ H ∧ ∃ hg : g ∈ Subgroup.normalizer (R : Set G),
      convI hV ⟨g, hg⟩ ∈ S := by
  unfold preSet
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨x, hx, hxg⟩, hgH⟩
    subst hxg
    exact ⟨hgH, x.2, hx⟩
  · rintro ⟨hgH, hgN, hS⟩
    exact ⟨⟨⟨g, hgN⟩, hS, rfl⟩, hgH⟩

end Preimage

end CFSG.Quasithin.H13.T614.FFStep

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

open FFStep in
theorem ffCentralizerFact_of (hT : TitsBasicFact) (hB55 : CFSG.ASVolI.B_5_5)
    (hNot : TitsNotB55Fact) : FFCentralizerFact := by
  intro G _ _ T M L V M₁ K₁ h horth hM₁ hCM₁ hK₁ htits hTK hJ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hq, hZ⟩ := hT (ModO2 K₁) htits
  have hsimp : IsSimpleGroup (ModO2 K₁) := by
    haveI := hq.2.1
    exact MulEquiv.isSimpleGroup
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)
  have hK₁M₁ : K₁ ≤ M₁ := le_of_mem_cComp hK₁
  have hTM₁ : T ≤ M₁ := (le_centralizer_omegaOne T).trans hCM₁
  have hperf : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr (mem_cComp_iff.mp hK₁).2.1
  have hsyl : IsSylowTwoOf T (K₁ ⊔ T) := h.toHyp5_0_1.isSylowTwoOf le_sup_right
  have hHN : K₁ ⊔ T ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hTK
  have hH1 : K₁ ⊔ T ≤ M₁ := sup_le hK₁M₁ hTM₁
  have hV : IsElemAbelian 2 (quasithinOmegaOneCenter (pCoreOf 2 (K₁ ⊔ T))) :=
    isElemAbelian_omegaOneCenter _
  have hHNR : K₁ ⊔ T ≤
      Subgroup.normalizer (quasithinOmegaOneCenter (pCoreOf 2 (K₁ ⊔ T)) : Set G) :=
    normalizer_le_omegaOne (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K₁ ⊔ T))
  have hQC : pCoreOf 2 (K₁ ⊔ T) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter (pCoreOf 2 (K₁ ⊔ T)) : Set G) :=
    le_centralizer_omegaOne _
  by_cases hKC : K₁ ≤ Subgroup.centralizer (quasithinOmegaOneCenter (pCoreOf 2 (K₁ ⊔ T)) : Set G)
  · exact hKC
  exfalso
  set R : Subgroup G := quasithinOmegaOneCenter (pCoreOf 2 (K₁ ⊔ T)) with hRdef
  have hKR : K₁ ≤ Subgroup.normalizer (R : Set G) := fun k hk => hHNR (Subgroup.mem_sup_left hk)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht => hHNR (Subgroup.mem_sup_right ht)
  have hRT : R ≤ T :=
    (omegaOne_le _).trans (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hsyl)
  have hOC : pCoreOf 2 K₁ ≤ Subgroup.centralizer (R : Set G) := by
    refine le_trans ?_ hQC
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans le_sup_left)
      (fun x hx => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁ (hHN hx))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hKC' : K₁ ⊓ Subgroup.centralizer (R : Set G) = pCoreOf 2 K₁ :=
    centralizer_inf_eq_pCoreOf hKR hperf hsimp hOC hKC
  have hO2 : pCoreOf 2 (autI hV (K₁ ⊔ T)) = ⊥ :=
    pCoreOf_autI_eq_bot hV hTK hsyl hperf hsimp hHNR hQC hKC'
  obtain ⟨A, hA, hAC, a, haA, u, hu, hnot⟩ := exists_offender hTK hKR hKC' hJ
  have hAH : A ≤ K₁ ⊔ T := hA.1.trans le_sup_right
  have hoffT : IsFFStarOffender (autI hV T) (autI hV A) :=
    offenderImages_isFFStarOffender hV hRT hTR ⟨A, ⟨hA, hAC⟩, rfl⟩
  have hoffH : IsFFStarOffender (autI hV (K₁ ⊔ T)) (autI hV A) :=
    isFFStarOffender_of_le (autI_mono hV hAH) hoffT
  set G₀ : Subgroup (MulAut (IntMod R hV)) := ffJ (autI hV (K₁ ⊔ T)) with hG₀
  have hAG₀ : autI hV A ≤ G₀ := B6.le_ffJ hoffH
  have hG₀le : G₀ ≤ autI hV (K₁ ⊔ T) := B6.ffJ_le _
  have hG₀n : ∀ g ∈ autI hV (K₁ ⊔ T), ∀ x ∈ G₀, g * x * g⁻¹ ∈ G₀ := by
    intro g hg x hx
    have := ffJ_conj_le hg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa [MulAut.conj_apply] using this
  have hG₀N : autI hV (K₁ ⊔ T) ≤ Subgroup.normalizer (G₀ : Set (MulAut (IntMod R hV))) :=
    le_normalizer_ffJ
  have hG₀eq : G₀ = ffJ G₀ := (CFSG.Quasithin.InternalSec.ffJ_ffJ (autI hV (K₁ ⊔ T))).symm
  have hpG₀ : pCoreOf 2 G₀ = ⊥ := by
    have h1 : pCoreOf 2 G₀ ≤ autI hV (K₁ ⊔ T) := (CFSG.LieType.BorelTits.pCoreOf_le 2 G₀).trans hG₀le
    have h2 : autI hV (K₁ ⊔ T) ≤ Subgroup.normalizer (pCoreOf 2 G₀ : Set (MulAut (IntMod R hV))) :=
      hG₀N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 G₀)
    have h3 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h1 h2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀)
    rw [hO2] at h3
    exact le_bot_iff.mp h3
  set J' : Subgroup G := preSet hV G₀ (K₁ ⊔ T) with hJ'
  have hJ'H : J' ≤ K₁ ⊔ T := inf_le_right
  have hJ'N : J' ≤ Subgroup.normalizer (R : Set G) := hJ'H.trans hHNR
  have hSQM₁ : SQTKGroup ↥M₁ :=
    sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian
      (CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hM₁.1)
  have hSQ : SQTKGroup ↥J' := B42Dispatch.sqtkGroup_of_le hSQM₁ (hJ'H.trans hH1)
  have hφ₀mem : ∀ y : ↥J', (convI hV) (Subgroup.inclusion hJ'N y) ∈ G₀ := by
    intro y
    obtain ⟨-, hg, hmem⟩ := (mem_preSet hV).mp y.2
    exact hmem
  let φ : ↥J' →* ↥G₀ := ((convI hV).comp (Subgroup.inclusion hJ'N)).codRestrict G₀ hφ₀mem
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨g, hgH, hg⟩ := (mem_autI hV).mp (hG₀le z.2)
    have hmem : convI hV ⟨(g : G), g.2⟩ ∈ G₀ := by
      rw [show convI hV ⟨(g : G), g.2⟩ = convI hV g from rfl, hg]
      exact z.2
    refine ⟨⟨(g : G), (mem_preSet hV).mpr ⟨hgH, g.2, hmem⟩⟩, Subtype.ext ?_⟩
    exact hg
  have e : ↥G₀ ≃* ↥J' ⧸ φ.ker := (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm
  have hB53 : CFSG.Quasithin.B53Hyp G₀ :=
    ⟨hpG₀, hG₀eq, ↥J', inferInstance, inferInstance, φ.ker, inferInstance, hSQ, ⟨e⟩⟩
  set Kh : Subgroup (MulAut (IntMod R hV)) := autI hV K₁ with hKh
  have hKhH : Kh ≤ autI hV (K₁ ⊔ T) := autI_mono hV le_sup_left
  have hKhn : ∀ g ∈ autI hV (K₁ ⊔ T), ∀ x ∈ Kh, g * x * g⁻¹ ∈ Kh := by
    intro g hg x hx
    obtain ⟨h, hhH, rfl⟩ := (mem_autI hV).mp hg
    obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).mp hx
    have hN : (h : G) * (k : G) * (h : G)⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ h.2 k.2) (Subgroup.inv_mem _ h.2)
    show _ ∈ autI hV K₁
    rw [mem_autI hV]
    refine ⟨⟨(h : G) * (k : G) * (h : G)⁻¹, hN⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hHN hhH) (k : G)).mp hkK
    · have e' : (⟨(h : G) * (k : G) * (h : G)⁻¹, hN⟩ : ↥(Subgroup.normalizer (R : Set G))) =
          h * k * h⁻¹ := rfl
      rw [e', map_mul, map_mul, map_inv]
  set ψK : ↥K₁ →* MulAut (IntMod R hV) := (convI hV).comp (Subgroup.inclusion hKR) with hψK
  have hkerψ : ψK.ker = (pCoreOf 2 K₁).subgroupOf K₁ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxC : (x : G) ∈ Subgroup.centralizer (R : Set G) :=
        (convI_eq_one_iff hV ⟨(x : G), hKR x.2⟩).mp hx
      rw [← hKC']
      exact Subgroup.mem_inf.mpr ⟨x.2, hxC⟩
    · intro hx
      rw [← hKC'] at hx
      exact (convI_eq_one_iff hV ⟨(x : G), hKR x.2⟩).mpr (Subgroup.mem_inf.mp hx).2
  have hpc' : (pCoreOf 2 K₁).subgroupOf K₁ = CFSG.pCore 2 ↥K₁ := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hker' : ψK.ker = CFSG.pCore 2 ↥K₁ := hkerψ.trans hpc'
  have hrange : ψK.range = Kh := by
    ext φ'
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_autI hV).mpr ⟨⟨(x : G), hKR x.2⟩, x.2, rfl⟩
    · intro hφ
      obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).mp hφ
      exact ⟨⟨(g : G), hgK⟩, rfl⟩
  have eK : ModO2 K₁ ≃* ↥Kh :=
    ((QuotientGroup.quotientMulEquivOfEq hker').symm.trans (QuotientGroup.quotientKerEquivRange ψK)).trans
      (MulEquiv.subgroupCongr hrange)
  have hKq : CFSG.IsQuasisimple ↥Kh := CFSG.IsQuasisimple.of_mulEquiv eK.symm hq
  set Kc : Subgroup ↥(autI hV (K₁ ⊔ T)) := Kh.subgroupOf (autI hV (K₁ ⊔ T)) with hKc
  set Nc : Subgroup ↥(autI hV (K₁ ⊔ T)) := G₀.subgroupOf (autI hV (K₁ ⊔ T)) with hNc
  haveI hNcn : Nc.Normal := by
    constructor
    intro n hn g
    rw [hNc, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hG₀n _ g.2 _ hn
  haveI hKcn : Kc.Normal := by
    constructor
    intro n hn g
    rw [hKc, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hKhn _ g.2 _ hn
  have hKcomp : CFSG.IsComponent Kc :=
    ⟨CFSG.IsQuasisimple.of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hKhH).trans eK.symm) hq,
      Subgroup.Normal.isSubnormal inferInstance⟩
  have hcen := CFSG.LocalCores.component_normal_subgroup hKcomp hNcn
  have hKhG0 : Kh ≤ G₀ := by
    rcases hcen with hle | hcomm
    · intro x hx
      have hxKc : (⟨x, hKhH hx⟩ : ↥(autI hV (K₁ ⊔ T))) ∈ Kc := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp (hle hxKc)
    · exfalso
      have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have haT : a ∈ T := hA.1 haA
      have haR : a ∈ Subgroup.normalizer (R : Set G) := hTR haT
      have huR : u ∈ Subgroup.normalizer (R : Set G) := hKR hu
      have hcA : convI hV ⟨a, haR⟩ ∈ G₀ := hAG₀ (convI_mem_autI hV haA haR)
      have hcu : convI hV ⟨u, huR⟩ ∈ Kh := convI_mem_autI hV hu huR
      have hnN : (⟨convI hV ⟨a, haR⟩, hG₀le hcA⟩ : ↥(autI hV (K₁ ⊔ T))) ∈ Nc :=
        Subgroup.mem_subgroupOf.mpr hcA
      have hxKc : (⟨convI hV ⟨u, huR⟩, hKhH hcu⟩ : ↥(autI hV (K₁ ⊔ T))) ∈ Kc :=
        Subgroup.mem_subgroupOf.mpr hcu
      have hcomm' := Subgroup.mem_centralizer_iff.mp (hcent hxKc) _ hnN
      have hcomm'' : convI hV ⟨a, haR⟩ * convI hV ⟨u, huR⟩ =
          convI hV ⟨u, huR⟩ * convI hV ⟨a, haR⟩ := congrArg Subtype.val hcomm'
      have hN : a * u * a⁻¹ * u⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haR huR)
          (Subgroup.inv_mem _ haR)) (Subgroup.inv_mem _ huR)
      have hkey : convI hV ⟨a * u * a⁻¹ * u⁻¹, hN⟩ = 1 := by
        have e' : (⟨a * u * a⁻¹ * u⁻¹, hN⟩ : ↥(Subgroup.normalizer (R : Set G))) =
            ⟨a, haR⟩ * ⟨u, huR⟩ * ⟨a, haR⟩⁻¹ * ⟨u, huR⟩⁻¹ := rfl
        rw [e', map_mul, map_mul, map_mul, map_inv, map_inv, hcomm'']
        group
      have hCm : a * u * a⁻¹ * u⁻¹ ∈ Subgroup.centralizer (R : Set G) :=
        (convI_eq_one_iff hV _).mp hkey
      have hKm : a * u * a⁻¹ * u⁻¹ ∈ K₁ :=
        K₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTK haT) u).mp hu) (K₁.inv_mem hu)
      exact hnot (by rw [← hKC']; exact Subgroup.mem_inf.mpr ⟨hKm, hCm⟩)
  have hcompG₀ : CFSG.Open.IsComponentOf Kh G₀ := by
    refine ⟨hKhG0, ?_, ⟨Group.isPerfect_def.mp hKq.1, hKq.2.1⟩⟩
    have hnormal : (Kh.subgroupOf G₀).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hKhn _ (hG₀le g.2) _ hn
    exact CFSG.Open.IsSubnormal.step hKhG0 hnormal (CFSG.Open.IsSubnormal.refl G₀)
  have hexp : ∀ v : IntMod R hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have h55 := (hB55 (IntMod R hV) hexp G₀ hB53).1 Kh hcompG₀
  exact hNot (ModO2 K₁) ↥Kh htits ⟨eK.symm⟩ h55.2.2.2

end CFSG.Quasithin.H13.T614
