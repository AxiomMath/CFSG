module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.FS81.OrthMaxTorus
public import CFSG.LocalAnalysis.StandardType.FS81.RowFacts
public import CFSG.LocalAnalysis.StandardType.FS81.OrthRowCanonAux
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus
  nondegenerate_polarBilin_quadPlus nondegenerate_polarBilin_quadMinus_of_finite)

theorem fs81_canon_of_orthEquiv
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (htype : IsPlusType Q ↔ Even n)
    {G : Type} [Group G] {K A : Subgroup G}
    (e : ↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hA : IsMaxElemAb3 K A) :
    Nat.card A = 3 ^ n ∧ Subgroup.centralizer (A : Set G) ⊓ K = A := by
  have hAK : (A.subgroupOf K).map K.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hElemK : IsElemAbelian 3 (A.subgroupOf K) := hA.2.1.subgroupOf K
  have hMaxK : ∀ F : Subgroup ↥K, IsElemAbelian 3 F → A.subgroupOf K ≤ F →
      F = A.subgroupOf K := by
    intro F hF hAF
    have h1 : F.map K.subtype = A := by
      refine hA.2.2 (F.map K.subtype) ?_ (hF.map K.subtype) ?_
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · calc A = (A.subgroupOf K).map K.subtype := hAK.symm
          _ ≤ F.map K.subtype := Subgroup.map_mono hAF
    calc F = (F.map K.subtype).comap K.subtype :=
          (Subgroup.comap_map_eq_self_of_injective K.subtype_injective F).symm
      _ = A.comap K.subtype := by rw [h1]
      _ = A.subgroupOf K := rfl
  set Ω : Subgroup (V ≃ₗ[ZMod 2] V) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ with hΩ
  let E : Subgroup ↥Ω := (A.subgroupOf K).map e.toMonoidHom
  let E' : Subgroup (V ≃ₗ[ZMod 2] V) := E.map Ω.subtype
  have hE'elem : IsElemAbelian 3 E' := (hElemK.map e.toMonoidHom).map Ω.subtype
  have hE'Ω : E' ≤ Ω := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE'max : ∀ E'' : Subgroup (V ≃ₗ[ZMod 2] V), E'' ≤ Ω → IsElemAbelian 3 E'' → E' ≤ E'' →
      E'' = E' := by
    intro E'' hE''le hE''elem hE'E''
    have hFelem : IsElemAbelian 3 ((E''.comap Ω.subtype).comap e.toMonoidHom) :=
      (hE''elem.comap Ω.subtype_injective).comap e.injective
    have hAF : A.subgroupOf K ≤ (E''.comap Ω.subtype).comap e.toMonoidHom := fun x hx =>
      hE'E'' (Subgroup.mem_map_of_mem Ω.subtype (Subgroup.mem_map_of_mem e.toMonoidHom hx))
    have hF := hMaxK _ hFelem hAF
    refine le_antisymm (fun y hy => ?_) hE'E''
    have hyΩ : y ∈ Ω := hE''le hy
    have hxF : e.symm ⟨y, hyΩ⟩ ∈ (E''.comap Ω.subtype).comap e.toMonoidHom := by
      show Ω.subtype (e.toMonoidHom (e.symm ⟨y, hyΩ⟩)) ∈ E''
      simpa using hy
    rw [hF] at hxF
    exact ⟨⟨y, hyΩ⟩, ⟨e.symm ⟨y, hyΩ⟩, hxF, by simp⟩, rfl⟩
  obtain ⟨l, hl, hlen, hEtorus⟩ :=
    fs81_orth_maxElemAb3_eq_torus hQ hdim htype hE'Ω hE'elem hE'max
  have hcardE' : Nat.card E' = Nat.card A := by
    change Nat.card (((A.subgroupOf K).map e.toMonoidHom).map Ω.subtype) = Nat.card A
    rw [Subgroup.card_map_of_injective Ω.subtype_injective,
      Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  have hcardA : Nat.card A = 3 ^ n := by
    rw [← hcardE', hEtorus, card_torus hl, hlen]
  have hfull : finrank (ZMod 2) V = 2 * l.length := by rw [hlen, hdim]
  have hcent : Subgroup.centralizer (E' : Set (V ≃ₗ[ZMod 2] V)) ⊓ Ω = E' := by
    rw [hEtorus]
    exact centralizer_torus_eq_self_of_frame hl hQ hfull
  have hcentE : Subgroup.centralizer (E : Set ↥Ω) = E := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : V ≃ₗ[ZMod 2] V) ∈ Subgroup.centralizer (E' : Set (V ≃ₗ[ZMod 2] V)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨z, hz, rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx z hz)
      have hx'' : (x : V ≃ₗ[ZMod 2] V) ∈
          Subgroup.centralizer (E' : Set (V ≃ₗ[ZMod 2] V)) ⊓ Ω :=
        Subgroup.mem_inf.2 ⟨hx', x.2⟩
      rw [hcent] at hx''
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx''
      exact (Subtype.ext hzx) ▸ hz
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hE'elem.comm (Subgroup.mem_map_of_mem Ω.subtype hy)
        (Subgroup.mem_map_of_mem Ω.subtype hx))
  refine ⟨hcardA, le_antisymm ?_ ?_⟩
  · rintro x ⟨hxc, hxK⟩
    have hxE : e ⟨x, hxK⟩ ∈ Subgroup.centralizer (E : Set ↥Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      apply e.symm.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.symm_apply_apply]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hxc (a : G) ha
    rw [hcentE] at hxE
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxE
    obtain rfl := e.injective hyx
    exact hy
  · intro a ha
    exact Subgroup.mem_inf.2
      ⟨Subgroup.mem_centralizer_iff.2 fun h hh => hA.2.1.comm hh ha, hA.1 ha⟩

theorem fs81_orth_row_canon
    {G : Type} [Group G] [Finite G] {K A : Subgroup G} {r : Row} (hr : r ≠ Row.E7)
    (hK : IsRow r K) (hZ : Subgroup.center K = ⊥) (hA : IsMaxElemAb3 K A) :
    Nat.card A = 3 ^ r.n ∧ Subgroup.centralizer (A : Set G) ⊓ K = A := by
  obtain ⟨lab, hFS, hlab⟩ := exists_glaLabel hK
  obtain ⟨hn1, hcases⟩ := hFS
  have hmarked := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hlab
  obtain ⟨-, lab', hlab2, hraw⟩ := hmarked
  obtain ⟨R, _, I, F, hs, hna, θ, hEq, hmod⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hmod' : MarkedModel lab R := hEq ▸ hmod
  let e0 : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eK : ↥K ≃* R := e0.symm.trans θ
  have hmodK : MarkedModel lab ↥K := MarkedModel.of_mulEquiv eK.symm hmod'
  rcases hcases with ⟨hrD, hD, hr6⟩ | ⟨hrt, htwD, hr7⟩ | ⟨hrE, hE7, hr0⟩
  · subst hrD
    have h1 : markTag lab = .POmegaPlus := by simp [markTag, hD, hr6]
    have h2 : markRank lab = 6 := by simp [markRank, hD, hr6]
    have h3 : markChar lab = 2 := by simp [markChar, hD, hr6]
    have h4 : markDeg lab = 1 := by simp [markDeg, hD, hr6, hn1]
    have hmR : LieModel ↥K .POmegaPlus 6 2 1 := by
      have h := hmodK
      unfold MarkedModel at h
      rwa [h1, h2, h3, h4] at h
    have hst : StatedClassicalModel ↥K .POmegaPlus 6 2 1 :=
      hmR.statedClassicalModel (by decide)
    haveI : Nonempty (Fin 6 ⊕ Fin 6) := ⟨.inl 0⟩
    have hQ : (QuadraticMap.polarBilin (quadPlus 6 (ZMod 2))).Nondegenerate :=
      nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
    have hdim : finrank (ZMod 2) (Fin 6 ⊕ Fin 6 → ZMod 2) = 2 * 6 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
    have htype : IsPlusType (quadPlus 6 (ZMod 2)) ↔ Even 6 :=
      ⟨fun _ => ⟨3, rfl⟩, fun _ => isPlusType_quadPlus (ZMod 2) 6⟩
    have hY : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 6 (ZMod 2))))
        .POmegaPlus 6 2 1 :=
      ⟨hst.1, ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨e1⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hst hY
    exact fs81_canon_of_orthEquiv hQ hdim htype
      (e1.trans (CFSG.AGLEmbedding.ToralCensus.statedProjOmegaEquivDerivedCharTwo
        (coe_quadPlus 6 (ZMod 2)) hQ)) hA
  · subst hrt
    have h1 : markTag lab = .POmegaMinus := by simp [markTag, htwD, hr7]
    have h2 : markRank lab = 7 := by simp [markRank, htwD, hr7]
    have h3 : markChar lab = 2 := by simp [markChar, htwD, hr7]
    have h4 : markDeg lab = 1 := by simp [markDeg, htwD, hr7, hn1]
    have hmR : LieModel ↥K .POmegaMinus 7 2 1 := by
      have h := hmodK
      unfold MarkedModel at h
      rwa [h1, h2, h3, h4] at h
    have hst : StatedClassicalModel ↥K .POmegaMinus 7 2 1 :=
      hmR.statedClassicalModel (by decide)
    haveI : Nonempty (Fin (7 - 1) ⊕ Fin (7 - 1) ⊕ Fin 2) := ⟨.inr (.inr 0)⟩
    have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
    have hQ : (QuadraticMap.polarBilin (quadMinus 7 (ZMod 2) 1 1)).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2) hirr
    have hdim : finrank (ZMod 2) (Fin (7 - 1) ⊕ Fin (7 - 1) ⊕ Fin 2 → ZMod 2) = 2 * 7 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
    have htype : IsPlusType (quadMinus 7 (ZMod 2) 1 1) ↔ Even 7 :=
      ⟨fun hp => absurd hp (not_isPlusType_quadMinus (by omega : 1 ≤ 7) hirr),
        fun he => absurd he (by decide)⟩
    have hY : StatedClassicalModel
        (StatedProj (StatedOmega (StatedQuadMinus 7 (ZMod 2) 1 1))) .POmegaMinus 7 2 1 :=
      ⟨hst.1, ZMod 2, inferInstance, inferInstance, by simp, 1, 1, hirr, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨e1⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hst hY
    exact fs81_canon_of_orthEquiv hQ hdim htype
      (e1.trans (CFSG.AGLEmbedding.ToralCensus.statedProjOmegaEquivDerivedCharTwo
        (coe_quadMinus 7 (ZMod 2) 1 1) hQ)) hA
  · exact absurd hrE hr

end CFSG.StandardType.FrameRoute.FS81

end
