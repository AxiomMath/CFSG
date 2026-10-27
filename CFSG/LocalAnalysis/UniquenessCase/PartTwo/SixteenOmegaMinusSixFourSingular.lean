module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6ParaAux1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Comm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4Over

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s168e3_parabolic_data_of_exact_cover
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV)
    {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (hF : Nat.card F = 2 ^ n) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ε : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hcoords : S18.NatCoordsOmegaMinusOn (lBar V₀ V hV L) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ)
    {K : Subgroup G} (hKc : K ∈ calC D.M)
    (hbarK : barSub V₀ V hV K = lBar V₀ V hV L)
    (hU4K : IsU4 (Bar2 K) n)
    {w : G} (hw : w ∈ V)
    (hwl : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ≠ 1)
    (hsing : StatedQuadMinus 3 F b c
      (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩)) = 0) :
    ∃ P X : Subgroup G, ParabolicOf K P ∧ X = F07.DerInf P ∧
      IsL2 (Bar2 X) (2 * n) ∧ pCoreOf 2 X ≠ ⊥ ∧
      X ≤ D.M ⊓ centralizer ({w} : Set G) := by
  classical
  have hFact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Hyp125 D V₀ V := hS.setting.hyp151.hyp125
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hKc.1
  have hKstab : K ≤ stabTil V₀ V :=
    hKM.trans (le_stabTil hH.pairFacts.le_normalizer hH.pairFacts.le_normalizer₀)
  let mkK : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let q : Bar2 K →* ↥(barSub V₀ V hV K) := barSubBar2HomOfHyp125 hH hKc
  have hq : Function.Surjective q := barSubBar2HomOfHyp125_surjective hH hKc
  let actK : ↥K →* ↥(barSub V₀ V hV K) := q.comp mkK
  have hqmk : ∀ x : ↥K, q (mkK x) =
      ⟨actTil V₀ V hV ⟨(x : G), hKstab x.2⟩,
        actTil_mem_barSub V₀ V hV x.2 (hKstab x.2)⟩ := by
    intro x
    change barSubBar2HomOfHyp125 hH hKc (mkK x) = _
    unfold barSubBar2HomOfHyp125 barSubBar2Hom
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    rfl
  have hactK : Function.Surjective actK :=
    hq.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
  have hpcK : CFSG.pCore 2 ↥K ≤ actK.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change q (mkK x) = 1
    have h1 : mkK x = 1 := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) x).2 hx
    rw [h1, map_one]
  have hsimpleK : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4K
  have hbarNtriv : Nontrivial ↥(barSub V₀ V hV K) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (by
      rw [hbarK]
      exact hS.ne_bot)
  have hqker : q.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal q.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥(barSub V₀ V hV K))
      obtain ⟨x, rfl⟩ := hq y
      exact hy (by
        have hx : x ∈ q.ker := h ▸ Subgroup.mem_top x
        exact MonoidHom.mem_ker.mp hx)
  have hker_act : actK.ker = CFSG.pCore 2 ↥K := by
    refine le_antisymm ?_ hpcK
    intro x hx
    have hxq : mkK x ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      simpa [actK] using hx
    rw [hqker, Subgroup.mem_bot] at hxq
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) x).1 hxq
  have hΦKsurj : Function.Surjective
      (ε.toMonoidHom.comp ((MulEquiv.subgroupCongr hbarK).toMonoidHom.comp actK)) :=
    ε.surjective.comp ((MulEquiv.subgroupCongr hbarK).surjective.comp hactK)
  let ΦK : ↥K →* ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
    ε.toMonoidHom.comp ((MulEquiv.subgroupCongr hbarK).toMonoidHom.comp actK)
  have hkerΦK : ΦK.ker = CFSG.pCore 2 ↥K := by
    rw [← hker_act]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (MulEquiv.subgroupCongr hbarK) (actK x) = 1 :=
        ε.injective (by simpa [ΦK] using hx)
      exact (MulEquiv.subgroupCongr hbarK).injective (by simpa using h1)
    · intro hx
      simpa [ΦK] using congrArg (fun y => ε ((MulEquiv.subgroupCongr hbarK) y)) hx
  let v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F :=
    Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩)
  have hv0 : v ≠ 0 := by
    intro h0
    apply hwl
    have hψ1 : ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ = 1 := by
      have h1 : Multiplicative.ofAdd v = 1 := by rw [h0]; rfl
      rwa [show v = Multiplicative.toAdd
        (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩) from rfl,
        ofAdd_toAdd] at h1
    have h2 : (⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Vtil V₀ V hV))) = 1 :=
      ψ.injective (by rw [hψ1, map_one])
    simpa using congrArg Subtype.val h2
  obtain ⟨Q, hQw, hQpar, _hQO2, hQl2, hQp, _hQB⟩ :=
    S18.k_K_Omega6Minus_singularPointStabilizer_holds hF hbc v hv0 hsing
  let P : Subgroup G := (Q.comap ΦK).map K.subtype
  have hPsub : P.subgroupOf K = Q.comap ΦK :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hO2P : CFSG.Open.pCoreOf 2 K ≤ P := by
    rw [CFSG.Assembly.pCoreOf_eq_map_pCore]
    rintro - ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_comap.mpr (by
      have h1 : ΦK y = 1 := (MonoidHom.mem_ker).1 (by rw [hkerΦK]; exact hy)
      rw [h1]
      exact Q.one_mem), rfl⟩
  have hmapP : (P.subgroupOf K).map ΦK = Q := by
    rw [hPsub]
    exact Subgroup.map_comap_eq_self_of_surjective hΦKsurj Q
  have hpar : ParabolicOf K P := by
    refine ⟨hO2P, hPK, ?_⟩
    show IsParabolicTwo (Bar2 K) ((P.subgroupOf K).map mkK)
    let Φbar : Bar2 K →* ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
      ε.toMonoidHom.comp ((MulEquiv.subgroupCongr hbarK).toMonoidHom.comp q)
    have hΦbar : Function.Surjective Φbar :=
      ε.surjective.comp ((MulEquiv.subgroupCongr hbarK).surjective.comp hq)
    have hΦKbar : ΦK = Φbar.comp mkK := rfl
    have hmapQ : (P.subgroupOf K).map mkK = Q.comap Φbar := by
      rw [hPsub, hΦKbar]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)) (Q.comap Φbar)
    rw [hmapQ]
    exact IsParabolicTwo.comap Φbar hΦbar hQpar
  let X : Subgroup G := F07.DerInf P
  have hXK : X ≤ K := (Subgroup.map_subtype_le _).trans hPK
  have hmapX : (X.subgroupOf K).map ΦK = F07.DerInf Q := by
    change Subgroup.map ΦK (((perfectResidual ↥P).map P.subtype).subgroupOf K) = F07.DerInf Q
    rw [CFSG.perfectResidual_subtype_subgroupOf P K hPK, ← hmapP]
    exact SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ΦK (P.subgroupOf K)
  let g : ↥(X.subgroupOf K) →* ↥(F07.DerInf Q) :=
    (ΦK.comp (X.subgroupOf K).subtype).codRestrict (F07.DerInf Q)
      (fun z => hmapX ▸ Subgroup.mem_map_of_mem ΦK z.2)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∈
        (X.subgroupOf K).map ΦK := by rw [hmapX]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hgker : g.ker = (CFSG.pCore 2 ↥K).comap (X.subgroupOf K).subtype := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hz
      have h1 : ΦK (z : ↥K) = 1 := congrArg Subtype.val hz
      have h2 : (z : ↥K) ∈ ΦK.ker := (MonoidHom.mem_ker).2 h1
      rwa [hkerΦK] at h2
    · intro hz
      apply Subtype.ext
      have h2 : (z : ↥K) ∈ ΦK.ker := by rw [hkerΦK]; exact hz
      simpa [g] using (MonoidHom.mem_ker).1 h2
  have hg2 : IsPGroup 2 g.ker := by
    rw [hgker]
    exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2)) _
      (Subgroup.subtype_injective _)
  let eX : ↥(X.subgroupOf K) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
  let f : ↥X →* ↥(F07.DerInf Q) := g.comp eX.symm.toMonoidHom
  have hfsurj : Function.Surjective f := hgsurj.comp eX.symm.surjective
  have hf2 : IsPGroup 2 f.ker := by
    have hkerf : f.ker = g.ker.comap eX.symm.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      rfl
    rw [hkerf]
    exact IsPGroup.comap_of_injective hg2 _ eX.symm.injective
  obtain ⟨eBar⟩ :=
    CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hfsurj hf2
  have hL2X : IsL2 (Bar2 X) (2 * n) :=
    CFSG.Blueprint.LieModel.of_mulEquiv eBar.symm hQl2
  have hXp : CFSG.Open.pCoreOf 2 X ≠ ⊥ := by
    have hYp : CFSG.pCore 2 ↥(F07.DerInf Q) ≠ ⊥ := by
      intro hbot
      apply hQp
      rw [CFSG.Assembly.pCoreOf_eq_map_pCore, hbot, Subgroup.map_bot]
    have hXpc : CFSG.pCore 2 ↥X ≠ ⊥ :=
      CFSG.pCore_ne_bot_of_surjective_of_isPGroup_ker f hfsurj hf2 hYp
    rw [CFSG.Open.pCoreOf]
    intro hb
    exact hXpc ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb)
  have hXperf : ⁅X, X⁆ = X := by
    rw [show X = F07.DerInf P from rfl]
    exact Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect P)
  refine ⟨P, X, hpar, rfl, hL2X, hXp, le_inf (hXK.trans hKM) ?_⟩
  apply s16c6_le_centralizer_of_fix D hS hKM hKc.2.1 hXK hw
  · intro x hxX
    have hxK : x ∈ K := hXK hxX
    have hxS : x ∈ stabTil V₀ V := hKstab hxK
    let Ω : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
      StatedOmega (StatedQuadMinus 3 F b c)
    let Qgl : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := Q.map Ω.subtype
    have hQglv : ∀ y ∈ Qgl,
        (y : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v ∈
          Submodule.span F {v} := by
      rintro y ⟨q, hq, rfl⟩
      exact hQw q hq
    have hDerFixQgl := s16c6_derInf_fixes Qgl v hv0 hQglv
    have hDerMap : (F07.DerInf Q).map Ω.subtype = F07.DerInf Qgl :=
      Hinf_map Ω.subtype Q
    have hPhiDer : ΦK ⟨x, hxK⟩ ∈ F07.DerInf Q := by
      rw [← hmapX]
      exact Subgroup.mem_map_of_mem ΦK (Subgroup.mem_subgroupOf.mpr hxX)
    have hfixvec : (((ΦK ⟨x, hxK⟩ : ↥Ω) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v = v := by
      have hmem : ((ΦK ⟨x, hxK⟩ : ↥Ω) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∈ F07.DerInf Qgl := by
        rw [← hDerMap]
        exact Subgroup.mem_map_of_mem Ω.subtype hPhiDer
      exact hDerFixQgl _ hmem
    have hcast : ((MulEquiv.subgroupCongr hbarK) (actK ⟨x, hxK⟩) :
        ↥(lBar V₀ V hV L)) =
        ⟨actTil V₀ V hV ⟨x, hxS⟩, by
          rw [← hbarK]; exact actTil_mem_barSub V₀ V hV hxK hxS⟩ := by
      apply Subtype.ext
      change ((q (mkK ⟨x, hxK⟩) : ↥(barSub V₀ V hV K)) :
        MulAut (Vtil V₀ V hV)) = actTil V₀ V hV ⟨x, hxS⟩
      rw [hqmk ⟨x, hxK⟩]
    have hfixvec' : (((ε ⟨actTil V₀ V hV ⟨x, hxS⟩, by
          rw [← hbarK]; exact actTil_mem_barSub V₀ V hV hxK hxS⟩ : ↥Ω) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v = v := by
      rw [← hcast]
      exact hfixvec
    have hgoal : actTil V₀ V hV ⟨x, hxS⟩
        (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) := by
      have h : (⟨actTil V₀ V hV ⟨x, hxS⟩ (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)),
          Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV))) =
          ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ := by
        apply ψ.injective
        have hco := hcoords (l := ⟨actTil V₀ V hV ⟨x, hxS⟩, by
            rw [← hbarK]; exact actTil_mem_barSub V₀ V hV hxK hxS⟩)
          (s := ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩)
        rw [hco]
        rw [show Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
            Subgroup.mem_top _⟩) = v from rfl]
        rw [hfixvec']
        rfl
      exact congrArg Subtype.val h
    have := hgoal
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at this
    simpa [IntMod.mk, IntMod.val] using this
  · exact Or.inl hXperf


theorem s168e3_uniqueMax_of_exact_cover
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV)
    {n : ℕ} (hn : 1 < n) {F : Type} [Field F] [Finite F] {b c : F}
    (hF : Nat.card F = 2 ^ n) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ε : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hcoords : S18.NatCoordsOmegaMinusOn (lBar V₀ V hV L) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ)
    {K : Subgroup G} (hKc : K ∈ calC D.M)
    (hKN : D.M ≤ normalizer (K : Set G))
    (hbarK : barSub V₀ V hV K = lBar V₀ V hV L)
    (hU4K : IsU4 (Bar2 K) n)
    {w : G} (hw : w ∈ V)
    (hwl : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ≠ 1)
    (hsing : StatedQuadMinus 3 F b c
      (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩)) = 0)
    (h924 : R9_24X D) (hSP : IsStronglyPEmbedded 3 D.M) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨P, X, hP, hX, hL2, hXp, hXle⟩ :=
    s168e3_parabolic_data_of_exact_cover D hS hF hbc ε ψ hcoords hKc hbarK hU4K hw hwl hsing
  have hcomm := s16c6_comm D hKc hKN hn hU4K
    (fun {_ _ _} hP' hX' hL2' hXR' => s16c6_u4_overgroup hn hU4K hP' hX' hL2' hXR')
    hP hX hL2 hXp
  have huniq : UniqueMax D.M X := h924 K P X n hKc hKN hn hU4K hP hX hL2 hXp hcomm hSP
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, inf_le_left⟩, ?_⟩
  intro N hN
  have hN' : N ∈ calMOf X := ⟨hN.1, hXle.trans hN.2⟩
  rw [huniq] at hN'
  exact hN'


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
