module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Cover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6ParaAux1
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

variable {G : Type} [Group G] [Finite G]

private noncomputable def s16c6_barSubBar2Hom {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L : Subgroup G} (hLS : L ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥) :
    Bar2 L →* ↥(barSub V₀ V hV L) := by
  classical
  let φ : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLS)).codRestrict
      (barSub V₀ V hV L) (fun x => actTil_mem_barSub V₀ V hV x.2 (hLS x.2))
  have hker : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hLS x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V hV hxP (hLS x.2)
    rw [h2, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  exact QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hker

private theorem s16c6_barSubBar2Hom_surjective {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L : Subgroup G} (hLS : L ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥) :
    Function.Surjective (s16c6_barSubBar2Hom hV hLS h2) := by
  classical
  intro y
  obtain ⟨a, haL, hay⟩ := (mem_barSub V₀ V hV L (y : MulAut (Vtil V₀ V hV))).1 y.2
  refine ⟨QuotientGroup.mk ⟨a, haL⟩, ?_⟩
  apply Subtype.ext
  change actTil V₀ V hV a = (y : MulAut (Vtil V₀ V hV))
  rw [hay]

private theorem s16c6_barSubBar2Hom_mk {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L : Subgroup G} (hLS : L ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥)
    (l : ↥L) :
    s16c6_barSubBar2Hom hV hLS h2 (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
      ⟨actTil V₀ V hV ⟨(l : G), hLS l.2⟩, actTil_mem_barSub V₀ V hV l.2 (hLS l.2)⟩ := by
  classical
  unfold s16c6_barSubBar2Hom
  rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  rfl

theorem s16c6_parabolic_of_singular
    (D : Data G) (hstd : S168e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case163_6 D V₀ V hV L)
    (c : S16c6Coords V₀ V L hV) {w : G} (hw : w ∈ V) (hsing : c.Singular w hw) :
    ∃ K P X : Subgroup G, K ∈ calC D.M ∧ D.M ≤ normalizer (K : Set G) ∧ IsU4 (Bar2 K) 3 ∧
      ParabolicOf K P ∧ X = F07.DerInf P ∧ IsL2 (Bar2 X) (2 * 3) ∧ pCoreOf 2 X ≠ ⊥ ∧
      ∀ x ∈ X, x * w * x⁻¹ * w⁻¹ ∈ V₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKcalC, hKN, hKbar, hKsimple⟩ := s16c6_exists_cover D hstd hS hc
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hKcalC.1
  have hKstab : K ≤ stabTil V₀ V :=
    hKM.trans (le_stabTil hH.pairFacts.le_normalizer hH.pairFacts.le_normalizer₀)
  have hKne : barSub V₀ V hV K ≠ ⊥ := by
    rw [hKbar]
    simpa only [lBar] using hS.ne_bot
  have h2K : barSub V₀ V hV (CFSG.Open.pCoreOf 2 K) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hKcalC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hH)
  have hker : (s16c6_barSubBar2Hom hV hKstab h2K).ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (s16c6_barSubBar2Hom hV hKstab h2K).ker with h | h
    · exact h
    · refine absurd ?_ hKne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, hy⟩ := s16c6_barSubBar2Hom_surjective hV hKstab h2K ⟨x, hx⟩
      have hy1 : s16c6_barSubBar2Hom hV hKstab h2K y = 1 :=
        (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top y)
      have hval : ((s16c6_barSubBar2Hom hV hKstab h2K y : ↥(barSub V₀ V hV K)) :
          MulAut (Vtil V₀ V hV)) = x := congrArg Subtype.val hy
      rw [hy1] at hval
      simpa using hval.symm
  let eK : Bar2 K ≃* ↥(barSub V₀ V hV K) :=
    MulEquiv.ofBijective (s16c6_barSubBar2Hom hV hKstab h2K)
      ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, s16c6_barSubBar2Hom_surjective hV hKstab h2K⟩
  have hOmegaK : IsOmegaMinus ↥(barSub V₀ V hV K) 6 3 := by
    rw [hKbar]
    exact hc.1
  have hU4K : IsU4 (Bar2 K) 3 :=
    CFSG.Blueprint.LieModel.of_mulEquiv eK.symm (S18.isU4_of_isOmegaMinus hOmegaK)
  let castE : ↥(barSub V₀ V hV K) ≃* ↥(lBar V₀ V hV L) := MulEquiv.subgroupCongr hKbar
  let Φ : Bar2 K ≃* ↥(StatedOmega (StatedQuadMinus 3 c.F c.b c.c)) := eK.trans (castE.trans c.ε)
  have hΦapply : ∀ a, Φ a = c.ε (castE (eK a)) := by
    intro a
    rfl
  have hw' : c.vec w hw ≠ 0 := by
    intro h0
    apply hsing.1
    have hψ : c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ = 1 := by
      have h1 : Multiplicative.ofAdd (c.vec w hw) = 1 := by rw [h0]; rfl
      rwa [show c.vec w hw = Multiplicative.toAdd
        (c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩) from rfl,
        ofAdd_toAdd] at h1
    have h2 : (⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Vtil V₀ V hV))) = 1 :=
      c.ψ.injective (by rw [hψ, map_one])
    simpa using congrArg Subtype.val h2
  obtain ⟨Q, hQw, hQpar, _hQO2, hQl2, hQp, _hQB⟩ :=
    S18.k_K_Omega6Minus_singularPointStabilizer_holds c.card_eq c.irr (c.vec w hw) hw' hsing.2
  let mkK : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let ΦK : ↥K →* ↥(StatedOmega (StatedQuadMinus 3 c.F c.b c.c)) := Φ.toMonoidHom.comp mkK
  let P : Subgroup G := ((Q.comap Φ.toMonoidHom).comap mkK).map K.subtype
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hO2P : CFSG.Open.pCoreOf 2 K ≤ P := by
    rw [CFSG.Assembly.pCoreOf_eq_map_pCore]
    rintro - ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hy1 : mkK y = 1 := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) y).2 hy
    rw [hy1]
    exact (Q.comap Φ.toMonoidHom).one_mem
  have hsub : P.subgroupOf K = (Q.comap Φ.toMonoidHom).comap mkK :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hpre : (P.subgroupOf K).map mkK = Q.comap Φ.toMonoidHom := by
    rw [hsub]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)) _
  have hpar : ParabolicOf K P := by
    refine ⟨hO2P, hPK, ?_⟩
    show IsParabolicTwo (Bar2 K) ((P.subgroupOf K).map mkK)
    rw [hpre]
    exact IsParabolicTwo.comap Φ.toMonoidHom Φ.surjective hQpar
  let X : Subgroup G := F07.DerInf P
  have hXK : X ≤ K := (Subgroup.map_subtype_le _).trans hPK
  have hmapP : (P.subgroupOf K).map ΦK = Q := by
    rw [show ΦK = Φ.toMonoidHom.comp mkK from rfl, ← Subgroup.map_map, hpre,
      Subgroup.map_comap_eq_self_of_surjective Φ.surjective]
  have hmapX : (X.subgroupOf K).map ΦK = F07.DerInf Q := by
    change Subgroup.map ΦK (((perfectResidual ↥P).map P.subtype).subgroupOf K) = F07.DerInf Q
    rw [CFSG.perfectResidual_subtype_subgroupOf P K hPK, ← hmapP]
    exact SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ΦK (P.subgroupOf K)
  have hkerΦK : ΦK.ker = CFSG.pCore 2 ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : mkK x = 1 := Φ.injective (by simpa [ΦK] using hx)
      exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) x).1 h1
    · intro hx
      have h1 : mkK x = 1 := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) x).2 hx
      simp [ΦK, h1]
  let g : ↥(X.subgroupOf K) →* ↥(F07.DerInf Q) :=
    (ΦK.comp (X.subgroupOf K).subtype).codRestrict (F07.DerInf Q)
      (fun z => hmapX ▸ Subgroup.mem_map_of_mem ΦK z.2)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : ↥(StatedOmega (StatedQuadMinus 3 c.F c.b c.c))) ∈
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
  have hL2X : IsL2 (Bar2 X) (2 * 3) :=
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
  refine ⟨K, P, X, hKcalC, hKN, hU4K, hpar, rfl, hL2X, hXp, ?_⟩
  intro x hxX
  have hxK : x ∈ K := hXK hxX
  have hxS : x ∈ stabTil V₀ V := hKstab hxK
  let Ω : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) :=
    StatedOmega (StatedQuadMinus 3 c.F c.b c.c)
  let Qgl : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) := Q.map Ω.subtype
  have hQglv : ∀ y ∈ Qgl,
      (y : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) *ᵥ c.vec w hw ∈
        Submodule.span c.F {c.vec w hw} := by
    rintro y ⟨q, hq, rfl⟩
    exact hQw q hq
  have hDerFixQgl := s16c6_derInf_fixes Qgl (c.vec w hw) hw' hQglv
  have hDerMap : (F07.DerInf Q).map Ω.subtype = F07.DerInf Qgl :=
    Hinf_map Ω.subtype Q
  have hPhiDer : Φ (mkK ⟨x, hxK⟩) ∈ F07.DerInf Q := by
    have h1 : ΦK ⟨x, hxK⟩ ∈ F07.DerInf Q := by
      rw [← hmapX]
      exact Subgroup.mem_map_of_mem ΦK (Subgroup.mem_subgroupOf.mpr hxX)
    simpa [ΦK] using h1
  have hfixvec : (((Φ (mkK ⟨x, hxK⟩) : ↥Ω) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) *ᵥ c.vec w hw = c.vec w hw := by
    have hmem : ((Φ (mkK ⟨x, hxK⟩) : ↥Ω) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) ∈ F07.DerInf Qgl := by
      rw [← hDerMap]
      exact Subgroup.mem_map_of_mem Ω.subtype hPhiDer
    exact hDerFixQgl _ hmem
  have hcast : (castE (eK (mkK ⟨x, hxK⟩)) : ↥(lBar V₀ V hV L)) =
      ⟨actTil V₀ V hV ⟨x, hxS⟩, by
        rw [← hKbar]; exact actTil_mem_barSub V₀ V hV hxK hxS⟩ := by
    have heKval : eK (mkK ⟨x, hxK⟩) = ⟨actTil V₀ V hV ⟨x, hxS⟩,
        actTil_mem_barSub V₀ V hV hxK hxS⟩ := by
      rw [show eK (mkK ⟨x, hxK⟩) = s16c6_barSubBar2Hom hV hKstab h2K (mkK ⟨x, hxK⟩)
        from rfl, s16c6_barSubBar2Hom_mk]
    rw [heKval]
    apply Subtype.ext
    simp [castE, MulEquiv.subgroupCongr_apply]
  have hfixvec' : (((c.ε ⟨actTil V₀ V hV ⟨x, hxS⟩, by
        rw [← hKbar]; exact actTil_mem_barSub V₀ V hV hxK hxS⟩ : ↥Ω) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) *ᵥ c.vec w hw = c.vec w hw := by
    rw [← hcast, ← hΦapply]
    exact hfixvec
  have hgoal : actTil V₀ V hV ⟨x, hxS⟩
      (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) = mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) := by
    have h : (⟨actTil V₀ V hV ⟨x, hxS⟩ (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)),
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV))) =
        ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ := by
      apply c.ψ.injective
      have hco := c.coords (l := ⟨actTil V₀ V hV ⟨x, hxS⟩, by
          rw [← hKbar]; exact actTil_mem_barSub V₀ V hV hxK hxS⟩)
        (s := ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩)
      rw [hco]
      rw [show Multiplicative.toAdd (c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
          Subgroup.mem_top _⟩) = c.vec w hw from rfl]
      rw [hfixvec']
      rfl
    exact congrArg Subtype.val h
  have hconj : x * w * x⁻¹ * w⁻¹ ∈ V₀ := by
    have := hgoal
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at this
    simpa [IntMod.mk, IntMod.val] using this
  exact hconj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
