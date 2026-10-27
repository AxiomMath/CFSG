module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameD
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RhoNeg
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RhoTw
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5EvenF
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inputs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5TwFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1Neg
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5TwData
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5TwLabel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4C1
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RParam
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLangComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLangFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Label
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameO

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso GGHasLabel GGInnerDiagOn)
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup IsRoot permLattice)

section Glue

private theorem w5T_two_pow_cast_three {f : ℕ} (hf : f % 2 = 1) :
    (((2 ^ f : ℕ)) : ZMod 3) = 2 := by
  have h := tc_two_pow_mod_three f
  rw [if_neg (by omega)] at h
  rw [← ZMod.natCast_mod, h]
  rfl

private theorem w5T_two_pow_cast_three_even {f : ℕ} (hf : f % 2 = 0) :
    (((2 ^ f : ℕ)) : ZMod 3) = 1 := by
  have h := tc_two_pow_mod_three f
  rw [if_pos hf] at h
  rw [← ZMod.natCast_mod, h]
  rfl

private theorem w5T_range_rootDiagUnit_eq {τ : Tag} {Lf : Type} [Field Lf]
    {Dg : Subgroup (ModGL τ Lf)}
    (a : ↥Dg → Fin τ.rank → Lfˣ) (ha : ∀ u : ↥Dg, (u : ModGL τ Lf) = rootDiagUnit τ (a u)) :
    (Set.range fun u : ↥Dg => rootDiagUnit τ (a u)) = (Dg : Set (ModGL τ Lf)) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    show rootDiagUnit τ (a u) ∈ (Dg : Set (ModGL τ Lf))
    rw [← ha u]
    exact u.2
  · intro hx
    exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩

private theorem w5T_component_eq_of_mem {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i j : KernelComponent χ}
    {γ : Fin τ.rank → ℤ} (hi : γ ∈ componentRoots χ i) (hj : γ ∈ componentRoots χ j) : i = j := by
  obtain ⟨h1, rfl⟩ := hi
  obtain ⟨h2, rfl⟩ := hj
  rfl

private theorem w5T_componentRoots_nonempty {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    ∃ γ, γ ∈ componentRoots χ i := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  exact ⟨x, x.2, rfl⟩

private theorem w5T_finite_of_le_gamma
    {τ : Tag} {Lf : Type} [Field Lf] [IsAlgClosed Lf] {p₀ : ℕ} (S : LangSetup τ Lf p₀)
    {Y : Subgroup (ModGL τ Lf)} (hY : Y ≤ S.Γ) : Finite ↥Y := by
  have := S.finite
  have hΓ : S.Γ ≤ S.D.model := Subgroup.commutator_le_self _
  exact Finite.of_injective (Subgroup.inclusion (hY.trans hΓ)) (Subgroup.inclusion_injective _)

private theorem w5T_centralizer_zpowers_eq_single {G : Type*} [Group G] (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

end Glue

section Survivor

theorem GGTCHyp.survivor_twE6
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel) (hG : GGTCInputG6InnerDiagLangTw)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hp : p = 3) (hf : 1 ≤ f)
    (act : TwE6Act G₀ B hf)
    (htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ d : ↥D, g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, h.d_le d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))) :
    f = 1 ∧ LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3 ∧
      (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 3 ∨
        LieModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 0 2 1 ∨
        LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1) := by
  classical
  subst hp
  have hDB : D ≤ B := h.d_le
  have hJG : J ≤ G₀ := h.j_comp.1.trans inf_le_left
  have hJcomp : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) :=
    Assembly.isComponentOf_iff_open.1 h.j_comp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', m, f', hlt, hm, -⟩ := id hF
  obtain ⟨S₁, hq, ⟨w, hρw⟩, fr, hΘ, hBimg, hDT, g₀, hg₀, hν⟩ :=
    exists_frameO_twE6_sub hf act hDB htor
  obtain ⟨w', hρ⟩ := rho_eq_neg_smul_of_twE6 hρw
  have hnotW := langSetup_rho_not_weyl_twE6 S₁ hρw
  set K : Type := GaloisField 2 (2 * f) with hKdef
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.exists_primitive_root_two
    (L := AlgebraicClosure K) Nat.prime_three (by norm_num)
  obtain ⟨a, i, ha, hap, hspan, h2⟩ := exists_family_dataO (uFieldInput_of_SL hR (Or.inl rfl))
    Nat.prime_three (by norm_num) S₁ hq fr hΘ hDT h.b_norm h.b_elem hDB hJG hJcomp
    ⟨t', m, f', hlt, hm⟩
  have hT : ∀ u : ↥(fr.DimgO D), rootDiagUnit .E6 (a u) ∈ S₁.D.torus := fun u =>
    (ha u) ▸ hDT u.2
  have hDcard : Nat.card ↥(fr.DimgO D) = 3 ^ 2 := by
    rw [fr.card_DimgO h.d_le, h.d_card]
  obtain ⟨P, hP2, hPmem, hPmul, hPinj⟩ := exists_tcPlane hζ (fr.DimgO D) hDcard a ha hap
  have hkerP := kernelRoots_famChar_eq_plane hζ a hap P hPmem
  obtain ⟨iJ, hiJ⟩ := exists_componentRoots_eq hkerP i
  have hJ2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) := by
    rw [← hiJ]
    exact h2
  have hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, (((S₁.ρ (Pi.single j 1)) k : ℤ) : ZMod 3) * v k = ((2 ^ f : ℕ) : ZMod 3) * v j := by
    intro v hv j
    have h1 := tcFrob_plane hζ S₁ a hap hT P hPmem v hv j
    rw [hq] at h1
    exact h1
  have hxB : x ∈ B := h.d_le h.x_mem
  have hxD : fr.ν ⟨x, hxB⟩ ∈ fr.DimgO D := fr.ν_mem_DimgO h.d_le h.x_mem
  set xg : ↥(fr.DimgO D) := ⟨fr.ν ⟨x, hxB⟩, hxD⟩ with hxg
  have hx1 : xg ≠ 1 := by
    intro h1
    have h2 : fr.ν ⟨x, hxB⟩ = 1 := congrArg Subtype.val h1
    have h3 : (⟨x, hxB⟩ : ↥B) = 1 := fr.νinj (h2.trans (map_one fr.ν).symm)
    exact h.x_ne (congrArg Subtype.val h3)
  have hax : rootDiagUnit .E6 (a xg) = fr.ν ⟨x, hxB⟩ := (ha xg).symm
  have hxP : tcExpVec hζ (a xg) (hap xg) ∈ P := (hPmem _).2 ⟨xg, rfl⟩
  have hx0 : tcExpVec hζ (a xg) (hap xg) ≠ 0 := fun h0 => hx1 (hPinj xg h0)
  have h1x : rootDiagUnit .E6 (a xg) ≠ 1 := fun h1 => hx1 (Subtype.ext ((ha xg).trans h1))
  have hJG : J ≤ G₀ := h.j_comp.1.trans inf_le_left
  have hJc : IsComponentOf (fr.JimgO J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : ↥(fr.DimgO D) => rootDiagUnit .E6 (a u))) := by
    rw [w5T_range_rootDiagUnit_eq a ha, ← hΘ]
    exact fr.isComponentOf_JimgO h.b_norm h.d_le hJG (Assembly.isComponentOf_iff_open.1 h.j_comp)
  have hLG : L ≤ G₀ := h.l_le
  have hLq : CFSG.Open.IsQuasisimple ↥L := (Assembly.isComponentOf_iff_open.1 h.l_comp).2.2
  have hLc0 := fr.isComponentOf_JimgO h.b_norm (D := Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxB)
    hLG (by
      rw [w5T_centralizer_zpowers_eq_single]
      exact Assembly.isComponentOf_iff_open.1 h.l_comp)
  rw [fr.centralizer_DimgO_zpowers hxB, ← hax, hΘ] at hLc0
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := fun h0 =>
    absurd ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 3).1 h0) (by norm_num)
  have hsmall : Tag.E6 = Tag.G2 → 5 ≤ 3 ∨ 4 ≤ S₁.D.q := fun h0 => absurd h0 (by decide)
  obtain ⟨ix₀, hsub₀, hJle₀, hRC⟩ := exists_rationalComponent_ge S₁ Nat.prime_three hpL hsmall a
    hT hap xg h1x i hJc (hJc.1.trans inf_le_left) hspan
  have : Finite ↥(S₁.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit .E6 (a xg)} : Set (ModGL .E6 (AlgebraicClosure K)))) :=
    w5T_finite_of_le_gamma S₁ inf_le_left
  have hLeq : fr.JimgO L = rationalComponent S₁.ρ S₁.Γ (rootCharHom (a xg)) ix₀ :=
    tc_components_eq hLc0 hRC (fr.JimgO_mono h.j_le_l) hJle₀
      (tc_exists_noncomm_of_isComponentOf hJc)
  obtain ⟨ixp, hixp⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq (a xg)).symm ix₀
  obtain ⟨ix, hix⟩ := exists_componentRoots_eq
    (kernelRoots_rootCharHom_eq_line hζ (a xg) (hap xg)) ix₀
  have hΨx : componentRoots (famCharHom (fun _ : PUnit.{1} => a xg)) ixp =
      componentRoots (tcChiLn Tag.E6 3 (tcExpVec hζ (a xg) (hap xg))) ix := hixp.symm.trans hix
  have hforb : famOrbit S₁.ρ (fun _ : PUnit.{1} => a xg) ixp =
      rationalRoots S₁.ρ (rootCharHom (a xg)) ix₀ := by
    ext γ
    simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
    rw [hixp]
  have hspanL : fr.JimgO L ≤ rootSpan .E6 (AlgebraicClosure K)
      (famOrbit S₁.ρ (fun _ : PUnit.{1} => a xg) ixp) := by
    rw [hLeq, hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hLc' : IsComponentOf (fr.JimgO L) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : PUnit.{1} => rootDiagUnit .E6 ((fun _ : PUnit.{1} => a xg) u))) := by
    have : (Set.range fun u : PUnit.{1} => rootDiagUnit .E6 ((fun _ : PUnit.{1} => a xg) u)) =
        {rootDiagUnit .E6 (a xg)} := Set.range_const
    rw [this]
    exact hLc0
  have hlabL := tc_langLabel hR2 (Or.inl rfl) S₁ Nat.prime_three (by norm_num) hq
    (fun _ : PUnit.{1} => a xg) (fun _ => hT xg) (fun _ j => hap xg j) hLc' ixp hspanL
  rw [hΨx] at hlabL
  have hJx : componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆
      componentRoots (tcChiLn Tag.E6 3 (tcExpVec hζ (a xg) (hap xg))) ix := by
    rw [← hiJ, ← hix]
    exact hsub₀
  have hne : componentRoots (tcChiLn Tag.E6 3 (tcExpVec hζ (a xg) (hap xg))) ix ≠
      componentRoots (tcChiPl Tag.E6 3 P) iJ := by
    intro heq
    have hsubK : componentRoots (famCharHom (fun _ : PUnit.{1} => a xg)) ixp ⊆
        kernelRoots (famCharHom a) := by
      rw [hΨx, heq, ← hiJ]
      exact fun α hα => hα.1
    have hcomm := tc_le_centralizer_of_kernel_le S₁ a ha hT xg ixp hsubK hspanL
    have hDC : D ≤ Subgroup.centralizer (L : Set X) :=
      fr.le_centralizer_of_langO_commute h.b_norm h.d_le hLG hLq.1 hcomm
    have hcyc : IsCyclic ↥D := h.l_cyc D hDC (IsPGroup.of_card h.d_card)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ 3 = 1 := Subtype.ext (by simpa using h.b_elem.2 g (h.d_le g.2))
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hgp
    rw [hord, h.d_card] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsplit : ∃ lab', GGLabelIso lab' (LabAt S₁.ρ f
      (componentRoots (tcChiLn Tag.E6 3 (tcExpVec hζ (a xg) (hap xg))) ix)) ∧
      LargeEvenSplit 3 lab' := by
    obtain ⟨e⟩ := fr.nonempty_equiv_JimgO hLG hLq
    have hlabL2 := ggHasLabel_of_mulEquiv e.symm hlabL.2.2.1
    obtain ⟨lab', hiso, hs⟩ := exists_labelIso_of_marking ggLabelRigidInput_holds h.l_split
      hlabL.1 hlabL2
    exact ⟨lab', ggLabelIso_symm hiso, hs⟩
  have hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • tcExpVec hζ (a xg) (hap xg)) →
      ∀ ik : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) ik →
      GGLabelIso (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E6 3 d) ik))
        (LabAt S₁.ρ f (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E6 3 d) ik)) ∧
        LargeEvenHalfSplit 3 lab' c := by
    intro d hd hd0 hdx ik hik
    obtain ⟨ud, hud⟩ := (hPmem d).1 hd
    subst hud
    have ha1 : a 1 = 1 :=
      rootDiagUnit_injective (by rw [← ha 1, Subgroup.coe_one, rootDiagUnit_one])
    have hvv1 : tcExpVec hζ (a 1) (hap 1) = 0 :=
      (tcExpVec_eq_zero_iff hζ (a 1) (hap 1)).2 fun j => congrFun ha1 j
    have : Finite ↥(fr.DimgO D) := Nat.finite_of_card_ne_zero (by rw [hDcard]; norm_num)
    have hud1 : ud ≠ 1 := fun h1 => hd0 (by rw [h1]; exact hvv1)
    have hudx : ud ∉ Subgroup.zpowers xg := by
      intro hmem
      obtain ⟨m, hm⟩ := tc_vec_of_mem_zpowers (fun u : ↥(fr.DimgO D) => tcExpVec hζ (a u) (hap u))
        hPmul hvv1 hmem
      exact hdx (m : ZMod 3) (by rw [hm, Nat.cast_smul_eq_nsmul])
    obtain ⟨b, hb, hbud⟩ := ud.2
    have hbD : (b : X) ∈ D := Subgroup.mem_subgroupOf.1 hb
    have hdB : (b : X) ∈ B := b.2
    have hbmk : (⟨(b : X), hdB⟩ : ↥B) = b := Subtype.ext rfl
    have hbud' : fr.ν ⟨(b : X), hdB⟩ = (ud : ModGL .E6 (AlgebraicClosure K)) := by
      rw [hbmk]
      exact hbud
    have hdXx : (b : X) ∉ Subgroup.zpowers x := by
      intro hm
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hm
      apply hudx
      refine Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext ?_⟩
      have hb' : b = (⟨x, hxB⟩ : ↥B) ^ m := Subtype.ext (by simpa using hm.symm)
      rw [← hbud, hb']
      simp only [Subgroup.coe_zpow]
      exact (map_zpow fr.ν (⟨x, hxB⟩ : ↥B) m).symm
    have h1d : rootDiagUnit .E6 (a ud) ≠ 1 := fun h1 => hud1 (Subtype.ext ((ha ud).trans h1))
    have hdud : rootDiagUnit .E6 (a ud) = fr.ν ⟨(b : X), hdB⟩ := by
      rw [← ha ud, hbud']
    obtain ⟨id₀, hsubd, hJled, hRCd⟩ := exists_rationalComponent_ge S₁ Nat.prime_three hpL hsmall
      a hT hap ud h1d i hJc (hJc.1.trans inf_le_left) hspan
    obtain ⟨ik', hik'⟩ := exists_componentRoots_eq
      (kernelRoots_rootCharHom_eq_line hζ (a ud) (hap ud)).symm ik
    obtain ⟨γ, hγ⟩ := w5T_componentRoots_nonempty iJ
    have hγ1 : γ ∈ componentRoots (famCharHom a) i := by
      rw [hiJ]
      exact hγ
    have hik'id : ik' = id₀ := w5T_component_eq_of_mem (by rw [← hik']; exact hik hγ) (hsubd hγ1)
    subst hik'id
    obtain ⟨idp, hidp⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq (a ud)).symm ik'
    have hΨd : componentRoots (famCharHom (fun _ : PUnit.{1} => a ud)) idp =
        componentRoots (tcChiLn Tag.E6 3 (tcExpVec hζ (a ud) (hap ud))) ik :=
      hidp.symm.trans hik'.symm
    have hforbd : famOrbit S₁.ρ (fun _ : PUnit.{1} => a ud) idp =
        rationalRoots S₁.ρ (rootCharHom (a ud)) ik' := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hidp]
    have hspanRC : rationalComponent S₁.ρ S₁.Γ (rootCharHom (a ud)) ik' ≤ rootSpan .E6
        (AlgebraicClosure K) (famOrbit S₁.ρ (fun _ : PUnit.{1} => a ud) idp) := by
      rw [hforbd]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    have hRC' : IsComponentOf (rationalComponent S₁.ρ S₁.Γ (rootCharHom (a ud)) ik')
        (S₁.Γ ⊓ Subgroup.centralizer (Set.range fun u : PUnit.{1} =>
          rootDiagUnit .E6 ((fun _ : PUnit.{1} => a ud) u))) := by
      have : (Set.range fun u : PUnit.{1} => rootDiagUnit .E6 ((fun _ : PUnit.{1} => a ud) u)) =
          {rootDiagUnit .E6 (a ud)} := Set.range_const
      rw [this]
      exact hRCd
    have hlabRC := tc_langLabel hR2 (Or.inl rfl) S₁ Nat.prime_three (by norm_num) hq
      (fun _ : PUnit.{1} => a ud) (fun _ => hT ud) (fun _ j => hap ud j) hRC' idp hspanRC
    rw [hΨd] at hlabRC
    obtain ⟨Kd, hKdG, hKdc0, hKdL⟩ := fr.exists_component_lift h.b_norm
      (D₁ := Subgroup.zpowers (b : X)) (Subgroup.zpowers_le.2 hdB) (by
        rw [fr.centralizer_DimgO_zpowers hdB, ← hdud, hΘ]
        exact hRCd)
    have hKdc : IsComponentOf Kd (G₀ ⊓ Subgroup.centralizer ({(b : X)} : Set X)) := by
      rw [← w5T_centralizer_zpowers_eq_single]
      exact hKdc0
    have hKdq : CFSG.Open.IsQuasisimple ↥Kd := hKdc.2.2
    have hJperf : commutator ↥J = ⊤ := (Assembly.isComponentOf_iff_open.1 h.j_comp).2.2.1
    have hJKd : J ≤ Kd := fr.le_of_JimgO_le hJG hJperf (by rw [hKdL]; exact hJled)
    have hlabJ := tc_langLabel hR2 (Or.inl rfl) S₁ Nat.prime_three (by norm_num) hq a hT hap hJc i
      hspan
    rw [hiJ] at hlabJ
    by_cases hKJ : Kd = J
    · left
      have hRCJ : rationalComponent S₁.ρ S₁.Γ (rootCharHom (a ud)) ik' = fr.JimgO J := by
        rw [← hKdL, hKJ]
      rw [hRCJ] at hlabRC
      exact tc_labelIso_of_compLabel hlabRC hlabJ
    · right
      obtain ⟨iR, -, hfield⟩ := hR .E6 (AlgebraicClosure K) _ 3 S₁ (Or.inl rfl) Nat.prime_three
        (by norm_num) _ a hT hap (fr.JimgO J) hJc
      rw [hq, ← pow_mul] at hfield
      obtain ⟨eJ⟩ := fr.exists_centerQuotEquivO hJG hJperf
      have hJcard : 3 ∣ Nat.card ↥J :=
        tc_three_dvd_card (hfield.of_centerQuotEquiv eJ.symm)
      have hinL := hG (AlgebraicClosure K) _ S₁ hnotW (a ud) (a xg) (hT ud) (hT xg) (hap ud)
        (hap xg) h1d _ hRCd
      rw [hax, ← hKdL] at hinL
      have hKdperf : commutator ↥Kd = ⊤ := hKdq.1
      have hKnorm := fr.zpowers_le_normalizer h.b_norm hxB hKdG hKdperf
        (ggInnerDiagOn_le_normalizer hinL)
      have hinner := fr.ggInnerDiagOn_of_lang hxB hKdG hKdperf hKnorm hinL
      have hnbr := h.nbr (b : X) hbD hdXx Kd (Assembly.isComponentOf_iff_open.2 hKdc) hJKd hKJ
        hJcard hinner
      rw [← hKdL] at hlabRC
      obtain ⟨e⟩ := fr.nonempty_equiv_JimgO hKdG hKdq
      have hhas := ggHasLabel_of_mulEquiv e.symm hlabRC.2.2.1
      obtain ⟨lab', hiso, hs⟩ := exists_labelIso_of_marking ggLabelRigidInput_holds hnbr hlabRC.1
        hhas
      exact ⟨_, lab', ggLabelIso_symm hiso, hs⟩
  have hJperf : commutator ↥J = ⊤ := hJcomp.2.2.1
  have hlabJ := tc_langLabel hR2 (Or.inl rfl) S₁ Nat.prime_three (by norm_num) hq a hT hap hJc i
    hspan
  rw [hiJ] at hlabJ
  obtain ⟨eJ, -⟩ := fr.exists_centerQuotEquivO hJG hJperf
  by_cases hfodd : f % 2 = 1
  · have hfodd' : f = 1 ∨ (3 ≤ f ∧ f % 2 = 1) := by
      rcases Nat.lt_or_ge f 3 with h3 | h3
      · left
        omega
      · exact Or.inr ⟨h3, hfodd⟩
    have hfrob2 : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
        ∑ k, (((S₁.ρ (Pi.single j 1)) k : ℤ) : ZMod 3) * v k = 2 * v j := by
      intro v hv j
      rw [hfrob v hv j, w5T_two_pow_cast_three hfodd]
    obtain ⟨hf1, hrow⟩ := tcC1_neg_odd_of_certificate w' S₁.ρ hρ hfodd' P hP2 hfrob2
      iJ hJ2 hxP hx0 ix hJx hne hsplit hoth
    subst hf1
    obtain ⟨hrJ, hNJ, heJ, hkJ, hxrow⟩ := hrow
    have hmodJ : LieModel (↥(fr.JimgO J) ⧸ Subgroup.center ↥(fr.JimgO J)) .PSL 2 2 3 :=
      tc_lieModel_of_labAt (r := 1) (e := 3) (f := 1) hrJ (by omega) hkJ heJ hlabJ
    refine ⟨rfl, lieModel_of_mulEquiv' eJ.symm hmodJ, ?_⟩
    obtain ⟨eL, -⟩ := fr.exists_centerQuotEquivO hLG hLq.1
    rcases hxrow with ⟨hrx, hNx, hex, hkx⟩ | ⟨hrx, hNx, hex, hkx⟩ | ⟨hrx, hNx, hex, hkx⟩
    · left
      exact lieModel_of_mulEquiv' eL.symm
        (tc_lieModel_of_labAt_suN (r := 2) (e := 3) (f := 1) hrx hkx hex hlabL)
    · right
      left
      exact lieModel_of_mulEquiv' eL.symm
        (tc_lieModel_of_labAt_exc (e := 1) (f := 1) hrx hkx hex hlabL)
    · right
      right
      exact lieModel_of_mulEquiv' eL.symm
        (tc_lieModel_of_labAt_suN (r := 5) (e := 1) (f := 1) hrx hkx hex hlabL)
  · exfalso
    have hf2 : 2 ≤ f ∧ f % 2 = 0 := by omega
    have hfrob1 : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
        ∑ k, (((S₁.ρ (Pi.single j 1)) k : ℤ) : ZMod 3) * v k = v j := by
      intro v hv j
      rw [hfrob v hv j, w5T_two_pow_cast_three_even hf2.2, one_mul]
    obtain ⟨hrJ, hNJ, heJ, hkJ, -⟩ := tcC1_neg_even_of_certificate w' S₁.ρ hρ hf2 P hP2
      hfrob1 iJ hJ2 hxP hx0 ix hJx hne hsplit hoth
    have hLab : LabAt S₁.ρ f (componentRoots (tcChiPl Tag.E6 3 P) iJ) =
        ⟨LargeEvenLieTag.A, 1, 2 * f⟩ := by
      unfold LabAt
      rw [hkJ, hrJ, heJ]
      simp [componentLabel, hNJ]
    have hlab2 := hlabJ.2.2.1
    rw [hLab] at hlab2
    exact false_of_fieldExt_label_A1_twE6 hJcomp.2.2 hf
      (ggHasLabel_of_mulEquiv eJ.symm hlab2) hF

end Survivor

end CFSG.StandardType.TableCRes

end
