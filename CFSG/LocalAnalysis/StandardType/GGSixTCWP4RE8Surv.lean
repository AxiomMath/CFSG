module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6TwoThree

public section

namespace CFSG.StandardType.TableCRes


open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso GGHasLabel GGInnerDiagOn)

section LangSurvivors

theorem tc_lang_survivors_E8_comp
    (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hpJ : p ∣ Nat.card ↥J)
    {K : Type} [Field K] [Finite K] [CharP K 2] {S₁ : LangSetup Tag.E8 (AlgebraicClosure K) 5}
    (fr₁ : GGTCUFrame S₁.Γ G₀ B) (hq : S₁.D.q = 2 ^ f) (hDT : fr₁.DLang D ≤ S₁.D.torus)
    (hρw : ∃ w : WeylGroup Tag.E8, ∀ γ, IsRoot Tag.E8 γ → S₁.ρ γ = w • γ)
    (a : ↥(fr₁.DLang D) → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (i : KernelComponent (famCharHom a))
    (ha : ∀ u : ↥(fr₁.DLang D),
      (u : ModGL Tag.E8 (AlgebraicClosure K)) = rootDiagUnit Tag.E8 (a u))
    (hap : ∀ u j, a u j ^ p = 1)
    (hspan : fr₁.JLang J ≤ rootSpan Tag.E8 (AlgebraicClosure K) (famOrbit S₁.ρ a i))
    (h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i)) :
    ∃ (P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p))
      (iJ : KernelComponent (tcChiPl Tag.E8 p P)) (x' : Fin Tag.E8.rank → ZMod p)
      (ix : KernelComponent (tcChiLn Tag.E8 p x')),
      Module.finrank (ZMod p) P = 2 ∧
      (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
        ∑ k, (((S₁.ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = ((2 ^ f : ℕ) : ZMod p) * v j) ∧
      2 ≤ componentOrbitLength S₁.ρ (componentRoots (tcChiPl Tag.E8 p P) iJ) ∧
      x' ∈ P ∧ x' ≠ 0 ∧
      componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p x') ix ∧
      componentRoots (tcChiLn Tag.E8 p x') ix ≠ componentRoots (tcChiPl Tag.E8 p P) iJ ∧
      (∃ lab', GGLabelIso lab' (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p x') ix)) ∧
        LargeEvenSplit p lab') ∧
      (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x') →
        ∀ ik : KernelComponent (tcChiLn Tag.E8 p d),
        componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p d) ik →
        GGLabelIso (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p d) ik))
          (LabAt S₁.ρ f (componentRoots (tcChiPl Tag.E8 p P) iJ)) ∨
        ∃ (c : Prop) (lab' : LargeEvenLabel),
          GGLabelIso lab' (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p d) ik)) ∧
          LargeEvenHalfSplit p lab' c) ∧
      componentRoots (tcChiPl Tag.E8 p P) iJ = componentRoots (famCharHom a) i := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : NeZero p := ⟨h.prime.ne_zero⟩
  have : Fact (Nat.Prime p) := ⟨h.prime⟩
  obtain ⟨ζ, hζ⟩ := HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.exists_primitive_root_two
    (L := AlgebraicClosure K) h.prime h.ne_two
  have hT : ∀ u : ↥(fr₁.DLang D), rootDiagUnit .E8 (a u) ∈ S₁.D.torus := fun u =>
    (ha u) ▸ hDT u.2
  have hDcard : Nat.card ↥(fr₁.DLang D) = p ^ 2 := by
    rw [fr₁.card_DLang h.d_le, h.d_card]
  obtain ⟨P, hP2, hPmem, hPmul, hPinj⟩ := exists_tcPlane hζ (fr₁.DLang D) hDcard a ha hap
  have hkerP := kernelRoots_famChar_eq_plane hζ a hap P hPmem
  obtain ⟨iJ, hiJ⟩ := exists_componentRoots_eq hkerP i
  have hJ2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (tcChiPl Tag.E8 p P) iJ) := by
    rw [← hiJ]
    exact h2
  have hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, (((S₁.ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = ((2 ^ f : ℕ) : ZMod p) * v j := by
    intro v hv j
    have h1 := tcFrob_plane hζ S₁ a hap hT P hPmem v hv j
    rw [hq] at h1
    exact h1
  have hxB : x ∈ B := h.d_le h.x_mem
  have hxD : fr₁.toLang ⟨x, hxB⟩ ∈ fr₁.DLang D := fr₁.toLang_mem_DLang h.d_le h.x_mem
  set xg : ↥(fr₁.DLang D) := ⟨fr₁.toLang ⟨x, hxB⟩, hxD⟩ with hxg
  have hx1 : xg ≠ 1 := by
    intro h1
    have h2 : fr₁.toLang ⟨x, hxB⟩ = 1 := congrArg Subtype.val h1
    have h3 : (⟨x, hxB⟩ : ↥B) = 1 := fr₁.toLang_injective (h2.trans (map_one fr₁.toLang).symm)
    exact h.x_ne (congrArg Subtype.val h3)
  have hax : rootDiagUnit .E8 (a xg) = fr₁.toLang ⟨x, hxB⟩ := (ha xg).symm
  have hxP : tcExpVec hζ (a xg) (hap xg) ∈ P := (hPmem _).2 ⟨xg, rfl⟩
  have hx0 : tcExpVec hζ (a xg) (hap xg) ≠ 0 := fun h0 => hx1 (hPinj xg h0)
  have h1x : rootDiagUnit .E8 (a xg) ≠ 1 := fun h1 => hx1 (Subtype.ext ((ha xg).trans h1))
  have hJG : J ≤ G₀ := h.j_comp.1.trans inf_le_left
  have hJc : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : ↥(fr₁.DLang D) => rootDiagUnit .E8 (a u))) := by
    rw [tc_range_rootDiagUnit_eq a ha]
    exact fr₁.isComponentOf_JLang h.d_le hJG (Assembly.isComponentOf_iff_open.1 h.j_comp)
  have hLG : L ≤ G₀ := h.l_le
  have hLq : CFSG.Open.IsQuasisimple ↥L := (Assembly.isComponentOf_iff_open.1 h.l_comp).2.2
  have hLc0 := fr₁.isComponentOf_JLang (D := Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxB)
    hLG (by
      rw [centralizer_zpowers_eq_single]
      exact Assembly.isComponentOf_iff_open.1 h.l_comp)
  rw [fr₁.centralizer_DLang_zpowers hxB, ← hax] at hLc0
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := fun h0 =>
    h.ne_two ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h0)).symm
  have hsmall : Tag.E8 = Tag.G2 → 5 ≤ p ∨ 4 ≤ S₁.D.q := fun h0 => absurd h0 (by decide)
  obtain ⟨ix₀, hsub₀, hJle₀, hRC⟩ := exists_rationalComponent_ge S₁ h.prime hpL hsmall a
    hT hap xg h1x i hJc (hJc.1.trans inf_le_left) hspan
  have : Finite ↥(S₁.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit .E8 (a xg)} : Set (ModGL .E8 (AlgebraicClosure K)))) :=
    tc_finite_of_le_gamma S₁ inf_le_left
  have hLeq : fr₁.JLang L = rationalComponent S₁.ρ S₁.Γ (rootCharHom (a xg)) ix₀ :=
    tc_components_eq hLc0 hRC (fr₁.JLang_mono h.j_le_l) hJle₀
      (tc_exists_noncomm_of_isComponentOf hJc)
  obtain ⟨ixp, hixp⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq (a xg)).symm ix₀
  obtain ⟨ix, hix⟩ := exists_componentRoots_eq
    (kernelRoots_rootCharHom_eq_line hζ (a xg) (hap xg)) ix₀
  have hΨx : componentRoots (famCharHom (fun _ : PUnit.{1} => a xg)) ixp =
      componentRoots (tcChiLn Tag.E8 p (tcExpVec hζ (a xg) (hap xg))) ix := hixp.symm.trans hix
  have hforb : famOrbit S₁.ρ (fun _ : PUnit.{1} => a xg) ixp =
      rationalRoots S₁.ρ (rootCharHom (a xg)) ix₀ := by
    ext γ
    simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
    rw [hixp]
  have hspanL : fr₁.JLang L ≤ rootSpan .E8 (AlgebraicClosure K)
      (famOrbit S₁.ρ (fun _ : PUnit.{1} => a xg) ixp) := by
    rw [hLeq, hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hLc' : IsComponentOf (fr₁.JLang L) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : PUnit.{1} => rootDiagUnit .E8 ((fun _ : PUnit.{1} => a xg) u))) := by
    have : (Set.range fun u : PUnit.{1} => rootDiagUnit .E8 ((fun _ : PUnit.{1} => a xg) u)) =
        {rootDiagUnit .E8 (a xg)} := Set.range_const
    rw [this]
    exact hLc0
  have hlabL := tc_langLabel hR2 (Or.inr rfl) S₁ h.prime h.ne_two hq
    (fun _ : PUnit.{1} => a xg) (fun _ => hT xg) (fun _ j => hap xg j) hLc' ixp hspanL
  rw [hΨx] at hlabL
  have hJx : componentRoots (tcChiPl Tag.E8 p P) iJ ⊆
      componentRoots (tcChiLn Tag.E8 p (tcExpVec hζ (a xg) (hap xg))) ix := by
    rw [← hiJ, ← hix]
    exact hsub₀
  have hne : componentRoots (tcChiLn Tag.E8 p (tcExpVec hζ (a xg) (hap xg))) ix ≠
      componentRoots (tcChiPl Tag.E8 p P) iJ := by
    intro heq
    have hsubK : componentRoots (famCharHom (fun _ : PUnit.{1} => a xg)) ixp ⊆
        kernelRoots (famCharHom a) := by
      rw [hΨx, heq, ← hiJ]
      exact fun α hα => hα.1
    have hcomm := tc_le_centralizer_of_kernel_le S₁ a ha hT xg ixp hsubK hspanL
    have hDC : D ≤ Subgroup.centralizer (L : Set X) :=
      fr₁.le_centralizer_of_lang_commute h.d_le hLG hLq.1 hcomm
    have hcyc : IsCyclic ↥D := h.l_cyc D hDC (IsPGroup.of_card h.d_card)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using h.b_elem.2 g (h.d_le g.2))
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rw [hord, h.d_card] at hdvd
    have hle := Nat.le_of_dvd h.prime.pos hdvd
    have h1 := h.prime.one_lt
    nlinarith
  have hsplit : ∃ lab', GGLabelIso lab' (LabAt S₁.ρ f
      (componentRoots (tcChiLn Tag.E8 p (tcExpVec hζ (a xg) (hap xg))) ix)) ∧
      LargeEvenSplit p lab' := by
    obtain ⟨e⟩ := fr₁.nonempty_equiv_JLang hLG hLq
    have hlabL2 := ggHasLabel_of_mulEquiv e.symm hlabL.2.2.1
    obtain ⟨lab', hiso, hs⟩ := exists_labelIso_of_marking ggLabelRigidInput_holds h.l_split
      hlabL.1 hlabL2
    exact ⟨lab', ggLabelIso_symm hiso, hs⟩
  have hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • tcExpVec hζ (a xg) (hap xg)) →
      ∀ ik : KernelComponent (tcChiLn Tag.E8 p d),
      componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p d) ik →
      GGLabelIso (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p d) ik))
        (LabAt S₁.ρ f (componentRoots (tcChiPl Tag.E8 p P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p d) ik)) ∧
        LargeEvenHalfSplit p lab' c := by
    intro d hd hd0 hdx ik hik
    obtain ⟨ud, hud⟩ := (hPmem d).1 hd
    subst hud
    have ha1 : a 1 = 1 :=
      rootDiagUnit_injective (by rw [← ha 1, Subgroup.coe_one, rootDiagUnit_one])
    have hvv1 : tcExpVec hζ (a 1) (hap 1) = 0 :=
      (tcExpVec_eq_zero_iff hζ (a 1) (hap 1)).2 fun j => congrFun ha1 j
    have : Finite ↥(fr₁.DLang D) :=
      Nat.finite_of_card_ne_zero (by rw [hDcard]; exact pow_ne_zero 2 h.prime.ne_zero)
    have hud1 : ud ≠ 1 := fun h1 => hd0 (by rw [h1]; exact hvv1)
    have hudx : ud ∉ Subgroup.zpowers xg := by
      intro hmem
      obtain ⟨m, hm⟩ := tc_vec_of_mem_zpowers (fun u : ↥(fr₁.DLang D) => tcExpVec hζ (a u) (hap u))
        hPmul hvv1 hmem
      exact hdx (m : ZMod p) (by rw [hm, Nat.cast_smul_eq_nsmul])
    obtain ⟨_, ⟨b, hb, rfl⟩, hbud⟩ := ud.2
    have hbD : (b : X) ∈ D := Subgroup.mem_subgroupOf.1 hb
    have hdB : (b : X) ∈ B := b.2
    have hbmk : (⟨(b : X), hdB⟩ : ↥B) = b := Subtype.ext rfl
    have hbud' : fr₁.toLang ⟨(b : X), hdB⟩ = (ud : ModGL .E8 (AlgebraicClosure K)) := by
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
      exact (map_zpow fr₁.toLang (⟨x, hxB⟩ : ↥B) m).symm
    have h1d : rootDiagUnit .E8 (a ud) ≠ 1 := fun h1 => hud1 (Subtype.ext ((ha ud).trans h1))
    have hdud : rootDiagUnit .E8 (a ud) = fr₁.toLang ⟨(b : X), hdB⟩ := by
      rw [← ha ud, hbud']
    obtain ⟨id₀, hsubd, hJled, hRCd⟩ := exists_rationalComponent_ge S₁ h.prime hpL hsmall
      a hT hap ud h1d i hJc (hJc.1.trans inf_le_left) hspan
    obtain ⟨ik', hik'⟩ := exists_componentRoots_eq
      (kernelRoots_rootCharHom_eq_line hζ (a ud) (hap ud)).symm ik
    obtain ⟨γ, hγ⟩ := tc_componentRoots_nonempty iJ
    have hγ1 : γ ∈ componentRoots (famCharHom a) i := by
      rw [hiJ]
      exact hγ
    have hik'id : ik' = id₀ :=
      eq_of_mem_componentRoots (by rw [← hik']; exact hik hγ) (hsubd hγ1)
    subst hik'id
    obtain ⟨idp, hidp⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq (a ud)).symm ik'
    have hΨd : componentRoots (famCharHom (fun _ : PUnit.{1} => a ud)) idp =
        componentRoots (tcChiLn Tag.E8 p (tcExpVec hζ (a ud) (hap ud))) ik :=
      hidp.symm.trans hik'.symm
    have hforbd : famOrbit S₁.ρ (fun _ : PUnit.{1} => a ud) idp =
        rationalRoots S₁.ρ (rootCharHom (a ud)) ik' := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hidp]
    have hspanRC : rationalComponent S₁.ρ S₁.Γ (rootCharHom (a ud)) ik' ≤ rootSpan .E8
        (AlgebraicClosure K) (famOrbit S₁.ρ (fun _ : PUnit.{1} => a ud) idp) := by
      rw [hforbd]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    have hRC' : IsComponentOf (rationalComponent S₁.ρ S₁.Γ (rootCharHom (a ud)) ik')
        (S₁.Γ ⊓ Subgroup.centralizer (Set.range fun u : PUnit.{1} =>
          rootDiagUnit .E8 ((fun _ : PUnit.{1} => a ud) u))) := by
      have : (Set.range fun u : PUnit.{1} => rootDiagUnit .E8 ((fun _ : PUnit.{1} => a ud) u)) =
          {rootDiagUnit .E8 (a ud)} := Set.range_const
      rw [this]
      exact hRCd
    have hlabRC := tc_langLabel hR2 (Or.inr rfl) S₁ h.prime h.ne_two hq
      (fun _ : PUnit.{1} => a ud) (fun _ => hT ud) (fun _ j => hap ud j) hRC' idp hspanRC
    rw [hΨd] at hlabRC
    obtain ⟨Kd, hKdG, hKdc, hKdL⟩ := fr₁.exists_tcComponent_lift (d := (b : X)) hdB (by
      rw [← hdud]
      exact hRCd)
    have hKdq : CFSG.Open.IsQuasisimple ↥Kd := hKdc.2.2
    have hJperf : commutator ↥J = ⊤ := (Assembly.isComponentOf_iff_open.1 h.j_comp).2.2.1
    have hJKd : J ≤ Kd := tc_le_of_JLang_le fr₁ hJG hKdG hJperf (by rw [hKdL]; exact hJled)
    have hlabJ := tc_langLabel hR2 (Or.inr rfl) S₁ h.prime h.ne_two hq a hT hap hJc i
      hspan
    rw [hiJ] at hlabJ
    by_cases hKJ : Kd = J
    · left
      have hRCJ : rationalComponent S₁.ρ S₁.Γ (rootCharHom (a ud)) ik' = fr₁.JLang J := by
        rw [← hKdL, hKJ]
      rw [hRCJ] at hlabRC
      exact tc_labelIso_of_compLabel hlabRC hlabJ
    · right
      have hinL := hG6 .E8 (AlgebraicClosure K) _ p S₁ (Or.inl rfl) hρw h.prime h.ne_two (a ud)
        (a xg) (hT ud) (hT xg) (hap ud) (hap xg) h1d _ hRCd
      rw [hax, ← hKdL] at hinL
      have hKdperf : commutator ↥Kd = ⊤ := hKdq.1
      have hKnorm := fr₁.tcZpowers_le_normalizer hxB hKdG hKdperf
        (ggInnerDiagOn_le_normalizer hinL)
      have hinner := fr₁.ggInnerDiagOn_of_lang hxB hKdG hKdperf hKnorm hinL
      have hnbr := h.nbr (b : X) hbD hdXx Kd (Assembly.isComponentOf_iff_open.2 hKdc) hJKd hKJ
        hpJ hinner
      rw [← hKdL] at hlabRC
      obtain ⟨e⟩ := fr₁.nonempty_equiv_JLang hKdG hKdq
      have hhas := ggHasLabel_of_mulEquiv e.symm hlabRC.2.2.1
      obtain ⟨lab', hiso, hs⟩ := exists_labelIso_of_marking ggLabelRigidInput_holds hnbr hlabRC.1
        hhas
      exact ⟨_, lab', ggLabelIso_symm hiso, hs⟩
  exact ⟨P, iJ, tcExpVec hζ (a xg) (hap xg), ix, hP2, hfrob, hJ2, hxP, hx0, hJx, hne, hsplit, hoth,
    hiJ.symm⟩

theorem tc_lang_survivors_E8
    (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hpJ : p ∣ Nat.card ↥J)
    {K : Type} [Field K] [Finite K] [CharP K 2] {S₁ : LangSetup Tag.E8 (AlgebraicClosure K) 5}
    (fr₁ : GGTCUFrame S₁.Γ G₀ B) (hq : S₁.D.q = 2 ^ f) (hDT : fr₁.DLang D ≤ S₁.D.torus)
    (hρw : ∃ w : WeylGroup Tag.E8, ∀ γ, IsRoot Tag.E8 γ → S₁.ρ γ = w • γ)
    (a : ↥(fr₁.DLang D) → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (i : KernelComponent (famCharHom a))
    (ha : ∀ u : ↥(fr₁.DLang D),
      (u : ModGL Tag.E8 (AlgebraicClosure K)) = rootDiagUnit Tag.E8 (a u))
    (hap : ∀ u j, a u j ^ p = 1)
    (hspan : fr₁.JLang J ≤ rootSpan Tag.E8 (AlgebraicClosure K) (famOrbit S₁.ρ a i))
    (h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i)) :
    ∃ (P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p))
      (iJ : KernelComponent (tcChiPl Tag.E8 p P)) (x' : Fin Tag.E8.rank → ZMod p)
      (ix : KernelComponent (tcChiLn Tag.E8 p x')),
      Module.finrank (ZMod p) P = 2 ∧
      (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
        ∑ k, (((S₁.ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = ((2 ^ f : ℕ) : ZMod p) * v j) ∧
      2 ≤ componentOrbitLength S₁.ρ (componentRoots (tcChiPl Tag.E8 p P) iJ) ∧
      x' ∈ P ∧ x' ≠ 0 ∧
      componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p x') ix ∧
      componentRoots (tcChiLn Tag.E8 p x') ix ≠ componentRoots (tcChiPl Tag.E8 p P) iJ ∧
      (∃ lab', GGLabelIso lab' (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p x') ix)) ∧
        LargeEvenSplit p lab') ∧
      (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x') →
        ∀ ik : KernelComponent (tcChiLn Tag.E8 p d),
        componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p d) ik →
        GGLabelIso (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p d) ik))
          (LabAt S₁.ρ f (componentRoots (tcChiPl Tag.E8 p P) iJ)) ∨
        ∃ (c : Prop) (lab' : LargeEvenLabel),
          GGLabelIso lab' (LabAt S₁.ρ f (componentRoots (tcChiLn Tag.E8 p d) ik)) ∧
          LargeEvenHalfSplit p lab' c) := by
  obtain ⟨P, iJ, x', ix, hP2, hfrob, hJ2, hxP, hx0, hJx, hne, hsplit, hoth, -⟩ :=
    tc_lang_survivors_E8_comp hR2 hG6 h hpJ fr₁ hq hDT hρw a i ha hap hspan h2
  exact ⟨P, iJ, x', ix, hP2, hfrob, hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩

end LangSurvivors

end CFSG.StandardType.TableCRes

end
