module

public import CFSG.LocalAnalysis.StandardType.ExcPos.LangFrameDefs
public import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcLangFrame

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes CFSG.StandardType.LieCore CFSG.Assembly
  CFSG.LocalAnalysis.ComponentInitial



private theorem u1aD_x_mem {t : StatedLieTag} {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) : x ∈ D := by
  rw [← F.closure_eq]
  exact Subgroup.subset_closure (by simp)

private theorem u1aD_jointChar_eq_one {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) {γ : Fin τ.rank → ℤ} :
    LieCore.jointChar a₁ a₂ (Multiplicative.ofAdd γ) = 1 ↔
      rootChar a₁ γ = 1 ∧ rootChar a₂ γ = 1 := by
  simp [LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom]

private theorem u1aD_mapsTo_rho_chiD {t : StatedLieTag} {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    Set.MapsTo F.ρ (kernelRoots F.chiD) (kernelRoots F.chiD) := by
  intro γ hγ
  obtain ⟨hroot, hchar⟩ := hγ
  have hpair : rootChar (F.coord x) γ = 1 ∧ rootChar (F.coord F.d) γ = 1 :=
    (u1aD_jointChar_eq_one (F.coord x) (F.coord F.d)).1 hchar
  refine ⟨(F.frob.isRoot_iff γ).2 hroot, ?_⟩
  refine (u1aD_jointChar_eq_one (F.coord x) (F.coord F.d)).2 ⟨?_, ?_⟩
  · rw [F.frob.rootChar_eq (F.coord x) (F.coord_torus x (u1aD_x_mem F)) γ hroot, hpair.1,
      one_pow]
  · rw [F.frob.rootChar_eq (F.coord F.d) (F.coord_torus F.d F.d_mem) γ hroot, hpair.2,
      one_pow]

private theorem u1aD_kernelRoots_famChar_eq {t : StatedLieTag} {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    kernelRoots (famCharHom (![F.coord x, F.coord F.d] :
        Fin 2 → Fin (langTag t).rank → GGLˣ)) = kernelRoots F.chiD := by
  ext γ
  rw [mem_kernelRoots_famChar]
  constructor
  · rintro ⟨hroot, h⟩
    have h0 : rootChar (F.coord x) γ = 1 := by simpa using h 0
    have h1 : rootChar (F.coord F.d) γ = 1 := by simpa using h 1
    exact ⟨hroot, (u1aD_jointChar_eq_one (F.coord x) (F.coord F.d)).2 ⟨h0, h1⟩⟩
  · rintro ⟨hroot, hchar⟩
    refine ⟨hroot, fun u => ?_⟩
    have hp := (u1aD_jointChar_eq_one (F.coord x) (F.coord F.d)).1 hchar
    fin_cases u
    · simpa using hp.1
    · simpa using hp.2

private theorem u1aD_componentLabel_n {r N n : ℕ} {k : TwistKind} :
    (componentLabel r N k n).n = n := by
  cases k with
  | inner => unfold componentLabel; split_ifs <;> rfl
  | suN => rfl
  | twoD => rfl
  | exc => unfold componentLabel; split_ifs <;> rfl

private theorem u1aD_le_markDeg_componentLabel {r N n : ℕ} {k : TwistKind} :
    n ≤ markDeg (componentLabel r N k n) := by
  cases k <;> simp only [componentLabel]
  · split_ifs <;> simp [markDeg]
  · simp [markDeg]
  · by_cases hr : r = 2
    · simp [markDeg, hr]; omega
    · simp [markDeg, hr]
  · split_ifs <;> simp [markDeg]

theorem componentOrbitLength_eq_one {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {ψ : (ggU t n f).K →* X}
    {G₀ B₁ D J L : Subgroup X} {x : X} (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) (iJ : KernelComponent F.chiD)
    (hJ : (J.subgroupOf G₀).map F.η = LieCore.ratComp F.ρ F.Δ.Γ (componentRoots F.chiD iJ)) :
    componentOrbitLength F.ρ (componentRoots F.chiD iJ) = 1 := by
  classical
  obtain ⟨h1ψ, h2ker, h3model, h4odd, h5p, h6p2, h7B1G0, h8inner, h9abel, h10p4,
    h11DB, h12Dcard, h13B1J, h14centJ, h15Jcomp, h16oddZ, h17xD, h18xne, h19LG0,
    h20Lcomp, h21JL, h22notDCL, h23mark, h24B1L, h25mark2, h26notA3, h27notE6,
    h28notA6, h29notField, h30, h31⟩ := h
  have hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  haveI : CharP GGL 2 := inferInstance
  obtain ⟨S, hSD, hSρ⟩ := exists_langSetup_of_datum F.Δ F.ρ F.frob F.finite F.one_le_f F.q_eq
  let a : Fin 2 → Fin (langTag t).rank → GGLˣ := ![F.coord x, F.coord F.d]
  have hxmem : x ∈ D := u1aD_x_mem F
  have hT : ∀ u, rootDiagUnit (langTag t) (a u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · simpa [a, hSD] using F.coord_torus x hxmem
    · simpa [a, hSD] using F.coord_torus F.d F.d_mem
  have hap : ∀ u j, a u j ^ p = 1 := by
    intro u j
    fin_cases u
    · simpa [a] using F.coord_pow x hxmem j
    · simpa [a] using F.coord_pow F.d F.d_mem j
  have h1 : ∃ u, rootDiagUnit (langTag t) (a u) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hx1 : rootDiagUnit (langTag t) (F.coord x) = 1 := by simpa [a] using hcon 0
    have hd1 : rootDiagUnit (langTag t) (F.coord F.d) = 1 := by simpa [a] using hcon 1
    have hxΘ : F.Θ ⟨x, h11DB hxmem⟩ = 1 := by
      rw [F.Θ_eq_coord ⟨x, h11DB hxmem⟩ hxmem, hx1]
    have hdΘ : F.Θ ⟨F.d, h11DB F.d_mem⟩ = 1 := by
      rw [F.Θ_eq_coord ⟨F.d, h11DB F.d_mem⟩ F.d_mem, hd1]
    let Ksub : Subgroup ↥D :=
      Subgroup.comap (Subgroup.inclusion h11DB) (MonoidHom.ker F.Θ)
    have hDle : D ≤ Subgroup.map D.subtype Ksub := by
      have hcl : Subgroup.closure ({x, F.d} : Set X) ≤ Subgroup.map D.subtype Ksub := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with h | h
        · rw [h]
          exact ⟨⟨x, hxmem⟩, hxΘ, rfl⟩
        · rw [h]
          exact ⟨⟨F.d, F.d_mem⟩, hdΘ, rfl⟩
      rwa [F.closure_eq] at hcl
    have hDcent : D ≤ Subgroup.centralizer (G₀ : Set X) := by
      intro e he
      obtain ⟨k, hk, hke⟩ := hDle he
      have hk' : F.Θ (Subgroup.inclusion h11DB k) = 1 := by
        have hk'' : Subgroup.inclusion h11DB k ∈ F.Θ.ker := hk
        exact MonoidHom.mem_ker.1 hk''
      have hΘ1 : F.Θ ⟨e, h11DB he⟩ = 1 := by
        subst hke
        exact hk'
      exact (F.Θ_eq_one ⟨e, h11DB he⟩).1 hΘ1
    exact h22notDCL (hDcent.trans (Subgroup.centralizer_le h19LG0))
  have hpos : 0 < componentOrbitLength F.ρ (componentRoots F.chiD iJ) :=
    componentOrbitLength_componentRoots_pos (u1aD_mapsTo_rho_chiD F) iJ
  by_contra hbne
  have hb2 : 2 ≤ componentOrbitLength F.ρ (componentRoots F.chiD iJ) := by omega
  obtain ⟨i', hi'⟩ := exists_componentRoots_eq (u1aD_kernelRoots_famChar_eq F).symm iJ
  let K : Subgroup (ModGL (langTag t) GGL) :=
    LieCore.ratComp F.ρ F.Δ.Γ (componentRoots F.chiD iJ)
  have hJG0 : J ≤ G₀ := h15Jcomp.1.trans inf_le_left
  let ψJ : ↥J →* ModGL (langTag t) GGL :=
    F.η.comp (Subgroup.inclusion hJG0)
  have hψJmem : ∀ j, ψJ j ∈ K := by
    intro j
    have hmem : ψJ j ∈ (J.subgroupOf G₀).map F.η :=
      ⟨⟨j, hJG0 j.2⟩, j.2, rfl⟩
    rwa [hJ] at hmem
  let φ : ↥J →* ↥K := ψJ.codRestrict K hψJmem
  have hφsurj : Function.Surjective φ := by
    intro k
    have hk : (k : ModGL (langTag t) GGL) ∈ (J.subgroupOf G₀).map F.η := by
      rw [hJ]; exact k.2
    obtain ⟨g, hg, hgk⟩ := hk
    exact ⟨⟨g, hg⟩, by apply Subtype.ext; exact hgk⟩
  have hkerη : F.η.ker = Subgroup.center ↥G₀ := F.ker_η
  have hφker : φ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro j'
    have hj1 : F.η ⟨j, hJG0 j.2⟩ = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
      change F.η ⟨j, hJG0 j.2⟩ = 1 at h
      exact h
    have hjker : (⟨j, hJG0 j.2⟩ : ↥G₀) ∈ F.η.ker := MonoidHom.mem_ker.2 hj1
    have hjcenter : (⟨j, hJG0 j.2⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      rwa [hkerη] at hjker
    apply Subtype.ext
    change (j' : X) * (j : X) = (j : X) * (j' : X)
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hjcenter ⟨j', hJG0 j'.2⟩)
  have hJqs : CFSG.IsQuasisimple ↥J :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥J).2.1.mpr h15Jcomp.2.2
  have hφne : ∃ j, φ j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hJcenter : ∀ j : ↥J, (⟨j, hJG0 j.2⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      intro j
      have hj1 : F.η ⟨j, hJG0 j.2⟩ = 1 := by
        have h := congrArg Subtype.val (hcon j)
        change F.η ⟨j, hJG0 j.2⟩ = 1 at h
        exact h
      have hjker : (⟨j, hJG0 j.2⟩ : ↥G₀) ∈ F.η.ker := MonoidHom.mem_ker.2 hj1
      rwa [hkerη] at hjker
    have hcommJ : ∀ a b : ↥J, a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact (congrArg Subtype.val
        (Subgroup.mem_center_iff.1 (hJcenter a) ⟨b, hJG0 b.2⟩)).symm
    haveI : IsMulCommutative ↥J := IsMulCommutative.of_comm hcommJ
    haveI : Group.IsPerfect ↥J := hJqs.1
    haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJqs.2.1.toNontrivial
    haveI : Nontrivial ↥J :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative ↥J) inferInstance
  have hKq : CFSG.IsQuasisimple ↥K :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hJqs hφsurj hφne
  have hqs' : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i') := by
    have hKq' : CFSG.IsQuasisimple ↥(LieCore.ratComp S.ρ S.D.Γ
        (componentRoots (famCharHom a) i')) := by
      rw [hSρ, hSD, ← hi']
      exact hKq
    rwa [ratComp_eq_rationalComponentM] at hKq'
  have hFam : FamLabelAt S (famCharHom a) i' :=
    langFamRatLabel_of_lanes langFamRatLabel_typeA langFamRatLabel_inner
      langFamRatLabel_outerD_high langFamRatLabel_outerD_four langFamRatLabel_outerE
      (langTag t) GGL 5 S hτ p h5p h6p2 (Fin 2) a hT hap h1 i' hqs'
  have hfq : S.D.q = 2 ^ f := by rw [hSD]; exact F.q_eq
  have hKi : K = rationalComponentM S.ρ S.Γ (famCharHom a) i' := by
    change LieCore.ratComp F.ρ F.Δ.Γ (componentRoots F.chiD iJ) =
      rationalComponentM S.ρ S.Γ (famCharHom a) i'
    rw [hi', ratComp_eq_rationalComponentM, ← hSρ, ← hSD]
    rfl
  obtain ⟨nlab, hnlab, hlabn⟩ :=
    langFamilyCompLabel_conclusion_of_famLabelAt S i' hKi hFam
  have h2n : (2 : ℕ) ^ nlab =
      2 ^ (componentOrbitLength S.ρ (componentRoots (famCharHom a) i') * f) := by
    rw [hnlab, hfq, ← pow_mul, mul_comm]
  have hnf : nlab = componentOrbitLength S.ρ (componentRoots (famCharHom a) i') * f :=
    Nat.pow_right_injective (le_refl 2) h2n
  let lab : LargeEvenLabel := LabAt S.ρ f (componentRoots (famCharHom a) i')
  have hlab : GGCompLabelAt lab K := by
    change GGCompLabelAt (LabAt S.ρ f (componentRoots (famCharHom a) i')) K
    unfold LabAt
    rw [← hnf]
    exact hlabn
  obtain ⟨-, hchar, -, R, instR, hR, ⟨eR⟩⟩ := hlab
  letI : Group R := instR
  let t' : StatedLieTag := markTag lab
  let m : ℕ := markRank lab
  let f' : ℕ := markDeg lab
  have hR' : CFSG.Blueprint.LieModel R t' m 2 f' := by
    unfold CFSG.StandardType.MarkedModel at hR
    rwa [hchar] at hR
  have hKmodel : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) t' m 2 f' :=
    CFSG.Blueprint.LieModel.of_mulEquiv eR.symm hR'
  obtain ⟨eJ⟩ := center_quotient_equiv_of_surjective hJqs φ hφsurj hφker
  have hJmodel : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f' :=
    CFSG.Blueprint.LieModel.of_mulEquiv eJ.symm hKmodel
  have hb2' : 2 ≤ componentOrbitLength S.ρ (componentRoots (famCharHom a) i') := by
    simpa [hSρ, hi'] using hb2
  have hf1 : 1 ≤ f := F.one_le_f
  have hlabn' : lab.n = componentOrbitLength S.ρ (componentRoots (famCharHom a) i') * f := by
    unfold lab LabAt
    exact u1aD_componentLabel_n
  have hdeg : componentOrbitLength S.ρ (componentRoots (famCharHom a) i') * f ≤ f' := by
    rw [← hlabn']
    dsimp only [lab, LabAt, f']
    rw [u1aD_componentLabel_n]
    exact u1aD_le_markDeg_componentLabel
  have hff' : f < f' := by
    have hbf : f < componentOrbitLength S.ρ (componentRoots (famCharHom a) i') * f := by
      nlinarith
    omega
  exact h29notField ⟨t', m, f', hff', hJmodel, by
    rintro ⟨-, -, hPSU | hTw⟩
    · rcases ht with rfl | rfl | rfl <;> exact absurd hPSU (by decide)
    · rcases ht with rfl | rfl | rfl <;> exact absurd hTw (by decide)⟩

end CFSG.StandardType.LieKnownR2.ExcPos.ExcLangFrame
