module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviCell
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviStabThree
public import CFSG.LocalAnalysis.StandardType.GGTBJE6Three
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeCount
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeRootPts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJE6Levi_of_threeCoordData
    {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G} {g : G} (hgBs : g ∈ Bs)
    (hJX : J ≤ X) (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    {P : Prop} (hC : GGE6ThreeCoordData Bs X J g hgBs P) (hP : ¬ P)
    (bX : ↥Bs) (hbX1 : bX ≠ 1) (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 3) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ι, φ, h, α, f, κW, cd, K, hKfield, ζ, hζ, hζo, hlin,
    hrefl, hpair, hf, hclos, hκW, hcd, hrange, hcdW, hTD, hkerX, hg1, i, hCENT, hLow,
    hD4cl⟩ := hC
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  letI : Field K := hKfield
  let gB : ↥Bs := ⟨g, hgBs⟩
  let x_g : Fin Tag.E6.rank → ZMod 3 := Multiplicative.toAdd (cd gB)
  let a : Fin Tag.E6.rank → Kˣ := TableBExc.E6Three.zetaVec ζ hζ x_g
  have hxg_ne : x_g ≠ 0 := by
    intro h0
    apply hg1
    have h1 : Multiplicative.ofAdd x_g = 1 := by rw [h0]; rfl
    simpa [x_g, gB] using h1
  have ha : ∀ j, a j ^ 3 = 1 := by
    intro j
    change (TableBExc.E6Three.zetaVec ζ hζ x_g j) ^ 3 = 1
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hc
    have h1 : ∀ j, a j = 1 := fun j => by
      by_contra hj
      exact hc ⟨j, hj⟩
    have hone : TableBExc.E6Three.zetaVec ζ hζ x_g = 1 := by
      funext j
      exact h1 j
    have hx0 : x_g = 0 := by
      apply TableBExc.E6Three.zetaVec_injective hζo hζ
      rw [hone]
      funext j
      rw [TableBExc.E6Three.zetaVec_apply]
      simp
    exact hxg_ne hx0
  have hprim : IsPrimitiveRoot (ζ : K) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζo)
  have h3 := e6Three_rank_ge_three cd hrange (componentRoots (rootCharHom a) i) hCENT
    bX hbX1 (hkerX bX hbXc) hcardJ
  obtain ⟨v₀, S, hS, hΨeq⟩ :=
    e6_class_levi (p := 3) Nat.prime_three (by norm_num) hprim a ha ha1 i h3
  let F : WeylGroup .E6 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp κW.toMonoidHom
  let Fw : WeylGroup .E6 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
  have hFwdef : ∀ u, Fw u = (f (κW u) : MulAut ↥Bs) := fun u => rfl
  have hlower : ∀ c ∈ componentRoots (rootCharHom a) i,
      Fw (rootReflection c) ∈ ggAutomizer J Bs := by
    intro c hc
    obtain ⟨n, hn⟩ := hLow c hc
    have hnJ : ggTDρB J Bs n ∈ ggAutomizer J Bs := by
      rw [← ggTDρB_range]
      exact ⟨n, rfl⟩
    let nX : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(n : G), hJX n.2.1, n.2.2⟩
    have hnX : ggTDρB X Bs nX = ggTDρB J Bs n := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [ggTDρB_apply, ggTDρB_apply]
    have hTDn : ggTDρB X Bs nX = (f (κW (rootReflection c)) : MulAut ↥Bs) := by
      refine hTD nX (rootReflection c) ?_
      intro b
      rw [hnX]
      exact hn b
    rw [hFwdef, ← hTDn, hnX]
    exact hnJ
  have hupper : ∀ t ∈ ggAutomizer J Bs,
      t ∈ (Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i)).map Fw := by
    intro t ht
    obtain ⟨j, hjJ, hjN, hφt⟩ := mem_ggAutomizer_iff.mp ht
    have htX : t ∈ ggAutomizer X Bs := mem_ggAutomizer_iff.mpr ⟨j, hJX hjJ, hjN, hφt⟩
    let w : WeylGroup .E6 := κW.symm (f.symm ⟨t, htX⟩)
    have hFwu : Fw w = t := by
      rw [hFwdef]
      change ((f (κW (κW.symm (f.symm ⟨t, htX⟩))) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = t
      simp
    have htfix : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (J : Set G) → t b = b := by
      intro b hb
      apply Subtype.ext
      rw [hφt b, (Subgroup.mem_centralizer_iff.mp hb) j hjJ]
      group
    have htg : t gB = gB := by
      apply Subtype.ext
      have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp (hJg hjJ))
      calc ((t gB : ↥Bs) : G) = j * (gB : G) * j⁻¹ := hφt gB
        _ = (gB : G) := by
            change j * g * j⁻¹ = g
            rw [hcomm]
            group
    have hws : adAct .E6 3 w x_g = x_g := by
      have h1 : cd gB = Multiplicative.ofAdd (adAct .E6 3 w x_g) := by
        have h := hcdW w gB
        rw [← hFwdef w, hFwu, htg] at h
        exact h
      have h2 : Multiplicative.ofAdd x_g = Multiplicative.ofAdd (adAct .E6 3 w x_g) := by
        calc Multiplicative.ofAdd x_g = cd gB := rfl
          _ = Multiplicative.ofAdd (adAct .E6 3 w x_g) := h1
      exact (Multiplicative.ofAdd.injective h2).symm
    have hwstab : w ∈ rootCharStabilizerSubgroup a := by
      rw [mem_rootCharStabilizerSubgroup]
      intro c
      change rootChar a (w • c) = rootChar a c
      rw [NoOffE8Five.rootChar_zetaVec hζ, NoOffE8Five.rootChar_zetaVec hζ]
      have hdot : (∑ j, ((w • c) j : ZMod 3) * x_g j) =
          ∑ j, (c j : ZMod 3) * x_g j := by
        have h := e6Three_dot_adAct w c x_g
        rwa [hws] at h
      rw [hdot]
    have hwfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ∀ j, ((w • c) j : ZMod 3) = (c j : ZMod 3) := by
      intro c hcK hcΨ
      have hrange_x : ∀ x ∈ NoOffRest.hypE6, ∃ b : ↥Bs, Multiplicative.toAdd (cd b) = x := by
        intro x hx
        have hxr : Multiplicative.ofAdd x ∈ cd.range := by
          rcases hrange with hr | hr
          · rw [hr]; exact Subgroup.mem_top _
          · exact (hr x).2 hx
        obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hxr
        exact ⟨b, by simpa using congrArg Multiplicative.toAdd hb⟩
      obtain ⟨b_c, hbc⟩ := hrange_x (e6ThreeRootPt c) (e6ThreeRootPt_mem_hypE6 c)
      have hc_mem : c ∈ componentRoots (rootCharHom a) ⟦⟨c, hcK⟩⟧ := ⟨hcK, rfl⟩
      have hne : (⟦⟨c, hcK⟩⟧ : KernelComponent (rootCharHom a)) ≠ i := by
        intro heq
        exact hcΨ (by rwa [heq] at hc_mem)
      have horth : ∀ γ ∈ componentRoots (rootCharHom a) i,
          ∑ j, (γ j : ZMod 3) * e6ThreeRootPt c j = 0 := by
        intro γ hγ
        rw [e6ThreeRootPt_dot]
        have hform : CFSG.LieType.Steinberg.Adjoint.iform γ c = 0 :=
          CFSG.LieType.Chevalley.iform_eq_zero_of_mem_componentRoots hne.symm hγ hc_mem
        rw [hform, Int.cast_zero]
      have hbC : (b_c : G) ∈ Subgroup.centralizer (J : Set G) :=
        hCENT b_c (fun γ hγ => by rw [hbc]; exact horth γ hγ)
      have h1 : cd b_c = Multiplicative.ofAdd (adAct .E6 3 w (e6ThreeRootPt c)) := by
        have h := hcdW w b_c
        rw [← hFwdef w, hFwu, htfix b_c hbC, hbc] at h
        exact h
      have hsmul : adAct .E6 3 w (e6ThreeRootPt c) = e6ThreeRootPt c := by
        apply Multiplicative.ofAdd.injective
        calc Multiplicative.ofAdd (adAct .E6 3 w (e6ThreeRootPt c))
            = cd b_c := h1.symm
          _ = Multiplicative.ofAdd (e6ThreeRootPt c) := congrArg Multiplicative.ofAdd hbc
      have hroot' : IsRoot .E6 (w • c) := IsRoot.smul hcK.1 w
      have heqpt : e6ThreeRootPt (w • c) = e6ThreeRootPt c := by
        rw [e6ThreeRootPt_smul, hsmul]
      exact e6ThreeRootPt_injOn hroot' hcK.1 heqpt
    have hD4' : ∀ v : WeylGroup .E6, componentRoots (rootCharHom a) i ≠
        (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))} :=
      fun v hv => hP (hD4cl ⟨v, hv⟩)
    have hwcl := mem_closure_rootReflection_of_fix_E6_three ha i h3 hD4' hwstab hwfix
    exact ⟨w, hwcl, hFwu⟩
  have hJeq : ggAutomizer J Bs =
      (Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i)).map Fw := by
    apply le_antisymm
    · intro t ht
      exact hupper t ht
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨r, ⟨c, hc, rfl⟩, rfl⟩
      exact hlower c hc
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .E6 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, rfl⟩
  have hpar : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure ((fun j : Fin 6 => v₀ * simple .E6 j * v₀⁻¹) ''
        {j : Fin 6 | j ∉ S}) := by
    rw [hset, hΨeq, closure_rootReflection_smul_parabolicRoots (τ := .E6) v₀]
    rfl
  have hψsimple : ∀ j, Fw (simple .E6 j) = φ j := by
    intro j
    rw [hFwdef, hκW j]
    exact hf j
  let u : CoxeterMatrix.E₆.Group := κW v₀
  have hJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 6 // j ∉ S} =>
        (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := by
    rw [hJeq, hpar, MonoidHom.map_closure, Set.image_image, Set.image_eq_range]
    congr 1
    ext t
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [map_mul, map_mul, map_inv, hψsimple j, hFwdef v₀]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [map_mul, map_mul, map_inv, hψsimple j, hFwdef v₀]⟩
  exact ggE6LeviDatum_of_conj (p := 3) (by norm_num) hlin hrefl hpair hf hclos u hS hJ'

end CFSG.StandardType

end
