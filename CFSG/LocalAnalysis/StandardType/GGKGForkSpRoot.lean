module

public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGSpRootGenAvoid
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp

open SpCoord Multiplicative CFSG.SeitzReduction.SymplecticPilot
  CFSG.SeitzReduction.OmegaPilot NbrSp ReflSp CFSG.Quasithin
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spIncl spIncl_apply leviEmbedSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)

private theorem ggKGSpR_spPermSp_eq_permSp {K : Type} [Field K] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    NbrSp.spPermSp (K := K) σ = permSp K σ := by
  apply Subtype.ext
  apply Units.ext
  change mat n K (NbrSp.spPermSp (K := K) σ) = mat n K (permSp K σ)
  rw [mat_permSp]
  ext a b
  rw [spIncl_apply, mat_apply]
  simp only [NbrSp.spPermSp, NbrSp.pairPerm]
  rw [TauCeti.permutationGL_coe]
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  apply propext
  constructor
  · intro h
    rw [← h]
    simp [Equiv.Perm.coe_inv]
  · intro h
    rw [h]
    simp [Equiv.Perm.coe_inv]

private theorem ggKGSpR_spPermSp_swap_mem_siegelBlock {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (a b : Fin n) :
    NbrSp.spPermSp (K := K) (Equiv.swap a b) ∈ siegelBlock K ({a, b} : Finset (Fin n)) := by
  rw [ggKGSpR_spPermSp_eq_permSp]
  rw [siegelBlock]
  exact ⟨q2SwapSL a b, q2SwapSL_mem_blockSpecialLinear a b,
    (CFSG.SeitzReduction.OmegaPilot.permSp_swap_eq a b).symm⟩

private theorem ggKGSpR_map_centralizer_of_bij {G H : Type} [Group G] [Group H] (f : G →* H)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) (s : Set G) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s f) ?_
  rintro y hy
  obtain ⟨x, rfl⟩ := hsurj y
  refine Subgroup.mem_map_of_mem f ?_
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro a ha
  have h2 : f a ∈ f '' s := ⟨a, ha, rfl⟩
  exact hinj (by rw [map_mul, map_mul]; exact hy (f a) h2)

private theorem ggKGSpR_proj_spTorusSp {K : Type} [Field K] {n : ℕ}
    {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) (f : Fin n → Multiplicative (ZMod p)) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K (spTorusSp (m := n) hζ f) =
      spTorus (m := n) hζ f := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj]
  rfl

private theorem ggKGSpR_negSgn_eq {p k : ℕ} {a b : Fin k} :
    (sgnAut (p := p) b * permAut (Equiv.swap a b) * sgnAut (p := p) b :
        MulAut (Fin k → Multiplicative (ZMod p))) =
      sgnAut (p := p) a * sgnAut (p := p) b * permAut (Equiv.swap a b) := by
  have hcomm : (permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod p))) *
      sgnAut (p := p) b = sgnAut (p := p) a * permAut (Equiv.swap a b) := by
    have h := IsSignedPerm.mul_sgnAut
      (u := (permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod p))))
      (π := Equiv.swap a b) (ε := fun _ => (1 : ZMod p))
      (by
        intro f i
        show toAdd ((permAut (Equiv.swap a b) f) ((Equiv.swap a b) i)) = 1 * toAdd (f i)
        rw [permAut_apply, Function.comp_apply]
        simp) b
    rw [Equiv.swap_apply_right] at h
    exact h
  calc (sgnAut (p := p) b * permAut (Equiv.swap a b) * sgnAut (p := p) b :
        MulAut (Fin k → Multiplicative (ZMod p)))
      = sgnAut (p := p) b * (permAut (Equiv.swap a b) * sgnAut (p := p) b) := by group
    _ = sgnAut (p := p) b * (sgnAut (p := p) a * permAut (Equiv.swap a b)) := by rw [hcomm]
    _ = sgnAut (p := p) a * sgnAut (p := p) b * permAut (Equiv.swap a b) := by
      rw [sgnAut_mul_comm]; group

private abbrev ggKGSpR_Idx (n : ℕ) : Type :=
  Fin n ⊕ {q : Fin n × Fin n // q.1 ≠ q.2} ⊕ {q : Fin n × Fin n // q.1 ≠ q.2}

private noncomputable def ggKGSpR_W {K : Type} [Field K] [CharP K 2] {n : ℕ} :
    ggKGSpR_Idx n → LargeEvenProj (LargeEvenSpGroup K n) :=
  Sum.elim (fun i => LargeEvenProjMk _ (spSwapSp i))
    (Sum.elim (fun q => LargeEvenProjMk _ (NbrSp.spPermSp (K := K) (Equiv.swap q.1.1 q.1.2)))
      (fun q => LargeEvenProjMk _ (spSwapSp q.1.2) *
        LargeEvenProjMk _ (NbrSp.spPermSp (K := K) (Equiv.swap q.1.1 q.1.2)) *
        (LargeEvenProjMk _ (spSwapSp q.1.2))⁻¹))

private noncomputable def ggKGSpR_s {n p : ℕ} :
    ggKGSpR_Idx n → MulAut (Fin n → Multiplicative (ZMod p)) :=
  Sum.elim (fun i => sgnAut i)
    (Sum.elim (fun q => permAut (Equiv.swap q.1.1 q.1.2))
      (fun q => sgnAut q.1.1 * sgnAut q.1.2 * permAut (Equiv.swap q.1.1 q.1.2)))

private noncomputable def ggKGSpR_S {K : Type} [Field K] [CharP K 2] {n : ℕ} :
    ggKGSpR_Idx n → Subgroup (LargeEvenProj (LargeEvenSpGroup K n)) :=
  Sum.elim (fun i => (spBlock K ({i} : Finset (Fin n))).map (LargeEvenProjMk _))
    (Sum.elim (fun q => (siegelBlock K ({q.1.1, q.1.2} : Finset (Fin n))).map (LargeEvenProjMk _))
      (fun q => ((siegelBlock K ({q.1.1, q.1.2} : Finset (Fin n))).map
        (MulAut.conj (spSwapSp q.1.2 : LargeEvenSpGroup K n)).toMonoidHom).map
        (LargeEvenProjMk _)))

private theorem ggKGSpR_negWeyl {R : Type} [Group R] {n p : ℕ} {a b : Fin n}
    {τ : (Fin n → Multiplicative (ZMod p)) →* R} {xb wab : R}
    (hxb : ∀ f, xb * τ f * xb⁻¹ = τ (sgnAut (p := p) b f))
    (hwab : ∀ f, wab * τ f * wab⁻¹ = τ (permAut (p := p) (Equiv.swap a b) f))
    (f : Fin n → Multiplicative (ZMod p)) :
    (xb * wab * xb⁻¹) * τ f * (xb * wab * xb⁻¹)⁻¹ =
      τ ((sgnAut (p := p) a * sgnAut (p := p) b * permAut (p := p) (Equiv.swap a b) :
        MulAut (Fin n → Multiplicative (ZMod p))) f) := by
  have hxb_inv : ∀ g, xb⁻¹ * τ g * xb = τ (sgnAut (p := p) b g) := by
    intro g
    have hss : sgnAut (p := p) b (sgnAut (p := p) b g) = g := by
      have hB : (sgnAut (p := p) b : MulAut (Fin n → Multiplicative (ZMod p))) *
          sgnAut (p := p) b = 1 := by
        have := sgnAut_sq (p := p) b
        simpa [sq] using this
      have h1 : ((sgnAut (p := p) b : MulAut (Fin n → Multiplicative (ZMod p))) *
          sgnAut (p := p) b) g = g := by rw [hB, MulAut.one_apply]
      simpa only [MulAut.mul_apply] using h1
    have h := hxb (sgnAut (p := p) b g)
    rw [hss] at h
    calc xb⁻¹ * τ g * xb = xb⁻¹ * (xb * τ (sgnAut (p := p) b g) * xb⁻¹) * xb := by rw [← h]
      _ = τ (sgnAut (p := p) b g) := by group
  calc (xb * wab * xb⁻¹) * τ f * (xb * wab * xb⁻¹)⁻¹
      = xb * (wab * (xb⁻¹ * τ f * xb) * wab⁻¹) * xb⁻¹ := by group
    _ = xb * (wab * τ (sgnAut (p := p) b f) * wab⁻¹) * xb⁻¹ := by rw [hxb_inv f]
    _ = xb * τ (permAut (p := p) (Equiv.swap a b) (sgnAut (p := p) b f)) * xb⁻¹ := by rw [hwab]
    _ = τ (sgnAut (p := p) b (permAut (p := p) (Equiv.swap a b) (sgnAut (p := p) b f))) :=
        hxb _
    _ = τ ((sgnAut (p := p) a * sgnAut (p := p) b * permAut (p := p) (Equiv.swap a b) :
          MulAut (Fin n → Multiplicative (ZMod p))) f) := by
        congr 1
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ggKGSpR_negSgn_eq]

private theorem ggKGSpR_hws {K : Type} [Field K] [CharP K 2] {n p : ℕ} {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (i : ggKGSpR_Idx n) (f : Fin n → Multiplicative (ZMod p)) :
    ggKGSpR_W i * spTorus (m := n) hζ f * (ggKGSpR_W i)⁻¹ =
      spTorus (m := n) hζ (ggKGSpR_s i f) := by
  rcases i with i | q | q
  · exact spSwap_conj_spTorus (K := K) (m := n) hζ i f
  · exact SpModel.projMk_spPermSp_conj_spTorus (K := K) (m := n) hζ (Equiv.swap q.1.1 q.1.2) f
  · exact ggKGSpR_negWeyl (p := p)
      (hxb := spSwap_conj_spTorus (K := K) (m := n) hζ q.1.2)
      (hwab := SpModel.projMk_spPermSp_conj_spTorus (K := K) (m := n) hζ
        (Equiv.swap q.1.1 q.1.2)) f

private theorem ggKGSpR_isSignedPerm_of_conj {K : Type} [Field K] [CharP K 2] {n p : ℕ}
    [NeZero n] (hp : p.Prime) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {g : LargeEvenProj (LargeEvenSpGroup K n)}
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : ∀ f, g * spTorus (m := n) hζ f * g⁻¹ = spTorus (m := n) hζ (u f)) :
    IsSignedPerm ⇑u := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hxinj : Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K) :=
    AutPSp.proj_injective (n := n) (K := K)
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin n ⊕ Fin n) K).subgroupOf (LargeEvenSpGroup K n)) g
  have hproj : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K g₀ = g := hg₀
  have hgconj : ∀ f, g₀ * spTorusSp (m := n) hζ f * g₀⁻¹ = spTorusSp (m := n) hζ (u f) := by
    intro f
    apply hxinj
    calc CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K
            (g₀ * spTorusSp (m := n) hζ f * g₀⁻¹)
        = CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K g₀ *
            CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K (spTorusSp (m := n) hζ f) *
            (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K g₀)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = g * spTorus (m := n) hζ f * g⁻¹ := by
          rw [hproj, ggKGSpR_proj_spTorusSp (K := K) (n := n) hζ f]
      _ = spTorus (m := n) hζ (u f) := hu f
      _ = CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K
            (spTorusSp (m := n) hζ (u f)) :=
          (ggKGSpR_proj_spTorusSp (K := K) (n := n) hζ (u f)).symm
  obtain ⟨j, ε, hε, hj⟩ := ReflSp.exists_monomial_data hζo hζ (g₀ : GL (Fin n ⊕ Fin n) K)
  have hGL : ∀ f, (g₀ : GL (Fin n ⊕ Fin n) K) * spTorusGL (m := n) hζ f =
      spTorusGL (m := n) hζ (u f) * (g₀ : GL (Fin n ⊕ Fin n) K) := by
    intro f
    have h1 := congrArg (fun y : LargeEvenSpGroup K n => (y : GL (Fin n ⊕ Fin n) K)) (hgconj f)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe] at h1
    rw [← h1]
    group
  have hji : Function.Injective j := by
    intro i i' hii
    by_contra hne
    have h1 := hj (Pi.mulSingle i (ofAdd (1 : ZMod p)))
      (u (Pi.mulSingle i (ofAdd (1 : ZMod p)))) (hGL (Pi.mulSingle i (ofAdd (1 : ZMod p)))) i
    have h2 := hj (Pi.mulSingle i (ofAdd (1 : ZMod p)))
      (u (Pi.mulSingle i (ofAdd (1 : ZMod p)))) (hGL (Pi.mulSingle i (ofAdd (1 : ZMod p)))) i'
    rw [hii] at h1
    rw [h1] at h2
    simp only [toAdd_mulSingle, ↓reduceIte, if_neg (Ne.symm hne), mul_one, mul_zero] at h2
    rcases hε i with h | h <;> rw [h] at h2
    · exact coord_zero_ne_one hp h2.symm
    · exact coord_zero_ne_one hp (neg_eq_zero.mp h2).symm
  refine ⟨Equiv.ofBijective j hji.bijective_of_finite, ε, hε, fun f i => ?_⟩
  exact hj f (u f) (hGL f) i

private theorem ggKGSpR_isComponentOf_of_perfectCore_eq {G : Type*} [Group G] {C S : Subgroup G}
    (h : perfectCore C = S) (hq : CFSG.Assembly.IsQuasisimple S) :
    CFSG.Assembly.IsComponentOf S C := by
  subst h
  exact ⟨perfectCore_le C, CFSG.Assembly.IsSubnormal.step (perfectCore_le C)
    (perfectCore_normal C) (CFSG.Assembly.IsSubnormal.refl _), hq⟩

private theorem ggKGSpR_spTorusSp_eq_diagSp {K : Type} [Field K] {n p : ℕ} {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (f : Fin n → Multiplicative (ZMod p)) :
    (spTorusSp (m := n) hζ f : LargeEvenSpGroup K n) =
      diagSp K n fun j => zmodPowHom hζ (f j) := by
  refine mat_injective ?_
  rw [mat_diagSp, mat_apply, spTorusSp_coe, spTorusGL_apply, TauCeti.diagGL_coe]
  congr 1
  funext x
  rcases x with j | j <;> rfl

private theorem ggKGSpR_spBlock_univ {K : Type} [Field K] {n : ℕ} :
    spBlock K (Finset.univ : Finset (Fin n)) = ⊤ :=
  eq_top_iff.mpr fun _ _ a b hab =>
    (hab ⟨Finset.mem_univ (planeOf a), Finset.mem_univ (planeOf b)⟩).elim

private theorem ggKGSpR_sgnAut_eq_self_iff {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin k)
    (f : Fin k → Multiplicative (ZMod p)) : sgnAut i f = f ↔ f i = 1 := by
  constructor
  · intro h
    have h1 := congrFun h i
    rw [sgnAut_apply, Function.update_self] at h1
    have h2 : toAdd (f i) = -toAdd (f i) := by rw [← toAdd_inv, h1]
    rw [← ofAdd_toAdd (f i), coord_eq_zero_of_eq_neg hp hp2 h2, ofAdd_zero]
  · intro h
    rw [sgnAut_apply, h, inv_one, ← h, Function.update_eq_self]

private theorem ggKGSpR_permAut_swap_eq_self_iff {p k : ℕ} {a b : Fin k}
    (f : Fin k → Multiplicative (ZMod p)) :
    permAut (Equiv.swap a b) f = f ↔ f a = f b := by
  constructor
  · intro h
    have h1 := congrFun h a
    rw [permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext j
    rw [permAut_apply, Function.comp_apply, Equiv.swap_inv]
    by_cases hja : j = a
    · subst hja
      rw [Equiv.swap_apply_left, h]
    · by_cases hjb : j = b
      · subst hjb
        rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

private theorem ggKGSpR_comp_mulSingle {K : Type} [Field K] {n p : ℕ}
    (χ : Multiplicative (ZMod p) →* Kˣ) (j : Fin n) (x : Multiplicative (ZMod p)) :
    (fun k => χ ((Pi.mulSingle j x : Fin n → Multiplicative (ZMod p)) k)) =
      Pi.mulSingle j (χ x) := by
  funext k
  exact Pi.apply_mulSingle (fun _ => χ) (fun _ => map_one χ) j x k

private theorem ggKGSpR_zeta_mul_self_ne_one {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) : ζ * ζ ≠ 1 := by
  intro h
  have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  rw [hζo] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)

private theorem ggKGSpR_zmodPowHom_one {K : Type} [Field K] {p : ℕ} {ζ : Kˣ}
    (hζ : ζ ^ p = 1) : zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) = ζ := by
  have h1 := zmodPowHom_natCast hζ 1
  rwa [Nat.cast_one, pow_one] at h1

private theorem ggKGSpR_statedComp_sgn {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (h4 : 4 ≤ Nat.card K) (i : Fin n) :
    CFSG.Assembly.IsComponentOf (spBlock K ({i} : Finset (Fin n)))
      (Subgroup.centralizer ((spTorusSp (m := n) hζ : _ →* LargeEvenSpGroup K n) ''
        {f : Fin n → Multiplicative (ZMod p) | sgnAut i f = f})) := by
  have hκ : ζ * ζ ≠ 1 := ggKGSpR_zeta_mul_self_ne_one hp hp2 hζo
  have hχg : zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) = ζ := ggKGSpR_zmodPowHom_one hζ
  have hcent : Subgroup.centralizer ((spTorusSp (m := n) hζ : _ →* LargeEvenSpGroup K n) ''
        {f : Fin n → Multiplicative (ZMod p) | sgnAut i f = f}) =
      spBlock K (Finset.univ : Finset (Fin n)) ⊓ Subgroup.centralizer
        (diagSp K n '' ((fun f j => zmodPowHom hζ (f j)) ''
          {f : Fin n → Multiplicative (ZMod p) | sgnAut i f = f})) := by
    rw [ggKGSpR_spBlock_univ, top_inf_eq]
    congr 1
    rw [Set.image_image]
    exact Set.image_congr fun f _ => ggKGSpR_spTorusSp_eq_diagSp hζ f
  rw [hcent]
  refine ggKGSpR_isComponentOf_of_perfectCore_eq
    (perfectCore_spBlock_inf_centralizer_eq (Finset.subset_univ _) _
      ?_ ?_ (commutator_spBlock_eq h4 _)) ?_
  · rintro _ ⟨f, hf, rfl⟩ x hx y hy
    have hfr : f i = 1 := (ggKGSpR_sgnAut_eq_self_iff hp hp2 i f).1 hf
    have ht : (fun j => zmodPowHom hζ (f j)) ∈ planeTorusParam K ({i} : Finset (Fin n)) :=
      fun j hj => show zmodPowHom hζ (f j) = 1 by
        rw [Finset.mem_singleton.1 hj, hfr, map_one]
    rw [diagSpEntry_eq_one_of_mem_planeTorusParam ht hx,
      diagSpEntry_eq_one_of_mem_planeTorusParam ht hy]
  · rintro x - y - hxy hI
    have key : ∀ j : Fin n, j ≠ i →
        diagSpEntry (Pi.mulSingle j ζ) x ≠ diagSpEntry (Pi.mulSingle j ζ) y →
        ∃ s ∈ (fun f j => zmodPowHom hζ (f j)) ''
          {f : Fin n → Multiplicative (ZMod p) | sgnAut i f = f},
          diagSpEntry s x ≠ diagSpEntry s y := by
      intro j hji hne
      refine ⟨_, ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_, rfl⟩, ?_⟩
      · exact (ggKGSpR_sgnAut_eq_self_iff hp hp2 i _).2 (Pi.mulSingle_eq_of_ne (Ne.symm hji) _)
      · beta_reduce
        rw [ggKGSpR_comp_mulSingle, hχg]
        exact hne
    rcases hI with hx | hy
    · exact key (planeOf x) (fun h => hx (by rw [mem_planeCoords, h]; simp))
        (diagSpEntry_mulSingle_ne hκ hxy (Or.inl (mem_coords_planeOf x)))
    · exact key (planeOf y) (fun h => hy (by rw [mem_planeCoords, h]; simp))
        (diagSpEntry_mulSingle_ne hκ hxy (Or.inr (mem_coords_planeOf y)))
  · refine Assembly.IsQuasisimple.of_mulEquiv (spBlockEquiv (F := K) ({i} : Finset (Fin n))).symm ?_
    rw [Finset.card_singleton]
    have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 1 K le_rfl (Or.inl (Or.inr h4))
    exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

private theorem ggKGSpR_statedComp_swap {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (h4 : 4 ≤ Nat.card K) {a b : Fin n} (hab : a ≠ b) :
    CFSG.Assembly.IsComponentOf (siegelBlock K ({a, b} : Finset (Fin n)))
      (Subgroup.centralizer ((spTorusSp (m := n) hζ : _ →* LargeEvenSpGroup K n) ''
        {f : Fin n → Multiplicative (ZMod p) | permAut (Equiv.swap a b) f = f})) := by
  have hκ : ζ * ζ ≠ 1 := ggKGSpR_zeta_mul_self_ne_one hp hp2 hζo
  have hχg : zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) = ζ := ggKGSpR_zmodPowHom_one hζ
  have hcent : Subgroup.centralizer ((spTorusSp (m := n) hζ : _ →* LargeEvenSpGroup K n) ''
        {f : Fin n → Multiplicative (ZMod p) | permAut (Equiv.swap a b) f = f}) =
      spBlock K (Finset.univ : Finset (Fin n)) ⊓ Subgroup.centralizer
        (diagSp K n '' ((fun f j => zmodPowHom hζ (f j)) ''
          {f : Fin n → Multiplicative (ZMod p) | permAut (Equiv.swap a b) f = f})) := by
    rw [ggKGSpR_spBlock_univ, top_inf_eq]
    congr 1
    rw [Set.image_image]
    exact Set.image_congr fun f _ => ggKGSpR_spTorusSp_eq_diagSp hζ f
  rw [hcent]
  refine ggKGSpR_isComponentOf_of_perfectCore_eq
    (perfectCore_spBlock_inf_centralizer_eq_siegelBlock (Finset.subset_univ _) _ ?_ ?_
      (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
        (by rw [Finset.card_pair hab]) h4)) ?_
  · rintro _ ⟨f, hf, rfl⟩ i hi j hj
    have hfab : f a = f b := (ggKGSpR_permAut_swap_eq_self_iff f).1 hf
    have hc : ∀ k ∈ ({a, b} : Finset (Fin n)), f k = f a := fun k hk => by
      rcases Finset.mem_insert.1 hk with rfl | hk
      · rfl
      · rw [Finset.mem_singleton.1 hk, hfab]
    show zmodPowHom hζ (f i) = zmodPowHom hζ (f j)
    rw [hc i hi, hc j hj]
  · rintro x - y - hxy hB
    have key : ∀ j : Fin n, j ≠ a → j ≠ b →
        diagSpEntry (Pi.mulSingle j ζ) x ≠ diagSpEntry (Pi.mulSingle j ζ) y →
        ∃ s ∈ (fun f j => zmodPowHom hζ (f j)) ''
          {f : Fin n → Multiplicative (ZMod p) | permAut (Equiv.swap a b) f = f},
          diagSpEntry s x ≠ diagSpEntry s y := by
      intro j hja hjb hne
      refine ⟨_, ⟨Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p)), ?_, rfl⟩, ?_⟩
      · exact (ggKGSpR_permAut_swap_eq_self_iff _).2 (by
          rw [Pi.mulSingle_eq_of_ne (Ne.symm hja), Pi.mulSingle_eq_of_ne (Ne.symm hjb)])
      · beta_reduce
        rw [ggKGSpR_comp_mulSingle, hχg]
        exact hne
    have hnot : ∀ c : Fin n ⊕ Fin n, c ∉ planeCoords ({a, b} : Finset (Fin n)) →
        planeOf c ≠ a ∧ planeOf c ≠ b := by
      intro c hc
      refine ⟨fun h => hc ?_, fun h => hc ?_⟩ <;> rw [mem_planeCoords, h] <;> simp
    by_cases hx : x ∈ planeCoords ({a, b} : Finset (Fin n))
    · by_cases hy : y ∈ planeCoords ({a, b} : Finset (Fin n))
      · set f₀ : Fin n → Multiplicative (ZMod p) :=
          fun k => if k ∈ ({a, b} : Finset (Fin n)) then Multiplicative.ofAdd (1 : ZMod p) else 1
          with hf₀
        refine ⟨_, ⟨f₀, (ggKGSpR_permAut_swap_eq_self_iff f₀).2 (by simp [hf₀]), rfl⟩, ?_⟩
        have h3 : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := fun e =>
          units_ne_inv_of_mul_self_ne_one hκ (Units.ext e)
        rw [mem_planeCoords] at hx hy
        rcases x with i | i <;> rcases y with j | j
        · exact absurd ⟨hx, hy⟩ hB
        · have hfi : f₀ i = Multiplicative.ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hx
          have hfj : f₀ j = Multiplicative.ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hy
          show diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inl i) ≠
            diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inr j)
          rw [diagSpEntry_inl, diagSpEntry_inr, hfi, hfj, hχg]
          exact h3
        · have hfi : f₀ i = Multiplicative.ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hx
          have hfj : f₀ j = Multiplicative.ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hy
          show diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inr i) ≠
            diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inl j)
          rw [diagSpEntry_inr, diagSpEntry_inl, hfi, hfj, hχg]
          exact h3.symm
        · exact absurd ⟨hx, hy⟩ hB
      · obtain ⟨h1, h2⟩ := hnot y hy
        exact key _ h1 h2 (diagSpEntry_mulSingle_ne hκ hxy (Or.inr (mem_coords_planeOf y)))
    · obtain ⟨h1, h2⟩ := hnot x hx
      exact key _ h1 h2 (diagSpEntry_mulSingle_ne hκ hxy (Or.inl (mem_coords_planeOf x)))
  · refine Assembly.IsQuasisimple.of_mulEquiv
      (siegelBlockEquiv (F := K) ({a, b} : Finset (Fin n))).symm ?_
    rw [Finset.card_pair hab]
    have hq := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
      K le_rfl (Or.inr (by omega)) (Or.inr (by omega))
    exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

private theorem ggKGSpR_card_SL2 {K : Type} [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

private theorem ggKGSpR_four_le_card {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) {ζ : Kˣ} (hζo : orderOf ζ = p) : 4 ≤ Nat.card K := by
  haveI := Fintype.ofFinite K
  obtain ⟨f, -, hfK⟩ := FiniteField.card K 2
  have hf_ne_one : (f : ℕ) ≠ 1 := by
    intro hf1
    have hcard : Nat.card K = 2 := by
      rw [Nat.card_eq_fintype_card, hfK, hf1, pow_one]
    have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hcard]
    have hdv : orderOf ζ ∣ Nat.card Kˣ := orderOf_dvd_natCard ζ
    rw [hunits] at hdv
    have hone : orderOf ζ = 1 := Nat.dvd_one.mp hdv
    rw [hone] at hζo
    exact hp.one_lt.ne' hζo.symm
  have hf2 : 2 ≤ (f : ℕ) := by
    have h1 : 1 ≤ (f : ℕ) := f.2
    omega
  rw [Nat.card_eq_fintype_card, hfK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (f : ℕ) := Nat.pow_le_pow_right (by norm_num) hf2

private theorem ggKGSpR_dvd_card_sub_one {K : Type} [Field K] {p : ℕ} {ζ : Kˣ}
    (hζo : orderOf ζ = p) : p ∣ Nat.card K - 1 := by
  have h : p ∣ Nat.card Kˣ := by rw [← hζo]; exact orderOf_dvd_natCard ζ
  rwa [Nat.card_units] at h

private theorem ggKGSpR_spSwapSp_mem_spBlock {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (i : Fin n) : (spSwapSp i : LargeEvenSpGroup K n) ∈ spBlock K ({i} : Finset (Fin n)) := by
  have hmem : ∀ c : Fin n ⊕ Fin n,
      c ∈ planeCoords ({i} : Finset (Fin n)) ↔ c = Sum.inl i ∨ c = Sum.inr i := by
    intro c
    rw [mem_planeCoords, Finset.mem_singleton]
    rcases c with j | j <;> simp
  intro a b hab
  rw [mat_apply, spSwapSp_coe, TauCeti.permutationGL_coe,
    show pairSwap i = Equiv.swap (Sum.inl i) (Sum.inr i) from rfl, Equiv.swap_inv,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq, Matrix.submatrix_apply]
  change (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Equiv.swap (Sum.inl i) (Sum.inr i) a) b =
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a b
  by_cases ha : a ∈ planeCoords ({i} : Finset (Fin n))
  · have hb : b ∉ planeCoords ({i} : Finset (Fin n)) := fun hb => hab ⟨ha, hb⟩
    have hsa : Equiv.swap (Sum.inl i) (Sum.inr i) a ∈ planeCoords ({i} : Finset (Fin n)) := by
      rcases (hmem a).1 ha with rfl | rfl
      · rw [Equiv.swap_apply_left]
        exact (hmem _).2 (Or.inr rfl)
      · rw [Equiv.swap_apply_right]
        exact (hmem _).2 (Or.inl rfl)
    rw [Matrix.one_apply_ne
        (show Equiv.swap (Sum.inl i) (Sum.inr i) a ≠ b from fun h => hb (h ▸ hsa)),
      Matrix.one_apply_ne (show a ≠ b from fun h => hb (h ▸ ha))]
  · rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha ((hmem a).2 (Or.inl h)))
      (fun h => ha ((hmem a).2 (Or.inr h)))]

private theorem ggKGSpR_proj_centralizer {K : Type} [Field K] [CharP K 2] {n p : ℕ} [NeZero n]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (X : Set (Fin n → Multiplicative (ZMod p))) :
    (Subgroup.centralizer (spTorusSp (m := n) hζ '' X)).map
        (LargeEvenProjMk (LargeEvenSpGroup K n)) =
      Subgroup.centralizer (spTorus (m := n) hζ '' X) := by
  rw [ggKGSpR_map_centralizer_of_bij (LargeEvenProjMk (LargeEvenSpGroup K n))
    (AutPSp.proj_injective (n := n) (K := K)) (QuotientGroup.mk'_surjective _)]
  congr 1
  ext e
  constructor
  · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, ggKGSpR_proj_spTorusSp (K := K) (n := n) hζ f⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨spTorusSp (m := n) hζ f, ⟨f, hf, rfl⟩, ggKGSpR_proj_spTorusSp (K := K) (n := n) hζ f⟩

private theorem ggKGSpR_comp_proj {K : Type} [Field K] [CharP K 2] {n p : ℕ} [NeZero n]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) {S : Subgroup (LargeEvenSpGroup K n)}
    {X : Set (Fin n → Multiplicative (ZMod p))}
    (h : CFSG.Assembly.IsComponentOf S (Subgroup.centralizer (spTorusSp (m := n) hζ '' X))) :
    CFSG.Assembly.IsComponentOf (S.map (LargeEvenProjMk (LargeEvenSpGroup K n)))
      (Subgroup.centralizer (spTorus (m := n) hζ '' X)) := by
  have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective h
    (LargeEvenProjMk (LargeEvenSpGroup K n)) (AutPSp.proj_injective (n := n) (K := K))
  rwa [ggKGSpR_proj_centralizer (K := K) (n := n) hζ X] at h1

private theorem ggKGSpR_hwS {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (i : ggKGSpR_Idx n) : ggKGSpR_W i ∈ ggKGSpR_S (K := K) i := by
  rcases i with i | q | q
  · exact Subgroup.mem_map_of_mem _ (ggKGSpR_spSwapSp_mem_spBlock i)
  · exact Subgroup.mem_map_of_mem _ (ggKGSpR_spPermSp_swap_mem_siegelBlock q.1.1 q.1.2)
  · change LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp q.1.2) *
        LargeEvenProjMk (LargeEvenSpGroup K n)
          (NbrSp.spPermSp (K := K) (Equiv.swap q.1.1 q.1.2)) *
        (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp q.1.2))⁻¹ ∈
      ((siegelBlock K ({q.1.1, q.1.2} : Finset (Fin n))).map
        (MulAut.conj (spSwapSp q.1.2 : LargeEvenSpGroup K n)).toMonoidHom).map
        (LargeEvenProjMk _)
    rw [← map_mul, ← map_inv]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
      (ggKGSpR_spPermSp_swap_mem_siegelBlock q.1.1 q.1.2))

private theorem ggKGSpR_map_conj_centralizer {G : Type} [Group G] (C : Set G) (g : G) :
    (Subgroup.centralizer C).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((MulAut.conj g) '' C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ c ∈ C, c * y = y * c := Subgroup.mem_centralizer_iff.mp hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    calc (g * c * g⁻¹) * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
      _ = g * (y * c) * g⁻¹ := by rw [hy' c hc]
      _ = (g * y * g⁻¹) * (g * c * g⁻¹) := by group
  · intro hx
    have hx' : ∀ c ∈ C, (g * c * g⁻¹) * x = x * (g * c * g⁻¹) := by
      intro c hc
      exact Subgroup.mem_centralizer_iff.mp hx (g * c * g⁻¹) ⟨c, hc, rfl⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change g⁻¹ * x * g ∈ Subgroup.centralizer C
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have h := hx' c hc
      have h2 := congrArg (fun w => g⁻¹ * w * g) h
      simpa [mul_assoc] using h2
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private theorem ggKGSpR_permAut_mul_sgnAut {p m : ℕ} {a b : Fin m} :
    (permAut (p := p) (Equiv.swap a b) : MulAut (Fin m → Multiplicative (ZMod p))) *
        sgnAut (p := p) b =
      sgnAut (p := p) a * permAut (p := p) (Equiv.swap a b) := by
  have h := IsSignedPerm.mul_sgnAut
    (u := permAut (p := p) (Equiv.swap a b)) (π := Equiv.swap a b)
    (ε := fun _ => (1 : ZMod p))
    (fun f i => by simp [permAut_apply, Function.comp_apply]) b
  rwa [Equiv.swap_apply_right] at h

private theorem ggKGSpR_fix_negswap {p m : ℕ} {a b : Fin m} :
    (sgnAut (p := p) b : MulAut (Fin m → Multiplicative (ZMod p))) ''
        {f | permAut (p := p) (Equiv.swap a b) f = f} =
      {f | (sgnAut (p := p) a * sgnAut (p := p) b *
        permAut (p := p) (Equiv.swap a b) :
          MulAut (Fin m → Multiplicative (ZMod p))) f = f} := by
  let V := Fin m → Multiplicative (ZMod p)
  let A : MulAut V := sgnAut a
  let B : MulAut V := sgnAut b
  let P : MulAut V := permAut (Equiv.swap a b)
  have hPB : P * B = A * P := ggKGSpR_permAut_mul_sgnAut (p := p) (a := a) (b := b)
  have hAB : A * B = B * A := sgnAut_mul_comm (p := p) a b
  have hAA : A * A = 1 := by
    have := sgnAut_sq (p := p) a
    simpa [sq] using this
  have hBB : B * B = 1 := by
    have := sgnAut_sq (p := p) b
    simpa [sq] using this
  have hBPB : B * P * B = A * B * P := by
    calc B * P * B = B * (P * B) := by group
      _ = B * (A * P) := by rw [hPB]
      _ = (B * A) * P := by group
      _ = (A * B) * P := by rw [← hAB]
      _ = A * B * P := by group
  have hAPB : A * B * P * B = B * P := by
    calc A * B * P * B = A * (B * P * B) := by group
      _ = A * (A * B * P) := by rw [hBPB]
      _ = (A * A) * (B * P) := by group
      _ = B * P := by rw [hAA, one_mul]
  change B '' {f | P f = f} = {f | (A * B * P) f = f}
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (A * B * P * B) g = B g
    rw [hAPB]
    change B (P g) = B g
    rw [hg]
  · intro hf
    refine ⟨B f, ?_, ?_⟩
    · have h1 : B (P f) = A f := by
        have h := congrArg (fun x => A x) hf
        have h' : (A * A) (B (P f)) = A f := h
        rw [hAA, MulAut.one_apply] at h'
        exact h'
      have h2 : P f = A (B f) := by
        have h := congrArg (fun x => B x) h1
        have h' : (B * B) (P f) = B (A f) := h
        rw [hBB, MulAut.one_apply] at h'
        calc P f = B (A f) := h'
          _ = (B * A) f := rfl
          _ = (A * B) f := by rw [← hAB]
          _ = A (B f) := rfl
      calc P (B f) = (P * B) f := rfl
        _ = (A * P) f := by rw [hPB]
        _ = A (P f) := rfl
        _ = A (A (B f)) := by rw [h2]
        _ = (A * A) (B f) := rfl
        _ = B f := by rw [hAA, MulAut.one_apply]
    · change (B * B) f = f
      rw [hBB, MulAut.one_apply]

private theorem ggKGSpR_isComponentOf_negSwap {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p : ℕ} [NeZero n] (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (h4 : 4 ≤ Nat.card K) {a b : Fin n} (hab : a ≠ b) :
    CFSG.Assembly.IsComponentOf
      (((siegelBlock K ({a, b} : Finset (Fin n))).map
        (MulAut.conj (spSwapSp b : LargeEvenSpGroup K n)).toMonoidHom).map
        (LargeEvenProjMk (LargeEvenSpGroup K n)))
      (Subgroup.centralizer (spTorus (m := n) hζ ''
        {f : Fin n → Multiplicative (ZMod p) |
          (sgnAut a * sgnAut b * permAut (Equiv.swap a b) :
            MulAut (Fin n → Multiplicative (ZMod p))) f = f})) := by
  have hcomp := ggKGSpR_comp_proj hζ (ggKGSpR_statedComp_swap hp hp2 hζo hζ h4 hab)
  have hconj := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp
    (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b))
  have hfun : ∀ f, (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b)))
      (spTorus (m := n) hζ f) = spTorus (m := n) hζ (sgnAut b f) := by
    intro f
    have h := spSwap_conj_spTorus (K := K) (m := n) hζ b f
    rwa [show LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b) * spTorus (m := n) hζ f *
        (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b))⁻¹ =
        (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b)))
          (spTorus (m := n) hζ f) from (MulAut.conj_apply _ _).symm] at h
  have hset : (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b))) ''
        (spTorus (m := n) hζ '' {f | permAut (Equiv.swap a b) f = f}) =
      spTorus (m := n) hζ ''
        {f | (sgnAut a * sgnAut b * permAut (Equiv.swap a b) :
          MulAut (Fin n → Multiplicative (ZMod p))) f = f} := by
    ext y
    constructor
    · rintro ⟨z, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨sgnAut b f, (ggKGSpR_fix_negswap (p := p) (a := a) (b := b)).le ⟨f, hf, rfl⟩,
        (hfun f).symm⟩
    · intro hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [← ggKGSpR_fix_negswap (p := p) (a := a) (b := b)] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      exact ⟨spTorus (m := n) hζ f, ⟨f, hf, rfl⟩, hfun f⟩
  have hcd : (Subgroup.centralizer (spTorus (m := n) hζ ''
        {f | permAut (Equiv.swap a b) f = f})).map
          (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b))).toMonoidHom =
      Subgroup.centralizer (spTorus (m := n) hζ ''
        {f | (sgnAut a * sgnAut b * permAut (Equiv.swap a b) :
          MulAut (Fin n → Multiplicative (ZMod p))) f = f}) := by
    rw [ggKGSpR_map_conj_centralizer, hset]
  have hK : ((siegelBlock K ({a, b} : Finset (Fin n))).map
        (LargeEvenProjMk (LargeEvenSpGroup K n))).map
        (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K n) (spSwapSp b))).toMonoidHom =
      ((siegelBlock K ({a, b} : Finset (Fin n))).map
        (MulAut.conj (spSwapSp b : LargeEvenSpGroup K n)).toMonoidHom).map
        (LargeEvenProjMk (LargeEvenSpGroup K n)) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hK] at hconj
  rwa [hcd] at hconj

private theorem ggKGSpR_dvd_card_sgn {K : Type} [Field K] [CharP K 2] {n p : ℕ}
    [NeZero n] (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (i : Fin n) :
    p ∣ Nat.card ((spBlock K ({i} : Finset (Fin n))).map (LargeEvenProjMk _)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  change p ∣ Nat.card ((spBlock K ({i} : Finset (Fin n))).map
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K))
  rw [Subgroup.card_map_of_injective (AutPSp.proj_injective (n := n) (K := K))]
  have hχg : zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) = ζ := ggKGSpR_zmodPowHom_one hζ
  have hx : spTorusSp (m := n) hζ (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) ∈
      spBlock K ({i} : Finset (Fin n)) := by
    rw [ggKGSpR_spTorusSp_eq_diagSp hζ, ggKGSpR_comp_mulSingle, hχg, spBlock_singleton]
    exact rootTorusSp_le_longRootSp2 (K := K) i (rootTorusHom_mem_rootTorusSp (K := K) i ζ)
  have hτinj : Function.Injective (spTorusSp (m := n) hζ) := fun x y h =>
    spTorus_injective hζ hζo (hp.odd_of_ne_two hp2) (by
      change CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K (spTorusSp hζ x) =
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K (spTorusSp hζ y)
      rw [h])
  have hord : orderOf (spTorusSp (m := n) hζ
      (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)))) = p := by
    rw [orderOf_injective (spTorusSp (m := n) hζ) hτinj, orderOf_piMulSingle,
      orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have h1 := orderOf_dvd_natCard (⟨_, hx⟩ : spBlock K ({i} : Finset (Fin n)))
  rwa [Subgroup.orderOf_mk, hord] at h1

private theorem ggKGSpR_dvd_card_swap {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hpq : p ∣ Nat.card K - 1) {a b : Fin n} (hab : a ≠ b) :
    p ∣ Nat.card (siegelBlock K ({a, b} : Finset (Fin n))) := by
  rw [Nat.card_congr (siegelBlockEquiv (F := K) ({a, b} : Finset (Fin n))).toEquiv.symm,
    Finset.card_pair hab, ggKGSpR_card_SL2]
  have h1 := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
  rw [one_pow] at h1
  exact Dvd.dvd.mul_left (hpq.trans h1) _

theorem ggKGRootDatumAt_spTorus
    {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} [NeZero n] (hn : 3 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    GGKGRootDatumAt p (spTorus (m := n) hζ).range := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hτ : Function.Injective (spTorus (m := n) hζ) :=
    spTorus_injective hζ hζo (hp.odd_of_ne_two hp2)
  have hK : 4 ≤ Nat.card K := ggKGSpR_four_le_card hp hζo
  have hpq : p ∣ Nat.card K - 1 := ggKGSpR_dvd_card_sub_one hζo
  have hS : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K n)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n
      (le_trans (by norm_num : 1 ≤ 3) hn) (Or.inl (Or.inr hK))
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K n)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot
  have hnc : ∃ a b : LargeEvenProj (LargeEvenSpGroup K n), a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI := hS
    have htop : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K n)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact (h x y).symm
    have hbot : (⊤ : Subgroup (LargeEvenProj (LargeEvenSpGroup K n))) = ⊥ := by
      rw [← htop, hZ]
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (LargeEvenProj (LargeEvenSpGroup K n))
    refine hxy ?_
    have hx1 : x = 1 := by
      have hxmem : x ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSpGroup K n))) := by
        rw [← hbot]; exact Subgroup.mem_top x
      simpa using hxmem
    have hy1 : y = 1 := by
      have hymem : y ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSpGroup K n))) := by
        rw [← hbot]; exact Subgroup.mem_top y
      simpa using hymem
    rw [hx1, hy1]
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (LargeEvenProj (LargeEvenSpGroup K n)) := by
    haveI : Fintype K := Fintype.ofFinite K
    have hdata := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds K n
      (by omega) (fun h => by have h1 : n = 2 := congrArg Prod.fst h; omega)
    have hchev0 := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
        (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv n K) hdata.chev
    rw [ringChar.eq K 2] at hchev0
    exact hchev0
  refine RealKGModelRoot.ggKGRootDatumAt_of_model hp hτ rfl
    (ggKGSpR_W (K := K)) (ggKGSpR_s (n := n) (p := p)) (ggKGSpR_S (K := K)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun i => ggKGSpR_hws (K := K) hζ i
  · exact fun i => ggKGSpR_hwS (K := K) i
  · intro i
    rcases i with i | q | q
    · exact ggKGSpR_comp_proj hζ (ggKGSpR_statedComp_sgn hp hp2 hζo hζ hK i)
    · exact ggKGSpR_comp_proj hζ (ggKGSpR_statedComp_swap hp hp2 hζo hζ hK q.2)
    · exact ggKGSpR_isComponentOf_negSwap hp hp2 hζo hζ hK q.2
  · intro i
    rcases i with i | q | q
    · exact ggKGSpR_dvd_card_sgn hp hp2 hζ hζo i
    · change p ∣ Nat.card ((siegelBlock K ({q.1.1, q.1.2} : Finset (Fin n))).map
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K))
      rw [Subgroup.card_map_of_injective (AutPSp.proj_injective (n := n) (K := K))]
      exact ggKGSpR_dvd_card_swap hpq q.2
    · change p ∣ Nat.card (((siegelBlock K ({q.1.1, q.1.2} : Finset (Fin n))).map
          (MulAut.conj (spSwapSp q.1.2 : LargeEvenSpGroup K n)).toMonoidHom).map
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K))
      rw [Subgroup.card_map_of_injective (AutPSp.proj_injective (n := n) (K := K)),
        Subgroup.card_map_of_injective (MulAut.conj (spSwapSp q.1.2)).injective]
      exact ggKGSpR_dvd_card_swap hpq q.2
  · intro g u hgu hu2 hcard
    have husp : IsSignedPerm ⇑u := ggKGSpR_isSignedPerm_of_conj (K := K) hp hζo hζ hgu
    rcases RealKGSignedRefl.signedRefl_cases hp hp2 husp hu2 hcard with ⟨a, ha⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl a, ha.symm⟩
    · rcases x with ⟨⟨⟨a, b⟩, hab⟩, sgn⟩
      by_cases hs : sgn = true
      · refine ⟨Sum.inr (Sum.inr ⟨(a, b), hab.ne⟩), ?_⟩
        subst hs
        exact hx.symm
      · refine ⟨Sum.inr (Sum.inl ⟨(a, b), hab.ne⟩), ?_⟩
        have hs' : sgn = false := by cases sgn <;> simp_all
        subst hs'
        exact hx.symm
  · intro a ha J hJ hJa
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp ha
    have hfp : f ^ p = 1 := by
      funext j
      apply Multiplicative.toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero,
        zero_mul]
    have hap : (spTorus (m := n) hζ f) ^ p = 1 := by
      rw [← map_pow, hfp, map_one]
    exact ggKG_layer_of_chevSimple hS hnc hchev hp hp2 hap hJ hJa

private theorem ggKGSpR_eq_map_conj_of_exists {K : Type} [Field K] {n p : ℕ} {ζ : Kˣ}
    (hζ : ζ ^ p = 1) {E : Subgroup (LargeEvenProj (LargeEvenSpGroup K n))}
    {x : LargeEvenProj (LargeEvenSpGroup K n)}
    (hx1 : ∀ f, x * spTorus (m := n) hζ f * x⁻¹ ∈ E)
    (hx2 : ∀ e ∈ E, ∃ f, x * spTorus (m := n) hζ f * x⁻¹ = e) :
    E = (spTorus (m := n) hζ).range.map (MulAut.conj x).toMonoidHom := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf⟩ := hx2 e he
    exact ⟨spTorus (m := n) hζ f, ⟨f, rfl⟩,
      by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hf⟩
  · rintro ⟨t, ⟨f, rfl⟩, htf⟩
    rw [← htf]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx1 f

private theorem ggKGSpR_card_coords {p n : ℕ} :
    Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
  let ε : Multiplicative (Fin n → ZMod p) ≃* (Fin n → Multiplicative (ZMod p)) :=
    MulEquiv.piMultiplicative _
  rw [← Nat.card_congr ε.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n → ZMod p) ≃ (Fin n → ZMod p)),
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

theorem ggKGRootDatum_symplectic
    {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} [NeZero n] (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGKGRootDatum p n (LargeEvenProj (LargeEvenSpGroup K n)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units (α := K)]; exact hpq)
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hτ : Function.Injective (spTorus (m := n) hζ) :=
    spTorus_injective hζ hζo (hp.odd_of_ne_two hp2)
  intro E hEab h3 hr hsc
  by_cases hn3 : 3 ≤ n
  · have hT : GGKGRootDatumAt p (spTorus (m := n) hζ).range :=
      ggKGRootDatumAt_spTorus hn3 hp hp2 hζo hζ
    obtain ⟨x, hx1, hx2⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hEab hr
    have hEeq := ggKGSpR_eq_map_conj_of_exists hζ hx1 hx2
    rw [hEeq]
    refine ggKGRootDatumAt_of_mulEquiv (MulAut.conj x).symm ?_
    rw [Subgroup.map_map]
    have hcomp : (((MulAut.conj x).symm : LargeEvenProj (LargeEvenSpGroup K n) ≃*
        LargeEvenProj (LargeEvenSpGroup K n)).toMonoidHom.comp
        (MulAut.conj x).toMonoidHom) = MonoidHom.id _ := by
      ext y
      simp
    rw [hcomp, Subgroup.map_id]
    exact hT
  · have hn2 : n = 2 := by omega
    subst hn2
    obtain ⟨x, hx1, hx2⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hEab hr
    have hEeq := ggKGSpR_eq_map_conj_of_exists hζ hx1 hx2
    have hcardE : Nat.card E = p ^ 2 := by
      rw [hEeq, Subgroup.card_map_of_injective (MulAut.conj x).injective,
        (Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv).symm, ggKGSpR_card_coords]
    rw [hcardE] at h3
    exact absurd h3 (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)))

end CFSG.StandardType
