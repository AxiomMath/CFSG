module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart11

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

namespace CFSG.StandardType.F4ExplicitPos.InnerDirect
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private theorem f4_exists_mul_psi_mem_centralizer
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {G : Type*} [Group G] (ψ : ↥(adjointGroup .F4 K) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(adjointGroup .F4 K)) {d : G}
    (hpos : ∀ i : Fin Tag.F4.rank, ∃ χ : K, ∀ c,
      d⁻¹ * ψ (xPar (rootOperatorFamily .F4) (Pi.single i 1) c) * d =
        ψ (xPar (rootOperatorFamily .F4) (Pi.single i 1) (χ * c)))
    (hneg : ∀ i : Fin Tag.F4.rank, ∃ φ : K → K, ∀ c,
      d⁻¹ * ψ (xPar (rootOperatorFamily .F4) (-Pi.single i 1) c) * d =
        ψ (xPar (rootOperatorFamily .F4) (-Pi.single i 1) (φ c))) :
    ∃ u : ↥(adjointGroup .F4 K), d * ψ u ∈ Subgroup.centralizer (ψ.range : Set G) := by
  classical
  let F := rootOperatorFamily .F4
  let D := f4Datum K
  choose χ hχ using hpos
  choose χ' hχ' using hneg
  let φi : (i : Fin Tag.F4.rank) → SL2 K →* ↥(adjointGroup .F4 K) := fun i =>
    (simpleRootSL2 .F4 K i).codRestrict (adjointGroup .F4 K)
      (simpleRootSL2_mem_adjointGroup i)
  have hφi_inj : ∀ i, Function.Injective (φi i) := by
    intro i
    have h := CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two
      (CharP.cast_eq_zero K 2) i
    intro a b hab
    exact h (by
      simpa [φi, MonoidHom.codRestrict_apply] using
        congrArg (fun x : ↥(adjointGroup .F4 K) => (x : ModGL .F4 K)) hab)
  have hΦ : ∀ i, Function.Injective (ψ.comp (φi i)) := fun i =>
    PsiDiag.injective_comp_of_ker_le_center (φi i) (hφi_inj i) ψ hker
  have hxPs : ∀ (i : Fin Tag.F4.rank) (c : K),
      xPar F (Pi.single i 1) c = F.eltElement (simpleRoot .F4 i) c := by
    intro i c
    rw [show xPar F (Pi.single i 1) c =
        F.eltElement ⟨Pi.single i 1, isRoot_single .F4 i⟩ c from
      dif_pos (isRoot_single .F4 i)]
    rfl
  have hxNs : ∀ (i : Fin Tag.F4.rank) (c : K),
      xPar F (-Pi.single i 1) c = F.eltElement (-simpleRoot .F4 i) c := by
    intro i c
    rw [show xPar F (-Pi.single i 1) c =
        F.eltElement ⟨-Pi.single i 1, isRoot_neg_single .F4 i⟩ c from
      dif_pos (isRoot_neg_single .F4 i)]
    rfl
  have hxu : ∀ i c, (xPar F (Pi.single i 1) c : ModGL .F4 K) = xUnit .F4 K i c := by
    intro i c
    rw [hxPs i c, F.coe_eltElement, F.eltUnit_simple]
  have hxv : ∀ i c, (xPar F (-Pi.single i 1) c : ModGL .F4 K) = yUnit .F4 K i c := by
    intro i c
    rw [hxNs i c, F.coe_eltElement, F.eltUnit_neg_simple]
  have hφu : ∀ i c, φi i (uSL c) = xPar F (Pi.single i 1) c := by
    intro i c
    apply Subtype.ext
    change ((simpleRootSL2 .F4 K i) (uSL c) : ModGL .F4 K) =
      (xPar F (Pi.single i 1) c : ModGL .F4 K)
    rw [simpleRootSL2_uSL, hxu]
  have hφl : ∀ i c, φi i (vSL c) = xPar F (-Pi.single i 1) c := by
    intro i c
    apply Subtype.ext
    change ((simpleRootSL2 .F4 K i) (vSL c) : ModGL .F4 K) =
      (xPar F (-Pi.single i 1) c : ModGL .F4 K)
    rw [simpleRootSL2_vSL, hxv]
  have hsl2u : ∀ c : K, sl2Upper c = uSL c := fun c => Subtype.ext rfl
  have hsl2l : ∀ c : K, sl2Lower c = vSL c := fun c => Subtype.ext rfl
  have hx0 : ∀ γ : Fin Tag.F4.rank → ℤ, xPar F γ (0 : K) = 1 := by
    intro γ
    by_cases h : IsRoot .F4 γ
    · rw [show xPar F γ (0 : K) = F.eltElement ⟨γ, h⟩ (0 : K) from dif_pos h,
        F.eltElement_zero]
    · rw [show xPar F γ (0 : K) = 1 from dif_neg h]
  have hχ0 : ∀ i, χ i ≠ 0 := by
    intro i h0
    have h := hχ i 1
    rw [h0, zero_mul, hx0 (Pi.single i 1), map_one] at h
    have h' : ψ (xPar F (Pi.single i 1) 1) = 1 := by
      calc ψ (xPar F (Pi.single i 1) 1) =
            d * (d⁻¹ * ψ (xPar F (Pi.single i 1) 1) * d) * d⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h'' : (ψ.comp (φi i)) (sl2Upper 1) = (ψ.comp (φi i)) 1 := by
      rw [MonoidHom.comp_apply, hsl2u, hφu, h']
      simp
    have h3 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) (hΦ i h'')
    simp [CFSG.LieType.Steinberg.sl2Upper] at h3
  let e : Fin Tag.F4.rank → Kˣ := fun i => Units.mk0 (χ i) (hχ0 i)
  have hdet : D.cartan.det = 2 ^ 0 := by
    show (Tag.cartan .F4).det = 2 ^ 0
    decide +kernel
  obtain ⟨s, hs⟩ := PsiDiag.exists_prod_zpow_cartan_eq (I := Fin Tag.F4.rank) D.cartan
    (a := 0) hdet e
  let T : ↥(adjointGroup .F4 K) :=
    ((List.finRange (Tag.rank .F4)).map (fun j => torusElement .F4 K j (s j))).prod
  have hsingle_pos : ∀ (j i : Fin Tag.F4.rank) (v : K),
      torusElement .F4 K j (s j) * xPar F (Pi.single i 1) v *
        (torusElement .F4 K j (s j))⁻¹ =
      xPar F (Pi.single i 1) (((s j ^ D.cartan j i : Kˣ) : K) * v) := by
    intro j i v
    apply Subtype.ext
    have h := (simple_torus_root_conjugation .F4 K j i (s j) v).1
    simpa [torusElement, hxu, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hsingle_neg : ∀ (j i : Fin Tag.F4.rank) (v : K),
      torusElement .F4 K j (s j) * xPar F (-Pi.single i 1) v *
        (torusElement .F4 K j (s j))⁻¹ =
      xPar F (-Pi.single i 1) (((s j ^ (-D.cartan j i) : Kˣ) : K) * v) := by
    intro j i v
    apply Subtype.ext
    have h := (simple_torus_root_conjugation .F4 K j i (s j) v).2
    simpa [torusElement, hxv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hprod : ∀ (γ : Fin Tag.F4.rank → ℤ) (g : Fin Tag.F4.rank → Kˣ) (v : K),
      (∀ j, ∀ w : K, torusElement .F4 K j (s j) * xPar F γ w *
        (torusElement .F4 K j (s j))⁻¹ = xPar F γ ((g j : K) * w)) →
      T * xPar F γ v * T⁻¹ = xPar F γ (((∏ j, g j : Kˣ) : K) * v) := by
    intro γ g v hg
    have hmain : ∀ (L : List (Fin Tag.F4.rank)),
        (L.map (fun j => torusElement .F4 K j (s j))).prod * xPar F γ v *
          ((L.map (fun j => torusElement .F4 K j (s j))).prod)⁻¹ =
        xPar F γ ((((L.map g).prod : Kˣ) : K) * v) := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        simp only [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul]
        calc torusElement .F4 K a (s a) *
              (L.map (fun j => torusElement .F4 K j (s j))).prod * xPar F γ v *
              (((L.map (fun j => torusElement .F4 K j (s j))).prod)⁻¹ *
                (torusElement .F4 K a (s a))⁻¹)
            = torusElement .F4 K a (s a) *
              ((L.map (fun j => torusElement .F4 K j (s j))).prod * xPar F γ v *
                ((L.map (fun j => torusElement .F4 K j (s j))).prod)⁻¹) *
              (torusElement .F4 K a (s a))⁻¹ := by group
          _ = torusElement .F4 K a (s a) *
              xPar F γ ((((L.map g).prod : Kˣ) : K) * v) *
              (torusElement .F4 K a (s a))⁻¹ := by rw [ih]
          _ = xPar F γ ((g a : K) * ((((L.map g).prod : Kˣ) : K) * v)) := by rw [hg a]
          _ = xPar F γ ((((g a) * (L.map g).prod : Kˣ) : K) * v) := by
                rw [Units.val_mul, mul_assoc]
    simpa [T, ← Fin.prod_univ_def] using hmain (List.finRange (Tag.rank .F4))
  have hTpos : ∀ i v, T * xPar F (Pi.single i 1) v * T⁻¹ =
      xPar F (Pi.single i 1) (((e i : Kˣ) : K) * v) := by
    intro i v
    rw [hprod (Pi.single i 1) (fun j => s j ^ D.cartan j i) v (fun j w => hsingle_pos j i w),
      hs i]
  let ν : Fin Tag.F4.rank → Kˣ := fun i => ∏ j, s j ^ (-D.cartan j i)
  have hTneg : ∀ i v, T * xPar F (-Pi.single i 1) v * T⁻¹ =
      xPar F (-Pi.single i 1) (((ν i : Kˣ) : K) * v) :=
    fun i v => hprod (-Pi.single i 1) (fun j => s j ^ (-D.cartan j i)) v
      (fun j w => hsingle_neg j i w)
  set d' := d * ψ T with hd'
  have hconj : ∀ z, d'⁻¹ * ψ z * d' = ψ T⁻¹ * (d⁻¹ * ψ z * d) * ψ T := by
    intro z
    rw [hd', map_inv]
    group
  have hinvT : ∀ i v, T⁻¹ * xPar F (Pi.single i 1) v * T =
      xPar F (Pi.single i 1) ((((e i)⁻¹ : Kˣ) : K) * v) := by
    intro i v
    have h := hTpos i ((((e i)⁻¹ : Kˣ) : K) * v)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    group
  have hinvTn : ∀ i v, T⁻¹ * xPar F (-Pi.single i 1) v * T =
      xPar F (-Pi.single i 1) ((((ν i)⁻¹ : Kˣ) : K) * v) := by
    intro i v
    have h := hTneg i ((((ν i)⁻¹ : Kˣ) : K) * v)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    group
  have hfpos : ∀ i c, d'⁻¹ * ψ (xPar F (Pi.single i 1) c) * d' =
      ψ (xPar F (Pi.single i 1) c) := by
    intro i c
    rw [hconj, hχ i c, ← map_mul, ← map_mul, hinvT]
    have harg : (((e i)⁻¹ : Kˣ) : K) * (χ i * c) = c := by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc, inv_mul_cancel₀ (hχ0 i), one_mul]
    rw [harg]
  have hfneg : ∀ i c, d'⁻¹ * ψ (xPar F (-Pi.single i 1) c) * d' =
      ψ (xPar F (-Pi.single i 1) c) := by
    intro i c
    have hl : ∀ c', d'⁻¹ * ψ (xPar F (-Pi.single i 1) c') * d' =
        ψ (xPar F (-Pi.single i 1) ((((ν i)⁻¹ : Kˣ) : K) * χ' i c')) := by
      intro c'
      rw [hconj, hχ' i c', ← map_mul, ← map_mul, hinvTn]
    have he1 : ∀ c', (((ν i)⁻¹ : Kˣ) : K) * χ' i c' = c' := by
      intro c'
      refine PsiDiag.eq_of_conj_sl2 (ψ.comp (φi i)) (hΦ i) (d := d')
        (φ := fun c' => (((ν i)⁻¹ : Kˣ) : K) * χ' i c') (fun c' => ?_) (fun c' => ?_) c'
      · rw [hsl2u, MonoidHom.comp_apply, hφu]
        exact hfpos i c'
      · rw [hsl2l, hsl2l, MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl]
        exact hl c'
    rw [hl, he1]
  have hfix : ∀ i, simplePosSubgroup .F4 K i ≤ (Subgroup.centralizer ({d'} : Set G)).comap ψ ∧
      simpleNegSubgroup .F4 K i ≤ (Subgroup.centralizer ({d'} : Set G)).comap ψ := by
    intro i
    constructor
    · intro z hz
      obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hz
      rw [PsiDiag.mem_fix_iff]
      have hz' : z = xPar F (Pi.single i 1) c := by
        apply Subtype.ext
        rw [hc, hxu]
      rw [hz']
      exact hfpos i c
    · intro z hz
      obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hz
      rw [PsiDiag.mem_fix_iff]
      have hz' : z = xPar F (-Pi.single i 1) c := by
        apply Subtype.ext
        rw [hc, hxv]
      rw [hz']
      exact hfneg i c
  have hS : (⨆ i, (simplePosSubgroup .F4 K i ⊔ simpleNegSubgroup .F4 K i)) ≤
      (Subgroup.centralizer ({d'} : Set G)).comap ψ :=
    iSup_le fun i => sup_le (hfix i).1 (hfix i).2
  rw [iSup_simplePosSubgroup_sup_simpleNegSubgroup] at hS
  refine ⟨T, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (Subgroup.mem_comap.mp (hS (Subgroup.mem_top z)))

theorem f4_exists_inner_correction_of_hlin
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hlin : ∀ i : Fin Tag.F4.rank, ∀ h ∈ ggTorus (f4Datum K), ∃ χ : K, ∀ t : K,
      h * xPar (rootOperatorFamily .F4) (Pi.single i 1) t * h⁻¹ =
        xPar (rootOperatorFamily .F4) (Pi.single i 1) (χ * t))
    {G : Type*} [Group G] (ψ : ↥(adjointGroup .F4 K) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(adjointGroup .F4 K)) {c : G}
    (hc : GGPsiInnerDiag (f4Datum K) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  classical
  let F := rootOperatorFamily .F4
  let D := f4Datum K
  obtain ⟨g, hg, hγ⟩ := hc
  have hrGs : ∀ i : Fin Tag.F4.rank, D.rootGroup (Pi.single i 1) =
      F.rootSubgroup K (simpleRoot .F4 i) := by
    intro i
    change rootGroup F K (Pi.single i 1) = F.rootSubgroup K (simpleRoot .F4 i)
    rw [show rootGroup F K (Pi.single i 1) =
        (if h : IsRoot .F4 (Pi.single i 1) then F.rootSubgroup K ⟨Pi.single i 1, h⟩ else ⊥)
        from rfl, dif_pos (isRoot_single .F4 i)]
    rfl
  have hrGn : ∀ i : Fin Tag.F4.rank, D.rootGroup (-Pi.single i 1) =
      F.rootSubgroup K (-simpleRoot .F4 i) := by
    intro i
    change rootGroup F K (-Pi.single i 1) = F.rootSubgroup K (-simpleRoot .F4 i)
    rw [show rootGroup F K (-Pi.single i 1) =
        (if h : IsRoot .F4 (-Pi.single i 1) then F.rootSubgroup K ⟨-Pi.single i 1, h⟩ else ⊥)
        from rfl, dif_pos (isRoot_neg_single .F4 i)]
    rfl
  have hxPs : ∀ (i : Fin Tag.F4.rank) (c : K),
      xPar F (Pi.single i 1) c = F.eltElement (simpleRoot .F4 i) c := by
    intro i c
    rw [show xPar F (Pi.single i 1) c =
        F.eltElement ⟨Pi.single i 1, isRoot_single .F4 i⟩ c from
      dif_pos (isRoot_single .F4 i)]
    rfl
  have hxNs : ∀ (i : Fin Tag.F4.rank) (c : K),
      xPar F (-Pi.single i 1) c = F.eltElement (-simpleRoot .F4 i) c := by
    intro i c
    rw [show xPar F (-Pi.single i 1) c =
        F.eltElement ⟨-Pi.single i 1, isRoot_neg_single .F4 i⟩ c from
      dif_pos (isRoot_neg_single .F4 i)]
    rfl
  have key : ∀ i, ∃ χ : K, ∀ c', (c * g)⁻¹ * ψ (xPar F (Pi.single i 1) c') * (c * g) =
      ψ (xPar F (Pi.single i 1) (χ * c')) := by
    intro i
    obtain ⟨h, hh, hz⟩ := hγ (Pi.single i 1)
      (single_mem_roots (D := f4Datum K) i)
    obtain ⟨χ, hχ⟩ := hlin i h hh
    refine ⟨χ, fun c' => ?_⟩
    have hmem : xPar F (Pi.single i 1) c' ∈ D.rootGroup (Pi.single i 1) := by
      rw [hrGs i, hxPs i c']
      exact F.eltElement_mem_rootSubgroup (simpleRoot .F4 i) c'
    exact (hz _ hmem).trans (congrArg ψ (hχ c'))
  have keyn : ∀ i, ∃ φ : K → K, ∀ c', (c * g)⁻¹ * ψ (xPar F (-Pi.single i 1) c') * (c * g) =
      ψ (xPar F (-Pi.single i 1) (φ c')) := by
    intro i
    obtain ⟨h, hh, hz⟩ := hγ (-Pi.single i 1)
      (neg_single_mem_roots (D := f4Datum K) i)
    have hN : h ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set _) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh (-Pi.single i 1) (neg_single_mem_roots (D := f4Datum K) i)
    have hmem : ∀ c', ∃ c'', xPar F (-Pi.single i 1) c'' =
        h * xPar F (-Pi.single i 1) c' * h⁻¹ := by
      intro c'
      have hx : xPar F (-Pi.single i 1) c' ∈ D.rootGroup (-Pi.single i 1) := by
        rw [hrGn i, hxNs i c']
        exact F.eltElement_mem_rootSubgroup (-simpleRoot .F4 i) c'
      have hconj := (Subgroup.mem_normalizer_iff.mp hN _).mp hx
      rw [hrGn i] at hconj
      obtain ⟨c'', hc''⟩ := F.mem_rootSubgroup.1 hconj
      refine ⟨c'', ?_⟩
      rw [hxNs i c'']
      exact hc''
    choose φ hφ using hmem
    refine ⟨φ, fun c' => ?_⟩
    have hx : xPar F (-Pi.single i 1) c' ∈ D.rootGroup (-Pi.single i 1) := by
      rw [hrGn i, hxNs i c']
      exact F.eltElement_mem_rootSubgroup (-simpleRoot .F4 i) c'
    exact (hz _ hx).trans (congrArg ψ (hφ c').symm)
  obtain ⟨u, hu⟩ := f4_exists_mul_psi_mem_centralizer K ψ hker key keyn
  exact ⟨g * ψ u, mul_mem hg ⟨u, rfl⟩, by rwa [← mul_assoc]⟩

theorem f4_exists_inner_correction
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {G : Type*} [Group G] (ψ : ↥(adjointGroup .F4 K) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(adjointGroup .F4 K)) {c : G}
    (hc : GGPsiInnerDiag (f4Datum K) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have hlin : ∀ i : Fin Tag.F4.rank, ∀ h ∈ ggTorus (f4Datum K), ∃ χ : K, ∀ t : K,
      h * xPar (rootOperatorFamily .F4) (Pi.single i 1) t * h⁻¹ =
        xPar (rootOperatorFamily .F4) (Pi.single i 1) (χ * t) := by
    intro i h hh
    obtain ⟨χ, hχ⟩ :=
      CFSG.StandardType.F4ExplicitPos.RootScalar.f4_xPar_simple_scalar_of_mem_ggTorus K i h hh
    exact ⟨(χ : K), fun t => hχ t⟩
  exact f4_exists_inner_correction_of_hlin (K := K) (hlin := hlin) (G := G)
    (ψ := ψ) (hker := hker) (c := c) (hc := hc)

theorem f4_exists_inner_correction_hH
    {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    ∀ b ∈ B₁, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := by
  obtain ⟨h1, h2, _, _, _, _, _, h8, _⟩ := hH
  intro b hb
  have hc : GGPsiInnerDiag (f4Datum (GaloisField 2 f)) ψ b := h8 b hb
  obtain ⟨g, hg, hgC⟩ :=
    f4_exists_inner_correction (K := GaloisField 2 f) (G := X) ψ h2 hc
  exact ⟨g, h1 ▸ hg, h1 ▸ hgC⟩

end CFSG.StandardType.F4ExplicitPos.InnerDirect

end
end
end
end
end
end

end
