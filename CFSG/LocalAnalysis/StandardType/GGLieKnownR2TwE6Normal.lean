module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Comm

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

private theorem memF4_iff
    (v : Fin (Tag.rank .F4) → ℤ) : memF4 v = true ↔ IsRoot .F4 v :=
  StringData.memDec_iff (Tag.rootCertificate_check .F4) (Tag.stringData_check .F4)

private theorem twE6Delta_last (j : Fin 12) : twE6Delta j twE6Last = 0 := by
  fin_cases j <;> decide +kernel

private theorem twE6Delta_ne_zero (j : Fin 12) : twE6Delta j ≠ 0 := by
  fin_cases j <;> decide +kernel

private theorem twE6Delta_add_alpha_ne_zero (j : Fin 12) :
    twE6Delta j + twE6Alpha ≠ 0 := by
  fin_cases j <;> decide +kernel

private theorem twE6Delta_add_alpha_not_isRoot
    (j : Fin 12) :
    ¬ IsRoot .F4 (twE6Delta j + twE6Alpha) := by
  intro h
  have h1 : memF4 (twE6Delta j + twE6Alpha) = true := (memF4_iff _).2 h
  have h2 : memF4 (twE6Delta j + twE6Alpha) = false := by
    fin_cases j <;> decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

private theorem not_isRoot_twE6Long_add_pairRoot
    (j : Fin 12) : ¬ IsRoot .E6 (twE6Long j + twE6PairRoot 0) := by
  intro h
  have hproj := isRoot_proj h
  rw [map_add, twE6_proj_long j, twE6_proj_pairRoot 0] at hproj
  exact twE6Delta_add_alpha_not_isRoot j hproj

private theorem twE6Long_add_pairRoot_ne_zero (j : Fin 12) :
    twE6Long j + twE6PairRoot 0 ≠ 0 := by
  intro h
  have hproj := congrArg proj h
  rw [map_add, map_zero, twE6_proj_long j, twE6_proj_pairRoot 0] at hproj
  exact twE6Delta_add_alpha_ne_zero j hproj

private theorem not_isRoot_twE6Long_add_rho_pairRoot
    (j : Fin 12) : ¬ IsRoot .E6 (twE6Long j + rho (twE6PairRoot 0)) := by
  intro h
  have hproj := isRoot_proj h
  rw [map_add, twE6_proj_long j, proj_rho, twE6_proj_pairRoot 0] at hproj
  exact twE6Delta_add_alpha_not_isRoot j hproj

private theorem twE6Long_add_rho_pairRoot_ne_zero
    (j : Fin 12) : twE6Long j + rho (twE6PairRoot 0) ≠ 0 := by
  intro h
  have hproj := congrArg proj h
  rw [map_add, map_zero, twE6_proj_long j, proj_rho, twE6_proj_pairRoot 0] at hproj
  exact twE6Delta_add_alpha_ne_zero j hproj

private theorem twE6Y_mem_twE6Delta
    {k : Type} [Field k] (θ : k →+* k) (j : Fin 12) :
    twE6Y θ j ∈ twistedRootGroup k θ (twE6Delta j) := by
  change xFixed θ (twE6Long_isRoot j) (twE6Long_rho j) (1 : k) (map_one θ) ∈
    twistedRootGroup k θ (twE6Delta j)
  have h := xFixed_mem θ (twE6Long_isRoot j) (twE6Long_rho j) (1 : k) (map_one θ)
  rwa [twE6_proj_long j] at h

private theorem linIndepPair_of_level_zero {δ γ : Fin (Tag.rank .F4) → ℤ}
    (hδne : δ ≠ 0) (hδ0 : δ twE6Last = 0) (hγne : γ twE6Last ≠ 0) :
    LinIndepPair δ γ := by
  intro a b hab
  have h := congrFun hab twE6Last
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at h
  simp only [zsmul_eq_mul] at h
  rw [hδ0, mul_zero, zero_add] at h
  have hb : b = 0 := (mul_eq_zero.mp h).resolve_right hγne
  subst hb
  rw [zero_smul, add_zero] at hab
  have ha : a = 0 := by
    obtain ⟨i, hi⟩ : ∃ i, δ i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hδne (funext h')
    have h2 := congrFun hab i
    simp only [Pi.smul_apply, Pi.zero_apply, zsmul_eq_mul] at h2
    exact (mul_eq_zero.mp h2).resolve_right hi
  exact ⟨ha, rfl⟩

private theorem openCone_last_ge {δ γ ε : Fin (Tag.rank .F4) → ℤ} {l : ℤ}
    (hδ0 : δ twE6Last = 0) (hl1 : 1 ≤ l) (hγl : l ≤ γ twE6Last)
    (hε : ε ∈ openCone {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β} δ γ) :
    l ≤ ε twE6Last := by
  obtain ⟨-, a, b, -, hb, heq⟩ := hε
  have hlev : ε twE6Last = (a : ℤ) * (δ twE6Last) + (b : ℤ) * (γ twE6Last) := by
    rw [heq]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply]
    simp only [nsmul_eq_mul]
  rw [hlev, hδ0, mul_zero, zero_add]
  have hl0 : (0 : ℤ) ≤ l := le_trans (by norm_num) hl1
  have hb1 : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  calc l = 1 * l := (one_mul l).symm
    _ ≤ (b : ℤ) * (γ twE6Last) := mul_le_mul hb1 hγl hl0 (by positivity)

private theorem iSup_openCone_le_ggSub
    {k : Type} [Field k] (θ : k →+* k)
    (S : Set (Fin (Tag.rank .F4) → ℤ)) (l : ℤ)
    (hSall : ∀ ε, IsRoot .F4 ε → l ≤ ε twE6Last → ε ∈ S)
    {δ γ : Fin (Tag.rank .F4) → ℤ} (hδ0 : δ twE6Last = 0) (hl1 : 1 ≤ l)
    (hγl : l ≤ γ twE6Last) :
    (⨆ ε ∈ openCone {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β} δ γ,
      twistedRootGroup k θ ε) ≤ ggSub (twistedDatum k θ) S :=
  iSup₂_le fun ε hε =>
    le_iSup₂_of_le (f := fun ε (_ : ε ∈ S) => twistedRootGroup k θ ε) ε
      (hSall ε hε.1 (openCone_last_ge hδ0 hl1 hγl hε)) le_rfl

private theorem conj_mem_ggSub_of_mem_rootGroup_level_zero
    {k : Type} [Field k] (θ : k →+* k)
    (S : Set (Fin (Tag.rank .F4) → ℤ)) (l : ℤ)
    (hSall : ∀ ε, IsRoot .F4 ε → l ≤ ε twE6Last → ε ∈ S)
    (hSlev : ∀ γ ∈ S, l ≤ γ twE6Last) (hl1 : 1 ≤ l)
    (δ : Fin (Tag.rank .F4) → ℤ) (hδne : δ ≠ 0) (hδ0 : δ twE6Last = 0)
    {g : fixedGroup k θ} (hg : g ∈ twistedRootGroup k θ δ)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ S) {x : fixedGroup k θ}
    (hx : x ∈ twistedRootGroup k θ γ) :
    g * x * g⁻¹ ∈ ggSub (twistedDatum k θ) S := by
  have hγl : l ≤ γ twE6Last := hSlev γ hγ
  have hγne : γ twE6Last ≠ 0 := by
    intro h0
    have h1 : (1 : ℤ) ≤ (0 : ℤ) := by rw [← h0]; exact le_trans hl1 hγl
    omega
  have hlin : LinIndepPair δ γ := linIndepPair_of_level_zero hδne hδ0 hγne
  have hcu := commutator_mem_iSup_twistedRootGroup hlin hg hx
  have hmem : ⁅g, x⁆ ∈ ggSub (twistedDatum k θ) S :=
    (iSup_openCone_le_ggSub θ S l hSall hδ0 hl1 hγl) hcu
  have hxS : x ∈ ggSub (twistedDatum k θ) S :=
    le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl hx
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem hmem hxS

private theorem mem_normalizer_ggSub_of_forall
    {k : Type} [Field k] (θ : k →+* k)
    (S : Set (Fin (Tag.rank .F4) → ℤ)) {u : fixedGroup k θ}
    (h : ∀ γ ∈ S, ∀ x ∈ twistedRootGroup k θ γ, u * x * u⁻¹ ∈ ggSub (twistedDatum k θ) S)
    (h' : ∀ γ ∈ S, ∀ x ∈ twistedRootGroup k θ γ, u⁻¹ * x * u ∈ ggSub (twistedDatum k θ) S) :
    u ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) S : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hm : (ggSub (twistedDatum k θ) S).map (MulAut.conj u).toMonoidHom ≤
        ggSub (twistedDatum k θ) S := by
      change (⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ).map
        (MulAut.conj u).toMonoidHom ≤ ⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ
      rw [Subgroup.map_iSup]
      refine iSup_le fun γ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hγ => ?_
      rintro y ⟨z, hz, rfl⟩
      change u * z * u⁻¹ ∈ ggSub (twistedDatum k θ) S
      exact h γ hγ z hz
    exact hm ⟨x, hx, rfl⟩
  · intro hx
    have hm : (ggSub (twistedDatum k θ) S).map (MulAut.conj u⁻¹).toMonoidHom ≤
        ggSub (twistedDatum k θ) S := by
      change (⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ).map
        (MulAut.conj u⁻¹).toMonoidHom ≤ ⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ
      rw [Subgroup.map_iSup]
      refine iSup_le fun γ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hγ => ?_
      rintro y ⟨z, hz, rfl⟩
      change u⁻¹ * z * u ∈ ggSub (twistedDatum k θ) S
      exact h' γ hγ z hz
    have hmem := hm ⟨u * x * u⁻¹, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hmem

private theorem nHat_conj_le_ggSub
    {k : Type} [Field k] (θ : k →+* k) (S : Set (Fin (Tag.rank .F4) → ℤ))
    (i : Fin (Tag.rank .F4)) (hS : ∀ γ ∈ S, IsRoot .F4 γ)
    (hSrefl : ∀ γ ∈ S, reflect .F4 i γ ∈ S) :
    (ggSub (twistedDatum k θ) S).map (MulAut.conj (nHat θ i)).toMonoidHom ≤
      ggSub (twistedDatum k θ) S := by
  change (⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ).map
    (MulAut.conj (nHat θ i)).toMonoidHom ≤ ⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ
  rw [Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  rintro y ⟨z, hz, rfl⟩
  change nHat θ i * z * (nHat θ i)⁻¹ ∈ ggSub (twistedDatum k θ) S
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ)
    (reflect .F4 i γ) (hSrefl γ hγ) le_rfl (nHat_conj_mem θ i (hS γ hγ) hz)

private theorem nHat_inv_conj_le_ggSub
    {k : Type} [Field k] (θ : k →+* k) (S : Set (Fin (Tag.rank .F4) → ℤ))
    (i : Fin (Tag.rank .F4)) (hS : ∀ γ ∈ S, IsRoot .F4 γ)
    (hSrefl : ∀ γ ∈ S, reflect .F4 i γ ∈ S) :
    (ggSub (twistedDatum k θ) S).map (MulAut.conj (nHat θ i)⁻¹).toMonoidHom ≤
      ggSub (twistedDatum k θ) S := by
  change (⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ).map
    (MulAut.conj (nHat θ i)⁻¹).toMonoidHom ≤ ⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ
  rw [Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  rintro y ⟨z, hz, rfl⟩
  change (nHat θ i)⁻¹ * z * ((nHat θ i)⁻¹)⁻¹ ∈ ggSub (twistedDatum k θ) S
  have hz' : nHat θ i * z * (nHat θ i)⁻¹ ∈ twistedRootGroup k θ (reflect .F4 i γ) :=
    nHat_conj_mem θ i (hS γ hγ) hz
  have ht : nHat θ i ^ 2 ∈ hHat k θ i := nHat_sq_mem θ i
  have htinv : (nHat θ i ^ 2)⁻¹ ∈ hHat k θ i := inv_mem ht
  have hmem := hHat_conj_mem θ i (hS (reflect .F4 i γ) (hSrefl γ hγ)) htinv hz'
  have e : (nHat θ i)⁻¹ * z * ((nHat θ i)⁻¹)⁻¹ =
      (nHat θ i ^ 2)⁻¹ * (nHat θ i * z * (nHat θ i)⁻¹) *
        ((nHat θ i ^ 2)⁻¹)⁻¹ := by
    simp only [pow_two, inv_inv]
    group
  rw [e]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ)
    (reflect .F4 i γ) (hSrefl γ hγ) le_rfl hmem

private theorem nHat_mem_normalizer_ggSub
    {k : Type} [Field k] (θ : k →+* k) (S : Set (Fin (Tag.rank .F4) → ℤ))
    (i : Fin (Tag.rank .F4)) (hS : ∀ γ ∈ S, IsRoot .F4 γ)
    (hSrefl : ∀ γ ∈ S, reflect .F4 i γ ∈ S) :
    nHat θ i ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) S : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) :=
  mem_normalizer_ggSub_of_forall θ S
    (fun γ hγ x hx => (nHat_conj_le_ggSub θ S i hS hSrefl)
      ⟨x, le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl hx,
        rfl⟩)
    (fun γ hγ x hx => (nHat_inv_conj_le_ggSub θ S i hS hSrefl)
      ⟨x, le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl hx,
        rfl⟩)

private theorem hHat_mem_normalizer_ggSub
    {k : Type} [Field k] (θ : k →+* k) (S : Set (Fin (Tag.rank .F4) → ℤ))
    (i : Fin (Tag.rank .F4)) (hS : ∀ γ ∈ S, IsRoot .F4 γ) {h : fixedGroup k θ}
    (hh : h ∈ hHat k θ i) :
    h ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) S : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  apply mem_normalizer_ggSub_of_forall θ S
  · intro γ hγ x hx
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl
      (hHat_conj_mem θ i (hS γ hγ) hh hx)
  · intro γ hγ x hx
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl
      (by simpa only [inv_inv] using hHat_conj_mem θ i (hS γ hγ) (inv_mem hh) hx)

private theorem twE6Delta_le_centralizer_alpha
    {k : Type} [Field k] (θ : k →+* k) (j : Fin 12) :
    twistedRootGroup k θ (twE6Delta j) ≤
      Subgroup.centralizer
        ((twistedRootGroup k θ twE6Alpha : Subgroup (fixedGroup k θ)) :
          Set (fixedGroup k θ)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨c, -, hg_eq⟩ :=
    (mem_twistedRootGroup_iff_of_fixed θ (twE6Long_isRoot j) (twE6_proj_long j)
      (twE6Long_rho j) g).1 hg
  obtain ⟨c', hx_eq⟩ :=
    (mem_twistedRootGroup_iff_of_pair θ (twE6PairRoot_isRoot 0) (twE6_proj_pairRoot 0)
      (twE6PairRoot_ne_rho 0) x).1 hx
  have hc1 : Commute (e6Data_valid.xm k (twE6Long j) c)
      (e6Data_valid.xm k (twE6PairRoot 0) c') :=
    commute_xm (twE6Long_isRoot j) (twE6PairRoot_isRoot 0)
      (twE6Long_add_pairRoot_ne_zero j) (not_isRoot_twE6Long_add_pairRoot j) c c'
  have hc2 : Commute (e6Data_valid.xm k (twE6Long j) c)
      (e6Data_valid.xm k (rho (twE6PairRoot 0))
        ((twistSign (twE6PairRoot 0) : k) * θ c')) :=
    commute_xm (twE6Long_isRoot j) (isRoot_rho (twE6PairRoot_isRoot 0))
      (twE6Long_add_rho_pairRoot_ne_zero j) (not_isRoot_twE6Long_add_rho_pairRoot j) c _
  have hcomm : Commute g x := by
    apply Subtype.ext
    change (g : e6Data_valid.minGroup k) * (x : e6Data_valid.minGroup k) =
      (x : e6Data_valid.minGroup k) * (g : e6Data_valid.minGroup k)
    rw [hg_eq, hx_eq]
    exact (hc1.mul_right hc2).eq
  exact hcomm.eq.symm

private theorem reflect_shortNode_alpha :
    reflect .F4 twE6ShortNode twE6Alpha = twE6Alpha := by
  decide +kernel

private theorem reflect_last_of_ne (i : Fin (Tag.rank .F4)) (hi : i ≠ twE6Last)
    (v : Fin (Tag.rank .F4) → ℤ) :
    (reflect .F4 i v) twE6Last = v twE6Last := by
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  simp only [zsmul_eq_mul]
  rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero, sub_zero]

private theorem reflect_shortNode_last (v : Fin (Tag.rank .F4) → ℤ) :
    (reflect .F4 twE6ShortNode v) twE6Last = v twE6Last :=
  reflect_last_of_ne twE6ShortNode (by decide) v

theorem twE6Y_mem_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k) (j : Fin 12) :
    twE6Y θ j ∈ Subgroup.normalizer
      (((twistedDatum k θ).rootGroup twE6Alpha : Subgroup (fixedGroup k θ)) :
        Set (fixedGroup k θ)) := by
  have hY : twE6Y θ j ∈ twistedRootGroup k θ (twE6Delta j) := twE6Y_mem_twE6Delta θ j
  have hcent : twE6Y θ j ∈ Subgroup.centralizer
      ((twistedRootGroup k θ twE6Alpha : Subgroup (fixedGroup k θ)) :
        Set (fixedGroup k θ)) :=
    twE6Delta_le_centralizer_alpha θ j hY
  have hcent' : (twE6Y θ j)⁻¹ ∈ Subgroup.centralizer
      ((twistedRootGroup k θ twE6Alpha : Subgroup (fixedGroup k θ)) :
        Set (fixedGroup k θ)) :=
    twE6Delta_le_centralizer_alpha θ j (inv_mem hY)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hc : x * twE6Y θ j = twE6Y θ j * x :=
      (Subgroup.mem_centralizer_iff.1 hcent) x hx
    rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  · intro hx
    have hc : (twE6Y θ j * x * (twE6Y θ j)⁻¹) * (twE6Y θ j)⁻¹ =
        (twE6Y θ j)⁻¹ * (twE6Y θ j * x * (twE6Y θ j)⁻¹) :=
      (Subgroup.mem_centralizer_iff.1 hcent') (twE6Y θ j * x * (twE6Y θ j)⁻¹) hx
    have e : x = (twE6Y θ j)⁻¹ * (twE6Y θ j * x * (twE6Y θ j)⁻¹) * twE6Y θ j := by
      group
    rw [e, hc.symm, mul_assoc, inv_mul_cancel, mul_one]
    exact hx

theorem nHat_mem_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k) :
    nHat θ twE6ShortNode ∈ Subgroup.normalizer
      (((twistedDatum k θ).rootGroup twE6Alpha : Subgroup (fixedGroup k θ)) :
        Set (fixedGroup k θ)) := by
  have hα : IsRoot .F4 twE6Alpha := by
    have h := twE6_alpha_mem_roots θ
    rwa [twistedDatum_roots] at h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := nHat_conj_mem θ twE6ShortNode hα hx
    rwa [reflect_shortNode_alpha] at h
  · intro hx
    have ht : nHat θ twE6ShortNode ^ 2 ∈ hHat k θ twE6ShortNode := nHat_sq_mem θ _
    have htinv : (nHat θ twE6ShortNode ^ 2)⁻¹ ∈ hHat k θ twE6ShortNode := inv_mem ht
    have hz : (nHat θ twE6ShortNode ^ 2)⁻¹ *
        (nHat θ twE6ShortNode * x * (nHat θ twE6ShortNode)⁻¹) *
          ((nHat θ twE6ShortNode ^ 2)⁻¹)⁻¹ ∈ twistedRootGroup k θ twE6Alpha :=
      hHat_conj_mem θ twE6ShortNode hα htinv hx
    have hz2 : (nHat θ twE6ShortNode ^ 2)⁻¹ *
        (nHat θ twE6ShortNode * x * (nHat θ twE6ShortNode)⁻¹) *
          ((nHat θ twE6ShortNode ^ 2)⁻¹)⁻¹ =
        (nHat θ twE6ShortNode)⁻¹ * x * nHat θ twE6ShortNode := by
      simp only [pow_two, inv_inv]
      group
    rw [hz2] at hz
    have h3 := nHat_conj_mem θ twE6ShortNode hα hz
    rw [reflect_shortNode_alpha] at h3
    have h3' : nHat θ twE6ShortNode * ((nHat θ twE6ShortNode)⁻¹ * x * nHat θ twE6ShortNode) *
        (nHat θ twE6ShortNode)⁻¹ = x := by group
    rw [h3'] at h3
    exact h3

theorem hHat_le_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k) (i : Fin (Tag.rank .F4)) :
    hHat k θ i ≤ Subgroup.normalizer
      (((twistedDatum k θ).rootGroup twE6Alpha : Subgroup (fixedGroup k θ)) :
        Set (fixedGroup k θ)) := by
  have hα : IsRoot .F4 twE6Alpha := by
    have h := twE6_alpha_mem_roots θ
    rwa [twistedDatum_roots] at h
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hHat_conj_mem θ i hα hh hx
  · intro hx
    have h' := hHat_conj_mem θ i hα (inv_mem hh) hx
    have e : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
    rwa [e] at h'

theorem twE6Y_mem_normalizer_rad_cen
    {k : Type} [Field k] (θ : k →+* k) (j : Fin 12) :
    twE6Y θ j ∈ Subgroup.normalizer
        ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) ⊓
      Subgroup.normalizer ((twE6Cen θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  have hY : twE6Y θ j ∈ twistedRootGroup k θ (twE6Delta j) := twE6Y_mem_twE6Delta θ j
  have hYinv : (twE6Y θ j)⁻¹ ∈ twistedRootGroup k θ (twE6Delta j) := inv_mem hY
  have hRadAll : ∀ ε : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 ε → 1 ≤ ε twE6Last →
      ε ∈ {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} :=
    fun ε hε hlev => ⟨by rwa [twistedDatum_roots], hlev⟩
  have hRadLev : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last}, 1 ≤ γ twE6Last :=
    fun _ hγ => hγ.2
  have hCenAll : ∀ ε : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 ε → 2 ≤ ε twE6Last →
      ε ∈ {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last} :=
    fun ε hε hlev => ⟨by rwa [twistedDatum_roots], hlev⟩
  have hCenLev : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last}, 2 ≤ γ twE6Last :=
    fun _ hγ => hγ.2
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show twE6Y θ j ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} :
          Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))
    refine mem_normalizer_ggSub_of_forall θ _ ?_ ?_
    · intro γ hγ x hx
      exact conj_mem_ggSub_of_mem_rootGroup_level_zero θ _ 1 hRadAll hRadLev
        (by norm_num) (twE6Delta j) (twE6Delta_ne_zero j) (twE6Delta_last j) hY hγ hx
    · intro γ hγ x hx
      exact conj_mem_ggSub_of_mem_rootGroup_level_zero θ _ 1 hRadAll hRadLev
        (by norm_num) (twE6Delta j) (twE6Delta_ne_zero j) (twE6Delta_last j) hYinv hγ hx
  · show twE6Y θ j ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last} :
          Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))
    refine mem_normalizer_ggSub_of_forall θ _ ?_ ?_
    · intro γ hγ x hx
      exact conj_mem_ggSub_of_mem_rootGroup_level_zero θ _ 2 hCenAll hCenLev
        (by norm_num) (twE6Delta j) (twE6Delta_ne_zero j) (twE6Delta_last j) hY hγ hx
    · intro γ hγ x hx
      exact conj_mem_ggSub_of_mem_rootGroup_level_zero θ _ 2 hCenAll hCenLev
        (by norm_num) (twE6Delta j) (twE6Delta_ne_zero j) (twE6Delta_last j) hYinv hγ hx

theorem nHat_mem_normalizer_rad_cen
    {k : Type} [Field k] (θ : k →+* k) :
    nHat θ twE6ShortNode ∈
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) ⊓
        Subgroup.normalizer ((twE6Cen θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  have hRadRoot : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last}, IsRoot .F4 γ := by
    rintro γ ⟨hγ, -⟩
    rwa [twistedDatum_roots] at hγ
  have hRadRefl : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
      reflect .F4 twE6ShortNode γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} := by
    rintro γ ⟨hγ, hlev⟩
    refine ⟨?_, ?_⟩
    · rw [twistedDatum_roots] at hγ ⊢
      exact hγ.reflect twE6ShortNode
    · rwa [reflect_shortNode_last]
  have hCenRoot : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last}, IsRoot .F4 γ := by
    rintro γ ⟨hγ, -⟩
    rwa [twistedDatum_roots] at hγ
  have hCenRefl : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last},
      reflect .F4 twE6ShortNode γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last} := by
    rintro γ ⟨hγ, hlev⟩
    refine ⟨?_, ?_⟩
    · rw [twistedDatum_roots] at hγ ⊢
      exact hγ.reflect twE6ShortNode
    · rwa [reflect_shortNode_last]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show nHat θ twE6ShortNode ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} :
          Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))
    exact nHat_mem_normalizer_ggSub θ _ twE6ShortNode hRadRoot hRadRefl
  · show nHat θ twE6ShortNode ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last} :
          Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))
    exact nHat_mem_normalizer_ggSub θ _ twE6ShortNode hCenRoot hCenRefl

theorem hHat_le_normalizer_rad_cen
    {k : Type} [Field k] (θ : k →+* k) (i : Fin (Tag.rank .F4)) :
    hHat k θ i ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) ⊓
        Subgroup.normalizer ((twE6Cen θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  have hRadRoot : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last}, IsRoot .F4 γ := by
    rintro γ ⟨hγ, -⟩
    rwa [twistedDatum_roots] at hγ
  have hCenRoot : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ |
      γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last}, IsRoot .F4 γ := by
    rintro γ ⟨hγ, -⟩
    rwa [twistedDatum_roots] at hγ
  refine le_inf ?_ ?_
  · intro h hh
    show h ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} :
          Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))
    exact hHat_mem_normalizer_ggSub θ _ i hRadRoot hh
  · intro h hh
    show h ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) {γ : Fin (Tag.rank .F4) → ℤ |
        γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last} :
          Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))
    exact hHat_mem_normalizer_ggSub θ _ i hCenRoot hh

end CFSG.StandardType.LieKnownR2.Short
