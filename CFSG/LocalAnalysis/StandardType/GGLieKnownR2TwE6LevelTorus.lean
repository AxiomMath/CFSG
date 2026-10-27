module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NDefs
public import CFSG.LieType.TitsSimplicity.LeviSteinberg
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.StandardType.LieKnownR2.TwE6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.StandardType.LieKnownR2.Short
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Minuscule.MinData
open scoped commutatorElement

@[expose] def twE6LevelNu : Fin (Tag.rank .F4) → ℕ := ![2, 4, 3, 2]

@[expose] noncomputable def twE6LevelTorus
    {k : Type} [Field k] (θ : k →+* k) (μ : (fixedSubfield θ)ˣ) : fixedGroup k θ :=
  torS θ fun i => μ ^ twE6LevelNu i

private theorem l10se2b1_level_eq :
    ∀ γ ∈ rootFinset Tag.F4,
      γ twE6Last = ∑ i, (twE6LevelNu i : ℤ) * toWeight γ i := by
  decide +kernel

private theorem l10se2b1_level_le_two :
    ∀ γ ∈ rootFinset Tag.F4, γ twE6Last ≤ 2 := by
  decide +kernel

private theorem l10se2b1_prod_zpow {G : Type*} [CommGroup G] {ι : Type*} (t : Finset ι)
    (y : G) (e : ι → ℤ) : (∏ i ∈ t, y ^ e i) = y ^ (∑ i ∈ t, e i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

private theorem l10se2b1_torS_mem_rootGroup
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ}
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum k θ).roots)
    {y : fixedGroup k θ} (hy : y ∈ (twistedDatum k θ).rootGroup γ) :
    torS θ s * y * (torS θ s)⁻¹ ∈ (twistedDatum k θ).rootGroup γ := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq (isRoot_of_mem_twistedDatum_roots θ hγ)
  by_cases hfix : rho α = α
  · obtain ⟨c, hc, hyeq⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ hα hp hfix y).1 hy
    have hyx : y = xFixed θ hα hfix c hc := by
      apply Subtype.ext
      simpa only [xFixed_val] using hyeq
    have heq := torS_conj_xFixed θ s hα hfix c hc
    rw [← hyx] at heq
    rw [heq, ← hp]
    exact xFixed_mem θ hα hfix _ _
  · obtain ⟨c, hyeq⟩ :=
      (mem_twistedRootGroup_iff_of_pair θ hα hp hfix y).1 hy
    have hyx : y = xPair θ hθ hα hfix c := by
      apply Subtype.ext
      simpa only [xPair_val] using hyeq
    have heq := torS_conj_xPair θ hθ s hα hfix c
    rw [← hyx] at heq
    rw [heq, ← hp]
    exact xPair_mem θ hθ hα hfix _

private theorem l10se2b1_torS_one
    {k : Type} [Field k] (θ : k →+* k) :
    torS θ (1 : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) = 1 := by
  apply Subtype.ext
  simp only [torS, torU, coeU]
  exact map_one _

private theorem l10se2b1_torS_inv
    {k : Type} [Field k] (θ : k →+* k)
    (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) :
    torS θ s⁻¹ = (torS θ s)⁻¹ := by
  have h1 : torS θ s * torS θ s⁻¹ = 1 := by
    rw [← torS_mul, mul_inv_cancel, l10se2b1_torS_one]
  exact eq_inv_of_mul_eq_one_right h1

private theorem l10se2b1_chiS_eq
    {k : Type} [Field k] (θ : k →+* k) {μ : (fixedSubfield θ)ˣ}
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum k θ).roots) :
    chiS θ (fun i => μ ^ twE6LevelNu i) γ = μ ^ (γ twE6Last) := by
  let γ' : Fin (Tag.rank .F4) → ℤ := γ
  have hγF : γ' ∈ rootFinset Tag.F4 :=
    mem_rootFinset.mpr (isRoot_of_mem_twistedDatum_roots θ hγ)
  change (∏ i, (fun i => μ ^ twE6LevelNu i) i ^ toWeight γ' i) = μ ^ (γ twE6Last)
  calc (∏ i, (fun i => μ ^ twE6LevelNu i) i ^ toWeight γ' i)
      = ∏ i, μ ^ ((twE6LevelNu i : ℤ) * toWeight γ' i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show (fun i => μ ^ twE6LevelNu i) i = μ ^ ((twE6LevelNu i : ℤ)) by simp,
          ← zpow_mul]
    _ = μ ^ (∑ i, (twE6LevelNu i : ℤ) * toWeight γ' i) :=
        l10se2b1_prod_zpow Finset.univ μ _
    _ = μ ^ (γ twE6Last) := by
        rw [show γ twE6Last = ∑ i, (twE6LevelNu i : ℤ) * toWeight γ' i from
          l10se2b1_level_eq γ' hγF]

private theorem l10se2b1_zpow_two_ne_one
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) {μ : (fixedSubfield θ)ˣ}
    (hμ : μ ≠ 1) : μ ^ (2 : ℤ) ≠ 1 := by
  haveI : CharP ↥(fixedSubfield θ) 2 := CharP.subring k 2 (fixedSubfield θ).toSubring
  intro h
  have hsq : ((μ : fixedSubfield θ)) ^ 2 = 1 := by
    have := congrArg (fun u : (fixedSubfield θ)ˣ => (u : fixedSubfield θ)) h
    simpa using this
  have h2 : (2 : fixedSubfield θ) = 0 := CharP.cast_eq_zero _ 2
  have h11 : (1 : fixedSubfield θ) + 1 = 0 := by
    rw [show (1 : fixedSubfield θ) + 1 = 2 by norm_num, h2]
  have hexp : ((μ : fixedSubfield θ) - 1) ^ 2 = ((μ : fixedSubfield θ)) ^ 2 + 1 := by
    rw [sub_sq, h2]; ring
  have hzero : ((μ : fixedSubfield θ) - 1) ^ 2 = 0 := by
    rw [hexp, hsq, h11]
  have h1 : (μ : fixedSubfield θ) - 1 = 0 := sq_eq_zero_iff.mp hzero
  exact hμ (Units.ext (sub_eq_zero.mp h1))

private theorem l10se2b1_rootGroup_eq_one_of_fixed
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {μ : (fixedSubfield θ)ˣ} (hμ : μ ≠ 1)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum k θ).roots)
    (hlvl : 1 ≤ γ twE6Last)
    {y : fixedGroup k θ} (hy : y ∈ (twistedDatum k θ).rootGroup γ)
    (hyfix : torS θ (fun i => μ ^ twE6LevelNu i) * y *
      (torS θ (fun i => μ ^ twE6LevelNu i))⁻¹ = y) :
    y = 1 := by
  have hγF : γ ∈ rootFinset Tag.F4 :=
    mem_rootFinset.mpr (isRoot_of_mem_twistedDatum_roots θ hγ)
  have hlevel_le : γ twE6Last ≤ 2 := l10se2b1_level_le_two γ hγF
  obtain ⟨α, hα, hp⟩ := exists_proj_eq (isRoot_of_mem_twistedDatum_roots θ hγ)
  have hchi_proj : chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) = μ ^ (γ twE6Last) := by
    rw [hp]
    exact l10se2b1_chiS_eq θ hγ
  have hscalar_ne :
      ((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k) ≠ 1 := by
    rw [hchi_proj]
    intro h1
    have hμeq : μ ^ (γ twE6Last) = 1 := by
      apply Units.ext
      apply Subtype.ext
      simpa using h1
    have hlev : γ twE6Last = 1 ∨ γ twE6Last = 2 := by omega
    rcases hlev with h1' | h2'
    · rw [h1'] at hμeq
      exact hμ (by simpa using hμeq)
    · rw [h2'] at hμeq
      exact l10se2b1_zpow_two_ne_one θ hμ (by simpa using hμeq)
  by_cases hfixα : rho α = α
  · obtain ⟨c, hc, hyeq⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ hα hp hfixα y).1 hy
    have hyx : y = xFixed θ hα hfixα c hc := by
      apply Subtype.ext
      simpa only [xFixed_val] using hyeq
    have hconj := torS_conj_xFixed θ (fun i => μ ^ twE6LevelNu i) hα hfixα c hc
    have hEq := hconj.symm
    rw [← hyx, hyfix, hyx] at hEq
    have hxm : e6Data_valid.xm k α
          (((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k) * c) =
        e6Data_valid.xm k α c := by
      have hval := congrArg (fun z : fixedGroup k θ => (z : e6Data_valid.minGroup k)) hEq
      simpa only [xFixed_val] using hval
    have hcc :
        ((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k) * c = c :=
      e6Data_valid.xm_injective k hα hxm
    have hc0 : c = 0 := by
      have hmul : (((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k)
          - 1) * c = 0 := by
        rw [sub_mul, hcc, one_mul, sub_self]
      rcases mul_eq_zero.1 hmul with h | h
      · exact absurd (sub_eq_zero.1 h) hscalar_ne
      · exact h
    rw [hyx]
    apply Subtype.ext
    rw [xFixed_val, hc0, e6Data_valid.xm_zero]
    rfl
  · obtain ⟨c, hyeq⟩ :=
      (mem_twistedRootGroup_iff_of_pair θ hα hp hfixα y).1 hy
    have hyx : y = xPair θ hθ hα hfixα c := by
      apply Subtype.ext
      simpa only [xPair_val] using hyeq
    have hconj := torS_conj_xPair θ hθ (fun i => μ ^ twE6LevelNu i) hα hfixα c
    have hEq := hconj.symm
    rw [← hyx, hyfix, hyx] at hEq
    have hval : e6Data_valid.xm k α
            (((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k) * c) *
          e6Data_valid.xm k (rho α)
            (twistSign α * θ (((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α)
              : (fixedSubfield θ)ˣ) : k) * c)) =
        e6Data_valid.xm k α c * e6Data_valid.xm k (rho α) (twistSign α * θ c) := by
      have h' := congrArg (fun z : fixedGroup k θ => (z : e6Data_valid.minGroup k)) hEq
      simpa only [xPair_val] using h'
    have hcc :
        ((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k) * c = c :=
      (xm_mul_xm_rho_inj hα hfixα hval).1
    have hc0 : c = 0 := by
      have hmul : (((chiS θ (fun i => μ ^ twE6LevelNu i) (proj α) : (fixedSubfield θ)ˣ) : k)
          - 1) * c = 0 := by
        rw [sub_mul, hcc, one_mul, sub_self]
      rcases mul_eq_zero.1 hmul with h | h
      · exact absurd (sub_eq_zero.1 h) hscalar_ne
      · exact h
    rw [hyx]
    apply Subtype.ext
    rw [xPair_val, hc0]
    simp [e6Data_valid.xm_zero]

private theorem l10se2b1_rad_centralizer
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {h : fixedGroup k θ}
    (hnorm : ∀ γ : Fin (Tag.rank .F4) → ℤ, γ ∈ (twistedDatum k θ).roots →
      h ∈ Subgroup.normalizer ((twistedDatum k θ).rootGroup γ : Set (fixedGroup k θ)))
    (hfix : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      γ ∈ (twistedDatum k θ).roots → 1 ≤ γ twE6Last →
      ∀ y ∈ (twistedDatum k θ).rootGroup γ, h * y * h⁻¹ = y → y = 1)
    {y : fixedGroup k θ} (hy : y ∈ twE6Rad θ) (hc : h * y = y * h) :
    y = 1 := by
  let last : Fin (twistedDatum k θ).rank := twE6Last
  let Φ := RootSystem.ofCartan (twistedDatum k θ).isFiniteType (twistedDatum k θ).divisible
  have hct : IsCTGroupDatum (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum k θ).isFiniteType) (twistedDatum k θ).roots
      (twistedDatum k θ).rootGroup (nHat θ) (hHat k θ) := twE6_hct θ hθ
  have hext : SteinbergExtras (twistedDatum k θ) (nHat θ) (hHat k θ) :=
    twistedDatum_steinbergExtras θ hθ
  obtain ⟨L, hnd, hL, hs, hinj⟩ := (isSteinberg_of hct hext).exists_posList
  let L₁ := L.filter (fun γ => decide (1 ≤ γ last))
  have hnd₁ : L₁.Nodup := hnd.filter _
  have hs₁ : L₁.Pairwise (fun a b => ht a ≤ ht b) := hs.sublist List.filter_sublist
  have hinj₁ : ProdInjectiveFor (twistedDatum k θ).rootGroup L₁ :=
    CFSG.LieType.TitsSimplicity.Levi.SE.prodInjectiveFor_of_sublist
      List.filter_sublist hnd hinj
  have hmemL : ∀ γ, γ ∈ (twistedDatum k θ).roots → 1 ≤ γ last → γ ∈ L := by
    intro γ hγ hlvl
    rw [hL]
    refine ⟨RootSystem.mem_pos_of_pos Φ (show γ ∈ Φ.roots from hγ) (j := last)
      (by omega), ?_⟩
    intro δ hδ
    exact CFSG.LieType.TitsSimplicity.Levi.SE.ne_two_smul_of_mem_roots
      (D := twistedDatum k θ) (hdiv := rfl) hγ (show δ ∈ (twistedDatum k θ).roots from hδ)
  have hle : twE6Rad θ ≤ ⨆ v ∈ L₁, (twistedDatum k θ).rootGroup v := by
    rw [twE6Rad, ggSub]
    refine iSup₂_le fun γ hγ => ?_
    exact le_iSup₂_of_le γ (List.mem_filter.mpr ⟨hmemL γ hγ.1 hγ.2, decide_eq_true hγ.2⟩) le_rfl
  have hc₁ : ∀ a ∈ L₁, ∀ b ∈ L₁, a ≠ b →
      ∀ x ∈ (twistedDatum k θ).rootGroup a, ∀ z ∈ (twistedDatum k θ).rootGroup b,
      ⁅x, z⁆ ∈ ⨆ c ∈ L₁, ⨆ (_ : min (ht a) (ht b) < ht c),
        (twistedDatum k θ).rootGroup c := by
    intro a ha b hb hab x hx z hz
    obtain ⟨haL, hal⟩ := List.mem_filter.mp ha
    obtain ⟨hbL, hbl⟩ := List.mem_filter.mp hb
    have haR : a ∈ (twistedDatum k θ).roots := ((hL a).1 haL).1.1
    have hbR : b ∈ (twistedDatum k θ).roots := ((hL b).1 hbL).1.1
    have haI : Φ.IsIndiv a := ((hL a).1 haL).2
    have hbI : Φ.IsIndiv b := ((hL b).1 hbL).2
    have haP : a ∈ Φ.pos := ((hL a).1 haL).1
    have hbP : b ∈ Φ.pos := ((hL b).1 hbL).1
    have hal' : 1 ≤ a last := of_decide_eq_true hal
    have hbl' : 1 ≤ b last := of_decide_eq_true hbl
    have hli : LinIndepPair a b := Φ.linIndepPair_of_mem_pos haP haI hbP hbI hab
    have hxy := hext.commutator_mem a haR b hbR hli x hx z hz
    have hle' : (⨆ ε ∈ openCone (twistedDatum k θ).roots a b,
        (twistedDatum k θ).rootGroup ε) ≤
        ⨆ c ∈ L₁, ⨆ (_ : min (ht a) (ht b) < ht c),
          (twistedDatum k θ).rootGroup c := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨c, ⟨hcpos, hcind⟩, hlt, hcε⟩ :=
        Φ.exists_of_mem_openCone_pos haP haI hbP hbI hab hε
      have hcL : c ∈ L := (hL c).2 ⟨hcpos, hcind⟩
      have hlevelε : 2 ≤ ε last := by
        obtain ⟨-, m, n, hm, hn, rfl⟩ := hε
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
        have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
        have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
        nlinarith [hal', hbl']
      have hlevelc : 1 ≤ c last := by
        rcases hcε with rfl | h2
        · omega
        · have h2c : ε last = 2 * (c last) := by
            rw [h2]
            rfl
          omega
      have hcL₁ : c ∈ L₁ := List.mem_filter.mpr ⟨hcL, decide_eq_true hlevelc⟩
      have hleε : (twistedDatum k θ).rootGroup ε ≤
          (twistedDatum k θ).rootGroup c := by
        rcases hcε with rfl | h2
        · exact le_rfl
        · rw [h2]
          exact hext.two_smul_le c ((hL c).1 hcL).1.1 (by rw [← h2]; exact hε.1)
      exact hleε.trans (le_iSup₂_of_le c hcL₁ (le_iSup_of_le hlt le_rfl))
    exact hle' hxy
  obtain ⟨F, hF, hFy⟩ := exists_prod_eq_of_commutator_mem (twistedDatum k θ).rootGroup ht
    hnd₁ hs₁ hc₁ y (hle hy)
  have hfixfac : ∀ γ ∈ L₁, h * F γ * h⁻¹ = F γ := by
    intro γ hγ
    obtain ⟨hγL, -⟩ := List.mem_filter.mp hγ
    have hγR : γ ∈ (twistedDatum k θ).roots := ((hL γ).1 hγL).1.1
    have hmap : (L₁.map fun δ => h * F δ * h⁻¹).prod = h * (L₁.map F).prod * h⁻¹ := by
      have := map_list_prod (MulAut.conj h).toMonoidHom (L₁.map F)
      simpa [List.map_map, Function.comp_def] using this.symm
    have hprod : (L₁.map fun δ => h * F δ * h⁻¹).prod = (L₁.map F).prod := by
      rw [hmap, ← hFy, hc]
      group
    exact hinj₁ (fun δ => h * F δ * h⁻¹) F
      (fun δ hδ => (Subgroup.mem_normalizer_iff.1
        (hnorm (δ : Fin (Tag.rank .F4) → ℤ) (((hL δ).1 (List.mem_filter.mp hδ).1).1.1))
        (F δ)).1 (hF δ hδ))
      hF hprod γ hγ
  rw [hFy]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hγL, hγl⟩ := List.mem_filter.mp hγ
  exact hfix (γ : Fin (Tag.rank .F4) → ℤ) (((hL γ).1 hγL).1.1) (of_decide_eq_true hγl)
    (F γ) (hF γ hγ) (hfixfac γ hγ)

theorem twE6LevelTorus_mem_normalizer
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (μ : (fixedSubfield θ)ˣ)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum k θ).roots) :
    twE6LevelTorus θ μ ∈
      Subgroup.normalizer ((twistedDatum k θ).rootGroup γ : Set (fixedGroup k θ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact l10se2b1_torS_mem_rootGroup θ hθ hγ hx
  · intro hx
    have hx' : torS θ (fun i => μ ^ twE6LevelNu i) * x *
        (torS θ (fun i => μ ^ twE6LevelNu i))⁻¹ ∈ (twistedDatum k θ).rootGroup γ := hx
    have h2 := l10se2b1_torS_mem_rootGroup θ hθ
      (s := (fun i => μ ^ twE6LevelNu i)⁻¹) hγ hx'
    rw [l10se2b1_torS_inv θ (fun i => μ ^ twE6LevelNu i)] at h2
    simp only [inv_inv] at h2
    convert h2 using 1
    group

theorem twE6Rad_eq_one_of_commute_levelTorus
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {μ : (fixedSubfield θ)ˣ} (hμ : μ ≠ 1) {y : fixedGroup k θ} (hy : y ∈ twE6Rad θ)
    (hc : twE6LevelTorus θ μ * y = y * twE6LevelTorus θ μ) : y = 1 := by
  refine l10se2b1_rad_centralizer θ hθ ?_ ?_ hy hc
  · intro γ hγ
    exact twE6LevelTorus_mem_normalizer θ hθ μ hγ
  · intro γ hγ hlvl z hz hzfix
    exact l10se2b1_rootGroup_eq_one_of_fixed θ hθ hμ hγ hlvl hz hzfix

end CFSG.StandardType.LieKnownR2.TwE6
