module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NPanel
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NTor
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Norm
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
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

private def l10sw1_nu : Fin (Tag.rank .F4) → ℕ := ![2, 4, 3, 2]

private theorem l10sw1_level_eq :
    ∀ γ ∈ rootFinset Tag.F4,
      γ twE6Last = ∑ i, (l10sw1_nu i : ℤ) * toWeight γ i := by
  decide +kernel

private theorem l10sw1_level_le_two :
    ∀ γ ∈ rootFinset Tag.F4, γ twE6Last ≤ 2 := by
  decide +kernel

private theorem l10sw1_prod_zpow {G : Type*} [CommGroup G] {ι : Type*} (t : Finset ι)
    (y : G) (e : ι → ℤ) : (∏ i ∈ t, y ^ e i) = y ^ (∑ i ∈ t, e i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

private theorem l10sw1_torS_mem_rootGroup
    {f : ℕ} (hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c)
    {s : Fin (Tag.rank .F4) → (fixedSubfield (frobQ 2 f))ˣ}
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum (GaloisField 2 (2 * f))
      (frobQ 2 f)).roots)
    {y : twistedE6Group 2 f} (hy : y ∈ twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) γ) :
    torS (frobQ 2 f) s * y * (torS (frobQ 2 f) s)⁻¹ ∈
      twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) γ := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq (isRoot_of_mem_twistedDatum_roots (frobQ 2 f) hγ)
  by_cases hfix : rho α = α
  · obtain ⟨c, hc, hyeq⟩ :=
      (mem_twistedRootGroup_iff_of_fixed (frobQ 2 f) hα hp hfix y).1 hy
    have hyx : y = xFixed (frobQ 2 f) hα hfix c hc := by
      apply Subtype.ext
      simpa only [xFixed_val] using hyeq
    have heq := torS_conj_xFixed (frobQ 2 f) s hα hfix c hc
    rw [← hyx] at heq
    rw [heq, ← hp]
    exact xFixed_mem (frobQ 2 f) hα hfix _ _
  · obtain ⟨c, hyeq⟩ :=
      (mem_twistedRootGroup_iff_of_pair (frobQ 2 f) hα hp hfix y).1 hy
    have hyx : y = xPair (frobQ 2 f) hθ hα hfix c := by
      apply Subtype.ext
      simpa only [xPair_val] using hyeq
    have heq := torS_conj_xPair (frobQ 2 f) hθ s hα hfix c
    rw [← hyx] at heq
    rw [heq, ← hp]
    exact xPair_mem (frobQ 2 f) hθ hα hfix _

private theorem l10sw1_level_torus
    {f : ℕ} (hf : 2 ≤ f) :
    ∃ h : twistedE6Group 2 f,
      (∀ γ : Fin (Tag.rank .F4) → ℤ, γ ∈ (twistedDatum (GaloisField 2 (2 * f))
          (frobQ 2 f)).roots →
        h ∈ Subgroup.normalizer
          (twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) γ : Set (twistedE6Group 2 f))) ∧
      Odd (orderOf h) ∧
      (∀ γ : Fin (Tag.rank .F4) → ℤ,
        γ ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots → 1 ≤ γ twE6Last →
        ∀ y ∈ twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) γ, h * y * h⁻¹ = y → y = 1) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := fun c => frobQ_frobQ 2 f (by omega) c
  haveI : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  haveI : Finite (twistedE6Group 2 f) := Subtype.finite
  haveI : Fintype ((fixedSubfield θ)ˣ) := Fintype.ofFinite _
  have hkcard : Nat.card k = (2 ^ f) ^ 2 := by
    change Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2
    rw [GaloisField.card 2 (2 * f) (by omega), show 2 * f = f * 2 by ring, ← pow_mul]
  have hθq : ∀ c, θ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hFcard : Nat.card (fixedSubfield θ) = 2 ^ f :=
    card_fixedSubfield_of_card (θ := θ) hkcard hθq
  have hunits : Nat.card (fixedSubfield θ)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, hFcard]
  have hodd : Odd (2 ^ f - 1) := by
    have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2]
    refine ⟨2 ^ (f - 1) - 1, ?_⟩
    have : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    omega
  have hcu : 1 < Fintype.card ((fixedSubfield θ)ˣ) := by
    rw [← Nat.card_eq_fintype_card, hunits]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := pow_le_pow_right' (show (1 : ℕ) ≤ 2 by norm_num) hf
    omega
  obtain ⟨μ, hμne⟩ := Fintype.exists_ne_of_one_lt_card hcu (1 : (fixedSubfield θ)ˣ)
  let s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ := fun i => μ ^ (l10sw1_nu i : ℤ)
  have hμpow : μ ^ (2 ^ f - 1) = 1 := by
    rw [show 2 ^ f - 1 = Nat.card ((fixedSubfield θ)ˣ) from hunits.symm]
    exact pow_card_eq_one'
  have hchi : ∀ γ ∈ (twistedDatum k θ).roots,
      chiS θ s (γ : Fin (Tag.rank .F4) → ℤ) = μ ^ (γ twE6Last) := by
    intro γ hγ
    let γ' : Fin (Tag.rank .F4) → ℤ := γ
    have hγF : γ' ∈ rootFinset Tag.F4 :=
      mem_rootFinset.mpr (isRoot_of_mem_twistedDatum_roots θ hγ)
    change (∏ i, s i ^ toWeight γ' i) = μ ^ (γ twE6Last)
    calc (∏ i, s i ^ toWeight γ' i)
        = ∏ i, μ ^ ((l10sw1_nu i : ℤ) * toWeight γ' i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [show s i = μ ^ (l10sw1_nu i : ℤ) from rfl, ← zpow_mul]
      _ = μ ^ (∑ i, (l10sw1_nu i : ℤ) * toWeight γ' i) :=
          l10sw1_prod_zpow Finset.univ μ _
      _ = μ ^ (γ twE6Last) := by
          rw [show γ twE6Last = ∑ i, (l10sw1_nu i : ℤ) * toWeight γ' i from
            l10sw1_level_eq γ' hγF]
  refine ⟨torS θ s, ?_, ?_, ?_⟩
  · intro γ hγ
    rw [mem_normalizer_iff_map_conj]
    have hle : (twistedRootGroup k θ γ).map
        (MulAut.conj (torS θ s)).toMonoidHom ≤ twistedRootGroup k θ γ := by
      rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      exact l10sw1_torS_mem_rootGroup (f := f) hθ (s := s) hγ hy
    have hcard : Nat.card ((twistedRootGroup k θ γ).map
        (MulAut.conj (torS θ s)).toMonoidHom) = Nat.card (twistedRootGroup k θ γ) :=
      Subgroup.card_map_of_injective (MulAut.conj (torS θ s)).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  · have hpow : (torS θ s) ^ (2 ^ f - 1) = 1 := by
      apply Subtype.ext
      change (minTorus e6Data_valid k (fun a => coeU θ (s (orbitMap a)))) ^ (2 ^ f - 1) = 1
      rw [← map_pow, ← map_one (minTorus e6Data_valid k)]
      congr 1
      funext a
      change (coeU θ (s (orbitMap a))) ^ (2 ^ f - 1) = 1
      rw [← map_pow]
      have hspow : (s (orbitMap a)) ^ (2 ^ f - 1) = 1 := by
        have hμm : μ ^ ((2 ^ f - 1 : ℕ) : ℤ) = 1 := by
          rw [zpow_natCast]
          exact hμpow
        rw [show s (orbitMap a) = μ ^ (l10sw1_nu (orbitMap a) : ℤ) from rfl,
          ← zpow_natCast, ← zpow_mul]
        rw [show (l10sw1_nu (orbitMap a) : ℤ) * ((2 ^ f - 1 : ℕ) : ℤ) =
            ((2 ^ f - 1 : ℕ) : ℤ) * (l10sw1_nu (orbitMap a) : ℤ) by ring,
          zpow_mul, hμm, one_zpow]
      rw [hspow, map_one]
    exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · intro γ hγ hlvl y hy hyfix
    have hγF : γ ∈ rootFinset Tag.F4 :=
      mem_rootFinset.mpr (isRoot_of_mem_twistedDatum_roots θ hγ)
    have hlevel_le : γ twE6Last ≤ 2 := l10sw1_level_le_two γ hγF
    obtain ⟨α, hα, hp⟩ := exists_proj_eq (isRoot_of_mem_twistedDatum_roots θ hγ)
    have hchi_proj : chiS θ s (proj α) = μ ^ (γ twE6Last) := by
      rw [hp]
      exact hchi γ hγ
    have hscalar_ne : ((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) ≠ 1 := by
      rw [hchi_proj]
      intro h1
      have hμeq : μ ^ (γ twE6Last) = 1 := by
        apply Units.ext
        apply Subtype.ext
        simpa using h1
      have hlev : γ twE6Last = 1 ∨ γ twE6Last = 2 := by omega
      rcases hlev with h1' | h2'
      · rw [h1'] at hμeq
        exact hμne (by simpa using hμeq)
      · rw [h2'] at hμeq
        have hord : orderOf μ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hμeq)
        have hordN : orderOf μ ∣ Nat.card ((fixedSubfield θ)ˣ) := orderOf_dvd_natCard μ
        have hgcd : Nat.gcd 2 (Nat.card ((fixedSubfield θ)ˣ)) = 1 := by
          rw [hunits]
          exact Nat.coprime_two_left.mpr hodd
        have hdvd : orderOf μ ∣ 1 := by
          rw [← hgcd]
          exact Nat.dvd_gcd hord hordN
        exact hμne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))
    by_cases hfixα : rho α = α
    · obtain ⟨c, hc, hyeq⟩ :=
        (mem_twistedRootGroup_iff_of_fixed θ hα hp hfixα y).1 hy
      have hyx : y = xFixed θ hα hfixα c hc := by
        apply Subtype.ext
        simpa only [xFixed_val] using hyeq
      have hconj := torS_conj_xFixed θ s hα hfixα c hc
      have hEq := hconj.symm
      rw [← hyx, hyfix, hyx] at hEq
      have hxm : e6Data_valid.xm k α
            (((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) * c) =
          e6Data_valid.xm k α c := by
        have hval := congrArg (fun z : fixedGroup k θ => (z : e6Data_valid.minGroup k)) hEq
        simpa only [xFixed_val] using hval
      have hcc : ((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) * c = c :=
        e6Data_valid.xm_injective k hα hxm
      have hc0 : c = 0 := by
        have hmul : (((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) - 1) * c = 0 := by
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
      have hconj := torS_conj_xPair θ hθ s hα hfixα c
      have hEq := hconj.symm
      rw [← hyx, hyfix, hyx] at hEq
      have hval : e6Data_valid.xm k α
              (((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) * c) *
            e6Data_valid.xm k (rho α)
              (twistSign α * θ (((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) * c)) =
          e6Data_valid.xm k α c * e6Data_valid.xm k (rho α) (twistSign α * θ c) := by
        have h' := congrArg (fun z : fixedGroup k θ => (z : e6Data_valid.minGroup k)) hEq
        simpa only [xPair_val] using h'
      have hcc : ((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) * c = c :=
        (xm_mul_xm_rho_inj hα hfixα hval).1
      have hc0 : c = 0 := by
        have hmul : (((chiS θ s (proj α) : (fixedSubfield θ)ˣ) : k) - 1) * c = 0 := by
          rw [sub_mul, hcc, one_mul, sub_self]
        rcases mul_eq_zero.1 hmul with h | h
        · exact absurd (sub_eq_zero.1 h) hscalar_ne
        · exact h
      rw [hyx]
      apply Subtype.ext
      rw [xPair_val, hc0]
      simp [e6Data_valid.xm_zero]

private theorem l10sw1_rad_centralizer
    {f : ℕ} (hf : 1 ≤ f) {h : twistedE6Group 2 f}
    (hnorm : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      γ ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots →
      h ∈ Subgroup.normalizer
        (twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) γ :
          Set (twistedE6Group 2 f)))
    (hfix : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      γ ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots → 1 ≤ γ twE6Last →
      ∀ y ∈ twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) γ, h * y * h⁻¹ = y → y = 1)
    {y : twistedE6Group 2 f} (hy : y ∈ twE6Rad (frobQ 2 f)) (hc : h * y = y * h) :
    y = 1 := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := fun c => frobQ_frobQ 2 f (by omega) c
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

theorem ggRootNoCentral_twistedE6_shortHighest
    {f : ℕ} (hf : 2 ≤ f) :
    GGRootNoCentralAt (⊤ : Subgroup (twistedE6Group 2 f))
      ((twistedE6Datum 2 f).rootGroup twE6Alpha) := by
  haveI : Finite ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f))) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid _
  haveI : Finite (twistedE6Group 2 f) := Subtype.finite
  obtain ⟨h, hnorm, hodd, hfpf⟩ := l10sw1_level_torus (f := f) hf
  refine noCentral_of_fixedPoint_odd hodd ?_ ?_
  · exact ⟨trivial, hnorm twE6Alpha (twE6_alpha_mem_roots (frobQ 2 f))⟩
  · intro y hy hycomm
    rw [top_inf_eq] at hy
    have hyR : y ∈ twE6Rad (frobQ 2 f) := twE6_pCoreOf_normalizer_le_rad f hf hy
    have hy1 : y = 1 := l10sw1_rad_centralizer (f := f) (by omega) hnorm hfpf hyR hycomm
    rw [hy1]
    exact Subgroup.one_mem _

end CFSG.StandardType.LieKnownR2.TwE6
