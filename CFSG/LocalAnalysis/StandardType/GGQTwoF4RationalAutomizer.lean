module

public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoF4Class
public import CFSG.LocalAnalysis.StandardType.GGLangLatSolv
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoKernel
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open scoped commutatorElement

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootTorus
  CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.StandardType.LangRat CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Std
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.Decide.Bounded in
private theorem f4_orthogonal_frame :
    ∀ e ∈ rts, ∃ a ∈ rts, ipL a e = 0 ∧
      ∃ b ∈ rts, ipL b e = 0 ∧ ipL a b = 0 ∧ ipL a a = ipL b b ∧
        ∃ c ∈ rts, ipL c e = 0 ∧ ipL a c = 0 ∧ ipL b c = 0 ∧ ipL a a = ipL c c ∧
          ∃ u ∈ rts, ipL u e = 0 ∧
            vec4 b = vec4 a - (2 * ipL u a / ipL u u) • vec4 u ∧
            ∃ v ∈ rts, ipL v e = 0 ∧
              vec4 c = vec4 b - (2 * ipL v b / ipL v v) • vec4 v := by
  decide +kernel


theorem exists_orthogonal_frame_perp_F4 {e : Fin Tag.F4.rank → ℤ}
    (he : IsRoot Tag.F4 e) :
    ∃ a b c u v : Fin Tag.F4.rank → ℤ,
      IsRoot Tag.F4 a ∧ IsRoot Tag.F4 b ∧ IsRoot Tag.F4 c ∧
      IsRoot Tag.F4 u ∧ IsRoot Tag.F4 v ∧
      iform a e = 0 ∧ iform b e = 0 ∧ iform c e = 0 ∧ iform u e = 0 ∧ iform v e = 0 ∧
      iform a b = 0 ∧ iform a c = 0 ∧ iform b c = 0 ∧
      rootReflection u • a = b ∧ rootReflection v • b = c := by
  obtain ⟨e', he', rfl⟩ := (mem_rts_iff e).1 he
  obtain ⟨a', ha', hae, b', hb', hbe, hab, hlenb,
    c', hc', hce, hac, hbc, hlenc, u', hu', hue, hub, v', hv', hve, hvc⟩ :=
    f4_orthogonal_frame e' he'
  have ha : IsRoot Tag.F4 (vec4 a') := (mem_rts_iff _).2 ⟨a', ha', rfl⟩
  have hb : IsRoot Tag.F4 (vec4 b') := (mem_rts_iff _).2 ⟨b', hb', rfl⟩
  have hc : IsRoot Tag.F4 (vec4 c') := (mem_rts_iff _).2 ⟨c', hc', rfl⟩
  have hu : IsRoot Tag.F4 (vec4 u') := (mem_rts_iff _).2 ⟨u', hu', rfl⟩
  have hv : IsRoot Tag.F4 (vec4 v') := (mem_rts_iff _).2 ⟨v', hv', rfl⟩
  have hswap1 : rootReflection (vec4 u') • vec4 a' = vec4 b' := by
    rw [rootReflection_smul hu, corootPair]
    simp only [iform_F4, ipF4_vec4]
    exact hub.symm
  have hswap2 : rootReflection (vec4 v') • vec4 b' = vec4 c' := by
    rw [rootReflection_smul hv, corootPair]
    simp only [iform_F4, ipF4_vec4]
    exact hvc.symm
  refine ⟨vec4 a', vec4 b', vec4 c', vec4 u', vec4 v', ha, hb, hc, hu, hv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hswap1, hswap2⟩
  · simpa only [iform_F4, ipF4_vec4] using hae
  · simpa only [iform_F4, ipF4_vec4] using hbe
  · simpa only [iform_F4, ipF4_vec4] using hce
  · simpa only [iform_F4, ipF4_vec4] using hue
  · simpa only [iform_F4, ipF4_vec4] using hve
  · simpa only [iform_F4, ipF4_vec4] using hab
  · simpa only [iform_F4, ipF4_vec4] using hac
  · simpa only [iform_F4, ipF4_vec4] using hbc

private theorem f4_rep_root {L : Type} [Field L] [CharP L 2]
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    canonicalRep (coxeterSystem Tag.F4) L (rootReflection γ) = rootSL2 Tag.F4 L γ WSL := by
  have hEq :=
    (CFSG.RankThree.Chevalley.even_F4_qplus_canonical_Weyl_rational_normalization.2.1 L).2.2.2 γ hγ
  rw [← hEq,
    rootWeylSL2, nSL_one]

private theorem f4_rootWeyl_comm {L : Type} [Field L] [CharP L 2]
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) (hβ : IsRoot Tag.F4 β)
    (horth : iform α β = 0) :
    rootSL2 Tag.F4 L α WSL * rootSL2 Tag.F4 L β WSL =
      rootSL2 Tag.F4 L β WSL * rootSL2 Tag.F4 L α WSL := by
  have hconj : rootReflection β * rootReflection α * (rootReflection β)⁻¹ =
      rootReflection α := by
    rw [← rootReflection_smul_root _ hα,
      rootReflection_smul_of_iform_eq_zero hβ (by rw [iform_comm]; exact horth)]
  have hc : rootReflection α * rootReflection β = rootReflection β * rootReflection α :=
    ((mul_inv_eq_iff_eq_mul).1 hconj).symm
  have hmul :=
    (CFSG.RankThree.Chevalley.even_F4_qplus_canonical_Weyl_rational_normalization.2.1 L).1
  rw [← f4_rep_root hα, ← f4_rep_root hβ, ← hmul, hc, hmul]

private theorem f4_rootWeyl_conj {L : Type} [Field L] [CharP L 2]
    {α β u : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) (hβ : IsRoot Tag.F4 β)
    (hu : IsRoot Tag.F4 u) (hswap : rootReflection u • α = β) :
    rootSL2 Tag.F4 L u WSL * rootSL2 Tag.F4 L α WSL * (rootSL2 Tag.F4 L u WSL)⁻¹ =
      rootSL2 Tag.F4 L β WSL := by
  have hmul :=
    (CFSG.RankThree.Chevalley.even_F4_qplus_canonical_Weyl_rational_normalization.2.1 L).1
  let f : WeylGroup Tag.F4 →* ModGL Tag.F4 L := MonoidHom.mk' _ hmul
  have hrep : ∀ γ, IsRoot Tag.F4 γ → f (rootReflection γ) = rootSL2 Tag.F4 L γ WSL :=
    fun γ hγ => f4_rep_root hγ
  rw [← hrep _ hu, ← hrep _ hα, ← hrep _ hβ, ← map_inv, ← map_mul, ← map_mul,
    ← rootReflection_smul_root _ hα, hswap]

theorem four_dvd_aut_of_perp_frame_F4 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = -γ) {t : Fin Tag.F4.rank → Lˣ}
    (i : KernelComponent (rootCharHom t))
    {a b c u v : Fin Tag.F4.rank → ℤ}
    (ha : IsRoot Tag.F4 a) (hb : IsRoot Tag.F4 b) (hc : IsRoot Tag.F4 c)
    (hu : IsRoot Tag.F4 u) (hv : IsRoot Tag.F4 v)
    (hai : a ∈ componentRoots (rootCharHom t) i)
    (hbi : b ∈ componentRoots (rootCharHom t) i)
    (hci : c ∈ componentRoots (rootCharHom t) i)
    (hui : u ∈ componentRoots (rootCharHom t) i)
    (hvi : v ∈ componentRoots (rootCharHom t) i)
    (hab : iform a b = 0) (hac : iform a c = 0) (hbc : iform b c = 0)
    (hswap1 : rootReflection u • a = b) (hswap2 : rootReflection v • b = c) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom t) i)
      (fullThreeTorus S)) := by
  classical
  let H := rationalSpan S.ρ S.Γ (rootCharHom t) i
  let J := rationalComponent S.ρ S.Γ (rootCharHom t) i
  let n₁ := rootSL2 Tag.F4 L a WSL
  let n₂ := rootSL2 Tag.F4 L b WSL
  let n₃ := rootSL2 Tag.F4 L c WSL
  let p := rootSL2 Tag.F4 L u WSL
  let q := rootSL2 Tag.F4 L v WSL
  have hmem : ∀ γ, IsRoot Tag.F4 γ → γ ∈ componentRoots (rootCharHom t) i →
      rootSL2 Tag.F4 L γ WSL ∈ H := by
    intro γ hγ hγi
    have hrat : γ ∈ rationalRoots S.ρ (rootCharHom t) i := ⟨0, γ, hγi, rfl⟩
    exact ⟨rootSL2_mem_rootSpan_of_mem_rationalRoots S i hrat WSL,
      rootWeylSL2_mem_Γ_of_rho_neg S (Or.inl rfl)
        (f := 1) (by simpa using hq) hAlg hγ (hρ γ hγ)⟩
  have hn₁ := hmem a ha hai
  have hn₂ := hmem b hb hbi
  have hn₃ := hmem c hc hci
  have hp := hmem u hu hui
  have hq' := hmem v hv hvi
  have hsq : ∀ γ, rootSL2 Tag.F4 L γ WSL * rootSL2 Tag.F4 L γ WSL = 1 :=
    rootSL2_WSL_mul_self
  have h12 : Commute n₁ n₂ := f4_rootWeyl_comm ha hb hab
  have h13 : Commute n₁ n₃ := f4_rootWeyl_comm ha hc hac
  have h23 : Commute n₂ n₃ := f4_rootWeyl_comm hb hc hbc
  have hcp : p * n₁ * p⁻¹ = n₂ := f4_rootWeyl_conj ha hb hu hswap1
  have hcq : q * n₂ * q⁻¹ = n₃ := f4_rootWeyl_conj hb hc hv hswap2
  let g := ⁅n₁, p⁆
  let h := ⁅n₂, q⁆
  have hgJ : g ∈ J := Subgroup.commutator_mem_commutator hn₁ hp
  have hhJ : h ∈ J := Subgroup.commutator_mem_commutator hn₂ hq'
  have hinv : ∀ γ, (rootSL2 Tag.F4 L γ WSL)⁻¹ = rootSL2 Tag.F4 L γ WSL :=
    fun γ => inv_eq_of_mul_eq_one_right (hsq γ)
  have hg : g = n₁ * n₂ := by
    calc g = n₁ * (p * n₁ * p⁻¹) := by
            simp only [g, commutatorElement_def, n₁, p, hinv]
            group
      _ = n₁ * n₂ := by rw [hcp]
  have hh : h = n₂ * n₃ := by
    calc h = n₂ * (q * n₂ * q⁻¹) := by
            simp only [h, commutatorElement_def, n₂, q, hinv]
            group
      _ = n₂ * n₃ := by rw [hcq]
  have hg2 : g * g = 1 := by
    rw [hg, ← pow_two, h12.mul_pow, pow_two, pow_two, hsq a, hsq b, one_mul]
  have hh2 : h * h = 1 := by
    rw [hh, ← pow_two, h23.mul_pow, pow_two, pow_two, hsq b, hsq c, one_mul]
  have hgh : g * h = h * g := by
    rw [hg, hh]
    exact ((h12.mul_right h13).mul_left ((Commute.refl n₂).mul_right h23)).eq
  have hN : ∀ γ, IsRoot Tag.F4 γ → rootSL2 Tag.F4 L γ WSL ∈
      Subgroup.normalizer (fullThreeTorus S : Set (ModGL Tag.F4 L)) :=
    fun γ hγ => rootWeylSL2_mem_normalizer_fullThreeTorus S hγ (hρ γ hγ)
  have hgN : g ∈ Subgroup.normalizer (fullThreeTorus S : Set (ModGL Tag.F4 L)) := by
    rw [hg]; exact Subgroup.mul_mem _ (hN a ha) (hN b hb)
  have hhN : h ∈ Subgroup.normalizer (fullThreeTorus S : Set (ModGL Tag.F4 L)) := by
    rw [hh]; exact Subgroup.mul_mem _ (hN b hb) (hN c hc)
  obtain ⟨ζ, hζ, hζ1⟩ := QTwoCav.exists_primitive_cube_root (L := L)
  let d := rootDiagUnit Tag.F4 (fun j => ζ ^ corootPair a (Pi.single j 1))
  let e := rootDiagUnit Tag.F4 (fun j => ζ ^ corootPair c (Pi.single j 1))
  have hdA : d ∈ fullThreeTorus S := corootTuple_mem_fullThreeTorus S (Or.inl rfl) hq hρ ha hζ
  have heA : e ∈ fullThreeTorus S := corootTuple_mem_fullThreeTorus S (Or.inl rfl) hq hρ hc hζ
  have hfix : ∀ α β, IsRoot Tag.F4 α → IsRoot Tag.F4 β → iform α β = 0 →
      rootSL2 Tag.F4 L β WSL *
        rootDiagUnit Tag.F4 (fun j => ζ ^ corootPair α (Pi.single j 1)) *
        (rootSL2 Tag.F4 L β WSL)⁻¹ =
      rootDiagUnit Tag.F4 (fun j => ζ ^ corootPair α (Pi.single j 1)) := by
    intro α β hα hβ horth
    rw [rootWeylSL2_conj_rootDiagUnit S hβ,
      weylTuple_corootTuple_eq_self_of_orthogonal hα hβ horth]
  have h2d : n₂ * d * n₂⁻¹ = d := hfix a b ha hb hab
  have h3d : n₃ * d * n₃⁻¹ = d := hfix a c ha hc hac
  have h1e : n₁ * e * n₁⁻¹ = e := hfix c a hc ha (by rw [iform_comm]; exact hac)
  have h2e : n₂ * e * n₂⁻¹ = e := hfix c b hc hb (by rw [iform_comm]; exact hbc)
  have hmoveg : g * d * g⁻¹ ≠ d := by
    have hEq : g * d * g⁻¹ = n₁ * d * n₁⁻¹ := by
      calc g * d * g⁻¹ = n₁ * (n₂ * d * n₂⁻¹) * n₁⁻¹ := by rw [hg]; group
        _ = n₁ * d * n₁⁻¹ := by rw [h2d]
    rw [hEq]
    exact rootWeylSL2_moves_corootTuple S ha hζ hζ1
  have hmoveh : h * e * h⁻¹ ≠ e := by
    have hEq : h * e * h⁻¹ = n₃ * e * n₃⁻¹ := by
      calc h * e * h⁻¹ = n₃ * (n₂ * e * n₂⁻¹) * n₃⁻¹ := by rw [hh, h23.eq]; group
        _ = n₃ * e * n₃⁻¹ := by rw [h2e]
    rw [hEq]
    exact rootWeylSL2_moves_corootTuple S hc hζ hζ1
  have hfixh : h * d * h⁻¹ = d := by
    calc h * d * h⁻¹ = n₂ * (n₃ * d * n₃⁻¹) * n₂⁻¹ := by rw [hh]; group
      _ = d := by rw [h3d, h2d]
  have hfixg : g * e * g⁻¹ = e := by
    calc g * e * g⁻¹ = n₁ * (n₂ * e * n₂⁻¹) * n₁⁻¹ := by rw [hg]; group
      _ = e := by rw [h2e, h1e]
  have hmovegh : (g * h) * d * (g * h)⁻¹ ≠ d := by
    have hEq : (g * h) * d * (g * h)⁻¹ = g * d * g⁻¹ := by
      calc (g * h) * d * (g * h)⁻¹ = g * (h * d * h⁻¹) * g⁻¹ := by group
        _ = g * d * g⁻¹ := by rw [hfixh]
    rw [hEq]; exact hmoveg
  have hg1 : g ≠ 1 := by intro h1; exact hmoveg (by rw [h1]; group)
  have hh1 : h ≠ 1 := by intro h1; exact hmoveh (by rw [h1]; group)
  have hne : g ≠ h := by intro h1; exact hmoveg (by rw [h1]; exact hfixh)
  exact four_dvd_ggAutomizer_of_coroot_witnesses hgJ hhJ hgN hhN hdA heA
    hg2 hh2 hgh hg1 hh1 hne hmoveg hmoveh hfixh hfixg hmovegh

theorem four_dvd_aut_of_quasisimple_F4 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = -γ) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (ha3 : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hQ : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fullThreeTorus S)) := by
  rcases langRatDetectsTwoF4_class_cases ha3 i with hall | hsix | ⟨e, he, hΨ⟩
  · have ha : a = 1 := by
      funext j
      have h := hall (Pi.single j 1) (isRoot_single Tag.F4 j)
      simpa only [rootChar_single, Pi.one_apply] using h
    exact False.elim (h1 (by rw [ha, rootDiagUnit_one]))
  · have h3L : (3 : L) ≠ 0 := by
      have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
      have h3 : (3 : L) = (2 : L) + 1 := by norm_num
      rw [h3, h2, zero_add]
      exact one_ne_zero
    have hq1 : S.D.q = 2 ^ 1 := by simpa using hq
    have hρ' : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = (-1 : ℤ) • latPerm 1 γ := by
      intro γ hγ
      rw [hρ γ hγ]
      exact (neg_one_smul ℤ (latPerm 1 γ)).symm
    have hsolv : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      isSolvable_rationalComponent_of_latSolv S hq1 Nat.prime_three h3L
        (Equiv.refl _) (-1) (Or.inr rfl) (by rw [hq]; norm_num) hρ' hT ha3 i
        ⟨rfl, Or.inr ⟨by rw [rationalRoots_eq_of_rho_neg S hρ i]; exact hsix.1,
          by intro γ hγ; rfl⟩⟩
    haveI : Group.IsPerfect ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := hQ.1
    haveI : Nontrivial ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact False.elim ((Group.IsPerfect.not_isSolvable
      (G := ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) hsolv)
  · obtain ⟨α, β, γ, u, v, hα, hβ, hγ, hu, hv, hαe, hβe, hγe, hue, hve,
        hαβ, hαγ, hβγ, hswap1, hswap2⟩ := exists_orthogonal_frame_perp_F4 he
    have hmem : ∀ x, IsRoot Tag.F4 x → iform x e = 0 →
        x ∈ componentRoots (rootCharHom a) i := by
      intro x hx hxe
      rw [hΨ]
      exact ⟨hx, hxe⟩
    exact four_dvd_aut_of_perp_frame_F4 S hq hAlg hρ i hα hβ hγ hu hv
      (hmem α hα hαe) (hmem β hβ hβe) (hmem γ hγ hγe)
      (hmem u hu hue) (hmem v hv hve) hαβ hαγ hβγ hswap1 hswap2

end CFSG.StandardType.QTwoCav

end
