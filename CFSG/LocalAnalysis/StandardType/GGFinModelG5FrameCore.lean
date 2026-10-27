module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangSL2
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangDatum

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section FrameCore

private theorem g5_list_prod_ofFn_mul_of_ne {G : Type*} [Group G] :
    ∀ {n : ℕ} (f g : Fin n → G), (∀ i j, i ≠ j → Commute (f i) (g j)) →
      (List.ofFn fun i => f i * g i).prod = (List.ofFn f).prod * (List.ofFn g).prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, g5_list_prod_ofFn_mul_of_ne (fun i => f i.succ) (fun i => g i.succ)
        (fun i j hij => h i.succ j.succ fun e => hij (Fin.succ_injective _ e))]
    have hc : Commute (g 0) (List.ofFn fun i => f i.succ).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact (h i.succ 0 (Fin.succ_ne_zero i)).symm
    rw [mul_assoc, ← mul_assoc (g 0), hc.eq]
    simp only [mul_assoc]

private theorem g5_coe_nSL_one {K : Type} [Field K] :
    ((nSL (1 : Kˣ) : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := by
  simp [nSL]

private theorem g5_map_nSL_one {K : Type} [Field K] (σ : K →+* K) :
    Matrix.SpecialLinearGroup.map σ (nSL (1 : Kˣ)) = nSL (1 : Kˣ) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, g5_coe_nSL_one]
  fin_cases i <;> fin_cases j <;> simp

private theorem g5_list_prod_conj {G : Type*} [Group G] :
    ∀ {m : ℕ} (f : Fin m → G) (a : G) (i : Fin m),
      (∀ j k, j ≠ k → Commute (f j) (f k)) →
      (∀ j, j ≠ i → Commute (f j) a) →
      (List.ofFn f).prod * a * ((List.ofFn f).prod)⁻¹ = f i * a * (f i)⁻¹
  | 0, f, a, i, _, _ => i.elim0
  | n + 1, f, a, ⟨0, _⟩, hpair, ha => by
    rw [List.ofFn_succ, List.prod_cons]
    have hB : Commute (List.ofFn fun j : Fin n => f j.succ).prod a :=
      Commute.list_prod_left _ _ fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact ha j.succ (Fin.succ_ne_zero j)
    have hc : (List.ofFn fun j : Fin n => f j.succ).prod * a *
        ((List.ofFn fun j : Fin n => f j.succ).prod)⁻¹ = a := by
      rw [hB.eq]
      group
    rw [mul_inv_rev,
      show (f 0 * (List.ofFn fun j : Fin n => f j.succ).prod) * a *
          (((List.ofFn fun j : Fin n => f j.succ).prod)⁻¹ * (f 0)⁻¹) =
        f 0 * ((List.ofFn fun j : Fin n => f j.succ).prod * a *
          ((List.ofFn fun j : Fin n => f j.succ).prod)⁻¹) * (f 0)⁻¹ by group,
      hc]
    rfl
  | n + 1, f, a, ⟨i' + 1, hi⟩, hpair, ha => by
    rw [List.ofFn_succ, List.prod_cons]
    have ih := g5_list_prod_conj (fun j : Fin n => f j.succ) a ⟨i', Nat.lt_of_succ_lt_succ hi⟩
      (fun j k hjk => hpair j.succ k.succ fun h => hjk (Fin.succ_inj.mp h))
      (fun j hj => ha j.succ fun h => hj (Fin.succ_inj.mp h))
    have h0i : Commute (f 0) (f (⟨i', Nat.lt_of_succ_lt_succ hi⟩ : Fin n).succ) :=
      hpair 0 _ (by simp)
    have h0a : Commute (f 0) a := ha 0 (by simp)
    have hcomm3 : Commute (f 0) (f (⟨i', Nat.lt_of_succ_lt_succ hi⟩ : Fin n).succ * a *
        (f (⟨i', Nat.lt_of_succ_lt_succ hi⟩ : Fin n).succ)⁻¹) :=
      (h0i.mul_right h0a).mul_right h0i.inv_right
    rw [mul_inv_rev,
      show (f 0 * (List.ofFn fun j : Fin n => f j.succ).prod) * a *
          (((List.ofFn fun j : Fin n => f j.succ).prod)⁻¹ * (f 0)⁻¹) =
        f 0 * ((List.ofFn fun j : Fin n => f j.succ).prod * a *
          ((List.ofFn fun j : Fin n => f j.succ).prod)⁻¹) * (f 0)⁻¹ by group,
      ih]
    rw [show f (⟨i' + 1, hi⟩ : Fin (n + 1)) =
      f (⟨i', Nat.lt_of_succ_lt_succ hi⟩ : Fin n).succ from rfl]
    rw [hcomm3.eq]
    group

private theorem g5_rho_nSL_mem_monomial
    {τ : Tag} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ h : rootSL2 τ GGL γ (nSL (1 : GGLˣ)) ∈ monomialSubgroup τ GGL,
      weylQuotientHom τ GGL ⟨_, h⟩ = rootReflection γ :=
  ((CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ GGL hγ).2.2.2.2.1
    (1 : GGLˣ)).2.2

private theorem g5_list_prod_rho_nSL_mem_monomial
    {τ : Tag} {m : ℕ}
    (γ : Fin m → Fin τ.rank → ℤ) (hγ : ∀ i, IsRoot τ (γ i)) :
    ∃ h : (List.ofFn fun i => rootSL2 τ GGL (γ i) (nSL (1 : GGLˣ))).prod ∈
        monomialSubgroup τ GGL,
      weylQuotientHom τ GGL ⟨_, h⟩ = (List.ofFn fun i => rootReflection (γ i)).prod := by
  choose hm hw using fun i => g5_rho_nSL_mem_monomial (τ := τ) (hγ i)
  set mm : Fin m → monomialSubgroup τ GGL := fun i => ⟨_, hm i⟩ with hmm
  have hcoe : (List.ofFn fun i => rootSL2 τ GGL (γ i) (nSL (1 : GGLˣ))).prod =
      (((List.ofFn mm).prod : monomialSubgroup τ GGL) : ModGL τ GGL) := by
    rw [SubmonoidClass.coe_list_prod, List.map_ofFn]
    rfl
  refine ⟨hcoe ▸ ((List.ofFn mm).prod).2, ?_⟩
  have he : (⟨_, hcoe ▸ ((List.ofFn mm).prod).2⟩ : monomialSubgroup τ GGL) =
      (List.ofFn mm).prod :=
    Subtype.ext hcoe
  rw [he, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hw i))

private theorem g5_rho_nSL_fixed
    {τ : Tag} (σ : GGL →+* GGL) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    Units.map (entrywiseHom σ) (rootSL2 τ GGL γ (nSL (1 : GGLˣ))) =
      rootSL2 τ GGL γ (nSL (1 : GGLˣ)) := by
  rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self σ,
    CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo (K := GGL) (L := GGL) σ hγ,
    g5_map_nSL_one σ]

private theorem g5_canonicalRep_mem_monomialSubgroup
    {τ : Tag} (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) GGL w ∈ monomialSubgroup τ GGL := by
  obtain ⟨ω, hω⟩ := (coxeterSystem τ).wordProd_surjective w
  rw [← hω, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_monomialSubgroup i

private theorem g5_weylQuotientHom_canonicalRep
    {τ : Tag} (w : WeylGroup τ) :
    weylQuotientHom τ GGL
        ⟨canonicalRep (coxeterSystem τ) GGL w, g5_canonicalRep_mem_monomialSubgroup w⟩ = w :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep (R := GGL) w)

private theorem g5_canonicalRep_fixed
    {τ : Tag} (w : WeylGroup τ) :
    Units.map (entrywiseHom (frobenius GGL 2)) (canonicalRep (coxeterSystem τ) GGL w) =
      canonicalRep (coxeterSystem τ) GGL w := by
  obtain ⟨ω, hω⟩ := (coxeterSystem τ).wordProd_surjective w
  rw [← hω, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo,
    map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  show Units.map (entrywiseHom (frobenius GGL 2)) (weylElt τ GGL i 1) = weylElt τ GGL i 1
  rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self (frobenius GGL 2),
    CFSG.RankThree.Chevalley.baseChangeGL_weylElt_one (frobenius GGL 2) i]

private theorem g5_eq_one_of_monomial_of_frob2
    {τ : Tag} {m : ModGL τ GGL}
    (hm : m ∈ monomialSubgroup τ GGL)
    (hρ : weylQuotientHom τ GGL ⟨m, hm⟩ = 1)
    (hφ : Units.map (entrywiseHom (frobenius GGL 2)) m = m) : m = 1 := by
  obtain ⟨w, k, hk, hmk⟩ := monomialSubgroup_le_torusWeylCosets (R := GGL) hm
  have hmaps : MapsRootLines m w := by
    rw [hmk]
    simpa only [one_mul] using
      (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep (R := GGL) w)
  have hw : w = 1 := by
    have h1 : weylQuotientHom τ GGL ⟨m, hm⟩ = w :=
      (mapsRootLines_weylQuotientHom ⟨m, hm⟩).unique hmaps
    rw [← h1, hρ]
  have hmk' : m = k := by rw [hmk, hw, canonicalRep_one, mul_one]
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  have hφa : Units.map (entrywiseHom (frobenius GGL 2))
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a := by
    rw [← ha, ← hmk']
    exact hφ
  have h0 : Units.map (entrywiseHom (frobenius GGL 2))
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ
        fun i => Units.map (frobenius GGL 2).toMonoidHom (a i) :=
    Units.ext (entrywise_rootDiag (frobenius GGL 2) a)
  have hfix : (fun i => Units.map (frobenius GGL 2).toMonoidHom (a i)) = a := by
    apply rootDiagUnit_injective
    rw [← h0, hφa]
  have ha1 : a = 1 := by
    funext i
    have h3 := congrFun hfix i
    have h4 : Units.map (frobenius GGL 2).toMonoidHom (a i) = a i ^ 2 :=
      Units.ext (by simp [frobenius_def])
    rw [h4] at h3
    have h5 : a i * a i = a i * 1 := by rw [mul_one, ← pow_two]; exact h3
    exact mul_left_cancel h5
  rw [hmk', ha, ha1, rootDiagUnit_one]

private theorem g5_list_prod_rho_nSL_eq_canonicalRep
    {τ : Tag} {m : ℕ}
    (γ : Fin m → Fin τ.rank → ℤ) (hγ : ∀ i, IsRoot τ (γ i)) :
    (List.ofFn fun i => rootSL2 τ GGL (γ i) (nSL (1 : GGLˣ))).prod =
      canonicalRep (coxeterSystem τ) GGL (List.ofFn fun i => rootReflection (γ i)).prod := by
  set Nn : ModGL τ GGL := (List.ofFn fun i => rootSL2 τ GGL (γ i) (nSL (1 : GGLˣ))).prod
    with hNndef
  set w : WeylGroup τ := (List.ofFn fun i => rootReflection (γ i)).prod with hwdef
  obtain ⟨hNmono, hNweyl⟩ := g5_list_prod_rho_nSL_mem_monomial γ hγ
  have hCmono : canonicalRep (coxeterSystem τ) GGL w ∈ monomialSubgroup τ GGL :=
    g5_canonicalRep_mem_monomialSubgroup w
  have hCweyl : weylQuotientHom τ GGL ⟨canonicalRep (coxeterSystem τ) GGL w, hCmono⟩ = w :=
    g5_weylQuotientHom_canonicalRep w
  set c : ModGL τ GGL := Nn * (canonicalRep (coxeterSystem τ) GGL w)⁻¹ with hcdef
  have hcmono : c ∈ monomialSubgroup τ GGL := by
    rw [hcdef]
    exact mul_mem hNmono (inv_mem hCmono)
  have hcweyl : weylQuotientHom τ GGL ⟨c, hcmono⟩ = 1 := by
    have h : (⟨c, hcmono⟩ : monomialSubgroup τ GGL) =
        ⟨Nn, hNmono⟩ * (⟨canonicalRep (coxeterSystem τ) GGL w, hCmono⟩ :
          monomialSubgroup τ GGL)⁻¹ :=
      Subtype.ext hcdef
    rw [h, map_mul, map_inv, hNweyl, hCweyl, mul_inv_cancel]
  have hNfix : Units.map (entrywiseHom (frobenius GGL 2)) Nn = Nn := by
    rw [hNndef, map_list_prod, List.map_ofFn]
    exact congrArg List.prod (congrArg List.ofFn
      (funext fun i => g5_rho_nSL_fixed (frobenius GGL 2) (hγ i)))
  have hcfixed : Units.map (entrywiseHom (frobenius GGL 2)) c = c := by
    rw [hcdef, map_mul, map_inv, hNfix, g5_canonicalRep_fixed w]
  have hc1 : c = 1 := g5_eq_one_of_monomial_of_frob2 hcmono hcweyl hcfixed
  rw [hcdef, mul_inv_eq_one] at hc1
  rw [hwdef]
  exact hc1

theorem ggG5_frame_of_prod
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t) (hf : 1 ≤ f) {m : ℕ}
    (β : Fin m → (Fin (ggU (absTag t) 6 f).D.rank → ℤ))
    (hroot : ∀ i, β i ∈ (ggU (absTag t) 6 f).D.roots)
    (hfix : ∀ i, latPerm (piB t p f) (β i) = β i)
    (hgraph : ∀ i, ggGraphLat t (ggLangReidx (rank_eq_langTag f ht) (β i)) =
      ggLangReidx (rank_eq_langTag f ht) (β i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 GGL,
      Commute (rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) (β i)) A)
        (rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) (β j)) B))
    (hlaw : GGWeylLaw t p f ht
      (List.ofFn fun i => rootReflection (ggLangReidx (rank_eq_langTag f ht) (β i))).prod)
    (hrf : ∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm (piB t p f) α = α →
      ∃ i, ∃ u : WeylGroup (langTag t), GGCommPi t p f ht u ∧
        u • ggLangReidx (rank_eq_langTag f ht) (β i) = ggLangReidx (rank_eq_langTag f ht) α)
    (hf5 : ∀ γ : Fin (langTag t).rank → ℤ, IsRoot (langTag t) γ → ggGraphLat t γ = γ →
      ∃ i, ∃ u : WeylGroup (langTag t),
        ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
          canonicalRep (coxeterSystem (langTag t)) GGL u ∧
        u • ggLangReidx (rank_eq_langTag f ht) (β i) = γ) :
    Nonempty (GGLangFrame t p f ht) := by
  classical
  obtain ⟨z, hz⟩ := ggLang_sl2 (f := f) hf
  set r : Fin m → Fin (langTag t).rank → ℤ :=
    fun i => ggLangReidx (rank_eq_langTag f ht) (β i) with hrdef
  have hr : ∀ i, IsRoot (langTag t) (r i) := fun i =>
    (mem_roots_iff_isRoot f ht (β i)).1 (hroot i)
  set g0 : ModGL (langTag t) GGL :=
    (List.ofFn fun i => rootSL2 (langTag t) GGL (r i) z).prod with hg0def
  set Nn : ModGL (langTag t) GGL :=
    (List.ofFn fun i => rootSL2 (langTag t) GGL (r i) (nSL (1 : GGLˣ))).prod with hNndef
  set w : WeylGroup (langTag t) := (List.ofFn fun i => rootReflection (r i)).prod with hwdef
  have hg0mem : g0 ∈ adjointGroup (langTag t) GGL := by
    rw [hg0def]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact rootSL2_mem_adjointGroup (r i) z
  have hPhi : ggPhi t f g0 = g0 * Nn := by
    rw [hg0def, hNndef, map_list_prod, List.map_ofFn]
    have h2 : (List.ofFn (⇑(ggPhi t f) ∘ fun i => rootSL2 (langTag t) GGL (r i) z)) =
        List.ofFn fun i => rootSL2 (langTag t) GGL (r i) z *
          rootSL2 (langTag t) GGL (r i) (nSL (1 : GGLˣ)) := by
      apply congrArg List.ofFn
      funext i
      simp only [Function.comp_apply]
      rw [ggG5_phi_rootSL2 ht f (hr i) (hgraph i) z, hz, map_mul]
    rw [h2, g5_list_prod_ofFn_mul_of_ne _ _
      (fun i j hij => hcomm i j hij z (nSL (1 : GGLˣ)))]
  have hN : Nn = canonicalRep (coxeterSystem (langTag t)) GGL w := by
    rw [hNndef, hwdef]
    exact g5_list_prod_rho_nSL_eq_canonicalRep r hr
  have hlang : ggPhi t f g0 = g0 * canonicalRep (coxeterSystem (langTag t)) GGL w := by
    rw [hPhi, hN]
  obtain ⟨M, _hMw, hMg0⟩ := ggG5_datum_of_lang ht hlaw hg0mem hlang
  refine ⟨{ M := M
            frame := Set.range β
            frame_root := ?_
            frame_fixed := ?_
            frame_graph := ?_
            z := z
            act := ?_
            cover_rf := ?_
            cover_f5 := ?_ }⟩
  · rintro β' ⟨i, rfl⟩
    exact hroot i
  · rintro β' ⟨i, rfl⟩
    exact hfix i
  · rintro β' ⟨i, rfl⟩
    exact hgraph i
  · rintro β' ⟨i, rfl⟩ A
    rw [hMg0, hg0def]
    show (List.ofFn fun j => rootSL2 (langTag t) GGL (r j) z).prod *
        rootSL2 (langTag t) GGL (r i) A *
        ((List.ofFn fun j => rootSL2 (langTag t) GGL (r j) z).prod)⁻¹ =
        rootSL2 (langTag t) GGL (r i) (z * A * z⁻¹)
    rw [g5_list_prod_conj _ _ i (fun j k _ => hcomm j k ‹_› z z)
      (fun j hj => hcomm j i hj z A), map_mul, map_mul, map_inv]
  · intro α hα hαfix
    obtain ⟨i, u, hu, hiu⟩ := hrf α hα hαfix
    exact ⟨β i, ⟨i, rfl⟩, u, hu, hiu⟩
  · intro γ hγ hgγ
    obtain ⟨i, u, hu, hiu⟩ := hf5 γ hγ hgγ
    exact ⟨β i, ⟨i, rfl⟩, u, hu, hiu⟩

end FrameCore

end CFSG.StandardType.GGFinModel.G5
