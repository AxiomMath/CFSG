module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGKGOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgF4
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KE CFSG.ComponentClassification.CatLeafProof
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem kgf_b3_cands_card :
    ((Tag.F4.artifactRoots.toFinset).filter (fun l : List ℤ =>
      ∀ j : Fin 3, iform (τ := Tag.F4) (fun k : Fin (Tag.rank .F4) => l.getD k 0)
        (Pi.single (b3Node j) 1 : Fin (Tag.rank .F4) → ℤ) = 0)).card ≤ 2 := by
  decide +kernel

private theorem kgf_c3_cands_card :
    ((Tag.F4.artifactRoots.toFinset).filter (fun l : List ℤ =>
      ∀ j : Fin 3, iform (τ := Tag.F4) (fun k : Fin (Tag.rank .F4) => l.getD k 0)
        (Pi.single (c3Node j) 1 : Fin (Tag.rank .F4) → ℤ) = 0)).card ≤ 2 := by
  decide +kernel

private theorem kgf_orth_le_two {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = f4LeviC3) :
    ∀ s : Finset (Fin (Tag.rank .F4) → ℤ),
      (∀ β ∈ s, IsRoot Tag.F4 β ∧ ∀ α ∈ parabolicRoots Tag.F4 J, iform β α = 0) →
      s.card ≤ 2 := by
  rcases hJ with rfl | rfl
  · intro s hs
    let cands : Finset (List ℤ) := (Tag.F4.artifactRoots.toFinset).filter (fun l : List ℤ =>
      ∀ j : Fin 3, iform (τ := Tag.F4) (fun k : Fin (Tag.rank .F4) => l.getD k 0)
        (Pi.single (b3Node j) 1 : Fin (Tag.rank .F4) → ℤ) = 0)
    have hb : cands.card ≤ 2 := by
      dsimp only [cands]
      exact kgf_b3_cands_card
    have hsub : s.image List.ofFn ⊆ cands := by
      intro l hl
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hl
      rw [Finset.mem_filter]
      refine ⟨List.mem_toFinset.2 ((isRoot_iff_mem_artifactRoots (τ := Tag.F4)).1
        (hs β hβ).1), ?_⟩
      intro j
      have hfun : (fun k : Fin (Tag.rank .F4) => (List.ofFn β).getD k 0) = β := by
        funext k
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]
      rw [hfun]
      exact (hs β hβ).2 _ (single_mem_parabolicRoots (A := f4LeviB3) (i := b3Node j) ⟨j, rfl⟩)
    calc s.card = (s.image List.ofFn).card :=
          (Finset.card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ cands.card := Finset.card_le_card hsub
      _ ≤ 2 := hb
  · intro s hs
    let cands : Finset (List ℤ) := (Tag.F4.artifactRoots.toFinset).filter (fun l : List ℤ =>
      ∀ j : Fin 3, iform (τ := Tag.F4) (fun k : Fin (Tag.rank .F4) => l.getD k 0)
        (Pi.single (c3Node j) 1 : Fin (Tag.rank .F4) → ℤ) = 0)
    have hb : cands.card ≤ 2 := by
      dsimp only [cands]
      exact kgf_c3_cands_card
    have hsub : s.image List.ofFn ⊆ cands := by
      intro l hl
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hl
      rw [Finset.mem_filter]
      refine ⟨List.mem_toFinset.2 ((isRoot_iff_mem_artifactRoots (τ := Tag.F4)).1
        (hs β hβ).1), ?_⟩
      intro j
      have hfun : (fun k : Fin (Tag.rank .F4) => (List.ofFn β).getD k 0) = β := by
        funext k
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]
      rw [hfun]
      exact (hs β hβ).2 _ (single_mem_parabolicRoots (A := f4LeviC3) (i := c3Node j) ⟨j, rfl⟩)
    calc s.card = (s.image List.ofFn).card :=
          (Finset.card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ cands.card := Finset.card_le_card hsub
      _ ≤ 2 := hb

private theorem kgf_big {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = f4LeviC3) :
    ∃ s : Finset (Fin (Tag.rank .F4) → ℤ),
      (∀ α ∈ s, α ∈ parabolicRoots Tag.F4 J) ∧ 2 < s.card := by
  rcases hJ with rfl | rfl
  · refine ⟨{Pi.single (b3Node 0) 1, Pi.single (b3Node 1) 1, Pi.single (b3Node 2) 1}, ?_, by decide⟩
    intro α hα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl
    · exact single_mem_parabolicRoots (A := f4LeviB3) (i := b3Node 0) ⟨0, rfl⟩
    · exact single_mem_parabolicRoots (A := f4LeviB3) (i := b3Node 1) ⟨1, rfl⟩
    · exact single_mem_parabolicRoots (A := f4LeviB3) (i := b3Node 2) ⟨2, rfl⟩
  · refine ⟨{Pi.single (c3Node 0) 1, Pi.single (c3Node 1) 1, Pi.single (c3Node 2) 1}, ?_, by decide⟩
    intro α hα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl
    · exact single_mem_parabolicRoots (A := f4LeviC3) (i := c3Node 0) ⟨0, rfl⟩
    · exact single_mem_parabolicRoots (A := f4LeviC3) (i := c3Node 1) ⟨1, rfl⟩
    · exact single_mem_parabolicRoots (A := f4LeviC3) (i := c3Node 2) ⟨2, rfl⟩

private theorem kgf_rho_mem
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin (Tag.rank .F4) → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.F4 J) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
  S.rho_mem_componentRootsT hT i v hroots (N := 2) (kgf_orth_le_two hJ) (kgf_big hJ)

private theorem kgf_orbitLength_eq_one
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin (Tag.rank .F4) → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.F4 J) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  have hρ := kgf_rho_mem S hT i v hJ hroots
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.F4).subset fun γ hγ => hγ.1.1
  exact componentOrbitLength_eq_one hfin hρ


private theorem kgf_quotSp_iso
    {m f : ℕ} {K : Type} [Field K] [Finite K]
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ f) (hne : ¬(m = 2 ∧ Nat.card K = 2))
    {X : Type} [Group X] (g : StatedSp m K →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (StatedSp m K)) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSp m K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hne' : (m, Fintype.card K) ≠ (2, 2) := fun h =>
    hne ⟨(Prod.mk.inj h).1, by rw [Nat.card_eq_fintype_card]; exact (Prod.mk.inj h).2⟩
  have hSpPerf : commutator (StatedSp m K) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds K m hm hne').perfect
  obtain ⟨e₁⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective hSpPerf g hg hker
  have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
    (s := m) hm hne hchar (MulEquiv.refl _)
  exact ⟨e₁.trans e₂⟩

private theorem kgf_adjoint
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKn : Nat.card K = 2 ^ n)
    {β : MulAut ↥(adjointGroup .F4 K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup .F4 K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup .F4 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) {k f : ℕ} (hk : 3 ≤ k)
    (hClab : GGHasLabel ⟨.C, k, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    k = 3 ∧ f = n := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_F4
      β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨fld, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hKfld : Nat.card K = ringChar K ^ (fld : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hKfld ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ fld.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hKfld ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hKfld]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .F4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ := single_edge_perfect .F4 K (by simp)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := .F4) (Or.inr (Or.inl rfl)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : Tag.F4 = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h => absurd h (by decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let R := ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
  let eJ : ↥J ≃* R := (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  haveI : CharP (AlgebraicClosure K) 2 := ringChar.of_eq hch
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hpLp : ringChar (AlgebraicClosure K) ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  let eJQ : ↥J ⧸ Subgroup.center ↥J ≃* R ⧸ Subgroup.center R :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨ν, fA, -, -, -, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model S hp hT hap h1 i
        hA hqs
    rw [hch] at hmodel
    rcases hmodel with hM | hM
    · exact (kg_false_of_psl hk hClab
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJQ.symm hM)).elim
    · exact (kg_false_of_psu hk hClab
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJQ.symm hM)).elim
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin (Tag.rank .F4) → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hA with ⟨v, hroots, -, -⟩ |
        ⟨v, Jc, hJc, hroots, -, -⟩
      · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
        · obtain ⟨K', hfin, hcard, g, hg, hker⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_exists_spSurj S hT i hinner (m := 2)
              (fun K' hfin' hcardK' => by
                haveI := hfin'
                haveI : Fintype ↥K' := Fintype.ofFinite _
                obtain ⟨hch', f', -, hKf', -, h4'⟩ :=
                  CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_subfield_params (m := 2) K'
                    (by norm_num) hcardK' (fun _ => hQ)
                haveI := hch'
                have hne2' : (2, Fintype.card ↥K') ≠ (2, 2) := by
                  intro hh
                  have h2 : Nat.card ↥K' = 2 := by
                    rw [Nat.card_eq_fintype_card]; exact (Prod.mk.inj hh).2
                  have h3 : 3 ≤ Nat.card ↥K' := by rw [hcardK']; exact hQ
                  omega
                refine ⟨(CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
                  ↥K' 2 (by norm_num) hne2').perfect, ?_⟩
                obtain ⟨Ψ, hΨk, hΨr⟩ :=
                  CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_cover_B2 (h4' rfl)
                obtain ⟨Ψ', hk', hr'⟩ :=
                  CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_spRange_smul v hΨk hΨr
                refine ⟨Ψ', hk', ?_⟩
                rw [hr']
                show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
                rw [hroots])
          haveI := hfin
          obtain ⟨hch', f', -, hKf', -, -⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_subfield_params (m := 2) K'
              (by norm_num) hcard (fun _ => hQ)
          haveI : Fintype ↥K' := Fintype.ofFinite _
          haveI := hch'
          have hne2 : ¬(2 = 2 ∧ Nat.card ↥K' = 2) := by
            rintro ⟨-, h2⟩
            have h3 : 3 ≤ Nat.card ↥K' := by rw [hcard]; exact hQ
            omega
          obtain ⟨φR⟩ := kgf_quotSp_iso (m := 2) (f := f') (by norm_num) hKf' hne2 g hg hker
          obtain ⟨h2k, -⟩ := kg_sp_of_quot_sp (E := ↥K') (s := 2) (k := f') (by norm_num) hKf'
            hne2 (eJQ.trans φR) hk hClab
          omega
        · obtain ⟨K', hfin, hK2', ⟨eR⟩⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_sp42_equiv_rationalComponent S hT i v
              hroots hinner (not_le.1 hQ) hqs
          haveI := hfin
          have hcardR : Nat.card (R ⧸ Subgroup.center R) = 360 :=
            CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.card_quot_center_eq_360_of_sp42 hK2' eR
          have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
            rw [Nat.card_congr eJQ.toEquiv, hcardR]
          have hf1 : 1 ≤ f := (kg_inLambda2_C hk hClab).1
          have hformula := kg_card_BC (kg_inLambda2_C hk hClab) (Or.inr rfl) hClab
          rw [hcardJ] at hformula
          have hfac : 512 ≤ 2 ^ (f * k ^ 2) := by
            have hk2 : 9 ≤ k ^ 2 := by nlinarith [hk]
            have h9 : 9 ≤ f * k ^ 2 := by
              calc 9 = 1 * 9 := by norm_num
                _ ≤ f * k ^ 2 := Nat.mul_le_mul hf1 hk2
            have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) h9
            simpa using this
          have hprod : 1 ≤ ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * f * i) - 1) := by
            apply Finset.one_le_prod
            intro i hi
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hpos : 1 ≤ 2 * f * i := by nlinarith
            have h2 : 2 ≤ 2 ^ (2 * f * i) := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (2 * f * i) := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hpos
            omega
          have h512 : 512 ≤ 2 ^ (f * k ^ 2) *
              ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * f * i) - 1) :=
            le_trans hfac (by simpa using Nat.mul_le_mul_left (2 ^ (f * k ^ 2)) hprod)
          have : 512 ≤ 360 := by rw [hformula]; exact h512
          omega
      · obtain ⟨K', hfin, hcard, g, hg, hker⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_exists_spSurj S hT i hinner (m := 3)
            (fun K' hfin' hcardK' => by
              haveI := hfin'
              haveI : Fintype ↥K' := Fintype.ofFinite _
              obtain ⟨hch', f', hf', hKf', -, -⟩ :=
                CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_subfield_params (m := 3) K'
                  (by norm_num) hcardK' (fun h => absurd h (by decide))
              haveI := hch'
              have hne3' : (3, Fintype.card ↥K') ≠ (2, 2) := by
                intro hh; exact absurd (Prod.mk.inj hh).1 (by decide)
              refine ⟨(CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
                ↥K' 3 (by norm_num) hne3').perfect, ?_⟩
              obtain ⟨Ψ, hΨk, hΨr⟩ :=
                CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_cover_levi hJc hf' hKf'
              obtain ⟨Ψ', hk', hr'⟩ :=
                CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_spRange_smul v hΨk hΨr
              refine ⟨Ψ', hk', ?_⟩
              rw [hr']
              show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
              rw [hroots])
        haveI := hfin
        obtain ⟨hch', f', hf', hKf', -, -⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.K155X.l154f4_subfield_params (m := 3) K'
            (by norm_num) hcard (fun h => absurd h (by decide))
        haveI : Fintype ↥K' := Fintype.ofFinite _
        haveI := hch'
        have hne3 : ¬(3 = 2 ∧ Nat.card ↥K' = 2) := by
          rintro ⟨h, -⟩; exact absurd h (by decide)
        obtain ⟨φR⟩ := kgf_quotSp_iso (m := 3) (f := f') (by norm_num) hKf' hne3 g hg hker
        obtain ⟨hmk, hkf⟩ := kg_sp_of_quot_sp (E := ↥K') (s := 3) (k := f') (by norm_num) hKf'
          hne3 (eJQ.trans φR) hk hClab
        have hs1 := kgf_orbitLength_eq_one S hT i v hJc hroots
        have hpow : 2 ^ f' =
            2 ^ (n * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
          rw [← hKf', hcard, hSq, hKn, pow_mul]
        have hfs : f' = n * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
          Nat.pow_right_injective (show 2 ≤ 2 by norm_num) hpow
        exact ⟨hmk.symm, by rw [← hkf, hfs, hs1, mul_one]⟩
    · rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨-, -, -, -, hr, hn⟩
      · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
      · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim

theorem kgExcF4_holds :
    KGSimpleOn FamExcF4 := by
  intro p hp hp2 S _ _ lab α K hFam hΛ hcen hin hαp hα1 hcomp k f hk hC
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hαmem : α ∈ innAutDerived S :=
    CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc hcen
      (Or.inl hFam) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := lab
  have htag : t = .F4 := hFam
  subst htag
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .F4 0 2 n := hM
  obtain ⟨-, Kf, _, _, hKf, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  have hZ : Subgroup.center ↥(adjointGroup .F4 Kf) = ⊥ := center_adjointGroup_eq_bot
  let ψ : S ≃* ↥(adjointGroup .F4 Kf) :=
    (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
      (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have hKf2 : ringChar Kf = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hKf
    exact ringChar.eq Kf 2
  have hα'mem : MulAut.congr ψ α ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hαmem
  have hα'p : (MulAut.congr ψ α) ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hα'1 : MulAut.congr ψ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hcomp_fix : CFSG.Assembly.IsComponentOf K (fixSubgroup α) := by
    rwa [CFSG.StandardType.TCJ.tcj_ggFixSub_eq_fixSubgroup] at hcomp
  have hcomp_open : CFSG.Open.IsComponentOf K (fixSubgroup α) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hcomp_fix
  have hcomp' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport ψ α hcomp_open
  let eKm : ↥K ≃* ↥(K.map ψ.toMonoidHom) := K.equivMapOfInjective ψ.toMonoidHom ψ.injective
  let eQ : ↥K ⧸ Subgroup.center ↥K ≃*
      ↥(K.map ψ.toMonoidHom) ⧸ Subgroup.center ↥(K.map ψ.toMonoidHom) :=
    QuotientGroup.congr _ _ eKm (Subgroup.map_center_eq eKm)
  have hC' : GGHasLabel ⟨.C, k, f⟩
      (↥(K.map ψ.toMonoidHom) ⧸ Subgroup.center ↥(K.map ψ.toMonoidHom)) :=
    CFSG.StandardType.ggHasLabel_of_mulEquiv eQ hC
  obtain ⟨hk3, hfn⟩ := kgf_adjoint hKf2 hp hp2 hKf hα'mem hα'p hα'1 hcomp' hk hC'
  exact Or.inr ⟨hk3, rfl, hfn.symm⟩

end CFSG.StandardType.KG
