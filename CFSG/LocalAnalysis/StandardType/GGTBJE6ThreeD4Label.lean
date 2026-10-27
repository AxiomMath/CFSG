module

public import CFSG.LocalAnalysis.StandardType.GGTBJXClass
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeD4Roots
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeD4RatLabel
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableCRes

private abbrev e6D4Nodes : Set (Fin Tag.E6.rank) :=
  {j | j ∉ ({0, 5} : Finset (Fin Tag.E6.rank))}

theorem e6D4_ne_one_of_class
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (i : KernelComponent (rootCharHom a))
    (hD4 : ∃ v : WeylGroup .E6, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) :
    a ≠ 1 := by
  rintro rfl
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup .E6, componentRoots (rootCharHom (1 : Fin Tag.E6.rank → Kˣ)) i =
      (fun α => v • α) '' parabolicRoots .E6 e6D4Nodes := hD4
  let e2 : Fin Tag.E6.rank → ℤ := Pi.single 2 1
  let e0 : Fin Tag.E6.rank → ℤ := Pi.single 0 1
  have he2 : e2 ∈ parabolicRoots Tag.E6 e6D4Nodes := ⟨IsRoot.basis 2, by decide⟩
  have hker : ∀ w : WeylGroup Tag.E6, ∀ j : Fin Tag.E6.rank,
      w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
        kernelRoots (rootCharHom (1 : Fin Tag.E6.rank → Kˣ)) :=
    fun w j => ⟨isRoot_iff_exists_smul_single.2 ⟨w, j, rfl⟩, by
      change rootChar (1 : Fin Tag.E6.rank → Kˣ) _ = 1
      simp [rootChar]⟩
  have hα : v • e2 ∈ componentRoots (rootCharHom (1 : Fin Tag.E6.rank → Kˣ)) i := by
    rw [hv]
    exact ⟨e2, he2, rfl⟩
  obtain ⟨_, hcls⟩ := hα
  have hne : CFSG.LieType.Steinberg.Adjoint.iform (v • e2) (v • e0) ≠ 0 := by
    rw [CFSG.LieType.Chevalley.iform_smul]
    decide +kernel
  have hβ : v • e0 ∈ componentRoots (rootCharHom (1 : Fin Tag.E6.rank → Kˣ)) i :=
    ⟨hker v 0, by
      rw [← hcls]
      exact (mk_eq_of_iform_ne_zero (α := ⟨v • e2, hker v 2⟩) (β := ⟨v • e0, hker v 0⟩) hne).symm⟩
  rw [hv] at hβ
  obtain ⟨δ, hδ, hδe⟩ := hβ
  have hδ0 : δ = e0 := MulAction.injective v hδe
  have h0 := hδ.2 0 (by decide)
  rw [hδ0] at h0
  simp [e0] at h0


theorem e6Split_setup {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure K) 5, (∀ α, S.ρ α = α) ∧
      S.Γ = (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ∧
      ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
        rootDiagUnit Tag.E6 a ∈ S.D.torus := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  set L := AlgebraicClosure K with hL
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hfne : (f : ℕ) ≠ 0 := f.pos.ne'
  haveI hcharL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ c : L, Fr c = c ^ 2 ^ (f : ℕ) := fun c => iterateFrobenius_def 2 f c
  let D : LangDatum Tag.E6 L :=
    LangDatum.ofFrobenius (τ := Tag.E6) Fr (2 ^ (f : ℕ)) hFr (1 : WeylGroup Tag.E6)
      (one_mem _) (by simp [canonicalRep_one])
  have hn1c : D.n = canonicalRep (coxeterSystem Tag.E6) L (1 : WeylGroup Tag.E6) := rfl
  have hDn : D.n = (1 : ModGL Tag.E6 L) := by
    rw [hn1c]
    exact canonicalRep_one (coxeterSystem Tag.E6) L
  have hDg0 : D.g0 = 1 := rfl
  have hDΦ : D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (by positivity : 0 < 2 ^ (f : ℕ))
    exact ⟨x, by rw [hFr, hx]⟩
  have hρ : FrobRootMap D (Equiv.refl (Fin Tag.E6.rank → ℤ)) :=
    { isRoot_iff := fun γ => Iff.rfl
      neg_eq := fun γ => rfl
      iform_eq := fun γ δ => rfl
      map_rootSubgroup := fun γ hγ => by
        have h := LangDatum.map_step_rootSubgroup (D := D) hsurj hDΦ
          (w := (1 : WeylGroup Tag.E6)) hn1c hγ
        simpa using h
      rootChar_eq := fun a ha γ hγ => by
        have h1 : D.Φ (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a := by
          have h := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ha).2
          rwa [hDn, one_mul, inv_one, mul_one] at h
        have h2 : Units.map (entrywiseHom Fr) (rootDiagUnit Tag.E6 a) =
            rootDiagUnit Tag.E6 a := by
          rw [← hDΦ]; exact h1
        have h3 : (fun i => Units.map Fr.toMonoidHom (a i)) = a := by
          apply CFSG.LieType.Chevalley.rootDiagUnit_injective
          rw [← units_map_entrywiseHom_rootDiagUnit Fr a, h2]
        have h5 : Units.map Fr.toMonoidHom (rootChar a γ) = rootChar a γ := by
          rw [units_map_rootChar, h3]
        have h6 : Units.map Fr.toMonoidHom (rootChar a γ) = rootChar a γ ^ D.q := by
          change Units.map Fr.toMonoidHom (rootChar a γ) = rootChar a γ ^ 2 ^ (f : ℕ)
          ext
          simp [hFr]
        exact h5.symm.trans h6 }
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    constructor
    · change IsPrimePow (2 ^ (f : ℕ))
      exact Nat.prime_two.isPrimePow.pow hfne
    · change (((2 ^ (f : ℕ) : ℕ)) : L) = 0
      exact (CharP.cast_eq_zero_iff L 2 (2 ^ (f : ℕ))).2 (dvd_pow_self 2 hfne)
  have hpq : ¬ 5 ∣ D.q := by
    change ¬ (5 : ℕ) ∣ 2 ^ (f : ℕ)
    intro h
    have h52 : (5 : ℕ) ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
    norm_num at h52
  have hperf : commutator ↥(adjointGroup Tag.E6 K) = ⊤ :=
    single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  have hFrK : ∀ c : L, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]; exact hFr c
  let ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E6 K).subtype
  have hrange : ι.range = (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hdesc : LangDescent D 5 ι :=
    langDescent_untw (K := K) (L := L) 3 (Or.inl ⟨rfl, rfl⟩) hFrK D hDΦ
      Nat.prime_five (by norm_num) hperf
  have hfin : Finite D.model := hdesc.finite_model
  let S : LangSetup Tag.E6 L 5 :=
    D.toSetup 5 (Equiv.refl _) hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hfin
  have hmodel : D.model = D.fix := by
    ext y
    rw [LangDatum.mem_model, LangDatum.mem_fix]
    constructor
    · rintro ⟨hy, hf⟩
      exact ⟨hy, by simpa [hDn] using hf⟩
    · rintro ⟨hy, hf⟩
      exact ⟨hy, by simpa [hDn] using hf⟩
  have hΓ_eq : S.Γ = ι.range := by
    change ⁅D.model, D.model⁆ = ι.range
    rw [hmodel]
    exact hdesc.derived
  have hpow : ∀ x : Lˣ, x ^ 3 = 1 → x ^ (2 ^ (f : ℕ)) = x := by
    intro x hx
    have h1 : 1 ≤ 2 ^ (f : ℕ) := Nat.one_le_two_pow
    rw [hK] at h3
    obtain ⟨k, hk⟩ := h3
    have hpow : 2 ^ (f : ℕ) = 3 * k + 1 := by omega
    rw [hpow, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
  refine ⟨S, fun α => rfl, hΓ_eq.trans hrange, fun a ha => ?_⟩
  change rootDiagUnit Tag.E6 a ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf D.n D.Φ
  rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
  refine ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
  rw [hDn, hDΦ]
  simp only [one_mul, inv_one, mul_one]
  rw [units_map_entrywiseHom_rootDiagUnit Fr a]
  congr 1
  funext i
  apply Units.ext
  change Fr (a i : L) = (a i : L)
  rw [hFr]
  exact congrArg (fun u : Lˣ => (u : L)) (hpow (a i) (ha i))



theorem e6D4_label_of_class
    {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL Tag.E6 K}
    (hker : ψ.ker ≤ Subgroup.center L') (hψ : ψ.range = adjointGroup Tag.E6 K)
    (a : Fin Tag.E6.rank → Kˣ) (hapK : ∀ j, a j ^ 3 = 1) (y : MulAut L')
    (hy : ∀ l, ψ (y l) = rootDiagUnit Tag.E6 a * ψ l * (rootDiagUnit Tag.E6 a)⁻¹)
    {J : Subgroup L'} (hJ : IsComponentOf J (fixSubgroup y))
    (i : KernelComponent (rootCharHom a))
    (hJi : J.map ψ = componentRootSpan K (rootCharHom a) i)
    (hD4 : ∃ v : WeylGroup .E6, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) :
    ∃ m : ℕ, 1 ≤ m ∧ GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hρ, hSΓ, hT3⟩ := e6Split_setup h3
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  haveI : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  have hJo : CFSG.Open.IsComponentOf J (fixSubgroup y) := isComponentOf_iff_open.1 hJ
  let a' : Fin Tag.E6.rank → Lˣ := fun j => Units.map ι.toMonoidHom (a j)
  have hbd : baseChangeGL ι (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a' :=
    baseChangeGL_rootDiagUnit ι a
  let d : ModGL Tag.E6 L := rootDiagUnit Tag.E6 a'
  let ψ' : L' →* ModGL Tag.E6 L := (baseChangeGL ι).comp ψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := fun l hl => hker (by
    rw [MonoidHom.mem_ker] at hl ⊢
    exact baseChangeGL_injective (f := ι) (hl.trans (map_one _).symm))
  have hrange : ψ'.range = S.Γ := by
    rw [hSΓ, ← hψ]
    exact MonoidHom.range_comp (baseChangeGL ι) ψ
  have hyd : ∀ l, ψ' (y l) = d * ψ' l * d⁻¹ := fun l => by
    change baseChangeGL ι (ψ (y l)) = _
    rw [hy l, map_mul, map_mul, map_inv, hbd]
    rfl
  have hap : ∀ j, a' j ^ 3 = 1 := fun j => by
    change (Units.map ι.toMonoidHom (a j)) ^ 3 = 1
    rw [← map_pow, hapK j, map_one]
  have hdT : d ∈ S.D.torus := hT3 a' hap
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    omega
  have hd1 : d ≠ 1 := by
    intro h
    have h1 : a' = 1 :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective
        (h.trans CFSG.LieType.Chevalley.rootDiagUnit_one.symm)
    apply e6D4_ne_one_of_class a i hD4
    funext j
    have h2 : Units.map ι.toMonoidHom (a j) = 1 := congrFun h1 j
    exact (Units.map_injective ι.injective) (h2.trans (map_one _).symm)
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJo.2.2.1⟩
  have hJperf : ⁅J.map ψ', J.map ψ'⁆ = J.map ψ' := by
    rw [← Subgroup.map_commutator, hJp]
  have hJnt : J.map ψ' ≠ ⊥ := by
    intro hbot
    have hJker : J ≤ ψ'.ker := by
      intro x hx
      have : ψ' x ∈ J.map ψ' := Subgroup.mem_map_of_mem ψ' hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    haveI : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial hJo.2.2
    have hJcomm : ⁅J, J⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx z hz
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 (hker' (hJker hz)) x
    rw [hJp] at hJcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : J)
    exact hx (Subtype.ext (by
      have : (x : L') ∈ (⊥ : Subgroup L') := hJcomm ▸ x.2
      simpa using this))
  have hCX : ∀ c ∈ fixSubgroup y, ψ' c ∈ S.Γ ⊓ Subgroup.centralizer {d} := by
    intro c hc
    refine ⟨hrange ▸ ⟨c, rfl⟩, ?_⟩
    show ψ' c ∈ Subgroup.centralizer {d}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hyd c
    rw [mem_fixSubgroup.mp hc] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
  have hJX : J.map ψ' ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCX x (hJo.1 hx)
  have hJle := LangRat.perfect_le_iSup_rationalComponent_of_ne_G2 S (fun h => by cases h)
    Nat.prime_three hpL hdT hap hd1 (J.map ψ') hJX hJperf
  obtain ⟨i', hqi, hmap⟩ : ∃ i' : KernelComponent (rootCharHom a'),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a') i') ∧
        J.map ψ' = rationalComponent S.ρ S.Γ (rootCharHom a') i' := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ i' : KernelComponent (rootCharHom a'),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a') i') →
          rationalComponent S.ρ S.Γ (rootCharHom a') i' ≤
            Subgroup.centralizer (J.map ψ' : Set (ModGL Tag.E6 L)) := by
      intro i' hqi
      have hS := CFSG.HardMathSupport.Dickson.Sec6.isComponentOf_rationalComponent S hdT i' hqi
      obtain ⟨Q, hQ, hQmap⟩ := ggTBJ_exists_component_lift_fix ψ' hker' y d hyd hS
        (hS.1.trans (inf_le_left.trans hrange.ge)) (hS.1.trans inf_le_right) hCX
      have hJQ : J ≠ Q := fun h => hcon i' hqi (by rw [h, hQmap])
      have hc : ⁅J, Q⁆ = ⊥ :=
        (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ
          (isComponentOf_iff_open.2 hQ)).resolve_left hJQ
      rw [← hQmap, ← Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.map_commutator,
        Subgroup.commutator_comm, hc, Subgroup.map_bot]
    have hab : ⁅J.map ψ', J.map ψ'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2
        (hJle.trans (iSup_le fun i' => iSup_le fun hi' => hcomm i' hi'))
    exact hJnt (hJperf.symm.trans hab)
  have hkr : kernelRoots (rootCharHom a) = kernelRoots (rootCharHom a') := by
    ext γ
    simp only [kernelRoots_rootCharHom, Set.mem_setOf_eq]
    refine and_congr_right fun _ => ?_
    have h1 : rootChar a' γ = Units.map ι.toMonoidHom (rootChar a γ) := by
      simp [a', rootChar, map_prod, map_zpow]
    rw [h1]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      exact (Units.map_injective ι.injective) (h.trans (map_one _).symm)
  obtain ⟨i'', hi''⟩ := TableCRes.exists_componentRoots_eq hkr i
  have hii : i' = i'' := by
    by_contra hne
    have hRi' : J.map ψ' ≤ componentRootSpan L (rootCharHom a') i' := by
      rw [hmap]
      refine (Subgroup.commutator_le_self _).trans (inf_le_left.trans ?_)
      change rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a') i') ≤ rootSpan Tag.E6 L _
      refine le_of_eq (congrArg (rootSpan Tag.E6 L) ?_)
      ext γ
      constructor
      · rintro ⟨k, δ, hδ, rfl⟩
        rwa [Function.iterate_fixed (hρ δ) k]
      · intro hγ
        exact ⟨0, γ, hγ, rfl⟩
    have hRi'' : J.map ψ' ≤ componentRootSpan L (rootCharHom a') i'' := by
      rw [show J.map ψ' = (J.map ψ).map (baseChangeGL ι) from (Subgroup.map_map _ _ _).symm, hJi]
      refine (map_baseChangeGL_rootSpan_le ι _).trans (le_of_eq (congrArg (rootSpan Tag.E6 L) ?_))
      exact hi''
    have hab : ⁅J.map ψ', J.map ψ'⁆ = ⊥ :=
      eq_bot_iff.2 ((Subgroup.commutator_mono hRi' hRi'').trans
        (commutator_componentRootSpan_eq_bot L hne).le)
    exact hJnt (hJperf.symm.trans hab)
  subst hii
  have hD4' : ∃ v : WeylGroup Tag.E6, componentRoots (rootCharHom a') i' =
      (fun α => v • α) '' parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))} := by
    obtain ⟨v, hv⟩ := hD4
    exact ⟨v, hi''.symm.trans hv⟩
  have hkind : twistKindOf S.ρ (componentRoots (rootCharHom a') i') = TwistKind.inner :=
    twistKindOf_id_eq_inner S.ρ hρ _
  obtain ⟨m, hm1, hlab⟩ := e6D4_label_of_rationalComponent (p₀ := 5) (p := 3) S Nat.prime_three
    (by norm_num) hdT hap i' hqi hD4' hkind
  let f : ↥J →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a') i') :=
    (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (ψ'.subgroupMap J)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (ψ'.subgroupMap_surjective J)
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hx1 : ψ' (x : L') = 1 := by
      have h1 : (MulEquiv.subgroupCongr hmap) (ψ'.subgroupMap J x) = 1 := hx
      have h2 : ψ'.subgroupMap J x = 1 := (MulEquiv.subgroupCongr hmap).map_eq_one_iff.1 h1
      exact congrArg Subtype.val h2
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker' hx1) (z : L'))
  haveI : Group.IsPerfect ↥J := ⟨hJo.2.2.1⟩
  exact ⟨m, hm1, ggHasLabel_quotCenter_of_central_cover inferInstance f hf hfker hlab⟩

theorem ggTBJE6Three_d4Label_of_class
    {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL Tag.E6 K}
    (hker : ψ.ker ≤ Subgroup.center L') (hψ : ψ.range = adjointGroup Tag.E6 K)
    (x : Fin Tag.E6.rank → ZMod 3) (y : MulAut L')
    (hy : ∀ l, ψ (y l) = rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * ψ l *
      (rootDiagUnit Tag.E6 (zetaVec ζ hζ x))⁻¹)
    {J : Subgroup L'} (hJ : IsComponentOf J (fixSubgroup y))
    (i : KernelComponent (rootCharHom (zetaVec ζ hζ x)))
    (hJi : J.map ψ = componentRootSpan K (rootCharHom (zetaVec ζ hζ x)) i)
    (hD4 : ∃ v : WeylGroup .E6, componentRoots (rootCharHom (zetaVec ζ hζ x)) i =
      (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) :
    ∃ m : ℕ, 1 ≤ m ∧ GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h3 : 3 ∣ Nat.card K - 1 := by
    have h1 : orderOf ζ ∣ Fintype.card Kˣ := orderOf_dvd_card
    rw [hζo, Fintype.card_units] at h1
    rwa [Nat.card_eq_fintype_card]
  exact e6D4_label_of_class h3 hker hψ (zetaVec ζ hζ x)
    (fun j => by
      rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]) y hy hJ i hJi hD4

end CFSG.StandardType

end
