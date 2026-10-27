module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagLie
public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagE6
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeSetupTwPlus
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextToralAux2
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeToralityA5
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeWeylGood
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.StandardType.Q1TwE6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem componentMarking_of_model_innerDiag
    {L : Type} [Field L]
    {C : Type} [Group C] (ψ : C →* ModGL Tag.E6 L)
    (hψinj : Function.Injective ψ)
    {A : Subgroup (MulAut C)} (ρ : A →* ModGL Tag.E6 L)
    (hρint : ∀ (a : A) (c : C), ψ (a.1 c) = ρ a * ψ c * (ρ a)⁻¹)
    {J : Subgroup C} (hGE : GGInnerDiagOn ρ.range (J.map ψ)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ I _ θJ => GGAutsInduceOn A J θJ I) := by
  classical
  have hGE' : LargeEvenMarking (J.map ψ) (fun lab R _ I F θK =>
      ρ.range ≤ Subgroup.normalizer ((J.map ψ : Subgroup (ModGL Tag.E6 L)) :
        Set (ModGL Tag.E6 L)) ∧
      ∀ b ∈ ρ.range, ∃ φ ∈ I, LargeEvenInduces θK (fun l l' : ↥(J.map ψ) =>
        (l' : ModGL Tag.E6 L) = b⁻¹ * (l : ModGL Tag.E6 L) * b) φ) := hGE
  let eJK : ↥J ≃* ↥(J.map ψ) := J.equivMapOfInjective ψ hψinj
  have hmarkJ : LargeEvenMarking J (fun _ _ _ I _ θJ => GGAutsInduceOn A J θJ I) := by
    refine largeEvenMarking_congr eJK ?_ hGE'
    intro lab R instR I F θK hP a ha
    have hb : (ρ ⟨a, ha⟩)⁻¹ ∈ ρ.range :=
      Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
    obtain ⟨φ, hφ, hind⟩ := hP.2 _ hb
    refine ⟨φ, hφ, ?_⟩
    refine (largeEvenInduces_congr_equiv eJK θK
      (fun j j' : ↥J => a (j : C) = (j' : C))
      (fun l l' : ↥(J.map ψ) => (l' : ModGL Tag.E6 L) =
        ((ρ ⟨a, ha⟩)⁻¹)⁻¹ * (l : ModGL Tag.E6 L) * (ρ ⟨a, ha⟩)⁻¹) ?_ φ).2 ?_
    · intro j j'
      have hcoe : ∀ j : ↥J,
          ((eJK j : ↥(J.map ψ)) : ModGL Tag.E6 L) = ψ (j : C) := fun _ => rfl
      rw [hcoe j, hcoe j']
      constructor
      · intro h
        rw [← h, hρint ⟨a, ha⟩ (j : C)]
        simp
      · intro h
        apply hψinj
        rw [hρint ⟨a, ha⟩ (j : C)]
        simpa using h.symm
    · exact hind
  have hnormK : ρ.range ≤ Subgroup.normalizer
      ((J.map ψ : Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) :=
    CFSG.StandardType.GGDichotomy.le_normalizer_of_innerDiagOn hGE
  have hnormJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := by
    intro a ha j hj
    have hmem : ρ ⟨a, ha⟩ * ψ (j : C) * (ρ ⟨a, ha⟩)⁻¹ ∈ J.map ψ :=
      (Subgroup.mem_normalizer_iff.mp
        (hnormK (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)) (ψ (j : C))).mp
        (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)
    have hEq : ψ (a j) = ρ ⟨a, ha⟩ * ψ (j : C) * (ρ ⟨a, ha⟩)⁻¹ :=
      hρint ⟨a, ha⟩ (j : C)
    rw [← hEq] at hmem
    obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp hmem
    exact (hψinj hxeq) ▸ hxJ
  exact ⟨hnormJ, hmarkJ⟩

section Certificates


theorem componentMarking_of_lang_connected
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀)
    {C : Type} [Group C] (ψ : C →* ModGL Tag.E6 L)
    (hψinj : Function.Injective ψ) (hψran : ψ.range = S.Γ)
    {A : Subgroup (MulAut C)} (ρ : A →* ModGL Tag.E6 L)
    (hρinj : Function.Injective ρ)
    (hρint : ∀ (a : A) (c : C), ψ (a.1 c) = ρ a * ψ c * (ρ a)⁻¹)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hρmodel : ρ.range ≤ S.D.model)
    (hρexp : ∀ a : A, (ρ a) ^ p = 1)
    {u : MulAut C} (hu : u ∈ A) (hu1 : u ≠ 1)
    {b : Fin Tag.E6.rank → Lˣ} (hbu : rootDiagUnit .E6 b = ρ ⟨u, hu⟩)
    (hbT : rootDiagUnit .E6 b ∈ S.D.torus)
    (hbpow : ∀ j, b j ^ p = 1)
    (hconn : ρ.range ≤ familyGroup (fun _ : Unit => b))
    {J : Subgroup C} (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ I _ θJ => GGAutsInduceOn A J θJ I) := by
  classical
  have hfix : (ggAutFixedSubgroup u).map ψ =
      S.Γ ⊓ Subgroup.centralizer {ρ ⟨u, hu⟩} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hψran]
        exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
      · change ψ x ∈ Subgroup.centralizer {ρ ⟨u, hu⟩}
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfixx : ρ ⟨u, hu⟩ * ψ x * (ρ ⟨u, hu⟩)⁻¹ = ψ x := by
          rw [← hρint ⟨u, hu⟩ x, hx]
        have hcomm : ψ x * ρ ⟨u, hu⟩ = ρ ⟨u, hu⟩ * ψ x := by
          have := congrArg (fun z => z * ρ ⟨u, hu⟩) hfixx
          simpa [mul_assoc] using this.symm
        exact hcomm
    · rintro ⟨hyΓ, hyC⟩
      change y ∈ (S.Γ : Set (ModGL Tag.E6 L)) at hyΓ
      have hyran : y ∈ ψ.range := by
        rw [hψran]
        exact hyΓ
      obtain ⟨c, rfl⟩ := hyran
      refine ⟨c, ?_, rfl⟩
      apply hψinj
      rw [hρint ⟨u, hu⟩ c]
      change ψ c ∈ Subgroup.centralizer {ρ ⟨u, hu⟩} at hyC
      have hc : ψ c * ρ ⟨u, hu⟩ = ρ ⟨u, hu⟩ * ψ c :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      rw [← hc]
      group
  have hJopen : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ
  have hKopen : CFSG.Open.IsComponentOf (J.map ψ)
      (S.Γ ⊓ Subgroup.centralizer {ρ ⟨u, hu⟩}) := by
    have hmap :=
      CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_map_of_injective ψ hψinj hJopen
    rwa [hfix] at hmap
  have hKopen' : CFSG.Open.IsComponentOf (J.map ψ)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 b}) := by
    simpa only [hbu] using hKopen
  have hb1 : rootDiagUnit .E6 b ≠ 1 := by
    rw [hbu]
    intro heq
    apply hu1
    exact congrArg Subtype.val (hρinj (heq.trans (map_one ρ).symm))
  obtain ⟨f, hf1, hqf⟩ := CFSG.HardMathSupport.Dickson.Sec6.ssTw_exists_f S (ℓ := 2)
  obtain ⟨S5, hD5, -⟩ :=
    CFSG.StandardType.LieCore.exists_langSetup_of_datum S.D S.ρ S.frob S.finite hf1 hqf
  have hΓ5 : S5.Γ = S.Γ := by
    show S5.D.Γ = S.D.Γ
    rw [hD5]
  have hX : CFSG.Assembly.IsComponentOf (J.map ψ)
      (S5.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 b}) := by
    rw [hΓ5]
    exact CFSG.Assembly.isComponentOf_iff_open.2 hKopen'
  have hEp : ∀ e ∈ ρ.range, e ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    exact hρexp a
  have hGE : GGE0Concl ρ.range (J.map ψ) :=
    langTorus_connectedModelAction (Or.inl rfl) hp hp2 S5 b
      (by rw [hD5]; exact hbT) hbpow hb1 _ _
      (by rw [hD5]; exact hρmodel) hEp hconn hX
  have hpL : (p : L) ≠ 0 := by
    refine natCast_ne_zero_of_ringChar_ne hp ?_
    rw [ringChar.eq L 2]
    exact fun h => hp2 h.symm
  obtain ⟨i, hQS, hXeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      S5 (by decide : Tag.E6 ≠ .G2) hp hpL (by rw [hD5]; exact hbT) hbpow hb1
        (CFSG.Assembly.isComponentOf_iff_open.mp hX)
  obtain ⟨t', n', f', hLM', -, -⟩ :=
    langComp_lieModel_alternative (Or.inl rfl) S5 hp hp2 (by rw [hD5]; exact hbT) hbpow i hQS
      (y := 1) (Subgroup.one_mem _) (map_one _) (by simp)
  have hmark : LargeEvenMarking ↥(J.map ψ) (fun _ _ _ _ _ _ => True) := by
    rw [hXeq]
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot (Group.isPerfect_def.mp hQS.1) hLM')
  have hM : GGInnerDiagOn ρ.range (J.map ψ) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨hGE.1, h.2⟩) (hGE.2 hmark)
  exact componentMarking_of_model_innerDiag ψ hψinj ρ hρint hM


theorem componentMarking_of_lang_torus
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀)
    {C : Type} [Group C] (ψ : C →* ModGL Tag.E6 L)
    (hψinj : Function.Injective ψ) (hψran : ψ.range = S.Γ)
    {A : Subgroup (MulAut C)} (ρ : A →* ModGL Tag.E6 L)
    (hρinj : Function.Injective ρ)
    (hρint : ∀ (a : A) (c : C), ψ (a.1 c) = ρ a * ψ c * (ρ a)⁻¹)
    (hρtor : ρ.range ≤ S.D.torus)
    (hρ3 : ∀ a : A, (ρ a) ^ 3 = 1)
    {u : MulAut C} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup C} (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ I _ θJ => GGAutsInduceOn A J θJ I) := by
  classical
  have hfix : (ggAutFixedSubgroup u).map ψ =
      S.Γ ⊓ Subgroup.centralizer {ρ ⟨u, hu⟩} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hψran]
        exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
      · change ψ x ∈ Subgroup.centralizer {ρ ⟨u, hu⟩}
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfixx : ρ ⟨u, hu⟩ * ψ x * (ρ ⟨u, hu⟩)⁻¹ = ψ x := by
          rw [← hρint ⟨u, hu⟩ x, hx]
        have hcomm : ψ x * ρ ⟨u, hu⟩ = ρ ⟨u, hu⟩ * ψ x := by
          have := congrArg (fun z => z * ρ ⟨u, hu⟩) hfixx
          simpa [mul_assoc] using this.symm
        exact hcomm
    · rintro ⟨hyΓ, hyC⟩
      change y ∈ (S.Γ : Set (ModGL Tag.E6 L)) at hyΓ
      have hyran : y ∈ ψ.range := by
        rw [hψran]
        exact hyΓ
      obtain ⟨c, rfl⟩ := hyran
      refine ⟨c, ?_, rfl⟩
      apply hψinj
      rw [hρint ⟨u, hu⟩ c]
      change ψ c ∈ Subgroup.centralizer {ρ ⟨u, hu⟩} at hyC
      have hc : ψ c * ρ ⟨u, hu⟩ = ρ ⟨u, hu⟩ * ψ c :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      rw [← hc]
      group
  have hJopen : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ
  have hKopen : CFSG.Open.IsComponentOf (J.map ψ)
      (S.Γ ⊓ Subgroup.centralizer {ρ ⟨u, hu⟩}) := by
    have hmap :=
      CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_map_of_injective ψ hψinj hJopen
    rwa [hfix] at hmap
  obtain ⟨b, hbu⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    ((CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mp
      (hρtor (MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩))).1)
  have hbT : rootDiagUnit .E6 b ∈ S.D.torus := by
    rw [← hbu]
    exact hρtor (MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩)
  have hbpow : ∀ j, b j ^ 3 = 1 := by
    have h3 : (rootDiagUnit .E6 b) ^ 3 = 1 := by
      rw [← hbu]
      exact hρ3 ⟨u, hu⟩
    have hb3' : b ^ 3 = 1 := by
      apply rootDiagUnit_injective
      rw [← rootDiagUnit_pow, h3, rootDiagUnit_one]
    intro j
    simpa using congrFun hb3' j
  have hb1 : rootDiagUnit .E6 b ≠ 1 := by
    rw [← hbu]
    intro hρu1
    have huA : (⟨u, hu⟩ : A) ≠ 1 := by
      intro h
      exact hu1 (congrArg Subtype.val h)
    exact huA (hρinj (by simpa using hρu1))
  have hE : ρ.range ≤ S.D.torus := hρtor
  have hEp : ∀ e ∈ ρ.range, e ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    exact hρ3 a
  have hKopen' : CFSG.Open.IsComponentOf (J.map ψ)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 b}) := by
    simpa only [← hbu] using hKopen
  have hM : GGInnerDiagOn ρ.range (J.map ψ) :=
    langTorus_innerDiagOn_subgroup_E6_three S hbT hbpow hb1 hE hEp hKopen'
  exact componentMarking_of_model_innerDiag ψ hψinj ρ hρint hM


theorem q1TwE6ThreeModel_holds
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1)
    {A : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : A ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (h5 : 3 ^ 5 ≤ Nat.card A)
    {u : MulAut (twistedE6RootGroup K σ)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
  classical
  let C := twistedE6RootGroup K σ
  let I_C : Subgroup (MulAut C) := twistedE6Inn K σ ⊔ twistedE6Diag K σ
  obtain ⟨S, e, -, -, hT3, hdict, hfaith⟩ :=
    twisted_setup_plus (f := n) hn hK σ hσ h3
  have hΓle : S.Γ ≤ S.D.model :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup.Γ_le_model S
  have hInn : (MulAut.conj : C →* MulAut C).range ≤ I_C := le_sup_left
  have hreal : ∀ φ : I_C, ∃ d ∈ S.D.model,
      ∀ y : C, e (φ.1 y) = d * e y * d⁻¹ := fun φ => hdict φ.1 φ.2
  obtain ⟨act, -, hact_mem, hact_rel⟩ :=
    exists_shape_model_action S e hΓle hInn hreal hfaith
  have hact_inj : Function.Injective act := by
    intro φ1 φ2 h12
    apply Subtype.ext
    exact MulEquiv.ext fun y => e.injective (Subtype.ext (by
      rw [hact_rel φ1 y, hact_rel φ2 y, h12]))
  let ρ : A →* ModGL Tag.E6 (AlgebraicClosure K) := act.comp (Subgroup.inclusion hAI)
  have hρinj : Function.Injective ρ := hact_inj.comp (Subgroup.inclusion_injective hAI)
  have hρ_model : ρ.range ≤ S.D.model := by
    rintro _ ⟨a, rfl⟩
    exact hact_mem (Subgroup.inclusion hAI a)
  have hAcomm : ∀ a b : A, a * b = b * a := by
    have : IsMulCommutative A := hA.1
    exact fun a b => mul_comm' a b
  have hAexp : ∀ a : A, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    exact hA.2 (a : MulAut C) a.2
  have hAel' : CFSG.Open.IsElemAbelian 3 ρ.range := by
    have htop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup A) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x _ => ?_⟩
      · apply Subtype.ext
        exact hAcomm (Subtype.val x) (Subtype.val y)
      · exact hAexp x
    have hmap := CFSG.Open.IsElemAbelian.map htop ρ
    simpa [MonoidHom.range_eq_map] using hmap
  have h5' : 3 ^ 5 ≤ Nat.card ρ.range := by
    have hcard : Nat.card ρ.range = Nat.card A := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hρinj]
      exact Nat.card_congr (Subgroup.topEquiv (G := A)).toEquiv
    rw [hcard]
    exact h5
  obtain ⟨h, hh, hconj⟩ :=
    toral_conj_in_model (weylGoodRankFive (AlgebraicClosure K)) S hT3 hρ_model hAel' h5'
  let ρ' : A →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (MulAut.conj h).toMonoidHom.comp ρ
  have hρ'tor : ρ'.range ≤ S.D.torus := by
    simpa only [ρ', MonoidHom.range_comp] using hconj
  have hhn : h ∈ Subgroup.normalizer
      (S.Γ : Set (ModGL Tag.E6 (AlgebraicClosure K))) :=
    Subgroup.normalizer_commutator_ge_right S.D.model S.D.model hh
  let σΓ : S.Γ ≃* S.Γ := S.Γ.normalizerMonoidHom ⟨h, hhn⟩
  let e' : twistedE6RootGroup K σ ≃* S.Γ := e.trans σΓ
  let ψ : twistedE6RootGroup K σ →* ModGL Tag.E6 (AlgebraicClosure K) :=
    S.Γ.subtype.comp e'.toMonoidHom
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact e'.injective (Subtype.ext hxy)
  have hψran : ψ.range = S.Γ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e' x).2
    · intro hy
      refine ⟨e'.symm ⟨y, hy⟩, ?_⟩
      show ((e' (e'.symm ⟨y, hy⟩) : S.Γ) : ModGL Tag.E6 (AlgebraicClosure K)) = y
      rw [e'.apply_symm_apply]
  have hψcoe : ∀ c : twistedE6RootGroup K σ,
      ψ c = h * (e c : ModGL Tag.E6 (AlgebraicClosure K)) * h⁻¹ := by
    intro c
    show ((σΓ (e c) : S.Γ) : ModGL Tag.E6 (AlgebraicClosure K)) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hint : ∀ (a : A) (c : twistedE6RootGroup K σ),
      ψ (a.1 c) = ρ' a * ψ c * (ρ' a)⁻¹ := by
    intro a c
    have hρ'coe : ρ' a = h * act (Subgroup.inclusion hAI a) * h⁻¹ := by
      change (MulAut.conj h) (act (Subgroup.inclusion hAI a)) =
        h * act (Subgroup.inclusion hAI a) * h⁻¹
      exact MulAut.conj_apply h _
    have hrel : (e (a.1 c) : ModGL Tag.E6 (AlgebraicClosure K)) =
        act (Subgroup.inclusion hAI a) * (e c : ModGL Tag.E6 (AlgebraicClosure K)) *
          (act (Subgroup.inclusion hAI a))⁻¹ :=
      hact_rel (Subgroup.inclusion hAI a) c
    rw [hψcoe (a.1 c), hψcoe c, hρ'coe, hrel]
    group
  have hρ'3 : ∀ a : A, (ρ' a) ^ 3 = 1 := by
    intro a
    have h3' : (Subgroup.inclusion hAI a) ^ 3 = 1 := by
      apply Subtype.ext
      exact hA.2 (a : MulAut C) a.2
    have hρ'a : ρ' a =
        (MulAut.conj h).toMonoidHom (act (Subgroup.inclusion hAI a)) := rfl
    rw [hρ'a, ← map_pow, ← map_pow, h3', map_one, map_one]
  have hρ'inj : Function.Injective ρ' := by
    intro a b hab
    apply hρinj
    exact (MulAut.conj h).injective (by simpa [ρ'] using hab)
  exact componentMarking_of_lang_torus S ψ hψinj hψran ρ' hρ'inj hint hρ'tor hρ'3 hu hu1 hJ

end Certificates

end CFSG.StandardType.Q1TwE6ThreeModel

end
