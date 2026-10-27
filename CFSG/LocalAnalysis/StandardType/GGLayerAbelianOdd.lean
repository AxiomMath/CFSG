module

public import CFSG.LocalAnalysis.StandardType.GGOddLayerCores

public section

namespace CFSG.StandardType

private theorem exists_odd_prime_mem_pow_eq_one {G : Type*} [Group G] [Finite G]
    {E : Subgroup G} (hE : Odd (Nat.card E)) (hne : E ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ z ∈ E, z ≠ 1 ∧ z ^ p = 1 := by
  have hcard : Nat.card E ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hp : (Nat.card E).minFac.Prime := Nat.minFac_prime hcard
  have hdvd : (Nat.card E).minFac ∣ Nat.card E := Nat.minFac_dvd _
  haveI : Fact (Nat.card E).minFac.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Nat.card E).minFac hdvd
  refine ⟨(Nat.card E).minFac, hp, hE.ne_two_of_dvd_nat hdvd, x, x.2, fun h => ?_, ?_⟩
  · have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact congrArg Subtype.val h

namespace LayerCores

theorem odd_card_map_conj {S : Type*} [Group S] {A : Subgroup S} (hA : Odd (Nat.card A)) :
    Odd (Nat.card (A.map (MulAut.conj : S →* MulAut S))) :=
  hA.of_dvd_nat (Subgroup.card_map_dvd _ _)

end LayerCores

section Cert

namespace LayerAbelian

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.I142N CFSG.LocalAnalysis.GLTheoremA.I142T
open scoped commutatorElement

theorem good_layer_abelianOdd {S : Type} [Group S] [Finite S] (E : Subgroup (MulAut S))
    (hEo : Odd (Nat.card E)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {z : MulAut S} (hzE : z ∈ E)
    (hz1 : z ≠ 1) {X : Subgroup S}
    (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z) {n : ℕ}
    (hcard : Nat.card E ≤ n)
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), Odd (Nat.card E') → (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) →
        Nat.card E' ≤ m → GoodA E'.subtype ⊤)
    (hK : ∀ K : Subgroup S, CFSG.Open.IsComponentOf K X → CPlus (↥K ⧸ Subgroup.center ↥K)) :
    GoodA E.subtype (GLALayer X) := by
  classical
  have hcE : ∀ a b : ↥E, a * b = b * a := fun a b => Subtype.ext (hEc a a.2 b b.2)
  have hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X := by
    intro a
    rw [hX]
    refine fixSubgroup_map_of_comm ?_
    have := congrArg Subtype.val (hcE a ⟨z, hzE⟩)
    exact this
  have hzX : ∀ x ∈ X, z x = x := by
    intro x hx
    rw [hX] at hx
    exact hx
  refine goodA_glaLayer_of_orbits E hXE ?_
  intro K₀ hK₀
  refine goodA_orbit_of_stab E hXE hK₀ ?_
  intro B hinv hB
  have hzK : ∀ y ∈ K₀, z y = y := fun y hy => hzX y (hK₀.1 hy)
  have hz_fix : K₀.map z.toMonoidHom = K₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := hzK y hy
      show z y ∈ K₀
      rw [this]
      exact hy
    · intro hx
      exact Subgroup.mem_map.2 ⟨x, hx, hzK x hx⟩
  have hzB : (⟨z, hzE⟩ : ↥E) ∈ B := hB ⟨z, hzE⟩ hz_fix
  set σ := quotAct (E.subtype.comp B.subtype) K₀ hinv with hσ
  set zB : ↥B := ⟨⟨z, hzE⟩, hzB⟩ with hzBdef
  have hzB_ne : zB ≠ 1 := by
    intro h
    apply hz1
    have := congrArg (fun u : ↥B => ((u : ↥E) : MulAut S)) h
    exact this
  have hzk : σ zB = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    show quotAct (E.subtype.comp B.subtype) K₀ hinv zB
        (QuotientGroup.mk' (Subgroup.center ↥K₀) x) =
      (1 : MulAut (↥K₀ ⧸ Subgroup.center ↥K₀)) (QuotientGroup.mk' (Subgroup.center ↥K₀) x)
    rw [← quotAct_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [restrictAct_apply]
    exact hzK x x.2
  have hcB : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (hcE a.1 b.1)
  have hpg : Odd (Nat.card σ.range) :=
    (hEo.of_dvd_nat (Subgroup.card_subgroup_dvd_card B)).of_dvd_nat (Subgroup.card_range_dvd σ)
  have hcr : ∀ u ∈ σ.range, ∀ v ∈ σ.range, u * v = v * u := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hcB a b]
  have hCP : CPlus (↥K₀ ⧸ Subgroup.center ↥K₀) := hK K₀ hK₀
  have hlt : Nat.card σ.range < n := by
    have h1 := card_range_lt σ hzB_ne hzk
    have h2 : Nat.card ↥B ≤ Nat.card E := Subgroup.card_le_card_group _
    omega
  have hG := ih (Nat.card σ.range) hlt (↥K₀ ⧸ Subgroup.center ↥K₀) hCP σ.range hpg hcr le_rfl
  intro P hP hPp
  rw [inf_top_eq] at hP ⊢
  have hP' : P ≤ fixA σ.range.subtype ⊓ ⊤ := by
    rw [inf_top_eq]
    exact (fixA_eq_range σ) ▸ hP
  have h3 := hG P hP' hPp
  rw [inf_top_eq] at h3
  exact (fixA_eq_range σ).symm ▸ h3

theorem step_good_abelianOdd {S : Type} [Group S] [Finite S] (hK : CompTypesCyc) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), Odd (Nat.card E') → (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) →
        Nat.card E' ≤ m → GoodA E'.subtype ⊤)
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S)
    (E : Subgroup (MulAut S)) (hEo : Odd (Nat.card E)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hcard : Nat.card E ≤ n) {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    GoodA E.subtype ⊤ := by
  have hXfix : I142.centFix (Subgroup.zpowers z) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := I142.centFix_zpowers z
  have hKc : ∀ K : Subgroup S, CFSG.Open.IsComponentOf K (I142.centFix (Subgroup.zpowers z)) →
      CPlus (↥K ⧸ Subgroup.center ↥K) := fun K hK' => hK S hS hnc hchev p hp hp2 z hzp K hK'
  have hGL := good_layer_abelianOdd E hEo hEc hzE hz1 hXfix hcard ih hKc
  have hcz := cyclic_good hS hnc hchev hp hp2 z hzp
  apply goodA_subtype_top_of_centFix
  intro P hP hPp
  have hzfix : ∀ x ∈ I142.centFix E, z x = x := fun x hx => I142.mem_centFix.1 hx z hzE
  have hPX : P ≤ I142.centFix (Subgroup.zpowers z) := by
    intro x hx
    rw [hXfix]
    exact hzfix x (hP hx)
  have hPL : P ≤ GLALayer (I142.centFix (Subgroup.zpowers z)) := hcz P hPX hPp
  have hP2 : P ≤ fixA E.subtype ⊓ GLALayer (I142.centFix (Subgroup.zpowers z)) := by
    rw [fixA_subtype_eq_centFix]
    exact le_inf hP hPL
  have h1 := hGL P hP2 hPp
  have hWX : fixA E.subtype ≤ I142.centFix (Subgroup.zpowers z) := by
    intro x hx
    rw [fixA_subtype_eq_centFix] at hx
    rw [hXfix]
    exact hzfix x hx
  have hsub := isSubnormal_inf_layer (I142.centFix (Subgroup.zpowers z)) hXfix hWX
  rw [fixA_subtype_eq_centFix] at h1 hsub
  exact h1.trans (GLALayer_mono_of_isSubnormal hsub)

theorem goodA_all_abelianOdd (hK : CompTypesCyc) (hT : TitsCentSolv) :
    ∀ n : ℕ, ∀ (S : Type) [Group S] [Finite S], CPlus S → ∀ E : Subgroup (MulAut S),
      Odd (Nat.card E) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ n →
        GoodA E.subtype ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hS E hEo hEc hcard
  obtain ⟨hsimp, hnc, hcl⟩ := hS
  by_cases hbot : E = ⊥
  · subst hbot
    apply goodA_subtype_top_of_centFix
    rw [I142.centFix_bot]
    intro P _ _
    exact I142.perfect_le_layer_top hsimp hnc P
  · obtain ⟨p, hp, hp2, z, hzE, hz1, hzp⟩ := exists_odd_prime_mem_pow_eq_one hEo hbot
    by_cases hTits : catalogIs S (onLie (· = TauCeti.LieTypeIndex.tits))
    · apply goodA_subtype_top_of_centFix
      intro P hP hPp
      haveI := hT S hTits p hp hp2 (Subgroup.zpowers z) (isElemAbelian_zpowers hzp)
        (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hz1)
      have hPz : P ≤ I142.centFix (Subgroup.zpowers z) := by
        intro x hx
        rw [I142.centFix_zpowers]
        exact I142.mem_centFix.1 (hP hx) z hzE
      have hPb := eq_bot_of_le_solvable (C := I142.centFix (Subgroup.zpowers z)) hPz hPp
      rw [hPb]
      exact bot_le
    · have hchev : IsChevSimple 2 S := hcl.resolve_right hTits
      exact step_good_abelianOdd hK hp hp2 ih hsimp hnc hchev E hEo hEc hcard hzE hz1 hzp

theorem lieSemisimpleCentAbelianOdd :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      IsChevSimple 2 S → ∀ E : Subgroup (MulAut S),
        Odd (Nat.card E) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
          ∀ P : Subgroup S, P ≤ I142.centFix E → ⁅P, P⁆ = P →
            P ≤ GLALayer (I142.centFix E) := by
  intro S _ _ hS hnc hchev E hEo hEc P hP hperf
  have hC : CPlus S := ⟨hS, hnc, Or.inl hchev⟩
  have hG := goodA_all_abelianOdd I142M.compTypesCyc_holds I142M.titsCentSolv_holds
    (Nat.card E) S hC E hEo hEc le_rfl
  have h := hG P (by rw [inf_top_eq, fixA_subtype_eq_centFix]; exact hP) hperf
  rw [inf_top_eq, fixA_subtype_eq_centFix] at h
  exact h

end LayerAbelian

namespace LayerCores

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem exists_subCoreFamily_of_chevSimple_odd {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S)
    (E : Subgroup (MulAut S)) (hEo : Odd (Nat.card E)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hZ : ∀ z ∈ CFSG.Open.GLALayer (I142.centFix E),
      (∀ y ∈ CFSG.Open.GLALayer (I142.centFix E), z * y = y * z) → z ^ 2 = 1 → z = 1) :
    ∃ (β : Type) (T : β → Subgroup S), IsSubCoreFamily (I142.centFix E) T :=
  exists_subCoreFamily_of_layer _
    (fun P hP hPp =>
      LayerAbelian.lieSemisimpleCentAbelianOdd S hS hnc hchev E hEo hEc P hP hPp)
    hZ

theorem exists_subCoreFamily_iff_layerCentre_odd {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S)
    (E : Subgroup (MulAut S)) (hEo : Odd (Nat.card E))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    (∃ (β : Type) (T : β → Subgroup S), IsSubCoreFamily (I142.centFix E) T) ↔
      ∀ z ∈ CFSG.Open.GLALayer (I142.centFix E),
        (∀ y ∈ CFSG.Open.GLALayer (I142.centFix E), z * y = y * z) → z ^ 2 = 1 → z = 1 :=
  ⟨fun ⟨_, _, h⟩ => layerCentre_of_isSubCoreFamily h,
    exists_subCoreFamily_of_chevSimple_odd hS hnc hchev E hEo hEc⟩

end LayerCores

end Cert

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.GLTheoremA

section Input

@[expose] def GGExcAdjOddLayerCentre (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A : Subgroup ↥(adjointGroup τ K)),
    Odd (Nat.card A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∀ z ∈ CFSG.Open.GLALayer (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))),
        (∀ y ∈ CFSG.Open.GLALayer (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))),
          z * y = y * z) → z ^ 2 = 1 → z = 1

@[expose] def GGE6InndiagOddLayerCentre : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A : Subgroup (MulAut ↥(adjointGroup .E6 K))),
    Odd (Nat.card A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
      ∀ z ∈ CFSG.Open.GLALayer (LayerSixE.autFix A),
        (∀ y ∈ CFSG.Open.GLALayer (LayerSixE.autFix A), z * y = y * z) → z ^ 2 = 1 → z = 1

end Input

section Bundle

@[expose] def GGTwE6OddLayerCentre : Prop :=
  ∀ f : ℕ, 1 ≤ f →
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), Odd (Nat.card A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      A ≤ LayerSixE.twInndiagAut f →
        ∀ z ∈ CFSG.Open.GLALayer (LayerSixE.autFix A),
          (∀ y ∈ CFSG.Open.GLALayer (LayerSixE.autFix A), z * y = y * z) → z ^ 2 = 1 → z = 1

@[expose] def GGOddLayerCentre : Prop :=
  GGExcAdjOddLayerCentre .F4 ∧ GGExcAdjOddLayerCentre .E7 ∧ GGExcAdjOddLayerCentre .E8 ∧
    GGE6InndiagOddLayerCentre ∧ GGTwE6OddLayerCentre

end Bundle

section Equivalence

theorem ggExcAdjOddLayerCores_iff_centre {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    GGExcAdjOddLayerCores τ ↔ GGExcAdjOddLayerCentre τ := by
  constructor
  · intro h K _ _ _ A hA hAc z hz hzc hz2
    obtain ⟨β, T, hT⟩ := h K A hA hAc
    exact LayerCores.layerCentre_of_isSubCoreFamily hT z hz hzc hz2
  · intro h K _ _ _ A hA hAc
    haveI := generated_group_finite τ K
    obtain ⟨hS, hnc⟩ := LayerCores.adjointGroup_isSimple_nonabelian hτ K
    have hE := LayerCores.centFix_map_conj A
    have key := (LayerCores.exists_subCoreFamily_iff_layerCentre_odd hS hnc
      (LayerCores.isChevSimple_adjointGroup_charTwo hτ K) (A.map MulAut.conj)
      (LayerCores.odd_card_map_conj hA) (LayerCores.comm_map_conj hAc)).2
      (by rw [hE]; exact h K A hA hAc)
    rw [hE] at key
    exact key

theorem ggE6InndiagOddLayerCores_iff_centre :
    GGE6InndiagOddLayerCores ↔ GGE6InndiagOddLayerCentre := by
  constructor
  · intro h K _ _ _ A hA hAc hAD z hz hzc hz2
    obtain ⟨β, T, hT⟩ := h K A hA hAc hAD
    exact LayerCores.layerCentre_of_isSubCoreFamily hT z hz hzc hz2
  · intro h K _ _ _ A hA hAc hAD
    haveI := generated_group_finite .E6 K
    obtain ⟨hS, hnc⟩ := LayerCores.adjointGroup_isSimple_nonabelian (Or.inr (Or.inl rfl)) K
    have hEq : LayerSixE.autFix A = I142.centFix A :=
      Subgroup.ext fun x => LayerSixE.mem_autFix.trans I142.mem_centFix.symm
    have key := (LayerCores.exists_subCoreFamily_iff_layerCentre_odd hS hnc
      (LayerCores.isChevSimple_adjointGroup_charTwo (Or.inr (Or.inl rfl)) K) A hA hAc).2
      (by rw [← hEq]; exact h K A hA hAc hAD)
    rw [← hEq] at key
    exact key

theorem ggTwE6OddLayerCores_iff_centre :
    GGTwE6OddLayerCores ↔ GGTwE6OddLayerCentre := by
  constructor
  · intro h f hf A hA hAc hAD z hz hzc hz2
    obtain ⟨β, T, hT⟩ := h f hf A hA hAc hAD
    exact LayerCores.layerCentre_of_isSubCoreFamily hT z hz hzc hz2
  · intro h f hf A hA hAc hAD
    haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
      Subtype.finite
    have hq := TwE6Nonsplit.isQuasisimple_graphFixedRootGroup f hf
    have hZ0 : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) = ⊥ :=
      CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_graphFixedRootGroup_E6_eq_bot
        (frobQ 2 f)
    let eZ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≃*
        (↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⧸
          Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
            (frobQ 2 f))) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).symm
    haveI := hq.2.1
    haveI hS : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) := eZ.isSimpleGroup
    have hnc : ∃ a b : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
    have hEq : LayerSixE.autFix A = I142.centFix A :=
      Subgroup.ext fun x => LayerSixE.mem_autFix.trans I142.mem_centFix.symm
    have key := (LayerCores.exists_subCoreFamily_iff_layerCentre_odd hS hnc
      (TwE6LayerRest.isChevSimple_graphFixedRootGroup f hf) A hA hAc).2
      (by rw [← hEq]; exact h f hf A hA hAc hAD)
    rw [← hEq] at key
    exact key

theorem ggOddLayerCores_iff_centre : GGOddLayerCores ↔ GGOddLayerCentre :=
  ⟨fun h => ⟨(ggExcAdjOddLayerCores_iff_centre (Or.inl rfl)).1 h.1,
      (ggExcAdjOddLayerCores_iff_centre (Or.inr (Or.inr (Or.inl rfl)))).1 h.2.1,
      (ggExcAdjOddLayerCores_iff_centre (Or.inr (Or.inr (Or.inr rfl)))).1 h.2.2.1,
      ggE6InndiagOddLayerCores_iff_centre.1 h.2.2.2.1, ggTwE6OddLayerCores_iff_centre.1 h.2.2.2.2⟩,
    fun h => ⟨(ggExcAdjOddLayerCores_iff_centre (Or.inl rfl)).2 h.1,
      (ggExcAdjOddLayerCores_iff_centre (Or.inr (Or.inr (Or.inl rfl)))).2 h.2.1,
      (ggExcAdjOddLayerCores_iff_centre (Or.inr (Or.inr (Or.inr rfl)))).2 h.2.2.1,
      ggE6InndiagOddLayerCores_iff_centre.2 h.2.2.2.1, ggTwE6OddLayerCores_iff_centre.2 h.2.2.2.2⟩⟩

end Equivalence

end CFSG.StandardType
