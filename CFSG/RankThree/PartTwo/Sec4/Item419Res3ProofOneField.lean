module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofOne
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec4.Item424ProofCensus
import CFSG.RankThree.PartOne.KE.SuzukiPlane
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.GorensteinWalter (PSL2 PGL2)
open CFSG.Blueprint (suzukiGroup)

namespace Item419Res3

theorem theta_le_center {L : Type*} [Group L] [Finite L] (hL : IsQuasisimple L) :
    aschbacherSolvableCore 3 L ≤ Subgroup.center L := by
  obtain ⟨hs, hchar, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  have := hchar
  have : (aschbacherSolvableCore 3 L).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL this with h | h
  · exfalso
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL
    have : Group.IsPerfect L := hL.1
    have : Group.IsSolvable L := by
      have e : (aschbacherSolvableCore 3 L : Subgroup L) ≃* L :=
        (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · exact h

theorem mem_centralizer_of_thetaQuot_eq_one {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsComponent L) {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (h1 : thetaQuotMulAut L (compAction L ⟨a, ha⟩) = 1) :
    a ∈ Subgroup.centralizer (L : Set G) := by
  have hq : IsQuasisimple L := hL.1
  have : Group.IsPerfect L := hq.1
  set φ := compAction L ⟨a, ha⟩ with hφ
  have hcent : ∀ l : L, l⁻¹ * φ.toMonoidHom l ∈ Subgroup.center L := by
    intro l
    apply theta_le_center hq
    have h2 := congrArg (fun γ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
      γ (l : L ⧸ aschbacherSolvableCore 3 L)) h1
    simp only [MulAut.one_apply, thetaQuotMulAut_mk] at h2
    have h3 := QuotientGroup.eq.mp h2.symm
    exact h3
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ.toMonoidHom hcent
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h4 := congrArg (fun f : L →* L => ((f ⟨l, hl⟩ : L) : G)) hid
  change a * l * a⁻¹ = l at h4
  calc l * a = a * l * a⁻¹ * a := by rw [h4]
    _ = a * l := by group

theorem mem_centralizer_of_inducedAutHom_eq_one {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsComponent L) {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (h1 : inducedAutHom L e ⟨a, ha⟩ = 1) :
    a ∈ Subgroup.centralizer (L : Set G) := by
  refine mem_centralizer_of_thetaQuot_eq_one hL ha ?_
  rw [inducedAutHom_apply] at h1
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

theorem false_of_isSolvable_fixSub {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    {K : Subgroup G} (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hs : Group.IsSolvable (Item426.fixSub (inducedAutHom L e ⟨a, ha⟩))) : False := by
  have hq : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hKle) hKc.1
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect K := hq.1
  have hKL : K ≤ L := hKle.trans inf_le_left
  set τ := inducedAutHom L e ⟨a, ha⟩ with hτ
  set π : K →* M := e.toMonoidHom.comp
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL)) with hπ
  have hfix : ∀ k : K, π k ∈ Item426.fixSub τ := by
    intro k
    have hk : a * (k : G) * a⁻¹ = k := by
      rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hKle k.2).2), mul_inv_cancel_right]
    have hφk : compAction L ⟨a, ha⟩ (Subgroup.inclusion hKL k) = Subgroup.inclusion hKL k := by
      apply Subtype.ext
      change a * (k : G) * a⁻¹ = k
      exact hk
    have hπk : π k = e ((Subgroup.inclusion hKL k : L) : L ⧸ aschbacherSolvableCore 3 L) := rfl
    rw [Item426.mem_fixSub, hτ, inducedAutHom_apply, MulAut.congr_apply, hπk,
      MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, thetaQuotMulAut_mk,
      hφk]
  set f : K →* Item426.fixSub τ := π.codRestrict _ hfix with hf
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hker : Group.IsSolvable f.ker := by
    have hle : ∀ k : f.ker, Subgroup.inclusion hKL k ∈ aschbacherSolvableCore 3 L := by
      intro k
      have hk : f k = 1 := k.2
      have hk' : π k = 1 := congrArg Subtype.val hk
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk'
      exact hk'
    let g : f.ker →* aschbacherSolvableCore 3 L :=
      ((Subgroup.inclusion hKL).comp f.ker.subtype).codRestrict _ hle
    exact Group.isSolvable_of_isSolvable_injective (f := g) fun x y hxy =>
      Subtype.ext (Subgroup.inclusion_injective hKL (congrArg Subtype.val hxy))
  have := hs
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])
  exact Group.IsPerfect.not_isSolvable K hKs

theorem sq_mem_range_toPGL {K : Type*} [Field K] (g : PGL2 K) :
    g ^ 2 ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g

theorem isInnerAut_of_mem_range_pglAction {K : Type*} [Field K] {τ : MulAut (PSL2 K)}
    (hτ3 : τ ^ 3 = 1)
    (hτ : τ ∈ (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K).range) :
    IsInnerAut τ := by
  obtain ⟨g, rfl⟩ := hτ
  obtain ⟨x, hx⟩ := sq_mem_range_toPGL g
  refine ⟨x⁻¹, ?_⟩
  have h1 : (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g) =
      ((CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction K g) ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ', hτ3]
  rw [h1, ← map_pow, ← hx, CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL,
    ← map_inv]

theorem inducesKindPSL2_field_of_component {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hL : IsComponent L) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    {F : Type} [Field F] [Finite F] (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 F) :
    InducesKindPSL2 F L a .field := by
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  set τ := inducedAutHom L e ⟨a, ha⟩ with hτ
  have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L e ha ha3'
  have hinner : ¬ IsInnerAut τ := by
    rintro ⟨g, hg⟩
    by_cases hg1 : g = 1
    · apply haC
      refine mem_centralizer_of_inducedAutHom_eq_one hL e ha ?_
      rw [← hτ, ← hg, hg1, map_one]
    · apply false_of_isSolvable_fixSub hKle hKc e ha
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
      have : Fact p.Prime := ⟨hp⟩
      have hF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
      have : Finite (PSL2 F) := Finite.of_equiv _ e.toEquiv
      have hfix : Item426.fixSub τ = Subgroup.centralizer ({g} : Set (PSL2 F)) := by
        ext y
        rw [Item426.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, ← hg,
          MulAut.conj_apply]
        constructor
        · intro h
          calc y * g = g * y * g⁻¹ * g := by rw [h]
            _ = g * y := by group
        · intro h
          rw [← h, mul_inv_cancel_right]
      rw [hfix]
      refine Item424Proof.isSolvable_of_center_ne_bot_psl2 hF _ ?_
      intro hbot
      have hgC : (⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
          Subgroup.centralizer ({g} : Set (PSL2 F))) ∈ Subgroup.center _ := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
      rw [hbot, Subgroup.mem_bot] at hgC
      exact hg1 (congrArg Subtype.val hgC)
  rcases hasKind_psl2_diagonal_or_field_of_pow_three_eq_one hτ3 hinner with hd | hf
  · exact (hinner (isInnerAut_of_mem_range_pglAction hτ3 hd.1)).elim
  · exact ⟨e, ha, hf⟩

theorem not_three_dvd_card_suzukiGroup {b : ℕ} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * b + 1)) :
    ¬ 3 ∣ Nat.card (suzukiGroup b F) := by
  rw [CFSG.LieType.Ree.suzuki_order hF]
  have hq : 2 ^ (2 * b + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ 2 ^ (2 * b + 1) := Nat.one_le_two_pow
  intro h3
  have h3' := (Nat.dvd_iff_mod_eq_zero ..).mp h3
  generalize hQ : 2 ^ (2 * b + 1) = Q at hq h1 h3'
  have hQ1 : (Q - 1) % 3 = 1 := by omega
  have hQ2 : Q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  have hQ21 : (Q ^ 2 + 1) % 3 = 2 := by omega
  rw [Nat.mul_mod, Nat.mul_mod (Q ^ 2), hQ2, hQ1, hQ21] at h3'
  omega

theorem inducesKindSz_field_of_component {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hL : IsComponent L) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {b : ℕ} {F : Type} [Field F] (hb : 1 ≤ b)
    (hF : Nat.card F = 2 ^ (2 * b + 1)) (e : L ⧸ aschbacherSolvableCore 3 L ≃* suzukiGroup b F) :
    InducesKindSz b F L a .field := by
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  by_cases hout : InducesOuterTheta a L
  · exact inducesKindSz_field L hb hF ha3' hout e
  · exfalso
    have hin : IsInnerAut (inducedAutHom L e ⟨a, ha⟩) := by
      by_contra h
      exact hout ((not_isInnerAut_inducedAutHom_iff L e ha).mp h)
    obtain ⟨g, hg⟩ := hin
    have hτ3 := inducedAutHom_pow_eq_one L e ha ha3'
    have hg3 : g ^ 3 = 1 := by
      apply CFSG.RankThree.PartOne.KE.suzuki_conj_injective hb hF
      rw [map_pow, hg, hτ3, map_one]
    have hfin : Finite (suzukiGroup b F) := Finite.of_equiv _ e.toEquiv
    have hg1 : g = 1 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ orderOf_dvd_natCard g) (not_three_dvd_card_suzukiGroup hF)
    apply haC
    refine mem_centralizer_of_inducedAutHom_eq_one hL e ha ?_
    rw [← hg, hg1, map_one]

end Item419Res3

open CFSG.LocalAnalysis.ComponentInitial

@[expose] def K419OneFieldPSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindPSL n F L x .field ∨ InducesKindPSL n F L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    (¬ InducesOuterTheta a L ∨ InducesKindPSL n F L a .diagonal) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindSL n F L x .field ∨ InducesKindSL n F L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    (¬ InducesOuterTheta a L ∨ InducesKindSL n F L a .diagonal) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldPSU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (p f : ℕ) (F : Type) [Field F] (hF : UnitaryFieldData p f F), 2 < p ^ f →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindPSU3 hF L x .field ∨ InducesKindPSU3 hF L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    (¬ InducesOuterTheta a L ∨ InducesKindPSU3 hF L a .diagonal) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldSU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (p f : ℕ) (F : Type) [Field F] (hF : UnitaryFieldData p f F) (hq : 2 < p ^ f),
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindSU3 hF L hq x .field ∨ InducesKindSU3 hF L hq x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    (¬ InducesOuterTheta a L ∨ InducesKindSU3 hF L hq a .diagonal) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldPSp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (r : ℕ) (F : Type) [Field F] [Finite F], (3 ≤ r ∨ (r = 2 ∧ ringChar F ≠ 2)) →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindPSp r F L x .field ∨ InducesKindPSp r F L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    (¬ InducesOuterTheta a L ∨ InducesKindPSp r F L a .diagonal) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldPSp4Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindPSp4Even F L x .field ∨ InducesKindPSp4Even F L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    (¬ InducesOuterTheta a L ∨ InducesKindPSp4Even F L a .diagonal) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

section Kinds


@[expose] def K419OneFieldG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 3 → 4 ≤ Nat.card F →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindG2 F L x .field ∨ InducesKindG2 F L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    ¬ InducesOuterTheta a L → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldTriality : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (f : ℕ), 1 ≤ f → ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ f) ^ 3 →
    ∀ σ : F ≃+* F, (∀ c, σ c = c ^ 2 ^ f) →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindTriality σ L x .field ∨ InducesKindTriality σ L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    ¬ InducesOuterTheta a L → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

@[expose] def K419OneFieldLargeRee : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ (b : ℕ), 1 ≤ b → ∀ (F : Type) [Field F] [Finite F]
      [CharP F CFSG.LieType.Ree.ReeTag.F4.prime], Nat.card F = 2 ^ (2 * b + 1) →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesKindLargeRee b F L x .field ∨ InducesKindLargeRee b F L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 → a ∉ Subgroup.centralizer (L : Set G) →
    ¬ InducesOuterTheta a L → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

end Kinds

namespace Item419Res3

theorem census_of_inducesStdKind
    (hPSL : K419OneFieldPSL) (hSL : K419OneFieldSL) (hPSU3 : K419OneFieldPSU3)
    (hSU3 : K419OneFieldSU3) (hPSp : K419OneFieldPSp) (hPSp4 : K419OneFieldPSp4Even)
    (hG2 : K419OneFieldG2) (hTri : K419OneFieldTriality) (hRee : K419OneFieldLargeRee)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsComponent L)
    (h46 : IsList46 (L ⧸ aschbacherSolvableCore 3 L)) {x a : G} (hx3 : x ^ 3 = 1)
    (hxa : x * a = a * x) {k : AutKind} (hk : k = .field ∨ k = .graphField)
    (hx : InducesStdKind L x k) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : orderOf a = 3) (haC : a ∉ Subgroup.centralizer (L : Set G)) {K : Subgroup G}
    (hK : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    (ht : IsType419 K) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  cases hx with
  | psl2 F h =>
    obtain ⟨e, -⟩ := h
    exact Or.inl (.psl2 F (inducesKindPSL2_field_of_component hL haL ha3 haC hK hKc e))
  | psl n F hn h =>
    have hxk : InducesKindPSL n F L x .field ∨ InducesKindPSL n F L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · rcases inducesKindPSL_diagonal_or_field L hn ha3' hout e with hd | hf
      · exact (hPSL G L hL h46 n F hn x a hx3 hxa hxk haL ha3 haC (Or.inr ⟨e, hd⟩) K hK hKc
          ht).elim
      · exact Or.inl (.psl n F hn ⟨e, hf⟩)
    · exact (hPSL G L hL h46 n F hn x a hx3 hxa hxk haL ha3 haC (Or.inl hout) K hK hKc ht).elim
  | sl n F hn h =>
    have hxk : InducesKindSL n F L x .field ∨ InducesKindSL n F L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · rcases inducesKindSL_diagonal_or_field L hn ha3' hout e with hd | hf
      · exact (hSL G L hL h46 n F hn x a hx3 hxa hxk haL ha3 haC (Or.inr hd) K hK hKc ht).elim
      · exact Or.inl (.sl n F hn hf)
    · exact (hSL G L hL h46 n F hn x a hx3 hxa hxk haL ha3 haC (Or.inl hout) K hK hKc ht).elim
  | psu3 hF hq h =>
    have hxk : InducesKindPSU3 hF L x .field ∨ InducesKindPSU3 hF L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · rcases inducesKindPSU3_diagonal_or_field L hq ha3' hout e with hd | hf
      · exact (hPSU3 G L hL h46 _ _ _ hF hq x a hx3 hxa hxk haL ha3 haC (Or.inr ⟨e, hd⟩) K hK
          hKc ht).elim
      · exact Or.inl (.psu3 hF hq ⟨e, hf⟩)
    · exact (hPSU3 G L hL h46 _ _ _ hF hq x a hx3 hxa hxk haL ha3 haC (Or.inl hout) K hK hKc
        ht).elim
  | su3 hF hq h =>
    have hxk : InducesKindSU3 hF L hq x .field ∨ InducesKindSU3 hF L hq x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · rcases inducesKindSU3_diagonal_or_field L hF hq ha3' hout e with hd | hf
      · exact (hSU3 G L hL h46 _ _ _ hF hq x a hx3 hxa hxk haL ha3 haC (Or.inr hd) K hK hKc
          ht).elim
      · exact Or.inl (.su3 hF hq hf)
    · exact (hSU3 G L hL h46 _ _ _ hF hq x a hx3 hxa hxk haL ha3 haC (Or.inl hout) K hK hKc
        ht).elim
  | psp r F hr h =>
    have hxk : InducesKindPSp r F L x .field ∨ InducesKindPSp r F L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · have hdf : InducesKind L (stdPinnedPSp r F) e a .diagonal ∨
          InducesKind L (stdPinnedPSp r F) e a .field := by
        rcases hr with hr3 | ⟨rfl, hodd⟩
        · exact inducesKindPSp_diagonal_or_field L hr3 ha3' hout e
        · exact inducesKindPSp_two_diagonal_or_field L hodd ha3' hout e
      rcases hdf with hd | hf
      · exact (hPSp G L hL h46 r F hr x a hx3 hxa hxk haL ha3 haC (Or.inr ⟨e, hd⟩) K hK hKc
          ht).elim
      · exact Or.inl (.psp r F hr ⟨e, hf⟩)
    · exact (hPSp G L hL h46 r F hr x a hx3 hxa hxk haL ha3 haC (Or.inl hout) K hK hKc ht).elim
  | psp4even F h =>
    have hxk : InducesKindPSp4Even F L x .field ∨ InducesKindPSp4Even F L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · rcases inducesKindPSp4Even_diagonal_or_field L ha3' hout e with hd | hf
      · exact (hPSp4 G L hL h46 F x a hx3 hxa hxk haL ha3 haC (Or.inr ⟨e, hd⟩) K hK hKc
          ht).elim
      · exact Or.inl (.psp4even F ⟨e, hf⟩)
    · exact (hPSp4 G L hL h46 F x a hx3 hxa hxk haL ha3 haC (Or.inl hout) K hK hKc ht).elim
  | g2 F hK3 hK4 h =>
    have hxk : InducesKindG2 F L x .field ∨ InducesKindG2 F L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · exact Or.inl (.g2 F hK3 hK4 (inducesKindG2_field L hK3 hK4 ha3' hout e))
    · exact (hG2 G L hL h46 F hK3 hK4 x a hx3 hxa hxk haL ha3 haC hout K hK hKc ht).elim
  | sz b F hb hF h =>
    obtain ⟨e, -⟩ := h
    exact Or.inl (.sz b F hb hF (inducesKindSz_field_of_component hL haL ha3 haC hb hF e))
  | triality f hf F hF σ hσ h =>
    have hxk : InducesKindTriality σ L x .field ∨ InducesKindTriality σ L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · exact Or.inr (.triality f hf F hF σ hσ
        (inducesKindTriality_graphField hf hF hσ L ha3' hout e))
    · exact (hTri G L hL h46 f hf F hF σ hσ x a hx3 hxa hxk haL ha3 haC hout K hK hKc ht).elim
  | largeRee b hb F hF h =>
    have hxk : InducesKindLargeRee b F L x .field ∨ InducesKindLargeRee b F L x .graphField :=
      by rcases hk with rfl | rfl; exacts [Or.inl h, Or.inr h]
    obtain ⟨e, -⟩ := h
    by_cases hout : InducesOuterTheta a L
    · exact Or.inl (.largeRee b hb F hF (inducesKindLargeRee_field L hb hF
        (CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj b F hF) ha3' hout e))
    · exact (hRee G L hL h46 b hb F hF x a hx3 hxa hxk haL ha3 haC hout K hK hKc ht).elim

end Item419Res3

open Item419Res3

theorem k419OneFieldCensus_of
    (hPSL : K419OneFieldPSL) (hSL : K419OneFieldSL) (hPSU3 : K419OneFieldPSU3)
    (hSU3 : K419OneFieldSU3) (hPSp : K419OneFieldPSp) (hPSp4 : K419OneFieldPSp4Even)
    (hG2 : K419OneFieldG2) (hTri : K419OneFieldTriality) (hRee : K419OneFieldLargeRee) :
    K419OneFieldCensus := by
  intro G _ _ L hL h46 x a hx3 hxa hx haL ha3 haC K hK hKc ht
  rcases hx with hx | hx
  · exact census_of_inducesStdKind hPSL hSL hPSU3 hSU3 hPSp hPSp4 hG2 hTri hRee hL h46 hx3 hxa
      (Or.inl rfl) hx haL ha3 haC hK hKc ht
  · exact census_of_inducesStdKind hPSL hSL hPSU3 hSU3 hPSp hPSp4 hG2 hTri hRee hL h46 hx3 hxa
      (Or.inr rfl) hx haL ha3 haC hK hKc ht

end CFSG.RankThree.PartTwo.Sec4
