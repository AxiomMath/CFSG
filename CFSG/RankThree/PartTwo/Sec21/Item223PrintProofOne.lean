module

public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofTheta
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofKZero
public import CFSG.RankThree.PartTwo.KFacts.AutTrialityOrderThree
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

namespace Item223PrintProof

section List46

variable {X Y : Type} [Group X] [Group Y]

theorem nonempty_mulEquiv_of_mulEquiv (e : X ≃* Y) {M : Type*} [Group M]
    (h : Nonempty (X ≃* M)) : Nonempty (Y ≃* M) :=
  h.map fun f => e.symm.trans f

theorem isSLThreeEpsAt_of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : Sec4.IsSLThreeEpsAt X q) :
    Sec4.IsSLThreeEpsAt Y q := by
  obtain ⟨K, _, _, h⟩ := h
  rcases h with ⟨hK, ⟨f⟩⟩ | ⟨hK, ⟨f⟩⟩
  · exact ⟨K, inferInstance, inferInstance, Or.inl ⟨hK, ⟨e.symm.trans f⟩⟩⟩
  · exact ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, ⟨e.symm.trans f⟩⟩⟩

theorem isChevTwoRankTwoModel_of_mulEquiv (e : X ≃* Y) (h : Sec4.IsChevTwoRankTwoModel X) :
    Sec4.IsChevTwoRankTwoModel Y := by
  rcases h with ⟨n, hn1, h⟩ | ⟨f, h⟩
  · refine Or.inl ⟨n, hn1, ?_⟩
    rcases h with h | h | h | h | h
    · exact Or.inl (nonempty_mulEquiv_of_mulEquiv e h)
    · exact Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h))
    · exact Or.inr (Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (nonempty_mulEquiv_of_mulEquiv e h))))
  · refine Or.inr ⟨f, ?_⟩
    rcases h with h | h | h | h | h
    · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e.symm h)
    · exact Or.inr (Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e.symm h))
    · exact Or.inr (Or.inr (Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv e.symm h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.reeTitsModel_of_mulEquiv e.symm h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (CFSG.SectionRank.reeTitsModel_of_mulEquiv e.symm h))))

theorem isList46_of_mulEquiv (e : X ≃* Y) (h : Sec4.IsList46 X) : Sec4.IsList46 Y := by
  rcases h with ⟨p, e', hp, hp2, he, h⟩ | ⟨p, e', hp, hp3, he1, he2, h⟩ | ⟨p, hp, hp3, h⟩ |
    h | h | h | h | h
  · exact Or.inl ⟨p, e', hp, hp2, he, nonempty_mulEquiv_of_mulEquiv e h⟩
  · refine Or.inr (Or.inl ⟨p, e', hp, hp3, he1, he2, ?_⟩)
    rcases h with h | h | h
    · exact Or.inl (isSLThreeEpsAt_of_mulEquiv e h)
    · exact Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h))
    · exact Or.inr (Or.inr (nonempty_mulEquiv_of_mulEquiv e h))
  · refine Or.inr (Or.inr (Or.inl ⟨p, hp, hp3, ?_⟩))
    rcases h with h | h | ⟨h3, h⟩ | ⟨h3, h⟩
    · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e.symm h)
    · exact Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h))
    · exact Or.inr (Or.inr (Or.inl ⟨h3, nonempty_mulEquiv_of_mulEquiv e h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h3, nonempty_mulEquiv_of_mulEquiv e h⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rcases h with ⟨n, hn, h⟩ | h | h
    · exact Or.inl ⟨n, hn, nonempty_mulEquiv_of_mulEquiv e h⟩
    · exact Or.inr (Or.inl (h.of_mulEquiv e))
    · exact Or.inr (Or.inr (h.of_mulEquiv e))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rcases h with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
    · exact Or.inl ⟨s, hs, nonempty_mulEquiv_of_mulEquiv e h⟩
    · exact Or.inr ⟨s, hs, h.of_mulEquiv e⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    rcases h with h | ⟨n, hn, h⟩
    · exact Or.inl (isChevTwoRankTwoModel_of_mulEquiv e h)
    · exact Or.inr ⟨n, hn, isSLThreeEpsAt_of_mulEquiv e h⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    rcases h with h | h | h
    · exact Or.inl (nonempty_mulEquiv_of_mulEquiv e h)
    · exact Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h))
    · exact Or.inr (Or.inr (nonempty_mulEquiv_of_mulEquiv e h))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
    rcases h with ⟨e', he1, he2, h⟩ | h | ⟨hZ, h⟩
    · refine Or.inl ⟨e', he1, he2, ?_⟩
      rcases h with h | h
      · exact Or.inl (nonempty_mulEquiv_of_mulEquiv e h)
      · exact Or.inr (nonempty_mulEquiv_of_mulEquiv e h)
    · exact Or.inr (Or.inl (nonempty_mulEquiv_of_mulEquiv e h))
    · have hZY : Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center X) := by
        rw [← Sec13.map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective]
      let eq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
        QuotientGroup.congr _ _ e (Sec13.map_center_mulEquiv e)
      refine Or.inr (Or.inr ⟨hZY ▸ hZ, ?_⟩)
      rcases h with h | h
      · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eq.symm h)
      · exact Or.inr (nonempty_mulEquiv_of_mulEquiv eq h)

end List46

variable {G : Type} [Group G]

theorem isList46_of_mem_thetaComponentsAt [Finite G] (h46 : Sec4.Item4_6)
    (hG : TheoremFourHyp G) {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) :
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨X', hC4, h3, hX', rfl⟩ := exists_sub_of_mem_thetaComponentsAt hG ha3 ha1 hX
  exact isList46_of_mulEquiv (Sec13.thetaQuotEquivSub C X') (h46 C hC4 h3 X' hX')

section Kinds

theorem inducesStdKind_diagonal_of [Finite G] (h47 : Sec4.Item4_7W) (hG : TheoremFourHyp G)
    {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {X : Subgroup G} (hXa : X ∈ thetaComponentsAt 3 a)
    {x : G} (hxa : x * a = a * x) (hx3 : orderOf x = 3) (hout : Sec4.InducesOuterTheta x X)
    (hfield : ¬ KFacts.InducesStdKind X x .field)
    (hgf : ¬ KFacts.InducesStdKind X x .graphField) : KFacts.InducesStdKind X x .diagonal := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨X', hC4, h3, hX', rfl⟩ := exists_sub_of_mem_thetaComponentsAt hG ha3 ha1 hXa
  set x' : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hxa⟩ with hx'
  have hout' : Sec4.InducesOuterTheta x' X' :=
    (Sec8.Item82OneProof.inducesOuterTheta_sub_iff C X' x').mpr hout
  have hx'3 : orderOf x' = 3 := by
    rw [hx', Subgroup.orderOf_mk]
    exact hx3
  rcases Sec8.Item82OneProof.alt47W_map C X' x' (h47 C hC4 h3 X' hX' x' hx'3 hout') with
    ⟨-, -, -, -, -, -, hk⟩ | ⟨-, -, -, -, -, -, -, hk⟩ | ⟨-, hk⟩ | ⟨-, -, -, hk⟩ | ⟨n, hn, hD4⟩
  · exact (hfield hk).elim
  · exact hk
  · exact (hfield hk).elim
  · exact hk
  · exfalso
    obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Sec4.exists_mulEquiv_graphFixedRootGroup_D4 hD4
    have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    exact hgf (KFacts.InducesStdKind.triality n hn K hK σ hσ
      (KFacts.inducesKindTriality_graphField hn hK hσ _ hx3' hout E))

end Kinds

theorem kOf_eq_kZero_of_mulEquiv {A : Subgroup G} (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≠ 2)
    (e : kOf A φ ≃* projSL 2 (GaloisField 2 n)) : kOf A φ = kZero A φ := by
  by_cases hU : StatedClassicalModel (kZero A φ) .PSU 3 2 2
  · exfalso
    obtain ⟨K', hK', -⟩ := hK φ hφ hU
    obtain ⟨e4⟩ := Item222Proof.nonempty_mulEquiv_projSL_of_statedClassicalModel
      (kOf_spec hU ⟨K', hK'⟩).2.1
    exact hn2 (eq_of_mulEquiv_projSL_two hn (by norm_num) (e.symm.trans e4))
  · exact kOf_eq_kZero hU

theorem card_fixedInG_eq [Finite G] {A : Subgroup G} (hAc : ∀ a b : A, a * b = b * a)
    (hA81 : Nat.card A = 3 ^ 4) {φ : MulAut A} (hφ : IsReflectionOn φ) :
    Nat.card (fixedInG A φ) = 3 ^ 3 := by
  rw [fixedInG, Subgroup.card_map_of_injective A.subtype_injective]
  have h := card_eq_three_mul_card_fixed hAc hφ
  rw [hA81] at h
  omega

theorem invTwoBarNontrivial_of [Finite G] {E X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hQθ : Q ⊓ inSubgroup (aschbacherSolvableCore 3) X = ⊥)
    (hEQ : ∀ e ∈ E, ∀ q ∈ Q, e * q * e⁻¹ = q) : Sec8.InvTwoBarNontrivial E X := by
  set θX := aschbacherSolvableCore 3 X with hθX
  refine ⟨(Q.subgroupOf X).map (QuotientGroup.mk' θX), ?_, ?_, ?_⟩
  · obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
    have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
    intro hbot
    have hmem : QuotientGroup.mk' θX (⟨q, hQX hq⟩ : X) ∈
        (Q.subgroupOf X).map (QuotientGroup.mk' θX) := ⟨⟨q, hQX hq⟩, hq, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    have h1 : q ∈ Q ⊓ inSubgroup (aschbacherSolvableCore 3) X := ⟨hq, ⟨_, hmem, rfl⟩⟩
    rw [hQθ, Subgroup.mem_bot] at h1
    exact hq1' h1
  · exact (hQ2.comap_of_injective X.subtype X.subtype_injective).map _
  · intro τ hτ y hy
    obtain ⟨h, hN, hE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    obtain ⟨⟨q, hqX⟩, hq, rfl⟩ := hy
    refine ⟨⟨q, hqX⟩, hq, ?_⟩
    rw [QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    exact (hEQ h hE q (Subgroup.mem_subgroupOf.mp hq)).symm

theorem inf_inSubgroup_theta_eq_bot [Finite G] {K X : Subgroup G} (hKX : K ≤ X)
    [IsSimpleGroup K] (hKp : Group.IsPerfect K) :
    K ⊓ inSubgroup (aschbacherSolvableCore 3) X = ⊥ := by
  have hθs := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
  let eK : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  have : IsSimpleGroup (K.subgroupOf X) := eK.isSimpleGroup
  have hKp' : Group.IsPerfect (K.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have h := inf_eq_bot_of_isSimpleGroup_of_isSolvable hθs hKp'
  have h2 := congrArg (Subgroup.map X.subtype) h
  rwa [Subgroup.map_inf_eq _ _ _ X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hKX,
    Subgroup.map_bot] at h2

theorem eq_one_of_forall_conj_eq {X : Subgroup G} (hZ : Subgroup.center X = ⊥) {w : G}
    (hw : w ∈ X) (h : ∀ l ∈ X, w * l * w⁻¹ = l) : w = 1 := by
  have hc : (⟨w, hw⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : G) * w = w * g
    have := h g g.2
    calc (g : G) * w = w * g * w⁻¹ * w := by rw [this]
      _ = w * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem exists_conj_eq_of_not_inducesOuterTheta [Finite G] {X : Subgroup G}
    (hθ : aschbacherSolvableCore 3 X = ⊥) {x : G} (hx : x ∈ Subgroup.normalizer (X : Set G))
    (hout : ¬ Sec4.InducesOuterTheta x X) :
    ∃ y ∈ X, ∀ l ∈ X, x * l * x⁻¹ = y * l * y⁻¹ := by
  have hin : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hx⟩) ∈
      (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
        MulAut (X ⧸ aschbacherSolvableCore 3 X)).range := by
    by_contra h
    exact hout ⟨hx, h⟩
  obtain ⟨q, hq⟩ := hin
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 X) q
  refine ⟨y, y.2, fun l hl => ?_⟩
  have h1 := DFunLike.congr_fun hq ((⟨l, hl⟩ : X) : X ⧸ aschbacherSolvableCore 3 X)
  rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, QuotientGroup.mk'_apply,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    hθ, Subgroup.mem_bot, inv_mul_eq_one] at h1
  have h2 := congrArg Subtype.val h1
  rw [Sec4.compAction, Sec4.normalizerMonoidHom_apply_coe] at h2
  simpa using h2.symm

theorem mem_of_conj_eq [Finite G] {A X : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center X = ⊥) {x y : G}
    (hxA : x ∈ A) (hyX : y ∈ X) (hxy : ∀ l ∈ X, x * l * x⁻¹ = y * l * y⁻¹) : y ∈ A := by
  have hAe : IsElemAbelian 3 A := hA.prop
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hconj : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ l ∈ X, g * l * g⁻¹ ∈ X :=
    fun g hg l hl => (Subgroup.mem_normalizer_iff.mp hg l).mp hl
  have hpow : ∀ k : ℕ, ∀ l ∈ X, y ^ k * l * (y ^ k)⁻¹ = x ^ k * l * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro l _; simp
    | succ k ih =>
      intro l hl
      have hl' : x * l * x⁻¹ ∈ X := hconj x (hAN hxA) l hl
      calc y ^ (k + 1) * l * (y ^ (k + 1))⁻¹ = y ^ k * (y * l * y⁻¹) * (y ^ k)⁻¹ := by group
        _ = y ^ k * (x * l * x⁻¹) * (y ^ k)⁻¹ := by rw [hxy l hl]
        _ = x ^ k * (x * l * x⁻¹) * (x ^ k)⁻¹ := ih _ hl'
        _ = x ^ (k + 1) * l * (x ^ (k + 1))⁻¹ := by group
  have hy3 : y ^ 3 = 1 := eq_one_of_forall_conj_eq hZ (X.pow_mem hyX 3) fun l hl => by
    rw [hpow 3 l hl, hx3]
    group
  have hxy' : ∀ l ∈ X, y⁻¹ * l * y = x⁻¹ * l * x := by
    intro l hl
    have hl' : x⁻¹ * l * x ∈ X := by
      have := hconj x⁻¹ (Subgroup.inv_mem _ (hAN hxA)) l hl
      simpa using this
    have h1 := hxy _ hl'
    have h2 : x * (x⁻¹ * l * x) * x⁻¹ = l := by group
    rw [h2] at h1
    calc y⁻¹ * l * y = y⁻¹ * (y * (x⁻¹ * l * x) * y⁻¹) * y := by rw [← h1]
      _ = x⁻¹ * l * x := by group
  refine Sec4.mem_of_maximal_of_commute hA hy3 fun a ha => ?_
  have hax : a * x = x * a := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨x, hxA⟩)
  have hw : a * y * a⁻¹ * y⁻¹ ∈ X :=
    X.mul_mem (hconj a (hAN ha) y hyX) (X.inv_mem hyX)
  have hw1 := eq_one_of_forall_conj_eq hZ hw fun l hl => by
    have hl1 : y⁻¹ * l * y ∈ X := by
      have := hconj y⁻¹ (Subgroup.le_normalizer (X.inv_mem hyX)) l hl
      simpa using this
    have hl2 : a⁻¹ * (x⁻¹ * l * x) * a ∈ X := by
      have h1 : x⁻¹ * l * x ∈ X := by
        have := hconj x⁻¹ (Subgroup.inv_mem _ (hAN hxA)) l hl
        simpa using this
      have := hconj a⁻¹ (Subgroup.inv_mem _ (hAN ha)) _ h1
      simpa using this
    calc a * y * a⁻¹ * y⁻¹ * l * (a * y * a⁻¹ * y⁻¹)⁻¹ =
          a * (y * (a⁻¹ * (y⁻¹ * l * y) * a) * y⁻¹) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * (x⁻¹ * l * x) * a) * y⁻¹) * a⁻¹ := by rw [hxy' l hl]
      _ = a * (x * (a⁻¹ * (x⁻¹ * l * x) * a) * x⁻¹) * a⁻¹ := by rw [hxy _ hl2]
      _ = (a * x * a⁻¹) * x⁻¹ * l * x * (a * x⁻¹ * a⁻¹) := by group
      _ = l := by
          have h1 : a * x * a⁻¹ = x := by rw [hax, mul_inv_cancel_right]
          have h2 : a * x⁻¹ * a⁻¹ = x⁻¹ := by
            have h3 := congrArg (·⁻¹) h1
            simpa [mul_assoc] using h3
          rw [h1, h2]
          group
  calc a * y = a * y * a⁻¹ * y⁻¹ * (y * a) := by group
    _ = y * a := by rw [hw1, one_mul]

structure OneData [Finite G] (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) (m : ℕ) :
    Prop where
  one_lt : 1 < m
  odd : Odd m
  equiv : Nonempty (X ≃* projSU 4 2 m)
  kOf_equiv : Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m))
  theta_eq_bot : inSubgroup (aschbacherSolvableCore 3) X = ⊥
  center_eq_bot : Subgroup.center X = ⊥
  le_normalizer : A ≤ Subgroup.normalizer (X : Set G)
  center : ∃ a ∈ A, a ≠ 1 ∧ X ∈ thetaComponentsAt 3 a ∧
    A ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers a
  inner : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X
  decomp : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G)
  card_inf : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 3

end Item223PrintProof

open Item223PrintProof

variable {G : Type} [Group G]

@[expose] def Item223OneInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X → ∃ m : ℕ, 1 < m ∧ Odd m ∧
        Nonempty (X ≃* projSU 4 2 m) ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
        inSubgroup (aschbacherSolvableCore 3) X = ⊥ ∧
        (∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) ∧ Nat.card (A ⊓ X : Subgroup G) = 3 ^ 3 ∧
        Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3

end CFSG.RankThree.PartTwo.Sec21
