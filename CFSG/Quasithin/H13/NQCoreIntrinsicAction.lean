module

public import CFSG.Quasithin.H13.NQCoreIntrinsicActionStmt
public import CFSG.Quasithin.H13.NQCoreCanonicalResidual
public import CFSG.Quasithin.H13.NQCoreEscapingBasic
public import CFSG.Quasithin.SteinbergCDOddPlaneRankFourFive
public import CFSG.Quasithin.SteinbergBQFivePlaneSupports

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Module
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergBQ (commSpan)
open CFSG.Quasithin.SteinbergCD (glFixedSpace)
open scoped IsMulCommutative

section BinaryAction

variable {Q : Type*} [Group Q] (V : Subgroup Q) [V.Normal] [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)]

@[expose] noncomputable def autLinearEquiv (σ : MulAut ↥V) : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V :=
  (MulEquiv.toAdditive σ).toLinearEquiv fun c x =>
    ZMod.map_smul (MulEquiv.toAdditive σ).toAddMonoidHom c x

@[expose] noncomputable def mulAutToGL :
    MulAut ↥V →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V) where
  toFun σ := LinearMap.GeneralLinearGroup.ofLinearEquiv (autLinearEquiv V σ)
  map_one' := by
    apply Units.ext
    ext x
    rfl
  map_mul' σ τ := by
    apply Units.ext
    ext x
    rfl

@[expose] noncomputable def conjGL : Q →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V) :=
  (mulAutToGL V).comp MulAut.conjNormal

theorem conjGL_apply (g : Q) (v : ↥V) :
    ((conjGL V g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) :
      Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul v) =
      Additive.ofMul (MulAut.conjNormal g v) :=
  rfl

end BinaryAction

@[expose] def StmtWholeModuleComparison : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M D X : Subgroup G) (p : ℕ),
    QTTMaxNQPrime T L M D p X → ⁅NQBlock.omegaOneCenterOf 2 (pCoreOf 2 X), X⁆ ≠ ⊥ →
    ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆ ≠ ⊥ ∧
    (∀ v ∈ ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆, v ^ 2 = 1) ∧
    T.subgroupOf (X ⊔ T) ⊓
        centralizer ((⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆ :
          Subgroup ↥(X ⊔ T)) : Set ↥(X ⊔ T)) =
      CFSG.pCore 2 ↥(X ⊔ T) ∧
    ∃ _ : (⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).Normal,
    ∃ _ : IsMulCommutative ↥⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆,
    ∀ [Module (ZMod 2) (Additive ↥⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)],
      Group.IsSolvable ↥(conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).range ∧
      CFSG.pCore 2 ↥(conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).range = ⊥ ∧
      ¬ 3 ∣ Nat.card (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).range ∧
      ∃ _ : (((X.subgroupOf (X ⊔ T)).map
          (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)).subgroupOf
        (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).range).Normal,
      IsPGroup 2 (↥(conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).range ⧸
        ((X.subgroupOf (X ⊔ T)).map
          (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)).subgroupOf
        (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).range) ∧
      ((IsElementaryAbelian p ↥((X.subgroupOf (X ⊔ T)).map
          (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) ∧
        Nat.card ((X.subgroupOf (X ⊔ T)).map
          (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) = p ^ 2) ∨
        ((∃ x y : ↥((X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)), x * y ≠ y * x) ∧
          Nat.card ((X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) = p ^ 3 ∧
          ∀ x : ↥((X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)), x ^ p = 1)) ∧
      commSpan ((X.subgroupOf (X ⊔ T)).map
        (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) = ⊤ ∧
      (IsElementaryAbelian p ↥((X.subgroupOf (X ⊔ T)).map
          (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) →
        ∀ P' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive ↥⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)),
          P' ≤ (X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆) →
          (∀ g ∈ (T.subgroupOf (X ⊔ T)).map
              (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆),
            ∀ x ∈ P', g * x * g⁻¹ ∈ P') →
          P' = ⊥ ∨ P' = (X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) ∧
      ∃ φ : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive ↥⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆),
        (∀ x ∈ (X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆),
          φ * x * φ⁻¹ ∈ (X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆)) ∧
        ∀ k : ℕ, ¬ ∀ x ∈ (X.subgroupOf (X ⊔ T)).map
            (conjGL ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆),
          φ ^ 2 ^ k * x = x * φ ^ 2 ^ k

@[expose] def StmtOriginalRadicalEscape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    Group.IsSolvable ↥((CFSG.solvableRadical ↥L).map L.subtype ⊔ T) ∧
    T ≤ (CFSG.solvableRadical ↥L).map L.subtype ⊔ T ∧
    (CFSG.solvableRadical ↥L).map L.subtype ⊔ T ≤ M ∧
    pCoreOf 2 M ≠ ⊥ ∧ pCoreOf 2 M ≤ pCoreOf 2 ((CFSG.solvableRadical ↥L).map L.subtype ⊔ T) ∧
    (∀ J : Subgroup G, quasithinIsMaxTwoLocal J → T ≤ J → J ≠ M →
      ¬ (CFSG.solvableRadical ↥L).map L.subtype ≤ J ∧
      ¬ (CFSG.solvableRadical ↥L).map L.subtype ⊔ T ≤ J) ∧
    ∀ (p₀ : ℕ) (X₀ : Subgroup G), p₀.Prime → 5 ≤ p₀ →
      X₀ ≤ (CFSG.solvableRadical ↥L).map L.subtype → (X₀.subgroupOf L).Characteristic →
      CFSG.pCore 2 X₀ ≠ ⊥ → NoPQuotient 2 X₀ → IsPGroup p₀ (X₀ ⧸ CFSG.pCore 2 X₀) →
      Monoid.exponent (X₀ ⧸ CFSG.pCore 2 X₀) = p₀ → CFSG.pRank p₀ (X₀ ⧸ CFSG.pCore 2 X₀) = 2 →
      Nat.card ((X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)) = p₀ ^ 2 →
      (∃ l : normalizer (X₀ : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X₀ l ≠ 1) →
      (∀ W : Subgroup ((X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)),
        (∀ l : normalizer (X₀ : Set G), (l : G) ∈ L → ∀ w ∈ W, normalizerFrattiniConj X₀ l w ∈ W) →
        W = ⊥ ∨ W = ⊤) →
      U3.UniqueMaxTwoLocal (X₀ ⊔ T) M ∧
        ∀ J : Subgroup G, quasithinIsMaxTwoLocal J → T ≤ J → J ≠ M → ¬ X₀ ⊔ T ≤ J

@[expose] def StmtSolvableFixedSpaceWitness : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G →
    CFSG.Assembly.evenRank G ≤ 2 → ∀ (T F J : Subgroup G), quasithinIsSylowTwo T → T ≤ F →
    U3.UniqueMaxTwoLocal F J →
    ∀ (V : Subgroup ↥F) [V.Normal] [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)],
      V ≠ ⊥ → (∀ v ∈ V, v ^ 2 = 1) → V.map F.subtype ≤ pCoreOf 2 J →
      ((T ⊓ centralizer (V.map F.subtype : Set G)).subgroupOf F).Normal →
      Group.IsSolvable ↥(conjGL V).range → CFSG.pCore 2 ↥(conjGL V).range = ⊥ →
      ¬ 3 ∣ Nat.card (conjGL V).range →
      (∃ S : Subgroup G, Group.IsSolvable ↥S ∧ T ≤ S ∧ pCoreOf 2 S ≠ ⊥ ∧ ¬ S ≤ J) →
      ∃ A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
        A ≤ (T.subgroupOf F).map (conjGL V) ∧ IsElementaryAbelian 2 ↥A ∧ A ≠ ⊥ ∧
        ∃ r : ℕ, Nat.card A = 2 ^ r ∧
          finrank (ZMod 2) (Additive ↥V ⧸ glFixedSpace A) ≤ 2 * r

theorem pow_four_commute_of_normalizes_card_five {K : Type*} [Group K] {Q : Subgroup K}
    (hQ : Nat.card Q = 5) {ψ : K} (hψ : ∀ x ∈ Q, ψ * x * ψ⁻¹ ∈ Q) :
    ∀ x ∈ Q, ψ ^ 4 * x = x * ψ ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic Q := isCyclic_of_prime_card hQ
  set σ : Q →* Q :=
    { toFun := fun x => ⟨ψ * x * ψ⁻¹, hψ x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] } with hσ
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  have h5 : ∀ x : Q, x ^ (5 : ℕ) = 1 := fun x => by rw [← hQ]; exact pow_card_eq_one'
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  have hpow : ∀ n : ℕ, ∀ x : Q, ψ ^ n * (x : K) * (ψ ^ n)⁻¹ = ((x ^ (m ^ n) : Q) : K) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have h1 : ψ ^ (n + 1) * (x : K) * (ψ ^ (n + 1))⁻¹ =
          ψ * (ψ ^ n * (x : K) * (ψ ^ n)⁻¹) * ψ⁻¹ := by group
      rw [h1, ih x]
      have h2 := congrArg Subtype.val (hm (x ^ (m ^ n)))
      simp only [hσ, MonoidHom.coe_mk, OneHom.coe_mk] at h2
      rw [h2, ← zpow_mul, pow_succ]
  have hm5 : ¬ (5 : ℤ) ∣ m := by
    rintro ⟨k, hk⟩
    obtain ⟨g, hg⟩ := exists_ne (1 : Q)
    have h1 : σ g = 1 := by
      rw [hm, hk, zpow_mul]
      have : g ^ (5 : ℤ) = 1 := by rw [zpow_ofNat]; exact h5 g
      rw [this, one_zpow]
    apply hg
    have h2 := congrArg Subtype.val h1
    simp only [hσ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h2
    apply Subtype.ext
    have h3 : (g : K) = ψ⁻¹ * (ψ * g * ψ⁻¹) * ψ := by group
    rw [h3, h2]
    simp
  have hm4 : ∀ x : Q, x ^ (m ^ 4) = x := by
    intro x
    have hmod : m ^ 4 % 5 = 1 := by
      have h4 := ((Int.mod_modEq m 5).symm).pow 4
      have h1 : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
      unfold Int.ModEq at h4
      rcases h1 with h | h | h | h <;> rw [h] at h4 <;> norm_num at h4 <;> exact h4
    have hx5 : x ^ (5 : ℤ) = 1 := by rw [zpow_ofNat]; exact h5 x
    rw [← Int.emod_add_mul_ediv (m ^ 4) 5, hmod, zpow_add, zpow_one, zpow_mul, hx5, one_zpow,
      mul_one]
  intro x hx
  have h1 := hpow 4 ⟨x, hx⟩
  rw [hm4] at h1
  have h2 : ψ ^ 4 * x = ψ ^ 4 * x * (ψ ^ 4)⁻¹ * ψ ^ 4 := by group
  rw [h2, h1]

theorem stmtIntrinsicActionExclusion_of
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) (hi : StmtWholeModuleComparison)
    (hii : StmtOriginalRadicalEscape) (hiii : StmtSolvableFixedSpaceWitness) :
    StmtIntrinsicActionExclusion := by
  intro G _ _ T L M D X p hX hJM hU
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h := hX.qtnq
  obtain ⟨hA, -⟩ := SNCanonical.of_qtTMaxNQPrime hA7u hA7n hX
  obtain ⟨hV1, hV2, hCR, hVn, hVc, hGL⟩ := hi G T L M D X p hX hne
  set V := ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆ with hVdef
  let _ : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← sq]
    exact Subtype.ext (hV2 _ x.toMul.2)
  obtain ⟨hsolv, hO2, h3, hPn, hΓP, hshape, hspan, hirr, hexcl⟩ := hGL
  obtain ⟨hSsolv, hTS, -, hO2M, hMS, hesc, -⟩ := hii G T L M h
  have hJmax := hU.1
  have hTJ : T ≤ normalizer (D : Set G) := hX.le_normalizer
  have hSJ := (hesc _ hJmax hTJ hJM).2
  have hO2S : pCoreOf 2 ((CFSG.solvableRadical ↥L).map L.subtype ⊔ T) ≠ ⊥ := fun hb =>
    hO2M (le_bot_iff.mp (hb ▸ hMS))
  have hEJ : X ⊔ T ≤ normalizer (D : Set G) := hU.2.1
  have hJT : pCoreOf 2 (normalizer (D : Set G)) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowIn_of_quasithin h.sylow hTJ)
  have hJE : pCoreOf 2 (normalizer (D : Set G)) ≤ pCoreOf 2 (X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hJT.trans le_sup_right)
      (hEJ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hEmap : pCoreOf 2 (X ⊔ T) = (CFSG.pCore 2 ↥(X ⊔ T)).map (X ⊔ T).subtype := by
    rw [pCoreOf]
  have hVJ : V.map (X ⊔ T).subtype ≤ pCoreOf 2 (normalizer (D : Set G)) := by
    refine fun v hv => hA.charTwo_normalizer (mem_inf.mpr ⟨hEJ (map_subtype_le _ hv), ?_⟩)
    obtain ⟨w, hw, rfl⟩ := hv
    rw [mem_centralizer_iff]
    intro r hr
    have h1 := hJE hr
    rw [hEmap, ← hCR] at h1
    obtain ⟨r', hr', rfl⟩ := h1
    exact (congrArg Subtype.val (mem_centralizer_iff.mp (mem_inf.mp hr').2 w hw)).symm
  have hRn : ((T ⊓ centralizer (V.map (X ⊔ T).subtype : Set G)).subgroupOf (X ⊔ T)).Normal := by
    have h1 : (T ⊓ centralizer (V.map (X ⊔ T).subtype : Set G)).subgroupOf (X ⊔ T) =
        CFSG.pCore 2 ↥(X ⊔ T) := by
      rw [← hCR]
      ext x
      simp only [mem_subgroupOf, mem_inf, mem_centralizer_iff]
      refine and_congr_right fun _ => ⟨fun hx v hv => Subtype.ext (hx _ ⟨v, hv, rfl⟩), ?_⟩
      rintro hx _ ⟨v, hv, rfl⟩
      exact congrArg Subtype.val (hx v hv)
    rw [h1]
    exact CFSG.pCore_normal
  obtain ⟨A, hAT, hAel, hA1, r, hr, hcod⟩ := hiii G h.qtke.2.1 h.qtke.2.2 T (X ⊔ T)
    (normalizer (D : Set G)) h.sylow le_sup_right hU V hV1 hV2 hVJ hRn hsolv hO2 h3
    ⟨_, hSsolv, hTS, hO2S, hSJ⟩
  have : Finite (Additive ↥V) := inferInstanceAs (Finite ↥V)
  have : FiniteDimensional (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have : IsElementaryAbelian 2 ↥A := hAel
  have hPΓ : (X.subgroupOf (X ⊔ T)).map (conjGL V) ≤ (conjGL V).range := map_le_range _ _
  have hTΓ : (T.subgroupOf (X ⊔ T)).map (conjGL V) ≤ (conjGL V).range := map_le_range _ _
  obtain ⟨hp5, hPel, hP25, Q, hQP, hQ5, hQ4⟩ :=
    SteinbergCD.odd_plane_two_action_bound_rank_four_five_support hX.prime hX.five_le hO2 hPΓ
      hPn hΓP hshape hspan (hAT.trans hTΓ) hA1 hr hcod
  subst hp5
  have : IsElementaryAbelian 5 ↥((X.subgroupOf (X ⊔ T)).map (conjGL V)) := hPel
  obtain ⟨P₁, P₂, hP12, hiff, -, hsup, -⟩ :=
    SteinbergBQ.irreducibly_normalized_five_plane_rank_four_supports_fill_whole_module
      (conjGL V).range ((X.subgroupOf (X ⊔ T)).map (conjGL V)) hPΓ hPn hP25 hspan
      (fun P' hP' hinv => hirr hPel P' hP' fun g hg x hx => hinv g (hTΓ hg) x hx)
      ⟨Q, hQP, hQ5, hQ4⟩
  obtain ⟨φ, hφP, hφ2⟩ := hexcl
  have hfam : ∀ Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
      (Q' ≤ (X.subgroupOf (X ⊔ T)).map (conjGL V) ∧ Nat.card Q' = 5 ∧
        finrank (ZMod 2) (commSpan Q') = 4) →
      (Q'.map (MulAut.conj φ).toMonoidHom = P₁ ∨ Q'.map (MulAut.conj φ).toMonoidHom = P₂) := by
    rintro Q' ⟨hQ'P, hQ'5, hQ'4⟩
    refine (hiff _).mp ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hφP x (hQ'P hx)
    · rw [Subgroup.card_map_of_injective (MulAut.conj φ).injective, hQ'5]
    · rw [SteinbergBQ.commSpan_map_conj]
      exact (LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.toLinearEquiv φ)
        (commSpan Q')).trans hQ'4
  have h₁ := hfam P₁ ((hiff P₁).mpr (Or.inl rfl))
  have h₂ := hfam P₂ ((hiff P₂).mpr (Or.inr rfl))
  have hne : P₁.map (MulAut.conj φ).toMonoidHom ≠ P₂.map (MulAut.conj φ).toMonoidHom :=
    fun h' => hP12 (Subgroup.map_injective (MulAut.conj φ).injective h')
  have hsq : ∀ Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
      (Q' = P₁ ∨ Q' = P₂) → Q'.map (MulAut.conj (φ ^ 2)).toMonoidHom = Q' := by
    have hmm : ∀ Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
        Q'.map (MulAut.conj (φ ^ 2)).toMonoidHom =
          (Q'.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj φ).toMonoidHom := fun Q' => by
      rw [Subgroup.map_map, map_pow, pow_two]
      rfl
    rintro Q' (h' | h') <;> rw [h', hmm]
    · rcases h₁ with h₁ | h₁
      · rw [h₁, h₁]
      · rcases h₂ with h₂ | h₂
        · rw [h₁, h₂]
        · exact absurd (h₁.trans h₂.symm) hne
    · rcases h₂ with h₂ | h₂
      · rcases h₁ with h₁ | h₁
        · exact absurd (h₁.trans h₂.symm) hne
        · rw [h₂, h₁]
      · rw [h₂, h₂]
  have hcent : ∀ Q' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
      (Q' = P₁ ∨ Q' = P₂) → ∀ x ∈ Q', φ ^ 2 ^ 3 * x = x * φ ^ 2 ^ 3 := by
    intro Q' hQ' x hx
    have h5 : Nat.card Q' = 5 := by
      rcases hQ' with h' | h'
      · rw [h']
        exact ((hiff P₁).mpr (Or.inl rfl)).2.1
      · rw [h']
        exact ((hiff P₂).mpr (Or.inr rfl)).2.1
    have hN : ∀ y ∈ Q', φ ^ 2 * y * (φ ^ 2)⁻¹ ∈ Q' := fun y hy => by
      rw [← hsq Q' hQ']
      exact ⟨y, hy, rfl⟩
    have h1 := pow_four_commute_of_normalizes_card_five h5 hN x hx
    rwa [← pow_mul] at h1
  refine hφ2 3 fun x hx => ?_
  have hxP : x ∈ P₁ ⊔ P₂ := hsup ▸ hx
  have hle : P₁ ⊔ P₂ ≤ centralizer ({φ ^ 2 ^ 3} : Set _) := by
    refine sup_le (fun y hy => ?_) fun y hy => ?_
    · rw [mem_centralizer_singleton_iff]
      exact (hcent P₁ (Or.inl rfl) y hy).symm
    · rw [mem_centralizer_singleton_iff]
      exact (hcent P₂ (Or.inr rfl) y hy).symm
  exact (mem_centralizer_singleton_iff.mp (hle hxP)).symm

end CFSG.Quasithin.H13.NQCore
