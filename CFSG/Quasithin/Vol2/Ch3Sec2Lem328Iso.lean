module

public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Matrix

section Faithful

variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}

theorem nonempty_mulEquiv_of_realizesVia {D : FFModel} (hD : D.Faithful) {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) : Nonempty (↥H ≃* D.Gam) :=
  ⟨(MulEquiv.ofBijective π ⟨h.injective_of_faithful hD, h.1⟩).symm⟩

end Faithful

section Zorn

variable {F : Type} [Field F]

theorem zornMul_self_eq_zero {u v : Fin 3 → F} (huv : u = 0 ∨ v = 0) :
    quasithinZornMul ((0, u, v, 0) : quasithinZorn F) (0, u, v, 0) = 0 := by
  rw [zornMul_self]
  rcases huv with rfl | rfl <;> simp

theorem eq_one_of_isZornAuto {g : quasithinZorn F ≃ₗ[F] quasithinZorn F} (hg : IsZornAuto g)
    (h : ∀ x : quasithinZorn F, x.1 + x.2.2.2 = 0 → ∃ c : F, g x - x = (c, 0, 0, c)) :
    g = 1 := by
  have hfix : ∀ u v : Fin 3 → F, (u = 0 ∨ v = 0) →
      g ((0, u, v, 0) : quasithinZorn F) = (0, u, v, 0) := by
    intro u v huv
    obtain ⟨c, hc⟩ := h (0, u, v, 0) (by simp)
    have hgx : g ((0, u, v, 0) : quasithinZorn F) = (c, u, v, c) := by
      rw [← sub_add_cancel (g _) ((0, u, v, 0) : quasithinZorn F), hc]
      simp
    have h1 := hg (0, u, v, 0) (0, u, v, 0)
    rw [zornMul_self_eq_zero huv, map_zero, hgx, zornMul_self] at h1
    have h2 := congrArg Prod.fst h1
    have hcc : c * c = 0 := by
      rcases huv with rfl | rfl <;> simpa using h2.symm
    rw [hgx, mul_self_eq_zero.1 hcc]
  set e : Fin 3 → F := ![1, 0, 0] with he
  have hE1 : g ((1, 0, 0, 0) : quasithinZorn F) = (1, 0, 0, 0) := by
    have hprod : quasithinZornMul ((0, e, 0, 0) : quasithinZorn F) (0, 0, e, 0) = (1, 0, 0, 0) := by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [quasithinZornMul, he, Fin.sum_univ_three]
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross, he]
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross, he]
      · simp [quasithinZornMul, he]
    rw [← hprod, hg, hfix e 0 (Or.inr rfl), hfix 0 e (Or.inl rfl)]
  have hE4 : g ((0, 0, 0, 1) : quasithinZorn F) = (0, 0, 0, 1) := by
    have hsum : ((0, 0, 0, 1) : quasithinZorn F) = zornOne - (1, 0, 0, 0) := by
      simp [zornOne]
    rw [hsum, map_sub, hg.map_one, hE1]
  refine LinearEquiv.ext fun z => ?_
  obtain ⟨a, u, v, b⟩ := z
  have hz : ((a, u, v, b) : quasithinZorn F) = a • ((1, 0, 0, 0) : quasithinZorn F) +
      (0, u, 0, 0) + (0, 0, v, 0) + b • ((0, 0, 0, 1) : quasithinZorn F) := by
    simp
  rw [hz, map_add, map_add, map_add, map_smul, map_smul, hE1, hE4, hfix u 0 (Or.inr rfl),
    hfix 0 v (Or.inl rfl)]
  rfl

theorem zornQ_faithful {Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)}
    (hΓ : Γ ≤ quasithinG2 F) : (FFModel.zornQ Γ).Faithful := by
  intro γ hγ
  apply Subtype.ext
  refine eq_one_of_isZornAuto (mem_quasithinG2_isZornAuto (hΓ γ.2)) fun x hx => ?_
  obtain ⟨c, hc⟩ := hγ (Multiplicative.ofAdd x) hx
  change Multiplicative.toAdd (zornAct Γ γ (Multiplicative.ofAdd x) * (Multiplicative.ofAdd x)⁻¹) =
    (c, 0, 0, c) at hc
  exact ⟨c, by simpa [zornAct, sub_eq_add_neg] using hc⟩

end Zorn

theorem altLift7_injective : Function.Injective altLift7 := by
  intro σ τ hστ
  have h1 := congrArg Subtype.val hστ
  apply Subtype.ext
  exact Equiv.Perm.viaEmbeddingHom_injective _ h1

theorem a7Four_faithful
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    (FFModel.a7Four α).Faithful := by
  intro σ hσ
  have h1 : (⟨α (altLift7 σ), Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)))) = 1 :=
    natAct_faithful ⊤ _ fun m => Subgroup.mem_bot.1 (hσ m trivial)
  have h2 : α (altLift7 σ) = 1 := congrArg Subtype.val h1
  rw [MulEquiv.map_eq_one_iff] at h2
  exact altLift7_injective (h2.trans (map_one altLift7).symm)

section SL

variable {n : ℕ}

@[expose] noncomputable def slCongr {ι : Type*} [Fintype ι] [DecidableEq ι] {K K' : Type*}
    [CommRing K] [CommRing K'] (ε : K ≃+* K') :
    Matrix.SpecialLinearGroup ι K ≃* Matrix.SpecialLinearGroup ι K' :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ε.toRingHom)
    (Matrix.SpecialLinearGroup.map ε.symm.toRingHom)
    (by ext A i j; simp) (by ext A i j; simp)

@[expose] noncomputable def ringEquivZModTwo {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) : K ≃+* ZMod 2 :=
  have : Fintype K := Fintype.ofFinite K
  (ZMod.ringEquivOfPrime K Nat.prime_two (by rw [← Nat.card_eq_fintype_card, hK])).symm

@[expose] noncomputable def statedSLEquivZModTwo {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : ↥(StatedSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (specialLinearGroupEquivStatedSL n K).symm.trans (slCongr (ringEquivZModTwo hK))

theorem center_sl_eq_bot {K : Type*} [Field K] (h : ∀ r : K, r ^ n = 1 → r = 1) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hA', h r hr]
  simp [Matrix.one_apply]

theorem isSimpleGroup_sl_zmodTwo (hn : 3 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n)
    (by omega) (Or.inl hn)
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ :=
    center_sl_eq_bot fun r hr => by
      have hn0 : n ≠ 0 := by omega
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) r with h0 | h1
      · rw [h0, zero_pow hn0] at hr
        exact absurd hr zero_ne_one
      · exact h1
  let e : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact e.isSimpleGroup

theorem injective_of_statedSL_zmodTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hn : 3 ≤ n) {X : Type*} [Group X] [Nontrivial X] {π : ↥(StatedSL n K) →* X}
    (hπ : Function.Surjective π) : Function.Injective π := by
  have := isSimpleGroup_sl_zmodTwo hn
  let e := statedSLEquivZModTwo (n := n) hK
  have : IsSimpleGroup ↥(StatedSL n K) := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).1 h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨y, rfl⟩ := hπ x
    exact hx ((MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top y))

end SL

section PSL2

theorem statedScalars_subgroupOf_eq_bot {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

theorem lieModel_psl_two_of_mulEquiv {X : Type} [Group X] [Nontrivial X] (hX : Group.IsPerfect X)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (e : X ≃* ↥(StatedSL 2 K)) : LieModel X .PSL 2 2 n := by
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [hK, pow_zero] at hK1
      omega
    · exact h
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    subst hn
    rw [pow_one] at hK
    let f := e.trans (statedSLEquivZModTwo (n := 2) hK)
    have hcard : Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 2 ^ 1 * 3 ^ 1 := by
      decide
    have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) hcard
    have : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom)
      f.injective
    have : Group.IsPerfect X := hX
    exact Group.IsPerfect.not_isSolvable X inferInstance
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hn1, le_rfl, ?_, ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨e.trans ?_⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    have : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    rw [‹2 ^ n = 3›] at this
    exact absurd this (by decide)
  · exact (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_eq_bot.symm))

end PSL2

@[expose] noncomputable def topBotEquiv (A : Type*) [Group A] :
    ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf ⊤)).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

theorem topBotEquiv_mk {A : Type*} [Group A] (m : ↥(⊤ : Subgroup A)) :
    topBotEquiv A (QuotientGroup.mk m) = (m : A) :=
  rfl

section Card

variable {V : Type*} [CommGroup V]

theorem card_eq_of_realizesVia_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    Nat.card U = Nat.card (ι → K) * Nat.card Z := by
  obtain ⟨-, hZU, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have h1 : Nat.card (↥U ⧸ β.ker) = Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv
  have h2 : Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) = Nat.card (ι → K) :=
    Nat.card_congr (topBotEquiv (Multiplicative (ι → K))).toEquiv
  have h3 : Nat.card ↥(Z.subgroupOf U) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker, h1, h2, hker, h3]

end Card

section NaturalTwo

variable {V : Type*} [CommGroup V]

theorem eq_top_of_binaryNaturalSL_one {H : Subgroup (MulAut V)} {n : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ n 1) : H = ⊤ := by
  obtain ⟨K, _, _, hK, π, -, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  rw [pow_one] at hK
  have hK01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    set ε := ringEquivZModTwo hK
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases h2 (ε c) with h0 | h1
    · exact Or.inl (ε.injective (h0.trans (map_zero ε).symm))
    · exact Or.inr (ε.injective (h1.trans (map_one ε).symm))
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let b : V ≃* Multiplicative (Fin n → K) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans (topBotEquiv _))
  have hb : ∀ v : V, topBotEquiv _ (β ⟨v, trivial⟩) = b v := fun v => rfl
  have hbe : ∀ (γ : ↥(StatedSL n K)) (v : V),
      b (((π γ : ↥H) : MulAut V) v) = natAct (StatedSL n K) γ (b v) := by
    intro γ v
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk
        (⟨b v, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (Fin n → K)))) := by
      apply (topBotEquiv _).injective
      exact hb v
    have h2 := congrArg (topBotEquiv _) (hβe γ ⟨v, trivial⟩ ⟨b v, trivial⟩ trivial trivial h1)
    exact (hb _).symm.trans h2
  rw [eq_top_iff]
  intro φ _
  let f : Multiplicative (Fin n → K) ≃* Multiplicative (Fin n → K) := b.symm.trans (φ.trans b)
  let E : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    { toFun := fun x => Multiplicative.toAdd (f (Multiplicative.ofAdd x))
      invFun := fun x => Multiplicative.toAdd (f.symm (Multiplicative.ofAdd x))
      map_add' := fun x y => by
        simp only [ofAdd_add, map_mul]
        rfl
      map_smul' := fun c x => by
        rcases hK01 c with rfl | rfl
        · simp only [zero_smul, ofAdd_zero, map_one, toAdd_one, RingHom.id_apply]
        · simp only [one_smul, RingHom.id_apply]
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  set M : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' (E : (Fin n → K) →ₗ[K] (Fin n → K))
  set M' : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (E.symm : (Fin n → K) →ₗ[K] (Fin n → K))
  have hMM' : M * M' = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (E : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (E.symm : (Fin n → K) →ₗ[K] (Fin n → K)) =
        LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hM'M : M' * M = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (E.symm : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (E : (Fin n → K) →ₗ[K] (Fin n → K)) =
        LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  let g : Matrix.GeneralLinearGroup (Fin n) K := ⟨M, M', hMM', hM'M⟩
  have hdet : (M : Matrix (Fin n) (Fin n) K).det = 1 := by
    rcases hK01 M.det with h0 | h1
    · exfalso
      have := congrArg Matrix.det hMM'
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    · exact h1
  have hg : g ∈ StatedSL n K := Subgroup.subset_closure hdet
  have hφ : ((π ⟨g, hg⟩ : ↥H) : MulAut V) = φ := by
    refine MulEquiv.ext fun v => b.injective ?_
    rw [hbe]
    show Multiplicative.ofAdd (M.mulVec (Multiplicative.toAdd (b v))) = b (φ v)
    rw [LinearMap.toMatrix'_mulVec]
    show Multiplicative.ofAdd (Multiplicative.toAdd (f (Multiplicative.ofAdd
      (Multiplicative.toAdd (b v))))) = b (φ v)
    simp [f]
  rw [← hφ]
  exact (π ⟨g, hg⟩).2

end NaturalTwo

theorem isHat_parts_of_mulEquiv {X Y S : Type} [Group X] [Group Y] [Group S] (e : X ≃* Y)
    (h : IsHat Y S) : Group.IsPerfect X ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty (X ⧸ Subgroup.center X ≃* S) := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hmap : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := e.surjective z
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hx w]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      rw [Subgroup.mem_center_iff] at hy
      intro z
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (e z)]
  have : Group.IsPerfect Y := hq.1
  refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_,
    ⟨(QuotientGroup.congr _ _ e hmap).trans f⟩⟩
  rw [← hc]
  exact Nat.card_congr ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)).toEquiv

end CFSG.Quasithin.H13
