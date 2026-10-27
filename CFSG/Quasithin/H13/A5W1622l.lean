module

public import CFSG.Quasithin.H13.A5W1622f
public import CFSG.Quasithin.H13.A5W1622h
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.SL3Model (natAct3 natAct3_apply)

variable {F : Type} [Field F]

@[expose] def natActK (k : ℕ) :
    Matrix.SpecialLinearGroup (Fin 3) F →* MulAut (Multiplicative (Fin k → Fin 3 → F)) where
  toFun A :=
    { toFun := fun w => Multiplicative.ofAdd (fun i => A • Multiplicative.toAdd w i)
      invFun := fun w => Multiplicative.ofAdd (fun i => A⁻¹ • Multiplicative.toAdd w i)
      left_inv := fun w => by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      right_inv := fun w => by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        funext i
        simp [smul_add] }
  map_one' := by
    ext w i j
    simp
  map_mul' := fun A B => by
    ext w i j
    simp [mul_smul]

theorem natActK_apply (k : ℕ) (A : Matrix.SpecialLinearGroup (Fin 3) F)
    (w : Multiplicative (Fin k → Fin 3 → F)) (i : Fin k) :
    Multiplicative.toAdd (natActK k A w) i = A • Multiplicative.toAdd w i := rfl

theorem eq_smul_e0_of_fixed {v : Fin 3 → F} (h : ∀ A ∈ unitriangular 3 F, A • v = v) :
    v = v 0 • (Pi.single 0 1 : Fin 3 → F) := by
  obtain ⟨h1, h2⟩ := fixed_unitriangular h
  funext j
  fin_cases j
  · simp
  · simp [h1]
  · simp [h2]

theorem smul_e0_of_smul {A : Matrix.SpecialLinearGroup (Fin 3) F} {c : F} (hc : c ≠ 0)
    (h : A • (c • (Pi.single 0 1 : Fin 3 → F)) = c • (Pi.single 0 1 : Fin 3 → F)) :
    A • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 := by
  rw [smul_comm] at h
  exact smul_right_injective _ hc h

theorem modelFix_natK (k : ℕ) : ModelFix (natActK (F := F) k) (unitriangular 3 F) := by
  intro n p hn hp hnS hpS x hx
  have hfix : ∀ w : Multiplicative (Fin k → Fin 3 → F),
      (∀ s ∈ unitriangular 3 F, natActK k s w = w) → ∀ i,
        Multiplicative.toAdd w i = Multiplicative.toAdd w i 0 • (Pi.single 0 1 : Fin 3 → F) := by
    intro w hw i
    refine eq_smul_e0_of_fixed fun A hA => ?_
    have := congrArg (fun u : Multiplicative (Fin k → Fin 3 → F) => Multiplicative.toAdd u i)
      (hw A hA)
    simpa [natActK_apply] using this
  obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd n i 0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    apply Multiplicative.toAdd.injective
    funext i
    rw [hfix n hnS i, h i, zero_smul]
    rfl
  have hx0 : x • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 := by
    refine smul_e0_of_smul hi ?_
    have := congrArg (fun u : Multiplicative (Fin k → Fin 3 → F) => Multiplicative.toAdd u i) hx
    simp only [natActK_apply] at this
    rw [hfix n hnS i] at this
    exact this
  apply Multiplicative.toAdd.injective
  funext j
  rw [natActK_apply, hfix p hpS j, smul_comm, hx0]

theorem modelFix_natAct3 : ModelFix (natAct3 (F := F)) (unitriangular 3 F) := by
  intro n p hn hp hnS hpS x hx
  have hfix : ∀ w : SL3Model.W3 F, (∀ s ∈ unitriangular 3 F, natAct3 s w = w) →
      Multiplicative.toAdd w = Multiplicative.toAdd w 0 • (Pi.single 0 1 : Fin 3 → F) := by
    intro w hw
    refine eq_smul_e0_of_fixed fun A hA => ?_
    have := congrArg Multiplicative.toAdd (hw A hA)
    rwa [natAct3_apply, toAdd_ofAdd] at this
  have hn0 : Multiplicative.toAdd n 0 ≠ 0 := by
    intro h
    apply hn
    apply Multiplicative.toAdd.injective
    rw [hfix n hnS, h, zero_smul]
    rfl
  have hx0 : x • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 := by
    refine smul_e0_of_smul hn0 ?_
    have := congrArg Multiplicative.toAdd hx
    rw [natAct3_apply, toAdd_ofAdd, hfix n hnS] at this
    exact this
  apply Multiplicative.toAdd.injective
  rw [natAct3_apply, toAdd_ofAdd, hfix p hpS, smul_comm, hx0]

theorem fixed_eq_zero_of_sl3 {v : Fin 3 → F}
    (h : ∀ A : Matrix.SpecialLinearGroup (Fin 3) F, A • v = v) : v = 0 := by
  have key : ∀ i j : Fin 3, i ≠ j → v j = 0 := by
    intro i j hij
    have h1 := h (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [SL3Model.transvection_smul, one_mul, add_eq_left, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd (congrFun h1 i) (by simp)
  funext j
  fin_cases j
  · exact key 1 0 (by decide)
  · exact key 0 1 (by decide)
  · exact key 0 2 (by decide)

section Block

variable {G : Type} [Group G]

theorem coe_symm_statedSL {K₀ : Subgroup G}
    (α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (ℓ : ↥K₀) :
    (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm (α ℓ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((α ℓ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  set g := e.symm (α ℓ) with hg
  have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F g
  have h2 : e g = α ℓ := e.apply_symm_apply _
  rw [← h2]
  exact h.symm

end Block

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_sumNatural (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    {M : Subgroup G} {F : Type} [Field F] [Fintype F] {n : ℕ} (hFn : Fintype.card F = 2 ^ n)
    {α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj K₀ α) {k : ℕ}
    (hM : IsSumOfNaturalModulesVia K₀ M ⊥ α false k)
    (hcommA : ∀ x ∈ K₀, x⁻¹ * S.a * x * S.a⁻¹ ∈ M) (he2M : S.e2 ∈ M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := n)
    (by rw [Nat.card_eq_fintype_card, hFn])
  obtain ⟨hKM, -, β, -, hβk, hβe⟩ := hM
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hN2 : ∀ w : Multiplicative (Fin k → Fin 3 → F), w ^ 2 = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i j
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((2 : ℕ) : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]
  have hA2 : ∀ x ∈ M, x ^ 2 = 1 := by
    intro x hx
    have h := hN2 (β ⟨x, hx⟩)
    rw [← map_pow] at h
    have h1 : (⟨x, hx⟩ : ↥M) ^ 2 = 1 := hβinj (h.trans (map_one β).symm)
    exact congrArg Subtype.val h1
  have hAc : ∀ x ∈ M, ∀ x' ∈ M, x * x' = x' * x := by
    intro x hx x' hx'
    have h : β (⟨x, hx⟩ * ⟨x', hx'⟩) = β (⟨x', hx'⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (hβinj h)
  have hlA : ∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ M := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hKM (hLvK₀ hy)) _).mp he2M
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let α' : ↥K₀ →* Matrix.SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α
  have hα' : Function.Surjective α' := e.symm.surjective.comp hα.1
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥M), (v : G) = ℓ * u * ℓ⁻¹ →
      β v = natActK k (α' ℓ) (β u) := by
    intro ℓ u v h
    apply Multiplicative.toAdd.injective
    funext i
    rw [natActK_apply, hβe ℓ u v h i]
    change _ = ((α' ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _
    rw [show α' ℓ = e.symm (α ℓ) from rfl, coe_symm_statedSL]
    rfl
  exact S.false_of_closing_model h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ hKM (Zc := ⊥) bot_le hA2 hAc hcommA he2M hlA hN2 (natActK k)
    (SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num)) (modelFix_natK k) α' hα'
    β (by rw [hβk]) hβe'

theorem false_of_sl3Block_gen (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsSL3Block K₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, n, F, _, _, hFn, α, hα, -, β, hβ, hβk, hβe⟩ := hblk
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := n)
    (by rw [Nat.card_eq_fintype_card, hFn])
  obtain ⟨hcommA, he2U, hlA, hU2, hUc⟩ :=
    S.closing_data_blockU h1222 h517 hK₀G hK₀ hTK₀ hLvK₀ hchar hshort
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let α' : ↥K₀ →* Matrix.SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α
  have hα' : Function.Surjective α' := e.symm.surjective.comp hα
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      β v = natAct3 (α' ℓ) (β u) := by
    intro ℓ u v h
    rw [natAct3_apply]
    apply Multiplicative.toAdd.injective
    rw [hβe ℓ u v h, toAdd_ofAdd]
    change _ = ((α' ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _
    rw [show α' ℓ = e.symm (α ℓ) from rfl, coe_symm_statedSL]
  have hN2 : ∀ w : SL3Model.W3 F, w ^ 2 = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((2 : ℕ) : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]
  exact S.false_of_closing_model h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ (C1.le_normalizer_blockU K₀) (Zc := blockZ K₀) inf_le_right hU2 hUc hcommA
    he2U hlA hN2 natAct3 (SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num))
    modelFix_natAct3 α' hα' β hβk hβe'

end Setting

end CFSG.Quasithin.H13.A5
