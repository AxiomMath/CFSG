module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Setup
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311SL3
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Coord
public import CFSG.Quasithin.Vol2.Ch4Sec3L439Mod

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def q4311 (I K : Subgroup G) : Subgroup G := c134Q (K ⊔ pCoreOf 2 I) K

@[expose] def u4311 (I K : Subgroup G) : Subgroup G := centerOf (q4311 I K)

theorem q4311_le (I K : Subgroup G) : q4311 I K ≤ pCoreOf 2 (K ⊔ pCoreOf 2 I) := by
  rw [q4311, c134Q, Subgroup.commutator_le]
  intro a ha k hk
  have hkN : k ∈ Subgroup.normalizer ((pCoreOf 2 (K ⊔ pCoreOf 2 I) : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk)
  have h2 : k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 (K ⊔ pCoreOf 2 I) :=
    (Subgroup.mem_normalizer_iff.mp hkN a⁻¹).mp (Subgroup.inv_mem _ ha)
  rw [commutatorElement_def]
  have h3 := Subgroup.mul_mem _ ha h2
  simpa [mul_assoc] using h3

theorem isPGroup_q4311 [Finite G] (I K : Subgroup G) : IsPGroup 2 ↥(q4311 I K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCoreOf_isPGroup 2 _).to_le (q4311_le I K)

theorem commutator_omegaOneCenter_le_u4311 (I K : Subgroup G) :
    ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)), K⁆ ≤ u4311 I K := by
  set P := pCoreOf 2 (K ⊔ pCoreOf 2 I) with hP
  have hΩ : omegaOneCenterOf P ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hKΩ : K ≤ Subgroup.normalizer ((omegaOneCenterOf P : Subgroup G) : Set G) :=
    (le_sup_left.trans (le_normalizer_pCoreOf 2 _)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf P)
  rw [u4311, centerOf]
  refine le_inf ?_ ?_
  · rw [q4311, c134Q]
    exact Subgroup.commutator_mono (hΩ.trans inf_le_left) le_rfl
  · rw [Subgroup.commutator_le]
    intro a ha k hk
    have h1 : ⁅a, k⁆ ∈ omegaOneCenterOf P := by
      rw [commutatorElement_def]
      have h2 : k * a⁻¹ * k⁻¹ ∈ omegaOneCenterOf P :=
        (Subgroup.mem_normalizer_iff.mp (hKΩ hk) a⁻¹).mp (Subgroup.inv_mem _ ha)
      have h3 := Subgroup.mul_mem _ ha h2
      simpa [mul_assoc] using h3
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (q4311_le I K)) (hΩ h1).2

theorem not_isC134Case2_of_isC134Case3 {G₀ R L : Subgroup G} (h3 : IsC134Case 3 G₀ R L) :
    ¬ IsC134Case 2 G₀ R L := by
  intro h2
  obtain ⟨⟨n₂, F₂, _, _, α₂, -, -, -, -, β₂, -, hβ₂k, -⟩, -⟩ := (h2 : IsC134Case2 _ _ _)
  obtain ⟨⟨n₃, F₃, _, _, α₃, -, -, -, -, -, β₃, hβ₃s, hβ₃k, -⟩, -⟩ := (h3 : IsC134Case3 _ _ _)
  have hinj : Function.Injective β₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₂k, Subgroup.bot_subgroupOf]
  have hab : ∀ x ∈ c134Q G₀ L, ∀ y ∈ c134Q G₀ L, x * y = y * x := by
    intro x hx y hy
    have h := hinj (show β₂ (⟨x, hx⟩ * ⟨y, hy⟩) = β₂ (⟨y, hy⟩ * ⟨x, hx⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have htriv : ∀ q : ↥(c134Q G₀ L), β₃ q = 1 := by
    intro q
    rw [← MonoidHom.mem_ker, hβ₃k, Subgroup.mem_subgroupOf]
    refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun y hy => (hab y hy q q.2)⟩
  obtain ⟨q, hq⟩ := hβ₃s (Multiplicative.ofAdd (fun _ _ => 1))
  rw [htriv q] at hq
  have := congrFun (congrFun (congrArg Multiplicative.toAdd hq) 0) 0
  simp at this

theorem exists_coords [Finite G] {T M L I H K : Subgroup G}
    (h3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L (v432 T M L) K)
    (h134 : IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSL 3 F))
      (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)) (W' : Submodule F (Fin 3 → F)),
      2 ≤ m ∧ Fintype.card F = 2 ^ m ∧ IsModO2Surj K α ∧ Function.Bijective β ∧
      K ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) ∧
      (∀ (k : ↥K) (u v : ↥(u4311 I K)), (v : G) = k * u * k⁻¹ →
        Multiplicative.toAdd (β v) =
          ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u)) ∧
      IsSumOfNaturalModulesVia K (q4311 I K) (u4311 I K) α true 2 ∧
      Module.finrank F W' = 2 ∧ v432 T M L ≤ u4311 I K ∧
      ∀ u : ↥(u4311 I K), (u : G) ∈ v432 T M L ↔ Multiplicative.toAdd (β u) ∈ W' := by
  classical
  have hle := commutator_omegaOneCenter_le_u4311 I K
  simp only [u4311, q4311] at hle ⊢
  have h134c := h134
  obtain ⟨⟨n₁, F, hFf, hFfin, α, hF, hαm, hU, hQ⟩, -⟩ := (h134c : IsC134Case3 _ _ _)
  obtain ⟨m₀, F₀, _, _, hm₀, hF₀, -, -, -, -, -, hline⟩ := h3
  have hline' : IsStabilizedLineOfNatural F₀ (pCoreOf 2 I) (H ⊓ M) K (v432 T M L) := by
    rcases hline with h | ⟨h2, -⟩
    · exact h
    · exact absurd h2 (not_isC134Case2_of_isC134Case3 h134)
  obtain ⟨W, hWle, α₀, β₀, hnat, hlineW, -⟩ := hline'
  obtain ⟨-, hα₀s, hα₀k, hβ₀s, hβ₀k, hβ₀a⟩ := hnat
  obtain ⟨hVW, W', hW'r, hW'iff⟩ := hlineW
  obtain ⟨hKU, -, β₁, hβ₁s, hβ₁k, hβ₁a⟩ := hU
  let ev : Multiplicative (Fin 1 → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
    { toFun := fun x => Multiplicative.ofAdd (Multiplicative.toAdd x 0)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨Multiplicative.ofAdd (fun _ => Multiplicative.toAdd y),
      rfl⟩⟩
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact congrArg Multiplicative.toAdd hxy
  set β := ev.comp β₁ with hβdef
  have hβ₁inj : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  have hβbij : Function.Bijective β := hev.comp ⟨hβ₁inj, hβ₁s⟩
  have hβa : ∀ (k : ↥K) (u v : ↥(centerOf (c134Q (K ⊔ pCoreOf 2 I) K))),
      (v : G) = k * u * k⁻¹ → Multiplicative.toAdd (β v) =
        ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) := by
    intro k u v huv
    exact hβ₁a k u v huv 0
  have hβ₀inj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₀k, Subgroup.bot_subgroupOf]
  have hcardSL : Nat.card ↥(StatedSL 3 F₀) = Nat.card ↥(StatedSL 3 F) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α₀ hα₀s).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαm.1).toEquiv, hα₀k, hαm.2]
  have hcard : Fintype.card F₀ = Fintype.card F := card_eq_of_card_statedSL_eq hcardSL
  have hWU : W = centerOf (c134Q (K ⊔ pCoreOf 2 I) K) := by
    refine Subgroup.eq_of_le_of_card_ge (hWle.trans hle) ?_
    have hU3 : Nat.card ↥(centerOf (c134Q (K ⊔ pCoreOf 2 I) K)) = Fintype.card F ^ 3 := by
      rw [Nat.card_congr (Equiv.ofBijective β hβbij), Nat.card_eq_fintype_card]
      simp
    have hW3 : Nat.card ↥W = Fintype.card F₀ ^ 3 := by
      rw [Nat.card_congr (Equiv.ofBijective β₀ ⟨hβ₀inj, hβ₀s⟩), Nat.card_eq_fintype_card]
      simp
    rw [hU3, hW3, hcard]
  subst hWU
  obtain ⟨W'', hW''r, hiff⟩ := L4311.exists_subspace_of_natural hcard hKU hαm.1 hβbij hβa hα₀s
    ⟨hβ₀inj, hβ₀s⟩ hβ₀a W'
  refine ⟨m₀, F, hFf, hFfin, α, β, W'', by omega, by rw [← hcard, hF₀], hαm, hβbij, hKU, hβa,
    hQ, hW''r.trans hW'r, hVW, fun u => (hW'iff u).trans (hiff u)⟩

theorem exists_normalized_coords {K U Q V Z : Subgroup G} {F : Type} [Field F] [Fintype F]
    {α : ↥K →* ↥(StatedSL 3 F)} (hαm : IsModO2Surj K α)
    {β : ↥U →* Multiplicative (Fin 3 → F)} (hβ : Function.Bijective β)
    (hβa : ∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hQ : IsSumOfNaturalModulesVia K Q U α true 2) {W' : Submodule F (Fin 3 → F)}
    (hW' : Module.finrank F W' = 2)
    (hViff : ∀ u : ↥U, (u : G) ∈ V ↔ Multiplicative.toAdd (β u) ∈ W') {p : Fin 3 → F}
    (hp : p ≠ 0) (hpW : p ∈ W')
    (hZiff : ∀ u : ↥U, (u : G) ∈ Z ↔ ∃ c : F, Multiplicative.toAdd (β u) = c • p) :
    ∃ (α' : ↥K →* ↥(StatedSL 3 F)) (β' : ↥U →* Multiplicative (Fin 3 → F))
      (W'' : Submodule F (Fin 3 → F)),
      IsModO2Surj K α' ∧ Function.Bijective β' ∧
      (∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
        Multiplicative.toAdd (β' v) =
          ((α' k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β' u)) ∧
      IsSumOfNaturalModulesVia K Q U α' true 2 ∧ Module.finrank F W'' = 2 ∧
      (∀ u : ↥U, (u : G) ∈ V ↔ Multiplicative.toAdd (β' u) ∈ W'') ∧ ![1, 0, 0] ∈ W'' ∧
      ∀ u : ↥U, (u : G) ∈ Z ↔ ∃ c : F, Multiplicative.toAdd (β' u) = c • ![1, 0, 0] := by
  classical
  obtain ⟨g₀, hg₀⟩ := SL3Pt.exists_mulVec_e0 hp
  let g : ↥(StatedSL 3 F) := specialLinearGroupEquivStatedSL 3 F g₀
  have hgm : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = g₀ :=
    specialLinearGroupEquivStatedSL_coe 3 F g₀
  have hMiMg : (((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [Subgroup.coe_inv]
    exact Units.inv_mul _
  have hMgMi : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [Subgroup.coe_inv]
    exact Units.mul_inv _
  have hgv : ∀ v, (((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hMiMg, Matrix.one_mulVec]
  have hgv' : ∀ v, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hMgMi, Matrix.one_mulVec]
  have hge : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = p := by
    rw [hgm, hg₀]
  have hMie : (((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p =
      ![1, 0, 0] := by
    rw [← hge, hgv]
  let α' : ↥K →* ↥(StatedSL 3 F) := (MulAut.conj g⁻¹).toMonoidHom.comp α
  let β' : ↥U →* Multiplicative (Fin 3 → F) :=
    { toFun := fun u => Multiplicative.ofAdd
        ((((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd (β u))
      map_one' := by
        apply Multiplicative.toAdd.injective
        simp
      map_mul' := fun u v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  have hβ' : ∀ u, Multiplicative.toAdd (β' u) =
      (((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β u) := fun _ => rfl
  let W'' : Submodule F (Fin 3 → F) :=
    { carrier := {v | ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W'}
      add_mem' := fun {v w} hv hw => by
        simp only [Set.mem_ofPred_eq, Matrix.mulVec_add] at hv hw ⊢
        exact W'.add_mem hv hw
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Matrix.mulVec_zero]
        exact W'.zero_mem
      smul_mem' := fun c v hv => by
        simp only [Set.mem_ofPred_eq, Matrix.mulVec_smul] at hv ⊢
        exact W'.smul_mem c hv }
  have hW''iff : ∀ v, v ∈ W'' ↔ ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W' :=
    fun _ => Iff.rfl
  refine ⟨α', β', W'', ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj g⁻¹).surjective.comp hαm.1
  · rw [← hαm.2]
    exact MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g⁻¹).injective
  · intro u v h
    have h1 := congrArg Multiplicative.toAdd h
    rw [hβ', hβ'] at h1
    have h2 := congrArg (fun x => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) h1
    simp only [hgv'] at h2
    exact hβ.1 (Multiplicative.toAdd.injective h2)
  · intro y
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd
      (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd y))
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hβ', hu, toAdd_ofAdd, hgv]
  · intro k u v huv
    rw [hβ', hβ', hβa k u v huv]
    show _ = ((((g⁻¹ * α k * g⁻¹⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ _
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv']
  · exact L4311.isSumOfNaturalModulesVia_conj hQ g⁻¹
  · rw [← hW']
    exact LinearEquiv.finrank_eq
      { toFun := fun v => ⟨((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (v : Fin 3 → F),
          v.2⟩
        invFun := fun w => ⟨(((g⁻¹ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F), by
          rw [hW''iff, hgv']
          exact w.2⟩
        map_add' := fun v w => Subtype.ext (by simp [Matrix.mulVec_add])
        map_smul' := fun c v => Subtype.ext (by simp [Matrix.mulVec_smul])
        left_inv := fun v => Subtype.ext (hgv _)
        right_inv := fun w => Subtype.ext (hgv' _) }
  · intro u
    rw [hViff, hβ', hW''iff, hgv']
  · rw [hW''iff, hge]
    exact hpW
  · intro u
    rw [hZiff, hβ']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, Matrix.mulVec_smul, hMie]⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun x => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) hc
      simp only [hgv', Matrix.mulVec_smul] at this
      rw [this, hge]

@[expose] noncomputable def stE0 (F : Type) [Field F] : Subgroup ↥(StatedSL 3 F) :=
  (Vol2.KGNat.stabE0 F).map (specialLinearGroupEquivStatedSL 3 F).toMonoidHom

theorem mem_stE0 {F : Type} [Field F] (s : ↥(StatedSL 3 F)) :
    s ∈ stE0 F ↔ ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, specialLinearGroupEquivStatedSL_coe]
    exact Vol2.KGNat.mem_stabE0.mp hB
  · intro h
    refine ⟨(specialLinearGroupEquivStatedSL 3 F).symm s, Vol2.KGNat.mem_stabE0.mpr ?_,
      MulEquiv.apply_symm_apply _ s⟩
    have := specialLinearGroupEquivStatedSL_coe 3 F ((specialLinearGroupEquivStatedSL 3 F).symm s)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
    exact h

theorem stE0_perfect {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅stE0 F, stE0 F⁆ = stE0 F := by
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ := by
    have h : ∃ s : Finset F, s.card = 4 := by
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
      exact ⟨t, ht⟩
    exact (CFSG.LinearGroups.special_linear_dimension_two_perfect h).commutator_eq_top
  rw [stE0, ← Subgroup.map_commutator, SL3Pt.stabE0_perfect hSL]

@[expose] noncomputable def stE0Equiv (F : Type) [Field F] : ↥(stE0 F) ≃* ↥(Vol2.KGNat.stabE0 F) :=
  ((Vol2.KGNat.stabE0 F).equivMapOfInjective (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
    (specialLinearGroupEquivStatedSL 3 F).injective).symm

theorem coe_stE0Equiv {F : Type} [Field F] (x : ↥(stE0 F)) :
    (((stE0Equiv F x : ↥(Vol2.KGNat.stabE0 F)) : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (((x : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
  have h := Subgroup.coe_equivMapOfInjective_apply (Vol2.KGNat.stabE0 F)
    (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
    (specialLinearGroupEquivStatedSL 3 F).injective (stE0Equiv F x)
  have h2 : (Vol2.KGNat.stabE0 F).equivMapOfInjective
      (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
      (specialLinearGroupEquivStatedSL 3 F).injective (stE0Equiv F x) = x :=
    MulEquiv.apply_symm_apply _ x
  rw [h2] at h
  rw [h, MulEquiv.coe_toMonoidHom, specialLinearGroupEquivStatedSL_coe]

theorem slE_stE0Equiv {F : Type} [Field F] (x : ↥(stE0 F)) :
    specialLinearGroupEquivStatedSL 3 F
      ((stE0Equiv F x : ↥(Vol2.KGNat.stabE0 F)) : Matrix.SpecialLinearGroup (Fin 3) F) =
      (x : ↥(StatedSL 3 F)) := by
  have h := Subgroup.coe_equivMapOfInjective_apply (Vol2.KGNat.stabE0 F)
    (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
    (specialLinearGroupEquivStatedSL 3 F).injective (stE0Equiv F x)
  have h2 : (Vol2.KGNat.stabE0 F).equivMapOfInjective
      (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
      (specialLinearGroupEquivStatedSL 3 F).injective (stE0Equiv F x) = x :=
    MulEquiv.apply_symm_apply _ x
  rw [h2] at h
  exact h.symm

theorem map_perfectCore_centralizer [Finite G] {K U Z : Subgroup G} {F : Type} [Field F]
    [Fintype F] (h4 : 4 ≤ Nat.card F) {α : ↥K →* ↥(StatedSL 3 F)} (hαs : Function.Surjective α)
    {β : ↥U →* Multiplicative (Fin 3 → F)} (hβ : Function.Bijective β)
    (hKU : K ≤ Subgroup.normalizer ((U : Subgroup G) : Set G))
    (hβa : ∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hZU : Z ≤ U)
    (hZiff : ∀ u : ↥U, (u : G) ∈ Z ↔ ∃ c : F, Multiplicative.toAdd (β u) = c • ![1, 0, 0]) :
    ((perfectCore (K ⊓ Subgroup.centralizer (Z : Set G))).subgroupOf K).map α = stE0 F := by
  classical
  set X := K ⊓ Subgroup.centralizer (Z : Set G) with hX
  have hcomap : X.subgroupOf K = (stE0 F).comap α := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_stE0]
    obtain ⟨z₀, hz₀⟩ := hβ.2 (Multiplicative.ofAdd ![1, 0, 0])
    have hz₀Z : (z₀ : G) ∈ Z := (hZiff z₀).mpr ⟨1, by rw [hz₀, toAdd_ofAdd, one_smul]⟩
    let conj : ↥U → ↥U := fun u =>
      ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
    constructor
    · rintro ⟨-, hkC⟩
      have hc : (k : G) * z₀ = z₀ * k := (Subgroup.mem_centralizer_iff.mp hkC (z₀ : G) hz₀Z).symm
      have h1 := hβa k z₀ z₀ (by rw [Subgroup.coe_inv, hc, mul_inv_cancel_right])
      rw [hz₀, toAdd_ofAdd] at h1
      exact h1.symm
    · intro hk
      refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      obtain ⟨c, hc⟩ := (hZiff ⟨z, hZU hz⟩).mp hz
      have h1 := hβa k ⟨z, hZU hz⟩ (conj ⟨z, hZU hz⟩) rfl
      rw [hc, Matrix.mulVec_smul, hk, ← hc] at h1
      have h2 : conj ⟨z, hZU hz⟩ = ⟨z, hZU hz⟩ := hβ.1 (Multiplicative.toAdd.injective h1)
      have h3 : (k : G) * z * (k : G)⁻¹ = z := congrArg (fun x : ↥U => (x : G)) h2
      calc z * (k : G) = k * z * (k : G)⁻¹ * k := by rw [h3]
        _ = k * z := by group
  have hXK : X ≤ K := inf_le_left
  have hcore : (perfectCore X).subgroupOf K = perfectCore (X.subgroupOf K) := by
    have h1 : (perfectCore (X.subgroupOf K)).map K.subtype = perfectCore X := by
      rw [map_perfectCore, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK]
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  rw [hcore, map_perfectCore, hcomap, Subgroup.map_comap_eq_self_of_surjective hαs,
    perfectCore_eq_self_of_perfect (stE0_perfect h4)]

theorem exists_torus_lift [Finite G] {K : Subgroup G} {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hm : 1 ≤ m) (hF : Fintype.card F = 2 ^ m) {α : ↥K →* ↥(StatedSL 3 F)}
    (hαs : Function.Surjective α) :
    ∃ (μ : Fˣ) (y : ↥K), orderOf μ = 2 ^ m - 1 ∧ Odd (orderOf y) ∧
      α y = specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor μ) := by
  classical
  obtain ⟨μ₀, hμ₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord₀ : orderOf μ₀ = 2 ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ₀, Nat.card_eq_fintype_card, Fintype.card_units,
      hF]
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  obtain ⟨k₀, hk₀⟩ := hαs (specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor μ₀))
  obtain ⟨b, r, hr, hbr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k₀).ne'
  refine ⟨μ₀ ^ (2 ^ b), k₀ ^ (2 ^ b), ?_, ?_, ?_⟩
  · rw [Nat.Coprime.orderOf_pow, hord₀]
    rw [hord₀]
    exact Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hodd)
  · rw [orderOf_pow' k₀ (pow_ne_zero _ two_ne_zero), hbr, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left r (Nat.two_pow_pos b)]
    exact hr
  · rw [map_pow, hk₀, ← map_pow, ← map_pow]

structure Setting4311 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ)
    (I H K : Subgroup G) (t : G) (m : ℕ) (F : Type) [Field F] [Fintype F]
    (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F))
    (W' : Submodule F (Fin 3 → F)) (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G) : Prop where
  sk : Setting432K G T M L n I H K t
  charTwo : CharTwo K
  c41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L (v432 T M L) K
  c3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L (v432 T M L) K
  c134 : IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K
  cent : T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥
  two_le : 2 ≤ m
  card_F : Fintype.card F = 2 ^ m
  modO2 : IsModO2Surj K α
  β_bij : Function.Bijective β
  K_U : K ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G)
  β_act : ∀ (k : ↥K) (u v : ↥(u4311 I K)), (v : G) = k * u * k⁻¹ →
    Multiplicative.toAdd (β v) =
      ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u)
  dualQ : IsSumOfNaturalModulesVia K (q4311 I K) (u4311 I K) α true 2
  W'_rank : Module.finrank F W' = 2
  V_le : v432 T M L ≤ u4311 I K
  V_iff : ∀ u : ↥(u4311 I K), (u : G) ∈ v432 T M L ↔ Multiplicative.toAdd (β u) ∈ W'
  e0_mem : ![1, 0, 0] ∈ W'
  ZS_eq : ZS = v432 T M L ⊓ Subgroup.centralizer ((T ⊓ H ⊓ L : Subgroup G) : Set G)
  ZS_iff : ∀ u : ↥(u4311 I K), (u : G) ∈ ZS ↔
    ∃ c : F, Multiplicative.toAdd (β u) = c • ![1, 0, 0]
  K₂_eq : K₂ = perfectCore (K ⊓ Subgroup.centralizer (ZS : Set G))
  K₂_map : (K₂.subgroupOf K).map α = stE0 F
  R₂_eq : R₂ = pCoreOf 2 (K₂ ⊔ T ⊓ H)
  μ_order : orderOf μ = 2 ^ m - 1
  y_mem : y ∈ K
  α_y : α ⟨y, y_mem⟩ = specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor μ)
  y_odd : Odd (orderOf y)

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G}

theorem T_le_normalizer_v432 [Finite G] (sk : Setting432K G T M L n I H K t) :
    T ≤ Subgroup.normalizer (v432 T M L : Set G) := by
  intro x hx
  apply mem_normalizer_of_map_conj_le
  rw [v432, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
    (A4.normalizer_le_normalizer_omegaOneCenterOf _
      ((le_sup_right.trans (sk.base.hyp421.sup_le_normalizer_Rp sk.base.hyp.normal)) hx)),
    map_conj_eq_of_mem_normalizer (sk.base.hyp.normal (sk.base.hyp.T_le hx))]

theorem L_le_normalizer_v432 [Finite G] (sk : Setting432K G T M L n I H K t) :
    L ≤ Subgroup.normalizer (v432 T M L : Set G) := by
  intro x hx
  apply mem_normalizer_of_map_conj_le
  rw [v432, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
    (A4.normalizer_le_normalizer_omegaOneCenterOf _
      ((le_sup_left.trans (sk.base.hyp421.sup_le_normalizer_Rp sk.base.hyp.normal)) hx)),
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)]

theorem commutator_v432_ne_bot [Finite G] (sk : Setting432K G T M L n I H K t)
    (hV : v432 T M L ≠ ⊥) : ⁅v432 T M L, L⁆ ≠ ⊥ := by
  intro h
  apply hV
  have h1 : ⁅⁅L, omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L))⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L]
    exact h
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h
  rw [sk.base.hyp.commutator_eq] at h3
  rw [v432, Subgroup.commutator_comm]
  exact h3

theorem not_S_inf_L_le_pCoreOf [Finite G] (sk : Setting432K G T M L n I H K t) :
    ¬ T ⊓ H ⊓ L ≤ pCoreOf 2 L := by
  intro hle
  have hsyl := sk.base.isSylowTwoOf_S_inf_L
  have hcard : Nat.card (ModO2 L) = 2 ^ n * (4 ^ n - 1) :=
    F420.card_of_statedPSL_two_two
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) sk.base.hyp.lie)
  have hsub : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact mem_pCoreOf_iff' x
  have hidx : ((pCoreOf 2 L).subgroupOf L).index = 2 ^ n * (4 ^ n - 1) := by
    rw [hsub, Subgroup.index]
    exact hcard
  have hdvd : ((pCoreOf 2 L).subgroupOf L).index ∣ ((T ⊓ H ⊓ L).subgroupOf L).index :=
    Subgroup.index_dvd_of_le (Subgroup.comap_mono (f := L.subtype) hle)
  rw [hidx] at hdvd
  have hn := sk.base.hyp.two_le
  exact hsyl.2.2 ((Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _).trans hdvd)

theorem exists_point [Finite G] (sk : Setting432K G T M L n I H K t)
    {F : Type} [Field F] [Fintype F] {m : ℕ} (hm : 1 ≤ m) (hF : Fintype.card F = 2 ^ m)
    {α : ↥K →* ↥(StatedSL 3 F)}
    {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)} {W' : Submodule F (Fin 3 → F)}
    (hβ : Function.Bijective β)
    (hKU : K ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G))
    (hβa : ∀ (k : ↥K) (u v : ↥(u4311 I K)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hW' : Module.finrank F W' = 2) (hVU : v432 T M L ≤ u4311 I K)
    (hViff : ∀ u : ↥(u4311 I K), (u : G) ∈ v432 T M L ↔ Multiplicative.toAdd (β u) ∈ W') :
    ∃ p : Fin 3 → F, p ≠ 0 ∧ p ∈ W' ∧ ∀ u : ↥(u4311 I K),
      (u : G) ∈ v432 T M L ⊓ Subgroup.centralizer ((T ⊓ H ⊓ L : Subgroup G) : Set G) ↔
        ∃ c : F, Multiplicative.toAdd (β u) = c • p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSLK : T ⊓ H ⊓ L ≤ K := inf_le_right.trans sk.L_le_K
  let P : Submodule F (Fin 3 → F) :=
    { carrier := {v | v ∈ W' ∧ ∀ s : ↥K, (s : G) ∈ T ⊓ H ⊓ L →
        ((α s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
      add_mem' := fun {v w} hv hw => ⟨W'.add_mem hv.1 hw.1, fun s hs => by
        rw [Matrix.mulVec_add, hv.2 s hs, hw.2 s hs]⟩
      zero_mem' := ⟨W'.zero_mem, fun s _ => Matrix.mulVec_zero _⟩
      smul_mem' := fun c v hv => ⟨W'.smul_mem c hv.1, fun s hs => by
        rw [Matrix.mulVec_smul, hv.2 s hs]⟩ }
  have hPW : P ≤ W' := fun v hv => hv.1
  have hiff : ∀ u : ↥(u4311 I K), (u : G) ∈ v432 T M L ⊓
      Subgroup.centralizer ((T ⊓ H ⊓ L : Subgroup G) : Set G) ↔
        Multiplicative.toAdd (β u) ∈ P := by
    intro u
    constructor
    · rintro ⟨huV, huC⟩
      refine ⟨(hViff u).mp huV, fun s hs => ?_⟩
      have hc : (s : G) * u = u * s := Subgroup.mem_centralizer_iff.mp huC (s : G) hs
      have h1 := hβa s u u (by
        rw [Subgroup.coe_inv, hc, mul_inv_cancel_right])
      exact h1.symm
    · rintro ⟨huW, hfix⟩
      refine ⟨(hViff u).mpr huW, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      let v : ↥(u4311 I K) :=
        ⟨s * u * s⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU (hSLK hs)) u).mp u.2⟩
      have h1 := hβa ⟨s, hSLK hs⟩ u v rfl
      rw [hfix ⟨s, hSLK hs⟩ hs] at h1
      have h2 : v = u := hβ.1 (Multiplicative.toAdd.injective h1)
      have h3 : s * (u : G) * s⁻¹ = u := congrArg Subtype.val h2
      calc s * (u : G) = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [h3]
  let fV : ↥(v432 T M L) → ↥W' := fun v =>
    ⟨Multiplicative.toAdd (β ⟨v, hVU v.2⟩), (hViff ⟨v, hVU v.2⟩).mp v.2⟩
  have hfV : Function.Bijective fV := by
    refine ⟨fun v w h => ?_, fun w => ?_⟩
    · have h1 : β ⟨v, hVU v.2⟩ = β ⟨w, hVU w.2⟩ :=
        Multiplicative.toAdd.injective (congrArg Subtype.val h)
      have h2 : (⟨v, hVU v.2⟩ : ↥(u4311 I K)) = ⟨w, hVU w.2⟩ := hβ.1 h1
      exact Subtype.ext (congrArg (fun x : ↥(u4311 I K) => (x : G)) h2)
    · obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd (w : Fin 3 → F))
      have huV : (u : G) ∈ v432 T M L := (hViff u).mpr (by rw [hu, toAdd_ofAdd]; exact w.2)
      refine ⟨⟨u, huV⟩, Subtype.ext ?_⟩
      show Multiplicative.toAdd (β ⟨(u : G), hVU huV⟩) = w
      rw [show (⟨(u : G), hVU huV⟩ : ↥(u4311 I K)) = u from rfl, hu, toAdd_ofAdd]
  have hcardV : Nat.card ↥(v432 T M L) = Fintype.card F ^ 2 := by
    rw [Nat.card_congr (Equiv.ofBijective fV hfV), Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := F), hW']
  have h2V : 2 ∣ Nat.card ↥(v432 T M L) := by
    rw [hcardV, hF, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  have hSV : T ⊓ H ⊓ L ≤ Subgroup.normalizer ((v432 T M L : Subgroup G) : Set G) :=
    (inf_le_left.trans inf_le_left).trans sk.T_le_normalizer_v432
  let _ : MulAction ↥(T ⊓ H ⊓ L) ↥(v432 T M L) :=
    { smul := fun s v => ⟨s * v * (s : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hSV s.2) v).mp v.2⟩
      one_smul := fun v => Subtype.ext (by
        show ((1 : ↥(T ⊓ H ⊓ L)) : G) * v * ((1 : ↥(T ⊓ H ⊓ L)) : G)⁻¹ = v
        simp)
      mul_smul := fun x y v => Subtype.ext (by
        show ((x * y : ↥(T ⊓ H ⊓ L)) : G) * v * ((x * y : ↥(T ⊓ H ⊓ L)) : G)⁻¹ =
          x * (y * v * (y : G)⁻¹) * (x : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hfix1 : (1 : ↥(v432 T M L)) ∈ MulAction.fixedPoints ↥(T ⊓ H ⊓ L) ↥(v432 T M L) := by
    intro s
    apply Subtype.ext
    show (s : G) * 1 * (s : G)⁻¹ = 1
    simp
  obtain ⟨b, hb, hb1⟩ :=
    sk.base.isSylowTwoOf_S_inf_L.2.1.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      ↥(v432 T M L) h2V hfix1
  have hbZ : (b : G) ∈ v432 T M L ⊓ Subgroup.centralizer ((T ⊓ H ⊓ L : Subgroup G) : Set G) := by
    refine ⟨b.2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have h1 : (s : G) * b * s⁻¹ = b := congrArg Subtype.val (hb ⟨s, hs⟩)
    calc s * (b : G) = s * b * s⁻¹ * s := by group
      _ = b * s := by rw [h1]
  have hbP : Multiplicative.toAdd (β ⟨b, hVU b.2⟩) ∈ P := (hiff ⟨b, hVU b.2⟩).mp hbZ
  have hb0 : Multiplicative.toAdd (β ⟨b, hVU b.2⟩) ≠ 0 := by
    intro h0
    apply hb1
    have h1 : β ⟨b, hVU b.2⟩ = β 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective h0
    have h2 := congrArg Subtype.val (hβ.1 h1)
    exact Subtype.ext h2.symm
  have hPne : ¬ W' ≤ P := by
    intro hWP
    have hVne : v432 T M L ≠ ⊥ := by
      intro hbot
      apply hb1
      apply Subtype.ext
      exact ((Subgroup.eq_bot_iff_forall _).mp hbot (b : G) b.2).symm
    have hSC : T ⊓ H ⊓ L ≤ L ⊓ Subgroup.centralizer ((v432 T M L : Subgroup G) : Set G) := by
      intro s hs
      refine ⟨hs.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hvZ := (hiff ⟨v, hVU hv⟩).mpr (hWP ((hViff ⟨v, hVU hv⟩).mp hv))
      exact (Subgroup.mem_centralizer_iff.mp hvZ.2 s hs).symm
    exact sk.not_S_inf_L_le_pCoreOf (hSC.trans (sk.base.hyp.inf_centralizer_le
      sk.L_le_normalizer_v432 (sk.commutator_v432_ne_bot hVne)))
  have hPrank : Module.finrank F P = 1 := by
    have hlt : Module.finrank F P < 2 := by
      rw [← hW']
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hPW fun h => hPne h.ge)
    have hne : Module.finrank F P ≠ 0 := by
      intro h0
      have hbot := Submodule.finrank_eq_zero.mp h0
      have : Multiplicative.toAdd (β ⟨b, hVU b.2⟩) ∈ (⊥ : Submodule F (Fin 3 → F)) :=
        hbot ▸ hbP
      exact hb0 ((Submodule.mem_bot F).mp this)
    omega
  obtain ⟨v, hv0, hvspan⟩ := finrank_eq_one_iff'.mp hPrank
  refine ⟨v, fun h => hv0 (Subtype.ext h), hPW v.2, fun u => ?_⟩
  rw [hiff]
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := hvspan ⟨_, hu⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨c, hc⟩
    rw [hc]
    exact P.smul_mem c v.2

theorem exists_setting4311 [Finite G] (sk : Setting432K G T M L n I H K t) (hchar : CharTwo K)
    (h41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L (v432 T M L) K)
    (h3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L (v432 T M L) K)
    (h134 : IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K)
    (hcent : T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSL 3 F))
      (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)) (W' : Submodule F (Fin 3 → F))
      (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G),
      Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y := by
  classical
  obtain ⟨m, F, hFf, hFfin, α₁, β₁, W₁, hm, hF, hα₁, hβ₁, hKU, hβ₁a, hQ₁, hW₁, hVU, hV₁⟩ :=
    exists_coords h3 h134
  obtain ⟨p, hp, hpW, hZ₁⟩ := sk.exists_point (by omega) hF hβ₁ hKU hβ₁a hW₁ hVU hV₁
  obtain ⟨α, β, W', hα, hβ, hβa, hQ, hW', hV, he0, hZ⟩ :=
    exists_normalized_coords hα₁ hβ₁ hβ₁a hQ₁ hW₁ hV₁ hp hpW hZ₁
  set ZS := v432 T M L ⊓ Subgroup.centralizer ((T ⊓ H ⊓ L : Subgroup G) : Set G) with hZS
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hK₂ := map_perfectCore_centralizer h4 hα.1 hβ hKU hβa (inf_le_left.trans hVU) hZ
  obtain ⟨μ, y, hμ, hy, hαy⟩ := exists_torus_lift (by omega) hF hα.1
  refine ⟨m, F, hFf, hFfin, α, β, W', ZS, perfectCore (K ⊓ Subgroup.centralizer (ZS : Set G)),
    pCoreOf 2 (perfectCore (K ⊓ Subgroup.centralizer (ZS : Set G)) ⊔ T ⊓ H), μ, y,
    ⟨sk, hchar, h41, h3, h134, hcent, hm, hF, hα, hβ, hKU, hβa, hQ, hW', hVU, hV, he0, rfl, hZ,
      rfl, hK₂, rfl, hμ, y.2, hαy, ?_⟩⟩
  rw [orderOf_submonoid]
  exact hy

end Setting432K

end CFSG.Quasithin.H13.Ch4
