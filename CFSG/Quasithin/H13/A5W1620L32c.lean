module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace L32

section Vectors

variable {F : Type*} [Field F]

theorem eq_zero_or_eq_one_of_natCard_two [Finite F] (hF : Nat.card F = 2) (a : F) :
    a = 0 ∨ a = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rcases eq_or_ne a 0 with h0 | h0
  · exact Or.inl h0
  · right
    have h := FiniteField.pow_card_sub_one_eq_one a h0
    rwa [← Nat.card_eq_fintype_card, hF, show 2 - 1 = 1 from rfl, pow_one] at h

theorem two_eq_zero_of_natCard_two [Finite F] (hF : Nat.card F = 2) : (2 : F) = 0 := by
  rcases eq_zero_or_eq_one_of_natCard_two hF 2 with h | h
  · exact h
  · exfalso
    have h1 : (1 : F) = 0 := by
      calc (1 : F) = (1 + 1) - 1 := by ring
        _ = 0 := by rw [one_add_one_eq_two, h, sub_self]
    exact one_ne_zero h1

theorem one_add_vecMulVec_mulVec (e φ x : Fin 3 → F) :
    (1 + Matrix.vecMulVec e φ) *ᵥ x = x + (φ ⬝ᵥ x) • e := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem det_one_add_vecMulVec {e φ : Fin 3 → F} (h : φ ⬝ᵥ e = 0) :
    (1 + Matrix.vecMulVec e φ).det = 1 := by
  rw [Matrix.vecMulVec_eq (ι := Unit), Matrix.det_one_add_replicateCol_mul_replicateRow, h,
    add_zero]

end Vectors

section Natural

variable {F : Type} [Field F]

noncomputable def tv (e φ : Fin 3 → F) (h : φ ⬝ᵥ e = 0) : ↥(StatedSL 3 F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec e φ)
    (by rw [det_one_add_vecMulVec h]; exact one_ne_zero), Subgroup.subset_closure
    (det_one_add_vecMulVec h)⟩

theorem tv_mulVec (e φ : Fin 3 → F) (h : φ ⬝ᵥ e = 0) (x : Fin 3 → F) :
    ((tv e φ h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + (φ ⬝ᵥ x) • e :=
  one_add_vecMulVec_mulVec e φ x

theorem exists_form_of_ne_zero (h01 : ∀ a : F, a = 0 ∨ a = 1)
    (h2 : (2 : F) = 0) {e : Fin 3 → F} (he : e ≠ 0) :
    ∃ φ x : Fin 3 → F, φ ⬝ᵥ e = 0 ∧ φ ⬝ᵥ x = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (funext h)
  have hi1 : e i = 1 := (h01 (e i)).resolve_left hi
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := ⟨i + 1, by
    intro h
    have := congrArg Fin.val h
    fin_cases i <;> simp_all⟩
  refine ⟨Pi.single j 1 + e j • Pi.single i 1, Pi.single j 1, ?_, ?_⟩
  · rw [add_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul,
      hi1, smul_eq_mul, mul_one, ← two_mul, h2, zero_mul]
  · rw [add_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne hj.symm, smul_eq_mul, mul_zero, add_zero]

theorem forall_of_invariant (h01 : ∀ a : F, a = 0 ∨ a = 1) {P : (Fin 3 → F) → Prop}
    (hadd : ∀ x w, P x → P w → P (x + w)) (hneg : ∀ x, P x → P (-x))
    (hγ : ∀ γ : ↥(StatedSL 3 F), ∀ x, P x →
      P (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x))
    {e : Fin 3 → F} (he : P e) (he0 : e ≠ 0) : ∀ x, P x := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he0 (funext h)
  have hi1 : e i = 1 := (h01 (e i)).resolve_left hi
  have h0 : ∀ x : Fin 3 → F, x i = 0 → P x := by
    intro x hx
    have hφ : (Pi.single i 1 : Fin 3 → F) ⬝ᵥ x = 0 := by rw [single_dotProduct, one_mul, hx]
    have h1 := hγ (tv x (Pi.single i 1) hφ) e he
    rw [tv_mulVec, single_dotProduct, one_mul, hi1, one_smul] at h1
    have h2 := hadd _ _ h1 (hneg e he)
    rwa [add_comm e x, add_neg_cancel_right] at h2
  intro x
  rcases h01 (x i) with hx | hx
  · exact h0 x hx
  · have h3 : P (x - e) := h0 _ (by rw [Pi.sub_apply, hx, hi1, sub_self])
    have h4 := hadd _ _ h3 he
    rwa [sub_add_cancel] at h4

theorem eq_zero_of_forall_fixed (h01 : ∀ a : F, a = 0 ∨ a = 1) {x : Fin 3 → F}
    (hx : ∀ γ : ↥(StatedSL 3 F), ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) :
    x = 0 := by
  classical
  by_contra hx0
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hi1 : x i = 1 := (h01 (x i)).resolve_left hi
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := ⟨i + 1, by
    intro h
    have := congrArg Fin.val h
    fin_cases i <;> simp_all⟩
  have hφ : (Pi.single i 1 : Fin 3 → F) ⬝ᵥ (Pi.single j 1 : Fin 3 → F) = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hj.symm]
  have h1 := hx (tv (Pi.single j 1) (Pi.single i 1) hφ)
  rw [tv_mulVec, single_dotProduct, one_mul, hi1, one_smul] at h1
  have h2 := congrFun (add_eq_left.mp h1) j
  rw [Pi.single_eq_same, Pi.zero_apply] at h2
  exact one_ne_zero h2

end Natural

section Group

variable {F : Type} [Field F] {G : Type*} [Group G]

theorem exists_mem_of_not_le [Finite F] (hF : Nat.card F = 2) {A X Z M : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥X →* Multiplicative (Fin 3 → F)} (hβk : β.ker = Z.subgroupOf X)
    (hβe : ∀ (a : ↥A) (u v : ↥X), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hMX : M ≤ X) (hAM : ∀ a ∈ A, ∀ u ∈ M, a * u * a⁻¹ ∈ M) (hMZ : ¬ M ≤ Z) :
    ∀ x : Fin 3 → F, ∃ u : ↥M, Multiplicative.toAdd (β (Subgroup.inclusion hMX u)) = x := by
  have h01 := eq_zero_or_eq_one_of_natCard_two hF
  obtain ⟨u₀, hu₀M, hu₀Z⟩ := Set.not_subset.mp hMZ
  refine forall_of_invariant h01
    (P := fun x => ∃ u : ↥M, Multiplicative.toAdd (β (Subgroup.inclusion hMX u)) = x)
    ?_ ?_ ?_ ⟨⟨u₀, hu₀M⟩, rfl⟩ ?_
  · rintro x w ⟨u, rfl⟩ ⟨u', rfl⟩
    exact ⟨u * u', by rw [map_mul, map_mul, toAdd_mul]⟩
  · rintro x ⟨u, rfl⟩
    exact ⟨u⁻¹, by rw [map_inv, map_inv, toAdd_inv]⟩
  · rintro γ x ⟨u, rfl⟩
    obtain ⟨a, rfl⟩ := hα γ
    exact ⟨⟨a * u * (a : G)⁻¹, hAM a a.2 u u.2⟩, hβe a _ _ rfl⟩
  · intro h0
    apply hu₀Z
    have hk : Subgroup.inclusion hMX ⟨u₀, hu₀M⟩ ∈ β.ker := toAdd_eq_zero.mp h0
    rw [hβk] at hk
    exact hk

theorem le_of_ne_bot [Finite F] (hF : Nat.card F = 2) {A X M : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥X →* Multiplicative (Fin 3 → F)} (hβk : β.ker = ⊥)
    (hβe : ∀ (a : ↥A) (u v : ↥X), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hMX : M ≤ X) (hAM : ∀ a ∈ A, ∀ u ∈ M, a * u * a⁻¹ ∈ M) (hM : M ≠ ⊥) : X ≤ M := by
  have hβk' : β.ker = (⊥ : Subgroup G).subgroupOf X := by rw [hβk, Subgroup.bot_subgroupOf]
  have hsurj := exists_mem_of_not_le hF hα hβk' hβe hMX hAM fun h => hM (le_bot_iff.mp h)
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
  intro q hq
  obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd (β ⟨q, hq⟩))
  have h1 : Subgroup.inclusion hMX u = ⟨q, hq⟩ := hinj (Multiplicative.toAdd.injective hu)
  have h2 : (u : G) = q := congrArg Subtype.val h1
  rw [← h2]
  exact u.2

theorem mem_of_forall_conj_eq [Finite F] (hF : Nat.card F = 2) {A X Z : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥X →* Multiplicative (Fin 3 → F)} (hβk : β.ker = Z.subgroupOf X)
    (hβe : ∀ (a : ↥A) (u v : ↥X), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    {q : G} (hq : q ∈ X) (hfix : ∀ a ∈ A, a * q * a⁻¹ = q) : q ∈ Z := by
  have h01 := eq_zero_or_eq_one_of_natCard_two hF
  have h0 : Multiplicative.toAdd (β ⟨q, hq⟩) = 0 := by
    refine eq_zero_of_forall_fixed h01 fun γ => ?_
    obtain ⟨a, rfl⟩ := hα γ
    exact (hβe a ⟨q, hq⟩ ⟨q, hq⟩ (hfix a a.2).symm).symm
  have hk : (⟨q, hq⟩ : ↥X) ∈ β.ker := toAdd_eq_zero.mp h0
  rw [hβk] at hk
  exact hk

theorem conj_mul_inv_mem_of_commute [Finite F] (hF : Nat.card F = 2) {A X Z M : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥X →* Multiplicative (Fin 3 → F)} (hβk : β.ker = Z.subgroupOf X)
    (hβe : ∀ (a : ↥A) (u v : ↥X), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hMX : M ≤ X) (hAM : ∀ a ∈ A, ∀ u ∈ M, a * u * a⁻¹ ∈ M) (hMZ : ¬ M ≤ Z)
    {y : G} (hyM : ∀ u ∈ M, y * u * y⁻¹ ∈ M)
    (hyZ : ∀ u ∈ M, u ∈ Z → y * u * y⁻¹ ∈ Z) (hyZ' : ∀ u ∈ M, y * u * y⁻¹ ∈ Z → u ∈ Z)
    (hcomm : ∀ a ∈ A, ∀ u ∈ M, a * (y * u * y⁻¹) * a⁻¹ = y * (a * u * a⁻¹) * y⁻¹) :
    ∀ u ∈ M, y * u * y⁻¹ * u⁻¹ ∈ Z := by
  classical
  have h01 := eq_zero_or_eq_one_of_natCard_two hF
  have h2 := two_eq_zero_of_natCard_two hF
  have hsurj := exists_mem_of_not_le hF hα hβk hβe hMX hAM hMZ
  set b : G → (Fin 3 → F) := fun g =>
    if h : g ∈ X then Multiplicative.toAdd (β ⟨g, h⟩) else 0 with hbdef
  have hbX : ∀ g (h : g ∈ X), b g = Multiplicative.toAdd (β ⟨g, h⟩) := fun g h => by
    simp [hbdef, h]
  have hbmul : ∀ g ∈ M, ∀ g' ∈ M, b (g * g') = b g + b g' := by
    intro g hg g' hg'
    rw [hbX _ (X.mul_mem (hMX hg) (hMX hg')), hbX _ (hMX hg), hbX _ (hMX hg'), ← toAdd_mul,
      ← map_mul]
    rfl
  have hbinv : ∀ g ∈ M, b g⁻¹ = -b g := by
    intro g hg
    rw [hbX _ (X.inv_mem (hMX hg)), hbX _ (hMX hg), ← toAdd_inv, ← map_inv]
    rfl
  have hb0 : ∀ g ∈ M, b g = 0 ↔ g ∈ Z := by
    intro g hg
    rw [hbX _ (hMX hg), toAdd_eq_zero, ← MonoidHom.mem_ker, hβk]
    rfl
  have hbe : ∀ (a : ↥A), ∀ g ∈ M,
      b (a * g * (a : G)⁻¹) = ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b g := by
    intro a g hg
    rw [hbX _ (hMX (hAM a a.2 g hg)), hbX _ (hMX hg)]
    exact hβe a ⟨g, hMX hg⟩ _ rfl
  have hbs : ∀ x : Fin 3 → F, ∃ u ∈ M, b u = x := by
    intro x
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨u, u.2, by rw [hbX _ (hMX u.2)]; exact hu⟩
  intro u hu
  have hyu : y * u * y⁻¹ ∈ M := hyM u hu
  have huinv : u⁻¹ ∈ M := M.inv_mem hu
  have hgoal : b (y * u * y⁻¹) = b u → y * u * y⁻¹ * u⁻¹ ∈ Z := by
    intro h
    refine (hb0 _ (M.mul_mem hyu huinv)).mp ?_
    rw [hbmul _ hyu _ huinv, hbinv _ hu, h, add_neg_cancel]
  apply hgoal
  set e := b u with he
  by_cases he0 : e = 0
  · have huZ : u ∈ Z := (hb0 u hu).mp he0
    rw [(hb0 _ hyu).mpr (hyZ u hu huZ)]
    exact he0.symm
  obtain ⟨φ, x, hφe, hφx⟩ := exists_form_of_ne_zero h01 h2 he0
  obtain ⟨a, haα⟩ := hα (tv e φ hφe)
  have haA : (a : G) ∈ A := a.2
  obtain ⟨u', hu'M, hu'⟩ := hbs x
  have hgu' : (a : G) * u' * (a : G)⁻¹ ∈ M := hAM _ haA _ hu'M
  set c₀ := (a : G) * u' * (a : G)⁻¹ * (u' * u)⁻¹ with hc₀def
  have hu'u : u' * u ∈ M := M.mul_mem hu'M hu
  have hc₀M : c₀ ∈ M := M.mul_mem hgu' (M.inv_mem hu'u)
  have hc₀Z : c₀ ∈ Z := by
    refine (hb0 _ hc₀M).mp ?_
    rw [hc₀def, hbmul _ hgu' _ (M.inv_mem hu'u), hbinv _ hu'u, hbmul _ hu'M _ hu,
      hbe a _ hu'M, haα, tv_mulVec, hu', hφx, one_smul, ← he]
    abel
  have hgeq : (a : G) * u' * (a : G)⁻¹ = c₀ * (u' * u) := by rw [hc₀def]; group
  have hyu' : y * u' * y⁻¹ ∈ M := hyM u' hu'M
  have hyc₀ : y * c₀ * y⁻¹ ∈ M := hyM c₀ hc₀M
  have hyc₀Z : b (y * c₀ * y⁻¹) = 0 := (hb0 _ hyc₀).mpr (hyZ c₀ hc₀M hc₀Z)
  have key : (a : G) * (y * u' * y⁻¹) * (a : G)⁻¹ =
      (y * c₀ * y⁻¹) * ((y * u' * y⁻¹) * (y * u * y⁻¹)) := by
    rw [hcomm _ haA _ hu'M, hgeq]
    group
  have key2 := congrArg b key
  rw [hbe a _ hyu', haα, tv_mulVec, hbmul _ hyc₀ _ (M.mul_mem hyu' hyu), hyc₀Z, zero_add,
    hbmul _ hyu' _ hyu] at key2
  have h3 : b (y * u * y⁻¹) = (φ ⬝ᵥ b (y * u' * y⁻¹)) • e := (add_left_cancel key2).symm
  rcases h01 (φ ⬝ᵥ b (y * u' * y⁻¹)) with h0 | h1
  · exfalso
    rw [h0, zero_smul] at h3
    exact he0 ((hb0 u hu).mpr (hyZ' u hu ((hb0 _ hyu).mp h3)))
  · rw [h3, h1, one_smul]

end Group

end L32

end CFSG.Quasithin.H13.A5
