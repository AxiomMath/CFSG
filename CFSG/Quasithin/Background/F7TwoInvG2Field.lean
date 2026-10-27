module

public import CFSG.Quasithin.Background.F7TwoInvG2Root

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F7Two.G2Ev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.LocalAnalysis.ComponentInitial

section Field


variable {K : Type} [Field K] [CharP K 2]

theorem delta_facts {f : ℕ} (hf : 2 ≤ f) (hfe : Even f) (hK : Nat.card K = 2 ^ f) (δ : K →+* K)
    (hδ : ∀ c, δ c = c ^ 2 ^ (f / 2)) : (∀ c, δ (δ c) = c) ∧ ∃ v : K, δ v ≠ v := by
  obtain ⟨e, he⟩ := hfe
  have hfe' : f / 2 = e := by omega
  have hU : UnitaryFieldData 2 e K :=
    ⟨Nat.prime_two, by omega, by rw [hK, he, ← two_mul]⟩
  have hδb : ∀ c, δ c = hU.bar c := fun c => by rw [hδ, hfe', hU.bar_apply]
  refine ⟨fun c => by rw [hδb, hδb, hU.bar_bar], ?_⟩
  obtain ⟨v, hv⟩ := hU.exists_bar_ne
  exact ⟨v, by rwa [hδb]⟩

theorem map_rootElt {β : MulAut ↥(adjointGroup .G2 K)} {δ : K →+* K}
    (hβ : ∀ u : ↥(adjointGroup .G2 K),
      (β u : ModGL .G2 K) = Units.map (entrywiseHom δ) (u : ModGL .G2 K))
    (γ : Fin Tag.G2.rank → ℤ) (x : K) : β (rootElt K γ x) = rootElt K γ (δ x) := by
  refine Subtype.ext ?_
  rw [hβ]
  exact Units.ext (by rw [Units.coe_map]; exact entrywise_pinnedX δ γ x)

theorem not_isPGroup_two_zpowers_of_scalar {y : ↥(adjointGroup .G2 K)}
    {γ : Fin Tag.G2.rank → ℤ} {l : K} (hl : l ≠ 1)
    (hy : ∀ x, y * rootElt K γ x * y⁻¹ = rootElt K γ (l * x)) :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isPGroup_two_zpowers_iff]
  rintro ⟨n, hn⟩
  have hpow : ∀ m : ℕ, y ^ m * rootElt K γ 1 * (y ^ m)⁻¹ = rootElt K γ (l ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * rootElt K γ 1 * (y ^ (m + 1))⁻¹
          = y * (y ^ m * rootElt K γ 1 * (y ^ m)⁻¹) * y⁻¹ := by group
        _ = rootElt K γ (l ^ (m + 1)) := by rw [ih, hy, pow_succ']
  have h1 := hpow (2 ^ n)
  rw [hn, one_mul, inv_one, mul_one] at h1
  have h2 : (1 : K) = l ^ 2 ^ n :=
    pinnedX_injective .G2 K γ (congrArg Subtype.val h1)
  have h3 : (l - 1) ^ 2 ^ n = 0 := by
    rw [sub_pow_char_pow, ← h2, one_pow, sub_self]
  exact hl (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 h3))

theorem mem_invXiAut_of_scalar {β : MulAut ↥(adjointGroup .G2 K)} {δ : K →+* K}
    (hβ : ∀ u : ↥(adjointGroup .G2 K),
      (β u : ModGL .G2 K) = Units.map (entrywiseHom δ) (u : ModGL .G2 K))
    (hδδ : ∀ c, δ (δ c) = c) {h : ↥(adjointGroup .G2 K)} {γ : Fin Tag.G2.rank → ℤ} {η : K}
    (hη : η ≠ 0) (hδη : δ η ≠ η) (hh : ∀ x, h * rootElt K γ x * h⁻¹ = rootElt K γ (η * x)) :
    h ∈ invXiAut β := by
  show ¬ IsPGroup 2 ↥(Subgroup.zpowers (β h * h⁻¹))
  refine not_isPGroup_two_zpowers_of_scalar (γ := γ) (l := δ η * η⁻¹) ?_ fun x => ?_
  · intro h1
    exact hδη (by simpa [hη] using (mul_inv_eq_one₀ hη).1 h1)
  · have e1 : h⁻¹ * rootElt K γ x * h = rootElt K γ (η⁻¹ * x) := by
      have h2 := hh (η⁻¹ * x)
      rw [mul_inv_cancel_left₀ hη] at h2
      calc h⁻¹ * rootElt K γ x * h = h⁻¹ * (h * rootElt K γ (η⁻¹ * x) * h⁻¹) * h := by rw [h2]
        _ = rootElt K γ (η⁻¹ * x) := by group
    have e2 : β h * rootElt K γ (η⁻¹ * x) * (β h)⁻¹ = rootElt K γ (δ η * η⁻¹ * x) := by
      obtain ⟨z, hz⟩ : ∃ z, δ z = η⁻¹ * x := ⟨δ (η⁻¹ * x), hδδ _⟩
      have h3 := congrArg β (hh z)
      rw [map_mul, map_mul, map_inv, map_rootElt hβ, map_rootElt hβ, map_mul] at h3
      rw [← hz, h3, hz, mul_assoc]
    calc β h * h⁻¹ * rootElt K γ x * (β h * h⁻¹)⁻¹
        = β h * (h⁻¹ * rootElt K γ x * h) * (β h)⁻¹ := by group
      _ = rootElt K γ (δ η * η⁻¹ * x) := by rw [e1, e2]

variable (K) in
@[expose] def tor (t₁ t₂ : Kˣ) : ↥(adjointGroup .G2 K) :=
  ⟨torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂,
    mul_mem (g2RankOne_le_adjointGroup _ (torusElt_mem_g2RankOne _ _))
      (g2RankOne_le_adjointGroup _ (torusElt_mem_g2RankOne _ _))⟩

theorem tor_conj_rootElt {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (t₁ t₂ : Kˣ) (x : K) :
    tor K t₁ t₂ * rootElt K γ x * (tor K t₁ t₂)⁻¹ =
      rootElt K γ (((t₁ ^ (∑ j, Tag.G2.cartan g2ia j * γ j) *
        t₂ ^ (∑ j, Tag.G2.cartan g2ir j * γ j) : Kˣ) : K) * x) :=
  Subtype.ext (torus_conj hγ t₁ t₂ x)

theorem exists_tor (u v : Kˣ) :
    ∃ h : ↥(adjointGroup .G2 K),
      (∀ x, h * rootElt K g2a x * h⁻¹ = rootElt K g2a ((u : K) * x)) ∧
      (∀ x, h * rootElt K g2r x * h⁻¹ = rootElt K g2r ((v : K) * x)) ∧
      (∀ x, h * rootElt K (-g2a) x * h⁻¹ = rootElt K (-g2a) (((u⁻¹ : Kˣ) : K) * x)) ∧
      (∀ x, h * rootElt K (-g2r) x * h⁻¹ = rootElt K (-g2r) (((v⁻¹ : Kˣ) : K) * x)) := by
  have hu := u.ne_zero
  have hv := v.ne_zero
  refine ⟨tor K (u ^ 2 * v ^ 3) (u * v ^ 2), fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [tor_conj_rootElt isRoot_g2a]
    have e1 : (∑ j, Tag.G2.cartan g2ia j * g2a j : ℤ) = 2 := by decide
    have e2 : (∑ j, Tag.G2.cartan g2ir j * g2a j : ℤ) = -3 := by decide
    have e : (((u ^ 2 * v ^ 3) ^ (2 : ℤ) * (u * v ^ 2) ^ (-3 : ℤ) : Kˣ) : K) = u := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      field_simp
    rw [e1, e2, e]
  · rw [tor_conj_rootElt isRoot_g2r]
    have e1 : (∑ j, Tag.G2.cartan g2ia j * g2r j : ℤ) = -1 := by decide
    have e2 : (∑ j, Tag.G2.cartan g2ir j * g2r j : ℤ) = 2 := by decide
    have e : (((u ^ 2 * v ^ 3) ^ (-1 : ℤ) * (u * v ^ 2) ^ (2 : ℤ) : Kˣ) : K) = v := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      field_simp
    rw [e1, e2, e]
  · rw [tor_conj_rootElt (IsRoot.neg isRoot_g2a)]
    have e1 : (∑ j, Tag.G2.cartan g2ia j * (-g2a) j : ℤ) = -2 := by decide
    have e2 : (∑ j, Tag.G2.cartan g2ir j * (-g2a) j : ℤ) = 3 := by decide
    have e : (((u ^ 2 * v ^ 3) ^ (-2 : ℤ) * (u * v ^ 2) ^ (3 : ℤ) : Kˣ) : K) =
        ((u⁻¹ : Kˣ) : K) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      field_simp
    rw [e1, e2, e]
  · rw [tor_conj_rootElt (IsRoot.neg isRoot_g2r)]
    have e1 : (∑ j, Tag.G2.cartan g2ia j * (-g2r) j : ℤ) = 1 := by decide
    have e2 : (∑ j, Tag.G2.cartan g2ir j * (-g2r) j : ℤ) = -2 := by decide
    have e : (((u ^ 2 * v ^ 3) ^ (1 : ℤ) * (u * v ^ 2) ^ (-2 : ℤ) : Kˣ) : K) =
        ((v⁻¹ : Kˣ) : K) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      field_simp
    rw [e1, e2, e]

theorem invAutGen_g2_field {f : ℕ} (hf : 2 ≤ f) (hfe : Even f) (hK : Nat.card K = 2 ^ f)
    {β : MulAut ↥(adjointGroup .G2 K)} {δ : K →+* K} (hδ : ∀ c, δ c = c ^ 2 ^ (f / 2))
    (hβ : ∀ u : ↥(adjointGroup .G2 K),
      (β u : ModGL .G2 K) = Units.map (entrywiseHom δ) (u : ModGL .G2 K)) :
    InvAutGen ↥(adjointGroup .G2 K) β := by
  obtain ⟨hδδ, v₀, hv₀⟩ := delta_facts hf hfe hK δ hδ
  have hv00 : v₀ ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero δ)
  set V : Kˣ := Units.mk0 v₀ hv00 with hV
  have hVδ : δ (V : K) ≠ V := hv₀
  have hfix : ∀ γ, rootElt K γ 1 ∈ fixSubgroup β := fun γ => by
    rw [mem_fixSubgroup_iff, map_rootElt hβ, map_one]
  have hΞr : ∀ h : ↥(adjointGroup .G2 K),
      (∀ x, h * rootElt K g2r x * h⁻¹ = rootElt K g2r ((V : K) * x)) → h ∈ invXiAut β :=
    fun h hh => mem_invXiAut_of_scalar hβ hδδ V.ne_zero hVδ hh
  have hΞa : ∀ (h : ↥(adjointGroup .G2 K)),
      (∀ x, h * rootElt K g2a x * h⁻¹ = rootElt K g2a ((V : K) * x)) → h ∈ invXiAut β :=
    fun h hh => mem_invXiAut_of_scalar hβ hδδ V.ne_zero hVδ hh
  obtain ⟨h₀, -, hr₀, -, -⟩ := exists_tor (1 : Kˣ) V
  have hne : (invXiAut β).Nonempty := ⟨h₀, hΞr h₀ hr₀⟩
  have hK' := fixSubgroup_le_closure_invXiAut hne
  set H : Subgroup ↥(adjointGroup .G2 K) := Subgroup.closure (invXiAut β) with hH
  have key : ∀ γ, rootElt K γ 1 ∈ H := fun γ => hK' (hfix γ)
  have conj_mem : ∀ (h : ↥(adjointGroup .G2 K)) (γ : Fin Tag.G2.rank → ℤ) (c : K),
      h ∈ H → (∀ x, h * rootElt K γ x * h⁻¹ = rootElt K γ (c * x)) → rootElt K γ c ∈ H :=
    fun h γ c hh hc => by
      have := H.mul_mem (H.mul_mem hh (key γ)) (H.inv_mem hh)
      rwa [hc 1, mul_one] at this
  have ha : HasRoot K H g2a := fun x => by
    by_cases hx : x = 0
    · rw [hx, rootElt_zero]
      exact H.one_mem
    · obtain ⟨h, ha1, hr1, -, -⟩ := exists_tor (Units.mk0 x hx) V
      exact conj_mem h _ _ (Subgroup.subset_closure (hΞr h hr1)) (by simpa using ha1)
  have hr : HasRoot K H g2r := fun x => by
    by_cases hx : x = 0
    · rw [hx, rootElt_zero]
      exact H.one_mem
    · obtain ⟨h, ha1, hr1, -, -⟩ := exists_tor V (Units.mk0 x hx)
      exact conj_mem h _ _ (Subgroup.subset_closure (hΞa h ha1)) (by simpa using hr1)
  have ha' : HasRoot K H (-g2a) := fun x => by
    by_cases hx : x = 0
    · rw [hx, rootElt_zero]
      exact H.one_mem
    · obtain ⟨h, -, hr1, ha1, -⟩ := exists_tor (Units.mk0 x hx)⁻¹ V
      exact conj_mem h _ _ (Subgroup.subset_closure (hΞr h hr1)) (by simpa using ha1)
  have hr' : HasRoot K H (-g2r) := fun x => by
    by_cases hx : x = 0
    · rw [hx, rootElt_zero]
      exact H.one_mem
    · obtain ⟨h, ha1, -, -, hr1⟩ := exists_tor V (Units.mk0 x hx)⁻¹
      exact conj_mem h _ _ (Subgroup.subset_closure (hΞa h ha1)) (by simpa using hr1)
  exact eq_top_of_hasRoot ha ha' hr hr'

end Field

end CFSG.Quasithin.F7Two.G2Ev
