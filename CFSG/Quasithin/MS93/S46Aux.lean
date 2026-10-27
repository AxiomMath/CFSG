module

public import CFSG.Quasithin.MS93.S4AM

public section

namespace CFSG.Quasithin.MS93.S46

open scoped commutatorElement

section ElemAb

variable {Γ : Type*} [Group Γ]

theorem exists_index_two_of_sq [Finite Γ] (h2 : ∀ x : Γ, x * x = 1) {H₀ : Subgroup Γ}
    (hH₀ : H₀ ≠ ⊤) : ∃ H : Subgroup Γ, H₀ ≤ H ∧ H.index = 2 := by
  have hcomm : ∀ x y : Γ, x * y = y * x := by
    intro x y
    have hxy := h2 (x * y)
    have hx := h2 x
    have hy := h2 y
    calc x * y = x * (x * y * (x * y)) * y := by rw [hxy, mul_one]
      _ = (x * x) * y * x * (y * y) := by group
      _ = y * x := by rw [hx, hy]; group
  obtain ⟨k, hk⟩ : ∃ k, k ∉ H₀ := by
    by_contra hall
    exact hH₀ (eq_top_iff.mpr fun x _ => by
      by_contra hx
      exact hall ⟨x, hx⟩)
  let S : Set (Subgroup Γ) := {H | H₀ ≤ H ∧ k ∉ H}
  have hfin : Finite (Subgroup Γ) :=
    Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ)) SetLike.coe_injective
  obtain ⟨H, hH₀H, hmax⟩ := Set.Finite.exists_le_maximal (s := S) (Set.toFinite S)
    (a := H₀) ⟨le_rfl, hk⟩
  have hkH : k ∉ H := hmax.1.2
  refine ⟨H, hH₀H, ?_⟩
  rw [Subgroup.index_eq_two_iff]
  refine ⟨k, fun b => ?_⟩
  by_cases hb : b ∈ H
  · refine Or.inr ⟨hb, fun hbk => hkH ?_⟩
    have : k = b⁻¹ * (b * k) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem hb) hbk
  · refine Or.inl ⟨?_, hb⟩
    have hlt : H < H ⊔ Subgroup.zpowers b :=
      lt_of_le_of_ne le_sup_left fun he => hb (he ▸ Subgroup.mem_sup_right
        (Subgroup.mem_zpowers b))
    have hkmem : k ∈ H ⊔ Subgroup.zpowers b := by
      by_contra hk'
      exact (hmax.not_gt ⟨hH₀H.trans le_sup_left, hk'⟩ hlt)
    let _ : CommGroup Γ := { (inferInstance : Group Γ) with mul_comm := hcomm }
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hkmem
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h2 b
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
    · exfalso
      apply hkH
      have : b ^ m = 1 := by rw [hj, zpow_mul, hb2, one_zpow]
      rw [← hyz, this, mul_one]
      exact hy
    · have : b ^ m = b := by rw [hj, zpow_add, zpow_mul, hb2, one_zpow, one_mul, zpow_one]
      rw [this] at hyz
      have : b * k = y := by
        rw [← hyz, hcomm y b, ← mul_assoc, h2 b, one_mul]
      rw [this]
      exact hy

end ElemAb

section Index2

variable {𝔾 : Type} [Group 𝔾]

theorem le_normalizer_of_commutator_le' {X K K' : Subgroup 𝔾} (hKK' : K ≤ K')
    (h : ⁅K', X⁆ ≤ K) :
    X ≤ Subgroup.normalizer (K : Set 𝔾) := by
  have key : ∀ x ∈ X, ∀ y ∈ K, x * y * x⁻¹ ∈ K := by
    intro x hx y hy
    have hyK' : y⁻¹ ∈ K' := K'.inv_mem (hKK' hy)
    have hc : ⁅y⁻¹, x⁆ ∈ K := h (Subgroup.commutator_mem_commutator hyK' hx)
    have e : x * y * x⁻¹ = y * ⁅y⁻¹, x⁆⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, inv_inv]
    exact K.mul_mem hy hc
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem exists_inv_index_two {X L Q K₀ K' : Subgroup 𝔾} [Finite ↥(K' ⊔ Q)]
    (hK'c : ∀ k ∈ K', ∀ k' ∈ K', k * k' = k' * k) (hK'2 : ∀ k ∈ K', k ^ 2 = 1)
    (hQ : IsPGroup 2 ↥Q) (hK₀ : K₀ ≤ K') (hne : ¬ K' ≤ K₀) (hX : X = L ⊔ Q)
    (hXK₀ : X ≤ Subgroup.normalizer (K₀ : Set 𝔾)) (hXK' : X ≤ Subgroup.normalizer (K' : Set 𝔾))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set 𝔾)) (hLK : ⁅K', L⁆ ≤ K₀) :
    ∃ K'' : Subgroup 𝔾, K₀ ≤ K'' ∧ K'' ≤ K' ∧ X ≤ Subgroup.normalizer (K'' : Set 𝔾) ∧
      K''.relIndex K' = 2 ∧ ⁅K', X⁆ ≤ K'' := by
  have hLX : L ≤ X := hX ▸ le_sup_left
  have hQX : Q ≤ X := hX ▸ le_sup_right
  have hQK' : Q ≤ Subgroup.normalizer (K' : Set 𝔾) := hQX.trans hXK'
  have hK'Q : ⁅K', Q⁆ ≤ K' := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hQK').trans' (by
      rw [Subgroup.commutator_comm])
  set K₁ := K₀ ⊔ ⁅K', Q⁆ with hK₁
  have hK₁K' : K₁ ≤ K' := sup_le hK₀ hK'Q
  have hK'n : ∀ A : Subgroup 𝔾, A ≤ K' → K' ≤ Subgroup.normalizer (A : Set 𝔾) := by
    intro A hA k hk
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have : k * a * k⁻¹ = a := by rw [hK'c k hk a (hA ha)]; group
      rw [this]; exact ha
    · intro ha
      have haK' : a ∈ K' := by
        have : a = k⁻¹ * (k * a * k⁻¹) * k := by group
        rw [this]
        exact K'.mul_mem (K'.mul_mem (K'.inv_mem hk) (hA ha)) hk
      have : k * a * k⁻¹ = a := by rw [hK'c k hk a haK']; group
      rwa [this] at ha
  have hXc : X ≤ Subgroup.normalizer ((⁅K', Q⁆ : Subgroup 𝔾) : Set 𝔾) := by
    refine le_normalizer_of_map_conj_le fun x hx => ?_
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hXK' hx),
      map_conj_eq_of_mem_normalizer (hXQ hx)]
  have hXK₁ : X ≤ Subgroup.normalizer (K₁ : Set 𝔾) :=
    (le_inf hXK₀ hXc).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hK'X : ⁅K', X⁆ ≤ K₁ := by
    rw [hX, Subgroup.commutator_comm]
    refine S4A.commutator_sup_le_of ?_ ?_ (hLX.trans hXK₁) (hQX.trans hXK₁)
    · rw [Subgroup.commutator_comm]; exact hLK.trans le_sup_left
    · rw [Subgroup.commutator_comm]; exact le_sup_right
  have hlt : ¬ K' ≤ K₁ := by
    intro hle
    have hK'p : IsPGroup 2 ↥K' := fun k => ⟨1, by
      have := hK'2 k k.2
      ext; simpa using this⟩
    have hP : IsPGroup 2 ↥(K' ⊔ Q) := hK'p.to_sup_of_normal_left' hQ hQK'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent ↥(K' ⊔ Q) := hP.isNilpotent
    obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (S := K' ⊔ Q)).mp hnil
    let f : ℕ → Subgroup 𝔾 := fun m => Nat.rec K' (fun _ A => ⁅A, Q⁆) m
    have hf0 : f 0 = K' := rfl
    have hfs : ∀ m, f (m + 1) = ⁅f m, Q⁆ := fun _ => rfl
    have hfK' : ∀ m, f m ≤ K' := by
      intro m
      induction m with
      | zero => exact le_rfl
      | succ m ih =>
        rw [hfs]
        exact (Subgroup.commutator_mono ih le_rfl).trans hK'Q
    have hfL : ∀ m, f m ≤ (K' ⊔ Q).lowerCentralSeries m := by
      intro m
      induction m with
      | zero => rw [hf0, Subgroup.lowerCentralSeries_zero]; exact le_sup_left
      | succ m ih =>
        rw [hfs, Subgroup.lowerCentralSeries_succ]
        exact Subgroup.commutator_mono ih le_sup_right
    have hfK₀ : ∀ m, K' ≤ K₀ ⊔ f m := by
      intro m
      induction m with
      | zero => exact le_sup_right
      | succ m ih =>
        refine hle.trans (sup_le le_sup_left ?_)
        refine (Subgroup.commutator_mono ih le_rfl).trans ?_
        refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
        · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQX.trans hXK₀)).trans
            le_sup_left |>.trans' (by rw [Subgroup.commutator_comm])
        · rw [← hfs]; exact le_sup_right
        · exact hK₀.trans (hK'n _ (sup_le hK₀ (hfK' (m + 1))))
        · exact (hfK' m).trans (hK'n _ (sup_le hK₀ (hfK' (m + 1))))
    have := hfK₀ n
    rw [show f n = ⊥ from le_bot_iff.mp ((hfL n).trans hn.le), sup_bot_eq] at this
    exact hne this
  have h2 : ∀ x : ↥K', x * x = 1 := fun x => Subtype.ext (by simpa [sq] using hK'2 x x.2)
  have hfinK' : Finite ↥K' :=
    Finite.of_injective _ (Subgroup.inclusion_injective (le_sup_left : K' ≤ K' ⊔ Q))
  have hne' : K₁.subgroupOf K' ≠ ⊤ := by
    intro htop
    apply hlt
    intro k hk
    have : (⟨k, hk⟩ : ↥K') ∈ K₁.subgroupOf K' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨H, hH₁, hH2⟩ := exists_index_two_of_sq h2 hne'
  refine ⟨H.map K'.subtype, ?_, Subgroup.map_subtype_le H, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨⟨k, hK₀ hk⟩, hH₁ (Subgroup.mem_subgroupOf.mpr ((le_sup_left : K₀ ≤ K₁) hk)), rfl⟩
  · refine le_normalizer_of_commutator_le' (Subgroup.map_subtype_le H) ?_
    intro x hx
    have hxK' : x ∈ K' := (hK'X.trans hK₁K') hx
    exact ⟨⟨x, hxK'⟩, hH₁ (Subgroup.mem_subgroupOf.mpr (hK'X hx)), rfl⟩
  · rw [Subgroup.relIndex, PU.map_subtype_subgroupOf]
    exact hH2
  · intro x hx
    have hxK' : x ∈ K' := (hK'X.trans hK₁K') hx
    exact ⟨⟨x, hxK'⟩, hH₁ (Subgroup.mem_subgroupOf.mpr (hK'X hx)), rfl⟩

end Index2

end CFSG.Quasithin.MS93.S46
