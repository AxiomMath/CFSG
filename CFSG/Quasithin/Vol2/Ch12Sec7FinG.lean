module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec7FinE

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

namespace S127

section Coset

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_relIndex_le_two {H D : Subgroup G} (hHD : H ≤ D)
    (h : H.relIndex D ≤ 2) : D ≤ Subgroup.normalizer (H : Set G) := by
  have h0 : H.relIndex D ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show H.relIndex D = 1 ∨ H.relIndex D = 2 by omega) with h1 | h2
  · have := Subgroup.relIndex_eq_one.1 h1
    rw [le_antisymm hHD this]
    exact Subgroup.le_normalizer
  · have hn : (H.subgroupOf D).Normal := Subgroup.normal_of_index_eq_two h2
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHD).1 hn

theorem conj_mem_of_pow_five {D D₀ : Subgroup G} (hidx : D₀.relIndex D ≤ 4)
    {x : G} (hx5 : x ^ 5 = 1) (hxD : x ∈ Subgroup.normalizer (D : Set G))
    (hxD₀ : x ∈ Subgroup.normalizer (D₀ : Set G)) {d : G} (hd : d ∈ D) :
    d⁻¹ * (x * d * x⁻¹) ∈ D₀ := by
  classical
  set e : ℕ → G := fun i => x ^ i * d * (x ^ i)⁻¹ with he
  have heD : ∀ i, e i ∈ D := fun i =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hxD i) d).1 hd
  have hsucc : ∀ i, e (i + 1) = x * e i * x⁻¹ := fun i => by
    simp only [he, pow_succ']
    group
  have hshift1 : ∀ i j, (e i)⁻¹ * e j ∈ D₀ → (e (i + 1))⁻¹ * e (j + 1) ∈ D₀ := by
    intro i j h
    rw [hsucc, hsucc]
    have := (Subgroup.mem_normalizer_iff.1 hxD₀ _).1 h
    simpa [mul_assoc] using this
  have hshift : ∀ n i j, (e i)⁻¹ * e j ∈ D₀ → (e (i + n))⁻¹ * e (j + n) ∈ D₀ := by
    intro n
    induction n with
    | zero => intro i j h; simpa using h
    | succ n ih =>
      intro i j h
      have := hshift1 _ _ (ih i j h)
      simpa [add_assoc] using this
  have hper : ∀ q r, e (5 * q + r) = e r := by
    intro q r
    simp only [he, pow_add, pow_mul, hx5, one_pow, one_mul]
  have he0 : e 0 = d := by simp [he]
  have hiter : ∀ m, (e 0)⁻¹ * e m ∈ D₀ → ∀ t, (e 0)⁻¹ * e (t * m) ∈ D₀ := by
    intro m hm t
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 := hshift (t * m) 0 m hm
      rw [zero_add] at h1
      have := D₀.mul_mem ih h1
      rw [show (t + 1) * m = m + t * m by ring]
      simpa [mul_assoc] using this
  by_contra hne
  have hne' : ¬ (e 0)⁻¹ * e 1 ∈ D₀ := by
    rw [he0]
    simpa [he] using hne
  have hdist : ∀ i j, i < j → j < 5 → ¬ (e i)⁻¹ * e j ∈ D₀ := by
    intro i j hij hj5 h
    have h1 := hshift (5 - i) i j h
    rw [show i + (5 - i) = 5 * 1 + 0 by omega, show j + (5 - i) = 5 * 1 + (j - i) by omega,
      hper, hper] at h1
    have h2 := hiter (j - i) h1
    apply hne'
    have hm : 1 ≤ j - i ∧ j - i ≤ 4 := by omega
    obtain ⟨t, ht⟩ : ∃ t, t * (j - i) = 5 * (t * (j - i) / 5) + 1 := by
      rcases (show j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨ j - i = 4 by omega) with h | h | h | h <;>
        rw [h]
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
    have := h2 t
    rwa [ht, hper] at this
  have hinj : Function.Injective (fun i : Fin 5 =>
      (QuotientGroup.mk (⟨e i, heD i⟩ : ↥D) : ↥D ⧸ D₀.subgroupOf D)) := by
    intro i j hij
    simp only [QuotientGroup.eq] at hij
    by_contra hne2
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne2) with h | h
    · exact hdist i j h j.2 (by simpa [Subgroup.mem_subgroupOf] using hij)
    · apply hdist j i h i.2
      have := (D₀.subgroupOf D).inv_mem hij
      simpa [Subgroup.mem_subgroupOf] using this
  have h5 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h5
  have : Nat.card (↥D ⧸ D₀.subgroupOf D) = D₀.relIndex D := rfl
  omega

omit [Finite G] in
@[expose] def stabSub (D D₀ : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ Subgroup.normalizer (D : Set G) ∧ z ∈ Subgroup.centralizer (D₀ : Set G) ∧
    ∀ d ∈ D, d⁻¹ * (z * d * z⁻¹) ∈ D₀}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun d _ => by simp⟩
  mul_mem' := by
    rintro z w ⟨hzN, hzC, hz⟩ ⟨hwN, hwC, hw⟩
    refine ⟨Subgroup.mul_mem _ hzN hwN, Subgroup.mul_mem _ hzC hwC, fun d hd => ?_⟩
    have hβ := hw d hd
    have hzβ : z * (d⁻¹ * (w * d * w⁻¹)) * z⁻¹ = d⁻¹ * (w * d * w⁻¹) := by
      rw [← Subgroup.mem_centralizer_iff.1 hzC _ hβ, mul_inv_cancel_right]
    have e1 : d⁻¹ * (z * w * d * (z * w)⁻¹) =
        (d⁻¹ * (z * d * z⁻¹)) * (z * (d⁻¹ * (w * d * w⁻¹)) * z⁻¹) := by group
    rw [e1, hzβ]
    exact D₀.mul_mem (hz d hd) hβ
  inv_mem' := by
    rintro z ⟨hzN, hzC, hz⟩
    refine ⟨Subgroup.inv_mem _ hzN, Subgroup.inv_mem _ hzC, fun d hd => ?_⟩
    have hd' : z⁻¹ * d * z⁻¹⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hzN) d).1 hd
    have h := D₀.inv_mem (hz _ hd')
    have e1 : ((z⁻¹ * d * z⁻¹⁻¹)⁻¹ * (z * (z⁻¹ * d * z⁻¹⁻¹) * z⁻¹))⁻¹ =
        d⁻¹ * (z⁻¹ * d * z⁻¹⁻¹) := by group
    rwa [e1] at h

omit [Finite G] in
theorem commutator_mem_centralizer_of_stab {D D₀ : Subgroup G}
    (hDD₀ : D ≤ Subgroup.normalizer (D₀ : Set G)) {x y : G} (hx : x ∈ stabSub D D₀)
    (hy : y ∈ stabSub D D₀) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  obtain ⟨hxN, hxC, hxs⟩ := hx
  obtain ⟨hyN, hyC, hys⟩ := hy
  have hZ : ∀ {z : G}, z ∈ Subgroup.centralizer (D₀ : Set G) →
      (∀ d ∈ D, d⁻¹ * (z * d * z⁻¹) ∈ D₀) → ∀ d ∈ D, ∀ u ∈ D₀,
        (d⁻¹ * (z * d * z⁻¹)) * u = u * (d⁻¹ * (z * d * z⁻¹)) := by
    intro z hzC _ d hd u hu
    have hdu : d * u * d⁻¹ ∈ D₀ := (Subgroup.mem_normalizer_iff.1 (hDD₀ hd) u).1 hu
    have h1 : z * (d * u * d⁻¹) * z⁻¹ = d * u * d⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.1 hzC _ hdu, mul_inv_cancel_right]
    have h2 : z * u * z⁻¹ = u := by
      rw [← Subgroup.mem_centralizer_iff.1 hzC _ hu, mul_inv_cancel_right]
    have h3 : z * (d * u * d⁻¹) * z⁻¹ = (z * d * z⁻¹) * (z * u * z⁻¹) * (z * d * z⁻¹)⁻¹ := by
      group
    rw [h2, h1] at h3
    calc d⁻¹ * (z * d * z⁻¹) * u
        = d⁻¹ * ((z * d * z⁻¹) * u * (z * d * z⁻¹)⁻¹) * (z * d * z⁻¹) := by group
      _ = d⁻¹ * (d * u * d⁻¹) * (z * d * z⁻¹) := by rw [← h3]
      _ = u * (d⁻¹ * (z * d * z⁻¹)) := by group
  have hact : ∀ d ∈ D, x * y * d * (x * y)⁻¹ = y * x * d * (y * x)⁻¹ := by
    intro d hd
    obtain ⟨α, hα⟩ : ∃ α, α = d⁻¹ * (x * d * x⁻¹) := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β, β = d⁻¹ * (y * d * y⁻¹) := ⟨_, rfl⟩
    have hαD : α ∈ D₀ := hα ▸ hxs d hd
    have hβD : β ∈ D₀ := hβ ▸ hys d hd
    have hxβ : x * β * x⁻¹ = β := by
      rw [← Subgroup.mem_centralizer_iff.1 hxC _ hβD, mul_inv_cancel_right]
    have hyα : y * α * y⁻¹ = α := by
      rw [← Subgroup.mem_centralizer_iff.1 hyC _ hαD, mul_inv_cancel_right]
    have hαβ : α * β = β * α := by
      rw [hα]
      exact hZ hxC hxs d hd β hβD
    have e3 : x * d * x⁻¹ = d * α := by rw [hα]; group
    have e4 : y * d * y⁻¹ = d * β := by rw [hβ]; group
    calc x * y * d * (x * y)⁻¹ = (x * d * x⁻¹) * (x * (d⁻¹ * (y * d * y⁻¹)) * x⁻¹) := by group
      _ = (d * α) * (x * β * x⁻¹) := by rw [e3, ← hβ]
      _ = d * (α * β) := by rw [hxβ]; group
      _ = d * (β * α) := by rw [hαβ]
      _ = (d * β) * (y * α * y⁻¹) := by rw [hyα]; group
      _ = (y * d * y⁻¹) * (y * (d⁻¹ * (x * d * x⁻¹)) * y⁻¹) := by rw [e4, ← hα]
      _ = y * x * d * (y * x)⁻¹ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : (y * x)⁻¹ * d * (y * x)⁻¹⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (Subgroup.mul_mem _ hyN hxN)) d).1 hd
  have h := hact _ hd'
  have e1 : y * x * ((y * x)⁻¹ * d * (y * x)⁻¹⁻¹) * (y * x)⁻¹ = d := by group
  rw [e1] at h
  calc d * (x * y * x⁻¹ * y⁻¹)
      = (x * y * ((y * x)⁻¹ * d * (y * x)⁻¹⁻¹) * (x * y)⁻¹) * (x * y * x⁻¹ * y⁻¹) := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ * d := by group

omit [Finite G] in
theorem commutator_stabSub_le {D D₀ : Subgroup G} (hDD₀ : D ≤ Subgroup.normalizer (D₀ : Set G)) :
    ⁅stabSub D D₀, stabSub D D₀⁆ ≤ Subgroup.centralizer (D : Set G) :=
  (Subgroup.commutator_le).2 fun _ hx _ hy => commutator_mem_centralizer_of_stab hDD₀ hx hy

end Coset

end S127

end CFSG.Quasithin.H13
