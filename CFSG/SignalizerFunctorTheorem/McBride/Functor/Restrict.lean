module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Size

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {P : Subgroup G → Prop} {X : Subgroup G}

@[expose] def restrictFunctor (H : Subgroup G) (θ : G → Subgroup G) : G → Subgroup G :=
  fun a => θ a ⊓ H

theorem IsFunctor.restrictFunctor (hθ : IsFunctor p A θ) {H : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) : IsFunctor p A (restrictFunctor H θ) where
  le_centralizer a ha ha1 := inf_le_left.trans (hθ.le_centralizer a ha ha1)
  coprime a ha ha1 :=
    (hθ.coprime a ha ha1).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  normalized a ha ha1 := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    exact ⟨Subgroup.le_normalizer_iff.mp (hθ.normalized a ha ha1) x hx y hy.1,
      Subgroup.le_normalizer_iff.mp hAH x hx y hy.2⟩
  balance a ha ha1 b hb hb1 := by
    intro x hx
    exact ⟨hθ.balance a ha ha1 b hb hb1 ⟨hx.1.1, hx.2⟩, hx.1.2⟩

theorem mem_signalizers_restrictFunctor_iff [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) {H : Subgroup G} :
    X ∈ signalizers p A (restrictFunctor H θ) P ↔ X ∈ signalizers p A θ P ∧ X ≤ H := by
  constructor
  · intro hX
    have hXθ : X ∈ signalizers p A θ P :=
      ⟨hX.1, hX.2.1, fun a ha ha1 => (hX.2.2.1 a ha ha1).trans inf_le_left, hX.2.2.2⟩
    refine ⟨hXθ, ?_⟩
    calc X = ⨆ (b : G) (_ : b ∈ A) (_ : b ≠ 1), X ⊓ Subgroup.centralizer {b} :=
          (iSup_inf_centralizer hp hA hrank hX.1 hX.2.1).symm
      _ ≤ H := iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
          (hX.2.2.1 b hb hb1).trans inf_le_right
  · rintro ⟨hX, hXH⟩
    exact ⟨hX.1, hX.2.1, fun a ha ha1 => le_inf (hX.2.2.1 a ha ha1) (inf_le_left.trans hXH),
      hX.2.2.2⟩

theorem size_restrictFunctor_lt [Finite G] {H : Subgroup G}
    (hex : ∃ a ∈ A, a ≠ 1 ∧ ¬ θ a ≤ H) : size A (restrictFunctor H θ) < size A θ := by
  obtain ⟨a, ha, ha1, hnle⟩ := hex
  refine size_lt_size (fun a _ _ => inf_le_left) ⟨a, ha, ha1, fun h => hnle ?_⟩
  exact inf_eq_left.mp h

theorem IsFunctor.mono_left (hθ : IsFunctor p A θ) {A₀ : Subgroup G} (h : A₀ ≤ A) :
    IsFunctor p A₀ θ where
  le_centralizer a ha ha1 := hθ.le_centralizer a (h ha) ha1
  coprime a ha ha1 := hθ.coprime a (h ha) ha1
  normalized a ha ha1 := h.trans (hθ.normalized a (h ha) ha1)
  balance a ha ha1 b hb hb1 := hθ.balance a (h ha) ha1 b (h hb) hb1

theorem signalizers_subset_of_le_left {A₀ : Subgroup G} (h : A₀ ≤ A) :
    signalizers p A θ P ⊆ signalizers p A₀ θ P :=
  fun _ hX => ⟨h.trans hX.1, hX.2.1, fun a ha ha1 => hX.2.2.1 a (h ha) ha1, hX.2.2.2⟩

theorem exists_le_card_eq_pow [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A) {k : ℕ}
    (hk : p ^ k ≤ Nat.card A) : ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = p ^ k := by
  obtain ⟨E, hEA, hEcard⟩ :=
    CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty p k hp A hA hk
  exact ⟨E, hEA, hEcard⟩

private theorem conj_comm_aux {x a : G} (h : x * a = a * x) (y : G) :
    a * (x * y * x⁻¹) * a⁻¹ = x * (a * y * a⁻¹) * x⁻¹ := by
  have h' : a⁻¹ * x⁻¹ = x⁻¹ * a⁻¹ := by
    rw [← mul_inv_rev, h, mul_inv_rev]
  calc a * (x * y * x⁻¹) * a⁻¹ = (a * x) * y * (x⁻¹ * a⁻¹) := by group
    _ = (x * a) * y * (a⁻¹ * x⁻¹) := by rw [h, h']
    _ = x * (a * y * a⁻¹) * x⁻¹ := by group

theorem isCompleteIn_of_le_left [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {A₀ : Subgroup G} (hA₀ : A₀ ≤ A) (hrank : p ^ 2 ≤ Nat.card A₀)
    (hconj : ∀ (X : Subgroup G), ∀ a ∈ A, P X → P (X.map (MulAut.conj a).toMonoidHom))
    (h₀ : IsCompleteIn (signalizers p A₀ θ P)) : IsCompleteIn (signalizers p A θ P) := by
  obtain ⟨Y, hY, hYmax⟩ := h₀
  have hA₀e : IsElemAbelian p A₀ :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hA₀
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    comm_of_mem_of_isMulCommutative hA.1 hx hy
  have hinv : ∀ a ∈ A, Y.map (MulAut.conj a).toMonoidHom ≤ Y := by
    intro a ha
    refine hYmax _ ⟨?_, ?_, ?_, hconj Y a ha hY.2.2.2⟩
    · rw [Subgroup.le_normalizer_iff]
      rintro x hx _ ⟨y, hy, rfl⟩
      refine ⟨x * y * x⁻¹, Subgroup.le_normalizer_iff.mp hY.1 x hx y hy, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      exact conj_comm_aux (hcomm x (hA₀ hx) a ha) y
    · rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
      exact hY.2.1
    · intro b hb hb1 z hz
      obtain ⟨⟨y, hy, rfl⟩, hzb⟩ := Subgroup.mem_inf.mp hz
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at hzb ⊢
      have hba : Commute b a := hcomm b (hA₀ hb) a ha
      have hbz : Commute b (a * y * a⁻¹) := Subgroup.mem_centralizer_iff.mp hzb b rfl
      have hby : Commute b y := by
        have h1 : Commute b (a⁻¹ * (a * y * a⁻¹) * a) :=
          (hba.inv_right.mul_right hbz).mul_right hba
        have h2 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
        rwa [h2] at h1
      have hyC : y ∈ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]
          exact hby
      have hyθ : y ∈ θ b := hY.2.2.1 b hb hb1 (Subgroup.mem_inf.mpr ⟨hy, hyC⟩)
      exact Subgroup.le_normalizer_iff.mp (hθ.normalized b (hA₀ hb) hb1) a ha y hyθ
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha y hy
    have := hinv a ha (Subgroup.mem_map_of_mem _ hy)
    simpa [MulAut.conj_apply] using this
  have hfix : ∀ a ∈ A, a ≠ 1 → Y ⊓ Subgroup.centralizer {a} ≤ θ a := by
    intro a ha ha1
    have hCA₀ : A₀ ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer {a} : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      obtain ⟨hyY, hya⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer_iff.mp hY.1 x hx y hyY, ?_⟩
      have hxa : Commute a x := hcomm a ha x (hA₀ hx)
      have hay : Commute a y := Subgroup.mem_centralizer_iff.mp hya a rfl
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact (hxa.mul_right hay).mul_right hxa.inv_right
    have hCcop : Nat.Coprime p (Nat.card (Y ⊓ Subgroup.centralizer {a} : Subgroup G)) :=
      hY.2.1.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    calc Y ⊓ Subgroup.centralizer {a}
        = ⨆ (b : G) (_ : b ∈ A₀) (_ : b ≠ 1),
            (Y ⊓ Subgroup.centralizer {a}) ⊓ Subgroup.centralizer {b} :=
          (iSup_inf_centralizer hp hA₀e hrank hCA₀ hCcop).symm
      _ ≤ θ a := by
        refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
        intro x hx
        obtain ⟨⟨hxY, hxa⟩, hxb⟩ := Subgroup.mem_inf.mp hx |>.imp Subgroup.mem_inf.mp id
        have hxθ : x ∈ θ b := hY.2.2.1 b hb hb1 (Subgroup.mem_inf.mpr ⟨hxY, hxb⟩)
        exact hθ.balance b (hA₀ hb) hb1 a ha ha1 (Subgroup.mem_inf.mpr ⟨hxθ, hxa⟩)
  exact ⟨Y, ⟨hAY, hY.2.1, hfix, hY.2.2.2⟩, fun X hX =>
    hYmax X (signalizers_subset_of_le_left hA₀ hX)⟩

end CFSG.SignalizerFunctorTheorem.McBride
