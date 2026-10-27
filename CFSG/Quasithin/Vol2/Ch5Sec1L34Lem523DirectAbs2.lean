module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs1

public section

namespace CFSG.Quasithin.H13.Abs523

variable {E : Type} [CommGroup E] [Finite E]

@[expose] def GInv (𝒦 : Subgroup (MulAut E)) (v : MulAut E) (Y : Subgroup E) : Prop :=
  (∀ k ∈ 𝒦, ∀ y ∈ Y, k y ∈ Y) ∧ (∀ y ∈ Y, v y ∈ Y)

@[expose] def fixIn (𝒦 : Subgroup (MulAut E)) (Y : Subgroup E) : Subgroup E where
  carrier := {y | y ∈ Y ∧ ∀ k ∈ 𝒦, k y = y}
  mul_mem' := fun {a b} ha hb => ⟨Y.mul_mem ha.1 hb.1, fun k hk => by
    rw [map_mul, ha.2 k hk, hb.2 k hk]⟩
  one_mem' := ⟨Y.one_mem, fun k _ => map_one k⟩
  inv_mem' := fun {a} ha => ⟨Y.inv_mem ha.1, fun k hk => by
    rw [map_inv, ha.2 k hk]⟩

theorem mem_fixIn {𝒦 : Subgroup (MulAut E)} {Y : Subgroup E} {y : E} :
    y ∈ fixIn 𝒦 Y ↔ y ∈ Y ∧ ∀ k ∈ 𝒦, k y = y := Iff.rfl

theorem conj_mem_of_normalizer {𝒦 : Subgroup (MulAut E)} {v : MulAut E}
    (hv : v ∈ Subgroup.normalizer (𝒦 : Set (MulAut E))) (k : MulAut E) (hk : k ∈ 𝒦) :
    v⁻¹ * k * v ∈ 𝒦 := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv) k).mp hk
  simpa using h

theorem fixIn_GInv {𝒦 : Subgroup (MulAut E)} {v : MulAut E}
    (hv : v ∈ Subgroup.normalizer (𝒦 : Set (MulAut E))) {Y : Subgroup E} (hY : GInv 𝒦 v Y) :
    GInv 𝒦 v (fixIn 𝒦 Y) := by
  refine ⟨fun k hk y hy => ?_, fun y hy => ?_⟩
  · have hyk : k y = y := (mem_fixIn.mp hy).2 k hk
    rw [hyk]
    exact hy
  · refine mem_fixIn.mpr ⟨hY.2 y (mem_fixIn.mp hy).1, fun l hl => ?_⟩
    have h1 : v⁻¹ * l * v ∈ 𝒦 := conj_mem_of_normalizer hv l hl
    have h2 : (v⁻¹ * l * v) y = y := (mem_fixIn.mp hy).2 _ h1
    calc l (v y) = v ((v⁻¹ * l * v) y) := by simp [MulAut.mul_apply]
      _ = v y := by rw [h2]

theorem exists_section (𝒦 : Subgroup (MulAut E)) (v : MulAut E)
    (hv : v ∈ Subgroup.normalizer (𝒦 : Set (MulAut E)))
    (hperf : ⁅(⊤ : Subgroup 𝒦), (⊤ : Subgroup 𝒦)⁆ = ⊤) (hnt : ∃ k ∈ 𝒦, k ≠ 1) :
    ∃ Y₀ Y₁ : Subgroup E, Y₀ < Y₁ ∧ GInv 𝒦 v Y₀ ∧ GInv 𝒦 v Y₁ ∧
      (∀ Z : Subgroup E, Y₀ ≤ Z → Z ≤ Y₁ → GInv 𝒦 v Z → Z = Y₀ ∨ Z = Y₁) ∧
      (∃ k ∈ 𝒦, ∃ y ∈ Y₁, k y * y⁻¹ ∉ Y₀) := by
  classical
  obtain ⟨k₀, hk₀𝒦, hk₀⟩ := hnt
  obtain ⟨x₀, hx₀⟩ : ∃ x : E, k₀ x ≠ x := by
    by_contra h
    push Not at h
    exact hk₀ (MulEquiv.ext fun x => by simpa using h x)
  let 𝒮 : Set (Subgroup E) := {Y | GInv 𝒦 v Y ∧ ∃ k ∈ 𝒦, ∃ y ∈ Y, k y ≠ y}
  have hTop : (⊤ : Subgroup E) ∈ 𝒮 :=
    ⟨⟨fun _ _ _ _ => trivial, fun _ _ => trivial⟩, k₀, hk₀𝒦, x₀, trivial, hx₀⟩
  obtain ⟨Y₁, hY₁𝒮, hmin⟩ := WellFounded.has_min wellFounded_lt 𝒮 ⟨⊤, hTop⟩
  obtain ⟨hY₁inv, k₁, hk₁𝒦, y₁, hy₁Y, hy₁⟩ := hY₁𝒮
  set Y₀ := fixIn 𝒦 Y₁ with hY₀
  have hY₀Y₁ : Y₀ ≤ Y₁ := fun y hy => (mem_fixIn.mp hy).1
  have hY₀inv : GInv 𝒦 v Y₀ := fixIn_GInv hv hY₁inv
  have hlt : Y₀ < Y₁ := by
    refine lt_of_le_of_ne hY₀Y₁ fun h => hy₁ ?_
    have : y₁ ∈ Y₀ := by rw [h]; exact hy₁Y
    exact (mem_fixIn.mp this).2 k₁ hk₁𝒦
  refine ⟨Y₀, Y₁, hlt, hY₀inv, hY₁inv, ?_, ?_⟩
  ·
    intro Z hZ₀ hZ₁ hZinv
    by_cases hZY : Z = Y₁
    · exact Or.inr hZY
    · left
      have hlt' : Z < Y₁ := lt_of_le_of_ne hZ₁ hZY
      have hnot : Z ∉ 𝒮 := fun hZ𝒮 => hmin Z hZ𝒮 hlt'
      have hfix : Z ≤ Y₀ := by
        intro z hz
        refine mem_fixIn.mpr ⟨hZ₁ hz, fun k hk => ?_⟩
        by_contra hne
        exact hnot ⟨hZinv, k, hk, z, hz, hne⟩
      exact le_antisymm hfix hZ₀
  ·
    by_contra hcon
    push Not at hcon
    have hshift : ∀ k ∈ 𝒦, ∀ l ∈ 𝒦, ∀ y ∈ Y₁, k (l y) * (l y)⁻¹ = k y * y⁻¹ := by
      intro k hk l hl y hy
      obtain ⟨w, hw⟩ : ∃ w, w = l y * y⁻¹ := ⟨_, rfl⟩
      have hwY : w ∈ Y₀ := by rw [hw]; exact hcon l hl y hy
      have hkw : k w = w := (mem_fixIn.mp hwY).2 k hk
      have e1 : l y = w * y := by rw [hw, inv_mul_cancel_right]
      rw [e1, map_mul, hkw, mul_inv]
      calc w * k y * (w⁻¹ * y⁻¹) = (w * w⁻¹) * (k y * y⁻¹) := by ac_rfl
        _ = k y * y⁻¹ := by rw [mul_inv_cancel, one_mul]
    have hmulψ : ∀ k ∈ 𝒦, ∀ l ∈ 𝒦, ∀ y ∈ Y₁, (k * l) y * y⁻¹ = (k y * y⁻¹) * (l y * y⁻¹) := by
      intro k hk l hl y hy
      rw [MulAut.mul_apply]
      calc k (l y) * y⁻¹ = (k (l y) * (l y)⁻¹) * (l y * y⁻¹) := by
            rw [mul_assoc, inv_mul_cancel_left]
        _ = (k y * y⁻¹) * (l y * y⁻¹) := by rw [hshift k hk l hl y hy]
    let Ψ : (↥𝒦) →* (↥Y₁ → E) :=
      { toFun := fun g y => (g : MulAut E) (y : E) * (y : E)⁻¹
        map_one' := by
          funext y
          simp
        map_mul' := by
          intro g h
          funext y
          exact hmulψ g.1 g.2 h.1 h.2 y y.2 }
    have hΨ : ∀ g : ↥𝒦, Ψ g = 1 := by
      intro g
      have htop : (⊤ : Subgroup ↥𝒦) ≤ Ψ.ker := by
        rw [← hperf]
        refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
      exact MonoidHom.mem_ker.mp (htop (Subgroup.mem_top g))
    have hk1 := congrFun (hΨ ⟨k₁, hk₁𝒦⟩) ⟨y₁, hy₁Y⟩
    have hk1' : k₁ y₁ * y₁⁻¹ = 1 := by
      simpa [Ψ] using hk1
    exact hy₁ (mul_inv_eq_one.mp hk1')

end CFSG.Quasithin.H13.Abs523
