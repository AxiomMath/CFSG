module

public import CFSG.SignalizerFunctorTheorem.NonLocal.HeisFam
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisChevalley
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

section FieldAlgebra

variable {k : Type} [Field k] (σ : k →+* k)

theorem sign_cases {ε : k} (h : ε * ε = 1) : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.1 h

theorem map_sign {ε : k} (h : ε * ε = 1) : σ ε = ε := by
  rcases sign_cases h with rfl | rfl <;> simp

theorem eq_of_forall_invariant (hσ2 : ∀ u, σ (σ u) = u) (hne : ∃ u, σ u ≠ u) {ε₀ : k}
    (hε₀ : ε₀ * ε₀ = 1) {p q : k} (hp : σ p = p) (hq : σ q = q)
    (h : ∀ u, p * u + q * σ u = ε₀ * σ (p * u + q * σ u)) : q = ε₀ * p := by
  have h' : ∀ u, p * u + q * σ u = ε₀ * (p * σ u + q * u) := fun u => by
    rw [h u, map_add, map_mul, map_mul, hp, hq, hσ2]
  have hX : ∀ u, (p - ε₀ * q) * (u - ε₀ * σ u) = 0 := fun u => by
    linear_combination (h' u) + (q * σ u) * hε₀
  obtain ⟨u₁, hu₁⟩ : ∃ u, u - ε₀ * σ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu⟩ := hne
    have h1 := hcon 1
    rw [map_one, mul_one, sub_eq_zero] at h1
    have h2 := hcon u
    rw [← h1, one_mul, sub_eq_zero] at h2
    exact hu h2.symm
  have hX1 : p - ε₀ * q = 0 := (mul_eq_zero.1 (hX u₁)).resolve_right hu₁
  linear_combination (-ε₀) * hX1 - q * hε₀

end FieldAlgebra

section GroupAlgebra

theorem commute_of_eq' {M : Type*} [Mul M] {a b : M} (h : a * b = b * a) : Commute a b := h

theorem commutator_mul_mul {G : Type*} [Group G] (Z : Subgroup G)
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) {b₁ b₂ a₁ a₂ : G}
    (hb₁ : ∀ z ∈ Z, b₁ * z = z * b₁) (ha₁ : ∀ z ∈ Z, a₁ * z = z * a₁)
    (h₁₁ : ⁅b₁, a₁⁆ ∈ Z) (h₁₂ : ⁅b₁, a₂⁆ ∈ Z) (h₂₁ : ⁅b₂, a₁⁆ ∈ Z) (h₂₂ : ⁅b₂, a₂⁆ ∈ Z) :
    ⁅b₁ * b₂, a₁ * a₂⁆ = ⁅b₁, a₁⁆ * ⁅b₁, a₂⁆ * (⁅b₂, a₁⁆ * ⁅b₂, a₂⁆) := by
  have key : ⁅b₁ * b₂, a₁ * a₂⁆ = b₁ * (⁅b₂, a₁⁆ * (a₁ * ⁅b₂, a₂⁆ * a₁⁻¹)) * b₁⁻¹ *
      (⁅b₁, a₁⁆ * (a₁ * ⁅b₁, a₂⁆ * a₁⁻¹)) := by
    simp only [commutatorElement_def]
    group
  have e1 : a₁ * ⁅b₂, a₂⁆ * a₁⁻¹ = ⁅b₂, a₂⁆ := by rw [ha₁ _ h₂₂, mul_inv_cancel_right]
  have e2 : a₁ * ⁅b₁, a₂⁆ * a₁⁻¹ = ⁅b₁, a₂⁆ := by rw [ha₁ _ h₁₂, mul_inv_cancel_right]
  have e3 : b₁ * (⁅b₂, a₁⁆ * ⁅b₂, a₂⁆) * b₁⁻¹ = ⁅b₂, a₁⁆ * ⁅b₂, a₂⁆ := by
    rw [hb₁ _ (mul_mem h₂₁ h₂₂), mul_inv_cancel_right]
  rw [key, e1, e2, e3]
  exact hZ _ (mul_mem h₂₁ h₂₂) _ (mul_mem h₁₁ h₁₂)

end GroupAlgebra

section RootData

@[expose] def e6BCodes : Fin 3 → ℕ := ![9017496, 10066072, 10066328]

@[expose] def e6RCodes : Fin 3 → ℕ := ![8952216, 8952217, 9017753]

@[expose] def e6B (j : Fin 3) : Fin TwistTag.E6.tag.rank → ℤ := decodeVec (e6BCodes j)

@[expose] def e6R (j : Fin 3) : Fin TwistTag.E6.tag.rank → ℤ := decodeVec (e6RCodes j)

theorem e6B_mem (j : Fin 3) : e6B j ∈ heisS TwistTag.E6.tag :=
  mem_heisS.2 ⟨e6BCodes j, by fin_cases j <;> decide, rfl⟩

theorem e6R_mem (j : Fin 3) : e6R j ∈ heisS TwistTag.E6.tag :=
  mem_heisS.2 ⟨e6RCodes j, by fin_cases j <;> decide, rfl⟩

theorem permLattice_e6B (j : Fin 3) :
    permLattice TwistTag.E6.perm (e6B j) = e6R j := by
  fin_cases j <;> decide +kernel

theorem permLattice_heisα0 :
    permLattice TwistTag.E6.perm (heisα0 TwistTag.E6.tag) = heisα0 TwistTag.E6.tag := by
  decide +kernel

theorem e6B_ne_e6R (j : Fin 3) : e6B j ≠ e6R j := by
  fin_cases j <;> decide +kernel

theorem e6_distinct : ∀ j j' : Fin 3, j ≠ j' →
    e6B j ≠ e6B j' ∧ e6B j ≠ e6R j' ∧ e6R j ≠ e6B j' ∧ e6R j ≠ e6R j' := by
  decide +kernel

end RootData

theorem hF6 :
    HeisFacts TwistTag.E6.tag := heisFacts_E6

theorem heisα0_pos :
    0 < height (heisα0 TwistTag.E6.tag) := by
  have h1 := hF6.two_height_lt _ (e6B_mem 0)
  have h2 := hF6.pos_of_mem _ (e6B_mem 0)
  omega

section Commutation

variable {k : Type} [Field k]

theorem commute_S {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (c d : k) :
    pinnedX TwistTag.E6.tag k x c * pinnedX TwistTag.E6.tag k y d =
      pinnedX TwistTag.E6.tag k y d * pinnedX TwistTag.E6.tag k x c :=
  pinned_comm_of_not_isRoot (τ := TwistTag.E6.tag) (Or.inl rfl) (hF6.isRoot_of_mem x hx)
    (hF6.isRoot_of_mem y hy)
    (hF6.pos_of_mem x hx) (hF6.pos_of_mem y hy) (hF6.not_isRoot_SS x hx y hy) c d

theorem commute_T {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (c d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - x) c *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - y) d =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - y) d *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - x) c :=
  pinned_comm_of_not_isRoot (τ := TwistTag.E6.tag) (Or.inl rfl) (hF6.isRoot_sub x hx)
    (hF6.isRoot_sub y hy)
    (heis_gamma_pos (hF := hF6) hx) (heis_gamma_pos (hF := hF6) hy)
    (hF6.not_isRoot_TT x hx y hy) c d

theorem commute_α0_S {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (c d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) c * pinnedX TwistTag.E6.tag k x d =
      pinnedX TwistTag.E6.tag k x d * pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) c :=
  pinned_comm_of_not_isRoot (τ := TwistTag.E6.tag) (Or.inl rfl) hF6.isRoot_α0
    (hF6.isRoot_of_mem x hx) heisα0_pos
    (hF6.pos_of_mem x hx) (hF6.not_isRoot_α0_S x hx) c d

theorem commute_α0_T {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (c d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) c *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - x) d =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - x) d *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) c :=
  pinned_comm_of_not_isRoot (τ := TwistTag.E6.tag) (Or.inl rfl) hF6.isRoot_α0
    (hF6.isRoot_sub x hx) heisα0_pos
    (heis_gamma_pos (hF := hF6) hx) (hF6.not_isRoot_α0_T x hx) c d

theorem commute_T_S {s s' : Fin TwistTag.E6.tag.rank → ℤ} (hs : s ∈ heisS TwistTag.E6.tag)
    (hs' : s' ∈ heisS TwistTag.E6.tag) (hne : s ≠ s') (c d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - s) c * pinnedX TwistTag.E6.tag k s' d =
      pinnedX TwistTag.E6.tag k s' d * pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - s) c :=
  pinned_comm_of_not_isRoot (τ := TwistTag.E6.tag) (Or.inl rfl) (hF6.isRoot_sub s hs)
    (hF6.isRoot_of_mem s' hs')
    (heis_gamma_pos (hF := hF6) hs) (hF6.pos_of_mem s' hs')
    (by rw [add_comm]; exact hF6.not_isRoot_ST s' hs' s hs (Ne.symm hne)) c d

theorem exists_comm_T_S {s : Fin TwistTag.E6.tag.rank → ℤ} (hs : s ∈ heisS TwistTag.E6.tag) :
    ∃ η : k, η * η = 1 ∧ ∀ c d : k,
      ⁅pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - s) c, pinnedX TwistTag.E6.tag k s d⁆ =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (η * c * d) := by
  have hβpos := hF6.pos_of_mem s hs
  have hlt := hF6.two_height_lt s hs
  have hne : heisα0 TwistTag.E6.tag - s ≠ s := fun h => hF6.sub_not_mem s hs (by rw [h]; exact hs)
  have hsum : heisα0 TwistTag.E6.tag - s + s = heisα0 TwistTag.E6.tag := sub_add_cancel _ _
  obtain ⟨ε', hε', hf⟩ := exists_pinned_comm_of_isRoot (τ := TwistTag.E6.tag) (Or.inl rfl)
    (hF6.isRoot_sub s hs) (hF6.isRoot_of_mem s hs) (heis_gamma_pos (hF := hF6) hs) hβpos hne
    (by rw [hsum]; exact hF6.isRoot_α0)
  refine ⟨(ε' : k), ?_, fun c d => ?_⟩
  · rcases hε' with rfl | rfl <;> simp
  · have := hf k c d
    simp only [hsum] at this
    exact this

end Commutation

section Twist

variable {k : Type} [Field k]
  (σ : k →+* k)

theorem twist_pinnedX {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    ∃ ε : k, ε * ε = 1 ∧ ∀ c : k, twistHom TwistTag.E6 k σ (pinnedX TwistTag.E6.tag k α c) =
      pinnedX TwistTag.E6.tag k (permLattice TwistTag.E6.perm α) (ε * σ c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := k) TwistTag.E6 hα
  refine ⟨ε, hε, fun c => ?_⟩
  rw [twistHom_apply, show Units.map (entrywiseHom σ) (pinnedX TwistTag.E6.tag k α c) =
    pinnedX TwistTag.E6.tag k α (σ c) from Units.ext (entrywise_pinnedX σ α c), h (σ c)]

theorem twist_twist (hσ2 : ∀ c, σ (σ c) = c) (g : ModGL TwistTag.E6.tag k) :
    twistHom TwistTag.E6 k σ (twistHom TwistTag.E6 k σ g) = g := by
  have hσ : σ ^ TwistTag.E6.order = 1 := RingHom.ext fun c => by
    show σ (σ c) = c
    exact hσ2 c
  exact twistHom_iterate_order_of_pow_eq_one σ hσ g

@[expose] def orb (α : Fin TwistTag.E6.tag.rank → ℤ) (c : k) : ModGL TwistTag.E6.tag k :=
  pinnedX TwistTag.E6.tag k α c * twistHom TwistTag.E6 k σ (pinnedX TwistTag.E6.tag k α c)

@[expose] def Comm2 (α : Fin TwistTag.E6.tag.rank → ℤ) : Prop :=
  ∀ c d : k, pinnedX TwistTag.E6.tag k α c * pinnedX TwistTag.E6.tag k (permLattice
    TwistTag.E6.perm α) d = pinnedX TwistTag.E6.tag k (permLattice TwistTag.E6.perm α) d *
      pinnedX TwistTag.E6.tag k α c

theorem twist_orb_eq {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hσ2 : ∀ c, σ (σ c) = c) (hc : Comm2 (k := k) α) (c : k) :
    twistHom TwistTag.E6 k σ (orb σ α c) = orb σ α c := by
  obtain ⟨ε, hε, hF⟩ := twist_pinnedX σ hα
  unfold orb
  rw [map_mul, twist_twist σ hσ2, hF c]
  exact (hc c (ε * σ c)).symm

theorem orb_mem {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hpos : 0 < height α) (hσ2 : ∀ c, σ (σ c) = c) (hc : Comm2 (k := k) α) (c : k) :
    orb σ α c ∈ graphFixedRootGroup TwistTag.E6 k σ := by
  obtain ⟨ε, hε, hF⟩ := twist_pinnedX σ hα
  have hρα : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
    hα.permLattice TwistTag.E6.cartan_perm
  have hρpos : 0 < height (permLattice TwistTag.E6.perm α) := by
    rw [height_permLattice]; exact hpos
  have hU : ∀ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β → 0 < height β →
      ∀ x : k, pinnedX TwistTag.E6.tag k β x ∈ posUnipotent TwistTag.E6.tag k := fun β hβ hp x =>
    rootSpan_le_posUnipotent (S := {x | IsRoot TwistTag.E6.tag x ∧ 0 < height x}) (fun _ h => h)
      (pinnedX_mem_rootSpan (S := {x | IsRoot TwistTag.E6.tag x ∧ 0 < height x}) ⟨hβ, hp⟩ x)
  refine graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 k σ ?_
  refine Subgroup.mem_inf.2 ⟨?_, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨?_, twist_orb_eq σ hα hσ2 hc c⟩⟩
  · unfold orb
    rw [hF c]
    exact mul_mem (hU α hα hpos c) (hU _ hρα hρpos _)
  · unfold orb
    rw [hF c]
    exact mul_mem (pinnedX_mem_adjointGroup α c) (pinnedX_mem_adjointGroup _ _)

end Twist

section OrbitCommutation

variable {k : Type} [Field k]
  (σ : k →+* k)

theorem permLattice_sub_heisα0 (x : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (heisα0 TwistTag.E6.tag - x) =
      heisα0 TwistTag.E6.tag - permLattice TwistTag.E6.perm x := by
  rw [permLattice_sub, permLattice_heisα0]

theorem commute_orb_S {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (hy' : permLattice TwistTag.E6.perm y ∈ heisS TwistTag.E6.tag)
    (c d : k) : orb σ x c * orb σ y d = orb σ y d * orb σ x c := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_of_mem x hx)
  obtain ⟨εy, -, hFy⟩ := twist_pinnedX σ (hF6.isRoot_of_mem y hy)
  unfold orb
  rw [hFx c, hFy d]
  exact ((commute_of_eq' (commute_S hx hy _ _)).mul_right (commute_of_eq' (commute_S hx hy' _ _))
    |>.mul_left ((commute_of_eq' (commute_S hx' hy _ _)).mul_right
      (commute_of_eq' (commute_S hx' hy' _ _)))).eq

theorem commute_orb_T {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (hy' : permLattice TwistTag.E6.perm y ∈ heisS TwistTag.E6.tag)
    (c d : k) : orb σ (heisα0 TwistTag.E6.tag - x) c * orb σ (heisα0 TwistTag.E6.tag - y) d =
      orb σ (heisα0 TwistTag.E6.tag - y) d * orb σ (heisα0 TwistTag.E6.tag - x) c := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_sub x hx)
  obtain ⟨εy, -, hFy⟩ := twist_pinnedX σ (hF6.isRoot_sub y hy)
  rw [permLattice_sub_heisα0] at hFx hFy
  unfold orb
  rw [hFx c, hFy d]
  exact ((commute_of_eq' (commute_T hx hy _ _)).mul_right (commute_of_eq' (commute_T hx hy' _ _))
    |>.mul_left ((commute_of_eq' (commute_T hx' hy _ _)).mul_right
      (commute_of_eq' (commute_T hx' hy' _ _)))).eq

theorem commute_orb_T_S {s s' : Fin TwistTag.E6.tag.rank → ℤ} (hs : s ∈ heisS TwistTag.E6.tag)
    (hs₁ : permLattice TwistTag.E6.perm s ∈ heisS TwistTag.E6.tag)
    (hs' : s' ∈ heisS TwistTag.E6.tag)
    (hs'₁ : permLattice TwistTag.E6.perm s' ∈ heisS TwistTag.E6.tag)
    (h11 : s ≠ s') (h12 : s ≠ permLattice TwistTag.E6.perm s')
    (h21 : permLattice TwistTag.E6.perm s ≠ s')
    (h22 : permLattice TwistTag.E6.perm s ≠ permLattice TwistTag.E6.perm s') (c d : k) :
    orb σ (heisα0 TwistTag.E6.tag - s) c * orb σ s' d =
      orb σ s' d * orb σ (heisα0 TwistTag.E6.tag - s) c := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_sub s hs)
  obtain ⟨εy, -, hFy⟩ := twist_pinnedX σ (hF6.isRoot_of_mem s' hs')
  rw [permLattice_sub_heisα0] at hFx
  unfold orb
  rw [hFx c, hFy d]
  exact ((commute_of_eq' (commute_T_S hs hs' h11 _ _)).mul_right
      (commute_of_eq' (commute_T_S hs hs'₁ h12 _ _))
    |>.mul_left ((commute_of_eq' (commute_T_S hs₁ hs' h21 _ _)).mul_right
      (commute_of_eq' (commute_T_S hs₁ hs'₁ h22 _ _)))).eq

theorem commute_α0_orb_S {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag) (w d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w * orb σ x d =
      orb σ x d * pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_of_mem x hx)
  unfold orb
  rw [hFx d]
  exact ((commute_of_eq' (commute_α0_S hx w _)).mul_right
    (commute_of_eq' (commute_α0_S hx' w _))).eq

theorem commute_α0_orb_T {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag) (w d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w *
        orb σ (heisα0 TwistTag.E6.tag - x) d =
      orb σ (heisα0 TwistTag.E6.tag - x) d *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_sub x hx)
  rw [permLattice_sub_heisα0] at hFx
  unfold orb
  rw [hFx d]
  exact ((commute_of_eq' (commute_α0_T hx w _)).mul_right
    (commute_of_eq' (commute_α0_T hx' w _))).eq

theorem comm2_B (j : Fin 3) : Comm2 (k := k) (e6B j) := fun c d => by
  rw [permLattice_e6B]
  exact commute_S (e6B_mem j) (e6R_mem j) c d

theorem comm2_T (j : Fin 3) : Comm2 (k := k) (heisα0 TwistTag.E6.tag - e6B j) := fun c d => by
  rw [permLattice_sub_heisα0, permLattice_e6B]
  exact commute_T (e6B_mem j) (e6R_mem j) c d

end OrbitCommutation

section RootSubgroup

theorem commute_rootSubgroup_E6
    {k : Type} [Field k] (α : Fin TwistTag.E6.tag.rank → ℤ) :
    ∀ x ∈ rootSubgroup TwistTag.E6.tag k α, ∀ y ∈ rootSubgroup TwistTag.E6.tag k α,
      x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hy
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

end RootSubgroup

section Pair

variable {k : Type} [Field k]
  (σ : k →+* k)

theorem pair_comm (hσ2 : ∀ c, σ (σ c) = c) (hne : ∃ u, σ u ≠ u) {ε₀ : k} (hε₀ : ε₀ * ε₀ = 1)
    (hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
        (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w)) (j : Fin 3) :
    ∃ p : k, p * p = 1 ∧ ∀ c d : k,
      ⁅(orb σ (heisα0 TwistTag.E6.tag - e6B j) c)⁻¹, orb σ (e6B j) d⁆ =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (p * c * d + ε₀ * σ (p * c * d)) := by
  have hβ : e6B j ∈ heisS TwistTag.E6.tag := e6B_mem j
  have hβ' : e6R j ∈ heisS TwistTag.E6.tag := e6R_mem j
  have hne' : e6B j ≠ e6R j := e6B_ne_e6R j
  have hργ : permLattice TwistTag.E6.perm (heisα0 TwistTag.E6.tag - e6B j) =
      heisα0 TwistTag.E6.tag - e6R j := by
    rw [permLattice_sub, permLattice_heisα0, permLattice_e6B]
  obtain ⟨εγ, hεγ, hFγ⟩ := twist_pinnedX σ (hF6.isRoot_sub _ hβ)
  obtain ⟨εβ, hεβ, hFβ⟩ := twist_pinnedX σ (hF6.isRoot_of_mem _ hβ)
  rw [hργ] at hFγ
  rw [permLattice_e6B] at hFβ
  obtain ⟨η₁, hη₁, h₁⟩ := exists_comm_T_S (k := k) hβ
  obtain ⟨η₂, hη₂, h₂⟩ := exists_comm_T_S (k := k) hβ'
  have hcγ : Comm2 (k := k) (heisα0 TwistTag.E6.tag - e6B j) := fun c d => by
    rw [hργ]
    exact commute_T hβ hβ' c d
  have hcβ : Comm2 (k := k) (e6B j) := fun c d => by
    rw [permLattice_e6B]
    exact commute_S hβ hβ' c d
  have hoγ : ∀ c, orb σ (heisα0 TwistTag.E6.tag - e6B j) c =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - e6B j) c *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - e6R j) (εγ * σ c) := fun c => by
    unfold orb
    rw [hFγ c]
  have hoβ : ∀ d, orb σ (e6B j) d = pinnedX TwistTag.E6.tag k (e6B j) d *
      pinnedX TwistTag.E6.tag k (e6R j) (εβ * σ d) := fun d => by
    unfold orb
    rw [hFβ d]
  set Z := rootSubgroup TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) with hZ
  have hZmem : ∀ w : k, pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w ∈ Z := fun w =>
    mem_rootSubgroup.2 ⟨w, rfl⟩
  have hcomm : ∀ c d : k,
      ⁅(orb σ (heisα0 TwistTag.E6.tag - e6B j) c)⁻¹, orb σ (e6B j) d⁆ =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
          (-η₁ * (c * d) + (-(η₂ * εγ * εβ)) * σ (c * d)) := fun c d => by
    rw [hoγ, hoβ, mul_inv_rev, pinnedX_neg, pinnedX_neg]
    rw [commutator_mul_mul Z (commute_rootSubgroup_E6 _)
      (b₁ := pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - e6R j) (-(εγ * σ c)))
      (b₂ := pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - e6B j) (-c))
      (a₁ := pinnedX TwistTag.E6.tag k (e6B j) d)
      (a₂ := pinnedX TwistTag.E6.tag k (e6R j) (εβ * σ d))
      (fun z hz => by
        obtain ⟨w, rfl⟩ := mem_rootSubgroup.1 hz
        exact (commute_α0_T hβ' w _).symm)
      (fun z hz => by
        obtain ⟨w, rfl⟩ := mem_rootSubgroup.1 hz
        exact (commute_α0_S hβ w _).symm)
      ?_ ?_ ?_ ?_]
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (commute_T_S hβ' hβ hne'.symm _ _), h₂, h₁,
        commutatorElement_eq_one_iff_mul_comm.2 (commute_T_S hβ hβ' hne' _ _), one_mul, mul_one,
        ← pinnedX_add]
      congr 1
      rw [map_mul]
      ring
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (commute_T_S hβ' hβ hne'.symm _ _)]
      exact one_mem _
    · rw [h₂]
      exact hZmem _
    · rw [h₁]
      exact hZmem _
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (commute_T_S hβ hβ' hne' _ _)]
      exact one_mem _
  have hp : σ (-η₁) = -η₁ := by rw [map_neg, map_sign σ hη₁]
  have hq : σ (-(η₂ * εγ * εβ)) = -(η₂ * εγ * εβ) := by
    rw [map_neg, map_mul, map_mul, map_sign σ hη₂, map_sign σ hεγ, map_sign σ hεβ]
  have hinv : ∀ u : k, (-η₁) * u + (-(η₂ * εγ * εβ)) * σ u =
      ε₀ * σ ((-η₁) * u + (-(η₂ * εγ * εβ)) * σ u) := fun u => by
    have h1 := hcomm 1 u
    simp only [one_mul] at h1
    have hfix : twistHom TwistTag.E6 k σ
        ⁅(orb σ (heisα0 TwistTag.E6.tag - e6B j) 1)⁻¹, orb σ (e6B j) u⁆ =
        ⁅(orb σ (heisα0 TwistTag.E6.tag - e6B j) 1)⁻¹, orb σ (e6B j) u⁆ := by
      rw [map_commutatorElement, map_inv, twist_orb_eq σ (hF6.isRoot_sub _ hβ) hσ2 hcγ,
        twist_orb_eq σ (hF6.isRoot_of_mem _ hβ) hσ2 hcβ]
    rw [h1, hF₀] at hfix
    exact (pinnedX_injective TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) hfix).symm
  have hqp := eq_of_forall_invariant σ hσ2 hne hε₀ hp hq hinv
  refine ⟨-η₁, by rw [neg_mul_neg]; exact hη₁, fun c d => ?_⟩
  rw [hcomm c d]
  congr 1
  rw [hqp]
  simp only [map_mul, hp]
  ring

end Pair

section Main

variable {k : Type} [Field k]
  (σ : k →+* k)

theorem z_mem (hσ2 : ∀ c, σ (σ c) = c) {ε₀ : k} (hε₀ : ε₀ * ε₀ = 1)
    (hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
        (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w)) (w : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + ε₀ * σ w) ∈
      graphFixedRootGroup TwistTag.E6 k σ := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 k σ ?_
  refine Subgroup.mem_inf.2 ⟨?_, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  · exact rootSpan_le_posUnipotent (S := {x | IsRoot TwistTag.E6.tag x ∧ 0 < height x})
      (fun _ h => h) (pinnedX_mem_rootSpan (S := {x | IsRoot TwistTag.E6.tag x ∧ 0 < height x})
        ⟨hF6.isRoot_α0, heisα0_pos⟩ _)
  · rw [hF₀]
    congr 1
    rw [map_add, map_mul, hσ2, map_sign σ hε₀]
    linear_combination w * hε₀

theorem exists_heisFam_E6 (hσ2 : ∀ c, σ (σ c) = c) (hne : ∃ u, σ u ≠ u) :
    ∃ H : HeisFam ↥(graphFixedRootGroup TwistTag.E6 k σ) (Fin 3) (fun _ => k) k,
      ∃ w ∈ H.Rg, H.z w ≠ 1 ∧ ((2 : k) = 0 → H.z w * H.z w = 1) := by
  classical
  obtain ⟨ε₀, hε₀, hF₀'⟩ := twist_pinnedX σ (hF6.isRoot_α0 (τ := TwistTag.E6.tag))
  have hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
      (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w) := fun w => by
    rw [hF₀' w, permLattice_heisα0]
  choose p hp1 hp2 using pair_comm σ hσ2 hne hε₀ hF₀
  have hp0 : ∀ j, p j ≠ 0 := fun j h => by
    have := hp1 j
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hρB : ∀ j, permLattice TwistTag.E6.perm (e6B j) ∈ heisS TwistTag.E6.tag := fun j => by
    rw [permLattice_e6B]; exact e6R_mem j
  have hxa : ∀ (j : Fin 3) (d : k), orb σ (e6B j) d ∈ graphFixedRootGroup TwistTag.E6 k σ :=
    fun j d => orb_mem σ (hF6.isRoot_of_mem _ (e6B_mem j)) (hF6.pos_of_mem _ (e6B_mem j)) hσ2
      (comm2_B j) d
  have hxb : ∀ (j : Fin 3) (c : k),
      orb σ (heisα0 TwistTag.E6.tag - e6B j) c ∈ graphFixedRootGroup TwistTag.E6 k σ :=
    fun j c => orb_mem σ (hF6.isRoot_sub _ (e6B_mem j)) (heis_gamma_pos (hF := hF6) (e6B_mem j))
      hσ2 (comm2_T j) c
  have hz := z_mem σ hσ2 hε₀ hF₀
  obtain ⟨w₀, hw₀⟩ : ∃ w : k, w + ε₀ * σ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu⟩ := hne
    have h1 := hcon 1
    rw [map_one, mul_one] at h1
    have h2 := hcon u
    have hε : ε₀ = -1 := by linear_combination h1
    rw [hε] at h2
    exact hu (by linear_combination -h2)
  refine ⟨{ xa := fun j d => ⟨orb σ (e6B j) d, hxa j d⟩
            xb := fun j c => ⟨orb σ (heisα0 TwistTag.E6.tag - e6B j) c, hxb j c⟩
            z := fun w => ⟨pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + ε₀ * σ w),
              hz w⟩
            e := fun j c d => p j * c * d
            Rg := ⊤
            z_add := fun w w' => Subtype.ext (by
              show pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + w' + ε₀ * σ (w + w')) =
                pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + ε₀ * σ w) *
                  pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w' + ε₀ * σ w')
              rw [← pinnedX_add, map_add]
              congr 1
              ring)
            e_add_left := fun s c c' d => by
              show p s * (c + c') * d = p s * c * d + p s * c' * d
              ring
            e_mem := fun _ _ _ => AddSubgroup.mem_top _
            e_surj := fun s c hc w _ => ⟨w / (p s * c), by
              show p s * c * (w / (p s * c)) = w
              have := hp0 s
              field_simp⟩
            xa_comm := fun s t c d => Subtype.ext
              (commute_orb_S σ (e6B_mem s) (hρB s) (e6B_mem t) (hρB t) c d)
            xb_comm := fun s t c d => Subtype.ext
              (commute_orb_T σ (e6B_mem s) (hρB s) (e6B_mem t) (hρB t) c d)
            z_comm_a := fun w s d => Subtype.ext
              (commute_α0_orb_S σ (e6B_mem s) (hρB s) _ d)
            z_comm_b := fun w s d => Subtype.ext
              (commute_α0_orb_T σ (e6B_mem s) (hρB s) _ d)
            xab_comm := fun s t hst c d => Subtype.ext (by
              obtain ⟨h11, h12, h21, h22⟩ := e6_distinct s t hst
              rw [← permLattice_e6B s, ← permLattice_e6B t] at *
              exact (commute_orb_T_S σ (e6B_mem s) (hρB s) (e6B_mem t) (hρB t) h11 h12 h21 h22
                c d))
            comm_ss := fun s c d => Subtype.ext (hp2 s c d) }, w₀, AddSubgroup.mem_top _, ?_, ?_⟩
  · intro h
    have h1 := congrArg Subtype.val h
    exact hw₀ (pinnedX_injective TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
      (h1.trans (pinnedX_zero _ _ _).symm))
  · intro h2
    refine Subtype.ext ?_
    show pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w₀ + ε₀ * σ w₀) *
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w₀ + ε₀ * σ w₀) = 1
    rw [← pinnedX_add]
    have : w₀ + ε₀ * σ w₀ + (w₀ + ε₀ * σ w₀) = 0 := by
      linear_combination (w₀ + ε₀ * σ w₀) * h2
    rw [this, pinnedX_zero]

theorem no_small_faithful_action_E6 [Finite k] (hσ2 : ∀ c, σ (σ c) = c) (hne : ∃ u, σ u ≠ u)
    (hk : 78 < Nat.card k ^ 3 ∨ ((2 : k) = 0 ∧ 78 < 2 * Nat.card k ^ 3)) {Λ : Type} [Finite Λ]
    (hΛ : Nat.card Λ ≤ 78) (π : ↥(graphFixedRootGroup TwistTag.E6 k σ) →* Equiv.Perm Λ)
    (hπ : Function.Injective π) : False := by
  classical
  have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  obtain ⟨H, w, hwR, hw1, hw2⟩ := exists_heisFam_E6 σ hσ2 hne
  have hnt : π (H.z w) ≠ 1 := fun h => hw1 (hπ (h.trans (map_one π).symm))
  have hcard : Nat.card (∀ _ : Fin 3, k) = Nat.card k ^ 3 := by
    rw [Nat.card_pi]
    simp
  rcases hk with hk | ⟨h2, hk⟩
  · have := H.card_le_perm π ⟨w, hwR, hnt⟩
    rw [hcard] at this
    omega
  · have := H.two_mul_card_le_perm π ⟨w, hwR, hw2 h2, hnt⟩
    rw [hcard] at this
    omega

end Main

end CFSG.SignalizerFunctorTheorem.NonLocal
