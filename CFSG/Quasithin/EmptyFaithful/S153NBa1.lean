module

public import CFSG.Quasithin.Background.S1567Z8
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.S153N

section Klein

variable {U : Type} [CommGroup U]

theorem klein_enum (hU : ∀ u : U, u ^ 2 = 1) {B : Subgroup U} [Finite B] (hB : Nat.card ↥B = 4)
    (ω : MulAut U) (hω3 : ∀ u, ω (ω (ω u)) = u) (hωB : ∀ u ∈ B, ω u ∈ B)
    (hfpf : ∀ u ∈ B, ω u = u → u = 1) {u : U} (hu : u ∈ B) (hu1 : u ≠ 1) :
    ∀ x ∈ B, x = 1 ∨ x = u ∨ x = ω u ∨ x = ω (ω u) := by
  classical
  have _ := hU
  have hωinj : ∀ x y : U, ω x = ω y → x = y := fun x y h => ω.injective h
  have hb1 : ω u ≠ 1 := fun h => hu1 (hωinj _ _ (by rw [h, map_one]))
  have hc1 : ω (ω u) ≠ 1 := fun h => hb1 (hωinj _ _ (by rw [h, map_one]))
  have hba : ω u ≠ u := fun h => hu1 (hfpf u hu h)
  have hca : ω (ω u) ≠ u := fun h => by
    have h2 : ω (ω (ω u)) = ω u := by rw [h]
    rw [hω3] at h2
    exact hba h2.symm
  have hcb : ω (ω u) ≠ ω u := fun h => hb1 (hfpf _ (hωB u hu) h)
  have hbB : ω u ∈ B := hωB u hu
  have hcB : ω (ω u) ∈ B := hωB _ hbB
  have : Fintype B := Fintype.ofFinite B
  have hcard : Fintype.card B = 4 := by rw [← Nat.card_eq_fintype_card]; exact hB
  let x0 : B := ⟨1, B.one_mem⟩
  let x1 : B := ⟨u, hu⟩
  let x2 : B := ⟨ω u, hbB⟩
  let x3 : B := ⟨ω (ω u), hcB⟩
  have h01 : x0 ≠ x1 := fun h => hu1 (congrArg Subtype.val h).symm
  have h02 : x0 ≠ x2 := fun h => hb1 (congrArg Subtype.val h).symm
  have h03 : x0 ≠ x3 := fun h => hc1 (congrArg Subtype.val h).symm
  have h12 : x1 ≠ x2 := fun h => hba (congrArg Subtype.val h).symm
  have h13 : x1 ≠ x3 := fun h => hca (congrArg Subtype.val h).symm
  have h23 : x2 ≠ x3 := fun h => hcb (congrArg Subtype.val h).symm
  have hS : ({x0, x1, x2, x3} : Finset B) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard]
    rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
      Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  intro x hx
  have hmem : (⟨x, hx⟩ : B) ∈ ({x0, x1, x2, x3} : Finset B) := by
    rw [hS]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem klein_prod_eq_one (hU : ∀ u : U, u ^ 2 = 1) {B : Subgroup U} [Finite B] (hB : Nat.card ↥B = 4)
    (ω : MulAut U) (hω3 : ∀ u, ω (ω (ω u)) = u) (hωB : ∀ u ∈ B, ω u ∈ B)
    (hfpf : ∀ u ∈ B, ω u = u → u = 1) {u : U} (hu : u ∈ B) : u * ω u * ω (ω u) = 1 := by
  by_cases hu1 : u = 1
  · subst hu1
    simp
  have hsq : ∀ x : U, x * x = 1 := fun x => by
    have := hU x
    rwa [pow_two] at this
  have hb1 : ω u ≠ 1 := fun h => hu1 (ω.injective (by rw [h, map_one]))
  have hba : ω u ≠ u := fun h => hu1 (hfpf u hu h)
  have hbB : ω u ∈ B := hωB u hu
  have hab : u * ω u ∈ B := B.mul_mem hu hbB
  have hab1 : u * ω u ≠ 1 := fun h => hba (by
    have : ω u = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact inv_eq_of_mul_eq_one_right (hsq u))
  have habu : u * ω u ≠ u := fun h => hb1 (by simpa using h)
  have habb : u * ω u ≠ ω u := fun h => hu1 (by simpa using h)
  have habc : u * ω u = ω (ω u) := by
    rcases klein_enum hU hB ω hω3 hωB hfpf hu hu1 _ hab with h | h | h | h
    · exact absurd h hab1
    · exact absurd h habu
    · exact absurd h habb
    · exact h
  rw [habc]
  exact hsq _

theorem klein_form (hU : ∀ u : U, u ^ 2 = 1) {B : Subgroup U} [Finite B] (hB : Nat.card ↥B = 4)
    (ω : MulAut U) (hω3 : ∀ u, ω (ω (ω u)) = u) (hωB : ∀ u ∈ B, ω u ∈ B)
    (hfpf : ∀ u ∈ B, ω u = u → u = 1) {u : U} (hu : u ∈ B) : u = ω u * ω (ω u) := by
  have h1 := klein_prod_eq_one hU hB ω hω3 hωB hfpf hu
  have hsq : ∀ x : U, x * x = 1 := fun x => by
    have := hU x
    rwa [pow_two] at this
  calc u = u * (u * ω u * ω (ω u)) := by rw [h1, mul_one]
    _ = (u * u) * (ω u * ω (ω u)) := by group
    _ = ω u * ω (ω u) := by rw [hsq, one_mul]

theorem exists_sigma_fixed (hU : ∀ u : U, u ^ 2 = 1) {B : Subgroup U} [Finite B] (hB : Nat.card ↥B = 4)
    (ω σ : MulAut U) (hω3 : ∀ u, ω (ω (ω u)) = u) (hωB : ∀ u ∈ B, ω u ∈ B)
    (hfpf : ∀ u ∈ B, ω u = u → u = 1) (hσB : ∀ u ∈ B, σ u ∈ B) (hσ2 : ∀ x, σ (σ x) = x) :
    ∃ w ∈ B, w ≠ 1 ∧ σ w = w := by
  have hB1 : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hB
    omega
  obtain ⟨⟨u, hu'⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have henum := klein_enum hU hB ω hω3 hωB hfpf hu' hu1'
  have hωinj : ∀ x y : U, ω x = ω y → x = y := fun x y h => ω.injective h
  have hσinj : ∀ x y : U, σ x = σ y → x = y := fun x y h => by
    have := congrArg σ h
    rwa [hσ2, hσ2] at this
  have hb1 : ω u ≠ 1 := fun h => hu1' (hωinj _ _ (by rw [h, map_one]))
  have hc1 : ω (ω u) ≠ 1 := fun h => hb1 (hωinj _ _ (by rw [h, map_one]))
  have hba : ω u ≠ u := fun h => hu1' (hfpf u hu' h)
  have hca : ω (ω u) ≠ u := fun h => by
    have h2 : ω (ω (ω u)) = ω u := by rw [h]
    rw [hω3] at h2
    exact hba h2.symm
  have hcb : ω (ω u) ≠ ω u := fun h => hb1 (hfpf _ (hωB u hu') h)
  have hbB : ω u ∈ B := hωB u hu'
  have hcB : ω (ω u) ∈ B := hωB _ hbB
  have hs1 : ∀ x : U, x ≠ 1 → σ x ≠ 1 := fun x hx h => hx (hσinj _ _ (by rw [h, map_one]))
  rcases henum (σ u) (hσB u hu') with h | h | h | h
  · exact absurd h (hs1 u hu1')
  · exact ⟨u, hu', hu1', h⟩
  ·
    have hσb : σ (ω u) = u := by rw [← h, hσ2]
    refine ⟨ω (ω u), hcB, hc1, ?_⟩
    rcases henum (σ (ω (ω u))) (hσB _ hcB) with h' | h' | h' | h'
    · exact absurd h' (hs1 _ hc1)
    · have e : σ (σ (ω (ω u))) = ω (ω u) := hσ2 _
      rw [h', h] at e
      exact absurd e.symm hcb
    · have e : σ (σ (ω (ω u))) = ω (ω u) := hσ2 _
      rw [h', hσb] at e
      exact absurd e.symm hca
    · exact h'
  ·
    have hσc : σ (ω (ω u)) = u := by rw [← h, hσ2]
    refine ⟨ω u, hbB, hb1, ?_⟩
    rcases henum (σ (ω u)) (hσB _ hbB) with h' | h' | h' | h'
    · exact absurd h' (hs1 _ hb1)
    · have e : σ (σ (ω u)) = ω u := hσ2 _
      rw [h', h] at e
      exact absurd e hcb
    · exact h'
    · have e : σ (σ (ω u)) = ω u := hσ2 _
      rw [h', hσc] at e
      exact absurd e.symm hba

theorem sigma_fixed_eq {B : Subgroup U} [Finite B] (hB : Nat.card ↥B = 4) (hU : ∀ u : U, u ^ 2 = 1)
    (ω σ : MulAut U) (hω3 : ∀ u, ω (ω (ω u)) = u) (hωB : ∀ u ∈ B, ω u ∈ B)
    (hfpf : ∀ u ∈ B, ω u = u → u = 1) (hσωB : ∀ u ∈ B, σ (ω u) = ω (ω (σ u))) {w : U} (hw : w ∈ B)
    (hw1 : w ≠ 1) (hσw : σ w = w) : ∀ x ∈ B, σ x = x → x = 1 ∨ x = w := by
  have henum := klein_enum hU hB ω hω3 hωB hfpf hw hw1
  have hωinj : ∀ x y : U, ω x = ω y → x = y := fun x y h => ω.injective h
  have hba : ω w ≠ w := fun h => hw1 (hfpf w hw h)
  have hbB : ω w ∈ B := hωB w hw
  intro x hx hσx
  rcases henum x hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  ·
    exfalso
    have h1 : σ (ω w) = ω (ω w) := by rw [hσωB w hw, hσw]
    rw [h] at hσx
    rw [h1] at hσx
    exact hba (hωinj _ _ hσx)
  ·
    exfalso
    have h1 : σ (ω w) = ω (ω w) := by rw [hσωB w hw, hσw]
    have h2 : σ (ω (ω w)) = ω w := by
      rw [hσωB (ω w) hbB, h1]
      have : ω (ω (ω (ω w))) = ω w := by rw [hω3]
      exact this
    rw [h, h2] at hσx
    exact hba (hωinj _ _ hσx).symm

end Klein

section Gen

variable {U : Type} [CommGroup U] {Cg : Type} [Group Cg]

theorem norm_eq_one_of_gen (hU : ∀ u : U, u ^ 2 = 1) {B : Subgroup U} [Finite B] (hB : Nat.card ↥B = 4)
    (ω : MulAut U) (hω3 : ∀ u, ω (ω (ω u)) = u) (hωB : ∀ u ∈ B, ω u ∈ B)
    (hfpf : ∀ u ∈ B, ω u = u → u = 1) (ρ : Cg →* MulAut U)
    (hρω : ∀ (c : Cg) (u : U), ρ c (ω u) = ω (ρ c u))
    (hgen : Subgroup.closure {u : U | ∃ (c : Cg) (v : U), v ∈ B ∧ u = ρ c v} = ⊤) (u : U) :
    u * ω u * ω (ω u) = 1 := by
  have := S1567.normW_eq_one_of_generated hU ω hω3 {u : U | ∃ (c : Cg) (v : U), v ∈ B ∧ u = ρ c v}
    (fun u hu => by
      obtain ⟨c, v, hv, rfl⟩ := hu
      have hv' := klein_form hU hB ω hω3 hωB hfpf hv
      refine ⟨ρ c (ω v), 1, ?_⟩
      calc ρ c v = ρ c (ω v * ω (ω v)) := by rw [← hv']
        _ = ρ c (ω v) * ρ c (ω (ω v)) := map_mul _ _ _
        _ = ρ c (ω v) * (ω ^ 1) (ρ c (ω v)) := by rw [pow_one, hρω c (ω v)])
    hgen u
  simpa [S1567.normW_apply] using this

theorem sigma_omega_of_gen {B : Subgroup U} (ω σ : MulAut U) (ρ : Cg →* MulAut U)
    (hρω : ∀ (c : Cg) (u : U), ρ c (ω u) = ω (ρ c u))
    (hρσ : ∀ (c : Cg) (u : U), ρ c (σ u) = σ (ρ c u))
    (hσB : ∀ u ∈ B, σ (ω u) = ω (ω (σ u)))
    (hgen : Subgroup.closure {u : U | ∃ (c : Cg) (v : U), v ∈ B ∧ u = ρ c v} = ⊤) (u : U) :
    σ (ω u) = ω (ω (σ u)) := by
  let f : U →* U := (σ : U ≃* U).toMonoidHom.comp (ω : U ≃* U).toMonoidHom
  let g : U →* U := (ω : U ≃* U).toMonoidHom.comp ((ω : U ≃* U).toMonoidHom.comp (σ : U ≃* U).toMonoidHom)
  have hfg : Set.EqOn f g (Subgroup.closure {u : U | ∃ (c : Cg) (v : U), v ∈ B ∧ u = ρ c v}) := by
    refine MonoidHom.eqOn_closure (f := f) (g := g) ?_
    rintro _ ⟨c, v, hv, rfl⟩
    show σ (ω (ρ c v)) = ω (ω (σ (ρ c v)))
    calc σ (ω (ρ c v)) = σ (ρ c (ω v)) := by rw [hρω]
      _ = ρ c (σ (ω v)) := (hρσ c _).symm
      _ = ρ c (ω (ω (σ v))) := by rw [hσB v hv]
      _ = ω (ω (ρ c (σ v))) := by rw [hρω, hρω]
      _ = ω (ω (σ (ρ c v))) := by rw [hρσ]
  have hu : u ∈ Subgroup.closure {u : U | ∃ (c : Cg) (v : U), v ∈ B ∧ u = ρ c v} := by
    rw [hgen]; trivial
  exact hfg hu

end Gen

end CFSG.Quasithin.S153N
