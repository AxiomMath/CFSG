module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D]

theorem index_two_decomp [Finite D] {A B : Subgroup D} (hAB : A.relIndex B = 2) {b : D}
    (hbB : b ∈ B) (hbA : b ∉ A) {x : D} (hx : x ∈ B) : x ∈ A ∨ ∃ a ∈ A, x = b * a := by
  classical
  let b' : ↥B := ⟨b, hbB⟩
  let x' : ↥B := ⟨x, hx⟩
  let A' : Subgroup ↥B := A.subgroupOf B
  have hcard : Nat.card (↥B ⧸ A') = 2 := hAB
  let _inst : Fintype (↥B ⧸ A') := Fintype.ofFinite _
  have hcard' : Fintype.card (↥B ⧸ A') = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  let a₀ : ↥B ⧸ A' := ((1 : ↥B) : ↥B ⧸ A')
  let a₁ : ↥B ⧸ A' := ((b' : ↥B) : ↥B ⧸ A')
  have h01 : a₀ ≠ a₁ := by
    intro h
    have := QuotientGroup.eq.mp h
    exact hbA (by simpa [A', Subgroup.mem_subgroupOf, b'] using this)
  have hmem : (x' : ↥B ⧸ A') = a₀ ∨ (x' : ↥B ⧸ A') = a₁ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c0, c1⟩ := hcon
    have hsub : ({a₀, a₁, (x' : ↥B ⧸ A')} : Finset (↥B ⧸ A')).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair c1.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, c0.symm⟩
    have := Finset.card_le_univ ({a₀, a₁, (x' : ↥B ⧸ A')} : Finset (↥B ⧸ A'))
    omega
  rcases hmem with h | h
  · left
    have := QuotientGroup.eq.mp h.symm
    simpa [A', Subgroup.mem_subgroupOf, x'] using this
  · right
    have := QuotientGroup.eq.mp h.symm
    have h2 : b⁻¹ * x ∈ A := by simpa [A', Subgroup.mem_subgroupOf, x', b'] using this
    exact ⟨b⁻¹ * x, h2, by group⟩

@[expose] def sqCommSub (X : Subgroup D) : Subgroup D :=
  Subgroup.closure {w | ∃ x ∈ X, ∃ y ∈ X, w = x * x ∨ w = x * y * x⁻¹ * y⁻¹}

theorem mul_self_mem_sqCommSub {X : Subgroup D} {x : D} (hx : x ∈ X) : x * x ∈ sqCommSub X :=
  Subgroup.subset_closure ⟨x, hx, x, hx, Or.inl rfl⟩

theorem comm_mem_sqCommSub {X : Subgroup D} {x y : D} (hx : x ∈ X) (hy : y ∈ X) :
    x * y * x⁻¹ * y⁻¹ ∈ sqCommSub X :=
  Subgroup.subset_closure ⟨x, hx, y, hy, Or.inr rfl⟩

theorem sqCommSub_le_self (X : Subgroup D) : sqCommSub X ≤ X := by
  unfold sqCommSub
  rw [Subgroup.closure_le]
  rintro w ⟨x, hx, y, hy, rfl | rfl⟩
  · exact X.mul_mem hx hx
  · exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)

theorem sqCommSub_mono {X Y : Subgroup D} (h : X ≤ Y) : sqCommSub X ≤ sqCommSub Y := by
  unfold sqCommSub
  rw [Subgroup.closure_le]
  rintro w ⟨x, hx, y, hy, rfl | rfl⟩
  · exact mul_self_mem_sqCommSub (h hx)
  · exact comm_mem_sqCommSub (h hx) (h hy)

theorem conj_mem_sqCommSub {X : Subgroup D} {g y : D} (hg : g ∈ Subgroup.normalizer (X : Set D))
    (hy : y ∈ sqCommSub X) : g * y * g⁻¹ ∈ sqCommSub X := by
  have hX : ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  induction hy using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, rfl | rfl⟩ := hw
    · have : g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
      rw [this]; exact mul_self_mem_sqCommSub (hX x hx)
    · have : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      rw [this]; exact comm_mem_sqCommSub (hX x hx) (hX y hy)
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact (sqCommSub X).mul_mem iha ihb
  | inv a _ ih =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact (sqCommSub X).inv_mem ih

theorem le_normalizer_sqCommSub {X : Subgroup D} {g : D}
    (hg : g ∈ Subgroup.normalizer (X : Set D)) :
    g ∈ Subgroup.normalizer (sqCommSub X : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_sqCommSub hg, fun hy => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (X : Set D) := inv_mem hg
  have := conj_mem_sqCommSub hg' hy
  simpa [mul_assoc] using this

theorem elemAbelian_of_sqCommSub_eq_bot {X : Subgroup D} (h : sqCommSub X = ⊥) :
    (∀ x ∈ X, x * x = 1) ∧ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := mul_self_mem_sqCommSub hx
    rwa [h, Subgroup.mem_bot] at this
  · have := comm_mem_sqCommSub hx hy
    rw [h, Subgroup.mem_bot] at this
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [this, one_mul]

section Coset

variable {Q R : Subgroup D} {v : D}

theorem vmul_comm_cancel (hv : ∀ q ∈ Q, v * q = q * v) (hv2 : v * v = 1) {r y : D}
    (hr : r ∈ Q) (hy : y ∈ Q) : (v * r) * y * (v * r)⁻¹ * y⁻¹ = r * y * r⁻¹ * y⁻¹ := by
  have h1 : v * (r * y * r⁻¹) = (r * y * r⁻¹) * v :=
    hv _ (Q.mul_mem (Q.mul_mem hr hy) (Q.inv_mem hr))
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  calc (v * r) * y * (v * r)⁻¹ * y⁻¹ = v * (r * y * r⁻¹) * v⁻¹ * y⁻¹ := by group
    _ = (r * y * r⁻¹) * v * v⁻¹ * y⁻¹ := by rw [h1]
    _ = r * y * r⁻¹ * y⁻¹ := by group

theorem vmul_sq (hv : ∀ q ∈ Q, v * q = q * v) (hv2 : v * v = 1) {r : D} (hr : r ∈ Q) :
    (v * r) * (v * r) = r * r := by
  have h1 : v * r = r * v := hv r hr
  calc (v * r) * (v * r) = v * (r * v) * r := by group
    _ = v * (v * r) * r := by rw [h1]
    _ = (v * v) * (r * r) := by group
    _ = r * r := by rw [hv2, one_mul]

theorem sqCommSub_eq_of_coset (hRQ : R ≤ Q) (hv : ∀ q ∈ Q, v * q = q * v) (hv2 : v * v = 1)
    (hcos : ∀ q ∈ Q, q ∈ R ∨ ∃ r ∈ R, q = v * r) : sqCommSub Q = sqCommSub R := by
  refine le_antisymm ?_ (sqCommSub_mono hRQ)
  unfold sqCommSub
  rw [Subgroup.closure_le]
  rintro w ⟨x, hx, y, hy, rfl | rfl⟩
  · rcases hcos x hx with h | ⟨r, hr, rfl⟩
    · exact mul_self_mem_sqCommSub h
    · rw [vmul_sq hv hv2 (hRQ hr)]; exact mul_self_mem_sqCommSub hr
  ·
    have hinv : ∀ a b : D, a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := fun a b => by group
    have hxv : ∀ r ∈ R, ∀ y ∈ Q, (v * r) * y * (v * r)⁻¹ * y⁻¹ ∈ sqCommSub R := by
      intro r hr y hy
      rw [vmul_comm_cancel hv hv2 (hRQ hr) hy]
      rcases hcos y hy with h | ⟨r', hr', rfl⟩
      · exact comm_mem_sqCommSub hr h
      · rw [hinv, vmul_comm_cancel hv hv2 (hRQ hr') (hRQ hr), ← hinv]
        exact comm_mem_sqCommSub hr hr'
    rcases hcos x hx with h | ⟨r, hr, rfl⟩
    · rcases hcos y hy with h' | ⟨r', hr', rfl⟩
      · exact comm_mem_sqCommSub h h'
      · rw [hinv, vmul_comm_cancel hv hv2 (hRQ hr') (hRQ h), ← hinv]
        exact comm_mem_sqCommSub h hr'
    · exact hxv r hr y hy

theorem elemAbelian_of_coset (hRQ : R ≤ Q) (hv : ∀ q ∈ Q, v * q = q * v)
    (hv2 : v * v = 1) (hcos : ∀ q ∈ Q, q ∈ R ∨ ∃ r ∈ R, q = v * r)
    (hR1 : ∀ x ∈ R, x * x = 1) (hR2 : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) :
    (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) ∧ ∀ a ∈ Q, a * a = 1 := by
  have hcomm_v : ∀ r ∈ R, ∀ r' ∈ R, (v * r) * r' = r' * (v * r) := by
    intro r hr r' hr'
    calc (v * r) * r' = v * (r * r') := mul_assoc _ _ _
      _ = v * (r' * r) := by rw [hR2 r hr r' hr']
      _ = (v * r') * r := (mul_assoc _ _ _).symm
      _ = (r' * v) * r := by rw [hv r' (hRQ hr')]
      _ = r' * (v * r) := mul_assoc _ _ _
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rcases hcos a ha with h | ⟨r, hr, rfl⟩ <;> rcases hcos b hb with h' | ⟨r', hr', rfl⟩
    · exact hR2 a h b h'
    · calc a * (v * r') = (a * v) * r' := (mul_assoc _ _ _).symm
        _ = (v * a) * r' := by rw [hv a ha]
        _ = v * (a * r') := mul_assoc _ _ _
        _ = v * (r' * a) := by rw [hR2 a h r' hr']
        _ = (v * r') * a := (mul_assoc _ _ _).symm
    · exact hcomm_v r hr b h'
    · calc (v * r) * (v * r') = (v * v) * (r * r') := by
            calc (v * r) * (v * r') = v * (r * v) * r' := by group
              _ = v * (v * r) * r' := by rw [hv r (hRQ hr)]
              _ = (v * v) * (r * r') := by group
        _ = r * r' := by rw [hv2, one_mul]
        _ = r' * r := hR2 r hr r' hr'
        _ = (v * v) * (r' * r) := by rw [hv2, one_mul]
        _ = (v * r') * (v * r) := by
            calc (v * v) * (r' * r) = v * (v * r') * r := by group
              _ = v * (r' * v) * r := by rw [hv r' (hRQ hr')]
              _ = (v * r') * (v * r) := by group
  · rcases hcos a ha with h | ⟨r, hr, rfl⟩
    · exact hR1 a h
    · rw [vmul_sq hv hv2 (hRQ hr)]; exact hR1 r hr

end Coset

end GoldAmL

end F6

end CFSG.Quasithin
