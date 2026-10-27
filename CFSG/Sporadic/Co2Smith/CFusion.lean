module

public import CFSG.Sporadic.Co2Smith.FusionC
public import CFSG.Sporadic.Co2Smith.ClassCount

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

universe u v

section Classes

variable {M : Type*} [Group M]

theorem conjSet_eq_orbit (x : M) : conjSet x = MulAction.orbit (ConjAct M) x := by
  ext y
  simp only [conjSet, Set.mem_ofPred_eq, MulAction.mem_orbit_iff, ConjAct.smul_def]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨ConjAct.toConjAct h, by simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨ConjAct.ofConjAct c, rfl⟩

theorem ncard_conjSet_mul [Finite M] (x : M) :
    (conjSet x).ncard * Nat.card (centralizer ({x} : Set M)) = Nat.card M := by
  rw [conjSet_eq_orbit, ← MulAction.index_stabilizer, nat_card_centralizer_nat_card_stabilizer,
    mul_comm, card_mul_index]
  rfl

theorem conjSet_conj (h x : M) : conjSet (h * x * h⁻¹) = conjSet x := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k * h, by group⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k * h⁻¹, by group⟩

theorem ncard_conjSet_mulEquiv {M' : Type*} [Group M'] (φ : M ≃* M') (x : M) :
    (conjSet (φ x)).ncard = (conjSet x).ncard := by
  have : conjSet (φ x) = φ '' conjSet x := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨φ.symm k * x * (φ.symm k)⁻¹, ⟨φ.symm k, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨φ k, by simp⟩
  rw [this, Set.ncard_image_of_injective _ φ.injective]

end Classes

variable {G : Type u} [Group G] {z : G}

theorem ncard_conjSet_swap [Finite G] {g : G} (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    (conjSet (⟨_, ht⟩ : centralizer ({z} : Set G))).ncard =
      (conjSet (⟨_, conj_mem_centralizer ht⟩ : centralizer ({z} : Set G))).ncard := by
  set H := centralizer ({z} : Set G)
  set t : H := ⟨_, ht⟩
  set s : H := ⟨_, conj_mem_centralizer ht⟩
  have hfw : ∀ x : H, x * t = t * x → g * (x : G) * g⁻¹ ∈ H := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have := congrArg Subtype.val hx
    simp only [Subgroup.coe_mul, t] at this
    calc g * (x : G) * g⁻¹ * z = g * ((x : G) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [this]
      _ = z * (g * x * g⁻¹) := by group
  have hbw : ∀ x : H, x * s = s * x → g⁻¹ * (x : G) * g ∈ H := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have := congrArg Subtype.val hx
    simp only [Subgroup.coe_mul, s] at this
    calc g⁻¹ * (x : G) * g * z = g⁻¹ * ((x : G) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [this]
      _ = z * (g⁻¹ * x * g) := by group
  have hzx : ∀ x : H, (x : G) * z = z * x := fun x => mem_centralizer_singleton_iff.mp x.2
  have hc : Nat.card (centralizer ({t} : Set H)) = Nat.card (centralizer ({s} : Set H)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨_, hfw x.1 (mem_centralizer_singleton_iff.mp x.2)⟩, ?_⟩
        invFun := fun x => ⟨⟨_, hbw x.1 (mem_centralizer_singleton_iff.mp x.2)⟩, ?_⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
        right_inv := fun x => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
    · rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, s]
      calc g * (x.1 : G) * g⁻¹ * (g * z * g⁻¹) = g * ((x.1 : G) * z) * g⁻¹ := by group
        _ = g * (z * x.1) * g⁻¹ := by rw [hzx x.1]
        _ = g * z * g⁻¹ * (g * x.1 * g⁻¹) := by group
    · rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, t]
      calc g⁻¹ * (x.1 : G) * g * (g⁻¹ * z * g) = g⁻¹ * ((x.1 : G) * z) * g := by group
        _ = g⁻¹ * (z * x.1) * g := by rw [hzx x.1]
        _ = g⁻¹ * z * g * (g⁻¹ * x.1 * g) := by group
  have h1 := ncard_conjSet_mul t
  have h2 := ncard_conjSet_mul s
  have hpos : 0 < Nat.card (centralizer ({s} : Set H)) := Nat.card_pos
  rw [hc] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

section Model

variable [Finite G] {M : Type v} [Group M] (φ : centralizer ({z} : Set G) ≃* M) {zM : M}

omit [Finite G] in
theorem mem_center_of_φ (hφz : φ (zC z) = zM) (y : M) : y * zM = zM * y := by
  rw [← hφz, ← MulEquiv.apply_symm_apply φ y, ← map_mul, ← map_mul,
    (mem_center_iff.mp (zC_mem_center z) (φ.symm y)).symm]

include φ in
theorem swap_classes (hφz : φ (zC z) = zM) {k : ℕ} (r : Fin k → M)
    (hinv : ∀ y : M, y * y = 1 → y = 1 ∨ y = zM ∨ ∃ i, ∃ h : M, h * y * h⁻¹ = r i)
    (hz2 : orderOf z = 2) {g : G} (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hte : g⁻¹ * z * g ≠ z) :
    ∃ i j, (∃ h : M, h * φ ⟨_, ht⟩ * h⁻¹ = r i) ∧
      (∃ h : M, h * φ ⟨_, conj_mem_centralizer ht⟩ * h⁻¹ = r j) ∧
      sqrtCnt zM (r i) = sqrtCnt (r j) (r j) ∧ sqrtCnt (r i) (r i) = sqrtCnt zM (r j) ∧
      (conjSet (r i)).ncard = (conjSet (r j)).ncard := by
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  set t : centralizer ({z} : Set G) := ⟨_, ht⟩
  set u : centralizer ({z} : Set G) := ⟨_, conj_mem_centralizer ht⟩
  have htt : t * t = 1 := Subtype.ext (mul_self_conj_z g hzz)
  have huu : u * u = 1 := Subtype.ext (by
    show g * z * g⁻¹ * (g * z * g⁻¹) = 1
    simpa using mul_self_conj_z g⁻¹ hzz)
  have ht1 : t ≠ 1 := fun e => hz1 (by
    have := congrArg Subtype.val e
    simp only [t, OneMemClass.coe_one] at this
    have := congrArg (fun w => g * w * g⁻¹) this
    simpa [mul_assoc] using this)
  have htz : t ≠ zC z := fun e => hte (congrArg Subtype.val e)
  have hu1 : u ≠ 1 := fun e => hz1 (by
    have := congrArg Subtype.val e
    simp only [u, OneMemClass.coe_one] at this
    have := congrArg (fun w => g⁻¹ * w * g) this
    simpa [mul_assoc] using this)
  have huz : u ≠ zC z := fun e => hte (by
    have := congrArg (fun w => g⁻¹ * w * g) (congrArg Subtype.val e)
    simp only [u, zC] at this
    simpa [mul_assoc] using this.symm)
  have hcls : ∀ x : centralizer ({z} : Set G), x * x = 1 → x ≠ 1 → x ≠ zC z →
      ∃ i, ∃ h : M, h * φ x * h⁻¹ = r i := by
    intro x hx hx1 hxz
    rcases hinv (φ x) (by rw [← map_mul, hx, map_one]) with h | h | h
    · exact absurd (φ.injective (h.trans (map_one φ).symm)) hx1
    · exact absurd (φ.injective (h.trans hφz.symm)) hxz
    · exact h
  obtain ⟨i, h, hh⟩ := hcls t htt ht1 htz
  obtain ⟨j, k', hk⟩ := hcls u huu hu1 huz
  obtain ⟨sw1, sw2⟩ := sqrtCnt_swap ht
  have ez : ∀ h : M, h * zM * h⁻¹ = zM := fun h => by
    rw [mem_center_of_φ φ hφz h, mul_inv_cancel_right]
  have hZ : ∀ (h : M) (x : centralizer ({z} : Set G)),
      sqrtCnt zM (h * φ x * h⁻¹) = sqrtCnt (zC z) x := by
    intro h x
    rw [← ez h, sqrtCnt_conj, ← hφz, sqrtCnt_mulEquiv]
  have hR : ∀ (h : M) (x : centralizer ({z} : Set G)),
      sqrtCnt (h * φ x * h⁻¹) (h * φ x * h⁻¹) = sqrtCnt x x := by
    intro h x
    rw [sqrtCnt_conj, sqrtCnt_mulEquiv]
  have hN : ∀ (h : M) (x : centralizer ({z} : Set G)),
      (conjSet (h * φ x * h⁻¹)).ncard = (conjSet x).ncard := by
    intro h x
    rw [conjSet_conj, ncard_conjSet_mulEquiv]
  refine ⟨i, j, ⟨h, hh⟩, ⟨k', hk⟩, ?_, ?_, ?_⟩
  · rw [← hh, ← hk, hZ, hR]
    exact sw1
  · rw [← hh, ← hk, hZ, hR]
    exact sw2
  · rw [← hh, ← hk, hN, hN]
    exact ncard_conjSet_swap ht

include φ in
theorem conj_eq_of_mem_pCore (hφz : φ (zC z) = zM) {k : ℕ} (r : Fin k → M)
    (hinv : ∀ y : M, y * y = 1 → y = 1 ∨ y = zM ∨ ∃ i, ∃ h : M, h * y * h⁻¹ = r i)
    (hz2 : orderOf z = 2) (i₀ : Fin k) (hr : ∀ i, r i ∈ CFSG.pCore 2 M → i = i₀)
    (hrow : ∀ j, sqrtCnt zM (r i₀) = sqrtCnt (r j) (r j) →
      sqrtCnt (r i₀) (r i₀) = sqrtCnt zM (r j) → (conjSet (r i₀)).ncard = (conjSet (r j)).ncard →
        False)
    (g : G) (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hE : (⟨_, ht⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G))) :
    g⁻¹ * z * g = z := by
  by_contra hte
  obtain ⟨i, j, ⟨h, hh⟩, -, e1, e2, e3⟩ := swap_classes φ hφz r hinv hz2 ht hte
  have hmem : r i ∈ CFSG.pCore 2 M := by
    rw [← hh]
    exact (CFSG.pCore_normal (p := 2) (G := M)).conj_mem _ (apply_mem_pCore_two φ hE) h
  have := hr i hmem
  subst this
  exact hrow j e1 e2 e3

include φ in
theorem conj_mem_of_model (hφz : φ (zC z) = zM) {k : ℕ} (r : Fin k → M)
    (hinv : ∀ y : M, y * y = 1 → y = 1 ∨ y = zM ∨ ∃ i, ∃ h : M, h * y * h⁻¹ = r i)
    (hz2 : orderOf z = 2) (A B : Finset (Fin k))
    (hpair : ∀ i j, sqrtCnt zM (r i) = sqrtCnt (r j) (r j) →
      sqrtCnt (r i) (r i) = sqrtCnt zM (r j) → (conjSet (r i)).ncard = (conjSet (r j)).ncard →
        i ∈ A ∨ (i = j ∧ i ∈ B))
    (hnorm : ∀ i ∈ B, ∀ g : G, g⁻¹ * z * g = ((φ.symm (r i) : centralizer ({z} : Set G)) : G) →
      g * z * g⁻¹ = ((φ.symm (r i) : centralizer ({z} : Set G)) : G) → False)
    (g : G) (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    g⁻¹ * z * g = z ∨ ∃ i ∈ A, ∃ h : M, h * φ ⟨_, ht⟩ * h⁻¹ = r i := by
  by_cases hte : g⁻¹ * z * g = z
  · exact Or.inl hte
  obtain ⟨i, j, ⟨h, hh⟩, ⟨k', hk⟩, e1, e2, e3⟩ := swap_classes φ hφz r hinv hz2 ht hte
  rcases hpair i j e1 e2 e3 with hi | ⟨rfl, hi⟩
  · exact Or.inr ⟨i, hi, h, hh⟩
  exfalso
  have lift : ∀ (h : M) (x : centralizer ({z} : Set G)), h * φ x * h⁻¹ = r i →
      ((φ.symm h : centralizer ({z} : Set G)) : G) * x * ((φ.symm h : centralizer ({z} : Set G)) :
        G)⁻¹ = ((φ.symm (r i) : centralizer ({z} : Set G)) : G) := by
    intro h x hx
    rw [← hx, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    simp
  obtain ⟨g', hg1, hg2⟩ := exists_swap_norm _ _ (mem_centralizer_singleton_iff.mp (φ.symm h).2)
    (mem_centralizer_singleton_iff.mp (φ.symm k').2) (lift h _ hh) (lift k' _ hk)
  exact hnorm i hi g' hg1 hg2

end Model

end CFSG.Sporadic.Co2Smith
