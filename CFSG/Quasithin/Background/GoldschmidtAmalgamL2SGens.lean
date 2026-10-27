module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SHyp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Gen (A B : Subgroup D) (z : D) (V : Subgroup D) (x a a₁ a₂ : D) : Prop where
  hyp : Hyp2 A B z V
  x_mem : x ∈ B
  x_not : x ∉ A ⊓ B
  x2_not : x * x ∉ A ⊓ B
  x_cube : x * x * x = 1
  a_mem : a ∈ V
  a_ne_one : a ≠ 1
  a_ne_z : a ≠ z
  V_set : (V : Set D) = {1, z, a, z * a}
  a₁_eq : a₁ = x * a * x⁻¹
  a₂_eq : a₂ = x * x * a * (x * x)⁻¹

theorem Hyp2.exists_gen [Finite D] (h : Hyp2 A B z V) :
    ∃ x a a₁ a₂, Gen A B z V x a a₁ a₂ := by
  obtain ⟨x, hxB, hx3⟩ := h.gold.vertex_right.exists_order_three
  obtain ⟨a, ha1, haz, hVset⟩ := h.natural.basis
  have hcube : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx3] at this
    simpa [pow_succ, mul_assoc] using this
  refine ⟨x, a, x * a * x⁻¹, x * x * a * (x * x)⁻¹,
    ⟨h, hxB, h.gold.vertex_right.not_mem_of_orderOf hx3,
    h.gold.vertex_right.sq_not_mem_of_orderOf hx3, hcube, ?_, ha1, haz, hVset, rfl, rfl⟩⟩
  have : a ∈ (V : Set D) := by rw [hVset]; simp
  exact this

namespace Gen

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

omit g in
theorem mem_V_iff (g : Gen A B z V x a a₁ a₂) {v : D} :
    v ∈ V ↔ v = 1 ∨ v = z ∨ v = a ∨ v = z * a := by
  have := Set.ext_iff.mp g.V_set v
  simpa using this

theorem conj_a₁ : x * a₁ * x⁻¹ = a₂ := by
  rw [g.a₁_eq, g.a₂_eq]; group

theorem conj_a₂ : x * a₂ * x⁻¹ = a := by
  rw [g.a₂_eq]
  calc x * (x * x * a * (x * x)⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
    _ = a := by rw [g.x_cube]; group

end Gen

section Facts

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.x2_mem : x * x ∈ B := B.mul_mem g.x_mem g.x_mem

theorem Gen.a_sq : a * a = 1 := g.hyp.V_sq g.a_mem

theorem Gen.a₁_sq : a₁ * a₁ = 1 := by
  rw [g.a₁_eq]
  calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
    _ = 1 := by rw [g.a_sq]; group

theorem Gen.a₂_sq : a₂ * a₂ = 1 := by
  rw [g.a₂_eq]
  calc x * x * a * (x * x)⁻¹ * (x * x * a * (x * x)⁻¹) = (x * x) * (a * a) * (x * x)⁻¹ := by
        group
    _ = 1 := by rw [g.a_sq]; group

theorem Gen.a_mem_U : a ∈ conjClosure V B := le_conjClosure V B g.a_mem

theorem Gen.a₁_mem_U : a₁ ∈ conjClosure V B := by
  rw [g.a₁_eq]; exact mem_conjClosure g.x_mem g.a_mem

theorem Gen.a₂_mem_U : a₂ ∈ conjClosure V B := by
  rw [g.a₂_eq]; exact mem_conjClosure g.x2_mem g.a_mem

theorem Gen.z_comm_a : z * a = a * z :=
  g.hyp.natural.comm_of_mem g.hyp.natural.z_mem_V g.a_mem

theorem Gen.z_conj : x * z * x⁻¹ = z := g.hyp.central x g.x_mem

theorem Gen.z_comm_a₁ : z * a₁ = a₁ * z := by
  have hz := g.z_conj
  calc z * a₁ = (x * z * x⁻¹) * (x * a * x⁻¹) := by rw [hz, g.a₁_eq]
    _ = x * (z * a) * x⁻¹ := by group
    _ = x * (a * z) * x⁻¹ := by rw [g.z_comm_a]
    _ = (x * a * x⁻¹) * (x * z * x⁻¹) := by group
    _ = a₁ * z := by rw [hz, g.a₁_eq]

theorem Gen.z_comm_a₂ : z * a₂ = a₂ * z := by
  have hz : x * x * z * (x * x)⁻¹ = z := g.hyp.central (x * x) g.x2_mem
  calc z * a₂ = (x * x * z * (x * x)⁻¹) * (x * x * a * (x * x)⁻¹) := by rw [hz, g.a₂_eq]
    _ = x * x * (z * a) * (x * x)⁻¹ := by group
    _ = x * x * (a * z) * (x * x)⁻¹ := by rw [g.z_comm_a]
    _ = (x * x * a * (x * x)⁻¹) * (x * x * z * (x * x)⁻¹) := by group
    _ = a₂ * z := by rw [hz, g.a₂_eq]

end Facts

theorem closure_comm {s : Set D} (hs : ∀ p ∈ s, ∀ q ∈ s, p * q = q * p) {u w : D}
    (hu : u ∈ Subgroup.closure s) (hw : w ∈ Subgroup.closure s) : u * w = w * u := by
  have h1 : ∀ p ∈ s, ∀ w ∈ Subgroup.closure s, p * w = w * p := by
    intro p hp w hw
    have hle : Subgroup.closure s ≤ Subgroup.centralizer ({p} : Set D) := by
      rw [Subgroup.closure_le]
      intro q hq
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hs y hp q hq
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) p rfl)
  have hle : Subgroup.closure s ≤ Subgroup.centralizer ({u} : Set D) := by
    rw [Subgroup.closure_le]
    intro q hq
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (h1 q hq y hu).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hw) u rfl)

section Gens

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.V_le_closure : V ≤ Subgroup.closure ({a, z, a₁, a₂} : Set D) := by
  intro v hv
  rcases (g.mem_V_iff).mp hv with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem Gen.x_conj_V {w : D} (hw : w ∈ V) :
    x * w * x⁻¹ ∈ Subgroup.closure ({a, z, a₁, a₂} : Set D) := by
  have hz : x * z * x⁻¹ = z := g.z_conj
  have ha : x * a * x⁻¹ = a₁ := g.a₁_eq.symm
  rcases (g.mem_V_iff).mp hw with rfl | rfl | rfl | rfl
  · simp
  · rw [hz]; exact Subgroup.subset_closure (by simp)
  · rw [ha]; exact Subgroup.subset_closure (by simp)
  · have e : x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
    rw [e, hz, ha]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem Gen.xx_conj_V {w : D} (hw : w ∈ V) :
    x * x * w * (x * x)⁻¹ ∈ Subgroup.closure ({a, z, a₁, a₂} : Set D) := by
  have hz : x * x * z * (x * x)⁻¹ = z := g.hyp.central (x * x) g.x2_mem
  have ha : x * x * a * (x * x)⁻¹ = a₂ := g.a₂_eq.symm
  rcases (g.mem_V_iff).mp hw with rfl | rfl | rfl | rfl
  · simp
  · rw [hz]; exact Subgroup.subset_closure (by simp)
  · rw [ha]; exact Subgroup.subset_closure (by simp)
  · have e : x * x * (z * a) * (x * x)⁻¹ =
        (x * x * z * (x * x)⁻¹) * (x * x * a * (x * x)⁻¹) := by group
    rw [e, hz, ha]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

variable [Finite D] in
theorem Gen.U_le_closure : conjClosure V B ≤ Subgroup.closure ({a, z, a₁, a₂} : Set D) := by
  refine conjClosure_le fun k hk v hv => ?_
  rcases coset_decomp g.hyp.gold.relIndex_right g.x_mem g.x_not g.x2_not hk with
    hkT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · have : k * v * k⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (g.hyp.natural.reduced.2.1 hkT.1) v).mp hv
    exact g.V_le_closure this
  · have htv : t * v * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (g.hyp.natural.reduced.2.1 htT.1) v).mp hv
    have e : x * t * v * (x * t)⁻¹ = x * (t * v * t⁻¹) * x⁻¹ := by group
    rw [e]; exact g.x_conj_V htv
  · have htv : t * v * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (g.hyp.natural.reduced.2.1 htT.1) v).mp hv
    have e : x * x * t * v * (x * x * t)⁻¹ = x * x * (t * v * t⁻¹) * (x * x)⁻¹ := by group
    rw [e]; exact g.xx_conj_V htv

theorem Gen.closure_le_U : Subgroup.closure ({a, z, a₁, a₂} : Set D) ≤ conjClosure V B := by
  rw [Subgroup.closure_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact g.a_mem_U
  · exact g.hyp.z_mem_U
  · exact g.a₁_mem_U
  · exact g.a₂_mem_U

variable [Finite D] in
theorem Gen.U_eq_closure :
    conjClosure V B = Subgroup.closure ({a, z, a₁, a₂} : Set D) :=
  le_antisymm g.U_le_closure g.closure_le_U

end Gens

section Rel

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.comm01_mem : a * a₁ * a⁻¹ * a₁⁻¹ ∈ Subgroup.zpowers z :=
  g.hyp.comm_UU g.a_mem_U g.a₁_mem_U

theorem Gen.conj_comm01 : x * (a * a₁ * a⁻¹ * a₁⁻¹) * x⁻¹ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by
  have e1 : x * a * x⁻¹ = a₁ := g.a₁_eq.symm
  have e2 : x * a₁ * x⁻¹ = a₂ := g.conj_a₁
  calc x * (a * a₁ * a⁻¹ * a₁⁻¹) * x⁻¹
      = (x * a * x⁻¹) * (x * a₁ * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * a₁ * x⁻¹)⁻¹ := by group
    _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by rw [e1, e2]

theorem Gen.conj_comm12 : x * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * x⁻¹ = a₂ * a * a₂⁻¹ * a⁻¹ := by
  have e1 : x * a₁ * x⁻¹ = a₂ := g.conj_a₁
  have e2 : x * a₂ * x⁻¹ = a := g.conj_a₂
  calc x * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * x⁻¹
      = (x * a₁ * x⁻¹) * (x * a₂ * x⁻¹) * (x * a₁ * x⁻¹)⁻¹ * (x * a₂ * x⁻¹)⁻¹ := by group
    _ = a₂ * a * a₂⁻¹ * a⁻¹ := by rw [e1, e2]

variable [Finite D] in
theorem Gen.comm01_ne_one : a * a₁ * a⁻¹ * a₁⁻¹ ≠ 1 := by
  intro h1
  have h12 : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 := by rw [← g.conj_comm01, h1]; group
  have h20 : a₂ * a * a₂⁻¹ * a⁻¹ = 1 := by rw [← g.conj_comm12, h12]; group
  have c01 : a * a₁ = a₁ * a := by
    calc a * a₁ = (a * a₁ * a⁻¹ * a₁⁻¹) * (a₁ * a) := by group
      _ = a₁ * a := by rw [h1, one_mul]
  have c12 : a₁ * a₂ = a₂ * a₁ := by
    calc a₁ * a₂ = (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (a₂ * a₁) := by group
      _ = a₂ * a₁ := by rw [h12, one_mul]
  have c20 : a₂ * a = a * a₂ := by
    calc a₂ * a = (a₂ * a * a₂⁻¹ * a⁻¹) * (a * a₂) := by group
      _ = a * a₂ := by rw [h20, one_mul]
  have cza := g.z_comm_a
  have cza₁ := g.z_comm_a₁
  have cza₂ := g.z_comm_a₂
  have hcomm : ∀ p ∈ ({a, z, a₁, a₂} : Set D), ∀ q ∈ ({a, z, a₁, a₂} : Set D),
      p * q = q * p := by
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first | rfl | assumption | (symm; assumption)
  have hbot : ⁅conjClosure V B, conjClosure V B⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro u hu w hw
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := closure_comm hcomm (g.U_le_closure hu) (g.U_le_closure hw)
    rw [this]; group
  have hz : z ∈ ⁅conjClosure V B, conjClosure V B⁆ := by
    rw [g.hyp.comm_U]; exact Subgroup.mem_zpowers z
  exact g.hyp.natural.z_ne (Subgroup.mem_bot.mp (hbot hz))

variable [Finite D] in
theorem Gen.comm01_eq : a * a₁ * a⁻¹ * a₁⁻¹ = z :=
  (g.hyp.mem_zpowers g.comm01_mem).resolve_left g.comm01_ne_one

variable [Finite D] in
theorem Gen.comm12_eq : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = z := by
  rw [← g.conj_comm01, g.comm01_eq]; exact g.z_conj

variable [Finite D] in
theorem Gen.comm20_eq : a₂ * a * a₂⁻¹ * a⁻¹ = z := by
  rw [← g.conj_comm12, g.comm12_eq]; exact g.z_conj

variable [Finite D] in
theorem Gen.r01 : a * a₁ = z * (a₁ * a) := by
  calc a * a₁ = (a * a₁ * a⁻¹ * a₁⁻¹) * (a₁ * a) := by group
    _ = z * (a₁ * a) := by rw [g.comm01_eq]

variable [Finite D] in
theorem Gen.r12 : a₁ * a₂ = z * (a₂ * a₁) := by
  calc a₁ * a₂ = (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (a₂ * a₁) := by group
    _ = z * (a₂ * a₁) := by rw [g.comm12_eq]

variable [Finite D] in
theorem Gen.r20 : a₂ * a = z * (a * a₂) := by
  calc a₂ * a = (a₂ * a * a₂⁻¹ * a⁻¹) * (a * a₂) := by group
    _ = z * (a * a₂) := by rw [g.comm20_eq]

end Rel

theorem U_le_normalizer (h : Hyp2 A B z V) {N : Subgroup D} (hZN : Subgroup.zpowers z ≤ N)
    (hNU : N ≤ conjClosure V B) : conjClosure V B ≤ Subgroup.normalizer (N : Set D) := by
  have key : ∀ u ∈ conjClosure V B, ∀ n ∈ N, u * n * u⁻¹ ∈ N := by
    intro u hu n hn
    have hc : u * n * u⁻¹ * n⁻¹ ∈ N := hZN (h.comm_UU hu (hNU hn))
    have e : u * n * u⁻¹ = (u * n * u⁻¹ * n⁻¹) * n := by group
    rw [e]; exact N.mul_mem hc hn
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => key u hu n hn, fun hn => ?_⟩
  have := key u⁻¹ ((conjClosure V B).inv_mem hu) _ hn
  simpa [mul_assoc] using this

theorem card_zpowers_le_two' {w : D} (hw : w * w = 1) : Nat.card (Subgroup.zpowers w) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw))

section Card

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.card_le_sixteen : Nat.card (conjClosure V B) ≤ 16 := by
  have hzV : Subgroup.zpowers z ≤ V := Subgroup.zpowers_le.mpr g.hyp.natural.z_mem_V
  have hVU : V ≤ conjClosure V B := le_conjClosure V B
  have hP_U : Subgroup.zpowers a₁ ⊔ V ≤ conjClosure V B :=
    sup_le (Subgroup.zpowers_le.mpr g.a₁_mem_U) hVU
  have hzP : Subgroup.zpowers z ≤ Subgroup.zpowers a₁ ⊔ V := hzV.trans le_sup_right
  have h1 : Subgroup.zpowers a₁ ≤ Subgroup.normalizer (V : Set D) :=
    Subgroup.zpowers_le.mpr (U_le_normalizer g.hyp hzV hVU g.a₁_mem_U)
  have h2 : Subgroup.zpowers a₂ ≤
      Subgroup.normalizer ((Subgroup.zpowers a₁ ⊔ V : Subgroup D) : Set D) :=
    Subgroup.zpowers_le.mpr (U_le_normalizer g.hyp hzP hP_U g.a₂_mem_U)
  have c1 := GoldAmN.card_sup_le_of_le_normalizer (Subgroup.zpowers a₁) V h1
  have c2 := GoldAmN.card_sup_le_of_le_normalizer (Subgroup.zpowers a₂)
    (Subgroup.zpowers a₁ ⊔ V) h2
  have hle : conjClosure V B ≤ Subgroup.zpowers a₂ ⊔ (Subgroup.zpowers a₁ ⊔ V) := by
    rw [g.U_eq_closure, Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right g.a_mem)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right g.hyp.natural.z_mem_V)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have c3 := Subgroup.card_le_of_le hle
  have n1 := card_zpowers_le_two' g.a₁_sq
  have n2 := card_zpowers_le_two' g.a₂_sq
  rw [g.hyp.natural.card_eq] at c1
  calc Nat.card (conjClosure V B) ≤ _ := c3
    _ ≤ _ := c2
    _ ≤ 2 * (2 * 4) := Nat.mul_le_mul n2 (c1.trans (Nat.mul_le_mul_right 4 n1))
    _ = 16 := by norm_num

end Card

end GoldAmL2S

end F6

end CFSG.Quasithin
