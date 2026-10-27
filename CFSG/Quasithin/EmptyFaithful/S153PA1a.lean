module

public import CFSG.Quasithin.EmptyFaithful.S153PDef

public section

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise

namespace S153P

namespace PA1

section Generic

variable {G : Type} [Group G]

theorem conj_eq_iff {g a b : G} : g * a * g⁻¹ = b ↔ a = g⁻¹ * b * g := by
  constructor
  · intro h; rw [← h]; group
  · intro h; rw [h]; group

theorem conj_cancel_iff {g a b : G} : g * a * g⁻¹ = g * b * g⁻¹ ↔ a = b := by simp

theorem y_zp (z y : G) : y * zp z y * y⁻¹ = z := by simp only [zp]; group

theorem mem_normalizer_of_conj {V : Subgroup G} {g : G}
    (h1 : ∀ v ∈ V, g * v * g⁻¹ ∈ V) (h2 : ∀ v ∈ V, g⁻¹ * v * g ∈ V) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h1 v, fun hv => ?_⟩
  simpa [mul_assoc] using h2 _ hv

theorem le_normalizer_of_conj {K S : Subgroup G}
    (h : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S) : K ≤ Subgroup.normalizer (S : Set G) := by
  intro k hk
  refine mem_normalizer_of_conj (h k hk) (fun v hv => ?_)
  simpa using h k⁻¹ (K.inv_mem hk) v hv

theorem conj_mem_sup {S T V : Subgroup G} {g : G} (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ V)
    (hT : ∀ t ∈ T, g * t * g⁻¹ ∈ V) {v : G} (hv : v ∈ S ⊔ T) : g * v * g⁻¹ ∈ V := by
  have h : S ⊔ T ≤ V.comap (MulAut.conj g).toMonoidHom := sup_le hS hT
  exact h hv

theorem conj_mem_centralizer {V : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hk : k ∈ Subgroup.centralizer (V : Set G)) :
    g * k * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
  have h := hk _ hv'
  calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * k * g⁻¹ * v := by group

theorem comm_mem_centralizer {V : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hk : k ∈ Subgroup.centralizer (V : Set G)) :
    ⁅g, k⁆ ∈ Subgroup.centralizer (V : Set G) :=
  mul_mem (conj_mem_centralizer hg hk) (inv_mem hk)

theorem conjSubgroup_zpowers (g x : G) :
    conjSubgroup (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold conjSubgroup
  rw [MonoidHom.map_zpowers]
  simp

end Generic

section Basic

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem z_mem_Z : z ∈ Z := by rw [A.Z_eq]; exact Subgroup.mem_zpowers z

theorem mem_Z_iff {x : G} : x ∈ Z ↔ x = 1 ∨ x = z := by
  rw [A.Z_eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact A.z_sq
    have hn : z ^ n = z ^ (n % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod n 2]
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [hn, h]; simp
    · right; rw [hn, h]; simp
  · rintro (h | h)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩

theorem mem_Mc_iff {g : G} : g ∈ Mc ↔ z * g = g * z := by
  rw [A.Mc_eq, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h z (z_mem_Z A)
  · intro h c hc
    rcases (mem_Z_iff A).mp hc with h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact h

theorem zp_sq : zp z y * zp z y = 1 := by
  have := A.z_sq
  calc zp z y * zp z y = y⁻¹ * (z * z) * y := by simp only [zp]; group
    _ = 1 := by rw [this]; group

theorem zp_comm : z * zp z y = zp z y * z := (A.Z_central _ A.zp_mem).symm

theorem yinv_zp : y⁻¹ * zp z y * y = z * zp z y := by
  have h := A.yz
  have h1 : z = zp z y * (y⁻¹ * zp z y * y) := by
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = y⁻¹ * (z * (y⁻¹ * z * y)) * y := by rw [h]
      _ = (y⁻¹ * z * y) * (y⁻¹ * (y⁻¹ * z * y) * y) := by group
      _ = zp z y * (y⁻¹ * zp z y * y) := rfl
  have h2 : y⁻¹ * zp z y * y = zp z y * z := by
    calc y⁻¹ * zp z y * y = zp z y * (zp z y * (y⁻¹ * zp z y * y)) := by
          rw [← mul_assoc (zp z y) (zp z y), zp_sq A, one_mul]
      _ = zp z y * z := by rw [← h1]
  rw [h2, ← zp_comm A]

theorem zp_ne_one : zp z y ≠ 1 := by
  intro h
  apply A.z_ne
  have := y_zp z y
  rw [h] at this
  simpa using this.symm

theorem z_zp_ne_one : z * zp z y ≠ 1 := by
  intro h
  apply A.zp_ne
  have h' : z * zp z y = z * z := by rw [h, A.z_sq]
  exact mul_left_cancel h'

theorem z_ne_z_zp : z ≠ z * zp z y := by
  intro h
  apply zp_ne_one A
  have : z * zp z y = z * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel this

theorem zp_ne_z_zp : zp z y ≠ z * zp z y := by
  intro h
  apply A.z_ne
  have : 1 * zp z y = z * zp z y := by rw [one_mul]; exact h
  exact (mul_right_cancel this).symm

theorem mem_conjZ_iff {x : G} : x ∈ conjSubgroup Z y ↔ x = 1 ∨ x = zp z y := by
  rw [mem_conjSubgroup_iff, mem_Z_iff A, conj_eq_iff, conj_eq_iff]
  simp [zp]

theorem zp_mem_conjZ : zp z y ∈ conjSubgroup Z y := by
  rw [mem_conjSubgroup_iff, y_zp z y]; exact z_mem_Z A

theorem Z_le_normalizer_conjZ : Z ≤ Subgroup.normalizer (conjSubgroup Z y : Set G) := by
  apply le_normalizer_of_conj
  intro a ha b hb
  have hcomm : a * b = b * a := by
    rcases (mem_Z_iff A).mp ha with h | h
    · rw [h]; simp
    · rcases (mem_conjZ_iff A).mp hb with h' | h'
      · rw [h']; simp
      · rw [h, h']; exact zp_comm A
  have : a * b * a⁻¹ = b := by rw [mul_inv_eq_iff_eq_mul]; exact hcomm
  rw [this]; exact hb

theorem V0_carrier : (V0g Z y : Set G) = (Z : Set G) * (conjSubgroup Z y : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right Z (conjSubgroup Z y) (Z_le_normalizer_conjZ A)

theorem z_mem_V0 : z ∈ V0g Z y := Subgroup.mem_sup_left (z_mem_Z A)

theorem zp_mem_V0 : zp z y ∈ V0g Z y := Subgroup.mem_sup_right (zp_mem_conjZ A)

theorem mem_V0_iff {v : G} : v ∈ V0g Z y ↔ v = 1 ∨ v = z ∨ v = zp z y ∨ v = z * zp z y := by
  have h : v ∈ (V0g Z y : Set G) ↔ v ∈ (Z : Set G) * (conjSubgroup Z y : Set G) := by
    rw [V0_carrier A]
  rw [← SetLike.mem_coe, h, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases (mem_Z_iff A).mp ha with h1 | h1 <;> rcases (mem_conjZ_iff A).mp hb with h2 | h2 <;>
      rw [h1, h2] <;> simp
  · rintro (h | h | h | h)
    · exact ⟨1, one_mem _, 1, one_mem _, by simp [h]⟩
    · exact ⟨z, z_mem_Z A, 1, one_mem _, by simp [h]⟩
    · exact ⟨1, one_mem _, zp z y, zp_mem_conjZ A, by simp [h]⟩
    · exact ⟨z, z_mem_Z A, zp z y, zp_mem_conjZ A, h.symm⟩

theorem y_conj_V0 {v : G} (hv : v ∈ V0g Z y) : y * v * y⁻¹ ∈ V0g Z y := by
  refine conj_mem_sup (S := Z) (T := conjSubgroup Z y) ?_ ?_ hv
  · intro s hs
    rcases (mem_Z_iff A).mp hs with h | h
    · rw [h]; simp
    · rw [h, A.yz]; exact mul_mem (z_mem_V0 A) (zp_mem_V0 A)
  · intro t ht
    rcases (mem_conjZ_iff A).mp ht with h | h
    · rw [h]; simp
    · rw [h, y_zp z y]; exact z_mem_V0 A

theorem yinv_conj_V0 {v : G} (hv : v ∈ V0g Z y) : y⁻¹ * v * y ∈ V0g Z y := by
  have key : y⁻¹ * v * y⁻¹⁻¹ ∈ V0g Z y := by
    refine conj_mem_sup (S := Z) (T := conjSubgroup Z y) ?_ ?_ hv
    · intro s hs
      rcases (mem_Z_iff A).mp hs with h | h
      · rw [h]; simp
      · rw [h, inv_inv]; exact zp_mem_V0 A
    · intro t ht
      rcases (mem_conjZ_iff A).mp ht with h | h
      · rw [h]; simp
      · rw [h, inv_inv, yinv_zp A]; exact mul_mem (z_mem_V0 A) (zp_mem_V0 A)
  simpa using key

theorem y_mem_normV0 : y ∈ Subgroup.normalizer (V0g Z y : Set G) :=
  mem_normalizer_of_conj (fun _ hv => y_conj_V0 A hv) (fun _ hv => yinv_conj_V0 A hv)

theorem U_le_normV0 : U ≤ Subgroup.normalizer (V0g Z y : Set G) := by
  apply le_normalizer_of_conj
  intro u hu v hv
  refine conj_mem_sup (S := Z) (T := conjSubgroup Z y) ?_ ?_ hv
  · intro s hs
    rcases (mem_Z_iff A).mp hs with h | h
    · rw [h]; simp
    · rw [h]
      have : u * z * u⁻¹ = z := by rw [mul_inv_eq_iff_eq_mul]; exact A.Z_central u hu
      rw [this]; exact z_mem_V0 A
  · intro t ht
    rcases (mem_conjZ_iff A).mp ht with h | h
    · rw [h]; simp
    · rw [h]
      have hc : ⁅u, zp z y⁆ ∈ Z := A.U_comm u hu _ A.zp_mem
      have : u * zp z y * u⁻¹ = ⁅u, zp z y⁆ * zp z y := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hc) (zp_mem_V0 A)

theorem U'_le_normV0 : conjSubgroup U y ≤ Subgroup.normalizer (V0g Z y : Set G) := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have key : y⁻¹ * (y * x * y⁻¹) * y ∈ Subgroup.normalizer (V0g Z y : Set G) :=
    mul_mem (mul_mem (inv_mem (y_mem_normV0 A)) (U_le_normV0 A hx)) (y_mem_normV0 A)
  have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
  rwa [e] at key

end Basic

end PA1

namespace Abs56

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem V0_eq : V0g Z y = V0of z (zp z y) := by
  show Z ⊔ conjSubgroup Z y = Subgroup.zpowers z ⊔ Subgroup.zpowers (zp z y)
  rw [A.Z_eq, PA1.conjSubgroup_zpowers]

theorem V0_card [Finite G] : Nat.card ↥(V0g Z y) = 4 := by
  have hset : (V0g Z y : Set G) = {1, z, zp z y, z * zp z y} := by
    ext v
    simp only [SetLike.mem_coe, PA1.mem_V0_iff A, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1 : (1 : G) ∉ ({z, zp z y, z * zp z y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨A.z_ne.symm, (PA1.zp_ne_one A).symm, (PA1.z_zp_ne_one A).symm⟩
  have h2 : z ∉ ({zp z y, z * zp z y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => A.zp_ne h.symm, PA1.z_ne_z_zp A⟩
  calc Nat.card ↥(V0g Z y) = Nat.card ↥(V0g Z y : Set G) := rfl
    _ = (V0g Z y : Set G).ncard := Nat.card_coe_set_eq _
    _ = ({1, z, zp z y, z * zp z y} : Set G).ncard := by rw [hset]
    _ = 4 := by
      rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
        Set.ncard_pair (PA1.zp_ne_z_zp A)]

theorem J_le_normV0 : Jg U y ≤ Subgroup.normalizer ((V0g Z y : Subgroup G) : Set G) :=
  sup_le (PA1.U_le_normV0 A) (PA1.U'_le_normV0 A)

end Abs56

end S153P

end CFSG.Quasithin
