module

public import CFSG.Quasithin.EmptyFaithful.SzF53MNatL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G]

theorem conj_mem_inf_centralizer_oTwoRes {X Z : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (Z : Set G)) {g : G} (hg : g ∈ X) {k : G}
    (hk : k ∈ Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) :
    g * k * g⁻¹ ∈ Z ⊓ Subgroup.centralizer (oTwoRes X : Set G) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hXN hg) k).mp hk.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro o ho
  have h1 : g⁻¹ * o * g ∈ oTwoRes X := by
    have := Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes X (X.inv_mem hg)) o
    simpa using this.mp ho
  have h2 := Subgroup.mem_centralizer_iff.mp hk.2 _ h1
  calc o * (g * k * g⁻¹) = g * ((g⁻¹ * o * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * o * g)) * g⁻¹ := by rw [h2]
    _ = g * k * g⁻¹ * o := by group

theorem isSec_inf_centralizer_oTwoRes {X Z : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G)) :
    IsSec X (Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) Z where
  le := inf_le_left
  normN := hXN
  normL := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨conj_mem_inf_centralizer_oTwoRes hXN hg, fun hh => ?_⟩
    have := conj_mem_inf_centralizer_oTwoRes hXN (X.inv_mem hg) hh
    simpa [mul_assoc] using this
  comm := fun x hx y hy => by
    have h1 := isMulCommutative_subgroup_iff.mp hZ.1 x hx y hy
    have : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]; exact h1
    rw [this]; exact Subgroup.one_mem _
  sq := fun x hx => by
    rw [hZ.2 x hx]; exact Subgroup.one_mem _

theorem mem_inf_centralizer_oTwoRes_of_forall {X Z : Subgroup G} (hZ : IsElemAbelian 2 Z)
    {z : G} (hz : z ∈ Z)
    (h : ∀ x ∈ X, z⁻¹ * (x * z * x⁻¹) ∈ Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) :
    z ∈ Z ⊓ Subgroup.centralizer (oTwoRes X : Set G) := by
  refine ⟨hz, ?_⟩
  have hodd : ∀ x ∈ X, ∀ m : ℕ, Odd m → x ^ m = 1 → z * x = x * z := by
    intro x hx m hm hxm
    set k := z⁻¹ * (x * z * x⁻¹) with hkdef
    have hk := h x hx
    have hxo : x ∈ oTwoRes X := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
    have hxk : x * k = k * x := Subgroup.mem_centralizer_iff.mp hk.2 x hxo
    have hxz : x * z * x⁻¹ = z * k := by rw [hkdef]; group
    have hpow : ∀ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = z * k ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hxk' : x * k ^ j * x⁻¹ = k ^ j := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (Commute.pow_right (show Commute x k from hxk) j).eq
        calc x ^ (j + 1) * z * (x ^ (j + 1))⁻¹
            = x * (x ^ j * z * (x ^ j)⁻¹) * x⁻¹ := by group
          _ = (x * z * x⁻¹) * (x * k ^ j * x⁻¹) := by rw [ih]; group
          _ = z * k ^ (j + 1) := by rw [hxz, hxk', pow_succ']; group
    have hk2 : k ^ 2 = 1 := hZ.2 k hk.1
    obtain ⟨r, rfl⟩ := hm
    have hkm : k ^ (2 * r + 1) = k := by
      rw [pow_succ, pow_mul, hk2, one_pow, one_mul]
    have h1 := hpow (2 * r + 1)
    rw [hxm, hkm] at h1
    have h2 : k = 1 := by
      have : z = z * k := by simpa using h1
      simpa using this.symm
    have h3 : x * z * x⁻¹ = z := by rw [hxz, h2, mul_one]
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  refine Subgroup.mem_centralizer_iff.mpr fun o ho => ?_
  have hle : oTwoRes X ≤ Subgroup.centralizer ({z} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, m, hm, hxm⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hodd x hx m hm hxm
  exact (Subgroup.mem_centralizer_iff.mp (hle ho) z rfl).symm

variable [Finite G]

theorem not_le_inf_centralizer_oTwoRes {X Z : Subgroup G} (θ : ↥X →* Perm (Fin 5))
    (hθ : Function.Surjective θ) (hk : θ.ker = (cSecIn X ⊥ Z).subgroupOf X) :
    ¬ Z ≤ Subgroup.centralizer (oTwoRes X : Set G) := by
  intro hZ
  have hσ : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hσ1 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  obtain ⟨f, hf⟩ := hθ (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2)
  have hmem : (f : G) ∈ oTwoRes X ⊔ cSecIn X ⊥ Z :=
    (mem_oTwoRes_sup_iff hθ hk f.2).mpr (by simp [hf])
  have hle : oTwoRes X ⊔ cSecIn X ⊥ Z ≤ Subgroup.centralizer (Z : Set G) := by
    refine sup_le ?_ ?_
    · intro o ho
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hZ hz) o ho).symm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨-, hg⟩
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have := hg z hz
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  have hc := Subgroup.mem_centralizer_iff.mp (hle hmem)
  have hker : f ∈ θ.ker := by
    rw [hk, Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨f.2, fun x hx => ?_⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact (hc x hx).symm
  exact hσ1 (hf ▸ MonoidHom.mem_ker.mp hker)

end CFSG.Quasithin.F53Mod
