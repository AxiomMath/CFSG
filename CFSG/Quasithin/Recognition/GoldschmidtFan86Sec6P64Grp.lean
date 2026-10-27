module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P64Alg

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

theorem relIndex_centralizer_eq_sixteen (V : Subgroup G) [Finite V] (x z c : G) (hx5 : x ^ 5 = 1)
    (hcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u) (hsq : ∀ v ∈ V, v * v = 1)
    (hnorm : ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hxz : x * z = z * x) (hcx : x * c * x⁻¹ ≠ c)
    (hgen : V = Subgroup.closure
      ({z} ∪ Set.range fun k : Fin 5 => x ^ (k : ℕ) * c * (x ^ (k : ℕ))⁻¹)) :
    (Subgroup.centralizer ({x} : Set G)).relIndex V = 16 := by
  classical
  have hz : z ∈ V := hgen ▸ Subgroup.subset_closure (Or.inl rfl)
  have hc : c ∈ V := hgen ▸ Subgroup.subset_closure (Or.inr ⟨0, by simp⟩)
  let _ : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }
  have hpow : ∀ n : ℕ, ∀ v ∈ V, x ^ n * v * (x ^ n)⁻¹ ∈ V := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      have e : x ^ (n + 1) * v * (x ^ (n + 1))⁻¹ = x * (x ^ n * v * (x ^ n)⁻¹) * x⁻¹ := by
        group
      rw [e]
      exact hnorm _ (ih v hv)
  have e1 : x⁻¹ = x ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx5)
  have e2 : (x ^ 4)⁻¹ = x := by rw [← e1, inv_inv]
  have hnorm' : ∀ v ∈ V, x⁻¹ * v * x ∈ V := by
    intro v hv
    have := hpow 4 v hv
    rwa [e2, ← e1] at this
  let σ : MulAut V :=
    { toFun := fun v => ⟨x * v * x⁻¹, hnorm v v.2⟩
      invFun := fun v => ⟨x⁻¹ * v * x, hnorm' v v.2⟩
      left_inv := fun v => Subtype.ext (by
        show x⁻¹ * (x * (v : G) * x⁻¹) * x = v
        group)
      right_inv := fun v => Subtype.ext (by
        show x * (x⁻¹ * (v : G) * x) * x⁻¹ = v
        group)
      map_mul' := fun a b => Subtype.ext (by
        show x * (a * b : V) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  have hσ1 : ∀ v : V, (σ v : G) = x * v * x⁻¹ := fun v => rfl
  have hσn : ∀ (n : ℕ) (v : V), ((σ ^ n) v : G) = x ^ n * v * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, MulAut.mul_apply, ih, hσ1]
      group
  have hσ5 : σ ^ 5 = 1 := by
    ext v
    rw [hσn, hx5]
    simp
  have hsq' : ∀ a : V, a * a = 1 := fun a => Subtype.ext (hsq a a.2)
  have hz' : σ ⟨z, hz⟩ = ⟨z, hz⟩ := Subtype.ext (by rw [hσ1]; simp [hxz])
  have hc' : σ ⟨c, hc⟩ ≠ ⟨c, hc⟩ := fun h => hcx (congrArg Subtype.val h)
  have hk : ∀ k : Fin 5, (⟨x ^ (k : ℕ) * c * (x ^ (k : ℕ))⁻¹, hpow k c hc⟩ : V) =
      (σ ^ (k : ℕ)) ⟨c, hc⟩ := fun k => Subtype.ext (by rw [hσn])
  have hgen' : Subgroup.closure ({(⟨z, hz⟩ : V)} ∪
      Set.range fun k : Fin 5 => (σ ^ (k : ℕ)) ⟨c, hc⟩) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : (v : G) ∈ Subgroup.closure
        ({z} ∪ Set.range fun k : Fin 5 => x ^ (k : ℕ) * c * (x ^ (k : ℕ))⁻¹) := hgen ▸ v.2
    have key : ∀ g (hg : g ∈ Subgroup.closure
        ({z} ∪ Set.range fun k : Fin 5 => x ^ (k : ℕ) * c * (x ^ (k : ℕ))⁻¹)),
        ∃ h : g ∈ V, (⟨g, h⟩ : V) ∈ Subgroup.closure ({(⟨z, hz⟩ : V)} ∪
          Set.range fun k : Fin 5 => (σ ^ (k : ℕ)) ⟨c, hc⟩) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with hy | ⟨k, rfl⟩
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨hz, Subgroup.subset_closure (Or.inl rfl)⟩
        · exact ⟨hpow k c hc, by
            rw [hk k]
            exact Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)⟩
      | one => exact ⟨one_mem _, one_mem _⟩
      | mul y w _ _ hy hw =>
        obtain ⟨h1, h2⟩ := hy
        obtain ⟨h3, h4⟩ := hw
        exact ⟨mul_mem h1 h3, mul_mem h2 h4⟩
      | inv y _ hy =>
        obtain ⟨h1, h2⟩ := hy
        exact ⟨inv_mem h1, inv_mem h2⟩
    obtain ⟨h, h'⟩ := key v hv
    exact h'
  have key := index_ker_shiftHom σ hσ5 hsq' ⟨z, hz⟩ ⟨c, hc⟩ hz' hc' hgen'
  have hker : (Subgroup.centralizer ({x} : Set G)).subgroupOf V = (shiftHom σ).ker := by
    ext v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, MonoidHom.mem_ker,
      shiftHom_apply]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      refine Subtype.ext ?_
      show x * (v : G) * x⁻¹ * (v : G)⁻¹ = 1
      rw [h]
      group
    · intro h
      have h1 : x * (v : G) * x⁻¹ * (v : G)⁻¹ = 1 := congrArg Subtype.val h
      have h2 : x * (v : G) * x⁻¹ = v := mul_inv_eq_one.1 h1
      calc x * (v : G) = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [h2]
  rw [Subgroup.relIndex, hker]
  exact key

end CFSG.Quasithin.Fan86
