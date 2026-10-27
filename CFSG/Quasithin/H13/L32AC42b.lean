module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.L32A.C

theorem eq_one_of_cube_of_sq {X : Type*} [Group X] {y : X} (h3 : y ^ 3 = 1) (h2 : y * y = 1) :
    y = 1 := by
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem perm_three_gen : ∀ c d : Equiv.Perm (Fin 3), c ^ 3 = 1 → c ≠ 1 → d ^ 2 = 1 → d ≠ 1 →
    ∀ σ : Equiv.Perm (Fin 3), ∃ a < 3, ∃ b < 2, σ = c ^ a * d ^ b := by
  decide

section Inv

variable {X : Type*} [Group X] {x t : X}

theorem conj_pow_eq_inv (htx : t * x * t⁻¹ = x⁻¹) (i : ℕ) : t * x ^ i * t⁻¹ = (x ^ i)⁻¹ := by
  rw [← conj_pow, htx, inv_pow]

theorem not_comm_of_inv (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (htx : t * x * t⁻¹ = x⁻¹) (i : ℕ) :
    t * x ^ i * x ≠ x * (t * x ^ i) := by
  intro h
  have hxx : x * x ≠ 1 := fun h => hx1 (eq_one_of_cube_of_sq hx3 h)
  apply hxx
  have h1 : t * x * t⁻¹ = x := by
    calc t * x * t⁻¹ = t * x ^ i * x * (x ^ i)⁻¹ * t⁻¹ := by group
      _ = x * (t * x ^ i) * (x ^ i)⁻¹ * t⁻¹ := by rw [h]
      _ = x := by group
  calc x * x = x * (t * x * t⁻¹)⁻¹ := by rw [htx, inv_inv]
    _ = x * x⁻¹ := by rw [h1]
    _ = 1 := mul_inv_cancel x

theorem sq_eq_one_of_inv (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (htx : t * x * t⁻¹ = x⁻¹)
    {R : Subgroup X} (ht : t ∈ R) (hR : ∀ r ∈ R, ∃ i : ℕ, r = x ^ i ∨ r = t * x ^ i) :
    t * t = 1 := by
  obtain ⟨i, hi | hi⟩ := hR (t * t) (mul_mem ht ht)
  · have h1 : t * x ^ i * t⁻¹ = x ^ i := by
      rw [← hi]
      group
    rw [conj_pow_eq_inv htx] at h1
    have h2 : x ^ i * x ^ i = 1 := by
      calc x ^ i * x ^ i = (x ^ i)⁻¹ * x ^ i := by rw [h1]
        _ = 1 := inv_mul_cancel _
    have h3 : (x ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    rw [hi, eq_one_of_cube_of_sq h3 h2]
  · exfalso
    have htt : t = x ^ i := mul_left_cancel hi
    apply not_comm_of_inv hx3 hx1 htx 0
    rw [pow_zero, mul_one, htt, ← pow_succ, ← pow_succ']

end Inv

theorem exists_bijective_s5s3 {X : Type*} [Group X] [Finite X] {K : Subgroup X} [hKn : K.Normal]
    (φ : ↥K ≃* ↥(alternatingGroup (Fin 5))) {x t : X}
    (hx : x ∈ Subgroup.centralizer (K : Set X)) (ht : t ∈ Subgroup.centralizer (K : Set X))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (htx : t * x * t⁻¹ = x⁻¹)
    (hR : ∀ r ∈ Subgroup.centralizer (K : Set X), ∃ i : ℕ, r = x ^ i ∨ r = t * x ^ i)
    {τ : X} (hτ : ∀ k ∈ K, ∀ r ∈ Subgroup.centralizer (K : Set X), τ ≠ k * r) :
    ∃ ρ : X →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3), Function.Bijective ρ := by
  classical
  set R := Subgroup.centralizer (K : Set X) with hRdef
  have hRn : R.Normal := Subgroup.normal_centralizer
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hconj := conj_pow_eq_inv htx
  have hxx : x * x ≠ 1 := fun h => hx1 (eq_one_of_cube_of_sq hx3 h)
  have hcx := not_comm_of_inv hx3 hx1 htx
  have ht2 : t * t = 1 := sq_eq_one_of_inv hx3 hx1 htx ht hR
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  let e5 : Equiv.Perm (Fin 5) ≃* MulAut ↥(alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))
  let ρ₁ : X →* Equiv.Perm (Fin 5) :=
    e5.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal)
  have hρ₁K : ∀ k (hk : k ∈ K),
      ρ₁ k = ((φ ⟨k, hk⟩ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) := by
    intro k hk
    show e5.symm (MulAut.congr φ (MulAut.conjNormal k)) = _
    rw [MulEquiv.symm_apply_eq]
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have h1 : (MulAut.conjNormal k (φ.symm y) : ↥K) = ⟨k, hk⟩ * φ.symm y * ⟨k, hk⟩⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    show ((φ (MulAut.conjNormal k (φ.symm y)) : ↥(alternatingGroup (Fin 5))) :
      Equiv.Perm (Fin 5)) = _
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp [e5, MulAut.conjNormal_apply]
  have hρ₁R : ∀ r ∈ R, ρ₁ r = 1 := by
    intro r hr
    show e5.symm (MulAut.congr φ (MulAut.conjNormal r)) = 1
    have h1 : (MulAut.conjNormal r : MulAut ↥K) = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [(Subgroup.mem_centralizer_iff.mp hr _ y.2).symm, mul_inv_cancel_right]
    rw [h1, map_one, map_one]
  have hρ₁ker : ∀ g, ρ₁ g = 1 → g ∈ R := by
    intro g hg
    have h1 : (MulAut.conjNormal g : MulAut ↥K) = 1 := by
      have h2 : MulAut.congr φ (MulAut.conjNormal g) = 1 := by
        have h3 : e5.symm (MulAut.congr φ (MulAut.conjNormal g)) = 1 := hg
        rwa [MulEquiv.symm_apply_eq, map_one] at h3
      rwa [MulEquiv.map_eq_one_iff] at h2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := congrArg (fun α : MulAut ↥K => ((α ⟨y, hy⟩ : ↥K) : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group
  have hinvl : ∀ i : ℕ, t * x ^ i ∈ R ∧ t * x ^ i * (t * x ^ i) = 1 ∧ t * x ^ i ≠ 1 := by
    intro i
    refine ⟨mul_mem ht (pow_mem hx i), ?_, fun h => ?_⟩
    · calc t * x ^ i * (t * x ^ i) = t * x ^ i * t⁻¹ * (t * t) * x ^ i := by group
        _ = 1 := by rw [hconj, ht2]; group
    · apply hcx i
      rw [h, one_mul, mul_one]
  set I := {y : X // y ∈ R ∧ y * y = 1 ∧ y ≠ 1} with hIdef
  have hconjI : ∀ (g : X) (y : I), g * (y : X) * g⁻¹ ∈ R ∧
      g * (y : X) * g⁻¹ * (g * (y : X) * g⁻¹) = 1 ∧ g * (y : X) * g⁻¹ ≠ 1 := by
    intro g y
    refine ⟨hRn.conj_mem _ y.2.1 g, ?_, fun h => y.2.2.2 ?_⟩
    · calc g * (y : X) * g⁻¹ * (g * (y : X) * g⁻¹) = g * ((y : X) * y) * g⁻¹ := by group
        _ = 1 := by rw [y.2.2.1]; group
    · calc (y : X) = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
  let act : MulAction X I :=
    { smul := fun g y => ⟨g * y * g⁻¹, hconjI g y⟩
      one_smul := fun y => Subtype.ext (by
        show (1 : X) * y * 1⁻¹ = y
        group)
      mul_smul := fun g h y => Subtype.ext (by
        show g * h * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹
        group) }
  have hsmul : ∀ (g : X) (y : I), ((g • y : I) : X) = g * y * g⁻¹ := fun g y => rfl
  let f : Fin 3 → I := fun i => ⟨t * x ^ (i : ℕ), hinvl i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => ?_, fun y => ?_⟩
    · have h1 : x ^ (i : ℕ) = x ^ (j : ℕ) := mul_left_cancel (congrArg Subtype.val hij)
      exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hox]; exact i.2) (by rw [hox]; exact j.2) h1)
    · obtain ⟨i, hi | hi⟩ := hR y y.2.1
      · exfalso
        apply y.2.2.2
        have h3 : (y : X) ^ 3 = 1 := by rw [hi, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
        exact eq_one_of_cube_of_sq h3 y.2.2.1
      · refine ⟨⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, Subtype.ext ?_⟩
        show t * x ^ (i % 3) = y
        rw [hi, ← hox, pow_mod_orderOf]
  let eI : I ≃ Fin 3 := (Equiv.ofBijective f hf).symm
  let ρ₂ : X →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom eI).toMonoidHom.comp (MulAction.toPermHom X I)
  have hρ₂ : ∀ g, ρ₂ g = 1 ↔ ∀ y : I, g * (y : X) * g⁻¹ = y := by
    intro g
    constructor
    · intro h y
      have h1 : MulAction.toPermHom X I g = 1 := by
        have h3 : (Equiv.permCongrHom eI) (MulAction.toPermHom X I g) = 1 := h
        rwa [MulEquiv.map_eq_one_iff] at h3
      have h2 := congrArg (fun σ : Equiv.Perm I => ((σ y : I) : X)) h1
      exact h2
    · intro h
      have h1 : MulAction.toPermHom X I g = 1 := Equiv.ext fun y => Subtype.ext (h y)
      show (Equiv.permCongrHom eI) (MulAction.toPermHom X I g) = 1
      rw [h1, map_one]
  have hρ₂K : ∀ k ∈ K, ρ₂ k = 1 := by
    intro k hk
    rw [hρ₂]
    intro y
    rw [Subgroup.mem_centralizer_iff.mp y.2.1 k hk, mul_inv_cancel_right]
  have hρ₂x : ρ₂ x ≠ 1 := by
    rw [Ne, hρ₂]
    intro h
    have h1 := h (f 0)
    apply hcx 0
    simp only [f, Fin.val_zero, pow_zero, mul_one] at h1 ⊢
    calc t * x = x * t * x⁻¹ * x := by rw [h1]
      _ = x * t := by group
  have hρ₂t : ρ₂ t ≠ 1 := by
    rw [Ne, hρ₂]
    intro h
    have h1 := h (f 1)
    simp only [f, Fin.val_one, pow_one] at h1
    apply hxx
    have h2 : x = x⁻¹ := by
      calc x = t * t * x * t⁻¹ * t := by rw [ht2]; group
        _ = t * (t * x) * t⁻¹ * t := by group
        _ = t * x * t := by rw [h1]
        _ = t * x * t⁻¹ := by rw [htinv]
        _ = x⁻¹ := htx
    calc x * x = x * x⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel x
  have hρ₂x3 : ρ₂ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hρ₂t2 : ρ₂ t ^ 2 = 1 := by rw [← map_pow, pow_two, ht2, map_one]
  have hρ₂R : ∀ r ∈ R, ρ₂ r = 1 → r = 1 := by
    intro r hr h
    rw [hρ₂] at h
    have h0 := h (f 0)
    have h1 := h (f 1)
    simp only [f, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at h0 h1
    have hrt : r * t = t * r := by
      calc r * t = r * t * r⁻¹ * r := by group
        _ = t * r := by rw [h0]
    have hrx : r * x = x * r := by
      have e : r * (t * x) = t * x * r := by
        calc r * (t * x) = r * (t * x) * r⁻¹ * r := by group
          _ = t * x * r := by rw [h1]
      have hrt' : r * t⁻¹ = t⁻¹ * r := by rw [htinv]; exact hrt
      calc r * x = r * t⁻¹ * (t * x) := by group
        _ = t⁻¹ * r * (t * x) := by rw [hrt']
        _ = t⁻¹ * (r * (t * x)) := by group
        _ = t⁻¹ * (t * x * r) := by rw [e]
        _ = x * r := by group
    obtain ⟨i, hi | hi⟩ := hR r hr
    · subst hi
      have h2 : t * x ^ i * t⁻¹ = x ^ i := by
        calc t * x ^ i * t⁻¹ = x ^ i * t * t⁻¹ := by rw [hrt]
          _ = x ^ i := by group
      rw [hconj] at h2
      have h3 : x ^ i * x ^ i = 1 := by
        calc x ^ i * x ^ i = (x ^ i)⁻¹ * x ^ i := by rw [h2]
          _ = 1 := inv_mul_cancel _
      exact eq_one_of_cube_of_sq (by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]) h3
    · exact absurd (hi ▸ hrx) (hcx i)
  have hτodd : ρ₁ τ ∉ alternatingGroup (Fin 5) := by
    intro h
    set k : ↥K := φ.symm ⟨ρ₁ τ, h⟩ with hk
    have h1 : ρ₁ k = ρ₁ τ := by
      rw [hρ₁K k k.2, Subtype.coe_eta, hk, MulEquiv.apply_symm_apply]
    have h2 : (k : X)⁻¹ * τ ∈ R := hρ₁ker _ (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    exact hτ k k.2 _ h2 (by group)
  refine ⟨ρ₁.prod ρ₂, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ρ₁ g = 1 := congrArg Prod.fst hg
    have h2 : ρ₂ g = 1 := congrArg Prod.snd hg
    exact hρ₂R g (hρ₁ker g h1) h2
  · rintro ⟨π, σ⟩
    have hRsurj : ∀ σ' : Equiv.Perm (Fin 3), ∃ r ∈ R, ρ₂ r = σ' := by
      intro σ'
      obtain ⟨a, -, b, -, hab⟩ := perm_three_gen _ _ hρ₂x3 hρ₂x hρ₂t2 hρ₂t σ'
      exact ⟨x ^ a * t ^ b, mul_mem (pow_mem hx a) (pow_mem ht b),
        by rw [map_mul, map_pow, map_pow, hab]⟩
    have hKsurj : ∀ π' ∈ alternatingGroup (Fin 5), ∃ k ∈ K, ρ₁ k = π' := by
      intro π' hπ'
      refine ⟨φ.symm ⟨π', hπ'⟩, (φ.symm ⟨π', hπ'⟩).2, ?_⟩
      rw [hρ₁K _ (φ.symm ⟨π', hπ'⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
    by_cases hπ : π ∈ alternatingGroup (Fin 5)
    · obtain ⟨k, hk, hkπ⟩ := hKsurj π hπ
      obtain ⟨r, hr, hrσ⟩ := hRsurj σ
      refine ⟨k * r, Prod.ext ?_ ?_⟩
      · show ρ₁ (k * r) = π
        rw [map_mul, hkπ, hρ₁R r hr, mul_one]
      · show ρ₂ (k * r) = σ
        rw [map_mul, hρ₂K k hk, hrσ, one_mul]
    · have hπ' : π * (ρ₁ τ)⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hπ hτodd ⊢
        rw [map_mul, map_inv, Int.units_ne_iff_eq_neg.mp hπ, Int.units_ne_iff_eq_neg.mp hτodd]
        decide
      obtain ⟨k, hk, hkπ⟩ := hKsurj _ hπ'
      obtain ⟨r, hr, hrσ⟩ := hRsurj (σ * (ρ₂ τ)⁻¹)
      refine ⟨k * r * τ, Prod.ext ?_ ?_⟩
      · show ρ₁ (k * r * τ) = π
        rw [map_mul, map_mul, hkπ, hρ₁R r hr, mul_one, inv_mul_cancel_right]
      · show ρ₂ (k * r * τ) = σ
        rw [map_mul, map_mul, hρ₂K k hk, hrσ, one_mul, inv_mul_cancel_right]

end CFSG.Quasithin.H13.L32A.C
