module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.GoldschmidtCTKFam
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

@[expose] def kleinSigma : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def kleinTau : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem sq_eq_one_of_comm_kleinSigma (g : alternatingGroup (Fin 5))
    (hg : g * kleinSigma = kleinSigma * g) : g * g = 1 := by
  have key : ∀ p : Equiv.Perm (Fin 5), p * (Equiv.swap 0 1 * Equiv.swap 2 3) =
      (Equiv.swap 0 1 * Equiv.swap 2 3) * p → Equiv.Perm.sign p = 1 → p * p = 1 := by
    decide +kernel
  exact Subtype.ext (key g.1 (congrArg Subtype.val hg) (Equiv.Perm.mem_alternatingGroup.1 g.2))

theorem kleinTau_comm : kleinTau * kleinSigma = kleinSigma * kleinTau := by
  apply Subtype.ext
  change (Equiv.swap 0 2 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 2 3) =
    (Equiv.swap 0 1 * Equiv.swap 2 3) * (Equiv.swap 0 2 * Equiv.swap 1 3)
  decide +kernel

theorem IsDelta5Ext.exists_class_three {K : Type*} [Group K] {V : Subgroup K}
    (h : IsDelta5Ext K V) :
    ∃ H : Subgroup K, IsPGroup 2 H ∧ ∃ x ∈ H, ∃ y ∈ H, ∃ z ∈ H, ⁅⁅x, y⁆, z⁆ ≠ 1 := by
  obtain ⟨α, hα, hαk, β, hβ, hequiv⟩ := h
  have hVn : V.Normal := hαk ▸ α.normal_ker
  let c : ↥V → Fin 5 → ZMod 2 := fun u i =>
    ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) i
  have c_mul : ∀ u u' : ↥V, c (u * u') = c u + c u' := by
    intro u u'
    funext i
    simp [c, map_mul]
  have c_inv : ∀ u : ↥V, c u⁻¹ = c u := by
    intro u
    funext i
    simp [c, map_inv]
  have c_one : c 1 = 0 := by
    funext i
    simp [c]
  have c_inj : ∀ u : ↥V, c u = 0 → u = 1 := by
    intro u hu
    apply hβ.1
    rw [map_one]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    simpa [c] using congrFun hu i
  have c_conj : ∀ (ℓ : K) (u : ↥V) (hu : ℓ * (u : K) * ℓ⁻¹ ∈ V) (i : Fin 5),
      c ⟨ℓ * (u : K) * ℓ⁻¹, hu⟩ i =
        c u (((α ℓ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) :=
    fun ℓ u hu i => hequiv ℓ u ⟨_, hu⟩ rfl i
  obtain ⟨t, ht⟩ := hα kleinSigma
  obtain ⟨t', ht'⟩ := hα kleinTau
  let e : evenWeight 5 :=
    ⟨fun i => if i = 0 ∨ i = 4 then 1 else 0, by simp [evenWeight]; decide⟩
  obtain ⟨v, hv⟩ := hβ.2 (Multiplicative.ofAdd e)
  have cv : ∀ i, c v i = if i = 0 ∨ i = 4 then 1 else 0 := by
    intro i
    simp [c, hv, e]
  let v1 : ↥V := ⟨t' * (v : K) * t'⁻¹, hVn.conj_mem _ v.2 t'⟩
  let w : ↥V := v1 * v⁻¹
  let w1 : ↥V := ⟨t * (w : K) * t⁻¹, hVn.conj_mem _ w.2 t⟩
  let z : ↥V := w1 * w⁻¹
  have hσ : ((α t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ 0 = 1 := by
    rw [ht]; decide
  have hτ0 : ((α t' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ 0 = 2 := by
    rw [ht']; decide
  have hτ1 : ((α t' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ 1 = 3 := by
    rw [ht']; decide
  have cv1 : ∀ i, c v1 i = c v (((α t' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) :=
    fun i => c_conj t' v _ i
  have cw : ∀ i, c w i = c v (((α t' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) +
      c v i := by
    intro i
    simp only [w, c_mul, c_inv, Pi.add_apply, cv1]
  have cw1 : ∀ i, c w1 i = c w (((α t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) :=
    fun i => c_conj t w _ i
  have hz0 : c z 0 = 1 := by
    have : c z 0 =
        c w ((((α t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹) 0) + c w 0 := by
      simp only [z, c_mul, c_inv, Pi.add_apply, cw1]
    rw [this, hσ, cw, cw, hτ1, hτ0, cv, cv, cv, cv]
    decide
  have hz : z ≠ 1 := by
    intro h1
    have := congrFun (c_one ▸ congrArg c h1) 0
    rw [hz0] at this
    exact one_ne_zero this
  have hsq : ∀ k : K, α k * kleinSigma = kleinSigma * α k → k ^ (2 ^ 2) = 1 := by
    intro k hk
    have h2 : α (k ^ 2) = 1 := by
      rw [map_pow, pow_two]
      exact sq_eq_one_of_comm_kleinSigma _ hk
    have hk2 : k ^ 2 ∈ V := by rw [← hαk]; exact h2
    have h3 : (⟨k ^ 2, hk2⟩ : ↥V) * ⟨k ^ 2, hk2⟩ = 1 := by
      apply c_inj
      rw [c_mul]
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h4
    rw [show k ^ (2 ^ 2) = k ^ 2 * k ^ 2 by rw [← pow_add]; norm_num]
    exact h4
  have hcomm : ∀ k : K,
      α k ∈ Subgroup.centralizer ({kleinSigma} : Set (alternatingGroup (Fin 5))) →
      α k * kleinSigma = kleinSigma * α k := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hk kleinSigma rfl).symm
  refine ⟨Subgroup.comap α (Subgroup.centralizer ({kleinSigma} : Set (alternatingGroup (Fin 5)))),
    ?_, t', ?_, v, ?_, t, ?_, ?_⟩
  · intro k
    exact ⟨2, Subtype.ext (hsq k (hcomm k k.2))⟩
  · rw [Subgroup.mem_comap, ht']
    exact Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]; exact kleinTau_comm.symm
  · rw [Subgroup.mem_comap]
    have : α (v : K) = 1 := by rw [← MonoidHom.mem_ker, hαk]; exact v.2
    rw [this]
    exact one_mem _
  · rw [Subgroup.mem_comap, ht]
    exact Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
  · intro h1
    apply hz
    have hz' : (z : K) = ⁅⁅t', (v : K)⁆, t⁆⁻¹ := by
      simp only [z, w1, w, v1, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    apply Subtype.ext
    rw [hz', h1]
    simp

@[expose] def TwoGroupsClassTwo (S : Type*) [Group S] : Prop :=
  ∀ H : Subgroup S, IsPGroup 2 H → ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ⁅⁅x, y⁆, z⁆ = 1

theorem TwoGroupsClassTwo.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : TwoGroupsClassTwo S') : TwoGroupsClassTwo S := by
  intro H hH x hx y hy z hz
  apply e.injective
  rw [map_one, map_commutatorElement, map_commutatorElement]
  exact h (H.map e.toMonoidHom) (hH.map e.toMonoidHom) _ (Subgroup.mem_map_of_mem _ hx) _
    (Subgroup.mem_map_of_mem _ hy) _ (Subgroup.mem_map_of_mem _ hz)

theorem TwoGroupsClassTwo.of_sylow {S : Type*} [Group S] [Finite S] (Q : Sylow 2 S)
    (hQ : ∀ x ∈ (Q : Subgroup S), ∀ y ∈ (Q : Subgroup S), ∀ z ∈ (Q : Subgroup S),
      ⁅⁅x, y⁆, z⁆ = 1) : TwoGroupsClassTwo S := by
  intro H hH x hx y hy z hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₁, hHQ₁⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q Q₁
  have hmem : ∀ x ∈ (Q₁ : Subgroup S), ∃ q ∈ (Q : Subgroup S), x = MulAut.conj g q := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hmem x (hHQ₁ hx)
  obtain ⟨b, hb, rfl⟩ := hmem y (hHQ₁ hy)
  obtain ⟨c, hc, rfl⟩ := hmem z (hHQ₁ hz)
  rw [← map_commutatorElement, ← map_commutatorElement, hQ a ha b hb c hc, map_one]

theorem A5Config.false_of_classTwo {S : Type} [Group S] (hS : TwoGroupsClassTwo S)
    (h : A5Config S) : False := by
  obtain ⟨K, V, T₁, T₂, hVK, hV16, hel, hΔ, -⟩ := h
  obtain ⟨H, hH, x, hx, y, hy, z, hz, hne⟩ := hΔ.exists_class_three
  have h1 := hS (H.map K.subtype) (hH.map K.subtype) _ (Subgroup.mem_map_of_mem _ hx) _
    (Subgroup.mem_map_of_mem _ hy) _ (Subgroup.mem_map_of_mem _ hz)
  apply hne
  apply K.subtype_injective
  rw [map_one, map_commutatorElement, map_commutatorElement]
  exact h1

end CFSG.Quasithin.H13.CTK
