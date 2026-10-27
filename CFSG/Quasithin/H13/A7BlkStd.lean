module

public import CFSG.Quasithin.H13.A7BlkOff

public section

namespace CFSG.Quasithin.H13.A7Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

theorem permWeight_mul (σ τ : Perm (Fin 7)) (x : ↥(evenWeight 7)) :
    permWeight 7 (σ * τ) x = permWeight 7 σ (permWeight 7 τ x) := by
  apply Subtype.ext
  funext i
  show (x : Fin 7 → ZMod 2) ((σ * τ)⁻¹ i) = (x : Fin 7 → ZMod 2) (τ⁻¹ (σ⁻¹ i))
  rw [mul_inv_rev, Perm.mul_apply]

theorem permWeight_one (x : ↥(evenWeight 7)) : permWeight 7 1 x = x := rfl

theorem pwHom_bijective (σ : Perm (Fin 7)) : Function.Bijective (pwHom σ) := by
  refine ⟨fun x y h => ?_, fun y => ⟨permWeight 7 σ⁻¹ y, ?_⟩⟩
  · have h' := congrArg (permWeight 7 σ⁻¹) h
    change permWeight 7 σ⁻¹ (permWeight 7 σ x) = permWeight 7 σ⁻¹ (permWeight 7 σ y) at h'
    rwa [← permWeight_mul, ← permWeight_mul, inv_mul_cancel, permWeight_one, permWeight_one] at h'
  · change permWeight 7 σ (permWeight 7 σ⁻¹ y) = y
    rw [← permWeight_mul, mul_inv_cancel, permWeight_one]

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] noncomputable def AltData.conj (D : AltData K) (π : alternatingGroup (Fin 7)) :
    AltData K where
  α := (MulAut.conj π).toMonoidHom.comp D.α
  surj := (MulAut.conj π).surjective.comp D.surj
  ker := by
    rw [← D.ker]
    ext k
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (MulEquiv.map_eq_one_iff _)
  β := (AddMonoidHom.toMultiplicative (pwHom (π : Perm (Fin 7)))).comp D.β
  βsurj := (pwHom_bijective _).2.comp D.βsurj
  βker := by
    rw [← D.βker]
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      apply Multiplicative.toAdd.injective
      apply (pwHom_bijective (π : Perm (Fin 7))).1
      rw [toAdd_one, map_zero]
      exact congrArg Multiplicative.toAdd h
    · intro h
      rw [h]
      rfl
  βeq ℓ u v huv := by
    have h := D.βeq ℓ u v huv
    show permWeight 7 π (Multiplicative.toAdd (D.β v)) =
      permWeight 7 ((π : Perm (Fin 7)) * (D.α ℓ : Perm (Fin 7)) * (π : Perm (Fin 7))⁻¹)
        (permWeight 7 π (Multiplicative.toAdd (D.β u)))
    rw [h, ← permWeight_mul, ← permWeight_mul, inv_mul_cancel_right]

theorem AltData.conj_α (D : AltData K) (π : alternatingGroup (Fin 7)) (k : ↥K) :
    ((D.conj π).α k : Perm (Fin 7)) =
      (π : Perm (Fin 7)) * (D.α k : Perm (Fin 7)) * (π : Perm (Fin 7))⁻¹ := rfl

theorem card_alternatingGroup_pstd :
    Nat.card ↥(pstd.subgroupOf (alternatingGroup (Fin 7))) = 8 := by
  rw [← card_pstd]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe pstd_le_alternatingGroup).toEquiv

variable [Finite G]

theorem exists_stdPos (D₀ : AltData K) {T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) (hT : IsPGroup 2 T)
    (hsyl : IsSylowTwoOf (T ⊓ K) K) : ∃ D : AltData K, StdPos D T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup (alternatingGroup (Fin 7)) := ((T ⊓ K).subgroupOf K).map D₀.α with hP₀
  have hP₀2 : IsPGroup 2 P₀ :=
    (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
  have hP₀i : ¬ 2 ∣ P₀.index := fun h =>
    hsyl.2.2 (h.trans (Subgroup.index_map_dvd _ D₀.surj))
  set P₁ : Subgroup (alternatingGroup (Fin 7)) := pstd.subgroupOf (alternatingGroup (Fin 7))
    with hP₁
  have hP₁2 : IsPGroup 2 P₁ :=
    IsPGroup.of_card (n := 3) (by rw [card_alternatingGroup_pstd]; norm_num)
  have hP₁i : ¬ 2 ∣ P₁.index := by
    have h := Subgroup.index_mul_card P₁
    rw [card_alternatingGroup_pstd, card_alternatingGroup_seven] at h
    have h315 : P₁.index = 315 := by omega
    rw [h315]
    decide
  obtain ⟨π, hπ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hP₀2.toSylow hP₀i)
    (hP₁2.toSylow hP₁i)
  have hπ' : P₀.map (MulAut.conj π).toMonoidHom = P₁ := by
    have h := congrArg (fun S : Sylow 2 (alternatingGroup (Fin 7)) =>
      (S : Subgroup (alternatingGroup (Fin 7)))) hπ
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
    rw [Subgroup.pointwise_smul_def] at h
    exact h
  refine ⟨D₀.conj π, hTN, hT, ?_, ?_⟩
  · intro σ hσ
    have h1 : (⟨σ, pstd_le_alternatingGroup hσ⟩ : alternatingGroup (Fin 7)) ∈ P₁ := hσ
    rw [← hπ'] at h1
    obtain ⟨a, ha, hae⟩ := h1
    obtain ⟨k, hk, rfl⟩ := ha
    refine ⟨k, (Subgroup.mem_subgroupOf.mp hk).1, ?_⟩
    have := congrArg Subtype.val hae
    exact this
  · intro k hk
    have h1 : D₀.α k = 1 := by
      have h2 : (MulAut.conj π) (D₀.α k) = 1 := hk
      exact (MulEquiv.map_eq_one_iff _).mp h2
    have h3 : (k : G) ∈ blockQ K := mem_blockQ_of_ker D₀ h1
    exact (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl h3).1

end CFSG.Quasithin.H13.A7Blk

end
