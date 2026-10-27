module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EI

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6

variable {A : Type} [Group A]

variable [Finite A] {K : Subgroup A} [K.Normal]

theorem model_sp4_one_ext {S B E : Subgroup A} (hS : IsSylowTwoOf S ⊤)
    (hC : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) (hAlt : IsAlt 6 ↥K) (hKS : K ⊔ S = ⊤)
    (hdiag : ∀ P : Subgroup A, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) ≤ P →
        ¬ S ≤ Subgroup.normalizer (P : Set A))
    (hBorel : ∃ S₀ : Subgroup A, IsSylowTwoOf S₀ K ∧
      B ⊓ K = K ⊓ Subgroup.normalizer (S₀ : Set A))
    (hSB : S ≤ B) (hES : E ≤ S) (hSE : S ≤ Subgroup.normalizer (E : Set A))
    (hE2 : ∀ x ∈ E, x * x = 1) (hE4 : 4 ≤ Nat.card E) :
    (∃ σ : ↥(K ⊔ E) ≃* Equiv.Perm (Fin 6),
        ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map σ.toMonoidHom = S06 ∧
          (E.subgroupOf (K ⊔ E)).map σ.toMonoidHom = Z6) ∧
    (K ⊔ E).Normal ∧
      ∃ x ∈ K, K ⊔ E = E ⊔ CFSG.conjugate E x ∧ B ⊓ (K ⊔ E) = S ⊓ (K ⊔ E) ∧
        IsSylowTwoOf (S ⊓ (K ⊔ E)) (K ⊔ E) ∧ Nat.card E ≤ 4 ∧
        ∀ N : Subgroup A, N ≤ K ⊔ E → IsPGroup 2 N → (N.subgroupOf (K ⊔ E)).Normal → N = ⊥ := by
  have hSK : IsSylowTwoOf (S ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hS le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨e, he⟩ := exists_equiv_D0 hSK hAlt
  obtain ⟨t, htS, -, hRa, hRb⟩ := exists_swap hS e he hdiag
  have hEK := map_inf_le e he htS ⟨hRa, hRb⟩ hES hSE hE2
  have hEK2 : Nat.card ↥(E ⊓ K) ≤ 2 := by
    calc Nat.card ↥(E ⊓ K) = Nat.card ↥(((E ⊓ K).subgroupOf K).map e.toMonoidHom) := by
          rw [Subgroup.card_map_of_injective e.injective,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      _ ≤ Nat.card ↥(Ra ⊓ Rb) := Subgroup.card_le_of_le hEK
      _ ≤ 2 := card_Ra_inf_Rb_le
  obtain ⟨v₀, hv₀, hv₀K⟩ : ∃ v₀ ∈ E, v₀ ∉ K := by
    by_contra h
    push Not at h
    rw [inf_eq_left.2 h] at hEK2
    omega
  obtain ⟨χ, hχ⟩ := exists_chi hS.2.1 hC e he hEK hSE hE2 hv₀ hv₀K
  have hFn : (K ⊔ E).Normal := by
    have hle : K ⊔ S ≤ Subgroup.normalizer ((K ⊔ E : Subgroup A) : Set A) := by
      refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun s hs => ?_
      refine mem_normalizer_sup ?_ (hSE hs)
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top _
    rw [hKS] at hle
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
  have hSF := map_SF hχ he (hES hv₀) ((le_sup_right : E ≤ K ⊔ E) hv₀) hv₀K
  obtain ⟨S₀, hS₀, hB⟩ := hBorel
  have hBK0 := P5.inf_normalizer_eq_of_borel hSK hS₀ hB
    (le_inf (inf_le_left.trans hSB) inf_le_right)
  have hNSK : K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) = S ⊓ K := by
    rw [← map_subtype_normalizer inf_le_right]
    have h1 : Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K) =
        (S ⊓ K).subgroupOf K := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_equiv_normalizer_eq, he, normalizer_U6]
    rw [h1, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hBF := inf_eq_of_inf_eq hχ he (hBK0.trans hNSK) hSB hSF
  have hEZ := map_E_eq (S := S) hχ hSF htS ⟨hRa, hRb⟩ hES hSE hE2 hE4
  refine ⟨⟨χ, hSF, hEZ⟩, hFn, ((χ.symm x0 : ↥(K ⊔ E)) : A), mem_K_of_mem hχ (by
      rw [MulEquiv.apply_symm_apply]
      exact x0_mem), sup_eq hEZ, hBF,
    A4.isSylowTwoOf_inf_normal hS le_top (Subgroup.normalizer_eq_top_iff.mpr hFn).ge, ?_,
    fun N hNF hN2 hNn => eq_bot_of_normal hC e hNF hN2 hNn⟩
  calc Nat.card E = Nat.card ↥((E.subgroupOf (K ⊔ E)).map χ.toMonoidHom) := by
        rw [Subgroup.card_map_of_injective χ.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : E ≤ K ⊔ E)).toEquiv]
    _ ≤ 4 := hEZ ▸ card_Z6_le

end CFSG.Quasithin.Ch3E213M.P6E
