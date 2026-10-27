module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneEven
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneSub

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

namespace ThreeOne

private theorem card_subgroupOf_eq {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.card_map_of_injective H.subtype_injective (K := K.subgroupOf H),
    Subgroup.subgroupOf_map_subtype, inf_comm]

theorem overgroups_of_le_stabilizer {n : ℕ} (hn : 4 < n)
    {σ : Perm (Fin n)} (hσ : ∀ x, σ (σ x) = x) {α : Fin n} (hα : σ α = α)
    (hfix : ∀ x, x ≠ α → σ x ≠ x) {H T K : Subgroup (Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ H) (hT : IsSylowIn 2 T ⊤)
    (hTσ : T ≤ Subgroup.centralizer {σ}) (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K)
    (hKH : K ≤ H) (hKα : K ≤ MulAction.stabilizer (Perm (Fin n)) α) :
    K = H ⊓ Subgroup.centralizer {σ} ∨ K = H ⊓ MulAction.stabilizer (Perm (Fin n)) α ∨
      (Nonempty (↥H ≃* alternatingGroup (Fin 9)) ∧ IsE8L3 K) := by
  have hodd : Odd n := by
    have h := odd_card_of_apply_eq hσ hα hfix
    rwa [Fintype.card_fin] at h
  have hn_cases : n = 5 ∨ 7 ≤ n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hn_cases with hn5 | hn7
  · subst hn5
    have hTstab : T ≤ MulAction.stabilizer (Perm (Fin 5)) α := by
      intro t ht
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact apply_eq_of_mem_centralizer hα hfix (hTσ ht)
    have hUC : T ⊓ H ≤ H ⊓ Subgroup.centralizer {σ} :=
      le_inf inf_le_right (le_trans inf_le_left hTσ)
    have hUα : T ⊓ H ≤ H ⊓ MulAction.stabilizer (Perm (Fin 5)) α :=
      le_inf inf_le_right (le_trans inf_le_left hTstab)
    have hUK : T ⊓ H ≤ K := le_trans hUC hXK
    have hKHα : K ≤ H ⊓ MulAction.stabilizer (Perm (Fin 5)) α := le_inf hKH hKα
    have hcardT : Nat.card T = 8 := by
      have h := card_eq_of_isSylowIn_top hT (k := 3) (m := 15)
        (by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
        (by norm_num)
      simpa using h
    haveI : MulAction.IsPretransitive ↥H (Fin 5) := by
      apply MulAction.IsPretransitive.of_orbit (x₀ := α)
      intro y
      haveI : MulAction.IsPretransitive (alternatingGroup (Fin 5)) (Fin 5) :=
        alternatingGroup.isPretransitive_of_three_le_card (Fin 5)
          (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
      obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) α y
      refine ⟨⟨(a : Perm (Fin 5)), hA a.2⟩, ?_⟩
      simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using ha
    have hcard_stab : Nat.card ↥(H ⊓ MulAction.stabilizer (Perm (Fin 5)) α)
        = Nat.card ↥(MulAction.stabilizer ↥H α) := by
      rw [← MulAction.stabilizer_subgroupOf H α]
      exact (card_subgroupOf_eq H (MulAction.stabilizer (Perm (Fin 5)) α)).symm
    have hA5 : 5 * Nat.card ↥(H ⊓ MulAction.stabilizer (Perm (Fin 5)) α) = Nat.card H := by
      have hcard_idx := Subgroup.card_mul_index (H := MulAction.stabilizer ↥H α)
      have hidx : (MulAction.stabilizer ↥H α).index = 5 := by
        rw [MulAction.index_stabilizer_of_transitive (G := ↥H) (x := α),
          Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [hidx, ← hcard_stab] at hcard_idx
      rw [mul_comm] at hcard_idx
      exact hcard_idx
    have hcardHα : Nat.card ↥(H ⊓ MulAction.stabilizer (Perm (Fin 5)) α)
        = 3 * Nat.card ↥(T ⊓ H) := by
      rcases CFSG.ComponentClassification.SymmetricLocal.eq_alternatingGroup_or_eq_top hA with
        hHA | hHtop
      · have hcardU : Nat.card ↥(T ⊓ H) = 4 := by
          have h := two_mul_card_inf_alternatingGroup (T := T) hT
            (show 2 ≤ Fintype.card (Fin 5) by norm_num)
          rw [← hHA] at h
          rw [hcardT] at h
          omega
        have hcardH : Nat.card H = 60 := by
          rw [hHA, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
          norm_num
        omega
      · have hcardU : Nat.card ↥(T ⊓ H) = 8 := by
          rw [hHtop, inf_top_eq, hcardT]
        have hcardH : Nat.card H = 120 := by
          rw [hHtop, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card,
            Fintype.card_fin]
          norm_num
        omega
    have h3 : (T ⊓ H).relIndex (H ⊓ MulAction.stabilizer (Perm (Fin 5)) α) = 3 := by
      have h := Subgroup.relIndex_mul_card (H := T ⊓ H)
        (K := H ⊓ MulAction.stabilizer (Perm (Fin 5)) α)
      rw [inf_eq_left.mpr hUα] at h
      rw [hcardHα] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
    have hprod : (T ⊓ H).relIndex K
        * K.relIndex (H ⊓ MulAction.stabilizer (Perm (Fin 5)) α) = 3 := by
      have h := Subgroup.relIndex_mul_relIndex (H := T ⊓ H) (K := K)
        (L := H ⊓ MulAction.stabilizer (Perm (Fin 5)) α) hUK hKHα
      rwa [h3] at h
    have hdvd : (T ⊓ H).relIndex K ∣ 3 :=
      ⟨K.relIndex (H ⊓ MulAction.stabilizer (Perm (Fin 5)) α), hprod.symm⟩
    have hcases : (T ⊓ H).relIndex K = 1 ∨ (T ⊓ H).relIndex K = 3 :=
      Nat.prime_three.eq_one_or_self_of_dvd _ hdvd
    rcases hcases with hone | hthree
    · left
      have hKU : K = T ⊓ H := le_antisymm (Subgroup.relIndex_eq_one.mp hone) hUK
      rw [hKU] at hXK ⊢
      exact le_antisymm hUC hXK
    · right; left
      have hb : K.relIndex (H ⊓ MulAction.stabilizer (Perm (Fin 5)) α) = 1 := by
        have h := hprod
        rw [hthree] at h
        omega
      exact le_antisymm hKHα (Subgroup.relIndex_eq_one.mp hb)
  ·
    obtain ⟨σ', hσ'eq⟩ := exists_ofSubtype_eq (α := α) hα
    have hcardΩ' : Fintype.card {x : Fin n // x ≠ α} = n - 1 := by
      rw [card_subtype_ne (α := α), Fintype.card_fin]
    have h6 : 6 ≤ Fintype.card {x : Fin n // x ≠ α} := by omega
    have hσ'inv : ∀ x, σ' (σ' x) = x := by
      intro x
      apply Subtype.val_injective
      have h1 : ((σ' (σ' x)) : Fin n) = σ ((σ' x : {y : Fin n // y ≠ α}) : Fin n) := by
        have h := congrArg (fun f : Perm (Fin n) =>
          f ((σ' x : {y : Fin n // y ≠ α}) : Fin n)) hσ'eq
        rwa [Perm.ofSubtype_apply_of_mem σ' (σ' x).2] at h
      have h2 : ((σ' x : {y : Fin n // y ≠ α}) : Fin n) = σ (x : Fin n) := by
        have h := congrArg (fun f : Perm (Fin n) => f (x : Fin n)) hσ'eq
        rwa [Perm.ofSubtype_apply_of_mem σ' x.2] at h
      rw [h1, h2]
      exact hσ (x : Fin n)
    have hfix' : ∀ x : {x : Fin n // x ≠ α}, σ' x ≠ x := by
      intro x hx
      have hx' : σ (x : Fin n) = (x : Fin n) := by
        rw [← hσ'eq, Perm.ofSubtype_apply_of_mem σ' x.2]
        exact congrArg Subtype.val hx
      exact hfix (x : Fin n) x.2 hx'
    have hodd' : Odd (Fintype.card (Fin n)) := by rwa [Fintype.card_fin]
    have hTα : T ≤ MulAction.stabilizer (Perm (Fin n)) α := by
      intro t ht
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact apply_eq_of_mem_centralizer hα hfix (hTσ ht)
    have hA' : alternatingGroup {x : Fin n // x ≠ α}
        ≤ H.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n)) :=
      alternatingGroup_le_comap_ofSubtype (α := α) hA
    have hT' : IsSylowIn 2
        (T.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n))) ⊤ :=
      isSylowIn_comap_ofSubtype (α := α) hT hTα hodd'
    have hTσ' : T.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n))
        ≤ Subgroup.centralizer {σ'} := by
      rw [← comap_centralizer_ofSubtype (α := α) σ']
      exact Subgroup.comap_mono (by rw [hσ'eq]; exact hTσ)
    have hXK' : H.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n)) ⊓
          Subgroup.centralizer {σ'}
        ≤ K.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n)) := by
      rw [← comap_centralizer_ofSubtype (α := α) σ', ← Subgroup.comap_inf]
      exact Subgroup.comap_mono (by rw [hσ'eq]; exact hXK)
    have hKH' : K.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n))
        ≤ H.comap (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n)) :=
      Subgroup.comap_mono hKH
    have hres := overgroups_of_forall_apply_ne (Ω := {x : Fin n // x ≠ α})
      h6 hσ'inv hfix' hA' hT' hTσ' hXK' hKH'
    rcases hres with hK' | hK' | ⟨hcard8, hH'alt, hE8'⟩
    · right; left
      rw [← map_comap_ofSubtype_eq (α := α) hKα, hK', map_comap_ofSubtype_eq_inf (α := α) H]
    · left
      apply le_antisymm
      · refine le_inf hKH ?_
        intro k hk
        have hkmem : k ∈ (K.comap
            (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n))).map
            (Perm.ofSubtype : Perm {x : Fin n // x ≠ α} →* Perm (Fin n)) := by
          rw [map_comap_ofSubtype_eq (α := α) hKα]
          exact hk
        obtain ⟨k', hk'K, hk'eq⟩ := Subgroup.mem_map.mp hkmem
        have hk'C : k' ∈ Subgroup.centralizer {σ'} := by
          rw [hK'] at hk'K
          exact (Subgroup.mem_inf.mp hk'K).2
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hk'eq, ← hσ'eq, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp hk'C]
      · exact hXK
    · right; right
      have hn9 : n = 9 := by
        have := hcard8
        rw [hcardΩ'] at this
        omega
      have hHalt : H = alternatingGroup (Fin n) :=
        eq_alternatingGroup_of_comap_ofSubtype_eq (α := α)
          (by rw [Fintype.card_fin]; omega) hA hH'alt
      subst hn9
      refine ⟨⟨MulEquiv.subgroupCongr hHalt⟩, ?_⟩
      rw [← map_comap_ofSubtype_eq (α := α) hKα]
      exact IsE8L3.map hE8' _ Perm.ofSubtype_injective

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
