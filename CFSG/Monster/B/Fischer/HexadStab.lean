module

public import CFSG.Monster.B.Fischer.HexadCode
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.Fischer.HexadCode
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.Fischer.HexadStabInputs
public import Certificates.Certificate3030
public import Certificates.Certificate3029

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.Classical.Plane
  CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu CFSG.Monster.B.TwoA.Census

@[expose] def B₀ : Finset (Fin 24) := {2, 3, 4, 5, 6, 7}

theorem B₀_eq_ofMask : B₀ = ofMask 252 := by decide

theorem B₀_mem_ℬ₀ : B₀ ∈ ℬ₀ := by
  rw [ℬ₀_eq, ℬ₀list, List.mem_toFinset, B₀_eq_ofMask]
  exact List.mem_map_of_mem (by decide)

theorem B₀_subset_X₀ : B₀ ⊆ X₀ := (block_spec B₀_mem_ℬ₀).1

@[expose] def KB : Subgroup CFSG.Blueprint.NativeSporadic.M22 where
  carrier := {k | B₀.map (psiHom k).toEmbedding = B₀}
  mul_mem' {k l} hk hl := by
    change B₀.map (psiHom (k * l : CFSG.Blueprint.NativeSporadic.M22)).toEmbedding = B₀
    rw [Subgroup.coe_mul, map_mul, map_perm_mul, hl, hk]
  one_mem' := by
    change B₀.map (psiHom (1 : CFSG.Blueprint.NativeSporadic.M22)).toEmbedding = B₀
    rw [Subgroup.coe_one, map_one, map_perm_one]
  inv_mem' {k} hk := by
    change B₀.map (psiHom (k⁻¹ : CFSG.Blueprint.NativeSporadic.M22)).toEmbedding = B₀
    change B₀.map (psiHom k).toEmbedding = B₀ at hk
    conv_lhs => rw [← hk]
    rw [← map_perm_mul, Subgroup.coe_inv, map_inv, inv_mul_cancel, map_perm_one]

theorem mem_KB {k : CFSG.Blueprint.NativeSporadic.M22} :
    k ∈ KB ↔ B₀.map (psiHom k).toEmbedding = B₀ := Iff.rfl

@[expose] def letterM22 (z : ℤ) : CFSG.Blueprint.NativeSporadic.M22 :=
  if z = 1 then m22a else if z = -1 then m22a⁻¹ else if z = 2 then m22b else m22b⁻¹

@[expose] def wordM22 (w : List ℤ) : CFSG.Blueprint.NativeSporadic.M22 :=
  (w.map letterM22).prod

@[expose] def g₁ : CFSG.Blueprint.NativeSporadic.M22 := wordM22 [-1, 2, 2, 1]

@[expose] def g₂ : CFSG.Blueprint.NativeSporadic.M22 :=
  wordM22 [-2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2]

@[expose] def g₃ : CFSG.Blueprint.NativeSporadic.M22 := wordM22 [-2, -1, -2, -1, 2, 2, 1, 2, 1, 2]

theorem g₁_eq : g₁ = m22a⁻¹ * m22b ^ 2 * m22a := by
  simp [g₁, wordM22, letterM22, pow_two, mul_assoc]

theorem g₂_eq : g₂ = (m22b⁻¹ * m22a⁻¹) ^ 2 * m22b⁻¹ * (m22a * m22b) ^ 3 := by
  simp [g₂, wordM22, letterM22, pow_succ, mul_assoc]

theorem g₃_eq : g₃ = (m22b⁻¹ * m22a⁻¹) ^ 2 * m22b ^ 2 * (m22a * m22b) ^ 2 := by
  simp [g₃, wordM22, letterM22, pow_succ, mul_assoc]

@[expose] def genG₁ (t : ℕ) : ℕ :=
  [4, 5, 2, 3, 0, 1, 11, 10, 9, 8, 7, 6, 13, 12, 14, 15, 20, 21, 18, 19, 16, 17].getD t 0

@[expose] def genG₂ (t : ℕ) : ℕ :=
  [0, 1, 5, 4, 3, 2, 9, 8, 7, 6, 10, 11, 12, 13, 16, 17, 14, 15, 19, 18, 21, 20].getD t 0

@[expose] def genG₃ (t : ℕ) : ℕ :=
  [5, 1, 3, 2, 4, 0, 10, 7, 18, 15, 6, 11, 14, 19, 12, 9, 20, 17, 8, 13, 16, 21].getD t 0

theorem genG₁_spec : ∀ t : Fin 22, ((psiHom g₁ (coordAt t : Fin 24)) : ℕ) = genG₁ t + 2 := by
  decide +kernel

theorem genG₂_spec : ∀ t : Fin 22, ((psiHom g₂ (coordAt t : Fin 24)) : ℕ) = genG₂ t + 2 := by
  decide +kernel

theorem genG₃_spec : ∀ t : Fin 22, ((psiHom g₃ (coordAt t : Fin 24)) : ℕ) = genG₃ t + 2 := by
  decide +kernel

theorem genG₁_lt : ∀ t : Fin 22, genG₁ t < 22 := by decide

theorem genG₂_lt : ∀ t : Fin 22, genG₂ t < 22 := by decide

theorem genG₃_lt : ∀ t : Fin 22, genG₃ t < 22 := by decide

theorem g₁_mem_KB : g₁ ∈ KB := by
  rw [mem_KB]
  decide +kernel

theorem g₂_mem_KB : g₂ ∈ KB := by
  rw [mem_KB]
  decide +kernel

theorem g₃_mem_KB : g₃ ∈ KB := by
  rw [mem_KB]
  decide +kernel

@[expose, instance_reducible] noncomputable def vecAct :
    MulAction CFSG.Blueprint.NativeSporadic.M22 V₀ where
  smul g v := rho₀ g v
  one_smul v := by
    change rho₀ 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change rho₀ (g * h) v = rho₀ g (rho₀ h v)
    rw [map_mul]
    rfl

attribute [local instance] vecAct

@[expose] def genAB (k : ℕ) : CFSG.Blueprint.NativeSporadic.M22 := if k = 0 then m22a else m22b

theorem blockCert_ok :
    natCertOK actAB 2 (fun m => decide (m < 2 ^ 22)) 63 blockCert = true :=
  Certificates.certificate3030

theorem blockCert_size : blockCert.pts.size = 77 := rfl

theorem actAB_spec : ∀ k < 2, ∀ m, decide (m < 2 ^ 22) = true →
    vecOf (actAB k m) = genAB k • vecOf m := by
  intro k hk m _
  change vecOf (actAB k m) = rho₀ (genAB k) (vecOf m)
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact (rho₀_a_vecOf m).symm
  · exact (rho₀_b_vecOf m).symm

theorem closure_genAB :
    Subgroup.closure (genAB '' {k | k < 2}) = (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.M22) := by
  have : genAB '' {k | k < 2} = {m22a, m22b} := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
  rw [this]
  exact closure_pair_eq_top m22_eq _ _

theorem orbit_closure_eq {G X : Type*} [Group G] [MulAction G X] {S : Set G}
    (hS : Subgroup.closure S = ⊤) (x : X) :
    MulAction.orbit (Subgroup.closure S) x = MulAction.orbit G x := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, hS ▸ Subgroup.mem_top g⟩, rfl⟩

theorem ncard_orbit_block :
    (MulAction.orbit CFSG.Blueprint.NativeSporadic.M22 (vecOf 63)).ncard = 77 := by
  have h := ncard_orbit_of_natCertOK (G := CFSG.Blueprint.NativeSporadic.M22) (X := V₀)
    (dec := vecOf) (gens := genAB) blockCert_ok actAB_spec
    (fun a b ha hb e => vecOf_inj (of_decide_eq_true ha) (of_decide_eq_true hb) e)
  rw [orbit_closure_eq closure_genAB] at h
  rw [h, blockCert_size]

theorem vecOf_63 : vecOf 63 = blockVec B₀ := by
  rw [B₀_eq_ofMask, blockVec_ofMask]
  rfl

theorem blockVec_inj {B B' : Finset (Fin 24)} (hB : B ⊆ X₀) (hB' : B' ⊆ X₀)
    (h : blockVec B = blockVec B') : B = B' := by
  ext i
  by_cases hi : i ∈ X₀
  · have := congrFun h ⟨i, hi⟩
    rw [blockVec_apply, blockVec_apply] at this
    by_cases h1 : i ∈ B <;> by_cases h2 : i ∈ B' <;> simp_all
  · exact iff_of_false (fun h => hi (hB h)) (fun h => hi (hB' h))

theorem map_psiHom_subset_X₀ (g : Equiv.Perm (Fin 22)) {B : Finset (Fin 24)} (hB : B ⊆ X₀) :
    B.map (psiHom g).toEmbedding ⊆ X₀ := by
  intro i hi
  rw [Finset.mem_map_equiv] at hi
  have := hB hi
  rwa [← psiHom_mem_X₀ g, Equiv.apply_symm_apply] at this

theorem stabilizer_eq_KB :
    MulAction.stabilizer CFSG.Blueprint.NativeSporadic.M22 (vecOf 63) = KB := by
  ext k
  rw [MulAction.mem_stabilizer_iff, mem_KB]
  change rho₀ k (vecOf 63) = vecOf 63 ↔ _
  rw [vecOf_63, rho₀_apply, permRep_blockVec]
  exact ⟨blockVec_inj (map_psiHom_subset_X₀ _ B₀_subset_X₀) B₀_subset_X₀,
    fun h => by rw [h]⟩

theorem natCard_KB :
    Nat.card KB = 5760 := by
  have h := (MulAction.stabilizer CFSG.Blueprint.NativeSporadic.M22 (vecOf 63)).card_mul_index
  rw [MulAction.index_stabilizer, ncard_orbit_block, card_M22, stabilizer_eq_KB] at h
  omega

end CFSG.Monster.B.Fischer
