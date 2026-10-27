module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelPar
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Root

public noncomputable section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair

section Generic

variable {X : Type*} [Group X]

theorem eq_iSup_of_coe_eq_chainProd (A : ℤ → Subgroup X) (l : List ℤ) (P : Subgroup X)
    (hP : (P : Set X) = chainProd A l) : P = ⨆ k ∈ l, A k := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ chainProd A l := by
      rw [← hP]
      exact hx
    exact chainProd_subset A (⨆ k ∈ l, A k) l (fun k hk => le_iSup₂_of_le k hk le_rfl) hx'
  · refine iSup₂_le fun k hk x hx => ?_
    have : x ∈ (P : Set X) := by
      rw [hP]
      exact mem_chainProd_of_mem A hk hx
    exact this

variable {n : ℕ} (R : RankTwoSystem X n)

theorem Uplus_true_eq_iSup : Uplus R true = ⨆ k ∈ intList 2 (n : ℤ), R.root k :=
  eq_iSup_of_coe_eq_chainProd _ _ _ (coe_Uplus_true R)

theorem Uplus_false_eq_iSup : Uplus R false = ⨆ k ∈ intList 1 ((n : ℤ) - 1), R.root k :=
  eq_iSup_of_coe_eq_chainProd _ _ _ (coe_Uplus_false R)

end Generic

end CFSG.Quasithin.H13.F431.BN

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Quasithin.H13.F431.BN CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


variable {K : Type} [Field K]

theorem iSup_torus_eq_torusSub : (⨆ i, torus (τ := Tag.G2) K i) = torusSub Tag.G2 K := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (torusElt_mem_torusGroup i t)
  · intro x hx
    have hle : torusGroup Tag.G2 K ≤
        (⨆ i, torus (τ := Tag.G2) K i).map (adjointGroup Tag.G2 K).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, t⟩, rfl⟩
      exact ⟨torusElement Tag.G2 K i t, Subgroup.mem_iSup_of_mem i ⟨t, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_subgroupOf.1 hx)
    exact (Subtype.ext hyx : y = x) ▸ hy

theorem map_borelSub [Finite K] (hK : 3 ≤ Nat.card K) :
    (borelSub Tag.G2 K).map (mk K).toMonoidHom = (g2ModelSystem K hK).B := by
  rw [B_eq hK, iSup_torus_eq_torusSub, ← posUnipotentSub_eq, ← posUnipotentSub_sup_torusSub,
    sup_comm]
  rfl

theorem rootGroup_eq_Xe {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) :
    rootGroup (rootOperatorFamily Tag.G2) K γ = Xe K γ := by
  rw [rootGroup_of_isRoot hγ,
    ← (rootOperatorFamily Tag.G2).subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩]
  ext x
  rw [Subgroup.mem_subgroupOf, mem_rootSubgroup, mem_Xe_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

theorem root_eq_map_Xe (hK : 3 ≤ Nat.card K) {k : ℤ} (h0 : k ≠ 0) (h6 : k.natAbs ≤ 6) :
    (g2ModelSystem K hK).root k = (Xe K (hexPos k)).map (proj K) := by
  rw [g2ModelSystem_root]
  show (rootGroup (rootOperatorFamily Tag.G2) K (hexPos k)).map _ = _
  rw [rootGroup_eq_Xe (isRoot_hexPos h0 h6)]
  rfl

theorem map_Xr (hK : 3 ≤ Nat.card K) :
    (Xr K).map (proj K) = (g2ModelSystem K hK).root 1 := by
  rw [root_eq_map_Xe hK (by norm_num) (by norm_num)]
  have e : hexPos 1 = rR := by simp [hexPos, rR]
  rw [e]

theorem map_Xb (hK : 3 ≤ Nat.card K) :
    (Xb K).map (proj K) = (g2ModelSystem K hK).root 2 := by
  rw [root_eq_map_Xe hK (by norm_num) (by norm_num)]
  have e : hexPos 2 = rB := by simp [hexPos, rB]
  rw [e]

theorem map_Xv (hK : 3 ≤ Nat.card K) :
    (Xv K).map (proj K) = (g2ModelSystem K hK).root 3 := by
  rw [root_eq_map_Xe hK (by norm_num) (by norm_num)]
  have e : hexPos 3 = rV := by simp [hexPos, rV]
  rw [e]

theorem map_Xc (hK : 3 ≤ Nat.card K) :
    (Xc K).map (proj K) = (g2ModelSystem K hK).root 4 := by
  rw [root_eq_map_Xe hK (by norm_num) (by norm_num)]
  have e : hexPos 4 = rC := by simp [hexPos, rC]
  rw [e]

theorem map_Xu (hK : 3 ≤ Nat.card K) :
    (Xu K).map (proj K) = (g2ModelSystem K hK).root 5 := by
  rw [root_eq_map_Xe hK (by norm_num) (by norm_num)]
  have e : hexPos 5 = rU := by simp [hexPos, rU]
  rw [e]

theorem map_Xa (hK : 3 ≤ Nat.card K) :
    (Xa K).map (proj K) = (g2ModelSystem K hK).root 6 := by
  rw [root_eq_map_Xe hK (by norm_num) (by norm_num)]
  have e : hexPos 6 = rA := by simp [hexPos, rA]
  rw [e]

theorem Q_true_eq [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K) :
    Q (g2ModelSystem K hK) true = (Q1 K).map (mk K).toMonoidHom := by
  rw [Q_eq_Uplus _ (isSylowTwoOf_modelU hK) true, Uplus_true_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    obtain ⟨h2, h6⟩ := mem_intList_iff.1 hk
    have h6' : k ≤ 6 := by exact_mod_cast h6
    interval_cases k
    · rw [← map_Xb hK]
      exact Subgroup.map_mono Xb_le_Q1
    · rw [← map_Xv hK]
      exact Subgroup.map_mono Xv_le_Q1
    · rw [← map_Xc hK]
      exact Subgroup.map_mono Xc_le_Q1
    · rw [← map_Xu hK]
      exact Subgroup.map_mono Xu_le_Q1
    · rw [← map_Xa hK]
      exact Subgroup.map_mono Xa_le_Q1
  · show (Xa K ⊔ Xu K ⊔ Xv K ⊔ Xb K ⊔ Xc K).map (proj K) ≤ _
    simp only [Subgroup.map_sup]
    have hmem : ∀ k : ℤ, 2 ≤ k → k ≤ 6 → k ∈ intList 2 ((6 : ℕ) : ℤ) := fun k h1 h2 =>
      mem_intList_iff.2 ⟨h1, by exact_mod_cast h2⟩
    refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
    · rw [map_Xa hK]
      exact le_iSup₂_of_le 6 (hmem 6 (by norm_num) le_rfl) le_rfl
    · rw [map_Xu hK]
      exact le_iSup₂_of_le 5 (hmem 5 (by norm_num) (by norm_num)) le_rfl
    · rw [map_Xv hK]
      exact le_iSup₂_of_le 3 (hmem 3 (by norm_num) (by norm_num)) le_rfl
    · rw [map_Xb hK]
      exact le_iSup₂_of_le 2 (hmem 2 le_rfl (by norm_num)) le_rfl
    · rw [map_Xc hK]
      exact le_iSup₂_of_le 4 (hmem 4 (by norm_num) (by norm_num)) le_rfl

theorem Q_false_eq [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K) :
    Q (g2ModelSystem K hK) false = (Q2 K).map (mk K).toMonoidHom := by
  rw [Q_eq_Uplus _ (isSylowTwoOf_modelU hK) false, Uplus_false_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    obtain ⟨h1, h5⟩ := mem_intList_iff.1 hk
    have h5' : k ≤ 5 := by
      have : k ≤ ((6 : ℕ) : ℤ) - 1 := h5
      push_cast at this
      omega
    interval_cases k
    · rw [← map_Xr hK]
      exact Subgroup.map_mono Xr_le_Q2
    · rw [← map_Xb hK]
      exact Subgroup.map_mono Xb_le_Q2
    · rw [← map_Xv hK]
      exact Subgroup.map_mono Xv_le_Q2
    · rw [← map_Xc hK]
      exact Subgroup.map_mono Xc_le_Q2
    · rw [← map_Xu hK]
      exact Subgroup.map_mono Xu_le_Q2
  · show (Xr K ⊔ Xu K ⊔ Xv K ⊔ Xb K ⊔ Xc K).map (proj K) ≤ _
    simp only [Subgroup.map_sup]
    have hmem : ∀ k : ℤ, 1 ≤ k → k ≤ 5 → k ∈ intList 1 (((6 : ℕ) : ℤ) - 1) := fun k h1 h2 =>
      mem_intList_iff.2 ⟨h1, by push_cast; omega⟩
    refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
    · rw [map_Xr hK]
      exact le_iSup₂_of_le 1 (hmem 1 le_rfl (by norm_num)) le_rfl
    · rw [map_Xu hK]
      exact le_iSup₂_of_le 5 (hmem 5 (by norm_num) le_rfl) le_rfl
    · rw [map_Xv hK]
      exact le_iSup₂_of_le 3 (hmem 3 (by norm_num) (by norm_num)) le_rfl
    · rw [map_Xb hK]
      exact le_iSup₂_of_le 2 (hmem 2 (by norm_num) (by norm_num)) le_rfl
    · rw [map_Xc hK]
      exact le_iSup₂_of_le 4 (hmem 4 (by norm_num) (by norm_num)) le_rfl

theorem Pmin_one_inf_Pmin_zero [Finite K] (hK : 3 ≤ Nat.card K) :
    Pmin K ⟨1, by decide⟩ ⊓ Pmin K ⟨0, by decide⟩ = borelSub Tag.G2 K := by
  apply Subgroup.map_injective (f := (mk K).toMonoidHom) (mk K).injective
  rw [Subgroup.map_inf_eq _ _ (mk K).toMonoidHom (mk K).injective, map_Pmin_one hK,
    map_Pmin_zero hK, P₁_inf_P₂, map_borelSub hK]

end CFSG.Quasithin.H13.F431.G2
