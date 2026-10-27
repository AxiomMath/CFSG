module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamNoFive
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.E9

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique CFSG.Quasithin.H23P4
  CFSG.QuasithinUnique.Setup.X7a

variable {K : Type} [Field K]

theorem sl2_up_mul_low_cube [CharP K 2] : (sl2Up K 1 * sl2Low K 1) ^ 3 = 1 := by
  have h1 : (1 : K) + 1 = 0 := by
    have : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [← this]
    norm_num
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Up, sl2Low, pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h1]

theorem sl2_up_mul_low_entry :
    ((sl2Up K 1 * sl2Low K 1 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sl2Up, sl2Low, Matrix.mul_apply, Fin.sum_univ_two]

theorem order_three_of_embedded [CharP K 2] {Γ : Type*} [Group Γ] {M : Subgroup Γ}
    (φ : SpecialLinearGroup (Fin 2) K →* Γ) (hx : φ (sl2Up K 1) ∈ M)
    (hn : φ (sl2Up K 1) * φ (sl2Low K 1) * φ (sl2Up K 1) ∈ M) :
    φ (sl2Up K 1 * sl2Low K 1) ∈ M ∧ φ (sl2Up K 1 * sl2Low K 1) ^ 3 = 1 := by
  have hy : φ (sl2Low K 1) ∈ M := by
    have : φ (sl2Low K 1) = (φ (sl2Up K 1))⁻¹ *
        (φ (sl2Up K 1) * φ (sl2Low K 1) * φ (sl2Up K 1)) * (φ (sl2Up K 1))⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hx) hn) (inv_mem hx)
  refine ⟨by rw [map_mul]; exact mul_mem hx hy, ?_⟩
  rw [← map_pow, sl2_up_mul_low_cube, map_one]

variable {r : ℕ}

theorem proj_ne_one_of_entry {g : StatedSp r K} {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (h : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a b ≠ 0) :
    proj r K g ≠ 1 := by
  intro h1
  have h2 : g ∈ (proj r K).ker := h1
  rw [ker_proj] at h2
  obtain ⟨c, hc⟩ := h2
  have h3 : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Matrix.scalar (Fin r ⊕ Fin r) (c : K) := by
    have := congrArg (fun x : GL (Fin r ⊕ Fin r) K =>
      (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using this.symm
  apply h
  rw [h3]
  simp [Matrix.scalar_apply, hab]

variable [CharP K 2]

theorem exists_order_three_of_weylRep_mem (M : Subgroup (StatedSp r K))
    (hU : unipotent r K ≤ M) (k : Fin r) (hn : weylRep K k ∈ M) :
    ∃ g ∈ M, g ^ 3 = 1 ∧ proj r K g ≠ 1 := by
  by_cases h : (k : ℕ) + 1 < r
  · set k' : Fin r := ⟨k + 1, h⟩ with hk'
    have hkk' : k ≠ k' := fun e => by
      have := congrArg Fin.val e
      simp [k'] at this
    have hsnd : simpleSnd k = Sum.inl k' := by
      unfold simpleSnd
      rw [dite_eq_left h]
    have hkb : (Sum.inl k : Fin r ⊕ Fin r) ≠ Sum.inl k' := fun e => hkk' (Sum.inl_injective e)
    have hform := weylRep_eq_pair (K := K) k hsnd hkb
    rw [pairRootElt_short hkk', pairRootElt_short' hkk'] at hform
    simp only [CharTwo.neg_eq] at hform
    have hroot : pairRootElt hkb (1 : K) ∈ rootSubgroup K (simpleRootVec r k) := by
      have := pairRootElt_mem_rootSubgroup hkb (1 : K)
      rwa [← rootVec_simpleSnd k, hsnd]
    have hx : rho k k' hkk' (sl2Up K 1) ∈ M := by
      rw [← pairRootElt_short hkk']
      exact hU (rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k) hroot)
    obtain ⟨hgM, hg3⟩ := order_three_of_embedded (rho k k' hkk') hx (hform ▸ hn)
    refine ⟨_, hgM, hg3, proj_ne_one_of_entry (a := Sum.inl k) (b := Sum.inl k')
      hkb ?_⟩
    rw [coe_rho', fromBlocks_apply₁₁, (pairMat_apply_pair hkk' _).2.1, sl2_up_mul_low_entry]
    exact one_ne_zero
  · have hsnd : simpleSnd k = Sum.inr k := by
      unfold simpleSnd
      rw [dite_eq_right h]
    have hkb : (Sum.inl k : Fin r ⊕ Fin r) ≠ Sum.inr k := Sum.inl_ne_inr
    have hform := weylRep_eq_pair (K := K) k hsnd hkb
    rw [pairRootElt_long, pairRootElt_long'] at hform
    simp only [CharTwo.neg_eq] at hform
    have hroot : pairRootElt hkb (1 : K) ∈ rootSubgroup K (simpleRootVec r k) := by
      have := pairRootElt_mem_rootSubgroup hkb (1 : K)
      rwa [← rootVec_simpleSnd k, hsnd]
    have hx : lam k (sl2Up K 1) ∈ M := by
      rw [← pairRootElt_long]
      exact hU (rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k) hroot)
    obtain ⟨hgM, hg3⟩ := order_three_of_embedded (lam k) hx (hform ▸ hn)
    refine ⟨_, hgM, hg3, proj_ne_one_of_entry (a := Sum.inl k) (b := Sum.inr k) hkb ?_⟩
    rw [coe_lam, (pairMat_apply_pair hkb _).2.1, sl2_up_mul_low_entry]
    exact one_ne_zero

theorem borel_or_order_three_sp (M : Subgroup (StatedSp r K)) (hU : unipotent r K ≤ M) :
    M ≤ borelSubgroup r K ∨ ∃ g ∈ M, g ^ 3 = 1 ∧ proj r K g ≠ 1 := by
  by_cases h : ∃ k : Fin r, weylRep K k ∈ M
  · obtain ⟨k, hk⟩ := h
    exact Or.inr (exists_order_three_of_weylRep_mem M hU k hk)
  · push Not at h
    refine Or.inl ((le_flagStabilizer_borelCuts M hU).trans ?_)
    rw [(subflag_generation (K := K) (borelCuts K M)
      (fun i hi => (borelCuts_le M i hi).2)).1, Subgroup.closure_le]
    rintro g (hg | ⟨k, hk, rfl⟩)
    · exact hg
    · exact absurd ((succ_mem_borelCuts_iff M k).2 (h k)) hk

omit [CharP K 2] in
theorem pow_three_mem_unipotent (hK3 : ∀ x : K, x ≠ 0 → x ^ 3 = 1) {g : StatedSp r K}
    (hg : g ∈ borelSubgroup r K) : g ^ 3 ∈ unipotent r K := by
  have h1 : (diagHom r K ⟨g, hg⟩) ^ 3 = 1 := by
    funext i
    apply Units.ext
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one]
    exact hK3 _ (Units.ne_zero _)
  have h2 : (⟨g, hg⟩ : borelSubgroup r K) ^ 3 ∈ (diagHom r K).ker := by
    rw [MonoidHom.mem_ker, map_pow, h1]
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at h2
  simpa using h2

variable [Finite K]

theorem noFiveIndex_statedProj_sp (hr : 1 ≤ r) (hK3 : ∀ x : K, x ≠ 0 → x ^ 3 = 1) :
    NoFiveIndex (StatedProj (StatedSp r K)) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 hr
  have hS : IsSylowTwoOf (projUnipotent r K) ⊤ := by
    rw [isSylowTwoOf_top_iff, ← hP]
    exact ⟨P.isPGroup', P.not_dvd_index⟩
  refine noFiveIndex_of_dichotomy (B := projBorel r K) hS ?_ ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨s, hs, rfl⟩
    refine ⟨b * s * b⁻¹, ?_, by simp⟩
    have hs' : (⟨s, unipotent_le_borelSubgroup hs⟩ : borelSubgroup r K) ∈
        (unipotent r K).subgroupOf (borelSubgroup r K) := hs
    exact (unipotent_subgroupOf_borelSubgroup_normal (r := r) (K := K)).conj_mem _ hs' ⟨b, hb⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g ^ 3, pow_three_mem_unipotent hK3 hg, by simp⟩
  · intro A hA
    have hUM : unipotent r K ≤ A.comap (proj r K) := fun u hu =>
      hA (Subgroup.mem_map_of_mem _ hu)
    rcases borel_or_order_three_sp (A.comap (proj r K)) hUM with hle | ⟨g, hgM, hg3, hgs⟩
    · left
      intro a ha
      obtain ⟨g, rfl⟩ := proj_surjective (r := r) (K := K) a
      exact ⟨g, hle ha, rfl⟩
    · right
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact ⟨proj r K g, hgM, orderOf_eq_prime (by rw [← map_pow, hg3, map_one]) hgs⟩

end CFSG.Quasithin.E9

namespace CFSG.Quasithin.E9

open CFSG.QuasithinUnique CFSG.Quasithin.H23P4 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem rowOK_of_isPSp4_two_two {X : Type} [Group X] (h : IsPSp4 2 2 X) : RowOK X := by
  have h' := h
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by simpa using hK
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num : 1 ≤ 2) hK
  have hfinP : Finite (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp 2 K
  have hfinX : Finite X := Finite.of_equiv _ e.toEquiv.symm
  have hsimple : IsSimpleGroup X :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 2 h'
  have hout : CFSG.Quasithin.H23Out.NoFiveOut (StatedProj (StatedSp 2 K)) := by
    have := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hK
    have h4 := (CFSG.QuasithinUnique.Lin2.sp4OutCyclic K 2 hcard (by norm_num)).2
    intro h5
    rw [h4] at h5
    norm_num at h5
  refine ⟨?_, CFSG.Quasithin.H23Out.Out5Pow.of_noFiveOut
    (CFSG.Quasithin.H23Out.NoFiveOut.of_mulEquiv e hout),
    NoFiveIndex.of_mulEquiv e (noFiveIndex_statedProj_sp (by norm_num)
      (pow_three_eq_one_of_card_four hK4))⟩
  have hcard : Nat.card ((projUnipotent 2 K).map (e.symm : StatedProj (StatedSp 2 K) →* X)) =
      256 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_projUnipotent (by norm_num), hK4]
    norm_num
  exact center_eq_bot_of_simple_of_card hcard (by norm_num) (by norm_num)

end CFSG.Quasithin.E9
