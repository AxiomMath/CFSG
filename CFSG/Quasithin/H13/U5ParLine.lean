module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieE
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylC
public import CFSG.Milestones.ASVolI.F429.aC8U5
public import CFSG.LocalAnalysis.EvenBN.U5.ModelA2N2Two

public section

namespace CFSG.Quasithin.H13.U5Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.ASVolI CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

private theorem isub_le_u5LnStab : Isub h ≤ u5LnStab h :=
  (hypTorus_le_hypBorel h).trans
    (hypBorel_le_isoStabilizer h (d := 2) (by norm_num) (by norm_num))

private theorem ssub_le_u5LnStab : Ssub h ≤ u5LnStab h :=
  (Ssub_le_Usub.trans (hypUnitriangular_le_hypBorel h)).trans
    (hypBorel_le_isoStabilizer h (d := 2) (by norm_num) (by norm_num))

private theorem u5LnStab_le_normalizer_Ssub :
    u5LnStab h ≤ Subgroup.normalizer (Ssub h : Set (hypSU h 2 1)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact burnsideF429a_conj_mem_Ssub hg
  · intro hs
    have h' := burnsideF429a_conj_mem_Ssub (g := g⁻¹) (inv_mem hg) hs
    have e : g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ = s := by group
    rwa [e] at h'

private theorem exists_isub_eq_lev {t : hypSU h 2 1} (ht : t ∈ Isub h) :
    ∃ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), t = lev A hA := by
  obtain ⟨a, d, -, hp, hm⟩ := ht
  change mat t = diagonal (torusEntries h a d) at hm
  set a0 : K := (a 0 : K) with ha0def
  set a1 : K := (a 1 : K) with ha1def
  have ha0 : a0 ≠ 0 := (a 0).ne_zero
  have ha1 : a1 ≠ 0 := (a 1).ne_zero
  have hd0 : (d 0 : K) = h.bar (a0 * a1) / (a0 * a1) := by
    have hp' : (a0 * a1) / (h.bar a0 * h.bar a1) * (d 0 : K) = 1 := by
      simpa [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one, a0, a1] using hp
    have hb0 : h.bar a0 ≠ 0 := (map_ne_zero h.bar).mpr ha0
    have hb1 : h.bar a1 ≠ 0 := (map_ne_zero h.bar).mpr ha1
    rw [map_mul]
    field_simp at hp' ⊢
    linear_combination hp'
  refine ⟨!![a0, 0; 0, a1], isUnit_det_diag ha0 ha1, ?_⟩
  apply mat_injective
  rw [hm, mat_lev_diag ha0 ha1]
  ext c d'
  rcases c with i | k | i <;> rcases d' with j | l | j <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [torusEntries, a0, a1, hd0]

private theorem isub_le_normalizer_N₁sub :
    Isub h ≤ Subgroup.normalizer (N₁sub h : Set (hypSU h 2 1)) := by
  intro t ht
  obtain ⟨A, hA, rfl⟩ := exists_isub_eq_lev h ht
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact lev_conj_mem_N₁sub A hA
  · intro hn
    have hA' : IsUnit (A⁻¹).det := by rw [det_nonsing_inv]; exact hA.ringInverse
    have h2 := lev_conj_mem_N₁sub (h := h) A⁻¹ hA' hn
    rw [show lev (hK := h) A⁻¹ hA' = (lev (hK := h) A hA)⁻¹ from
      (lev_inv (h := h) A hA).symm] at h2
    have e : (lev (hK := h) A hA)⁻¹ * (lev (hK := h) A hA * n * (lev (hK := h) A hA)⁻¹) *
        ((lev (hK := h) A hA)⁻¹)⁻¹ = n := by group
    rwa [e] at h2

theorem blkA_eq_one_of_mem_Ssub {s : hypSU h 2 1} (hs : s ∈ Ssub h) :
    blkA (mat s) = 1 := by
  obtain ⟨-, x, C, hC⟩ := hs
  ext i j
  rw [hC, oddUni]
  simp [blkA]

theorem det_blkA_eq_one_of_mem_N₁sub {n : hypSU h 2 1} (hn : n ∈ N₁sub h) :
    (blkA (mat n)).det = 1 := by
  obtain ⟨A, rfl⟩ := hn
  have h : blkA (mat (leviSU h 1 A)) = (A : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    rw [blkA, mat_leviSU]
    simp
  rw [h, Matrix.SpecialLinearGroup.det_coe]

private theorem blkA_mul_of_mem_Ssub_mem_N₁sub {s n : hypSU h 2 1}
    (hs : s ∈ Ssub h) (hn : n ∈ N₁sub h) :
    blkA (mat s * mat n) = blkA (mat s) * blkA (mat n) := by
  obtain ⟨-, x, C, hC⟩ := hs
  obtain ⟨A, rfl⟩ := hn
  have h2 : ∀ (B : Matrix (Fin 2) (Fin 2) K) (X : Matrix (Fin 2) (Fin 1) K)
      (Y : Matrix (Fin 2) (Fin 2) K) (P : Matrix (Fin 1) (Fin 1) K)
      (Q : Matrix (Fin 1) (Fin 2) K) (D : Matrix (Fin 2) (Fin 2) K),
      blkA (blk3 B X Y P Q D) = B := by
    intro B X Y P Q D
    ext i j
    simp [blkA]
  rw [hC, oddUni, mat_leviSU, blk3_mul]
  simp only [h2]

theorem det_blkA_eq_one_of_mem_sup {x : hypSU h 2 1}
    (hx : x ∈ Ssub h ⊔ N₁sub h) : (blkA (mat x)).det = 1 := by
  have hNnorm : N₁sub h ≤ Subgroup.normalizer (Ssub h : Set (hypSU h 2 1)) :=
    N₁sub_le_u5LnStab.trans (u5LnStab_le_normalizer_Ssub h)
  change x ∈ ((Ssub h ⊔ N₁sub h : Subgroup (hypSU h 2 1)) : Set _) at hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (Ssub h) (N₁sub h) hNnorm,
    Set.mem_mul] at hx
  obtain ⟨s, hs, n, hn, rfl⟩ := hx
  rw [mat_mul, blkA_mul_of_mem_Ssub_mem_N₁sub h hs hn, Matrix.det_mul,
    blkA_eq_one_of_mem_Ssub h hs, Matrix.det_one, det_blkA_eq_one_of_mem_N₁sub h hn, one_mul]

private theorem eq_one_of_mul_self_eq_one_char_two {a : K} (h2 : (2 : K) = 0)
    (ha : a * a = 1) : a = 1 := by
  have : (a - 1) * (a - 1) = 0 := by linear_combination ha + (1 - a) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 this)

theorem u5LnStab_eq_sup :
    u5LnStab h = (Ssub h ⊔ N₁sub h) ⊔ Isub h := by
  apply le_antisymm
  · intro g hg
    have htri := burnsideF429a_mat_eq_zero_of_mem_u5LnStab (h := h) hg
    have hze : ∀ i : Fin 2, mat g (.inr (.inl 0)) (.inl i) = 0 := fun i =>
      htri _ _ (by simp [burnsideF429a_lev])
    have hfe : ∀ j i : Fin 2, mat g (.inr (.inr j)) (.inl i) = 0 := fun j i =>
      htri _ _ (by simp [burnsideF429a_lev])
    have hfz : ∀ j : Fin 2, mat g (.inr (.inr j)) (.inr (.inl 0)) = 0 := fun j =>
      htri _ _ (by simp [burnsideF429a_lev])
    obtain ⟨A, C, x, d, hA, hC, hd, -, -, hmat⟩ :=
      CFSG.Quasithin.H13.F431.Un.L5.syl_decomp hze hfe hfz
    obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub (hK := h) hC
    have hg_eq : g = lev A hA * s := by
      apply mat_injective
      rw [mat_mul, mat_lev, ← hd, hsm, ← hmat]
    obtain ⟨n, hn, hni⟩ := exists_lev_eq_mul (h := h) A hA
    have hiI : lev (hK := h) !![A.det, 0; 0, 1] (isUnit_det_diag hA.ne_zero one_ne_zero) ∈
        Isub h := (lev_diag (h := h) hA.ne_zero one_ne_zero).1
    rw [hg_eq, hni, mul_assoc]
    exact Subgroup.mul_mem ((Ssub h ⊔ N₁sub h) ⊔ Isub h)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hn))
      (Subgroup.mul_mem ((Ssub h ⊔ N₁sub h) ⊔ Isub h)
        (Subgroup.mem_sup_right hiI) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hs)))
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact ssub_le_u5LnStab h
    · exact N₁sub_le_u5LnStab
    · exact isub_le_u5LnStab h

theorem perfectCore_u5LnStab (hf : 2 ≤ f) :
    perfectCore (u5LnStab h) = Ssub h ⊔ N₁sub h := by
  set H : Subgroup (hypSU h 2 1) := Ssub h ⊔ N₁sub h with hH
  set Y : Subgroup (hypSU h 2 1) := u5LnStab h with hY
  have hHY : H ≤ Y := by rw [hY, u5LnStab_eq_sup h, hH]; exact le_sup_left
  have hIY : Isub h ≤ Y := by rw [hY]; exact isub_le_u5LnStab h
  have hYS : Y ≤ Subgroup.normalizer (Ssub h : Set (hypSU h 2 1)) := by
    rw [hY]; exact u5LnStab_le_normalizer_Ssub h
  have hIS : Isub h ≤ Subgroup.normalizer (Ssub h : Set (hypSU h 2 1)) := hIY.trans hYS
  have hIN : Isub h ≤ Subgroup.normalizer (N₁sub h : Set (hypSU h 2 1)) :=
    isub_le_normalizer_N₁sub h
  have hIleNH : Isub h ≤ Subgroup.normalizer (H : Set (hypSU h 2 1)) := by
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_sup (Ssub h) (N₁sub h) ⟨hIS ht, hIN ht⟩
  have hHn : (H.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHY]
    rw [hY, u5LnStab_eq_sup h]
    exact sup_le Subgroup.le_normalizer (by simpa [hH] using hIleNH)
  have hsolv : Group.IsSolvable ↥(Isub h) :=
    isSolvable_of_comm fun a b => Subtype.ext (hypTorus_comm h a.2 b.2)
  apply le_antisymm
  · refine perfectCore_le_of_sup_solvable (A := H) (B := Isub h) (Y := Y) hHY hHn ?_ hsolv
    show Y = H ⊔ Isub h
    rw [hY, u5LnStab_eq_sup h, hH]
  · refine le_perfectCore_of_perfect hHY ?_
    rw [hH]
    exact commutator_Ssub_sup_N₁sub hf

theorem Ssub_sup_N₁sub_inf_hypScalars :
    (Ssub h ⊔ N₁sub h) ⊓ hypScalars h 2 1 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨hxH, hxZ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨c, -, hcm⟩ := exists_scalar_of_mem_hypScalars hxZ
  have hdet := det_blkA_eq_one_of_mem_sup h hxH
  have hblk : blkA (mat x) = diagonal (fun _ : Fin 2 => c) := by
    ext i j
    simp only [blkA, Matrix.of_apply]
    rw [hcm]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hc2 : c * c = 1 := by
    rw [hblk, Matrix.det_diagonal, Finset.prod_const] at hdet
    simpa [pow_two] using hdet
  haveI : CharP K 2 := h.charP
  have hc1 : c = 1 := eq_one_of_mul_self_eq_one_char_two CharTwo.two_eq_zero hc2
  apply mat_injective
  ext a b
  rw [hcm, hc1, mat_one, one_apply]

theorem perfectCore_u5LnP (hf : 2 ≤ f) :
    perfectCore (u5LnP h) = (Ssub h ⊔ N₁sub h).map (hypProj h 2 1) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [u5LnP, projIsoStabilizer, ← map_perfectCore, perfectCore_u5LnStab h hf]

theorem pCoreOf_perfectCore_u5LnP (hf : 2 ≤ f) :
    CFSG.Open.pCoreOf 2 (perfectCore (u5LnP h)) = (Ssub h).map (hypProj h 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  let S : Subgroup (hypPSU h 2 1) := (Ssub h).map (hypProj h 2 1)
  have hP : u5LnP h ≤ Subgroup.normalizer (S : Set (hypPSU h 2 1)) := u5LnP_le_normalizer_S
  have hSle : S ≤ perfectCore (u5LnP h) := by
    change (Ssub h).map (hypProj h 2 1) ≤ perfectCore (u5LnP h)
    rw [perfectCore_u5LnP h hf]
    exact Subgroup.map_mono le_sup_left
  have hS2 : IsPGroup 2 S := by
    change IsPGroup 2 ((Ssub h).map (hypProj h 2 1))
    exact (IsPGroup.to_le (CFSG.RankThree.CentralLiftU.isPGroup_hypUnitriangular (h := h)
      (ε := 1) le_rfl) Ssub_le_Usub).map _
  have hSnorm : perfectCore (u5LnP h) ≤ Subgroup.normalizer (S : Set _) :=
    (perfectCore_le (u5LnP h)).trans hP
  have hlower : S ≤ CFSG.Open.pCoreOf 2 (perfectCore (u5LnP h)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSle hSnorm hS2
  have hupper : CFSG.Open.pCoreOf 2 (perfectCore (u5LnP h)) ≤
      CFSG.Open.pCoreOf 2 (u5LnP h) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (perfectCore (u5LnP h))).trans
        (perfectCore_le (u5LnP h))
    · have hN : u5LnP h ≤ Subgroup.normalizer (perfectCore (u5LnP h) : Set _) :=
        Subgroup.le_normalizer.trans
          (CFSG.Quasithin.normalizer_le_normalizer_perfectCore (u5LnP h))
      exact hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
        (perfectCore (u5LnP h)))
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (perfectCore (u5LnP h))
  rw [pCoreOf_u5LnP_eq] at hupper
  exact le_antisymm hupper hlower

end CFSG.Quasithin.H13.U5Par

end
