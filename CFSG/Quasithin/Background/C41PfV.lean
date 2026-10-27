module

public import CFSG.Quasithin.Background.C41PfR
public import CFSG.Quasithin.Vol2.Ch9KGFFSpConj

public section

namespace CFSG.Quasithin.C41Pf.SL3N

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def uMat (j : Fin 2) (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  if j = 0 then !![1, a, b; 0, 1, 0; 0, 0, 1] else !![1, 0, a; 0, 1, b; 0, 0, 1]

theorem det_uMat (j : Fin 2) (a b : K) : (uMat j a b).det = 1 := by
  fin_cases j <;> simp [uMat, Matrix.det_fin_three]

@[expose] def uSL (j : Fin 2) (a b : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨uMat j a b, det_uMat j a b⟩

theorem coe_uSL (j : Fin 2) (a b : K) :
    ((uSL j a b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uMat j a b := rfl

theorem uSL_mul (j : Fin 2) (a b c d : K) : uSL j a b * uSL j c d = uSL j (a + c) (b + d) := by
  apply Subtype.ext
  show uMat j a b * uMat j c d = uMat j (a + c) (b + d)
  ext r l
  fin_cases j <;> fin_cases r <;> fin_cases l <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uSL_zero (j : Fin 2) : uSL j (0 : K) 0 = 1 := by
  apply Subtype.ext
  show uMat j (0 : K) 0 = 1
  ext r l
  fin_cases j <;> fin_cases r <;> fin_cases l <;> simp [uMat]

theorem uSL_inv (j : Fin 2) (a b : K) : (uSL j a b)⁻¹ = uSL j (-a) (-b) := by
  rw [inv_eq_iff_mul_eq_one, uSL_mul, add_neg_cancel, add_neg_cancel, uSL_zero]

theorem uSL_mem_Q3 (j : Fin 2) (a b : K) : uSL j a b ∈ Q3 K j := by
  show uSL j a b ∈ stabilizer (flagSpace 3 K ((j : ℕ) + 1))
  refine mem_stabilizer_of_entries fun k l hk hl => ?_
  rw [coe_uSL]
  fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all [uMat]

theorem embSL_dT_mul_uSL_zero (t : Kˣ) (a b : K) :
    embSL 0 (CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT t) * uSL 0 a b =
      uSL 0 (((t⁻¹ : Kˣ) : K) * a) ((t : K) * b) *
        embSL 0 (CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT t) := by
  have ht : (t : K) ≠ 0 := t.ne_zero
  apply Subtype.ext
  show embMat 0 _ * uMat 0 a b = uMat 0 _ _ * embMat 0 _
  ext r l
  fin_cases r <;> fin_cases l <;>
    simp [embMat, uMat, CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT, Matrix.mul_apply,
      Fin.sum_univ_three] <;> field_simp

theorem embSL_dT_mul_uSL_one (t : Kˣ) (a b : K) :
    embSL 1 (CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT t) * uSL 1 a b =
      uSL 1 ((t : K) * a) (((t⁻¹ : Kˣ) : K) * b) *
        embSL 1 (CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT t) := by
  have ht : (t : K) ≠ 0 := t.ne_zero
  apply Subtype.ext
  show embMat 1 _ * uMat 1 a b = uMat 1 _ _ * embMat 1 _
  ext r l
  fin_cases r <;> fin_cases l <;>
    simp [embMat, uMat, CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem exists_uSL_eq_commutator (j : Fin 2) (t : Kˣ) (ht1 : (t : K) - 1 ≠ 0)
    (ht2 : ((t⁻¹ : Kˣ) : K) - 1 ≠ 0) (a b : K) :
    ∃ a₀ b₀ : K, ⁅embSL j (CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT t), uSL j a₀ b₀⁆ = uSL j a b := by
  match j with
  | 0 =>
    refine ⟨a / (((t⁻¹ : Kˣ) : K) - 1), b / ((t : K) - 1), ?_⟩
    rw [commutatorElement_def, embSL_dT_mul_uSL_zero, mul_inv_cancel_right, uSL_inv, uSL_mul]
    congr 1 <;> field_simp <;> ring
  | 1 =>
    refine ⟨a / ((t : K) - 1), b / (((t⁻¹ : Kˣ) : K) - 1), ?_⟩
    rw [commutatorElement_def, embSL_dT_mul_uSL_one, mul_inv_cancel_right, uSL_inv, uSL_mul]
    congr 1 <;> field_simp <;> ring

theorem exists_ne_zero_ne_one (hK4 : ∃ s : Finset K, s.card = 4) : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := hK4
  by_contra h
  push Not at h
  have hsub : s ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

@[expose] def xGrp (j : Fin 2) : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  Subgroup.closure (Set.range (fun p : K × K => uSL j p.1 p.2) ∪ Set.range (embSL (K := K) j))

theorem uSL_mem_xGrp (j : Fin 2) (a b : K) : uSL j a b ∈ xGrp j :=
  Subgroup.subset_closure (Or.inl ⟨(a, b), rfl⟩)

theorem xGrp_le_Q3 (j : Fin 2) : xGrp (K := K) j ≤ Q3 K j := by
  rw [xGrp, Subgroup.closure_le]
  rintro _ (⟨p, rfl⟩ | ⟨A, rfl⟩)
  · exact uSL_mem_Q3 j p.1 p.2
  · exact embSL_mem_Q3 j A

theorem xGrp_perfect (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    ⁅xGrp (K := K) j, xGrp (K := K) j⁆ = xGrp (K := K) j := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hrange : (embSL (K := K) j).range ≤ xGrp (K := K) j := by
    rintro _ ⟨A, rfl⟩
    exact Subgroup.subset_closure (Or.inr ⟨A, rfl⟩)
  rw [xGrp, Subgroup.closure_le]
  rintro _ (⟨⟨a, b⟩, rfl⟩ | ⟨A, rfl⟩)
  · obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_ne_one hK4
    set t : Kˣ := Units.mk0 x hx0 with ht
    have ht1 : (t : K) - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have ht2 : ((t⁻¹ : Kˣ) : K) - 1 ≠ 0 := by
      rw [Units.val_inv_eq_inv_val, sub_ne_zero]
      intro h
      apply hx1
      have := congrArg (·⁻¹) h
      simpa [ht] using this
    have hd : embSL j (CFSG.Quasithin.H13.Ch9.KGFF.SpM.dT t) ∈ xGrp (K := K) j :=
      hrange ⟨_, rfl⟩
    obtain ⟨a₀, b₀, h⟩ := exists_uSL_eq_commutator j t ht1 ht2 a b
    show uSL j a b ∈ ⁅xGrp (K := K) j, xGrp (K := K) j⁆
    rw [← h]
    exact Subgroup.commutator_mem_commutator hd (uSL_mem_xGrp j a₀ b₀)
  · have h := embSL_range_perfect hK4 j
    have hA : embSL j A ∈ ⁅(embSL (K := K) j).range, (embSL (K := K) j).range⁆ := by
      rw [h]
      exact ⟨A, rfl⟩
    exact Subgroup.commutator_mono hrange hrange hA

theorem uSL_mem_perfectCore (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) (a b : K) :
    uSL j a b ∈ perfectCore (Q3 K j) :=
  le_perfectCore_of_perfect (xGrp_le_Q3 j) (xGrp_perfect hK4 j) (uSL_mem_xGrp j a b)

section Rad

variable [Finite K]

@[expose] noncomputable def rad3 (j : Fin 2) : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  ((blk3 (K := K) j).ker).map (perfectCore (Q3 K j)).subtype

theorem rad3_le (j : Fin 2) : rad3 (K := K) j ≤ perfectCore (Q3 K j) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_rad3 {j : Fin 2} {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ perfectCore (Q3 K j))
    (h1 : blk3 j ⟨g, hg⟩ = 1) : g ∈ rad3 j :=
  ⟨⟨g, hg⟩, h1, rfl⟩

theorem blk3_eq_one_of_mem_rad3 {j : Fin 2} {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ rad3 j) :
    ∃ hg' : g ∈ perfectCore (Q3 K j), blk3 j ⟨g, hg'⟩ = 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨x.2, hx⟩

theorem rad3_isPGroup (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (j : Fin 2) :
    IsPGroup 2 ↥(rad3 (K := K) j) :=
  (blk3_ker_isPGroup hK j).map (perfectCore (Q3 K j)).subtype

theorem conj_mem_rad3 {j : Fin 2} {n r : SpecialLinearGroup (Fin 3) K}
    (hn : n ∈ perfectCore (Q3 K j)) (hr : r ∈ rad3 j) : n * r * n⁻¹ ∈ rad3 j := by
  obtain ⟨y, hy, rfl⟩ := hr
  exact ⟨_, (blk3 j).normal_ker.conj_mem y hy ⟨n, hn⟩, rfl⟩

theorem uSL_mem_rad3 (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) (a b : K) :
    uSL j a b ∈ rad3 j := by
  refine mem_rad3 (uSL_mem_perfectCore hK4 j a b) ?_
  apply Subtype.ext
  rw [blk3_coe]
  ext r l
  fin_cases j <;> fin_cases r <;> fin_cases l <;> simp [blkAt, uSL, uMat]

omit [Finite K] in
theorem fixed_uSL_zero {v : Fin 3 → K} (h1 : uMat 0 (1 : K) 0 *ᵥ v = v)
    (h2 : uMat 0 (0 : K) 1 *ᵥ v = v) : v 1 = 0 ∧ v 2 = 0 := by
  have e1 := congrFun h1 0
  have e2 := congrFun h2 0
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1 e2
  exact ⟨e1, e2⟩

omit [Finite K] in
theorem fixed_uSL_one {v : Fin 3 → K} (h1 : uMat 1 (1 : K) 0 *ᵥ v = v) : v 2 = 0 := by
  have e1 := congrFun h1 0
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1
  exact e1

theorem fixed_rad3_zero (hK4 : ∃ s : Finset K, s.card = 4) {v : Fin 3 → K}
    (hR : ∀ r ∈ rad3 (K := K) 0, ((r : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      v = v) : v 1 = 0 ∧ v 2 = 0 :=
  fixed_uSL_zero (hR _ (uSL_mem_rad3 hK4 0 1 0)) (hR _ (uSL_mem_rad3 hK4 0 0 1))

theorem fixed_rad3_one (hK4 : ∃ s : Finset K, s.card = 4) {v : Fin 3 → K}
    (hR : ∀ r ∈ rad3 (K := K) 1, ((r : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      v = v) : v 2 = 0 :=
  fixed_uSL_one (hR _ (uSL_mem_rad3 hK4 1 1 0))

theorem mulVec_of_mem_perfectCore_zero {n : SpecialLinearGroup (Fin 3) K}
    (hn : n ∈ perfectCore (Q3 K 0)) {v : Fin 3 → K} (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    (n : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  have hQ : n ∈ stabilizer (flagSpace 3 K 1) := perfectCore_le _ hn
  have h10 := stabilizer_entries (k := 1) (l := 0) hQ (by norm_num) (by norm_num)
  have h20 := stabilizer_entries (k := 2) (l := 0) hQ (by norm_num) (by norm_num)
  have h00 : (n : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    have := det_blkMon_eq_one (Q3 K 0) 0 1 (by norm_num) (blockLeft_zero _ 1)
      (blockRight_of_stabilizer fun g hg => hg) (perfectCore_le (Q3 K 0))
      (perfect_perfectCore_Q3 0) ⟨n, hn⟩
    rw [blkMon_apply, Matrix.det_unique] at this
    simpa [blkAt] using this
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, h00, h10, h20]

end Rad

section Normal

variable [Finite K]

theorem le_rad3_of_isPGroup [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) {j : Fin 2}
    {X : Subgroup (SpecialLinearGroup (Fin 3) K)} (hXN : X ≤ perfectCore (Q3 K j))
    (hnorm : ∀ n ∈ perfectCore (Q3 K j), ∀ x ∈ X, n * x * n⁻¹ ∈ X) (h2 : IsPGroup 2 ↥X) :
    X ≤ rad3 j := by
  have := sl2_isSimple (K := K) hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xc : Subgroup ↥(perfectCore (Q3 K j)) := X.subgroupOf (perfectCore (Q3 K j)) with hXc
  have hXcn : Xc.Normal := ⟨fun x hx n => hnorm n n.2 x hx⟩
  have hY := Subgroup.Normal.map hXcn (blk3 j) (blk3_surjective hK4 j)
  have hY2 : IsPGroup 2 ↥(Xc.map (blk3 j)) :=
    (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm).map (blk3 j)
  rcases Subgroup.Normal.eq_bot_or_eq_top (Xc.map (blk3 j)) with hbot | htop
  · intro x hx
    have hx' : (⟨x, hXN hx⟩ : ↥(perfectCore (Q3 K j))) ∈ Xc := hx
    have h1 : blk3 j ⟨x, hXN hx⟩ ∈ Xc.map (blk3 j) := ⟨_, hx', rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact mem_rad3 (hXN hx) h1
  · exfalso
    rw [htop] at hY2
    have h2' : IsPGroup 2 (SpecialLinearGroup (Fin 2) K) := hY2.of_equiv Subgroup.topEquiv
    have : Nontrivial (SpecialLinearGroup (Fin 2) K) := IsSimpleGroup.toNontrivial
    have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4
    exact Group.IsPerfect.not_isNilpotent _ h2'.isNilpotent

theorem eq_perfectCore_of_normal [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) {j : Fin 2} {Y : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hYN : Y ≤ perfectCore (Q3 K j))
    (hnorm : ∀ n ∈ perfectCore (Q3 K j), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) (hperf : ⁅Y, Y⁆ = Y)
    (hne : Y ≠ ⊥) : Y = perfectCore (Q3 K j) := by
  have := sl2_isSimple (K := K) hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := perfectCore (Q3 K j) with hN
  set Yc : Subgroup ↥N := Y.subgroupOf N with hYc
  have hYcn : Yc.Normal := ⟨fun y hy n => hnorm n n.2 y hy⟩
  have hY := Subgroup.Normal.map hYcn (blk3 j) (blk3_surjective hK4 j)
  rcases Subgroup.Normal.eq_bot_or_eq_top (Yc.map (blk3 j)) with hbot | htop
  · exfalso
    have hYrad : Y ≤ rad3 j := by
      intro y hy
      have hy' : (⟨y, hYN hy⟩ : ↥N) ∈ Yc := hy
      have h1 : blk3 j ⟨y, hYN hy⟩ ∈ Yc.map (blk3 j) := ⟨_, hy', rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact mem_rad3 (hYN hy) h1
    have hY2 : IsPGroup 2 ↥Y := (rad3_isPGroup hK j).to_le hYrad
    rcases Subgroup.bot_or_nontrivial Y with hb | hnt
    · exact hne hb
    · have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
      exact Group.IsPerfect.not_isNilpotent _ hY2.isNilpotent
  · refine le_antisymm hYN fun n hn => ?_
    have hsurj : ∀ x : ↥N, ∃ y ∈ Yc, (blk3 j) y = (blk3 j) x := by
      intro x
      have hx : (blk3 j) x ∈ Yc.map (blk3 j) := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, he⟩ := hx
      exact ⟨y, hy, he⟩
    let π := QuotientGroup.mk' Yc
    have hQ2 : IsPGroup 2 (↥N ⧸ Yc) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Yc q
      obtain ⟨y, hy, he⟩ := hsurj x
      have hr : ((y⁻¹ * x : ↥N) : SpecialLinearGroup (Fin 3) K) ∈ rad3 j :=
        mem_rad3 (y⁻¹ * x).2 (by rw [map_mul, map_inv, he, inv_mul_cancel])
      obtain ⟨a, ha⟩ := rad3_isPGroup hK j ⟨_, hr⟩
      refine ⟨a, ?_⟩
      have hy1 : QuotientGroup.mk' Yc y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      have e : (QuotientGroup.mk' Yc x : ↥N ⧸ Yc) = QuotientGroup.mk' Yc (y⁻¹ * x) := by
        rw [map_mul, map_inv, hy1, inv_one, one_mul]
      rw [e, ← map_pow]
      have h3 : (y⁻¹ * x) ^ 2 ^ a = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val ha
        simpa using this
      rw [h3, map_one]
    have hQperf : Group.IsPerfect (↥N ⧸ Yc) := by
      have hNp : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
      refine ⟨?_⟩
      have h1 : commutator (↥N ⧸ Yc) = (commutator ↥N).map π := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          QuotientGroup.range_mk']
      rw [h1, Group.isPerfect_def.mp hNp, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    have hsub : Subsingleton (↥N ⧸ Yc) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isNilpotent _ hQ2.isNilpotent
    have h1 : (QuotientGroup.mk' Yc ⟨n, hn⟩ : ↥N ⧸ Yc) = 1 := Subsingleton.elim _ _
    have h2 : (⟨n, hn⟩ : ↥N) ∈ Yc := (QuotientGroup.eq_one_iff _).mp h1
    exact h2

end Normal

section Parabolic

variable [Finite K] [CharP K 2]

theorem isSylowTwoOf_unitriangular_three :
    CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  exact hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem sl3_perfectCore_parabolic_conj (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    {Pa : Subgroup (SpecialLinearGroup (Fin 3) K)} (hpar : IsParabolic2 ⊤ Pa) (hne : Pa ≠ ⊤) :
    perfectCore Pa = ⊥ ∨ ∃ (g : SpecialLinearGroup (Fin 3) K) (j : Fin 2),
      perfectCore Pa = (perfectCore (Q3 K j)).map (MulAut.conj g).toMonoidHom := by
  have hR := linear_three_residual_of_cover hK (MonoidHom.id (SpecialLinearGroup (Fin 3) K))
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le)
  simp only [Subgroup.map_id] at hR
  exact CFSG.Quasithin.H13.Ch9.KGFF.perfectCore_parabolic_conj isSylowTwoOf_unitriangular_three hR
    hpar hne

end Parabolic

section Natural

theorem exists_sl3_mulVec_e0 {v : Fin 3 → K} (hv : v ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 3) K,
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1 : Fin 3 → K) = v := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨⟨!![0, 1, 0; 0, 0, (v 2)⁻¹; v 2, 0, 0], by simp [Matrix.det_fin_three, h2]⟩, ?_⟩
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1]
    · refine ⟨⟨!![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1], by simp [Matrix.det_fin_three, h1]⟩, ?_⟩
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0]
  · refine ⟨⟨!![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1], by simp [Matrix.det_fin_three, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_sl3_mulVec_eq {v w : Fin 3 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 3) K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_sl3_mulVec_e0 hv
  obtain ⟨b, hb⟩ := exists_sl3_mulVec_e0 hw
  refine ⟨b * a⁻¹, ?_⟩
  have hinv : ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (Pi.single 0 1 : Fin 3 → K) := by
    rw [← ha, Matrix.mulVec_mulVec]
    have e : ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (a : Matrix (Fin 3) (Fin 3) K) = 1 :=
      congrArg Subtype.val (inv_mul_cancel a)
    rw [e, Matrix.one_mulVec]
  have e2 : ((b * a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (b : Matrix (Fin 3) (Fin 3) K) * ((a⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := rfl
  rw [e2, ← Matrix.mulVec_mulVec, hinv, hb]

theorem eq_bot_or_eq_top_of_invariant (Y : AddSubgroup (Fin 3 → K))
    (hY : ∀ A : SpecialLinearGroup (Fin 3) K, ∀ y ∈ Y,
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hb : Y = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨y, hyY⟩, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hb
  have hy0' : y ≠ 0 := fun h => hy0 (Subtype.ext h)
  refine eq_top_iff.mpr fun w _ => ?_
  by_cases hw : w = 0
  · rw [hw]
    exact Y.zero_mem
  obtain ⟨A, hA⟩ := exists_sl3_mulVec_eq hy0' hw
  rw [← hA]
  exact hY A y hyY

theorem mulVec_mulVec_inv (g : SpecialLinearGroup (Fin 3) K) (y : Fin 3 → K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec]
  have e : (g : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g)
  rw [e, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (g : SpecialLinearGroup (Fin 3) K) (y : Fin 3 → K) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec]
  have e : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  rw [e, Matrix.one_mulVec]

theorem conj_mulVec_fixed_iff (g r : SpecialLinearGroup (Fin 3) K) (y : Fin 3 → K) :
    ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y = y ↔
      (r : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y := by
  have e : ∀ z, ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((r : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z)) := by
    intro z
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rfl
  constructor
  · intro h
    rw [e] at h
    have := congrArg (fun z => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ z) h
    simpa only [mulVec_inv_mulVec] using this
  · intro h
    rw [e, h, mulVec_mulVec_inv]

theorem embSL_one_mulVec (A : SpecialLinearGroup (Fin 2) K) {v : Fin 3 → K} (hv : v 2 = 0) :
    (embSL 1 A : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ![((A : Matrix (Fin 2) (Fin 2) K) *ᵥ ![v 0, v 1]) 0,
        ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ ![v 0, v 1]) 1, 0] := by
  rw [coe_embSL]
  funext i
  fin_cases i <;> simp [embMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
    hv]

theorem mulVec_of_mem_rad3_one [Finite K] {r : SpecialLinearGroup (Fin 3) K}
    (hr : r ∈ rad3 (K := K) 1) {v : Fin 3 → K} (hv : v 2 = 0) :
    (r : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  obtain ⟨hr', h1⟩ := blk3_eq_one_of_mem_rad3 hr
  have hQ : r ∈ stabilizer (flagSpace 3 K 2) := perfectCore_le _ hr'
  have h20 := stabilizer_entries (k := 2) (l := 0) hQ (by norm_num) (by norm_num)
  have h21 := stabilizer_entries (k := 2) (l := 1) hQ (by norm_num) (by norm_num)
  have hb : ∀ i k : Fin 2, blkAt (1 - ((1 : Fin 2) : ℕ)) 2 (q3_blk_le 1)
      (r : Matrix (Fin 3) (Fin 3) K) i k = (1 : Matrix (Fin 2) (Fin 2) K) i k := by
    intro i k
    have := congrArg (fun y : SpecialLinearGroup (Fin 2) K => (y : Matrix (Fin 2) (Fin 2) K) i k) h1
    exact this
  have e00 := hb 0 0
  have e01 := hb 0 1
  have e10 := hb 1 0
  have e11 := hb 1 1
  simp [blkAt] at e00 e01 e10 e11
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv, e00, e01, e10, e11, h20,
    h21]

end Natural

section Pair

theorem sl2_eq_bot_or_eq_top (Y : AddSubgroup (Fin 2 → K))
    (hY : ∀ A : SpecialLinearGroup (Fin 2) K, ∀ y ∈ Y, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ y ∈ Y) :
    Y = ⊥ ∨ Y = ⊤ := by
  by_cases hb : Y = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨y, hyY⟩, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hb
  have hy0' : y ≠ 0 := fun h => hy0 (Subtype.ext h)
  refine eq_top_iff.mpr fun w _ => ?_
  by_cases hw : w = 0
  · rw [hw]
    exact Y.zero_mem
  obtain ⟨A, hA⟩ := SpN.exists_sl2_mulVec_eq hy0' hw
  rw [← hA]
  exact hY A y hyY

theorem exists_scalar_of_commute (f : (Fin 2 → K) →+ (Fin 2 → K))
    (hf : ∀ A : SpecialLinearGroup (Fin 2) K, ∀ x,
      f ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ f x) :
    ∃ c : K, ∀ x, f x = c • x := by
  set u : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp⟩ with hu
  have he0 : (u : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
    funext i
    fin_cases i <;> simp [hu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 := hf u ![1, 0]
  rw [he0] at h1
  have h11 : f ![1, 0] 1 = 0 := by
    have := congrFun h1 0
    simp [hu, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this
  set c : K := f ![1, 0] 0 with hc
  have hfe : f ![1, 0] = c • ![1, 0] := by
    funext i
    fin_cases i <;> simp [h11, hc]
  refine ⟨c, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, smul_zero]
  obtain ⟨A, hA⟩ := SpN.exists_sl2_mulVec_e0 hx
  rw [← hA, hf, hfe, Matrix.mulVec_smul]

theorem sl2_submodule_pair (D : AddSubgroup ((Fin 2 → K) × (Fin 2 → K)))
    (hD : ∀ A : SpecialLinearGroup (Fin 2) K, ∀ p ∈ D,
      ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p.1, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ p.2) ∈ D) :
    D = ⊥ ∨ D = ⊤ ∨ (∃ c : K, ∀ p, p ∈ D ↔ p.2 = c • p.1) ∨ (∀ p, p ∈ D ↔ p.1 = 0) := by
  classical
  set D₂ : AddSubgroup (Fin 2 → K) := D.comap (AddMonoidHom.inr _ _) with hD₂
  set P₁ : AddSubgroup (Fin 2 → K) := D.map (AddMonoidHom.fst _ _) with hP₁
  have hD₂i : ∀ A : SpecialLinearGroup (Fin 2) K, ∀ y ∈ D₂,
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ y ∈ D₂ := by
    intro A y hy
    have := hD A _ hy
    simpa [hD₂, Matrix.mulVec_zero] using this
  have hP₁i : ∀ A : SpecialLinearGroup (Fin 2) K, ∀ x ∈ P₁,
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x ∈ P₁ := by
    rintro A _ ⟨p, hp, rfl⟩
    exact ⟨_, hD A p hp, rfl⟩
  rcases sl2_eq_bot_or_eq_top P₁ hP₁i with hP | hP
  ·
    have hfst : ∀ p ∈ D, p.1 = 0 := fun p hp => by
      have : p.1 ∈ P₁ := ⟨p, hp, rfl⟩
      rwa [hP, AddSubgroup.mem_bot] at this
    rcases sl2_eq_bot_or_eq_top D₂ hD₂i with h2 | h2
    · left
      rw [eq_bot_iff]
      intro p hp
      have h1 := hfst p hp
      have hp2 : p.2 ∈ D₂ := by
        show (0, p.2) ∈ D
        have e : p = (0, p.2) := Prod.ext h1 rfl
        rwa [← e]
      rw [h2, AddSubgroup.mem_bot] at hp2
      exact (AddSubgroup.mem_bot).mpr (Prod.ext h1 hp2)
    · right; right; right
      intro p
      constructor
      · exact hfst p
      · intro h1
        have hp2 : p.2 ∈ D₂ := h2 ▸ AddSubgroup.mem_top _
        have e : p = (0, p.2) := Prod.ext h1 rfl
        rw [e]
        exact hp2
  · rcases sl2_eq_bot_or_eq_top D₂ hD₂i with h2 | h2
    ·
      right; right; left
      have hex : ∀ x, ∃ y, (x, y) ∈ D := fun x => by
        have : x ∈ P₁ := hP ▸ AddSubgroup.mem_top x
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨p.2, hp⟩
      have huniq : ∀ x y y', (x, y) ∈ D → (x, y') ∈ D → y = y' := by
        intro x y y' h h'
        have : y - y' ∈ D₂ := by
          show (0, y - y') ∈ D
          have := D.sub_mem h h'
          simpa using this
        rw [h2, AddSubgroup.mem_bot, sub_eq_zero] at this
        exact this
      choose f hf using hex
      set fh : (Fin 2 → K) →+ (Fin 2 → K) :=
        { toFun := f
          map_zero' := huniq 0 _ 0 (hf 0) D.zero_mem
          map_add' := fun x y => huniq (x + y) _ _ (hf (x + y)) (D.add_mem (hf x) (hf y)) }
        with hfh
      have hcomm : ∀ A : SpecialLinearGroup (Fin 2) K, ∀ x,
          fh ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ fh x :=
        fun A x => huniq _ _ _ (hf _) (hD A _ (hf x))
      obtain ⟨c, hc⟩ := exists_scalar_of_commute fh hcomm
      refine ⟨c, fun p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
      · have := huniq p.1 _ _ hp (hf p.1)
        rw [this]
        exact hc p.1
      · have e : p = (p.1, f p.1) := by
          refine Prod.ext rfl ?_
          rw [hp]
          exact (hc p.1).symm
        rw [e]
        exact hf p.1
    · right; left
      rw [eq_top_iff]
      intro p _
      obtain ⟨q, hq, hq1⟩ : p.1 ∈ P₁ := hP ▸ AddSubgroup.mem_top _
      have h3 : p.2 - q.2 ∈ D₂ := h2 ▸ AddSubgroup.mem_top _
      have h4 := D.add_mem hq h3
      have e : q + (0, p.2 - q.2) = p := by
        refine Prod.ext ?_ ?_
        · simpa using hq1
        · simp
      rw [← e]
      exact h4

end Pair

end CFSG.Quasithin.C41Pf.SL3N
