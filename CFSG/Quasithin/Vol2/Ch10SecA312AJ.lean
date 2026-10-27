module

public import CFSG.Quasithin.Vol2.Ch10SecA312AH
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type} [Group G]

theorem commutator_perfectCore_le_of_le [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P) :
    ⁅Q, perfectCore P⁆ ≤ perfectCore P := by
  refine Subgroup.commutator_le.2 fun q hq b hb => ?_
  have hqN : q ∈ Subgroup.normalizer (perfectCore P : Set G) :=
    normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hQP hq))
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.1 hqN b).1 hb) (inv_mem hb)

theorem subgroupOf_le_pCoreOf [Finite G] {C : Subgroup G} {B : Subgroup ↥C} {Q : Subgroup G}
    (hQ : IsPGroup 2 ↥Q) (hQB : ∀ q ∈ Q, ∃ b ∈ B, (b : G) = q)
    (hBN : ∀ b ∈ B, (b : G) ∈ Subgroup.normalizer (Q : Set G)) :
    Q.subgroupOf C ≤ pCoreOf 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun q hq => ?_) (fun b hb => ?_) ?_
  · obtain ⟨b, hb, hbq⟩ := hQB _ hq
    rwa [show q = b from Subtype.ext hbq.symm]
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hBN b hb) (h : G)
  · let φ : ↥(Q.subgroupOf C) →* ↥Q :=
      { toFun := fun x => ⟨((x : ↥C) : G), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine IsPGroup.of_injective hQ φ fun x y h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

end General

section G2

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.LieType.Chevalley.RootOps
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem eq_zero_of_mul_add_self {w s : K} (hw : w ≠ 1) (h : w * s + s = 0) :
    s = 0 := by
  have h1 : (w + 1) * s = 0 := by rw [add_mul, one_mul]; exact h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (by linear_combination h2 - (CharTwo.two_eq_zero : (2 : K) = 0)) hw
  · exact h2

theorem g2_center_zero
    {z : ModGL Tag.G2 K} (hzQ : z ∈ parabolicRadical Tag.G2 K {i0})
    (hzC : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K))) :
    ∃ s t : K, z = gX rB s * gX rC t := by
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_zero hzQ
  have hN := N0_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i0} := fun hd c => mem_zero hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i0},
      ⁅gX rR t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N0 := N0.one_mem
  have hr : gX rR t₁ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i0} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have st1 := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
  have v1 : ⁅gX rR t₁, gX rV (1 : K)⁆ = gX rB (t₁ * 1) := rel_rv _ _
  have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
  have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
  have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
  have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
  rw [comm_five hN hr hu hv hb (by rw [v2]; exact gX_c_mem_N0 _)
    (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
    v1, v2, v3, v4, v5] at st1
  simp only [one_mul, mul_one] at st1
  rw [← (comm_bc t₁ t₂).eq] at st1
  obtain ⟨rfl, rfl⟩ := prod_bc_eq_one st1
  have st2 := hzg (gX rR 1) (hmem (Or.inl rfl) 1)
  have w1 : ⁅gX rR (0 : K), gX rR (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
  have w2 : ⁅gX rU (0 : K), gX rR (1 : K)⁆ = 1 := by
    rw [gX_zero]; exact commutatorElement_one_left _
  have w3 : ⁅gX rV t₃, gX rR (1 : K)⁆ = gX rB (1 * t₃) := by
    rw [← commutatorElement_inv, rel_rv, gX_inv]
  have w4 : ⁅gX rB t₄, gX rR (1 : K)⁆ = 1 := commutator_of_commute (comm_rb 1 t₄).symm
  have w5 : ⁅gX rC t₅, gX rR (1 : K)⁆ = 1 := commutator_of_commute (comm_rc 1 t₅).symm
  rw [comm_five hN hr hu hv hb (by rw [w2]; exact h1N)
    (by rw [w3]; exact gX_b_mem_N0 _) (by rw [w4]; exact h1N) (by rw [w5]; exact h1N),
    w1, w2, w3, w4, w5] at st2
  simp only [one_mul, mul_one] at st2
  have ht3 : t₃ = 0 := by simpa using gX_eq_one st2
  subst ht3
  exact ⟨t₄, t₅, by simp only [gX_zero, one_mul]⟩

theorem g2_center_one
    {z : ModGL Tag.G2 K} (hzQ : z ∈ parabolicRadical Tag.G2 K {i1})
    (hzC : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K))) :
    ∃ t : K, z = gX rC t := by
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_one hzQ
  have hN := N1_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rA ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i1} := fun hd c => mem_one hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i1},
      ⁅gX rA t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N1 := N1.one_mem
  have ha : gX rA t₁ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i1} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have ht₁ : t₁ = 0 := by
    have st := hzg (gX rB 1) (hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 1)
    have v1 : ⁅gX rA t₁, gX rB (1 : K)⁆ = gX rC (t₁ * 1) := rel_ab _ _
    have v2 : ⁅gX rU t₂, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_ub _ _)
    have v3 : ⁅gX rV t₃, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_vb _ _)
    have v4 : ⁅gX rB t₄, gX rB (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v5 : ⁅gX rC t₅, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_bc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₂ : t₂ = 0 := by
    have st := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
    have v1 : ⁅gX rA t₁, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_av _ _)
    have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
    have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact gX_c_mem_N1 _)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₃ : t₃ = 0 := by
    have st := hzg (gX rU 1) (hmem (Or.inr (Or.inl rfl)) 1)
    have v1 : ⁅gX rA t₁, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_au _ _)
    have v2 : ⁅gX rU t₂, gX rU (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v3 : ⁅gX rV t₃, gX rU (1 : K)⁆ = gX rC (1 * t₃) := by
      rw [← commutatorElement_inv, rel_uv, gX_inv]
    have v4 : ⁅gX rB t₄, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_ub 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_uc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact gX_c_mem_N1 _) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₄ : t₄ = 0 := by
    have st := hzg (gX rA 1) (hmem (Or.inl rfl) 1)
    have v1 : ⁅gX rA t₁, gX rA (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v2 : ⁅gX rU t₂, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_au 1 t₂).symm
    have v3 : ⁅gX rV t₃, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_av 1 t₃).symm
    have v4 : ⁅gX rB t₄, gX rA (1 : K)⁆ = gX rC (1 * t₄) := by
      rw [← commutatorElement_inv, rel_ab, gX_inv]
    have v5 : ⁅gX rC t₅, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_ac 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact gX_c_mem_N1 _) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  subst ht₁ ht₂ ht₃ ht₄
  exact ⟨t₅, by simp only [gX_zero, one_mul]⟩

theorem g2_commute_nr_c
    (x y : K) : Commute (gX rNR x) (gX rC y) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have r8 : ((6, 11, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have l6 : simple .G2 ⟨1, by decide⟩ • orbitCertRoot .G2 6 = rNR := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have l11 : simple .G2 ⟨1, by decide⟩ • orbitCertRoot .G2 11 = rC := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  exact commute_pinnedX_of_two_eq_zero h2 r8 rfl _ l6 l11 x y

omit [CharP K 2] in
theorem closure_xy_eq_rootSpan
    {τ : Tag} (i : Fin τ.rank) :
    Subgroup.closure {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K,
        g = xUnit τ K j c ∨ g = yUnit τ K j c} =
      rootSpan τ K {Pi.single i 1, -Pi.single i 1} := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩ <;> rw [Set.mem_singleton_iff] at hj <;> subst hj
    · rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan (Set.mem_insert _ _) c
    · rw [← pinnedX_neg_single]
      exact pinnedX_mem_rootSpan (Set.mem_insert_of_mem _ (Set.mem_singleton _)) c
  · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases hα with rfl | hα
    · rw [pinnedX_single]
      exact Subgroup.subset_closure ⟨i, rfl, c, Or.inl rfl⟩
    · rw [Set.mem_singleton_iff.1 hα, pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨i, rfl, c, Or.inr rfl⟩

omit [CharP K 2] in
theorem g2_perfectCore_le
    [Finite K] (i : Fin Tag.G2.rank) :
    perfectCore (parabolicSubgroup Tag.G2 K {i}) ≤
      parabolicRadical Tag.G2 K {i} ⊔ rootSpan Tag.G2 K {Pi.single i 1, -Pi.single i 1} := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  set Q := parabolicRadical Tag.G2 K {i} with hQ
  set L := rootSpan Tag.G2 K {Pi.single i 1, -Pi.single i 1} with hL
  have hPeq : parabolicSubgroup Tag.G2 K {i} = (Q ⊔ L) ⊔ torusGroup Tag.G2 K := by
    rw [← parabolicRadical_sup_parabolicLevi {i}, parabolicLevi, closure_xy_eq_rootSpan,
      sup_comm (torusGroup Tag.G2 K) L, sup_assoc]
  have hQL : Q ⊔ L = rootSpan Tag.G2 K (parabolicRadicalRoots Tag.G2 {i} ∪
      {Pi.single i 1, -Pi.single i 1}) := by
    rw [hQ, hL, parabolicRadical]
    simp only [rootSpan]
    exact iSup_union.symm
  have hroots : ∀ α ∈ parabolicRadicalRoots Tag.G2 {i} ∪ {Pi.single i 1, -Pi.single i 1},
      IsRoot Tag.G2 α := by
    intro α hα
    rcases hα with hα | hα | hα
    · exact (radical_pos α hα).1
    · rw [hα]
      exact isRoot_single Tag.G2 i
    · rw [Set.mem_singleton_iff.1 hα]
      exact isRoot_neg_single Tag.G2 i
  have hT : torusGroup Tag.G2 K ≤
      Subgroup.normalizer ((Q ⊔ L : Subgroup (ModGL Tag.G2 K)) : Set (ModGL Tag.G2 K)) := by
    rw [hQL]
    exact torusGroup_le_normalizer_rootSpan hroots
  have hle : Q ⊔ L ≤ parabolicSubgroup Tag.G2 K {i} := by
    rw [hPeq]
    exact le_sup_left
  have hnorm : ((Q ⊔ L).subgroupOf (parabolicSubgroup Tag.G2 K {i})).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, hPeq]
    exact sup_le Subgroup.le_normalizer hT
  have hsolv : Group.IsSolvable ↥(torusGroup Tag.G2 K) := by
    have : IsMulCommutative ↥(torusGroup Tag.G2 K) :=
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_diagonalGroup
        (torusGroup_le_diagonalGroup a.2) (torusGroup_le_diagonalGroup b.2))⟩⟩
    infer_instance
  exact perfectCore_le_of_sup_solvable hle hnorm hPeq hsolv

theorem g2_eq_one_zero
    [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) {z : ModGL Tag.G2 K}
    (hzU : z ∈ posUnipotent Tag.G2 K)
    (hzB : ∀ x ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}), z * x = x * z) : z = 1 := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hQP : parabolicRadical Tag.G2 K {i0} ≤ parabolicSubgroup Tag.G2 K {i0} :=
    (parabolicRadical_le_posUnipotent {i0}).trans (posUnipotent_le_parabolicSubgroup {i0})
  have hQB := (generated_zero (K := K) hK4).trans (commutator_perfectCore_le_of_le hQP)
  have hzC : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K)) :=
    Subgroup.mem_centralizer_iff.2 fun q hq => (hzB q (hQB hq)).symm
  have hJ : ({i0} : Set (Fin Tag.G2.rank)) ≠ Set.univ := fun h =>
    absurd (Set.mem_singleton_iff.1 (h ▸ Set.mem_univ i1)) (by decide)
  have hzQ := (Chevalley_proper_parabolic_root_radical_self_centralizing Tag.G2 K hJ).2
    ⟨posUnipotent_le_parabolicSubgroup {i0} hzU, hzC⟩
  obtain ⟨s, t, rfl⟩ := g2_center_zero hzQ hzC
  obtain ⟨L, hLP, hL, -, -, hh⟩ := leviL_data hK4 i0
  obtain ⟨u, hu⟩ := exists_units_ne_one (K := K) hK4
  have hd := hzB _ (le_perfectCore_of_perfect hLP hL (hh u))
  have hbR : IsRoot Tag.G2 rB := (isRoot_pos_iff.2 (by simp)).1
  have hcR : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1
  have e1 : ∑ j, Tag.G2.cartan i0 j * rB j = -1 := by decide
  have e2 : ∑ j, Tag.G2.cartan i0 j * rC j = 1 := by decide
  set d := torusElt Tag.G2 K i0 u with hdd
  have eb : d * gX rB s * d⁻¹ = gX rB (((u ^ (-1 : ℤ) : Kˣ) : K) * s) := by
    have h := root_torus_conjugation (τ := Tag.G2) (R := K) i0 hbR u s
    rw [e1] at h
    exact h
  have ec : d * gX rC t * d⁻¹ = gX rC (((u ^ (1 : ℤ) : Kˣ) : K) * t) := by
    have h := root_torus_conjugation (τ := Tag.G2) (R := K) i0 hcR u t
    rw [e2] at h
    exact h
  have E0 : d * (gX rB s * gX rC t) * d⁻¹ = gX rB s * gX rC t := by
    rw [← hd]
    group
  have E : gX rB (((u ^ (-1 : ℤ) : Kˣ) : K) * s) * gX rC (((u ^ (1 : ℤ) : Kˣ) : K) * t) =
      gX rB s * gX rC t := by
    rw [← eb, ← ec]
    calc d * gX rB s * d⁻¹ * (d * gX rC t * d⁻¹) = d * (gX rB s * gX rC t) * d⁻¹ := by group
      _ = gX rB s * gX rC t := E0
  have key : gX rB (((u ^ (-1 : ℤ) : Kˣ) : K) * s + s) *
      gX rC (((u ^ (1 : ℤ) : Kˣ) : K) * t + t) = 1 := by
    calc gX rB (((u ^ (-1 : ℤ) : Kˣ) : K) * s + s) * gX rC (((u ^ (1 : ℤ) : Kˣ) : K) * t + t) =
        gX rB s * (gX rB (((u ^ (-1 : ℤ) : Kˣ) : K) * s) *
          gX rC (((u ^ (1 : ℤ) : Kˣ) : K) * t)) * gX rC t := by
          rw [gX_add, gX_add, (gX_comm_self rB _ s).eq]
          simp only [mul_assoc]
      _ = 1 := by rw [E, ← mul_assoc, gX_self, one_mul, gX_self]
  obtain ⟨h1, h2⟩ := prod_bc_eq_one key
  rw [eq_zero_of_mul_add_self (zpow_val_ne_one hu (Or.inr rfl)) h1,
    eq_zero_of_mul_add_self (zpow_val_ne_one hu (Or.inl rfl)) h2, gX_zero, gX_zero, one_mul]

theorem g2_comm_one
    [Finite K] {v : ModGL Tag.G2 K} (hvQ : v ∈ parabolicRadical Tag.G2 K {i1})
    (hvC : v ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)))
    {x : ModGL Tag.G2 K} (hx : x ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1})) :
    x * v = v * x := by
  obtain ⟨t, rfl⟩ := g2_center_one hvQ hvC
  have hneg : -Pi.single i1 (1 : ℤ) = rNR := by
    funext k
    rcases fin_two_cases k with rfl | rfl <;> decide
  have hcent : parabolicRadical Tag.G2 K {i1} ⊔
      rootSpan Tag.G2 K {Pi.single i1 1, -Pi.single i1 1} ≤
        Subgroup.centralizer {gX rC t} := by
    refine sup_le (fun q hq => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (N1_le_centralizer (gX_c_mem_N1 t)) q hq)
    · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rcases hα with rfl | hα
      · rw [single_i1]
        exact Subgroup.mem_centralizer_singleton_iff.2 (comm_rc c t).eq
      · rw [Set.mem_singleton_iff.1 hα, hneg]
        exact Subgroup.mem_centralizer_singleton_iff.2 (g2_commute_nr_c c t).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hcent (g2_perfectCore_le i1 hx))

variable [Finite K]

theorem zcentFor_G2
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.G2 K)) : ZCentFor ↥(adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4' : ∃ s : Finset K, s.card = 4 := by
    refine Vol2Native.A312L.exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  choose g hg hker using fun j : Fin 2 =>
    Vol2Native.A312L.exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf2 (g2Index j)
  have := Vol2Native.A312L.sl2_isSimple hK4'
  refine ZCentFor.of_sylow _ hU₀ fun B hB hBtop z => ?_
  obtain ⟨j, rfl⟩ := Vol2Native.A312L.rank2_eq_perfectCore hq G2_residualOvergroupsAt
    (fun j => ⟨SL2 K, inferInstance, inferInstance, Vol2Native.A312L.sl2_nonabelian hK4', g j,
      hg j, by have := (hker j).isNilpotent; infer_instance⟩) hB hBtop
  have hPC : ∀ i, parabolicSubgroup Tag.G2 K {i} ≤ adjointGroup Tag.G2 K := fun i =>
    parabolicSubgroup_le_adjointGroup _ _ _
  have hcore : ∀ i, ∀ x ∈ perfectCore (parabolicSubgroup Tag.G2 K {i}), ∃ b ∈
      perfectCore ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)),
        (b : ModGL Tag.G2 K) = x := fun i x hx => by
    rw [← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC i)] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨b, hb, rfl⟩
  intro hzT hz1 _ hzB
  rcases fin_two_cases (g2Index j) with hj | hj <;> rw [hj] at hzB ⊢
  · exfalso
    refine hz1 (Subtype.ext (g2_eq_one_zero hK hf2 hzT fun x hx => ?_))
    obtain ⟨b, hb, rfl⟩ := hcore i0 x hx
    exact congrArg Subtype.val (hzB b hb)
  · intro v hv hvc _ b hb
    set Q := parabolicRadical Tag.G2 K {i1} with hQdef
    have hQP : Q ≤ parabolicSubgroup Tag.G2 K {i1} :=
      (parabolicRadical_le_posUnipotent {i1}).trans (posUnipotent_le_parabolicSubgroup {i1})
    have hQB := (generated_one (K := K) hK4).trans (commutator_perfectCore_le_of_le hQP)
    have hQO : Q.subgroupOf (adjointGroup Tag.G2 K) ≤ pCoreOf 2 (perfectCore
        ((parabolicSubgroup Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K))) :=
      subgroupOf_le_pCoreOf (pGroup_radical hK {i1}) (fun q hq => hcore i1 q (hQB hq))
        fun b hb => parabolicSubgroup_le_normalizer_parabolicRadical {i1}
          (Subgroup.mem_subgroupOf.1 (perfectCore_le _ hb))
    have hvC : (v : ModGL Tag.G2 K) ∈
        Subgroup.centralizer (Q : Set (ModGL Tag.G2 K)) := by
      refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
      have hqC : q ∈ adjointGroup Tag.G2 K := hPC i1 (hQP hq)
      exact congrArg Subtype.val (hvc ⟨q, hqC⟩ (hQO hq))
    have hvB : v ∈ perfectCore ((parabolicSubgroup Tag.G2 K {i1}).subgroupOf
        (adjointGroup Tag.G2 K)) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hv
    have hvP : (v : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i1} :=
      Subgroup.mem_subgroupOf.1 (perfectCore_le _ hvB)
    have hJ : ({i1} : Set (Fin Tag.G2.rank)) ≠ Set.univ := fun h =>
      absurd (Set.mem_singleton_iff.1 (h ▸ Set.mem_univ i0)) (by decide)
    have hvQ := (Chevalley_proper_parabolic_root_radical_self_centralizing Tag.G2 K hJ).2
      ⟨hvP, hvC⟩
    have hb' : (b : ModGL Tag.G2 K) ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1}) := by
      rw [← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC i1)]
      exact ⟨b, hb, rfl⟩
    exact Subtype.ext (g2_comm_one hvQ hvC hb')

end G2

theorem zcentFor_of_isG2
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {f : ℕ} (h : IsG2 2 f X) :
    ZCentFor X := by
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model h
  exact ZCentFor.of_mulEquiv e (zcentFor_G2 hK hf (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq))

end CFSG.Quasithin.Vol2.Ch10.A312A
