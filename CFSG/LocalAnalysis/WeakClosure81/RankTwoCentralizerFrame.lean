module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IP
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ
public import CFSG.LocalAnalysis.WeakClosure81.PerfectPSL2Actions

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Quasithin CFSG.Open Subgroup Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem nParam_centralizer_le_one_of_rankTwoFrame
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G}
    {K : Type} [Field K]
    {U : Subgroup (GL (Fin 2) K)} (π : U →* G)
    (hπrange : π.range = L ⊓ Subgroup.centralizer ({z} : Set G))
    (hCube : ClassicalInvolution.Q3.TA3.Q5GL2.CubeKer π)
    {F : Type} [Field F] [Finite F]
    (eSl : ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ≃* SL(2, F))
    {p f : ℕ} (hp : p.Prime) (hq5 : 5 < p ^ f)
    (hFcard : Nat.card F = p ^ f)
    (hSLC : ClassicalInvolution.Q3.TA3.Q5GL2.SLCentScalar U)
    (N1 : U) (hN1 : (N1 : GL (Fin 2) K) = -1) (hπN1 : π N1 = z)
    (hSquare : ∀ A : U, A * A ∈
      ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ⊔ Subgroup.center U)
    (hbound : ∀ (J B : Subgroup G), Group.IsPerfect J → J ≤ B →
      B ≤ Subgroup.normalizer (J : Set G) →
      IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J) →
      Group.IsSolvable ↥((Subgroup.centralizer (J : Set G)).subgroupOf B) →
      (∀ b : B, ∃ k : ℕ, b ^ 2 ^ k ∈ J.subgroupOf B ⊔
        (Subgroup.centralizer (J : Set G)).subgroupOf B) →
      E1.nParam B ≤ 1) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let CLJ : Subgroup G := L ⊓ Subgroup.centralizer
    ((π.comp (ClassicalInvolution.Q3.TA3.Q5GL2.slPart U).subtype).range : Set G)
  let J : Subgroup G := (π.comp (ClassicalInvolution.Q3.TA3.Q5GL2.slPart U).subtype).range
  have hJ_eq_map : J = (ClassicalInvolution.Q3.TA3.Q5GL2.slPart U).map π := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, A.2, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨⟨A, hA⟩, rfl⟩
  have hJleRange : J ≤ π.range := by
    rintro x ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  have hJC : J ≤ C := hJleRange.trans (by rw [hπrange]; exact inf_le_right)
  have hJperf : Group.IsPerfect J := by
    let eJ0 : ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ≃* J :=
      MonoidHom.ofInjective (ClassicalInvolution.Q3.TA3.Q5GL2.injective_slPart hCube)
    let eJ : J ≃* SL(2, F) := eJ0.symm.trans eSl
    have h4 : 4 ≤ Nat.card F := by omega
    exact ClassicalInvolution.isPerfect_of_equiv_sl2 h4 eJ
  have hJeq : J = ⁅J, J⁆ := (Subgroup.isPerfect_iff.mp hJperf).symm
  have hJleComm : J ≤ ⁅π.range, π.range⁆ := by
    rw [hJeq]
    exact Subgroup.commutator_mono hJleRange hJleRange
  have hcommLe : ⁅π.range, π.range⁆ ≤ J := by
    rw [hJ_eq_map]
    exact ClassicalInvolution.Q3.TA3.Q5GL2.commutator_range_le π
  have hJeqComm : J = ⁅π.range, π.range⁆ := le_antisymm hJleComm hcommLe
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hAS.normal]
    exact le_top
  have hCnormInf : C ≤ Subgroup.normalizer (L ⊓ C : Subgroup G) := by
    intro c hc
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (H := L) (K := C) ⟨hCL hc, Subgroup.le_normalizer hc⟩
  have hCnormRange : C ≤ Subgroup.normalizer (π.range : Set G) := by
    rw [hπrange]
    exact hCnormInf
  have hCnormJ : C ≤ Subgroup.normalizer (J : Set G) := by
    intro c hc
    rw [hJeqComm]
    exact Vol2.Ch11.SecU1.L3I.mem_normalizer_commutator (hCnormRange hc)
  have hzJ : z ∈ J := by
    have hN1sl : N1 ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart U := by
      rw [ClassicalInvolution.Q3.TA3.Q5GL2.mem_slPart]
      rw [hN1]
      have hdet : GeneralLinearGroup.det (-1 : GL (Fin 2) K) = 1 := by
        apply Units.ext
        change (((-1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) = (1 : K)
        rw [show ((-1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 by rfl]
        rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
        norm_num
      exact hdet
    rw [← hπN1]
    exact ⟨⟨N1, hN1sl⟩, rfl⟩
  have hCJleC : Subgroup.centralizer (J : Set G) ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx z hzJ).symm
  have hCLJcomm : ∀ a b : ↥CLJ, a * b = b * a := by
    intro a b
    have haL : (a : G) ∈ L := a.2.1
    have hbL : (b : G) ∈ L := b.2.1
    have haC : (a : G) ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp a.2.2 z hzJ).symm
    have hbC : (b : G) ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp b.2.2 z hzJ).symm
    have haRange : (a : G) ∈ π.range := by
      rw [hπrange]
      exact ⟨haL, haC⟩
    have hbRange : (b : G) ∈ π.range := by
      rw [hπrange]
      exact ⟨hbL, hbC⟩
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp haRange
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hbRange
    have hAcomm : ∀ B' ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart U,
        π A * π B' = π B' * π A := by
      intro B' hB'
      rw [hA]
      exact (Subgroup.mem_centralizer_iff.mp a.2.2 (π B') ⟨⟨B', hB'⟩, rfl⟩).symm
    have hBcomm : ∀ A' ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart U,
        π B * π A' = π A' * π B := by
      intro A' hA'
      rw [hB]
      exact (Subgroup.mem_centralizer_iff.mp b.2.2 (π A') ⟨⟨A', hA'⟩, rfl⟩).symm
    obtain ⟨cA, hcA⟩ :=
      ClassicalInvolution.Q3.TA3.Q5GL2.exists_scalar_of_commute hCube hSLC hAcomm
    obtain ⟨cB, hcB⟩ :=
      ClassicalInvolution.Q3.TA3.Q5GL2.exists_scalar_of_commute hCube hSLC hBcomm
    have hAB : (A : GL (Fin 2) K) * (B : GL (Fin 2) K) =
        (B : GL (Fin 2) K) * (A : GL (Fin 2) K) := by
      rw [hcA, hcB, ClassicalInvolution.Q3.TA3.Q5GL2.scalar_mul_comm]
    have hABU : A * B = B * A := Subtype.ext hAB
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    calc (a : G) * (b : G) = π (A * B) := by rw [map_mul, hA, hB]
      _ = π (B * A) := by rw [hABU]
      _ = (b : G) * (a : G) := by rw [map_mul, hB, hA]
  have hCLJsolv : Group.IsSolvable ↥CLJ :=
    Group.isSolvable_of_comm hCLJcomm
  have hCs : Group.IsSolvable ↥((Subgroup.centralizer (J : Set G)).subgroupOf C) := by
    have hCJsolv : Group.IsSolvable ↥(Subgroup.centralizer (J : Set G)) :=
      Vol2.Ch11.SecU1.L3I.isSolvable_centralizer_of_inf hAS hCLJsolv
    haveI : Group.IsSolvable ↥(Subgroup.centralizer (J : Set G)) := hCJsolv
    exact CFSG.GorensteinWalter.isSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hCJleC).symm
  have hcenterJ : (Subgroup.center U).map π ≤ CLJ := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxrange : π A ∈ π.range := ⟨A, rfl⟩
      rw [hπrange] at hxrange
      exact hxrange.1
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hj
      have hcommU : A * (B : U) = (B : U) * A :=
        (Subgroup.mem_center_iff.mp hA (B : U)).symm
      have hπcomm : π A * π B = π B * π A := by
        simpa [map_mul] using congrArg π hcommU
      rw [← hB]
      exact hπcomm.symm
  have hSquareLJ : ∀ c : ↥(L ⊓ C), (c : G) * (c : G) ∈ J ⊔ CLJ := by
    intro c
    have hcRange : (c : G) ∈ π.range := by
      rw [hπrange]
      exact c.2
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hcRange
    have hmap_le : (ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ⊔
        Subgroup.center U).map π ≤ J ⊔ CLJ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [← hJ_eq_map]
        exact le_sup_left
      · exact hcenterJ.trans le_sup_right
    have hmap : π (A * A) ∈ J ⊔ CLJ :=
      hmap_le (Subgroup.mem_map_of_mem π (hSquare A))
    have heq : π (A * A) = (c : G) * (c : G) := by rw [map_mul, hA]
    rwa [heq] at hmap
  have hpow : ∀ b : C, ∃ k : ℕ, b ^ 2 ^ k ∈ J.subgroupOf C ⊔
      (Subgroup.centralizer (J : Set G)).subgroupOf C := by
    intro b
    obtain ⟨k, hkL⟩ := hAS.two (b : G)
    have hkC : (b : G) ^ 2 ^ k ∈ C := C.pow_mem b.2 _
    have hkc : (b : G) ^ 2 ^ k ∈ L ⊓ C := Subgroup.mem_inf.mpr ⟨hkL, hkC⟩
    have hsq' : ((b : G) ^ 2 ^ k) * ((b : G) ^ 2 ^ k) ∈ J ⊔ CLJ := by
      simpa using hSquareLJ ⟨(b : G) ^ 2 ^ k, hkc⟩
    have hsq : ((b : G) ^ 2 ^ k) * ((b : G) ^ 2 ^ k) ∈
        J ⊔ Subgroup.centralizer (J : Set G) :=
      (show J ⊔ CLJ ≤ J ⊔ Subgroup.centralizer (J : Set G) from
        sup_le le_sup_left (inf_le_right.trans le_sup_right :
          CLJ ≤ J ⊔ Subgroup.centralizer (J : Set G))) hsq'
    refine ⟨k + 1, ?_⟩
    have hmemSup : (b : G) ^ 2 ^ (k + 1) ∈ J ⊔
        Subgroup.centralizer (J : Set G) := by
      have heq : (b : G) ^ 2 ^ (k + 1) =
          ((b : G) ^ 2 ^ k) * ((b : G) ^ 2 ^ k) := by
        rw [← pow_add]
        congr 1
        ring
      rw [heq]
      exact hsq
    rw [← Subgroup.subgroupOf_sup hJC hCJleC]
    exact Subgroup.mem_subgroupOf.mpr hmemSup
  exact hbound J C hJperf hJC hCnormJ (by
    have hPSL : IsPSL 2 p f (↥J ⧸ Subgroup.center ↥J) := by
      change CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 p f
      refine ⟨?_, ?_⟩
      · have hf1 : 1 ≤ f := by
          rcases Nat.eq_zero_or_pos f with hf0 | hfpos
          · rw [hf0, pow_zero] at hq5
            omega
          · exact hfpos
        refine ⟨hp, hf1, by norm_num, ?_, ?_⟩
        · intro h
          have := congrArg Prod.snd h
          omega
        · intro h
          have := congrArg Prod.snd h
          omega
      · let eJ0 : ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ≃* J :=
          MonoidHom.ofInjective (ClassicalInvolution.Q3.TA3.Q5GL2.injective_slPart hCube)
        let eJ : J ≃* SL(2, F) := eJ0.symm.trans eSl
        refine ⟨F, inferInstance, inferInstance, hFcard, ⟨?_⟩⟩
        exact (Vol2.Ch11.SecU1.L3I.quotCenterEquiv eJ).trans
          (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)
    exact hPSL) hCs hpow

theorem nParam_centralizer_le_one_of_rankTwoFrame_narrow
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G}
    {K : Type} [Field K]
    {U : Subgroup (GL (Fin 2) K)} (π : U →* G)
    (hπrange : π.range = L ⊓ Subgroup.centralizer ({z} : Set G))
    (hCube : ClassicalInvolution.Q3.TA3.Q5GL2.CubeKer π)
    {F : Type} [Field F] [Finite F]
    (eSl : ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ≃* SL(2, F))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (hFcard : Nat.card F = p ^ f)
    (hSLC : ClassicalInvolution.Q3.TA3.Q5GL2.SLCentScalar U)
    (N1 : U) (hN1 : (N1 : GL (Fin 2) K) = -1) (hπN1 : π N1 = z)
    (hSquare : ∀ A : U, A * A ∈
      ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ⊔ Subgroup.center U) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h3f : (3 : ℕ) ^ 3 ≤ p ^ f := by
    calc (3 : ℕ) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega : 0 < p) hf
  have hq5 : 5 < p ^ f := by
    have : (27 : ℕ) ≤ p ^ f := by simpa using h3f
    omega
  exact nParam_centralizer_le_one_of_rankTwoFrame hAS π hπrange hCube eSl
    hp hq5 hFcard hSLC N1 hN1 hπN1 hSquare
    (fun J B hJ hJB hBN hPSL hCs hpow =>
      nParam_le_one_of_normalized_perfect_psl2_two_action
        (p := p) (f := f) hp hp2 hf J B hJ hJB hBN hPSL hCs hpow)

theorem nParam_centralizer_le_one_of_rankTwoFrame_of_five_lt
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G}
    {K : Type} [Field K]
    {U : Subgroup (GL (Fin 2) K)} (π : U →* G)
    (hπrange : π.range = L ⊓ Subgroup.centralizer ({z} : Set G))
    (hCube : ClassicalInvolution.Q3.TA3.Q5GL2.CubeKer π)
    {F : Type} [Field F] [Finite F]
    (eSl : ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ≃* SL(2, F))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 < p ^ f)
    (hFcard : Nat.card F = p ^ f)
    (hSLC : ClassicalInvolution.Q3.TA3.Q5GL2.SLCentScalar U)
    (N1 : U) (hN1 : (N1 : GL (Fin 2) K) = -1) (hπN1 : π N1 = z)
    (hSquare : ∀ A : U, A * A ∈
      ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ⊔ Subgroup.center U) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 :=
  nParam_centralizer_le_one_of_rankTwoFrame hAS π hπrange hCube eSl
    hp hq5 hFcard hSLC N1 hN1 hπN1 hSquare
    (fun J B hJ hJB hBN hPSL hCs hpow =>
      nParam_le_one_of_normalized_perfect_psl2_two_action_of_five_lt
        (p := p) (f := f) hp hp2 hq5 J B hJ hJB hBN hPSL hCs hpow)

end CFSG.LocalAnalysis.WeakClosure81

end
