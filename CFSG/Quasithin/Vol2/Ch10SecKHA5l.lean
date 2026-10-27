module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5k
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Sp4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique
  CFSG.QuasithinUnique.A5.G3

section Sp4

variable {K : Type} [Field K] [Finite K]

theorem sl25_comm_data [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2)
    (hD : IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q2 K j)))
    (u : ↥(CFSG.Quasithin.perfectCore (Q2 K j)))
    (hu : u ∈ CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K j))) :
    ∃ x : ↥(CFSG.Quasithin.perfectCore (Q2 K j)), blkN j u = 1 ∧ (blkN j x) ^ 3 = 1 ∧
      blkN j x ≠ 1 ∧ x * u = u * x := by
  have := sl2_isSimple hK4
  have hpc : CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K j)) = (blkN j).ker :=
    pCore_two_eq_ker (sl2_nonabelian hK4) (blkN j) (blkN_surjective hK4 j)
      (blkN_ker_isPGroup hK j)
  obtain ⟨x, hx3, hxu⟩ := hD.three u hu
  have hx : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hxk : blkN j x ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨x, MonoidHom.mem_ker.mpr h1⟩
    have h2 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  exact ⟨x, MonoidHom.mem_ker.mp (hpc ▸ hu), by rw [← map_pow, hx, map_one], hxk, hxu⟩

theorem sl25_shape0 [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4)
    (hD : IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q2 K 0)))
    (u : ↥(CFSG.Quasithin.perfectCore (Q2 K 0)))
    (hu : u ∈ CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K 0))) :
    ∃ p : K, spMat (u : StatedSp 2 K) = zMat0 p := by
  obtain ⟨x, hu0, hx3, hx1, hxu⟩ := sl25_comm_data hK hK4 0 hD u hu
  exact N0_key x u hu0 hxu hx3 hx1

theorem sl25_shape1 [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4)
    (hD : IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q2 K 1)))
    (u : ↥(CFSG.Quasithin.perfectCore (Q2 K 1)))
    (hu : u ∈ CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K 1))) :
    ∃ C : Matrix (Fin 2) (Fin 2) K, Cᵀ = C ∧ spMat (u : StatedSp 2 K) = blockMat 1 C ∧
      C 0 0 = 0 ∧ C 1 1 = 0 := by
  obtain ⟨x, hu0, hx3, hx1, hxu⟩ := sl25_comm_data hK hK4 1 hD u hu
  obtain ⟨C, hC, hM, h00, h11⟩ := N1_fixed x u hu0 hxu
  obtain ⟨e0, e1⟩ := sl2_twisted_fixed (blkN 1 x) hx3 hx1 (C 0 0) (C 1 1) h00 h11
  exact ⟨C, hC, hM, e0, e1⟩

theorem sl25_card_pCore_le_zero [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4)
    (hD : IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q2 K 0))) :
    Nat.card (CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K 0))) ≤ Nat.card K := by
  let F : ↥(CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K 0))) → K := fun u =>
    spMat ((u : ↥(CFSG.Quasithin.perfectCore (Q2 K 0))) : StatedSp 2 K) (Sum.inl 0) (Sum.inr 0)
  refine Nat.card_le_card_of_injective F ?_
  intro u v huv
  obtain ⟨p, hp⟩ := sl25_shape0 hK hK4 hD u u.2
  obtain ⟨q, hq⟩ := sl25_shape0 hK hK4 hD v v.2
  have hFu : F u = p := by simp [F, hp, zMat0]
  have hFv : F v = q := by simp [F, hq, zMat0]
  have hpq : p = q := hFu.symm.trans (huv.trans hFv)
  apply Subtype.ext
  apply Subtype.ext
  apply statedSp_ext
  show spMat _ = spMat _
  rw [hp, hq, hpq]

theorem sl25_card_pCore_le_one [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4)
    (hD : IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q2 K 1))) :
    Nat.card (CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K 1))) ≤ Nat.card K := by
  let F : ↥(CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q2 K 1))) → K := fun u =>
    spMat ((u : ↥(CFSG.Quasithin.perfectCore (Q2 K 1))) : StatedSp 2 K) (Sum.inl 0) (Sum.inr 1)
  refine Nat.card_le_card_of_injective F ?_
  intro u v huv
  obtain ⟨Cu, hCu, hu', hu00, hu11⟩ := sl25_shape1 hK hK4 hD u u.2
  obtain ⟨Cv, hCv, hv', hv00, hv11⟩ := sl25_shape1 hK hK4 hD v v.2
  have hFu : F u = Cu 0 1 := by simp [F, hu', blockMat]
  have hFv : F v = Cv 0 1 := by simp [F, hv', blockMat]
  have h01 : Cu 0 1 = Cv 0 1 := hFu.symm.trans (huv.trans hFv)
  have hsu : Cu 1 0 = Cu 0 1 := congrFun (congrFun hCu 0) 1
  have hsv : Cv 1 0 = Cv 0 1 := congrFun (congrFun hCv 0) 1
  have hC : Cu = Cv := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hu00, hv00, hu11, hv11, h01, hsu, hsv]
  apply Subtype.ext
  apply Subtype.ext
  apply statedSp_ext
  show spMat _ = spMat _
  rw [hu', hv', hC]

theorem not_isSL25_perfectCore_Q2 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf2 : 2 ≤ f) (j : Fin 2) : ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q2 K j)) := by
  intro hD
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4' : 4 ≤ Nat.card K := by
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4'
  have hle : 32 ≤ Nat.card K := by
    have h32 := hD.card_pCore
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) j with rfl | rfl
    · have := sl25_card_pCore_le_zero hK hK4 hD
      omega
    · have := sl25_card_pCore_le_one hK hK4 hD
      omega
  have hdvd : Nat.card (SpecialLinearGroup (Fin 2) K) ∣
      Nat.card ↥(CFSG.Quasithin.perfectCore (Q2 K j)) :=
    Subgroup.card_dvd_of_surjective (blkN_surjective hK4 j)
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hD.card] at hdvd
  have hle2 := Nat.le_of_dvd (by norm_num) hdvd
  have h1 : 1024 ≤ Nat.card K ^ 2 := by nlinarith
  have h2 : 1023 ≤ Nat.card K ^ 2 - 1 := by omega
  have h3 : 32 * 1023 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul hle h2
  omega

theorem not_isSL25_perfectCore_of_projSp4 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf2 : 2 ≤ f) {Pa : Subgroup (StatedProj (StatedSp 2 K))}
    (hpar : CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) Pa)
    (hne : Pa ≠ ⊤) : ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore Pa) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : ∀ j : Fin 2, ∀ x ∈ CFSG.Quasithin.perfectCore (Q2 K j),
      ∀ y ∈ CFSG.Quasithin.perfectCore (Q2 K j), proj 2 K x = proj 2 K y → x = y :=
    fun j x _ y _ h => proj_injective_charTwo h
  refine not_isSL25_perfectCore_parabolic hU hres (fun j h => ?_) hpar hne
  exact not_isSL25_perfectCore_Q2 hf hf2 j
    (h.of_equiv (perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)).symm)

end Sp4

theorem not_isSL25_perfectCore_sp4 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : CFSG.Quasithin.IsPSp4 2 f ↥L)
    (hP : CFSG.Quasithin.IsMaxParabolic2 L P) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isSL25_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  exact not_isSL25_perfectCore_of_equiv e
    (not_isSL25_perfectCore_of_projSp4 hcard hf (isParabolic2_top_map_equiv e hpa)
      (map_ne_top_of_equiv e hna))

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
