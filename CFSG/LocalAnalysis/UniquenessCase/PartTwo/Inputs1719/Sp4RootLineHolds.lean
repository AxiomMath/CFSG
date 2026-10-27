module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatHolds
public import CFSG.Quasithin.Vol2.Ch10SecKHK3D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.ClassicalGroups.Symplectic.Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_rootLine_statedSp_two {n r : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ 2 ^ n - 1)
    (E : Subgroup (StatedSp 2 K)) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ B : Subgroup (StatedSp 2 K), B ≤ E ∧ Nat.card B = r ∧
      ∃ Y₀ : Subgroup (StatedSp 2 K),
        Y₀ ≤ Subgroup.centralizer (B : Set (StatedSp 2 K)) ∧ IsL2 ↥Y₀ n := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  set q : ℕ := Nat.card K with hqdef
  have hq2 : 2 ≤ q := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n)
  have hq1 : 1 ≤ q := by omega
  have hrdq : r ∣ q - 1 := by
    rw [hK]
    exact hrd
  have hdvd : r ∣ Nat.card K - 1 := by
    rw [← hqdef]
    exact hrdq
  let T : Subgroup (StatedSp 2 K) := torus 2 K
  have hcardT : Nat.card T = (q - 1) ^ 2 := by
    dsimp only [T]
    rw [show torus 2 K = (torusHom (r := 2) (k := K)).range from rfl,
      ← Nat.card_congr (MonoidHom.ofInjective
        (torusHom_injective (r := 2) (k := K))).toEquiv, Nat.card_pi]
    simp [Nat.card_units, Finset.prod_const, Fintype.card_fin]
    rw [← hqdef]
  have hcardY : Nat.card (StatedSp 2 K) =
      (q - 1) ^ 2 * (q ^ 4 * (q + 1) ^ 2 * (q ^ 2 + 1)) := by
    rw [card_statedSp_two, ← hqdef]
    have hq2sub : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h := Nat.sq_sub_sq q 1
      rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
      rw [h, mul_comm]
    have hq4sub : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
      have h := Nat.sq_sub_sq (q ^ 2) 1
      rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
      rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, h, mul_comm]
    rw [hq4sub, hq2sub]
    ring
  have hqpos : 0 < q - 1 := by omega
  have hTindex : T.index = q ^ 4 * (q + 1) ^ 2 * (q ^ 2 + 1) := by
    have h := T.card_mul_index
    rw [hcardT, hcardY] at h
    exact Nat.mul_left_cancel (pow_pos hqpos 2) h
  have hrq : ¬ r ∣ q := by
    intro h
    have h1 : r ∣ q - (q - 1) := Nat.dvd_sub h hrdq
    rw [show q - (q - 1) = 1 by omega] at h1
    exact hr.not_dvd_one h1
  have hrq1 : ¬ r ∣ q + 1 := by
    intro h
    have h1 : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hrdq
    rw [show (q + 1) - (q - 1) = 2 by omega] at h1
    have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) h1
    have hr2 : r ≠ 2 := by omega
    exact hr2 (le_antisymm hle hr.two_le)
  have hrq2 : ¬ r ∣ q ^ 2 + 1 := by
    intro h
    have hq2m1 : r ∣ q ^ 2 - 1 := by
      have h := Nat.sq_sub_sq q 1
      rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
      rw [h]
      exact dvd_mul_of_dvd_right hrdq (q + 1)
    have h1 : r ∣ (q ^ 2 + 1) - (q ^ 2 - 1) := Nat.dvd_sub h hq2m1
    have hq2one : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
    rw [show (q ^ 2 + 1) - (q ^ 2 - 1) = 2 by omega] at h1
    have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) h1
    have hr2 : r ≠ 2 := by omega
    exact hr2 (le_antisymm hle hr.two_le)
  have hM_cop : Nat.Coprime r (q ^ 4 * (q + 1) ^ 2 * (q ^ 2 + 1)) := by
    have hqcop : Nat.Coprime r q := (hr.coprime_iff_not_dvd).2 hrq
    have hq1cop : Nat.Coprime r (q + 1) := (hr.coprime_iff_not_dvd).2 hrq1
    have hq2cop : Nat.Coprime r (q ^ 2 + 1) := (hr.coprime_iff_not_dvd).2 hrq2
    exact ((hqcop.pow_right 4).mul_right (hq1cop.pow_right 2)).mul_right hq2cop
  let PT : Sylow r ↥T := Classical.arbitrary _
  let P : Subgroup (StatedSp 2 K) := Subgroup.map T.subtype (PT : Subgroup ↥T)
  have hPp : IsPGroup r P := PT.isPGroup'.map T.subtype
  have hPindex : P.index = (PT : Subgroup ↥T).index * T.index :=
    Subgroup.index_map_subtype (PT : Subgroup ↥T)
  have hPT_cop : Nat.Coprime r (PT : Subgroup ↥T).index :=
    (hr.coprime_iff_not_dvd).2 PT.not_dvd_index
  have hP_cop : Nat.Coprime r P.index := by
    rw [hPindex]
    exact hPT_cop.mul_right (by rw [hTindex]; exact hM_cop)
  have hP_idx : ¬ r ∣ P.index := (hr.coprime_iff_not_dvd).1 hP_cop
  let Ps : Sylow r (StatedSp 2 K) := hPp.toSylow hP_idx
  have hPs_coe : (Ps : Subgroup (StatedSp 2 K)) = P := IsPGroup.toSylow_coe hPp hP_idx
  have hPs_le_T : (Ps : Subgroup (StatedSp 2 K)) ≤ T := by
    rw [hPs_coe]
    exact Subgroup.map_subtype_le _
  obtain ⟨P0, hEP0⟩ := hEel.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 K) P0 Ps
  have hconj : (P0 : Subgroup (StatedSp 2 K)).conjBy g =
      (Ps : Subgroup (StatedSp 2 K)) := by
    have h := congrArg (fun S : Sylow r (StatedSp 2 K) =>
      (S : Subgroup (StatedSp 2 K))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    rw [Subgroup.conjBy]
    convert h using 2
    ext x
    rfl
  have hEconj_le_T : E.conjBy g ≤ T := by
    have h1 : E.conjBy g ≤ (P0 : Subgroup (StatedSp 2 K)).conjBy g := by
      simpa [Subgroup.conjBy] using Subgroup.map_mono hEP0
    rw [hconj] at h1
    exact h1.trans hPs_le_T
  let roots : Subgroup Kˣ := rootsOfUnity r K
  have hroots_card : Nat.card roots = r :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := K) (d := r) hdvd
  let Tr : Subgroup (StatedSp 2 K) :=
    Subgroup.map (torusHom (r := 2) (k := K))
      (Subgroup.pi Set.univ (fun _ : Fin 2 => roots))
  have hcardPi : Nat.card ↥(Subgroup.pi Set.univ (fun _ : Fin 2 => roots)) = r ^ 2 := by
    calc Nat.card ↥(Subgroup.pi Set.univ (fun _ : Fin 2 => roots))
        = Nat.card {f : Fin 2 → Kˣ // ∀ i, f i ∈ roots} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun f => by rw [Subgroup.mem_pi]; simp))
      _ = Nat.card (Π i : Fin 2, ↥roots) :=
          Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ z => z ∈ roots))
      _ = r ^ 2 := by
          rw [Nat.card_pi]
          simp [hroots_card, Finset.prod_const, Fintype.card_fin]
  have hcardTr : Nat.card Tr = r ^ 2 := by
    dsimp only [Tr]
    rw [Subgroup.card_map_of_injective (torusHom_injective (r := 2) (k := K))]
    exact hcardPi
  have hEconj_card : Nat.card (E.conjBy g) = r ^ 2 := by
    rw [Subgroup.conjBy,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
  have hEconj_pow : ∀ x ∈ E.conjBy g, x ^ r = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    change (MulAut.conj g y) ^ r = 1
    rw [← map_pow, hEel.2 y hy, map_one]
  have hEconj_le_Tr : E.conjBy g ≤ Tr := by
    intro x hx
    have hxT : x ∈ (torusHom (r := 2) (k := K)).range := by
      simpa [T, torus] using hEconj_le_T hx
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 hxT
    have htpow : t ^ r = 1 := torusHom_injective (by rw [map_pow, ht, hEconj_pow x hx, map_one])
    refine Subgroup.mem_map.2 ⟨t, ?_, ht⟩
    rw [Subgroup.mem_pi]
    intro i _
    rw [mem_rootsOfUnity]
    simpa [Pi.pow_apply] using congrFun htpow i
  have hEconj_eq_Tr : E.conjBy g = Tr :=
    Subgroup.eq_of_le_of_card_ge hEconj_le_Tr (by rw [hcardTr, hEconj_card])
  let bHom : roots →* StatedSp 2 K :=
    (torusHom (r := 2) (k := K)).comp
      ((MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) (1 : Fin 2)).comp roots.subtype)
  let B0 : Subgroup (StatedSp 2 K) := Subgroup.map bHom ⊤
  have hbHom_inj : Function.Injective bHom := by
    intro a b hab
    have h1 : (Pi.mulSingle (1 : Fin 2) (a : Kˣ) : Fin 2 → Kˣ) =
        Pi.mulSingle (1 : Fin 2) (b : Kˣ) := torusHom_injective hab
    have h2 : (a : Kˣ) = (b : Kˣ) := by
      have := congrFun h1 (1 : Fin 2)
      simpa using this
    exact Subtype.ext h2
  have hB0_card : Nat.card B0 = r := by
    dsimp only [B0]
    rw [Subgroup.card_map_of_injective hbHom_inj, Subgroup.card_top, hroots_card]
  have hB0_le_Tr : B0 ≤ Tr := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨Pi.mulSingle (1 : Fin 2) (a : Kˣ), ?_, rfl⟩
    rw [Subgroup.mem_pi]
    intro i _
    rw [mem_rootsOfUnity, Pi.mulSingle_apply]
    by_cases hi : i = (1 : Fin 2)
    · rw [if_pos hi]
      exact (mem_rootsOfUnity r (a : Kˣ)).1 a.2
    · rw [if_neg hi, one_pow]
  have hB0_le_Econj : B0 ≤ E.conjBy g := by
    rw [hEconj_eq_Tr]
    exact hB0_le_Tr
  let Y0 : Subgroup (StatedSp 2 K) :=
    ((CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam
      (r := 2) (k := K) (0 : Fin 2) :
      Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K)).range
  have hY0_L2 : IsL2 ↥Y0 n := by
    dsimp only [Y0]
    exact isL2_lam_zero_range n (by rw [← hqdef]; exact hK) hn
  have hY0_le_centB0 : Y0 ≤ Subgroup.centralizer (B0 : Set (StatedSp 2 K)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hb
    exact (Subgroup.mem_centralizer_singleton_iff.1
      (lam_zero_range_le_centralizer (K := K) (a : Kˣ) hy)).symm
  let B : Subgroup (StatedSp 2 K) := Subgroup.map (MulAut.conj g⁻¹).toMonoidHom B0
  let Yt : Subgroup (StatedSp 2 K) := Subgroup.map (MulAut.conj g⁻¹).toMonoidHom Y0
  refine ⟨B, ?_, ?_, Yt, ?_, ?_⟩
  · have h2 : B ≤ (E.conjBy g).conjBy g⁻¹ := Subgroup.map_mono hB0_le_Econj
    have h3 : (E.conjBy g).conjBy g⁻¹ = E := by
      rw [Subgroup.conjBy_conjBy, inv_mul_cancel, Subgroup.conjBy_one]
    rwa [h3] at h2
  · dsimp only [B]
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hB0_card]
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.1 hb
    have hcomm : b0 * y0 = y0 * b0 :=
      Subgroup.mem_centralizer_iff.1 (hY0_le_centB0 hy0) b0 hb0
    change (MulAut.conj g⁻¹ b0) * (MulAut.conj g⁻¹ y0) =
      (MulAut.conj g⁻¹ y0) * (MulAut.conj g⁻¹ b0)
    rw [← map_mul, ← map_mul, hcomm]
  · have hL2 : IsL2 ↥Yt n :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        (Subgroup.equivMapOfInjective Y0 (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective) hY0_L2
    exact hL2

theorem k_Sp4RootLine_holds : K_Sp4RootLine := by
  classical
  intro Y _ _ n hY hq r hr hr3 hrd E hEel hEcard
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eP⟩⟩ := hY.statedClassicalModel (by decide)
  let : Fintype K := Fintype.ofFinite K
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  let eYSp : Y ≃* StatedSp 2 K :=
    eP.trans (CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.projEquivSp (F := K)).symm
  let E' : Subgroup (StatedSp 2 K) := Subgroup.map eYSp.toMonoidHom E
  have hE'el : IsElemAbelian r E' := hEel.map eYSp.toMonoidHom
  have hE'card : Nat.card E' = r ^ 2 := by
    dsimp only [E']
    rw [Subgroup.card_map_of_injective eYSp.injective, hEcard]
  obtain ⟨B', hB'E', hB'card, Y0', hY0'le, hY0'L2⟩ :=
    exists_rootLine_statedSp_two hKcard hn hr hr3 hrd E' hE'el hE'card
  let B : Subgroup Y := Subgroup.map eYSp.symm.toMonoidHom B'
  let Y0 : Subgroup Y := Subgroup.map eYSp.symm.toMonoidHom Y0'
  refine ⟨B, ?_, ?_, Y0, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.1 (hB'E' hb')
    have hb_eq : eYSp.symm b' = e := by
      rw [← heq]
      exact eYSp.symm_apply_apply e
    change eYSp.symm b' ∈ E
    rw [hb_eq]
    exact he
  · dsimp only [B]
    rw [Subgroup.card_map_of_injective eYSp.symm.injective, hB'card]
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have hcomm : b' * y' = y' * b' :=
      Subgroup.mem_centralizer_iff.1 (hY0'le hy') b' hb'
    have := congrArg (fun z : StatedSp 2 K => eYSp.symm z) hcomm
    simpa [map_mul] using this
  · have hL2 : IsL2 ↥Y0 n :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        (Subgroup.equivMapOfInjective Y0' eYSp.symm.toMonoidHom eYSp.symm.injective)
        hY0'L2
    exact hL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
