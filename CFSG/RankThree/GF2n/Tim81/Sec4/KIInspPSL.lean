module

public import CFSG.RankThree.GF2n.Tim81.Sec4.KIInspLinear
public import CFSG.CGT.T75N.L29Overgroup
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralQuot
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.GroupTheory.ElemAbelianLiftOddKernel
public import CFSG.GroupTheory.CentralOddQuotientLift
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public noncomputable section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.Open CFSG.CGT.Timmesfeld75
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n s : ℕ}

private theorem weakTI_map_mulEquiv {G L : Type*} [Group G] [Group L] {T : Subgroup G}
    (h : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T) (e : G ≃* L) :
    CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI (T.map e.toMonoidHom) := by
  intro t ht ht1 y hy hodd
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨y₀, rfl⟩ := e.surjective y
  have ht1' : t₀ ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have hcomm' : y₀ * t₀ = t₀ * y₀ := by
    apply e.injective
    simpa using hy
  have hodd' : Odd (orderOf y₀) := by
    rwa [← MulEquiv.orderOf_eq e y₀]
  have hN := h t₀ ht₀ ht1' y₀ hcomm' hodd'
  exact Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hN)

private theorem weakTI_of_map_mk_eq {Z : Subgroup (SpecialLinearGroup (Fin n) K)} [Z.Normal]
    (hZ : Z ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)) (hZodd : Odd (Nat.card Z))
    {T : Subgroup (SpecialLinearGroup (Fin n) K)} (hT : Assembly.IsElemAbelian 2 T)
    {Tbar : Subgroup (SpecialLinearGroup (Fin n) K ⧸ Z)} (hmap : T.map (QuotientGroup.mk' Z) = Tbar)
    (hwti : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI Tbar) :
    CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T := by
  intro t ht ht1 y hcomm hyodd
  have hTZ : T ⊓ Z = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd (CFSG.Open.IsElemAbelian.isPGroup hT) hZodd
  have htbar1 : QuotientGroup.mk' Z t ≠ 1 := by
    intro h
    have htZ : t ∈ Z := (QuotientGroup.eq_one_iff t).mp h
    have hbot : t ∈ T ⊓ Z := ⟨ht, htZ⟩
    rw [hTZ] at hbot
    exact ht1 (Subgroup.mem_bot.mp hbot)
  have hyodd' : Odd (orderOf (QuotientGroup.mk' Z y)) :=
    Odd.of_dvd_nat hyodd (orderOf_map_dvd (QuotientGroup.mk' Z) y)
  have hcomm' : QuotientGroup.mk' Z y * QuotientGroup.mk' Z t =
      QuotientGroup.mk' Z t * QuotientGroup.mk' Z y := by
    rw [← map_mul, ← map_mul, hcomm]
  have hmem := hwti (QuotientGroup.mk' Z t)
    (hmap ▸ Subgroup.mem_map_of_mem _ ht) htbar1 (QuotientGroup.mk' Z y) hcomm' hyodd'
  rw [CFSG.GroupTheory.normalizer_eq_comap_of_isElemAbelian_map_mk_eq hZ hZodd hT hmap]
  exact hmem

private theorem eq_bot_or_eq_top_of_sl_invariant {W : Submodule K (Fin n → K)} (hn : 2 ≤ n)
    (hW : ∀ x : SpecialLinearGroup (Fin n) K, ∀ w ∈ W,
      (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot
    have hS : ∀ g : ↥(StatedSL n K), ∀ w ∈ W.toAddSubgroup,
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) ∈ W.toAddSubgroup := by
      intro g w hw
      let A : SpecialLinearGroup (Fin n) K :=
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm g
      have hA : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) := by
        simpa [A] using CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K A
      have hmem : (A : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W :=
        hW A w (by simpa using hw)
      simpa [hA] using hmem
    have htop := CFSG.Quasithin.eq_top_of_slMulVec_mem (F := K) (n := n) hn
      (S := W.toAddSubgroup) hS (by simpa using hv) hv0
    exact Submodule.toAddSubgroup_injective (by simpa using htop)

private theorem exists_lift_wc_weakTI (hn : 1 ≤ n) (hKcard : Nat.card K = 2 ^ s)
    {T : Subgroup (projectiveSL n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set (projectiveSL n K))))
    (hwti : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T) :
    ∃ T₀ : Subgroup (SpecialLinearGroup (Fin n) K),
      Assembly.IsElemAbelian 2 T₀ ∧ T₀.map (proj n K) = T ∧
      WeaklyClosedIn T₀ (Subgroup.normalizer (T₀ : Set (SpecialLinearGroup (Fin n) K))) ∧
      CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T₀ := by
  classical
  let Z : Subgroup (SpecialLinearGroup (Fin n) K) := scalars n K
  let π : SpecialLinearGroup (Fin n) K →* projectiveSL n K := proj n K
  have hZnormal : Z.Normal := scalars_normal n K
  letI : Z.Normal := hZnormal
  have hZcenter : Z ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := scalars_le_center n K
  have hs1 : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    rw [hs0, pow_zero] at hKcard
    have h2 := Finite.one_lt_card (α := K)
    omega
  have hKodd : Odd (Nat.card K - 1) := by
    rw [hKcard]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hZodd : Odd (Nat.card Z) :=
    Odd.of_dvd_nat hKodd (card_scalars_dvd (n := n) hn)
  obtain ⟨T₀, hT₀, hmap₀⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_two_map_mk_eq_of_odd_card (N := Z) hZodd hT
  have hwc₀ : WeaklyClosedIn T₀ (Subgroup.normalizer (T₀ : Set (SpecialLinearGroup (Fin n) K))) :=
    CFSG.GroupTheory.weaklyClosedIn_of_map_mk_eq hZcenter hZodd hT₀ hmap₀ hwc
  have hwti₀ : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T₀ :=
    weakTI_of_map_mk_eq hZcenter hZodd hT₀ hmap₀ hwti
  refine ⟨T₀, hT₀, ?_, hwc₀, hwti₀⟩
  simpa [π, Z, proj] using hmap₀

private theorem exists_stage_one_data (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K)
    (hKcard : Nat.card K = 2 ^ s)
    {T : Subgroup (projectiveSL n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set (projectiveSL n K))))
    (hwti : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T) :
    ∃ (T₀ : Subgroup (SpecialLinearGroup (Fin n) K))
      (x : SpecialLinearGroup (Fin n) K) (T₁ : Subgroup (SpecialLinearGroup (Fin n) K)),
      Assembly.IsElemAbelian 2 T₀ ∧ T₀.map (proj n K) = T ∧
      T₁ = conjSubgroup x⁻¹ T₀ ∧
      (T₁ ≤ tvCenterSL (Pi.single (⟨0, by omega⟩ : Fin n) 1) ∨
        T₁ ≤ tvAxisSL (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀, hmap₀, hwc₀, hwti₀⟩ :=
    exists_lift_wc_weakTI (by omega) hKcard hT hwc hwti
  obtain ⟨S, hSN, hT₀S⟩ :=
    CentralTI.exists_sylow_le_normalizer (CFSG.Open.IsElemAbelian.isPGroup hT₀) hwc₀
  obtain ⟨U, hU⟩ := LinearFlag.exists_sylow_unitriangular (K := K) (p := 2) (n := n) (by omega)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) K) U S
  have hS_eq : (S : Subgroup (SpecialLinearGroup (Fin n) K)) =
      conjSubgroup x (U : Subgroup (SpecialLinearGroup (Fin n) K)) := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let T₁ : Subgroup (SpecialLinearGroup (Fin n) K) := conjSubgroup x⁻¹ T₀
  have hT₁ : Assembly.IsElemAbelian 2 T₁ :=
    hT₀.map (MulAut.conj x⁻¹).toMonoidHom
  have hT₁U : T₁ ≤ (U : Subgroup (SpecialLinearGroup (Fin n) K)) := by
    have hT₀C : T₀ ≤ conjSubgroup x (U : Subgroup (SpecialLinearGroup (Fin n) K)) := hS_eq ▸ hT₀S
    calc T₁ = conjSubgroup x⁻¹ T₀ := rfl
      _ ≤ conjSubgroup x⁻¹ (conjSubgroup x (U : Subgroup (SpecialLinearGroup (Fin n) K))) :=
          Subgroup.map_mono hT₀C
      _ = (U : Subgroup (SpecialLinearGroup (Fin n) K)) := by
          rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hU_N : (U : Subgroup (SpecialLinearGroup (Fin n) K)) ≤
      Subgroup.normalizer (T₁ : Set (SpecialLinearGroup (Fin n) K)) := by
    intro u hu
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hxux : x * u * x⁻¹ ∈ (S : Subgroup (SpecialLinearGroup (Fin n) K)) := by
      rw [hS_eq]
      exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hu
    have hconj : conjSubgroup (x * u * x⁻¹) T₀ = T₀ :=
      mem_normalizer_iff_conjSubgroup_eq.mp (hSN hxux)
    have h1 : conjSubgroup x (conjSubgroup u T₁) = conjSubgroup x T₁ := by
      calc conjSubgroup x (conjSubgroup u T₁)
          = conjSubgroup (x * u) T₁ := by rw [conjSubgroup_conjSubgroup]
        _ = conjSubgroup ((x * u) * x⁻¹) T₀ := by
            rw [show T₁ = conjSubgroup x⁻¹ T₀ from rfl, conjSubgroup_conjSubgroup]
        _ = conjSubgroup (x * u * x⁻¹) T₀ := by rw [mul_assoc]
        _ = T₀ := hconj
        _ = conjSubgroup x T₁ := by
            rw [show T₁ = conjSubgroup x⁻¹ T₀ from rfl, conjSubgroup_conjSubgroup,
              mul_inv_cancel, conjSubgroup_one]
    exact Subgroup.map_injective (MulAut.conj x).injective h1
  have hwc₁ : WeaklyClosedIn T₁ (Subgroup.normalizer (T₁ : Set (SpecialLinearGroup (Fin n) K))) :=
    ⟨Subgroup.le_normalizer,
      CentralTI.weaklyClosed_map_mulEquiv (MulAut.conj x⁻¹) hwc₀.2⟩
  have hwti₁ : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T₁ :=
    weakTI_map_mulEquiv hwti₀ (MulAut.conj x⁻¹)
  have hB_N : upperTriangular n K ≤
      Subgroup.normalizer (T₁ : Set (SpecialLinearGroup (Fin n) K)) := by
    have hNU : Subgroup.normalizer
        ((U : Subgroup (SpecialLinearGroup (Fin n) K)) :
          Set (SpecialLinearGroup (Fin n) K)) ≤
        Subgroup.normalizer (T₁ : Set (SpecialLinearGroup (Fin n) K)) :=
      CentralTI.normalizer_sylow_le_normalizer hwc₁ hT₁U hU_N
    rwa [hU, LinearFlag.normalizer_unitriangular] at hNU
  have hT₁U' : T₁ ≤ unitriangular n K := by
    rwa [hU] at hT₁U
  have hstage : T₁ ≤ tvCenterSL (Pi.single (⟨0, by omega⟩ : Fin n) 1) ∨
      T₁ ≤ tvAxisSL (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) :=
    le_tvCenterSL_or_le_tvAxisSL hn hq hT₁ hT₁U' hB_N hwti₁
  exact ⟨T₀, x, T₁, hT₀, hmap₀, rfl, hstage⟩

private theorem exists_conj_stage_one
    (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K) (hKcard : Nat.card K = 2 ^ s)
    {T : Subgroup (projectiveSL n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set (projectiveSL n K))))
    (hwti : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T)
    (g : projectiveSL n K) (hgen : T ⊔ conjSubgroup g T = ⊤) :
    ∃ (T₁ : Subgroup (SpecialLinearGroup (Fin n) K))
      (g' : SpecialLinearGroup (Fin n) K),
      T₁ ⊔ conjSubgroup g' T₁ ⊔ scalars n K = ⊤ ∧
      (T₁ ≤ tvCenterSL (Pi.single (⟨0, by omega⟩ : Fin n) 1) ∨
        T₁ ≤ tvAxisSL (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) := by
  classical
  let Z : Subgroup (SpecialLinearGroup (Fin n) K) := scalars n K
  let π : SpecialLinearGroup (Fin n) K →* projectiveSL n K := proj n K
  have hZnormal : Z.Normal := scalars_normal n K
  letI : Z.Normal := hZnormal
  obtain ⟨T₀, x, T₁, -, hmap₀, hT₁eq, hstage⟩ :=
    exists_stage_one_data hn hq hKcard hT hwc hwti
  obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk'_surjective Z g
  have hZmap : Z.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_bot]
    change (QuotientGroup.mk' Z) z = 1
    exact (QuotientGroup.eq_one_iff z).mpr hz
  have hmapπ : T₀.map π = T := hmap₀
  have hĝπ : π ĝ = g := hĝ
  have hgenSL : T₀ ⊔ conjSubgroup ĝ T₀ ⊔ Z = ⊤ := by
    have hmapS : (T₀ ⊔ conjSubgroup ĝ T₀ ⊔ Z).map π = ⊤ := by
      rw [Subgroup.map_sup, Subgroup.map_sup, map_conjSubgroup, hmapπ, hĝπ, hZmap, hgen]
      simp
    have hker : π.ker = Z := by
      change (proj n K).ker = scalars n K
      exact ker_proj n K
    have hcomap : Subgroup.comap π ((T₀ ⊔ conjSubgroup ĝ T₀ ⊔ Z).map π) =
        T₀ ⊔ conjSubgroup ĝ T₀ ⊔ Z := by
      rw [Subgroup.comap_map_eq, hker]
      exact sup_eq_left.mpr (by change Z ≤ T₀ ⊔ conjSubgroup ĝ T₀ ⊔ Z; exact le_sup_right)
    rw [← hcomap, hmapS, Subgroup.comap_top]
  let g' : SpecialLinearGroup (Fin n) K := (MulAut.conj x⁻¹) ĝ
  have hZconj : Z.map (MulAut.conj x⁻¹).toMonoidHom = Z := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨w, hw, rfl⟩
      exact Subgroup.Normal.conj_mem (inferInstance : Z.Normal) w hw x⁻¹
    · intro z hz
      exact ⟨(MulAut.conj x) z, Subgroup.Normal.conj_mem (inferInstance : Z.Normal) z hz x,
        by simp [MulAut.conj_apply]; group⟩
  have hgenT₁ : T₁ ⊔ conjSubgroup g' T₁ ⊔ Z = ⊤ := by
    have h := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hgenSL
    rw [Subgroup.map_sup, Subgroup.map_sup, map_conjSubgroup, hZconj,
      show T₀.map (MulAut.conj x⁻¹).toMonoidHom = T₁ from hT₁eq.symm,
      Subgroup.map_top_of_surjective _ (MulAut.conj x⁻¹).surjective] at h
    exact h
  refine ⟨T₁, g', ?_, hstage⟩
  simpa [Z] using hgenT₁

private theorem kiInsp_projectiveSL (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K)
    (hKcard : Nat.card K = 2 ^ s)
    (T : Subgroup (projectiveSL n K)) (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set (projectiveSL n K))))
    (hwti : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T) (g : projectiveSL n K)
    (hgen : T ⊔ conjSubgroup g T = ⊤) : False := by
  classical
  obtain ⟨T₁, g', hgenT₁, hstage⟩ :=
    exists_conj_stage_one hn hq hKcard hT hwc hwti g hgen
  have hWex : ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x ∈ T₁ ⊔ conjSubgroup g' T₁, ∀ w ∈ W,
        (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    by_cases hcenter : T₁ ≤ tvCenterSL (Pi.single (⟨0, by omega⟩ : Fin n) 1)
    · exact exists_invariant_of_le_tvCenterSL (by omega) hcenter
        (Pi.single_ne_zero_iff.mpr one_ne_zero) g'
    · exact exists_invariant_of_le_tvAxisSL (by omega) (hstage.resolve_left hcenter)
        (Pi.single_ne_zero_iff.mpr one_ne_zero) g'
  obtain ⟨W, hWbot, hWtop, hWinv⟩ := hWex
  have hstabT : T₁ ≤ LinearFlag.stabilizer W :=
    CFSG.CGT.T75N.le_stabilizer_of_invariant T₁ W fun y hy =>
      hWinv y (Subgroup.mem_sup_left hy)
  have hstabC : conjSubgroup g' T₁ ≤ LinearFlag.stabilizer W :=
    CFSG.CGT.T75N.le_stabilizer_of_invariant (conjSubgroup g' T₁) W fun y hy =>
      hWinv y (Subgroup.mem_sup_right hy)
  have hstabZ : scalars n K ≤ LinearFlag.stabilizer W := LinearFlag.scalars_le_stabilizer W
  have hstabTop : (⊤ : Subgroup (SpecialLinearGroup (Fin n) K)) ≤ LinearFlag.stabilizer W := by
    rw [← hgenT₁]
    exact sup_le (sup_le hstabT hstabC) hstabZ
  have hstab : ∀ x : SpecialLinearGroup (Fin n) K, ∀ w ∈ W,
      (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro x w hw
    have hx : x ∈ LinearFlag.stabilizer W := hstabTop (Subgroup.mem_top x)
    rw [LinearFlag.mem_stabilizer] at hx
    have hmem : (Matrix.mulVecLin (x : Matrix (Fin n) (Fin n) K)) w ∈
        W.map (Matrix.mulVecLin (x : Matrix (Fin n) (Fin n) K)) := ⟨w, hw, rfl⟩
    rw [hx] at hmem
    simpa [Matrix.mulVecLin_apply] using hmem
  rcases eq_bot_or_eq_top_of_sl_invariant (by omega) hstab with h | h
  · exact hWbot h
  · exact hWtop h

theorem kiInsp_PSL {L : Type} [Group L] {n s : ℕ}
    (hL : CFSG.Open.StatedClassicalModel L .PSL n 2 s) (hn : 4 ≤ n)
    (hns : (n, s) ≠ (4, 1)) (T : Subgroup L) (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set L)))
    (hwti : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI T) (g : L) :
    T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ ⊤ := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hL
  letI := hKfield
  letI := hKfinite
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := s) (by rw [← Nat.card_eq_fintype_card, hKcard])
  letI := hchar
  have hs1 : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    rw [hs0, pow_zero] at hKcard
    have h2 := Finite.one_lt_card (α := K)
    omega
  have hq : n = 4 → 4 ≤ Nat.card K := by
    intro hn4
    have hs2 : 2 ≤ s := by
      have hsne : s ≠ 1 := by
        intro hs
        exact hns (by rw [hn4, hs])
      omega
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num : (2 : ℕ) > 0) hs2
  let eQ : L ≃* projectiveSL n K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        n K))
  let TQ : Subgroup (projectiveSL n K) := T.map eQ.toMonoidHom
  have hTQ : Assembly.IsElemAbelian 2 TQ := hT.map eQ.toMonoidHom
  have hwcQ : WeaklyClosedIn TQ (Subgroup.normalizer (TQ : Set (projectiveSL n K))) :=
    ⟨Subgroup.le_normalizer, CentralTI.weaklyClosed_map_mulEquiv eQ hwc.2⟩
  have hwtiQ : CFSG.RankThree.GF2n.Tim81.CentralTI.WeakTI TQ :=
    weakTI_map_mulEquiv hwti eQ
  intro hgen
  have hgenQ : TQ ⊔ conjSubgroup (eQ g) TQ = ⊤ := by
    calc TQ ⊔ conjSubgroup (eQ g) TQ
        = (T ⊔ conjSubgroup g T).map eQ.toMonoidHom := by
          rw [Subgroup.map_sup, map_conjSubgroup]
          rfl
      _ = ⊤ := by rw [hgen, Subgroup.map_top_of_surjective eQ.toMonoidHom eQ.surjective]
  exact kiInsp_projectiveSL hn hq hKcard TQ hTQ hwcQ hwtiQ (eQ g) hgenQ

end CFSG.RankThree.GF2n.Tim81

end
