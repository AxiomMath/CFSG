module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofB
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res7ProofUMat
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFixMat

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix (ProjGenLinGroup GeneralLinearGroup diagonal)
open scoped Matrix
open Item211Proof Item211Res2Proof Item2130Res5Proof Item2130Res6Proof

namespace Item2130Res7Proof

variable {G : Type} [Group G] [Finite G] {A E U L U₀ Y : Subgroup G} {c b : G}

theorem commute_of_frame {K : Type} [Field K] {g l y : GL (Fin 3) K} {δ : Fin 3 → K}
    (hy : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal δ)
    (hl : ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal δ =
      diagonal δ * ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    y * l = l * y := by
  have h1 : (g⁻¹ * y * g) * (g⁻¹ * l * g) = (g⁻¹ * l * g) * (g⁻¹ * y * g) := by
    apply Units.ext
    rw [Units.val_mul (g⁻¹ * y * g), Units.val_mul (g⁻¹ * l * g), hy]
    exact hl.symm
  calc y * l = g * ((g⁻¹ * y * g) * (g⁻¹ * l * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * l * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = l * y := by group

theorem exists_frame_entries {K : Type} [Field K] {g y : GL (Fin 3) K} {l s t : Kˣ}
    (hs : s ∈ rootsOfUnity 3 K) (ht : t ∈ rootsOfUnity 3 K)
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) :
    ∃ δ : Fin 3 → K, ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal δ ∧
      ∀ r, ∃ w : K, w ^ 3 = 1 ∧ δ r = l * w := by
  have hs3 : (s : K) ^ 3 = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hs)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have ht3 : (t : K) ^ 3 = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp ht)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  refine ⟨![(l : K), (l * s : Kˣ), (l * t : Kˣ)], ?_, fun r => ?_⟩
  · rw [hy, scalar_mul_diagUnits_eq, coe_diagHom]
  · fin_cases r
    · exact ⟨1, one_pow 3, by simp⟩
    · exact ⟨s, hs3, by simp⟩
    · exact ⟨t, ht3, by simp⟩

theorem false_of_typeC_model_unitary (hcfg : Config2130 G A E U c L)
    (hC : Choice2130 A E c L b U₀ Y) {p f : ℕ} {K : Type} [Field K]
    {ε : lBar Y →* ProjGenLinGroup (Fin 3) K} (hM : IsBarModel Y false p f K ε)
    (hodd : Odd (Nat.card (oThreePrime (Outer (lBar Y))))) {D : Subgroup (GL (Fin 3) K)}
    (hD : IsTypeC false (p ^ f) K D) (hAD : ∀ x ∈ A, ∃ y ∈ D, ActsVia Y ε x y)
    {yc : GL (Fin 3) K} (hycD : yc ∈ D) (hyc : ActsVia Y ε c yc) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK := hM.field
  have hq := hM.modThree
  have hU := hK.unitary
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have : Group.IsPerfect (projImage (slPi false 3 (p ^ f) K)) := hM.isPerfect
  have hle : ε.range ≤ projImage (slPi false 3 (p ^ f) K) := hM.range_eq.le
  have hge : projImage (slPi false 3 (p ^ f) K) ≤ ε.range := hM.range_eq.ge
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hEA : E ≤ A := hcfg.pair.mem_E.2
  have hcA : c ∈ A := hEA hpairs.1.1
  have hbA : b ∈ A := hC.b_mem.1
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by
    simpa using (hcfg.pair.mem_E.1.1.2 g g.2))⟩
  have hEN : E ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm E hE3 (hEA.trans hAC)
  have hU04 : Nat.card U₀ = 4 := hC.u_mem.1.2.2
  have hU02 : IsPGroup 2 U₀ := IsPGroup.of_card (n := 2) (by rw [hU04]; norm_num)
  have hEU : ⁅E, U₀⁆ = U₀ := by rw [Subgroup.commutator_comm]; exact hC.u_mem.2.symm
  have hU0K : U₀ ≤ Y ⊔ thetaQuotCentralizer Y :=
    le_sup_thetaQuotCentralizer_of_odd hodd hE3 hEN hC.u_norm hU02 hEU
  have hirrU : ∀ X : Subgroup G, X ≤ U₀ → E ≤ Subgroup.normalizer (X : Set G) →
      X = ⊥ ∨ X = U₀ := by
    rcases Sec6.mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hC.u_mem.1 with hp | ⟨-, hirr⟩
    · exact absurd hC.u_mem (Set.disjoint_left.mp (disjoint_fourGroupsPlus_fourGroupsMinus E) hp)
    · exact hirr
  have hEU0 : E ≤ Subgroup.normalizer (U₀ : Set G) := (mem_fourGroups_iff.mp hC.u_mem.1).1
  have hUC : U₀ ⊓ thetaQuotCentralizer Y = ⊥ := by
    have hEC : E ≤ Subgroup.normalizer ((thetaQuotCentralizer Y : Subgroup G) : Set G) :=
      fun x hx => normalizer_le_normalizer_thetaQuotCentralizer Y (hEN hx)
    rcases hirrU _ inf_le_left ((le_inf hEU0 hEC).trans
        Subgroup.inf_normalizer_le_normalizer_inf) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) (not_le_thetaQuotCentralizer hqY hC.y_comm_u)
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcfg.pair.mem_E.1.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hfix : ∀ u ∈ U₀, (∀ x ∈ E, x * u * x⁻¹ = u) → u = 1 := by
    intro u hu hxu
    have hECE : E ≤ Subgroup.normalizer ((Subgroup.centralizer (E : Set G) : Subgroup G) :
        Set G) := fun x hx => Subgroup.le_normalizer
      (Subgroup.mem_centralizer_iff.mpr fun y hy => hEcomm y hy x hx)
    rcases hirrU _ inf_le_left ((le_inf hEU0 hECE).trans
        Subgroup.inf_normalizer_le_normalizer_inf) with h | h
    · have hmem : u ∈ U₀ ⊓ Subgroup.centralizer (E : Set G) := by
        refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        calc x * u = x * u * x⁻¹ * x := by group
          _ = u * x := by rw [hxu x hx]
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      have hUC' : U₀ ≤ Subgroup.centralizer (E : Set G) := h ▸ inf_le_right
      have hbot : ⁅U₀, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC'
      rw [← hC.u_mem.2] at hbot
      rw [hbot, Subgroup.card_bot] at hU04
      norm_num at hU04
  have hdfix : ∀ u ∈ U₀, ∀ l : GL (Fin 3) K, ActsVia Y ε u l →
      (∀ x ∈ E, ∃ yx : GL (Fin 3) K, ActsVia Y ε x yx ∧ yx * l = l * yx) → u = 1 := by
    intro u hu l hul hcl
    refine hfix u hu fun x hx => ?_
    obtain ⟨yx, hyx, hcomm⟩ := hcl x hx
    have hk := (hyx.mul hul).mul (hyx.inv.mul hul.inv)
    have hk1 : yx * l * (yx⁻¹ * l⁻¹) = 1 := by
      rw [hcomm]
      group
    rw [hk1] at hk
    have hmemC := hk.mem_thetaQuotCentralizer hM.faithful (Subgroup.one_mem _)
    have hmemU : x * u * (x⁻¹ * u⁻¹) ∈ U₀ := by
      have h2 : x * u * x⁻¹ ∈ U₀ := (Subgroup.mem_normalizer_iff.mp (hEU0 hx) u).mp hu
      rw [show x * u * (x⁻¹ * u⁻¹) = x * u * x⁻¹ * u⁻¹ by group]
      exact U₀.mul_mem h2 (U₀.inv_mem hu)
    have hmem : x * u * (x⁻¹ * u⁻¹) ∈ U₀ ⊓ thetaQuotCentralizer Y := ⟨hmemU, hmemC⟩
    rw [hUC, Subgroup.mem_bot] at hmem
    calc x * u * x⁻¹ = x * u * (x⁻¹ * u⁻¹) * u := by group
      _ = u := by rw [hmem, one_mul]
  obtain ⟨g, hgH, hdiag, -⟩ := isTypeC_conj_std hK hq hD
  have hYc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hlift : ∀ u ∈ U₀, ∃ l ∈ slPi false 3 (p ^ f) K, ActsVia Y ε u l ∧
      l ^ 2 ∈ StatedScalars (Fin 3) K ∧ l * yc = yc * l := by
    intro u hu
    obtain ⟨l, hlS, hul⟩ := exists_actsVia_of_mem_sup hle (hU0K hu)
    have hu2 : u ^ 2 = 1 := hC.u_mem.1.2.1.2 u hu
    have hl2 : l ^ 2 ∈ StatedScalars (Fin 3) K := pow_mem_of_actsVia hK hq hge hul hu2
    have huc : u * c = c * u :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYc (hC.u_le hu))
    obtain ⟨μ, hμ⟩ := commMod_of_commute hK hq hge hul hyc huc
    have hconj : l * yc * l⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * yc := by
      rw [hμ]
      group
    have hμ1 := Sec16.Proof1613Fix.eq_one_of_conj_eq_scalar_mul_of_sq hconj hl2
    rw [hμ1, map_one, one_mul] at hconj
    refine ⟨l, hlS, hul, hl2, ?_⟩
    calc l * yc = l * yc * l⁻¹ * l := by group
      _ = yc * l := by rw [hconj]
  obtain ⟨lc, sc, tc, hsc, htc, hgc⟩ := hdiag yc hycD
  set d : Fin 3 → K := ![(lc : K), (lc * sc : Kˣ), (lc * tc : Kˣ)] with hd
  have hgcd : ((g⁻¹ * yc * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal d := by
    rw [hgc, scalar_mul_diagUnits_eq, coe_diagHom]
  have hmd : ∀ l : GL (Fin 3) K, l * yc = yc * l →
      ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d =
        Matrix.diagonal d * ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro l hl
    rw [← hgcd, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc g⁻¹ * l * g * (g⁻¹ * yc * g) = g⁻¹ * (l * yc) * g := by group
      _ = g⁻¹ * (yc * l) * g := by rw [hl]
      _ = g⁻¹ * yc * g * (g⁻¹ * l * g) := by group
  have hcZ : ¬ (sc = 1 ∧ tc = 1) := by
    intro h
    have hycZ : yc ∈ StatedScalars (Fin 3) K := by
      rw [← inv_conj_mem_statedScalars_iff g, hgc]
      exact (scalar_mul_diagUnits_mem_iff lc sc tc).mpr h
    have hcC := hyc.mem_thetaQuotCentralizer hM.faithful hycZ
    have hCA : A ⊓ thetaQuotCentralizer Y = Subgroup.zpowers b := by
      have hset := Sec13.sectionCentralizer_eq_inf hAL
      rw [hC.sec_cent] at hset
      exact SetLike.coe_injective hset.symm
    have hcb : c ∈ Subgroup.zpowers b := hCA ▸ (⟨hcA, hcC⟩ : c ∈ A ⊓ thetaQuotCentralizer Y)
    exact hcfg.not_mem ((Subgroup.zpowers_le.mpr hC.b_mem.2) hcb)
  obtain ⟨u₁, hu₁, -, -, hu₁1, -, -⟩ := exists_two_of_card_four hU04
  obtain ⟨l₁, hl₁S, hl₁, hl₁2, hl₁c⟩ := hlift u₁ hu₁
  set N : Matrix (Fin 3) (Fin 3) K :=
    ((g⁻¹ * l₁ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hNdef
  have hNd : N * Matrix.diagonal d = Matrix.diagonal d * N := hmd l₁ hl₁c
  have zN : ∀ {r s : Fin 3}, d r ≠ d s → N r s = 0 := fun h =>
    Item2130Res6Proof.entry_eq_zero_of_commute_diagonal hNd h
  have hEframe : ∀ x ∈ E, ∃ yx : GL (Fin 3) K, ActsVia Y ε x yx ∧ yx ∈ D ∧
      ∃ (lx : Kˣ) (δ : Fin 3 → K),
        ((g⁻¹ * yx * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal δ ∧
        ∀ r, ∃ w : K, w ^ 3 = 1 ∧ δ r = lx * w := by
    intro x hx
    obtain ⟨yx, hyxD, hyx⟩ := hAD x (hEA hx)
    obtain ⟨lx, sx, tx, hsx, htx, hgx⟩ := hdiag yx hyxD
    obtain ⟨δ, hδ, hδw⟩ := exists_frame_entries hsx htx hgx
    exact ⟨yx, hyx, hyxD, lx, δ, hδ, hδw⟩
  have hNdiag : N.IsDiag → False := by
    intro hdg
    apply hu₁1
    refine hdfix u₁ hu₁ l₁ hl₁ fun x hx => ?_
    obtain ⟨yx, hyx, -, lx, δ, hδ, -⟩ := hEframe x hx
    refine ⟨yx, hyx, commute_of_frame hδ ?_⟩
    change N * Matrix.diagonal δ = Matrix.diagonal δ * N
    rw [← (Matrix.isDiag_iff_diagonal_diag N).mp hdg]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    ring
  have key : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → d i ≠ d j → d i ≠ d k → d j = d k →
      False := by
    intro i j k hij hik hjk hdij hdik hdjk
    have hNij : N i j = 0 := zN hdij
    have hNik : N i k = 0 := zN hdik
    have hNji : N j i = 0 := zN (Ne.symm hdij)
    have hNki : N k i = 0 := zN (Ne.symm hdik)
    have hrs : N j k * N k j = 0 := by
      by_contra hne
      apply hu₁1
      refine hdfix u₁ hu₁ l₁ hl₁ fun x hx => ?_
      obtain ⟨yx, hyx, -, lx, δ, hδ, hδw⟩ := hEframe x hx
      refine ⟨yx, hyx, commute_of_frame hδ ?_⟩
      have hlx : ActsVia Y ε (x * u₁ * x⁻¹) (yx * l₁ * yx⁻¹) := (hyx.mul hl₁).mul hyx.inv
      have hux : x * u₁ * x⁻¹ ∈ U₀ := (Subgroup.mem_normalizer_iff.mp (hEU0 hx) u₁).mp hu₁
      have hcom : u₁ * (x * u₁ * x⁻¹) = (x * u₁ * x⁻¹) * u₁ :=
        congrArg Subtype.val (hC.u_mem.1.2.1.1.is_comm.comm ⟨u₁, hu₁⟩ ⟨_, hux⟩)
      obtain ⟨ν, hν⟩ := commMod_of_commute hK hq hge hl₁ hlx hcom
      have hconj : l₁ * (yx * l₁ * yx⁻¹) * l₁⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) ν * (yx * l₁ * yx⁻¹) := by
        rw [hν]
        group
      have hν1 := Sec16.Proof1613Fix.eq_one_of_conj_eq_scalar_mul_of_sq hconj hl₁2
      rw [hν1, map_one, one_mul] at hconj
      have hl1x : l₁ * (yx * l₁ * yx⁻¹) = (yx * l₁ * yx⁻¹) * l₁ := by
        calc l₁ * (yx * l₁ * yx⁻¹) = l₁ * (yx * l₁ * yx⁻¹) * l₁⁻¹ * l₁ := by group
          _ = (yx * l₁ * yx⁻¹) * l₁ := by rw [hconj]
      set N' : Matrix (Fin 3) (Fin 3) K :=
        ((g⁻¹ * (yx * l₁ * yx⁻¹) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hN'def
      have hNN' : N * N' = N' * N := by
        rw [hNdef, hN'def, ← Units.val_mul, ← Units.val_mul]
        congr 1
        calc g⁻¹ * l₁ * g * (g⁻¹ * (yx * l₁ * yx⁻¹) * g) =
            g⁻¹ * (l₁ * (yx * l₁ * yx⁻¹)) * g := by group
          _ = g⁻¹ * ((yx * l₁ * yx⁻¹) * l₁) * g := by rw [hl1x]
          _ = g⁻¹ * (yx * l₁ * yx⁻¹) * g * (g⁻¹ * l₁ * g) := by group
      have hN'δ : N' * Matrix.diagonal δ = Matrix.diagonal δ * N := by
        rw [hN'def, hNdef, ← hδ, ← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      have heq := mul_mul_eq_zero_of_block hij hik hjk hNij hNji hN'δ hNN'
      have hδ2 : δ k ^ 2 - δ j ^ 2 = 0 := (mul_eq_zero.mp heq).resolve_left hne
      obtain ⟨wj, hwj, hδj⟩ := hδw j
      obtain ⟨wk, hwk, hδk⟩ := hδw k
      have hδjk : δ j = δ k := by
        rw [hδj, hδk]
        refine eq_of_sq_eq_of_cube lx.ne_zero hwj hwk ?_
        rw [← hδj, ← hδk]
        linear_combination -hδ2
      exact commute_diagonal_of_block hij hik hjk hNij hNik hNji hNki hδjk
    have hgN : g⁻¹ * l₁ * g ∈ glPi false 3 (p ^ f) K :=
      mul_mem (mul_mem (inv_mem hgH) (slPi_le_glPi (fun _ => hU) hl₁S)) hgH
    have hNu : (N.map hU.bar)ᵀ * N = 1 := (mem_glPi_false hU).mp hgN
    obtain ⟨hjk0, hkj0⟩ := eq_zero_of_unitary_block hU.bar hNu hij hik hjk hNij hNik hrs
    exact hNdiag (isDiag_of_block hij hik hjk hNij hNik hNji hNki hjk0 hkj0)
  have hne : ∀ {u v : Kˣ}, u ≠ v → ((lc * u : Kˣ) : K) ≠ ((lc * v : Kˣ) : K) := by
    intro u v huv h
    exact huv (mul_left_cancel (Units.ext h))
  have hd0 : d 0 = ((lc * 1 : Kˣ) : K) := by simp [hd]
  have hd1 : d 1 = ((lc * sc : Kˣ) : K) := rfl
  have hd2 : d 2 = ((lc * tc : Kˣ) : K) := rfl
  by_cases hs1 : sc = 1
  · have ht1 : tc ≠ 1 := fun h => hcZ ⟨hs1, h⟩
    refine key 2 0 1 (by decide) (by decide) (by decide) ?_ ?_ ?_
    · rw [hd2, hd0]
      exact hne ht1
    · rw [hd2, hd1, hs1]
      exact hne ht1
    · rw [hd0, hd1, hs1]
  · by_cases ht1 : tc = 1
    ·
      refine key 1 0 2 (by decide) (by decide) (by decide) ?_ ?_ ?_
      · rw [hd1, hd0]
        exact hne hs1
      · rw [hd1, hd2, ht1]
        exact hne hs1
      · rw [hd0, hd2, ht1]
    · by_cases hst : sc = tc
      ·
        refine key 0 1 2 (by decide) (by decide) (by decide) ?_ ?_ ?_
        · rw [hd0, hd1]
          exact hne (Ne.symm hs1)
        · rw [hd0, hd2]
          exact hne (Ne.symm ht1)
        · rw [hd1, hd2, hst]
      ·
        refine hNdiag fun r s hrs => zN ?_
        have h01 : d 0 ≠ d 1 := by
          rw [hd0, hd1]
          exact hne (Ne.symm hs1)
        have h02 : d 0 ≠ d 2 := by
          rw [hd0, hd2]
          exact hne (Ne.symm ht1)
        have h12 : d 1 ≠ d 2 := by
          rw [hd1, hd2]
          exact hne hst
        have cover : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
        rcases cover r with rfl | rfl | rfl <;> rcases cover s with rfl | rfl | rfl <;>
          first | exact absurd rfl hrs | exact h01 | exact Ne.symm h01 | exact h02 |
            exact Ne.symm h02 | exact h12 | exact Ne.symm h12

end Item2130Res7Proof

end CFSG.RankThree.PartTwo.Sec21
