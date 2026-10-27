module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofAct
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFixMat
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res5ProofLThree
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.LowTwoRank (StatedScalars)

open CFSG.Assembly.RankThreeEven (projImage)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open Matrix (ProjGenLinGroup GeneralLinearGroup)

open scoped Matrix
open Item211Proof Item211Res2Proof Item2130Res5Proof

section Certs

@[expose] def Item2130CaseBEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b → Sec4.IsSLThreePiTheta Y →
      ¬ Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y) →
      (∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField) →
      (Sec4.IsTypeCOn A Y ∨ IsTypeCOnBarSL A Y) → c ∉ Y →
      (∃ (π : Bool) (f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π 2 f K ∧
        (Nonempty (lBar Y ≃* projImage (Sec4.slPi π 3 (2 ^ f) K)) ∨
          Nonempty (lBar Y ≃* Sec4.slPi π 3 (2 ^ f) K))) →
      (Sec4.InducesTypeOn Y c 2 ∨ InducesTypeOnBarSL Y c 2) → False

end Certs

namespace Item2130Res6Proof

variable {G : Type} [Group G] [Finite G]

theorem commute_of_isDiag {K : Type} [Field K] {M N : Matrix (Fin 3) (Fin 3) K} (hM : M.IsDiag)
    (hN : N.IsDiag) : M * N = N * M := by
  rw [← (Matrix.isDiag_iff_diagonal_diag M).mp hM, ← (Matrix.isDiag_iff_diagonal_diag N).mp hN,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem isDiag_scalar_mul_diagUnits {K : Type} [Field K] (l s t : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := by
  rw [scalar_mul_diagUnits_eq, coe_diagHom]
  exact Matrix.isDiag_diagonal _

theorem eq_two_of_two_eq_zero {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (h2 : (2 : K) = 0) : p = 2 := by
  have hp : p.Prime := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hK.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ (cond π f (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, hK.card]
    cases π
    · change (p ^ f) ^ 2 = p ^ (2 * f)
      rw [← pow_mul, mul_comm]
    · rfl
  have : CharP K p := charP_of_card_eq_prime_pow hcard
  have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
  rw [CharP.cast_eq_zero_iff K p] at h2'
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'

theorem exists_two_of_card_four {U : Subgroup G} (hU : Nat.card U = 4) :
    ∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ := by
  classical
  obtain ⟨u₁, hu₁, hu₁1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    push Not at h
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr h
    rw [this, Subgroup.card_bot] at hU
    norm_num at hU
  obtain ⟨u₂, hu₂, hu₂1, hu₂₁⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ u₁ := by
    by_contra h
    push Not at h
    have hsub : (U : Set G) ⊆ {1, u₁} := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Set.mem_insert _ _
      · rw [h x hx hx1]
        exact Set.mem_insert_of_mem _ rfl
    have hle : (U : Set G).ncard ≤ ({1, u₁} : Set G).ncard := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hu₁1.symm, ← Nat.card_coe_set_eq] at hle
    change Nat.card U ≤ 2 at hle
    omega
  exact ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, Ne.symm hu₂₁⟩

variable {A E U L U₀ Y : Subgroup G} {c b : G}

theorem false_of_typeC_model (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] {ε : lBar Y →* ProjGenLinGroup (Fin 3) K}
    (hM : IsBarModel Y π p f K ε) (hodd : Odd (Nat.card (oThreePrime (Outer (lBar Y)))))
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D)
    (hAD : ∀ x ∈ A, ∃ y ∈ D, ActsVia Y ε x y) {yc : GL (Fin 3) K} (hycD : yc ∈ D)
    (hyc : ActsVia Y ε c yc) (hc2 : Type123 π (p ^ f) K yc 2 → (2 : K) ≠ 0) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK := hM.field
  have hq := hM.modThree
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) := hM.isPerfect
  have hle : ε.range ≤ projImage (slPi π 3 (p ^ f) K) := hM.range_eq.le
  have hge : projImage (slPi π 3 (p ^ f) K) ≤ ε.range := hM.range_eq.ge
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
  obtain ⟨g, hgH, hdiag, -⟩ := isTypeC_conj_std hK hq hD
  have hdfix : ∀ u ∈ U₀, ∀ l : GL (Fin 3) K, ActsVia Y ε u l →
      ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag → u = 1 := by
    intro u hu l hul hdl
    refine hfix u hu fun x hx => ?_
    obtain ⟨yx, hyxD, hyx⟩ := hAD x (hEA hx)
    obtain ⟨lx, sx, tx, -, -, hgx⟩ := hdiag yx hyxD
    have hx' : ((g⁻¹ * yx * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
      rw [hgx]
      exact isDiag_scalar_mul_diagUnits lx sx tx
    have h1 : (g⁻¹ * yx * g) * (g⁻¹ * l * g) = (g⁻¹ * l * g) * (g⁻¹ * yx * g) := by
      apply Units.ext
      rw [Units.val_mul (g⁻¹ * yx * g), Units.val_mul (g⁻¹ * l * g)]
      exact commute_of_isDiag hx' hdl
    have hcomm : yx * l = l * yx := by
      calc yx * l = g * ((g⁻¹ * yx * g) * (g⁻¹ * l * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g) * (g⁻¹ * yx * g)) * g⁻¹ := by rw [h1]
        _ = l * yx := by group
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
  have hYc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hlift : ∀ u ∈ U₀, ∃ l : GL (Fin 3) K, ActsVia Y ε u l ∧
      l ^ 2 ∈ StatedScalars (Fin 3) K ∧ l * yc = yc * l := by
    intro u hu
    obtain ⟨l, -, hul⟩ := exists_actsVia_of_mem_sup hle (hU0K hu)
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
    refine ⟨l, hul, hl2, ?_⟩
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
  have hsq : ∀ l : GL (Fin 3) K, l ^ 2 ∈ StatedScalars (Fin 3) K → ∃ s : K,
      ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ * l * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s • 1 := by
    intro l hl
    obtain ⟨s, hs⟩ := (inv_conj_mem_statedScalars_iff g (l ^ 2)).mpr hl
    refine ⟨s, ?_⟩
    rw [← Units.val_mul, show g⁻¹ * l * g * (g⁻¹ * l * g) = g⁻¹ * l ^ 2 * g by
      rw [pow_two]; group, ← hs,
      coe_scalar_eq_smul]
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
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, hu₁₂⟩ := exists_two_of_card_four hU04
  obtain ⟨l₁, hl₁, hl₁2, hl₁c⟩ := hlift u₁ hu₁
  obtain ⟨l₂, hl₂, hl₂2, hl₂c⟩ := hlift u₂ hu₂
  by_cases hdist : sc ≠ 1 ∧ tc ≠ 1 ∧ sc ≠ tc
  ·
    refine hu₁1 (hdfix u₁ hu₁ l₁ hl₁ ?_)
    obtain ⟨hs1, ht1, hst⟩ := hdist
    have hd01 : d 0 ≠ d 1 := by
      intro h
      apply hs1
      have h' : (lc : K) = lc * sc := by simpa [hd] using h
      exact Units.ext (by
        have := mul_left_cancel₀ lc.ne_zero (h'.symm.trans (mul_one _).symm)
        simpa using this)
    have hd02 : d 0 ≠ d 2 := by
      intro h
      apply ht1
      have h' : (lc : K) = lc * tc := by simpa [hd] using h
      exact Units.ext (by
        have := mul_left_cancel₀ lc.ne_zero (h'.symm.trans (mul_one _).symm)
        simpa using this)
    have hd12 : d 1 ≠ d 2 := by
      intro h
      apply hst
      have h' : (lc : K) * sc = lc * tc := by simpa [hd] using h
      exact Units.ext (mul_left_cancel₀ lc.ne_zero h')
    intro r t hrt
    refine entry_eq_zero_of_commute_diagonal (hmd l₁ hl₁c) ?_
    have cover : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
    rcases cover r with rfl | rfl | rfl <;> rcases cover t with rfl | rfl | rfl <;>
      first | exact absurd rfl hrt | exact hd01 | exact Ne.symm hd01 | exact hd02 |
        exact Ne.symm hd02 | exact hd12 | exact Ne.symm hd12
  ·
    have h2 : (2 : K) ≠ 0 :=
      hc2 ((type123_of_diag hK hq (hD.1 hycD) hgH hsc htc hgc).2 hcZ hdist)
    have hnd : ¬ (d 0 = d 1 ∧ d 1 = d 2) := by
      rintro ⟨h01, h12⟩
      apply hcZ
      have h01' : (lc : K) = lc * sc := by simpa [hd] using h01
      have h02' : (lc : K) = lc * tc := by simpa [hd] using h01.trans h12
      refine ⟨Units.ext ?_, Units.ext ?_⟩
      · have := mul_left_cancel₀ lc.ne_zero (h01'.symm.trans (mul_one _).symm)
        simpa using this
      · have := mul_left_cancel₀ lc.ne_zero (h02'.symm.trans (mul_one _).symm)
        simpa using this
    have hu12 : u₁ * u₂ = u₂ * u₁ :=
      congrArg Subtype.val (hC.u_mem.1.2.1.1.is_comm.comm ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩)
    obtain ⟨ν, hν⟩ := commMod_of_commute hK hq hge hl₁ hl₂ hu12
    have hconj : l₁ * l₂ * l₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ν * l₂ := by
      rw [hν]
      group
    have hν1 := Sec16.Proof1613Fix.eq_one_of_conj_eq_scalar_mul_of_sq hconj hl₁2
    rw [hν1, map_one, one_mul] at hconj
    have hl12 : l₁ * l₂ = l₂ * l₁ := by
      calc l₁ * l₂ = l₁ * l₂ * l₁⁻¹ * l₁ := by group
        _ = l₂ * l₁ := by rw [hconj]
    have hm12 : ((g⁻¹ * l₁ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ * l₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g⁻¹ * l₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ * l₁ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      calc g⁻¹ * l₁ * g * (g⁻¹ * l₂ * g) = g⁻¹ * (l₁ * l₂) * g := by group
        _ = g⁻¹ * (l₂ * l₁) * g := by rw [hl12]
        _ = g⁻¹ * l₂ * g * (g⁻¹ * l₁ * g) := by group
    obtain ⟨s₁, hs₁⟩ := hsq l₁ hl₁2
    obtain ⟨s₂, hs₂⟩ := hsq l₂ hl₂2
    rcases isDiag_or_of_commute_diagonal h2 hnd hs₁ hs₂ hm12 (hmd l₁ hl₁c) (hmd l₂ hl₂c) with
      h | h | h
    · exact hu₁1 (hdfix u₁ hu₁ l₁ hl₁ h)
    · exact hu₂1 (hdfix u₂ hu₂ l₂ hl₂ h)
    ·
      have hu12U : u₁ * u₂ ∈ U₀ := U₀.mul_mem hu₁ hu₂
      have hu12_1 : u₁ * u₂ ≠ 1 := by
        intro h1
        have hu₁2 : u₁ ^ 2 = 1 := hC.u_mem.1.2.1.2 u₁ hu₁
        apply hu₁₂
        calc u₁ = u₁ * (u₁ * u₂) := by rw [h1, mul_one]
          _ = u₁ ^ 2 * u₂ := by rw [pow_two, mul_assoc]
          _ = u₂ := by rw [hu₁2, one_mul]
      refine hu12_1 (hdfix (u₁ * u₂) hu12U (l₁ * l₂) (hl₁.mul hl₂) ?_)
      rw [show g⁻¹ * (l₁ * l₂) * g = (g⁻¹ * l₁ * g) * (g⁻¹ * l₂ * g) by group, Units.val_mul]
      exact h

end Item2130Res6Proof

open Item2130Res6Proof

theorem item2130CaseB_of
    (hEven : Item2130CaseBEven) :
    Item2130CaseB := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY hSL hH hNF hTC hcY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hbA : b ∈ A := hC.b_mem.1
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hEv := hEven G A E U c L b U₀ Y hcfg h9 hC hAY hSL hH hNF hTC hcY
  rcases hTC with hTC' | hTC'
  ·
    obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hAD', -⟩ := hTC'
    have hq2 := two_lt_of_projImage hK hq hqY e
    have hAD : ∀ x ∈ A, ∃ y ∈ D,
        ActsVia Y ((projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom) x y :=
      fun x hx => by
        obtain ⟨y, hy, hyz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
        exact ⟨y, hy, hAL hx, hyz⟩
    obtain ⟨yc, hycD, hycz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨c, hAL hcA, hcA, rfl⟩)
    refine false_of_typeC_model hcfg hC (isBarModel_projImage hK hq hq2 e)
      (odd_oThreePrime_of_projImage hK hq2 e) hD hAD hycD ⟨hAL hcA, hycz⟩ fun h2t h20 => ?_
    have hp2 := eq_two_of_two_eq_zero hK h20
    subst hp2
    exact hEv ⟨π, f, K, inferInstance, hK, Or.inl ⟨e⟩⟩
      (Or.inl ⟨hAL hcA, π, 2, f, K, inferInstance, hK, hq, e, yc, hD.1 hycD, h2t, hycz⟩)
  ·
    obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hAD', -⟩ := hTC'
    have hq2 := two_lt_of_slPi hK hq hqY e
    have hmk : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (Y : Set G)) (y : GL (Fin 3) K),
        (∀ z : lBar Y, ((e (thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨x, hx⟩) z) :
          slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y * (e z : GL (Fin 3) K) * y⁻¹) →
        ActsVia Y ((ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp
          ((slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)) x y := fun x hx y hxy =>
      ⟨hx, fun z => by
        change ProjGenLinGroup.mk ((e (thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨x, hx⟩) z) :
            slPi π 3 (p ^ f) K) : GL (Fin 3) K) = ProjGenLinGroup.mk y *
          ProjGenLinGroup.mk ((e z : slPi π 3 (p ^ f) K) : GL (Fin 3) K) *
            (ProjGenLinGroup.mk y)⁻¹
        rw [hxy z, map_mul, map_mul, map_inv]⟩
    have hAD : ∀ x ∈ A, ∃ y ∈ D, ActsVia Y ((ProjGenLinGroup.mk : GL (Fin 3) K →*
        ProjGenLinGroup (Fin 3) K).comp ((slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)) x y :=
      fun x hx => by
        obtain ⟨y, hy, hyz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
        exact ⟨y, hy, hmk x (hAL hx) y hyz⟩
    obtain ⟨yc, hycD, hycz⟩ := hAD' _ (mem_autThetaQuot_iff.mpr ⟨c, hAL hcA, hcA, rfl⟩)
    refine false_of_typeC_model hcfg hC (isBarModel_slPi hK hq hq2 e)
      (odd_oThreePrime_of_slPi hK hq2 e) hD hAD hycD (hmk c (hAL hcA) yc hycz) fun h2t h20 => ?_
    have hp2 := eq_two_of_two_eq_zero hK h20
    subst hp2
    exact hEv ⟨π, f, K, inferInstance, hK, Or.inr ⟨e⟩⟩
      (Or.inr ⟨hAL hcA, π, 2, f, K, inferInstance, hK, hq, e, yc, hD.1 hycD, h2t, hycz⟩)

end CFSG.RankThree.PartTwo.Sec21
