module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail15
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofEFTools
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofEFMat
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.RankThree.PartTwo.Sec16.Proof1614Trans
  CFSG.RankThree.PartTwo.Sec16.Proof1613Inv CFSG.RankThree.PartTwo.Sec16.Proof1613Fix
  CFSG.RankThree.PartTwo.Sec16.Proof1615EF CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix

theorem ks1615EF_of
    (h131 : Item131) : KS1615EF := by
  intro G _ _ A c L h hPGL
  have h13 := h.toSec13Data
  obtain ⟨hL3, hZL, -⟩ := facts_of_isZ3PGLThreePi h13 hPGL
  refine ⟨hL3, ?_⟩
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hA := h.isElemAbelian
  have hcA : c ∈ A := h.mem_A
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  obtain ⟨d, hdAL, hd1, hDeq⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (card_inf_eq_three_of_pgl h13 hPGL)
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hdAL).1
  have hdL : d ∈ L := (Subgroup.mem_inf.mp hdAL).2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  obtain ⟨x, hxA, hx⟩ : ∃ x ∈ A, Sec4.InducesTypeOn L x 3 := by
    obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    obtain ⟨p, e, hp, -, hisoL⟩ := hL3
    rcases cases131 h131 sporadicModels131 slTwoCenter h13 with
        ⟨-, -, ⟨ψ⟩, -⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, -, -, hx⟩ | ⟨hcL', -⟩
    · exact (false_of_pgl_of_prod kSPGLProper h13 hPGL ψ).elim
    · exfalso
      rcases hMJ with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
      · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h13 hM12p hM12z χ
        exact KFacts.KS14.not_isoLThreePi_M12 p e (isoLThreePi_of_mulEquiv χ' hisoL)
      · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h13 hJ2p hJ2z χ
        exact KFacts.KS14.ks17J2NotList.1 p e (isoLThreePi_of_mulEquiv χ' hisoL)
    · exact hx
    · exact (hcL hcL').elim
  have hxd : x * d = d * x := h.commute hxA hdA
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hxc : x * c = c * x := h.commute hxA hcA
  have hxL : x ∉ L := not_mem_of_inducesTypeOn_three h.mem_thetaComponentsAt hx
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hPerfL : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
  have hPerf : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hsc : ∀ (u : Kˣ) (M : GL (Fin 3) K),
      M * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * M :=
    fun u M => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u M).eq
  obtain ⟨s, hs, hse, τ, hτ, hτ1, z₀, hz₀, g, hg, hD⟩ :=
    exists_type_one_lift hdL hd3 hd1 hxd hxN hK hq e hy3 hact
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ
    exact zero_ne_one hτ
  set ε : Kˣ := Units.mk0 τ hτ0 with hεdef
  have hε : (ε : K) = τ := rfl
  have hε3 : ε ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hε, hτ, Units.val_one])
  set δ := g * diagTau hτ * g⁻¹ with hδ
  set T := g * diagE ε * g⁻¹ with hT
  set κ := g * cycThree * g⁻¹ with hκ
  have hz₀1 : ProjGenLinGroup.mk z₀ = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₀)
  have hmkδ : ProjGenLinGroup.mk δ = ProjGenLinGroup.mk s := by
    have hsz : s * z₀ = δ := by rw [hδ, ← hD]; group
    rw [← hsz, map_mul, hz₀1, mul_one]
  have hTH : T ∈ glPi π 3 (p ^ f) K := by
    have hεq : ε ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
      cube_root_mem_qSubPi hq ((mem_rootsOfUnity 3 ε).mpr hε3)
    have hE : diagE ε ∈ glPi π 3 (p ^ f) K :=
      diagUnits_mem_glPi hK hεq (one_mem _) (one_mem _)
    exact mul_mem (mul_mem hg hE) (inv_mem hg)
  have hκS : κ ∈ slPi π 3 (p ^ f) K := conj_mem_slPi hπ hg (cycThree_mem_slPi hπ)
  have hTδ : T * δ = δ * T := by
    calc T * δ = g * (diagE ε * diagTau hτ) * g⁻¹ := by rw [hT, hδ]; group
      _ = g * (diagTau hτ * diagE ε) * g⁻¹ := by rw [diagE_comm_diagTau]
      _ = δ * T := by rw [hT, hδ]; group
  have hTκ : T * κ * T⁻¹ = δ * κ := by
    calc T * κ * T⁻¹ = g * (diagE ε * cycThree * (diagE ε)⁻¹) * g⁻¹ := by rw [hT, hκ]; group
      _ = g * (diagTau hτ * cycThree) * g⁻¹ := by rw [diagE_conj_cycThree hτ ε hε]
      _ = δ * κ := by rw [hδ, hκ]; group
  have hT3 : T ^ 3 = 1 := by
    rw [hT, conj_pow, diagE_pow_three (by rw [hε, hτ]), mul_one, mul_inv_cancel]
  clear_value δ T κ
  set mk := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hmkdef
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db : ↥L ⧸ aschbacherSolvableCore 3 ↥L := mk d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _) (Subgroup.one_mem _)
      (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  have hedb : ((e db : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk δ := by rw [hmkδ, hse]
  set κb : ↥L ⧸ aschbacherSolvableCore 3 ↥L := e.symm (projOf _ ⟨κ, hκS⟩) with hκb
  have heκ : ((e κb : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk κ := by rw [hκb, MulEquiv.apply_symm_apply, coe_projOf]
  have hmkconj : ∀ w : GL (Fin 3) K, ProjGenLinGroup.mk (g * w * g⁻¹) =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk w * (ProjGenLinGroup.mk g)⁻¹ := fun w => by
    rw [map_mul, map_mul, map_inv]
  have hcommb : db * κb = κb * db := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hedb, heκ, hδ, hκ, hmkconj,
      hmkconj]
    have R := mk_diagTau_cycThree hτ
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cycThree) *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk cycThree * ProjGenLinGroup.mk (diagTau hτ)) *
          (ProjGenLinGroup.mk g)⁻¹ := by rw [R]
      _ = ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹) := by
        group
  have hκb3 : κb ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, heκ, ← map_pow, hκ, conj_pow, cycThree_pow_three, mul_one,
      mul_inv_cancel, map_one, map_one, Subgroup.coe_one]
  have hκbn : κb ∉ Subgroup.zpowers db := by
    set μ : Kˣ := ε ^ (2 * 1) with hμ
    have hcd : cycThree * diagTau hτ * cycThree⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) μ * diagTau hτ := by
      have := cycThree_pow_conj_diagTau hτ hτ0 1
      rwa [pow_one] at this
    have hdc : diagTau hτ * cycThree * (diagTau hτ)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * cycThree := by
      have e1 : cycThree * diagTau hτ * cycThree⁻¹ * (diagTau hτ)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) μ := by
        rw [hcd]
        group
      have e2 : diagTau hτ * cycThree * (diagTau hτ)⁻¹ * cycThree⁻¹ =
          (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ := by
        rw [← e1]
        group
      rw [map_inv, ← e2]
      group
    have hμ1 : μ ≠ 1 := by
      intro h1
      apply hτ1
      have h2 : τ ^ 2 = 1 := by
        have := congrArg Units.val h1
        rwa [hμ, Units.val_pow_eq_pow_val, hε, Units.val_one] at this
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, h2, div_one]
    have hζ1 : μ⁻¹ ≠ 1 := fun h1 => hμ1 (inv_eq_one.mp h1)
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply not_mk_eq_zpow_of_heis (y₁ := diagTau hτ) (y₂ := cycThree) hζ1 hdc k
    have h2 := congrArg (fun m => ((e m : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) hk
    simp only [map_zpow, Subgroup.coe_zpow, hedb, heκ, hδ, hκ, hmkconj] at h2
    rw [conj_zpow] at h2
    rw [map_zpow]
    calc ProjGenLinGroup.mk cycThree = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) ^ k *
            (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by rw [h2]
      _ = ProjGenLinGroup.mk (diagTau hτ) ^ k := by group
  set Hb := Subgroup.zpowers db ⊔ Subgroup.zpowers κb with hHb
  have hHbab : CFSG.Assembly.IsElemAbelian 3 Hb :=
    Sec13.isElemAbelian_zpowers_sup hdb3 hκb3 hcommb
  have hHb9 : Nat.card Hb = 9 :=
    card_zpowers_sup_zpowers hκb3 (orderOf_eq_prime hdb3 hdb1) hκbn hcommb.symm
  have hHb3 : IsPGroup 3 Hb := fun b => ⟨1, Subtype.ext (by simpa using hHbab.2 b b.2)⟩
  obtain ⟨S, hdS, -, hS3, hSmap⟩ := Sec13.exists_isPGroup_le_map_eq (M := ⊤) hHb3
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    (isPGroup_zpowers_three hd'3) le_top
    (by rw [MonoidHom.map_zpowers]; exact le_sup_left)
  have hinjS := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hS3
  have hS9 : Nat.card S = 9 := by
    rw [← Sec13.card_map_eq_of_injOn _ hinjS, hSmap, hHb9]
  have hmkS : ∀ t ∈ S, mk t ∈ Hb := fun t ht => hSmap ▸ Subgroup.mem_map_of_mem _ ht
  have hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have := hHbab.1
    have hc : mk a * mk b = mk b * mk a :=
      congrArg Subtype.val (mul_comm' (⟨mk a, hmkS a ha⟩ : Hb) ⟨mk b, hmkS b hb⟩)
    exact hinjS (S.mul_mem ha hb) (S.mul_mem hb ha) (by rw [map_mul, map_mul, hc])
  set FL : Subgroup G := S.map L.subtype with hFL
  have hFLL : FL ≤ L := Subgroup.map_subtype_le S
  have hdFL : d ∈ FL := ⟨d', hdS (Subgroup.mem_zpowers d'), rfl⟩
  have hFL9 : Nat.card FL = 9 := by
    rw [hFL, Subgroup.card_map_of_injective L.subtype_injective, hS9]
  have hFL3 : IsPGroup 3 FL := hS3.map _
  obtain ⟨l₀, hl₀, k₀, ht₀N, ht₀⟩ := exists_acts_of_mem_glPi hxN hK hq e hyH hy3 hact hTH
  set t₀ := l₀ * x ^ k₀ with ht₀def
  set σ₀ := thetaQuotMulAut L (L.normalizerMonoidHom ⟨t₀, ht₀N⟩) with hσ₀
  have hσ₀db : σ₀ db = db := by
    apply e.injective
    apply Subtype.ext
    have hc : T * δ * T⁻¹ = δ := by rw [hTδ]; group
    rw [ht₀, hedb, ← map_inv, ← map_mul, ← map_mul, hc]
  have hσ₀κb : σ₀ κb = db * κb := by
    apply e.injective
    apply Subtype.ext
    have hc : ProjGenLinGroup.mk T * ProjGenLinGroup.mk κ * (ProjGenLinGroup.mk T)⁻¹ =
        ProjGenLinGroup.mk δ * ProjGenLinGroup.mk κ := by
      rw [← map_inv, ← map_mul, ← map_mul, hTκ, map_mul]
    rw [ht₀, heκ, hc, map_mul, Subgroup.coe_mul, hedb, heκ]
  have hσ₀Hb : Hb.map σ₀.toMonoidHom ≤ Hb := by
    rw [hHb, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · change σ₀ db ∈ Hb
      rw [hσ₀db]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers db)
    · change σ₀ κb ∈ Hb
      rw [hσ₀κb]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers db))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers κb))
  set P : Subgroup G := (Hb.comap mk).map L.subtype with hP
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hFLP : FL ≤ P := Subgroup.map_mono fun t ht => hmkS t ht
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hPcard : Nat.card P = 9 * Nat.card (aschbacherSolvableCore 3 ↥L) := by
    rw [hP, Subgroup.card_map_of_injective L.subtype_injective]
    set θ := aschbacherSolvableCore 3 ↥L
    have h1 := Subgroup.card_mul_index (Hb.comap (QuotientGroup.mk' θ))
    have h2 : (Hb.comap (QuotientGroup.mk' θ)).index = Hb.index :=
      Subgroup.index_comap_of_surjective Hb (QuotientGroup.mk'_surjective θ)
    have h3 := Subgroup.card_mul_index Hb
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    have hpos : 0 < Hb.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    rw [h2] at h1
    have h5 : Nat.card (Hb.comap (QuotientGroup.mk' θ)) * Hb.index =
        (Nat.card Hb * Nat.card θ) * Hb.index := by
      rw [h1, h4, ← h3]; ring
    rw [Nat.eq_of_mul_eq_mul_right hpos h5, hHb9]
  have hfac : (Nat.card P).factorization 3 = 2 := by
    rw [hPcard, Nat.factorization_mul (by norm_num) (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero,
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_three]
    rfl
  have hSylFL : CFSG.ABGLocalTools.IsSylowOf 3 FL P :=
    CFSG.ABGLocalTools.isSylowOf_of_card hFLP (by rw [hfac, hFL9]; norm_num)
  have ht₀P : ∀ t ∈ P, t₀ * t * t₀⁻¹ ∈ P := by
    rintro _ ⟨l, hl, rfl⟩
    have hlt : t₀ * (l : G) * t₀⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ht₀N (l : G)).mp l.2
    refine ⟨⟨_, hlt⟩, ?_, rfl⟩
    change mk ⟨_, hlt⟩ ∈ Hb
    have h1 : mk ⟨_, hlt⟩ = σ₀ (mk l) := by
      rw [hσ₀, hmkdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
      congr 1
    rw [h1]
    exact hσ₀Hb ⟨mk l, hl, rfl⟩
  set FL' := FL.map (MulAut.conj t₀).toMonoidHom with hFL'
  have hFL'P : FL' ≤ P := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht₀P t (hFLP ht)
  have hSylFL' : CFSG.ABGLocalTools.IsSylowOf 3 FL' P :=
    CFSG.ABGLocalTools.isSylowOf_of_card hFL'P
      (by rw [hfac, hFL', Subgroup.card_map_of_injective (MulAut.conj t₀).injective, hFL9];
          norm_num)
  obtain ⟨k, hkP, hk⟩ := hSylFL.exists_mem_conj hSylFL'
  obtain ⟨kl, hklHb, rfl⟩ := hkP
  obtain ⟨f₀', hf₀S, hf₀k⟩ : ∃ f₀' ∈ S, mk f₀' = mk kl := by
    have : mk kl ∈ S.map mk := by rw [hSmap]; exact hklHb
    obtain ⟨f₀', hf₀', h⟩ := this
    exact ⟨f₀', hf₀', h⟩
  set f₀ : G := (f₀' : G) with hf₀
  have hf₀L : f₀ ∈ L := f₀'.2
  have hf₀FL : f₀ ∈ FL := ⟨f₀', hf₀S, rfl⟩
  set k : G := (kl : G) with hkdef
  have hkL : k ∈ L := kl.2
  set t₁ := f₀ * k⁻¹ * t₀ with ht₁def
  have hfkN : f₀ * k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.le_normalizer (L.mul_mem hf₀L (L.inv_mem hkL))
  have ht₁N : t₁ ∈ Subgroup.normalizer (L : Set G) := Subgroup.mul_mem _ hfkN ht₀N
  have ht₁FL : ∀ t ∈ FL, t₁ * t * t₁⁻¹ ∈ FL := by
    intro t ht
    have h1 : t₀ * t * t₀⁻¹ ∈ FL' := ⟨t, ht, rfl⟩
    have h2 := (hk _).mp h1
    have h3 : t₁ * t * t₁⁻¹ = f₀ * (k⁻¹ * (t₀ * t * t₀⁻¹) * k) * f₀⁻¹ := by
      rw [ht₁def]; group
    rw [h3]
    exact FL.mul_mem (FL.mul_mem hf₀FL h2) (FL.inv_mem hf₀FL)
  have hfk1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨f₀ * k⁻¹, hfkN⟩) = 1 := by
    rw [act_inner (L.mul_mem hf₀L (L.inv_mem hkL)) hfkN]
    have h1 : mk ⟨f₀ * k⁻¹, L.mul_mem hf₀L (L.inv_mem hkL)⟩ = 1 := by
      have e1 : (⟨f₀ * k⁻¹, L.mul_mem hf₀L (L.inv_mem hkL)⟩ : ↥L) = f₀' * kl⁻¹ := rfl
      rw [e1, map_mul, map_inv, hf₀k, mul_inv_cancel]
    rw [h1, map_one]
  set σ₁ := thetaQuotMulAut L (L.normalizerMonoidHom ⟨t₁, ht₁N⟩) with hσ₁
  have hσ₁σ₀ : σ₁ = σ₀ := by
    rw [hσ₁, show (⟨t₁, ht₁N⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨f₀ * k⁻¹, hfkN⟩ * ⟨t₀, ht₀N⟩ from rfl, map_mul, map_mul, hfk1, one_mul]
  have ht₁ : ∀ u, ((e (σ₁ u) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk T * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk T)⁻¹ := by
    rw [hσ₁σ₀]
    exact ht₀
  have hl₁ : f₀ * k⁻¹ * l₀ ∈ L := L.mul_mem (L.mul_mem hf₀L (L.inv_mem hkL)) hl₀
  have ht₁eq : t₁ = (f₀ * k⁻¹ * l₀) * x ^ k₀ := by rw [ht₁def, ht₀def]; group
  have hn0 : orderOf t₁ ≠ 0 := (orderOf_pos t₁).ne'
  obtain ⟨a, b, hb3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  obtain ⟨b', hbb'⟩ : ∃ b' : ℕ, (b * b') % 3 = 1 := by
    rcases (show b % 3 = 1 ∨ b % 3 = 2 by omega) with h1 | h2
    · exact ⟨1, by rw [mul_one]; exact h1⟩
    · exact ⟨2, by rw [Nat.mul_mod, h2]⟩
  set m := b * b' with hm
  set w := t₁ ^ m with hw
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ ht₁N m
  have hσw : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) = σ₁ ^ m := by
    rw [hσ₁, show (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G)) = ⟨t₁, ht₁N⟩ ^ m from rfl,
      map_pow, map_pow]
  have hTm : T ^ m = T := by
    have h1 : m = 3 * (m / 3) + 1 := by omega
    rw [h1, pow_add, pow_mul, hT3, one_pow, one_mul, pow_one]
  have hwT : ∀ u, ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) u) :
      projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk T * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk T)⁻¹ := by
    intro u
    rw [hσw, acts_zpow e ht₁ m u, hTm]
  have hwFL : ∀ t ∈ FL, w * t * w⁻¹ ∈ FL := by
    have key : ∀ j : ℕ, ∀ t ∈ FL, t₁ ^ j * t * (t₁ ^ j)⁻¹ ∈ FL := by
      intro j
      induction j with
      | zero => intro t ht; simpa using ht
      | succ j ih =>
        intro t ht
        have h1 : t₁ ^ (j + 1) * t * (t₁ ^ (j + 1))⁻¹ = t₁ ^ j * (t₁ * t * t₁⁻¹) * (t₁ ^ j)⁻¹ := by
          rw [pow_succ]; group
        rw [h1]
        exact ih _ (ht₁FL t ht)
    exact key m
  have hl₁c : (f₀ * k⁻¹ * l₀) * c = c * (f₀ * k⁻¹ * l₀) := hLc _ hl₁
  have ht₁c : Commute t₁ c := by
    rw [ht₁eq]
    exact Commute.mul_left hl₁c ((Commute.pow_left hxc k₀))
  have hwc : w * c = c * w := (ht₁c.pow_left m).eq
  have hw3a : w ^ 3 ^ a = 1 := by
    rw [hw, ← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hn, hm]
    exact ⟨b', by ring⟩
  have hcube : ∀ l ∈ L, ∀ j : ℕ, ∃ l' ∈ L, (l * x ^ k₀) ^ j = l' * x ^ (k₀ * j) := by
    intro l hl j
    induction j with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨l', hl', hlj⟩ := ih
      have hxl : x ^ (k₀ * j) * l * (x ^ (k₀ * j))⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxN _) l).mp hl
      refine ⟨l' * (x ^ (k₀ * j) * l * (x ^ (k₀ * j))⁻¹), L.mul_mem hl' hxl, ?_⟩
      rw [pow_succ, hlj, show k₀ * (j + 1) = k₀ * j + k₀ by ring, pow_add]
      group
  have ht₁3 : t₁ ^ 3 ∈ L := by
    obtain ⟨l', hl', h1⟩ := hcube _ hl₁ 3
    rw [ht₁eq, h1, mul_comm k₀ 3, pow_mul, hx3, one_pow, mul_one]
    exact hl'
  have hw3L : w ^ 3 ∈ L := by
    rw [hw, ← pow_mul, mul_comm, pow_mul]
    exact L.pow_mem ht₁3 m
  have hw3N : w ^ 3 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hwN 3
  have hw3triv : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w ^ 3, hw3N⟩) = 1 := by
    have h1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w ^ 3, hw3N⟩) =
        thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) ^ 3 := by
      rw [show (⟨w ^ 3, hw3N⟩ : Subgroup.normalizer (L : Set G)) = ⟨w, hwN⟩ ^ 3 from rfl,
        map_pow, map_pow]
    ext u
    apply e.injective
    apply Subtype.ext
    rw [h1, acts_zpow e hwT 3 u, hT3, map_one, inv_one, one_mul, mul_one, MulAut.one_apply]
  have hw3θ : w ^ 3 = 1 := by
    rw [act_inner hw3L hw3N] at hw3triv
    have hcen : mk ⟨w ^ 3, hw3L⟩ ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut _ => φ z) hw3triv
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * mk ⟨w ^ 3, hw3L⟩ = mk ⟨w ^ 3, hw3L⟩ * z * (mk ⟨w ^ 3, hw3L⟩)⁻¹ *
            mk ⟨w ^ 3, hw3L⟩ := by rw [this]
        _ = mk ⟨w ^ 3, hw3L⟩ * z := by group
    rw [hZL, Subgroup.mem_bot] at hcen
    have hθ : (⟨w ^ 3, hw3L⟩ : ↥L) ∈ aschbacherSolvableCore 3 ↥L :=
      (QuotientGroup.eq_one_iff _).mp hcen
    set v : aschbacherSolvableCore 3 ↥L := ⟨⟨w ^ 3, hw3L⟩, hθ⟩ with hv
    have hva : v ^ 3 ^ a = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [hv, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, hw3a, one_pow]
    have hvo : orderOf v = 1 := by
      have h1 : orderOf v ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hva
      have h2 : orderOf v ∣ Nat.card (aschbacherSolvableCore 3 ↥L) := orderOf_dvd_natCard v
      have hcop : Nat.Coprime (3 ^ a) (Nat.card (aschbacherSolvableCore 3 ↥L)) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have := orderOf_eq_one_iff.mp hvo
    have h3 := congrArg (fun v : aschbacherSolvableCore 3 ↥L => ((v : ↥L) : G)) this
    simpa [hv] using h3
  have hwd : w * d = d * w := by
    obtain ⟨t', ht'S, ht'⟩ := hwFL d hdFL
    have hσwd : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) db = db := by
      apply e.injective
      apply Subtype.ext
      have hc : T * δ * T⁻¹ = δ := by rw [hTδ]; group
      rw [hwT, hedb, ← map_inv, ← map_mul, ← map_mul, hc]
    have h1 : mk t' = db := by
      rw [← hσwd, hdb, hmkdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      exact ht'
    have h2 : t' = d' := hinjS ht'S (hdS (Subgroup.mem_zpowers d')) h1
    have h3 : w * d * w⁻¹ = d := by
      rw [← ht', h2]
      rfl
    calc w * d = w * d * w⁻¹ * w := by group
      _ = d * w := by rw [h3]
  have hcd : c * d = d * c := h.commute hcA hdA
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc'
    apply hcL
    have hzd := zpowers_eq_of_mem_of_ne_one h.card_zpowers hdc' hd1
    exact (Subgroup.zpowers_le.mpr hdL) (hzd ▸ Subgroup.mem_zpowers c)
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hB
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := Sec13.isElemAbelian_zpowers_sup hc3 hd3 hcd
  have hc1 : c ≠ 1 := by
    intro h1
    have := h.card_zpowers
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
    norm_num at this
  have hB9 : Nat.card B = 9 :=
    card_zpowers_sup_zpowers hd3 (orderOf_eq_prime hc3 hc1) hdc hcd.symm
  have hwB : ∀ z ∈ B, z * w = w * z := by
    intro z hz
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hcd hz
    exact (Commute.mul_left (Commute.zpow_left hwc.symm i) (Commute.zpow_left hwd.symm j)).eq
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := h.le_normalizer hcA
  have hσd : ∀ u, ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) u) :
      projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk δ * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk δ)⁻¹ := by
    rw [act_inner hdL hdN]
    exact acts_conj e hedb
  have hσc : thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hcN⟩) = 1 := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe, ← hLc l l.2, mul_inv_cancel_right]
  have hactB : ∀ (i j k : ℤ) (hN : w ^ k * (c ^ i * d ^ j) ∈ Subgroup.normalizer (L : Set G)),
      ∀ u, ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨w ^ k * (c ^ i * d ^ j), hN⟩) u) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (T ^ k * δ ^ j) * (e u : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk (T ^ k * δ ^ j))⁻¹ := by
    intro i j k hN
    have e1 : (⟨w ^ k * (c ^ i * d ^ j), hN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨w, hwN⟩ ^ k * (⟨c, hcN⟩ ^ i * ⟨d, hdN⟩ ^ j) := rfl
    rw [e1, map_mul, map_mul, map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_zpow,
      map_zpow, map_zpow, hσc, one_zpow, one_mul]
    exact acts_mul e (acts_zpow' e hwT k) (acts_zpow' e hσd j)
  have hdecE : ∀ a ∈ B ⊔ Subgroup.zpowers w, ∃ i j k : ℤ, a = w ^ k * (c ^ i * d ^ j) := by
    intro a ha
    rw [sup_comm] at ha
    obtain ⟨k, z, hz, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers (fun z hz => hwB z hz) ha
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hcd hz
    exact ⟨i, j, k, rfl⟩
  have hε1 : ε ≠ 1 := fun h1 => hτ1 (by rw [← hε, h1, Units.val_one])
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hε1
  have hTδscal : ∀ k j : ℤ, ProjGenLinGroup.mk (T ^ k * δ ^ j) = 1 → (3 : ℤ) ∣ k ∧ (3 : ℤ) ∣ j := by
    intro k j hkj
    have hz : ∀ (a b c : Kˣ) (n : ℤ), diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) :=
      fun a b c n => by
        have : diagUnits a b c = diagHom (a, b, c) := rfl
        rw [this, ← map_zpow]
        rfl
    have e0 : T ^ k * δ ^ j = g * (diagE ε ^ k * diagTau hτ ^ j) * g⁻¹ := by
      rw [hT, hδ, conj_zpow, conj_zpow]; group
    have e2 : diagE ε ^ k * diagTau hτ ^ j = diagHom (ε ^ k * ε ^ j, (ε ^ 2) ^ j, 1) := by
      rw [diagTau_eq_diagUnits hτ ε hε, diagE, hz, hz, diagUnits_mul]
      simp only [one_zpow, one_mul]
      rfl
    rw [e0, e2, mk_eq_one_iff_mem_statedScalars] at hkj
    have hd : diagHom (ε ^ k * ε ^ j, (ε ^ 2) ^ j, (1 : Kˣ)) ∈ StatedScalars (Fin 3) K := by
      have := (StatedScalars.normal (Fin 3) K).conj_mem _ hkj g⁻¹
      rwa [show g⁻¹ * (g * diagHom (ε ^ k * ε ^ j, (ε ^ 2) ^ j, 1) * g⁻¹) * g⁻¹⁻¹ =
        diagHom (ε ^ k * ε ^ j, (ε ^ 2) ^ j, 1) by group] at this
    have hr := (diagHom_mem_statedScalars_iff _).mp hd
    simp only [ratioHom, MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, one_mul,
      inv_eq_one, mul_inv_eq_one] at hr
    obtain ⟨hj2, hkj1⟩ := hr
    rw [hkj1] at hj2
    have hεo' : ((orderOf ε : ℕ) : ℤ) = 3 := by rw [hεo]; rfl
    have hj : (3 : ℤ) ∣ j := by
      have h3 : (3 : ℤ) ∣ 2 * j := by
        rw [← hεo', orderOf_dvd_iff_zpow_eq_one, zpow_mul]
        rw [show ε ^ (2 : ℤ) = ε ^ (2 : ℕ) from zpow_ofNat ε 2]
        exact hj2
      omega
    have hk : (3 : ℤ) ∣ k := by
      have h3 : (3 : ℤ) ∣ k + j := by
        rw [← hεo', orderOf_dvd_iff_zpow_eq_one, zpow_add]
        exact hkj1
      omega
    exact ⟨hk, hj⟩
  have hT1 : ProjGenLinGroup.mk T ≠ 1 := by
    intro h1
    have := (hTδscal 1 0 (by rw [zpow_one, zpow_zero, mul_one]; exact h1)).1
    omega
  have hwnB : w ∉ B := by
    intro hwB'
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup hcd hwB'
    have hN' : w ^ (0 : ℤ) * (c ^ i * d ^ j) ∈ Subgroup.normalizer (L : Set G) := by
      rw [zpow_zero, one_mul, ← hij]; exact hwN
    have h1 := hactB i j 0 hN'
    have e1 : (⟨w ^ (0 : ℤ) * (c ^ i * d ^ j), hN'⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨w, hwN⟩ := by
      apply Subtype.ext
      show w ^ (0 : ℤ) * (c ^ i * d ^ j) = w
      rw [zpow_zero, one_mul, ← hij]
    rw [e1] at h1
    have h2 := acts_unique hK hq e hwT h1
    rw [zpow_zero, one_mul] at h2
    have h3 : ProjGenLinGroup.mk (T ^ (1 : ℤ) * δ ^ (-j)) = 1 := by
      rw [zpow_one, map_mul, h2, map_zpow, map_zpow, ← zpow_add, add_neg_cancel, zpow_zero]
    have := (hTδscal 1 (-j) h3).1
    omega
  have hw1 : w ≠ 1 := fun h1 => hwnB (h1 ▸ Subgroup.one_mem _)
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3θ hw1
  set E := B ⊔ Subgroup.zpowers w with hE
  have hBw : ∀ z ∈ B, ∀ y ∈ Subgroup.zpowers w, z * y = y * z := by
    intro z hz y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute z w from hwB z hz) k).eq
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    Sec13.isElemAbelian_sup hBab (Sec13.isElemAbelian_zpowers hw3θ) hBw
  have hE27 : Nat.card E = 27 := by
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B (Subgroup.zpowers w) hBw).1
    have hinf : B ⊓ Subgroup.zpowers w = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzB, hzw⟩ := Subgroup.mem_inf.mp hz
      by_contra hz1
      have hz1' : z ≠ 1 := fun h1 => hz1 (h1 ▸ Subgroup.one_mem _)
      have hzo : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hwo]
      have hzw' : Subgroup.zpowers z = Subgroup.zpowers w := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzw) ?_
        rw [hzo]
        have hzo' : orderOf z = 3 := orderOf_eq_prime (hEab.2 z (Subgroup.mem_sup_left hzB)) hz1'
        rw [Nat.card_zpowers, hzo']
      exact hwnB ((Subgroup.zpowers_le.mpr hzB) (hzw' ▸ Subgroup.mem_zpowers w))
    rw [hinf, Subgroup.card_bot, mul_one, hB9, Nat.card_zpowers, hwo] at h1
    exact h1
  have hcE : c ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hcN) (Subgroup.zpowers_le.mpr hdN))
      (Subgroup.zpowers_le.mpr hwN)
  have hsec : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    ext a
    constructor
    · rintro ⟨haE, hac⟩
      obtain ⟨i, j, k, rfl⟩ := hdecE a haE
      have haN := hEN haE
      have hσa : ∀ u, thetaQuotMulAut L (L.normalizerMonoidHom ⟨_, haN⟩) u = u := by
        intro u
        induction u using QuotientGroup.induction_on with
        | H l =>
          rw [thetaQuotMulAut_mk, QuotientGroup.eq_iff_div_mem]
          obtain ⟨t, ht, hteq⟩ := hac l l.2
          have e1 : (L.normalizerMonoidHom ⟨_, haN⟩ l) / l = t := by
            apply Subtype.ext
            change _ = L.subtype t
            rw [hteq]
            simp [div_eq_mul_inv]
          rw [e1]
          exact ht
      have h1 := hactB i j k haN
      have h2 : ∀ u, ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨_, haN⟩) u) :
          projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk 1 * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk 1)⁻¹ := by
        intro u
        rw [hσa, map_one, one_mul, inv_one, mul_one]
      have h3 := acts_unique hK hq e h1 h2
      rw [map_one] at h3
      obtain ⟨⟨k', hk'⟩, ⟨j', hj'⟩⟩ := hTδscal k j h3
      have hwk : w ^ k = 1 := by rw [hk', zpow_mul, show w ^ (3 : ℤ) = w ^ (3 : ℕ) from
        zpow_ofNat w 3, hw3θ, one_zpow]
      have hdj : d ^ j = 1 := by rw [hj', zpow_mul, show d ^ (3 : ℤ) = d ^ (3 : ℕ) from
        zpow_ofNat d 3, hd3, one_zpow]
      rw [hwk, hdj, one_mul, mul_one]
      exact Subgroup.zpow_mem_zpowers c i
    · intro ha
      refine ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left ha), fun l hl => ?_⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hcl : c ^ i * l = l * c ^ i := (Commute.zpow_left (hLc l hl).symm i).eq
      have h1 : c ^ i * l * (c ^ i)⁻¹ * l⁻¹ = 1 := by rw [hcl]; group
      rw [h1]
      exact Subgroup.one_mem _
  have hTδeq : ∀ k j : ℤ, T ^ k * δ ^ j = g * (diagE ε ^ k * diagTau hτ ^ j) * g⁻¹ := by
    intro k j
    rw [hT, hδ, conj_zpow, conj_zpow]; group
  have hTC : Sec4.IsTypeCOn E L := by
    refine ⟨π, p, f, K, inferInstance, hK, hq, e, (stdTypeC K).map (MulAut.conj g).toMonoidHom,
      isTypeC_map_conj (isTypeC_stdTypeC hK hq) hg, ?_, ?_⟩
    · intro τ' hτ'
      obtain ⟨a, haN, haE, rfl⟩ := mem_autThetaQuot_iff.mp hτ'
      obtain ⟨i, j, k, rfl⟩ := hdecE a haE
      refine ⟨g * (diagE ε ^ k * diagTau hτ ^ j) * g⁻¹,
        ⟨diagE ε ^ k * diagTau hτ ^ j, mul_mem (zpow_mem (diagE_mem_stdTypeC hε3) k)
          (zpow_mem (diagTau_mem_stdTypeC hτ ε hε) j), rfl⟩, ?_⟩
      intro z
      rw [← hTδeq]
      exact hactB i j k haN z
    · intro y' hy'
      obtain ⟨D₀, hD₀, rfl⟩ := hy'
      obtain ⟨⟨a₁, b₁, c₁⟩, ⟨ha₁, hb₁, hc₁⟩, rfl⟩ := hD₀
      have hu : ((a₁ * c₁⁻¹ : Kˣ) : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, mul_pow, (mem_rootsOfUnity 3 a₁).mp ha₁, inv_pow,
          (mem_rootsOfUnity 3 c₁).mp hc₁, inv_one, mul_one, Units.val_one]
      have hv : ((b₁ * c₁⁻¹ : Kˣ) : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, mul_pow, (mem_rootsOfUnity 3 b₁).mp hb₁, inv_pow,
          (mem_rootsOfUnity 3 c₁).mp hc₁, inv_one, mul_one, Units.val_one]
      obtain ⟨j, k, hjk⟩ := exists_eq_diagTau_pow_mul_diagE_pow hτ hτ1 ε hε hu hv
      have hN : w ^ (k : ℤ) * (c ^ (0 : ℤ) * d ^ (j : ℤ)) ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.mul_mem _ (Subgroup.zpow_mem _ hwN _)
          (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hcN _) (Subgroup.zpow_mem _ hdN _))
      have hmemE : w ^ (k : ℤ) * (c ^ (0 : ℤ) * d ^ (j : ℤ)) ∈ E :=
        Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers w)) _) (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hcE _)
          (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
            (Subgroup.mem_zpowers d))) _))
      refine ⟨_, mem_autThetaQuot_iff.mpr ⟨_, hN, hmemE, rfl⟩, fun z => ?_⟩
      have hmk : ProjGenLinGroup.mk (T ^ (k : ℤ) * δ ^ (j : ℤ)) =
          ProjGenLinGroup.mk ((MulAut.conj g).toMonoidHom (diagHom (a₁, b₁, c₁))) := by
        have e1 : diagHom (a₁, b₁, c₁) =
            GeneralLinearGroup.scalar (Fin 3) c₁ * (diagE ε ^ k * diagTau hτ ^ j) := by
          change diagUnits a₁ b₁ c₁ = _
          rw [diagUnits_eq_scalar_mul, hjk, ← (Commute.pow_pow
            (show Commute (diagE ε) (diagTau hτ) from diagE_comm_diagTau hτ ε) k j).eq]
        have hS1 : ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) c₁) = 1 :=
          mk_eq_one_iff_mem_statedScalars.mpr ⟨c₁, rfl⟩
        rw [hTδeq, zpow_natCast, zpow_natCast, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e1]
        simp only [map_mul, hS1, one_mul]
      rw [← hmk]
      exact hactB 0 j k hN z
  have hSel : CFSG.Assembly.IsElemAbelian 3 S :=
    ⟨⟨⟨fun a b => Subtype.ext (hSab a a.2 b b.2)⟩⟩, fun t ht => hinjS (S.pow_mem ht 3)
      (S.one_mem) (by rw [map_pow, map_one]; exact hHbab.2 _ (hmkS t ht))⟩
  have hFLab : CFSG.Assembly.IsElemAbelian 3 FL := Sec13.isElemAbelian_map hSel L.subtype
  set F := Subgroup.zpowers c ⊔ FL with hF
  have hcFL : ∀ z ∈ Subgroup.zpowers c, ∀ t ∈ FL, z * t = t * z := by
    intro z hz t ht
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (hLc t (hFLL ht)).symm i).eq
  have hFab : CFSG.Assembly.IsElemAbelian 3 F :=
    Sec13.isElemAbelian_sup (Sec13.isElemAbelian_zpowers hc3) hFLab hcFL
  have hF27 : Nat.card F = 27 := by
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers c) FL hcFL).1
    have hinf : Subgroup.zpowers c ⊓ FL = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzc, hzF⟩ := Subgroup.mem_inf.mp hz
      by_contra hz1
      have hz1' : z ≠ 1 := fun h1 => hz1 (h1 ▸ Subgroup.one_mem _)
      have hzw := zpowers_eq_of_mem_of_ne_one h.card_zpowers hzc hz1'
      exact hcL ((Subgroup.zpowers_le.mpr (hFLL hzF)) (hzw ▸ Subgroup.mem_zpowers c))
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hc3 hc1, hFL9] at h1
    exact h1
  have hBF : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ E ⊓ F := by
    rw [hDeq]
    refine le_inf le_sup_left (sup_le le_sup_left ?_)
    exact (Subgroup.zpowers_le.mpr hdFL).trans le_sup_right
  have hFEL : F ≤ E ⊔ L :=
    sup_le ((Subgroup.zpowers_le.mpr hcE).trans le_sup_left) (hFLL.trans le_sup_right)
  have hFLeq : F ⊓ L = FL := by
    have hle : FL ≤ F ⊓ L := le_inf le_sup_right hFLL
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hFL9]
    have hdvd : Nat.card (F ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hF27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m', hm', hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hne : m' ≠ 3 := by
      rintro rfl
      have heq : F ⊓ L = F :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hF27]; norm_num)
      apply hcL
      have hcF : c ∈ F := (le_sup_left : Subgroup.zpowers c ≤ F) (Subgroup.mem_zpowers c)
      have : c ∈ F ⊓ L := by rw [heq]; exact hcF
      exact (Subgroup.mem_inf.mp this).2
    rw [hcard]
    have : m' ≤ 2 := by omega
    calc 3 ^ m' ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      _ = 9 := by norm_num
  have hF9 : Nat.card (F ⊓ L : Subgroup G) = 9 := by rw [hFLeq, hFL9]
  have hfus : ∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z := by
    rw [hFLeq]
    rintro _ ⟨s₁, hs₁, rfl⟩ hy1 _ ⟨s₂, hs₂, rfl⟩ hz1
    have he₁ : (((Subgroup.topEquiv.trans e) ⟨db, Subgroup.mem_top _⟩ :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * diagTau hτ * g⁻¹) := by
      rw [← hδ]
      exact hedb
    have he₂ : (((Subgroup.topEquiv.trans e) ⟨κb, Subgroup.mem_top _⟩ :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * cycThree * g⁻¹) := by
      rw [← hκ]
      exact heκ
    have key := transitive_of_normal_form hK hq (L := (⊤ : Subgroup (↥L ⧸
      aschbacherSolvableCore 3 ↥L))) (Subgroup.topEquiv.trans e) hτ hτ1 hg
      (Subgroup.mem_top db) (Subgroup.mem_top κb) he₁ he₂
    have hne : ∀ t ∈ S, (t : G) ≠ 1 → mk t ≠ 1 := by
      intro t ht ht1 hmk1
      apply ht1
      have := hinjS ht S.one_mem (by rw [hmk1, map_one])
      rw [this]
      rfl
    obtain ⟨nb, ⟨-, hnbN⟩, hnb⟩ :=
      key (mk s₁) (hmkS s₁ hs₁) (hne s₁ hs₁ hy1) (mk s₂) (hmkS s₂ hs₂) (hne s₂ hs₂ hz1)
    have hnbN' : nb ∈ Subgroup.normalizer ((S.map mk : Subgroup _) : Set (↥L ⧸
        aschbacherSolvableCore 3 ↥L)) := by
      rw [hSmap]
      exact hnbN
    obtain ⟨n, hnS, hnn⟩ := (Sec13.normalizer_map_mk_eq hS3).le hnbN'
    refine ⟨(n : G), n.2, ?_⟩
    have hmem : n * s₁ * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hnS _).mp hs₁
    have heq : mk (n * s₁ * n⁻¹) = mk s₂ := by
      rw [map_mul, map_mul, map_inv]
      change mk n * mk s₁ * (mk n)⁻¹ = mk s₂
      rw [hnn]
      exact hnb
    exact congrArg Subtype.val (hinjS hmem hs₂ heq)
  have hσwdb : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) db = db := by
    apply e.injective
    apply Subtype.ext
    have hc : T * δ * T⁻¹ = δ := by rw [hTδ]; group
    rw [hwT, hedb, ← map_inv, ← map_mul, ← map_mul, hc]
  have hσwκb : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) κb = db * κb := by
    apply e.injective
    apply Subtype.ext
    have hc : ProjGenLinGroup.mk T * ProjGenLinGroup.mk κ * (ProjGenLinGroup.mk T)⁻¹ =
        ProjGenLinGroup.mk δ * ProjGenLinGroup.mk κ := by
      rw [← map_inv, ← map_mul, ← map_mul, hTκ, map_mul]
    rw [hwT, heκ, hc, map_mul, Subgroup.coe_mul, hedb, heκ]
  have hcomm_w : ∀ u ∈ Hb, u * (thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) u)⁻¹ ∈
      Subgroup.zpowers db := by
    intro u hu
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hcommb hu
    rw [map_mul, map_zpow, map_zpow, hσwdb, hσwκb,
      (Commute.mul_zpow (show Commute db κb from hcommb) j)]
    have e1 : db ^ i * κb ^ j * (db ^ i * (db ^ j * κb ^ j))⁻¹ = db ^ (-j) := by group
    rw [e1]
    exact Subgroup.zpow_mem_zpowers db (-j)
  have hFLNE : FL ≤ Subgroup.normalizer (E : Set G) := by
    rintro _ ⟨f', hf'S, rfl⟩
    set f := (f' : G) with hfdef
    have hfL : f ∈ L := f'.2
    have hfFL : f ∈ FL := ⟨f', hf'S, rfl⟩
    have hfw : f * w * f⁻¹ * w⁻¹ ∈ Subgroup.zpowers d := by
      obtain ⟨t, htS, ht⟩ := hwFL f⁻¹ (FL.inv_mem hfFL)
      have hmemS : f' * t ∈ S := S.mul_mem hf'S htS
      have hmk : mk (f' * t) ∈ Subgroup.zpowers db := by
        have h1 : mk t = (thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) (mk f'))⁻¹ := by
          rw [← map_inv, ← map_inv, hmkdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            thetaQuotMulAut_mk]
          congr 1
          apply Subtype.ext
          rw [normalizerMonoidHom_apply_coe]
          exact ht
        rw [map_mul, h1]
        exact hcomm_w _ (hmkS f' hf'S)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmk
      have hdj : d' ^ j ∈ S := S.zpow_mem (hdS (Subgroup.mem_zpowers d')) j
      have h2 : d' ^ j = f' * t := hinjS hdj hmemS (by rw [map_zpow]; exact hj)
      have h3 : f * w * f⁻¹ * w⁻¹ = d ^ j := by
        have := congrArg Subtype.val h2
        simp only [SubgroupClass.coe_zpow, Subgroup.coe_mul] at this
        rw [this, ← hfdef]
        change f * w * f⁻¹ * w⁻¹ = f * L.subtype t
        rw [ht]
        group
      rw [h3]
      exact Subgroup.zpow_mem_zpowers d j
    have hfwE : f * w * f⁻¹ ∈ E := by
      have e1 : f * w * f⁻¹ = (f * w * f⁻¹ * w⁻¹) * w := by group
      rw [e1]
      exact E.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right hfw))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    have hfc : f * c = c * f := hLc f hfL
    have hfd : f * d = d * f := hSab f' hf'S d' (hdS (Subgroup.mem_zpowers d')) |>
      congrArg Subtype.val
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨i, j, k, rfl⟩ := hdecE n hn
    change f * (w ^ k * (c ^ i * d ^ j)) * f⁻¹ ∈ E
    have e2 : f * (w ^ k * (c ^ i * d ^ j)) * f⁻¹ =
        (f * w * f⁻¹) ^ k * (c ^ i * d ^ j) := by
      rw [← MulAut.conj_apply, map_mul, map_mul, map_zpow, map_zpow, map_zpow, MulAut.conj_apply,
        MulAut.conj_apply, MulAut.conj_apply, hfc, hfd, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [e2]
    exact E.mul_mem (E.zpow_mem hfwE k) (E.mul_mem (E.zpow_mem hcE i)
      (E.zpow_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))) j))
  have hFNE : F ≤ Subgroup.normalizer (E : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hcE)) hFLNE
  exact ⟨E, F, hcE, hEab, hE27, hEN, hsec, hTC, hBF, hFEL, hFab, hF27, hF9, hfus, hFNE⟩

end CFSG.RankThree.PartTwo.Sec16
