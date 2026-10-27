module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteStd
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteStdA
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU2
import CFSG.GH74.Generic.S3.L3Cover
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
import CFSG.GH74.Generic.S1.LinFull
import CFSG.GH74.Generic.S3.LeavesFine
import CFSG.GH74.Generic.S3.Lem37
import CFSG.LargeExtraspecial.OfFStar
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary Additive

section Chart

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qtwoDU5_center_eq_bot (hF0 : Nat.card F0 = 4) {n : ℕ} (hn : 3 ≤ n) (hn3 : ¬ 3 ∣ n) :
    Subgroup.center (Su F0 2 1 n) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨lam, hlam⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := F0) (p := 2)
      (f := 1) (by rw [hF0]; norm_num)) hn hz
  have hdet : (lam : F0) ^ n = 1 := by
    have h := z.2.1
    rw [hlam] at h
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using h
  have h3 : (lam : F0) ^ 3 = 1 := by
    have hcard : Nat.card F0ˣ = 3 := by rw [Nat.card_units, hF0]
    have h := pow_card_eq_one' (x := lam)
    rw [hcard] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hlam1 : (lam : F0) = 1 := by
    have hcop : Nat.Coprime n 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3)
    have h := pow_gcd_eq_one.mpr ⟨hdet, h3⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  refine Subgroup.mem_bot.mpr (Subtype.ext (Units.ext ?_))
  rw [hlam, hlam1]
  simp

private theorem qtwoDU5_pow_val_add {ω : F0ˣ} (hω : orderOf ω = 3) (a b : ZMod 3) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [← pow_add, pow_inj_mod, hω, ZMod.val_add, Nat.mod_mod]

private theorem qtwoDU5_prod_pow_val {ω : F0ˣ} (hω : orderOf ω = 3) (a : Fin 5 → ZMod 3) :
    ∏ i, ω ^ (a i).val = ω ^ (∑ i, a i).val := by
  rw [Finset.prod_pow_eq_pow_sum, pow_inj_mod, hω]
  have h : ((∑ i, (a i).val : ℕ) : ZMod 3) = ∑ i, a i := by
    rw [Nat.cast_sum]
    simp [ZMod.natCast_zmod_val]
  rw [← h, ZMod.val_natCast, Nat.mod_mod]

private theorem qtwoDU5_pow_val_inj {ω : F0ˣ} (hω : orderOf ω = 3) {a b : ZMod 3}
    (h : ω ^ a.val = ω ^ b.val) : a = b := by
  rw [pow_inj_mod, hω, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
  exact ZMod.val_injective 3 h

theorem qtwoDU5_fixed_isSolvable (hF0 : Nat.card F0 = 4) {ω : F0ˣ} (hω : orderOf ω = 3)
    (v : Fin 5 → ZMod 3) (hcnt : ∀ k : ZMod 3, (Finset.univ.filter fun i => v i = k).card ≤ 3) :
    Group.IsSolvable ↥(fixedGroup (qtwoDB39_conjAut hF0 (fun i => ω ^ (v i).val))) := by
  classical
  obtain ⟨φ⟩ := CFSG.GH74.Generic.S3.exists_ringEquiv_of_card_eq (K := F0)
    (F := CFSG.Fischer.F4) (by rw [hF0, Nat.card_eq_fintype_card, CFSG.Fischer.F4.card])
  have hF : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  set δ := qtwoDB39_conjAut hF0 (fun i => ω ^ (v i).val) with hδ
  set k : ZMod 3 := ∑ i, v i with hk
  set w : Fin 5 → F0ˣ := fun i => ω ^ (v i + k).val with hw
  have hsum : ∑ i, (v i + k) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← hk]
    generalize k = s
    revert s
    decide
  have hw0 : qTwoChartTwoThree_diag w ∈
      CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1) 5 := by
    refine CFSG.LieType.Universal.Unitary.mem_SUid.mpr ⟨?_, qtwoDB39_diag_conjTr_mul hF0 w⟩
    change (Matrix.diagonal fun i => (w i : F0)).det = 1
    rw [Matrix.det_diagonal, ← Units.coe_prod, hw, qtwoDU5_prod_pow_val hω, hsum]
    simp
  let w₀ : Su F0 2 1 5 := ⟨qTwoChartTwoThree_diag w, hw0⟩
  let E : Su F0 2 1 5 ≃* CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.M5 :=
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 5)).trans
      (CFSG.GH74.Generic.S3.statedSUFieldEquiv φ 5 (2 ^ 1))
  have hE : ∀ u : Su F0 2 1 5,
      CFSG.LocalAnalysis.GLTheoremA.LevelLieU.mM5 (E u) =
        ((u : GL (Fin 5) F0) : Matrix (Fin 5) (Fin 5) F0).map φ := fun _ => rfl
  set d' : Fin 5 → CFSG.Fischer.F4 := fun i => φ (w i : F0) with hd'
  have hg : CFSG.LocalAnalysis.GLTheoremA.LevelLieU.mM5 (E w₀) = Matrix.diagonal d' := by
    rw [hE]
    exact Matrix.diagonal_map (map_zero φ)
  have hinj : ∀ i j, d' i = d' j → v i = v j := by
    intro i j hij
    have h1 : w i = w j := Units.ext (φ.injective hij)
    have h2 := qtwoDU5_pow_val_inj hω h1
    exact add_right_cancel h2
  have hcnt' : ∀ y : CFSG.Fischer.F4, (Finset.univ.filter fun i => d' i = y).card ≤ 3 := by
    intro y
    by_cases hy : ∃ i₀, d' i₀ = y
    · obtain ⟨i₀, rfl⟩ := hy
      refine le_trans (Finset.card_le_card fun i hi => ?_) (hcnt (v i₀))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hinj i i₀ hi
    · push Not at hy
      rw [Finset.filter_false_of_mem fun i _ => hy i, Finset.card_empty]
      norm_num
  haveI := CFSG.LocalAnalysis.GLTheoremA.LevelLieU.centralizer_diag_solvable (E w₀) d' hg hcnt'
  have hcomm : ∀ u ∈ fixedGroup δ, w₀ * u = u * w₀ := by
    intro u hu
    have h := (qtwoDB39_mem_fixed_iff hF0 _ u).mp hu
    apply Subtype.ext
    apply Units.ext
    have hmat := congrArg (fun A : GL (Fin 5) F0 => (A : Matrix (Fin 5) (Fin 5) F0)) h
    simp only [Units.val_mul] at hmat
    have hscal : (Matrix.diagonal fun i => (w i : F0)) =
        ((ω ^ k.val : F0ˣ) : F0) • Matrix.diagonal fun i => ((ω ^ (v i).val : F0ˣ) : F0) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      simp only [hw, qtwoDU5_pow_val_add hω, Units.val_mul, Pi.smul_apply, smul_eq_mul]
      ring
    change (Matrix.diagonal fun i => (w i : F0)) * ((u : GL (Fin 5) F0) : Matrix _ _ F0) =
      ((u : GL (Fin 5) F0) : Matrix _ _ F0) * Matrix.diagonal fun i => (w i : F0)
    rw [hscal, Matrix.smul_mul, Matrix.mul_smul]
    exact congrArg _ hmat
  let θ : ↥(fixedGroup δ) →* ↥(Subgroup.centralizer
      ({E w₀} : Set CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.M5)) :=
    (E.toMonoidHom.comp (fixedGroup δ).subtype).codRestrict _ fun u => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        Function.comp_apply]
      rw [← map_mul, ← map_mul, hcomm u u.2]
  have hθ : Function.Injective θ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (E.injective h)
  exact Group.isSolvable_of_isSolvable_injective hθ

end Chart

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

theorem qtwoDU5_DJ (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : m = 5) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) :
    ∃ (c : Fin m) (b' : ↥Bs), βL (Additive.ofMul b') = Pi.single c 1 ∧ (b' : G) ∈ B ∧
      D = Subgroup.closure {x, (b' : G)} ∧
        J = (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ := by
  subst hm
  classical
  have hF0 : Nat.card F0 = 4 := hbase.card_field
  have hω : orderOf ω = 3 := hcoords.ω_order
  have hp3 : p = 3 := hbase.p_eq
  have hC : GGConfig p B Bs x L D J := hcfg.1.1.1
  obtain ⟨hDleB, -, hcardD, hxD, hJlay, hJcomp, -⟩ := hC.2.2.1
  have hBBs : B ≤ Bs := hbase.hyp.bstar.1
  have hx_mem : x ∈ Bs := hbase.x_mem
  obtain ⟨d, hdD, hdx⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Subgroup.zpowers x := fun z hz => hcon z hz
    have h1 := Subgroup.card_le_of_le hle
    rw [hcardD, hp3, Nat.card_zpowers, hbase.x_order] at h1
    norm_num at h1
  set s : ↥Bs := ⟨d, hBBs (hDleB hdD)⟩ with hs
  set xB : ↥Bs := ⟨x, hx_mem⟩ with hxB
  set v : DVec 5 := βL (Additive.ofMul s) with hv
  have hxv : βL (Additive.ofMul xB) = fun _ => 1 := hcoords.x_coord hx_mem
  have hpowx : ∀ n : ℕ, βL (Additive.ofMul (xB ^ n)) = fun _ => (n : ZMod 3) := by
    intro n
    rw [ofMul_pow, map_nsmul, hxv]
    funext i
    simp
  have hncst : ¬ ∀ i, v i = v 0 := by
    intro hcst
    apply hdx
    have hsx : s = xB ^ (v 0).val := by
      apply Additive.ofMul.injective
      apply βL.injective
      rw [hpowx, ← hv]
      funext i
      rw [hcst i, ZMod.natCast_zmod_val]
    have h := congrArg Subtype.val hsx
    simp only [hs, hxB, SubmonoidClass.coe_pow] at h
    rw [h]
    exact Subgroup.npow_mem_zpowers x _
  by_cases hcnt : ∀ k : ZMod 3, (Finset.univ.filter fun i => v i = k).card ≤ 3
  ·
    exfalso
    set δ := qtwoDB39_conjAut hF0 (fun i => ω ^ (v i).val) with hδ
    have hHle : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ (fixedGroup δ).map ψ := by
      rintro y ⟨hyL, hyd⟩
      rw [← hbase.range] at hyL
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hyL
      have hdu : ψ u * d = d * ψ u := Subgroup.mem_centralizer_singleton_iff.mp hyd
      obtain ⟨u', hu'mat, hu'ψ⟩ := hcoords.induces s u
      have hu'eq : u' = δ u := by
        apply Subtype.ext
        rw [hδ, qtwoDB39_conjAut_apply, hu'mat]
      have hker : δ u * u⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hu'eq, hu'ψ]
        change d * ψ u * d⁻¹ * (ψ u)⁻¹ = 1
        rw [← hdu]
        group
      have h1 : δ u * u⁻¹ = 1 := by
        have h := hbase.hyp.ker hker
        rw [qtwoDU5_center_eq_bot hF0 (by norm_num) (by norm_num)] at h
        exact Subgroup.mem_bot.mp h
      exact Subgroup.mem_map.mpr ⟨u, mem_fixedGroup.mpr (mul_inv_eq_one.mp h1), rfl⟩
    haveI : Group.IsSolvable ↥(fixedGroup δ) := qtwoDU5_fixed_isSolvable hF0 hω v hcnt
    haveI : Group.IsSolvable ↥((fixedGroup δ).map ψ) :=
      Group.isSolvable_of_surjective (ψ.subgroupMap_surjective (fixedGroup δ))
    have hJle : J ≤ (fixedGroup δ).map ψ :=
      hJcomp.1.trans ((inf_le_inf_left L
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD))).trans hHle)
    haveI : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJle)
    have hq := hJcomp.2.2
    haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hq.2.toNontrivial
    haveI : Nontrivial ↥J := (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J).ne hq.1
  ·
    push Not at hcnt
    obtain ⟨k, hk⟩ := hcnt
    have hsplit : (Finset.univ.filter fun i : Fin 5 => v i = k).card +
        (Finset.univ.filter fun i : Fin 5 => ¬ v i = k).card = 5 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 5)))
        (fun i : Fin 5 => v i = k)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hle1 : (Finset.univ.filter fun i : Fin 5 => ¬ v i = k).card ≤ 1 := by omega
    obtain ⟨c, hc⟩ : ∃ c, Finset.univ.filter (fun i : Fin 5 => ¬ v i = k) = {c} := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
      · exfalso
        apply hncst
        have hall : ∀ i, v i = k := by
          intro i
          by_contra hi
          have hmem : i ∈ Finset.univ.filter (fun i : Fin 5 => ¬ v i = k) := by simp [hi]
          rw [Finset.card_eq_zero.mp h0] at hmem
          simp at hmem
        intro i
        rw [hall i, hall 0]
      · exact Finset.card_eq_one.mp h1
    have hvc : v c ≠ k := by
      have hmem : c ∈ Finset.univ.filter (fun i : Fin 5 => ¬ v i = k) := by
        rw [hc]; exact Finset.mem_singleton_self c
      simpa using hmem
    have hvi : ∀ i, i ≠ c → v i = k := by
      intro i hi
      by_contra hne
      have hmem : i ∈ Finset.univ.filter (fun i : Fin 5 => ¬ v i = k) := by simp [hne]
      rw [hc, Finset.mem_singleton] at hmem
      exact hi hmem
    set t : ZMod 3 := v c - k with ht
    have ht0 : t ≠ 0 := sub_ne_zero.mpr hvc
    set b' : ↥Bs := (s * (xB ^ k.val)⁻¹) ^ t.val with hb'def
    have hb' : βL (Additive.ofMul b') = Pi.single c 1 := by
      rw [hb'def, ofMul_pow, map_nsmul, ofMul_mul, ofMul_inv, map_add, map_neg, hpowx, ← hv]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, nsmul_eq_mul,
        ZMod.natCast_zmod_val]
      by_cases hic : i = c
      · subst hic
        rw [Pi.single_eq_same, ← sub_eq_add_neg, ← ht]
        revert ht0
        generalize t = r
        revert r
        decide
      · rw [Pi.single_eq_of_ne hic, hvi i hic, add_neg_cancel, mul_zero]
    have hb'D : (b' : G) ∈ D := by
      rw [hb'def, SubmonoidClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
        SubmonoidClass.coe_pow]
      exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hdD
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxD _))) _
    have hb'B : (b' : G) ∈ B := hDleB hb'D
    have hpre := ggQTwoDUnit_stdSubPre hcfg le_rfl hbase hcoords hb' hb'B
    obtain ⟨-, -, hcard', -, hJ', -, -⟩ := hpre
    have hle : Subgroup.closure {x, (b' : G)} ≤ D := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hxD
      · exact hb'D
    have hDeq : Subgroup.closure {x, (b' : G)} = D :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardD, hcard', hp3])
    refine ⟨c, b', hb', hb'B, hDeq.symm, ?_⟩
    rw [hJlay, ← hDeq, ← hJ']

end CFSG.StandardType.QTwo

end
