module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL2
public import CFSG.Quasithin.H13.L32ACSkPfU3
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneRoot
public import CFSG.RankThree.CentralLiftU.HypRankOne
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (rkOneQ rkOneQElt rkOneQ_mul
  exists_eq_rkOneQElt exists_norm_add_trace_eq_zero coe_rkOneQElt rkOneUHom rkOneUHom_injective
  rkOneQElt_mem rkOneQ_ef hypIndexFin3 normalizer_hypProjUnitriangular)
open CFSG.RankThree.CentralLiftU (iotaU coe_iotaU iotaU_injective pairIdx blockMat_apply_e
  blockMat_apply_of_notMem_left blockMat_apply_of_notMem_right pairIdx_injective)
open Matrix

section U3

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

theorem hypProj_injOn {u v : hypSU h 1 1} (hu : u ∈ hypUnitriangular h 1 1)
    (hv : v ∈ hypUnitriangular h 1 1) (he : hypProj h 1 1 u = hypProj h 1 1 v) : u = v := by
  have := rkOneUHom_injective h (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) (by
    change hypProjLineAction h 1 1 (hypProj h 1 1 u) = hypProjLineAction h 1 1 (hypProj h 1 1 v)
    rw [he])
  exact congrArg Subtype.val this

theorem commute_of_hypProj {b u : hypSU h 1 1} (hb : b ∈ hypBorel h 1 1)
    (hu : u ∈ hypUnitriangular h 1 1)
    (hc : hypProj h 1 1 b * hypProj h 1 1 u = hypProj h 1 1 u * hypProj h 1 1 b) :
    b * u = u * b := by
  have hu' : (⟨u, hypUnitriangular_le_hypBorel h hu⟩ : hypBorel h 1 1) ∈
      (hypDiagHom h 1 1 le_rfl).ker := by
    rw [ker_hypDiagHom, Subgroup.mem_subgroupOf]
    exact hu
  have hbu := (MonoidHom.normal_ker _).conj_mem _ hu' ⟨b, hb⟩
  rw [ker_hypDiagHom, Subgroup.mem_subgroupOf] at hbu
  have he := hypProj_injOn h hbu hu (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hc, mul_inv_cancel_right])
  calc b * u = b * u * b⁻¹ * b := by group
    _ = u * b := by
      have he' : b * u * b⁻¹ = u := he
      rw [he']

theorem coe_mul_comm {b u : hypSU h 1 1} (h1 : b * u = u * b) :
    ((b : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        ((b : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
  have := congrArg (fun g : hypSU h 1 1 =>
    ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) h1
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem cbAt_psu3 : CBAt (hypPSU h 1 1) (hypProjUnitriangular h 1 1) := by
  have : CharP K 2 := h.charP
  intro b' hb hc
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl] at hb
  obtain ⟨b, hbB, rfl⟩ := hb
  obtain ⟨d, hd⟩ := exists_norm_add_trace_eq_zero h 1
  have hQ := rkOneQElt_mem h hd
  have h1 := coe_mul_comm h (commute_of_hypProj h hbB hQ (hc _ ⟨_, hQ, rfl⟩))
  rw [coe_rkOneQElt] at h1
  set B := ((b : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hBdef
  have hT := blockTriangular_of_mem_hypBorel h le_rfl hbB
  have hze : B (.inr (.inl 0)) (.inl 0) = 0 := hT (by simp [fullPos])
  have hfe : B (.inr (.inr 0)) (.inl 0) = 0 := hT (by simp [fullPos])
  have hfz : B (.inr (.inr 0)) (.inr (.inl 0)) = 0 := hT (by simp [fullPos])
  have e1 := congrFun (congrFun h1 (.inl 0)) (.inr (.inl 0))
  have e2 := congrFun (congrFun h1 (.inr (.inl 0))) (.inr (.inr 0))
  simp [Matrix.mul_apply, Fintype.sum_sum_type, rkOneQ, CFSG.LinearGroups.heisenbergMatrix,
    hypIndexFin3, hze, hfz] at e1 e2
  have hg0 := (mem_hypSU.mp b.2).1
  rw [← hBdef] at hg0
  have hg := congrFun (congrFun hg0 (.inl 0)) (.inr (.inr 0))
  simp [Matrix.mul_apply, Fintype.sum_sum_type, hze, hfe] at hg
  have hdet := (mem_hypSU.mp b.2).2
  rw [← hBdef, ← Matrix.det_submatrix_equiv_self hypIndexFin3.symm, Matrix.det_fin_three] at hdet
  simp [hypIndexFin3, hze, hfe, hfz] at hdet
  have d1 : B (.inr (.inl 0)) (.inr (.inl 0)) = B (.inl 0) (.inl 0) := by linear_combination e1
  have d2 : B (.inr (.inr 0)) (.inr (.inr 0)) = B (.inl 0) (.inl 0) := by
    rw [← d1]
    linear_combination -e2
  set l := B (.inl 0) (.inl 0) with hl
  rw [d1, d2] at hdet
  rw [d2] at hg
  have hl0 : l ≠ 0 := by
    rintro h0
    rw [h0, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have hmap : (l⁻¹ • B).map h.bar = h.bar l⁻¹ • B.map h.bar := by
    ext i j
    simp [map_mul]
  have hsc : l⁻¹ * h.bar l⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, mul_comm, hg, inv_one]
  have hgram : ((l⁻¹ • B).map h.bar)ᵀ * hypGram 1 1 K * (l⁻¹ • B) = hypGram 1 1 K := by
    rw [hmap, Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hg0, hsc, one_smul]
  have hdet' : (l⁻¹ • B).det = 1 := by
    rw [Matrix.det_smul, (mem_hypSU.mp b.2).2]
    simp only [Fintype.card_sum, Fintype.card_fin, mul_one, inv_pow]
    rw [show l ^ (1 + (1 + 1)) = l * l * l by ring, hdet, inv_one]
  set u : hypSU h 1 1 := mkHypSU h (l⁻¹ • B) hgram hdet' with hudef
  have huU : u ∈ hypUnitriangular h 1 1 := by
    refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun a => ?_⟩
    · rw [hudef, coe_mkHypSU, Matrix.smul_apply, show B i j = 0 from hT hij, smul_zero]
    · rw [hudef, coe_mkHypSU, Matrix.smul_apply, smul_eq_mul]
      rcases a with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i
      · exact inv_mul_cancel₀ hl0
      · rw [d1]
        exact inv_mul_cancel₀ hl0
      · rw [d2]
        exact inv_mul_cancel₀ hl0
  set c : Kˣ := Units.mk0 l hl0 with hc
  have hb' : (b : GL (HypIndex 1 1) K) = (u : GL (HypIndex 1 1) K) *
      Matrix.GeneralLinearGroup.scalar (HypIndex 1 1) c := by
    refine Units.ext ?_
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hudef, coe_mkHypSU, ← hBdef]
    ext i j
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, hc,
      Units.val_mk0]
    field_simp
  have hs : u⁻¹ * b ∈ hypScalars h 1 1 := by
    refine mem_normOneScalars.mpr ⟨c, ?_, ?_, ?_⟩
    · rw [hc, Units.val_mk0, UnitaryFieldData.norm, mul_comm]
      exact hg
    · ext
      rw [Units.val_pow_eq_pow_val, hc, Units.val_mk0, Units.val_one,
        show l ^ (2 * 1 + 1) = l * l * l by ring, hdet]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hb', inv_mul_cancel_left]
  refine ⟨u, huU, ?_⟩
  have h2 : hypProj h 1 1 (u⁻¹ * b) = 1 := by
    rw [← MonoidHom.mem_ker, ker_hypProj]
    exact hs
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

theorem invAt_psu3 (hn : 3 ≤ n) : InvAt (hypPSU h 1 1) (hypProjUnitriangular h 1 1) := by
  have : CharP K 2 := h.charP
  have := h.finite
  intro z' hz hz1 hzc
  obtain ⟨u, hu, rfl⟩ := hz
  obtain ⟨a, b, hab, rfl⟩ := exists_eq_rkOneQElt h hu
  have key : ∀ (c d : K) (hcd : h.norm c + h.trace d = 0), h.bar a * c = h.bar c * a := by
    intro c d hcd
    have hQ := rkOneQElt_mem h hcd
    have h1 := coe_mul_comm h (commute_of_hypProj h (hypUnitriangular_le_hypBorel h hu) hQ
      (hzc _ ⟨_, hQ, rfl⟩))
    rw [coe_rkOneQElt, coe_rkOneQElt, rkOneQ_mul, rkOneQ_mul] at h1
    have h2 := congrFun (congrFun h1 (.inl 0)) (.inr (.inr 0))
    rw [rkOneQ_ef, rkOneQ_ef] at h2
    linear_combination -h2
  obtain ⟨d₁, hd₁⟩ := exists_norm_add_trace_eq_zero h 1
  have ha1 := key 1 d₁ hd₁
  rw [mul_one, map_one, one_mul] at ha1
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  obtain ⟨d₂, hd₂⟩ := exists_norm_add_trace_eq_zero h ω
  have haω := key ω d₂ hd₂
  rw [ha1] at haω
  have ha0 : a = 0 := by
    have h3 : a * (ω - h.bar ω) = 0 := by linear_combination haω
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm hω
  subst ha0
  have hb : h.bar b = b := by
    have h3 : h.trace b = 0 := by simpa [UnitaryFieldData.norm] using hab
    rw [UnitaryFieldData.trace] at h3
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h3 - b * h2
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hz1
    have hgg : rkOneQElt h 0 0 hab * rkOneQElt h 0 0 hab = rkOneQElt h 0 0 hab * 1 :=
      Subtype.ext (Units.ext (by
        rw [mul_one, Subgroup.coe_mul, Units.val_mul, coe_rkOneQElt,
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.rkOneQ_mul_zero, add_zero]))
    rw [mul_left_cancel hgg, map_one]
  have hc1 : (1 : K) ∈ h.traceZero := by
    rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
    exact CharTwo.add_self_eq_zero 1
  have hinj : Function.Injective ((hypProj h 1 1).comp (iotaU (ε := 1) h hc1 one_ne_zero 0)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have hmem : iotaU (ε := 1) h hc1 one_ne_zero 0 A ∈ hypScalars h 1 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker]
      exact hA
    obtain ⟨c, -, -, hcA⟩ := mem_normOneScalars.mp hmem
    have hzz := congrFun (congrFun (congrArg (fun g : GL (HypIndex 1 1) K =>
      (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hcA) (.inr (.inl 0))) (.inr (.inl 0))
    simp only [coe_iotaU, Matrix.GeneralLinearGroup.coe_scalar] at hzz
    rw [blockMat_apply_of_notMem_left _ (fun x => by fin_cases x <;> simp [pairIdx])] at hzz
    have hc : c = 1 := Units.ext (by simpa using hzz.symm)
    rw [hc, map_one] at hcA
    exact iotaU_injective h hc1 one_ne_zero 0 (by rw [map_one]; exact Subtype.ext hcA)
  set s : h.fixedField := ⟨b, (UnitaryFieldData.mem_fixedField h).mpr hb⟩ with hsdef
  have hs : s ≠ 0 := fun h0 => hb0 (congrArg Subtype.val h0)
  have hφs : iotaU (ε := 1) h hc1 one_ne_zero 0 (xT s) = rkOneQElt h 0 b hab := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_iotaU, coe_rkOneQElt]
    have he := pairIdx_injective (ε := 1) (0 : Fin 1)
    have hz : ∀ x : Fin 2, pairIdx (ε := 1) (0 : Fin 1) x ≠ .inr (.inl 0) := fun x => by
      fin_cases x <;> simp [pairIdx]
    ext x y
    rcases x with i | i | i <;> rcases y with j | j | j <;>
      obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j
    · exact (blockMat_apply_e he _ 0 0).trans (by
        simp [coe_xT, rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_of_notMem_right _ hz _).trans (by
        simp [rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_e he _ 0 1).trans (by
        simp [coe_xT, rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3, hsdef])
    · exact (blockMat_apply_of_notMem_left _ hz _).trans (by
        simp [rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_of_notMem_left _ hz _).trans (by
        simp [rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_of_notMem_left _ hz _).trans (by
        simp [rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_e he _ 1 0).trans (by
        simp [coe_xT, rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_of_notMem_right _ hz _).trans (by
        simp [rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
    · exact (blockMat_apply_e he _ 1 1).trans (by
        simp [coe_xT, rkOneQ, CFSG.LinearGroups.heisenbergMatrix, hypIndexFin3])
  have hFc : Nat.card h.fixedField = 2 ^ n := UnitaryFieldData.card_fixedField h
  have : CharP h.fixedField 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hFc
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_inv_of_hom hFc hn _ hinj hs
  refine ⟨y, hy1, ?_, hy3⟩
  rw [← hφs]
  exact hy2

end U3

theorem ordTwistedA_two_ne {q : ℕ} (hq : 8 ≤ q) : CFSG.Open.ordTwistedA 2 q ≠ 20160 := by
  intro h
  have hg : Nat.gcd (2 + 1) (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have a1 : 512 ≤ q ^ 3 := by
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have a2 : (64 : ℤ) ≤ (q : ℤ) ^ 2 := by
    have : 64 ≤ q ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    exact_mod_cast this
  have a3 : (512 : ℤ) ≤ (q : ℤ) ^ 3 := by exact_mod_cast a1
  unfold CFSG.Open.ordTwistedA at h
  rw [show 2 * (2 + 1) / 2 = 3 from rfl, show Finset.Icc 2 (2 + 1) = {2, 3} from rfl,
    Finset.prod_pair (by norm_num)] at h
  generalize hA : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = A at h
  generalize hB : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = B at h
  have hA' : 63 ≤ A := by
    rw [← hA]
    norm_num
    omega
  have hB' : 513 ≤ B := by
    rw [← hB]
    norm_num
    omega
  have hN : 512 * (63 * 513) ≤ q ^ 3 * (A * B) := Nat.mul_le_mul a1 (Nat.mul_le_mul hA' hB')
  have h3 := Nat.div_le_div_left hg hg0 (a := q ^ 3 * (A * B))
  rw [h] at h3
  have h4 := Nat.div_le_div_right (c := 3) hN
  omega

theorem false_of_autConf_psu3 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f)
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel M .PSU 3 2 f) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.1 rfl
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hU
  let e' : M ≃* hypPSU hU 1 1 := e.trans (hypPSUEquivStatedProj hU hR (by norm_num)).symm
  have := hU.finite
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h34 : ¬ IsPSL 3 2 2 (hypPSU hU 1 1) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e'.toEquiv, hcard] at h1
    exact ordTwistedA_two_ne h8 h1
  exact not_autConf_of_at (isSylowTwoOf_u3 hU) (n4At_u3 hU (by omega)) h34 (cbAt_psu3 hU)
    (invAt_psu3 hU hf) (h.map e')

end CFSG.Quasithin.H13.S126C
