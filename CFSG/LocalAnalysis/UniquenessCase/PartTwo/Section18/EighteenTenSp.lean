module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTen
public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.GF2Type.Smith1980Orth.IdentArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin Subgroup
open scoped Matrix

theorem k_18_10_Sp_holds : K_18_10_Sp := by
  intro W _ _ hWexp H f p hp hmod _hSp4 hNat v hv
  classical
  obtain ⟨-, K, instK, instFin, hKcard, hreal⟩ := hNat
  letI := instK
  letI := instFin
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableEq K := Classical.decEq K
  rw [show 4 / 2 = 2 from by norm_num] at hreal
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨φ, hφadd, hφker, hφsurj, hφeq⟩ :=
    CFSG.Quasithin.Vol2.KGNat.exists_coord
      (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSp 2 K)) hπ
  set q : ℕ := Nat.card K with hq
  have hq' : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, ← hq]
  have hqpow : q = 2 ^ f := hKcard
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hf1 : 1 ≤ f := by
    rw [← hq, hqpow] at hK2
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0] at hK2
    norm_num at hK2
  have hq2 : 2 ≤ q := by
    rw [hqpow]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  let ρ : StatedSp 2 K →* ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 ⊕ Fin 2 → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (Subgroup.subtype (StatedSp 2 K)))
  letI : DistribMulAction (StatedSp 2 K) (Fin 2 ⊕ Fin 2 → K) :=
    DistribMulAction.compHom (Fin 2 ⊕ Fin 2 → K) ρ
  have hsmul : ∀ (g : StatedSp 2 K) (y : Fin 2 ⊕ Fin 2 → K),
      g • y = ((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y := by
    intro g y
    show (ρ g) • y = _
    rw [LinearEquiv.smul_def]
    simp [ρ, Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  have hsmul_apply : ∀ (g : StatedSp 2 K) (y : Fin 2 ⊕ Fin 2 → K), g • y = (ρ g) y := by
    intro g y
    show (ρ g) • y = (ρ g) y
    rw [LinearEquiv.smul_def]
  have hsmul_inv : ∀ (g : StatedSp 2 K) (y : Fin 2 ⊕ Fin 2 → K), g⁻¹ • (g • y) = y := by
    intro g y
    rw [hsmul_apply, hsmul_apply, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  let x : Fin 2 ⊕ Fin 2 → K := φ v
  have hx : x ≠ 0 := by
    intro h0
    exact hv ((hφker v (Subgroup.mem_top v)).mp h0)
  set St : Subgroup (StatedSp 2 K) := MulAction.stabilizer (StatedSp 2 K) x with hSt
  haveI : Fintype (StatedSp 2 K) := Fintype.ofFinite _
  have hcardM : Nat.card (Fin 2 ⊕ Fin 2 → K) = q ^ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_sum, hq']
    norm_num
  have hcardPi : Fintype.card (Fin 2 ⊕ Fin 2 → K) = q ^ 4 := by
    rw [← Nat.card_eq_fintype_card, hcardM]
  have hcard0 : Fintype.card {y : Fin 2 ⊕ Fin 2 → K // y = 0} = 1 := by
    simp
  have hcardne : Nat.card {y : Fin 2 ⊕ Fin 2 → K // y ≠ 0} = q ^ 4 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hcardPi, hcard0]
  have horbit : MulAction.orbit (StatedSp 2 K) x = {y : Fin 2 ⊕ Fin 2 → K | y ≠ 0} := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
      rw [← hg]
      intro h0
      have h1 : g⁻¹ • (g • x) = 0 := by
        rw [h0, hsmul_apply, map_zero]
      rw [hsmul_inv] at h1
      exact hx h1
    · intro hy
      obtain ⟨g, hg⟩ := CFSG.Quasithin.MS93.statedSp2_transitive x y hx hy
      exact MulAction.mem_orbit_iff.mpr ⟨g, by rwa [hsmul]⟩
  have horbitCard : Nat.card (MulAction.orbit (StatedSp 2 K) x) = q ^ 4 - 1 := by
    rw [horbit]
    exact hcardne
  have hcardG : Nat.card (StatedSp 2 K) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, ← hq]
  have hOS : Nat.card (MulAction.orbit (StatedSp 2 K) x) * Nat.card St =
      Nat.card (StatedSp 2 K) := by
    have h := Subgroup.card_mul_index St
    have hidx : St.index = Nat.card (MulAction.orbit (StatedSp 2 K) x) := by
      change (MulAction.stabilizer (StatedSp 2 K) x).index = _
      rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
      rfl
    rw [hidx, mul_comm] at h
    exact h
  have hq41 : 0 < q ^ 4 - 1 := by
    have h16 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq2 4
    norm_num at h16
    omega
  have hStCard : Nat.card St = q ^ 4 * (q ^ 2 - 1) := by
    have heq : (q ^ 4 - 1) * Nat.card St =
        (q ^ 4 - 1) * (q ^ 4 * (q ^ 2 - 1)) := by
      calc
        (q ^ 4 - 1) * Nat.card St
            = Nat.card (MulAction.orbit (StatedSp 2 K) x) * Nat.card St := by
              rw [horbitCard]
        _ = Nat.card (StatedSp 2 K) := hOS
        _ = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := hcardG
        _ = (q ^ 4 - 1) * (q ^ 4 * (q ^ 2 - 1)) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left (n := q ^ 4 - 1) hq41 heq
  have hodd2f : Odd (2 ^ f + 1) :=
    CFSG.GF2Type.Smith1980Orth.odd_two_pow_add_one_of_pos hf1
  have hpdvdInt : (p : ℤ) ∣ (2 : ℤ) ^ f + 1 := by
    have h := hmod.dvd
    have h' : (p : ℤ) ∣ -((-1 : ℤ) - (2 : ℤ) ^ f) := dvd_neg.mpr h
    simpa using h'
  have hpdvd : p ∣ 2 ^ f + 1 := by
    exact_mod_cast hpdvdInt
  have hp2 : p ≠ 2 := Odd.ne_two_of_dvd_nat hodd2f hpdvd
  have hpq1 : p ∣ q + 1 := by
    rw [hqpow]
    exact hpdvd
  have hpq2 : p ∣ q ^ 2 - 1 := by
    have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      simpa using Nat.sq_sub_sq q 1
    rw [hsq]
    exact dvd_mul_of_dvd_left hpq1 (q - 1)
  have hpdvdSt : p ∣ Nat.card St := by
    rw [hStCard]
    exact dvd_mul_of_dvd_right hpq2 (q ^ 4)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' p hpdvdSt
  have hπinj : Function.Injective π :=
    CFSG.Quasithin.G64.RealizesVia.injective_of_faithful'
      (FFModel.nat_faithful (StatedSp 2 K)) hπ
  let h : ↥H := π (g : StatedSp 2 K)
  have hg'ord : orderOf (g : StatedSp 2 K) = p := (Subgroup.orderOf_coe g).trans hgord
  have hhpow : h ^ p = 1 := by
    have h1 : (g : StatedSp 2 K) ^ p = 1 := by
      rw [← hg'ord]
      exact pow_orderOf_eq_one _
    change (π (g : StatedSp 2 K)) ^ p = 1
    have hmap : (π (g : StatedSp 2 K)) ^ p = π ((g : StatedSp 2 K) ^ p) :=
      (map_pow π (g : StatedSp 2 K) p).symm
    rw [hmap, h1]
    exact map_one π
  have hhne : h ≠ 1 := by
    intro h1
    have hπg : π (g : StatedSp 2 K) = 1 := h1
    have hg1 : (g : StatedSp 2 K) = 1 := hπinj (by
      rw [hπg]
      exact (map_one π).symm)
    have h2 : orderOf (g : StatedSp 2 K) = 1 := by rw [hg1, orderOf_one]
    rw [hg'ord] at h2
    exact hp.ne_one h2
  have hhord : orderOf h = p := orderOf_eq_prime hhpow hhne
  have hgfix : (g : StatedSp 2 K) • x = x := by
    refine MulAction.mem_stabilizer_iff.mp ?_
    rw [← hSt]
    exact g.2
  have hxfix : (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSp 2 K)).lin
      (g : StatedSp 2 K) x = x := by
    have h1 := hsmul (g : StatedSp 2 K) x
    rw [hgfix] at h1
    rw [CFSG.Quasithin.Vol2.KGNat.linModelNat_lin]
    exact h1.symm
  have hφhv : φ ((h : MulAut W) v) = x := by
    have h1 := hφeq (g : StatedSp 2 K) v (Subgroup.mem_top v)
    rwa [hxfix, show x = φ v from rfl] at h1
  let c : W := (h : MulAut W) v * v⁻¹
  have hvv : v * v = 1 := by simpa [pow_two] using hWexp v
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hφ1 : φ (1 : W) = 0 := (hφker 1 (Subgroup.mem_top 1)).mpr (fixV H).one_mem
  have hxx : φ v + φ v = 0 := by
    have h := hφadd v (Subgroup.mem_top v) v (Subgroup.mem_top v)
    rw [hvv, hφ1] at h
    exact h.symm
  have hφc : φ c = 0 := by
    have h := hφadd ((h : MulAut W) v) (Subgroup.mem_top _) v⁻¹ (Subgroup.mem_top _)
    rw [hφhv, hvinv, hxx] at h
    simpa [c, hvinv] using h
  have hcFix : c ∈ fixV H := (hφker c (Subgroup.mem_top c)).mp hφc
  have hcFixed : (h : MulAut W) c = c := (mem_fixV.mp hcFix) (h : MulAut W) h.2
  have hcMul : (h : MulAut W) v = c * v := by
    rw [show c = (h : MulAut W) v * v⁻¹ from rfl]
    group
  have hpow : ∀ k : ℕ, ((h : MulAut W) ^ k) v = c ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hcFixed, hcMul]
      rw [pow_succ]
      group
  have hhWp : (h : MulAut W) ^ p = 1 := by
    have h1 : h ^ p = 1 := by rw [← hhord]; exact pow_orderOf_eq_one h
    exact congrArg (fun x : ↥H => (x : MulAut W)) h1
  have hcp : c ^ p = 1 := by
    have h := hpow p
    rw [hhWp] at h
    have h' : c ^ p * v = 1 * v := by rw [one_mul]; exact h.symm
    exact mul_right_cancel h'
  have hc2 : c ^ 2 = 1 := by simpa [pow_two] using hWexp c
  have hoddp : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hoddp
  have hc1 : c = 1 := by
    have h := hcp
    rw [hk] at h
    rw [show c ^ (2 * k + 1) = (c ^ 2) ^ k * c by rw [pow_succ, pow_mul], hc2] at h
    simpa using h
  have hhv : (h : MulAut W) v = v := by rw [hcMul, hc1, one_mul]
  have hmem : (h : MulAut W) ∈ centVec H v := ⟨h.2, hhv⟩
  have hordW : orderOf ((h : MulAut W)) = p := (Subgroup.orderOf_coe h).trans hhord
  refine ⟨hp, ?_⟩
  have hdvd := Subgroup.orderOf_dvd_natCard (centVec H v) hmem
  rwa [hordW] at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
