module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105AutOddU4
public import CFSG.HardMathSupport.U4FF.Defs
public import CFSG.HardMathSupport.U4FF.Disp
public import CFSG.HardMathSupport.U4FF.Outer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.U4FF

theorem exists_ne_one_pow_two_pow_add_one {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) :
    ∃ u : K, u ≠ 1 ∧ u ^ (2 ^ n + 1) = 1 := by
  haveI : Finite K := h.finite
  have hn : 1 ≤ n := h.one_le
  have heven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hne : 2 ^ n + 1 ≠ 1 := by
    have : 0 < 2 ^ n := by positivity
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := heven
    obtain ⟨l, hl⟩ := hpd
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have h2n : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    rw [Nat.mul_comm 2 n, pow_mul]
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [← Nat.sq_sub_sq (2 ^ n) 1, one_pow]
  have hcard : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, h.card, h2n, hsq]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by
    rw [hcard]
    exact dvd_mul_of_dvd_left hpd _)
  have hu1 : u ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hu ▸ hpd)
  refine ⟨(u : K), ?_, ?_⟩
  · intro h1
    have h2 : u = 1 := Units.ext h1
    rw [h2, orderOf_one] at hu
    have := hp.one_lt
    omega
  · rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]

theorem exists_torus_commutator {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)]
    {n : ℕ} {L : Subgroup (MulAut S)} (hL : IsU4Group n L) (hirr : IsIrrOn L) {σ : MulAut S}
    (hσ2 : σ * σ = 1) (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut S))) (hσL : σ ∉ L)
    {K : Type} [Field K] (h : UnitaryFieldData 2 n K) (η : ↥L ≃* gramSU h (miyamotoJ4 K)) :
    ∃ (x : ↥L) (t : gramSU h (miyamotoJ4 K)) (w : K), w ≠ 1 ∧ w ^ (2 ^ n + 1) = 1 ∧
      disp (x : MulAut S) ≤ 2 * disp σ ∧
      (((t * η x * t⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal ![w, w⁻¹, w⁻¹, w] := by
  classical
  have hS : ∀ s : S, s * s = 1 := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  let A : Subgroup (MulAut S) := Subgroup.zpowers σ
  have hσA : σ ∈ A := Subgroup.mem_zpowers σ
  have hA : CFSG.Quasithin.IsElemAbelian2 A := by
    constructor
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · intro a ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have h2 : σ ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, sq, hσ2]
      calc (σ ^ m) ^ 2 = (σ ^ m) ^ ((2 : ℕ) : ℤ) := (zpow_natCast (σ ^ m) 2).symm
        _ = σ ^ (m * ((2 : ℕ) : ℤ)) := (zpow_mul σ m _).symm
        _ = σ ^ (((2 : ℕ) : ℤ) * m) := by rw [mul_comm]
        _ = (σ ^ ((2 : ℕ) : ℤ)) ^ m := zpow_mul σ _ m
        _ = 1 := by rw [h2, one_zpow]
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S)) := Subgroup.zpowers_le.mpr hσN
  have hirr' : IsIrrOn (L ⊔ A) := fun W hW =>
    hirr W (fun x hx w hw => hW x (Subgroup.mem_sup_left hx) w hw)
  have hC := sup_inf_centralizer_eq_bot hS hL hA hAN hirr'
  let xN : Subgroup.normalizer (L : Set (MulAut S)) := ⟨σ, hAN hσA⟩
  have hα2 : miyamotoAct h L η xN * miyamotoAct h L η xN = 1 := by
    rw [← map_mul]
    have hx : xN * xN = 1 := Subtype.ext hσ2
    rw [hx, map_one]
  have hα1 : miyamotoAct h L η xN ≠ 1 := by
    intro he
    have hcent := (miyamotoAct_eq_one_iff h L η xN).1 he
    have hmem : σ ∈ (L ⊔ A) ⊓ Subgroup.centralizer (L : Set (MulAut S)) :=
      ⟨Subgroup.mem_sup_right hσA, hcent⟩
    rw [hC, Subgroup.mem_bot] at hmem
    exact hσL (hmem ▸ L.one_mem)
  have hord : orderOf (miyamotoAct h L η xN) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hff : miyamotoFieldFactor h (miyamotoAct h L η xN) ≠ 1 := fun he =>
    hσL (mem_of_fieldFactor_eq_one hS hL hA hAN hirr' h η hσA he)
  obtain ⟨t, ht⟩ := exists_conj_eq_u_or_uz1 h hord hff
  obtain ⟨u₀, hu₀ne, hu₀q⟩ := exists_ne_one_pow_two_pow_add_one h
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hu₀q
    exact zero_ne_one hu₀q
  let U₀ : Kˣ := Units.mk0 u₀ hu₀0
  have hU₀q : (U₀ : K) ^ (2 ^ n + 1) = 1 := hu₀q
  have hbarU₀ : h.bar (U₀ : K) = ((U₀⁻¹ : Kˣ) : K) := by
    rw [h.bar_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hU₀q])
  set d : Fin 4 → K :=
    ![(U₀ : K), ((U₀⁻¹ : Kˣ) : K), ((U₀⁻¹ : Kˣ) : K), (U₀ : K)] with hd
  set e : Fin 4 → K :=
    ![((U₀⁻¹ : Kˣ) : K), (U₀ : K), (U₀ : K), ((U₀⁻¹ : Kˣ) : K)] with he
  let w : K := ((U₀ : K) ^ 2)⁻¹
  let g₀ : gramSU h (miyamotoJ4 K) :=
    ⟨miyamotoIHom h (U₀, U₀⁻¹), by
      rw [miyamotoIHom_mem_gramSU_iff, Units.ext_iff]
      simp [miyamotoIParam, hbarU₀, hu₀0, Units.val_mk0]⟩
  have hg₀mat : (((g₀ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d := by
    have hbase : ((miyamotoIHom h (U₀, U₀⁻¹) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal
          ![(U₀ : K), ((U₀⁻¹ : Kˣ) : K), (h.bar ((U₀⁻¹ : Kˣ) : K))⁻¹,
            (h.bar (U₀ : K))⁻¹] := by
      simp [miyamotoIHom, miyamotoDiag]
    show ((miyamotoIHom h (U₀, U₀⁻¹) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal d
    rw [hbase, show ![(U₀ : K), ((U₀⁻¹ : Kˣ) : K), (h.bar ((U₀⁻¹ : Kˣ) : K))⁻¹,
        (h.bar (U₀ : K))⁻¹] = d by
      funext i
      fin_cases i <;> simp [d, hbarU₀]]
  have hg₀invmat : (((g₀⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal e := by
    have hGL : ((g₀⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
        miyamotoIHom h (U₀⁻¹, U₀) := by
      rw [Subgroup.coe_inv]
      show ((miyamotoIHom h (U₀, U₀⁻¹) : GL (Fin 4) K))⁻¹ =
        miyamotoIHom h (U₀⁻¹, U₀)
      rw [← map_inv, Prod.inv_mk, inv_inv]
    have hbase : ((miyamotoIHom h (U₀⁻¹, U₀) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal
          ![((U₀⁻¹ : Kˣ) : K), (U₀ : K), (h.bar (U₀ : K))⁻¹,
            (h.bar ((U₀⁻¹ : Kˣ) : K))⁻¹] := by
      simp [miyamotoIHom, miyamotoDiag]
    rw [hGL, hbase, show ![((U₀⁻¹ : Kˣ) : K), (U₀ : K), (h.bar (U₀ : K))⁻¹,
        (h.bar ((U₀⁻¹ : Kˣ) : K))⁻¹] = e by
      funext i
      fin_cases i <;> simp [e, hbarU₀]]
  have hg₀sqmat : ((((g₀ * g₀)⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![w, w⁻¹, w⁻¹, w] := by
    rw [show (g₀ * g₀)⁻¹ = g₀⁻¹ * g₀⁻¹ by group, Subgroup.coe_mul, Units.val_mul,
      hg₀invmat, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => e i * e i) = ![w, w⁻¹, w⁻¹, w] by
      funext i
      fin_cases i <;> simp [e, w] <;> first | rw [← pow_two, ← inv_pow] | rw [← pow_two]]
  let u : MulAut (gramSU h (miyamotoJ4 K)) := miyamotoFieldAut h (miyamotoBarEquiv h)
  let z : gramSU h (miyamotoJ4 K) := miyamotoZ1S h
  have hβu : u g₀ = g₀⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_miyamotoFieldAut_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hg₀invmat, hg₀mat,
      Matrix.diagonal_map (show ⇑(miyamotoBarEquiv h) 0 = 0 by simp)]
    change Matrix.diagonal (fun i => ⇑(miyamotoBarEquiv h) (d i)) = Matrix.diagonal e
    rw [show (fun i => ⇑(miyamotoBarEquiv h) (d i)) = e by
      funext i
      fin_cases i <;> simp [miyamotoBarEquiv_apply, d, e, hbarU₀]]
  have hzcomm : z * g₀ = g₀ * z := by
    show miyamotoZ1S h * g₀ = g₀ * miyamotoZ1S h
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hg₀mat, hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoZ1S, coe_miyamotoXGL, miyamotoX, Matrix.diagonal, Matrix.mul_apply,
        Fin.sum_univ_four]
  have hβuz : (MulAut.conj z * u) g₀ = g₀⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, hβu]
    have hcomm : Commute z g₀ := hzcomm
    rw [hcomm.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hw1 : w ≠ 1 := by
    intro h1
    have h2 : (U₀ : K) ^ 2 = 1 := inv_eq_one.mp h1
    have hn : 1 ≤ n := h.one_le
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have h3 : (U₀ : K) ^ (2 ^ n + 1) = 1 := hU₀q
    rw [show 2 ^ n + 1 = 2 * 2 ^ (n - 1) + 1 by rw [h2n]] at h3
    rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h3
    exact hu₀ne h3
  have hwq : w ^ (2 ^ n + 1) = 1 := by
    rw [show w = ((U₀ : K) ^ 2)⁻¹ by rfl, inv_pow, ← pow_mul,
      show 2 * (2 ^ n + 1) = (2 ^ n + 1) * 2 by ring, pow_mul, hU₀q]
    simp
  have finish : ∀ β : MulAut (gramSU h (miyamotoJ4 K)), β g₀ = g₀⁻¹ →
      MulAut.conj t * miyamotoAct h L η xN * (MulAut.conj t)⁻¹ = β →
      ∃ (x : ↥L) (w : K), w ≠ 1 ∧ w ^ (2 ^ n + 1) = 1 ∧
        disp (x : MulAut S) ≤ 2 * disp σ ∧
        (((t * η x * t⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![w, w⁻¹, w⁻¹, w] := by
    intro β hβg₀ hβ
    have hαform : ∀ g, miyamotoAct h L η xN g = t⁻¹ * β (t * g * t⁻¹) * t := by
      intro g
      have hαeq : miyamotoAct h L η xN = (MulAut.conj t)⁻¹ * β * MulAut.conj t := by
        rw [← hβ]
        group
      rw [hαeq]
      simp [MulAut.mul_apply, MulAut.conj_apply]
    let ĝ : ↥L := η.symm (t⁻¹ * g₀ * t)
    have hηĝ : η ĝ = t⁻¹ * g₀ * t := MulEquiv.apply_symm_apply η _
    have hmemc : σ * (ĝ : MulAut S) * σ⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hσN (ĝ : MulAut S)).mp ĝ.2
    let c : ↥L := ⟨σ * (ĝ : MulAut S) * σ⁻¹, hmemc⟩
    have hcη : η c = miyamotoAct h L η xN (η ĝ) := by
      have hcoe := coe_symm_miyamotoAct_apply h L η xN (η ĝ)
      have h2 : η.symm (miyamotoAct h L η xN (η ĝ)) = c := by
        apply Subtype.ext
        rw [hcoe]
        simp [c, xN]
      rw [← h2, MulEquiv.apply_symm_apply]
    let x' : ↥L := c * ĝ⁻¹
    have hαg₀ : miyamotoAct h L η xN (t⁻¹ * g₀ * t) = t⁻¹ * g₀⁻¹ * t := by
      rw [hαform, show t * (t⁻¹ * g₀ * t) * t⁻¹ = g₀ by group, hβg₀]
    have hηx' : η x' = t⁻¹ * (g₀ * g₀)⁻¹ * t := by
      show η (c * ĝ⁻¹) = t⁻¹ * (g₀ * g₀)⁻¹ * t
      rw [map_mul, map_inv, hcη, hηĝ, hαg₀]
      group
    have hmain : t * η x' * t⁻¹ = (g₀ * g₀)⁻¹ := by
      rw [hηx']
      group
    have hdisp : disp (x' : MulAut S) ≤ 2 * disp σ := by
      have hx'val : (x' : MulAut S) = σ * (ĝ : MulAut S) * σ⁻¹ * (ĝ : MulAut S)⁻¹ := rfl
      rw [hx'val, show σ * (ĝ : MulAut S) * σ⁻¹ * (ĝ : MulAut S)⁻¹ =
        σ * ((ĝ : MulAut S) * σ⁻¹ * (ĝ : MulAut S)⁻¹) by group]
      calc disp (σ * ((ĝ : MulAut S) * σ⁻¹ * (ĝ : MulAut S)⁻¹))
          ≤ disp ((ĝ : MulAut S) * σ⁻¹ * (ĝ : MulAut S)⁻¹) + disp σ := disp_mul_le _ _
        _ = disp σ + disp σ := by rw [disp_conj, hσinv]
        _ = 2 * disp σ := by ring
    refine ⟨x', w, hw1, hwq, hdisp, ?_⟩
    rw [hmain]
    exact hg₀sqmat
  rcases ht with ht | ht
  · obtain ⟨x, w', hw1', hwq', hdisp, hmat⟩ := finish u hβu ht
    exact ⟨x, t, w', hw1', hwq', hdisp, hmat⟩
  · obtain ⟨x, w', hw1', hwq', hdisp, hmat⟩ := finish (MulAut.conj z * u) hβuz ht
    exact ⟨x, t, w', hw1', hwq', hdisp, hmat⟩

theorem exists_torus_commutator_SU {S : Type} [CommGroup S] [Finite S]
    [Fact (∀ s : S, s * s = 1)] {n : ℕ} {L : Subgroup (MulAut S)} (hL : IsU4Group n L)
    (hirr : IsIrrOn L) {σ : MulAut S} (hσ2 : σ * σ = 1)
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut S))) (hσL : σ ∉ L)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥L ≃* ↥(CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4)) :
    ∃ (x : ↥L) (t : ↥(CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4)) (w : K),
      w ≠ 1 ∧ w ^ (2 ^ n + 1) = 1 ∧ disp (x : MulAut S) ≤ 2 * disp σ ∧
      (((t * η x * t⁻¹ : ↥(CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![w, w⁻¹, w⁻¹, w] := by
  classical
  have hU : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, one_le_of_isU4Group hL, by rw [hK, ← pow_mul, Nat.mul_comm n 2]⟩
  have hSU := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd.su_eq_gramSU_miyamotoJ4
    hU
  let e : ↥(CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4) ≃*
      gramSU hU (miyamotoJ4 K) := MulEquiv.subgroupCongr hSU
  let η' : ↥L ≃* gramSU hU (miyamotoJ4 K) := η.trans e
  obtain ⟨x, t, w, hw1, hwq, hdisp, hmat⟩ :=
    exists_torus_commutator (K := K) (n := n) hL hirr hσ2 hσN hσL hU η'
  refine ⟨x, e.symm t, w, hw1, hwq, hdisp, ?_⟩
  have hcoe : ∀ y : ↥(CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4),
      ((e y : gramSU hU (miyamotoJ4 K)) : GL (Fin 4) K) = ((y : GL (Fin 4) K)) := by
    intro y
    rfl
  have hGL : (((e.symm t * η x * (e.symm t)⁻¹ : ↥(CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4)) : GL (Fin 4) K)) =
      (((t * η' x * t⁻¹ : gramSU hU (miyamotoJ4 K)) : GL (Fin 4) K)) := by
    rw [← hcoe (e.symm t * η x * (e.symm t)⁻¹)]
    congr 1
  simpa only [hGL] using hmat

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
