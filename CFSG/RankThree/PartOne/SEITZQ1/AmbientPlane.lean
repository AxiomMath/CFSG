module

public import CFSG.RankThree.PartOne.SEITZQ1.Endgame
public import CFSG.RankThree.PartOne.SEITZQ1.Letters
public import CFSG.RankThree.PartOne.SEITZQ1.Plane
public import CFSG.RankThree.PartOne.SEITZQ1.Norm
public import CFSG.RankThree.PartOne.SEITZQ1.Cent
public import CFSG.RankThree.PartOne.CTP.SeitzUToral
public import CFSG.RankThree.PartOne.SEITZQ1.Embed

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Unitary

variable {f : ℕ} {K' : Type} [Field K']

theorem q1_exists_letters (h : UnitaryFieldData 2 f K') {ω : K'} (hω : ω ^ 2 + ω + 1 = 0)
    (hbar : h.bar ω = ω + 1) :
    ∃ u : Fin 9 → unitarySU 2 f K' 3,
      ∀ k, ((u k : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = f4MEv ω (q1LetterF4 k) := by
  have : CharP K' 2 := h.charP
  have hdet : ∀ k, (f4MEv ω (q1LetterF4 k)).det = 1 := fun k => by
    rw [f4MEv_det hω, (q1Letter_checks k).1]
    rfl
  refine ⟨fun k => ⟨Matrix.SpecialLinearGroup.toGL ⟨f4MEv ω (q1LetterF4 k), hdet k⟩,
    (mem_unitarySU_iff h).2 ⟨hdet k, ?_⟩⟩, fun k => rfl⟩
  change ((f4MEv ω (q1LetterF4 k)).map h.bar)ᵀ * f4MEv ω (q1LetterF4 k) = 1
  rw [f4MEv_map_transpose h.bar hbar, ← f4MEv_mul hω, (q1Letter_checks k).2.1, f4MEv_one]

variable {L : Type} [Field L]

theorem f4MEv_map (ι : K' →+* L) (ω : K') (A : F4M) :
    (f4MEv ω A).map ι = f4MEv (ι ω) A := by
  ext i j
  simp only [Matrix.map_apply, f4MEv, Matrix.of_apply]
  generalize A i j = t
  fin_cases t <;> simp [f4Ev]

theorem q1SUToSL_letter [CharP L 2] (h : UnitaryFieldData 2 f K') (ι : K' →+* L) {ω : K'}
    (hω : ω ^ 2 + ω + 1 = 0) (u : unitarySU 2 f K' 3) (k : Fin 9)
    (hu : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = f4MEv ω (q1LetterF4 k)) :
    q1SUToSL h ι u = q1TvProd (ι ω) (q1LetterDec k) := by
  have hω' : ι ω ^ 2 + ι ω + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω, map_zero]
  refine Subtype.ext ?_
  rw [coe_q1SUToSL, hu, f4MEv_map, ← (q1Letter_checks k).2.2.1,
    coe_q1TvProd hω' _ (q1Letter_checks k).2.2.2]

theorem q1_eq_one_of_center (h : UnitaryFieldData 2 f K') (ι : K' →+* L) {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {u : unitarySU 2 f K' 3} (hu : u ^ p = 1)
    (hc : q1SUToSL h ι u ∈ Subgroup.center SL(3, L)) : u = 1 := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin] at hr3
  have hjp : ((q1SUToSL h ι u : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) ^ p = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← map_pow, hu, map_one]
    rfl
  have hrp : r ^ p = 1 := by
    rw [← hr, ← map_pow] at hjp
    have := congrFun (congrFun hjp 0) 0
    simpa using this
  have hr1 : r = 1 := by
    have h3 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3
    have hpp : orderOf r ∣ p := orderOf_dvd_of_pow_eq_one hrp
    have hcop : Nat.Coprime 3 p :=
      (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
    have h1 : orderOf r ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h3 hpp
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hj1 : ((q1SUToSL h ι u : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1 := by
    rw [← hr, hr1, map_one]
  rw [coe_q1SUToSL] at hj1
  have hm : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 := by
    exact Matrix.map_injective ι.injective
      (hj1.trans (Matrix.map_one ι ι.map_zero ι.map_one).symm)
  exact Subtype.ext (Units.ext hm)

end Unitary

section Center

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem q1_mem_center_of_psi0 (hF : IsReeFrob a F) {g : SL(3, L)} (hg : q1Psi0 hF g = 1) :
    g ∈ Subgroup.center SL(3, L) := by
  rw [Subgroup.mem_center_iff]
  intro k
  apply q1Rho_injective
  have h1 : q1Rho L g = (q1PsiRho F a g)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← q1Psi0_apply]; exact hg)
  have h2 : Commute (q1Rho L k) (q1PsiRho F a g) := q1PsiRho_commute hF k g
  rw [map_mul, map_mul, h1]
  exact h2.inv_right.eq

end Center

section Main


theorem q1_phi2_plane {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * m + 1) + 1) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag K), E ≤ ReeTag.F4.reeGamma K m ∧
      (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
      Subgroup.closure {k | k ∈ ReeTag.F4.reeGamma K m ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} =
        ReeTag.F4.reeGamma K m := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := L) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' := GaloisField 2 (2 * (2 * m + 1))
  have h : UnitaryFieldData 2 (2 * m + 1) K' :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) K' := Algebra.IsAlgebraic.of_finite (ZMod 2) K'
  let ι : K' →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := K') (M := L)).toRingHom
  obtain ⟨ω', hω', hbar⟩ := q1_exists_omega h (odd_two_mul_add_one m)
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hFr : ∀ c, D.Frq (ι c) = ι (h.bar c) := fun c => by
    rw [frq_eq_pow D hK, UnitaryFieldData.bar_apply, map_pow]
  obtain ⟨Ψ, hΨ⟩ := q1_exists_hom D hK hω (q1SUToSL h ι) (q1SUToSL_fixed h ι D.Frq hFr)
  obtain ⟨E'', hcomm, hexp, hcard, hdiag, x₀, hx₀E, hx₀1, z, hz, hx₀z⟩ :=
    q1_plane h hp (by omega) (by omega) hpq
  have hinj : ∀ u ∈ E'', Ψ u = 1 → u = 1 := by
    intro u hu h1
    have h3 := (hΨ u).symm
    rw [h1, map_one, mul_inv_eq_one, mul_eq_left] at h3
    exact q1_eq_one_of_center h ι hp (by omega) (hexp u hu) (q1_mem_center_of_psi0 D.isFrob h3)
  let EΓ : Subgroup (ReeTag.F4.reeGamma K m) := E''.map Ψ
  let E : Subgroup (ModGL ReeTag.F4.tag K) := EΓ.map (ReeTag.F4.reeGamma K m).subtype
  have hexpΓ : ∀ x ∈ EΓ, x ^ p = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  have hcardΓ : Nat.card EΓ = p ^ 2 := by
    have hi : Function.Injective (Ψ.comp E''.subtype) := by
      rw [injective_iff_map_eq_one]
      intro v hv
      exact Subtype.ext (hinj v v.2 hv)
    have hr : (Ψ.comp E''.subtype).range = EΓ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, hcard]
  have hEΓ1 : ∀ u ∈ E'', u ≠ 1 → ((Ψ u : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K) ≠ 1 :=
    fun u hu hu1 h1 => hu1 (hinj u hu (Subtype.ext h1))
  set DE := Subgroup.closure
    {k | k ∈ ReeTag.F4.reeGamma K m ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} with hDE
  have hmem : ∀ k ∈ ReeTag.F4.reeGamma K m, ∀ x ∈ E, x ≠ 1 → k * x = x * k → k ∈ DE :=
    fun k hk x hx hx1 hkx => Subgroup.subset_closure ⟨hk, x, hx, hx1, hkx⟩
  have hDle : DE ≤ ReeTag.F4.reeGamma K m := (Subgroup.closure_le _).2 fun k hk => hk.1
  have hq : 2 ^ (2 * m + 1) ≠ 2 := by
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hSU : ∀ u : unitarySU 2 (2 * m + 1) K' 3,
      ((Ψ u : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K) ∈ DE := by
    intro u
    have hcl := CFSG.RankThree.PartOne.CTP.closure_centralizers_unitarySU_of_dvd_add_one (n := 2)
      h hp hpq hq E'' hcomm hexp hcard
    have hu : u ∈ Subgroup.closure {g | ∃ x ∈ E'', x ≠ 1 ∧ g * x = x * g} := by
      rw [hcl]; exact Subgroup.mem_top u
    have h2 := Subgroup.mem_map_of_mem ((ReeTag.F4.reeGamma K m).subtype.comp Ψ) hu
    rw [MonoidHom.map_closure] at h2
    refine (Subgroup.closure_le _).2 ?_ h2
    rintro _ ⟨g, ⟨x, hx, hx1, hgx⟩, rfl⟩
    refine hmem _ (Ψ g).2 _ ⟨Ψ x, ⟨x, hx, rfl⟩, rfl⟩ (hEΓ1 x hx hx1) ?_
    change ((Ψ g * Ψ x : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K) =
      ((Ψ x * Ψ g : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K)
    rw [← map_mul, ← map_mul, hgx]
  obtain ⟨g, hg⟩ := q1_exists_g D hω
  have hT : ∀ x ∈ EΓ, (q1C (ι ω'))⁻¹ * thetaGamma L m x * q1C (ι ω') ∈
      torusGroup ReeTag.F4.tag L := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hΨ u, show (q1C (ι ω'))⁻¹ * (q1C (ι ω') * q1Psi0 D.isFrob (q1SUToSL h ι u) *
      (q1C (ι ω'))⁻¹) * q1C (ι ω') = q1Psi0 D.isFrob (q1SUToSL h ι u) by group]
    refine q1Psi0_mem_torusGroup D.isFrob _ fun i k hik => ?_
    rw [coe_q1SUToSL, Matrix.map_apply, hdiag u hu i k hik, map_zero]
  have hnorm := q1_conj_mem hK hp hp5 hpq EΓ hT hexpΓ hcardΓ g hg
  have hconj : ∀ y ∈ DE,
      (g : ModGL ReeTag.F4.tag K) * y * (g : ModGL ReeTag.F4.tag K)⁻¹ ∈ DE := by
    intro y hy
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj (g : ModGL ReeTag.F4.tag K)).toMonoidHom hy
    rw [hDE, MonoidHom.map_closure] at h2
    refine (Subgroup.closure_le _).2 ?_ h2
    rintro _ ⟨k, ⟨hk, x, ⟨x', hx', rfl⟩, hx1, hkx⟩, rfl⟩
    refine hmem _ (mul_mem (mul_mem g.2 hk) (inv_mem g.2)) _
      ⟨g * x' * g⁻¹, hnorm x' hx', rfl⟩ ?_ ?_
    · intro h1
      apply hx1
      have h1' : ((g * x' * g⁻¹ : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K) = 1 := h1
      have : g * x' * g⁻¹ = 1 := Subtype.ext h1'
      rw [mul_inv_eq_one, mul_eq_left] at this
      rw [this]
      rfl
    · change (g : ModGL ReeTag.F4.tag K) * k * (g : ModGL ReeTag.F4.tag K)⁻¹ *
          (((g * x' * g⁻¹ : ReeTag.F4.reeGamma K m)) : ModGL ReeTag.F4.tag K) =
        (((g * x' * g⁻¹ : ReeTag.F4.reeGamma K m)) : ModGL ReeTag.F4.tag K) *
          ((g : ModGL ReeTag.F4.tag K) * k * (g : ModGL ReeTag.F4.tag K)⁻¹)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hkx' : k * (x' : ModGL ReeTag.F4.tag K) = (x' : ModGL ReeTag.F4.tag K) * k := hkx
      calc (g : ModGL ReeTag.F4.tag K) * k * (g : ModGL ReeTag.F4.tag K)⁻¹ *
            ((g : ModGL ReeTag.F4.tag K) * x' * (g : ModGL ReeTag.F4.tag K)⁻¹)
          = (g : ModGL ReeTag.F4.tag K) * (k * x') * (g : ModGL ReeTag.F4.tag K)⁻¹ := by group
        _ = (g : ModGL ReeTag.F4.tag K) * (x' * k) * (g : ModGL ReeTag.F4.tag K)⁻¹ := by
          rw [hkx']
        _ = _ := by group
  have hM0 : ReeTag.F4.reeLocalBlock K m ⟨0, by decide⟩ ≤ DE := by
    intro y hy
    have hyΓ : y ∈ ReeTag.F4.reeGamma K m := by
      have hle : ReeTag.F4.reeLocalBlock K m ⟨0, by decide⟩ ≤ ReeTag.F4.reeGamma K m :=
        sup_le inf_le_right inf_le_right
      exact hle hy
    have hd : ((q1SUToSL h ι x₀ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        Matrix.diagonal ![ι z, 1, (ι z)⁻¹] := by
      rw [coe_q1SUToSL, hx₀z, Matrix.diagonal_map ι.map_zero]
      congr 1
      funext i
      fin_cases i <;> simp [map_inv₀]
    have hc := q1_commute_localBlock D (ι ω') (Ψ x₀) (q1SUToSL h ι x₀) (ι z)
      ((map_ne_zero ι).2 hz) hd (hΨ x₀) y hy
    exact hmem y hyΓ _ ⟨Ψ x₀, ⟨x₀, hx₀E, rfl⟩, rfl⟩ (hEΓ1 x₀ hx₀E hx₀1) hc.symm
  obtain ⟨u, hu⟩ := q1_exists_letters h hω' hbar
  have hu' : ∀ k, q1SUToSL h ι (u k) = q1TvProd (ι ω') (q1LetterDec k) :=
    fun k => q1SUToSL_letter h ι hω' (u k) k (hu k)
  have hpar : q1Par m = if (m % 2 == 1) then 3 else 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · simp [q1Par, h0]
    · simp [q1Par, h1]
  have hlet := q1_letters_eq D hω (m % 2 == 1) hpar (f4Ev_pow_two_pow hω m) Ψ
    (q1SUToSL h ι) hΨ u hu' g hg
  have hprod : ∀ tgt : Bool, ((((q1Letters tgt).map fun x =>
      if x.1 then g * Ψ (u x.2) * g⁻¹ else Ψ (u x.2)).prod : ReeTag.F4.reeGamma K m) :
        ModGL ReeTag.F4.tag K) ∈ DE := by
    intro tgt
    rw [← Subgroup.subtype_apply, map_list_prod, List.map_map]
    refine list_prod_mem fun y hy => ?_
    obtain ⟨⟨side, k⟩, -, rfl⟩ := List.mem_map.1 hy
    cases side
    · exact hSU (u k)
    · exact hconj _ (hSU (u k))
  have hB : LargeReeInvolution.sylowB m K 1 0 ∈ DE := by
    have := hprod true
    rwa [hlet true] at this
  have hn : LargeReeInvolution.weylTwo K ∈ DE := by
    have := hprod false
    rwa [hlet false] at this
  refine ⟨E, Subgroup.map_subtype_le EΓ, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexpΓ x hx, map_one]
  · rw [Subgroup.card_map_of_injective (ReeTag.F4.reeGamma K m).subtype_injective, hcardΓ]
  · exact le_antisymm hDle (reeGamma_le_of_localBlock_zero hK DE hM0 hB hn)

end Main

end CFSG.RankThree.PartOne.SEITZQ1
