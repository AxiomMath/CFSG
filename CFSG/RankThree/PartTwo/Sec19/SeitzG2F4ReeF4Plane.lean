module

public import CFSG.RankThree.PartOne.SEITZQ1.AmbientPlane
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2ProofFix

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.SEITZQ1 CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups


section Unitary

variable {f : ℕ} {K' : Type} [Field K']

theorem q1_plane_any (h : UnitaryFieldData 2 f K') {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K' 3),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
      (∀ x ∈ E, ∀ i j : Fin 3, i ≠ j →
        ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0) ∧
      ∃ x₀ ∈ E, x₀ ≠ 1 ∧ ∃ z : K', z ≠ 0 ∧
        ((x₀ : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = Matrix.diagonal ![z, 1, z⁻¹] := by
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K'ˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [Nat.card_units, h.card, pow_mul']
    exact h1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ Dvd.dvd.mul_right hpq _)
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  set S := Subgroup.zpowers ζ with hS
  have hSp : ∀ s ∈ S, s ^ p = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]))
  have hSq : ∀ s ∈ S, s ^ (2 ^ f + 1) = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]; exact hpq))
  let E₀ : Subgroup (GL (Fin 3) K') := (S.prod S).map q1DiagTorus
  have hE₀G : E₀ ≤ unitarySU 2 f K' 3 := by
    rintro _ ⟨u, hu, rfl⟩
    exact q1DiagTorus_mem_unitarySU h (Prod.ext (hSq _ hu.1) (hSq _ hu.2))
  refine ⟨E₀.subgroupOf (unitarySU 2 f K' 3), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨v, hv, hyv⟩ := Subgroup.mem_subgroupOf.mp hy
    apply Subtype.ext
    show (x : GL (Fin 3) K') * y = y * x
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, mul_comm u v]
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    have hup : u ^ p = 1 := Prod.ext (hSp _ hu.1) (hSp _ hu.2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hxu, ← map_pow, hup, map_one]
    rfl
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀G).toEquiv,
      Subgroup.card_map_of_injective q1DiagTorus_injective,
      Nat.card_congr (Subgroup.prodEquiv S S).toEquiv, Nat.card_prod, hS, Nat.card_zpowers, hζ,
      sq]
  · intro x hx i j hij
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    rw [← hxu, coe_q1DiagTorus]
    exact Matrix.diagonal_apply_ne _ hij
  · have hζS : ζ ∈ S := Subgroup.mem_zpowers ζ
    refine ⟨⟨q1DiagTorus (ζ, ζ), hE₀G ⟨(ζ, ζ), ⟨hζS, hζS⟩, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨(ζ, ζ), ⟨hζS, hζS⟩, rfl⟩, ?_, (ζ : K'), ζ.ne_zero, ?_⟩
    · intro h1
      have h2 : q1DiagTorus (ζ, ζ) = q1DiagTorus 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact hζ1 (congrArg Prod.fst (q1DiagTorus_injective h2))
    · show (q1DiagTorus (ζ, ζ) : Matrix (Fin 3) (Fin 3) K') = _
      rw [coe_q1DiagTorus]
      congr 1
      funext i
      fin_cases i <;> simp


end Unitary

section Plane

variable {a : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {L : Type} [Field L] [Algebra K L]

theorem q1_conj_mem_three (hK : Nat.card K = 2 ^ (2 * a + 1)) {ω : L}
    (E : Subgroup (ReeTag.F4.reeGamma K a))
    (hT : ∀ x ∈ E, (q1C ω)⁻¹ * thetaGamma L a x * q1C ω ∈ torusGroup ReeTag.F4.tag L)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 3 ^ 2) (g : ReeTag.F4.reeGamma K a)
    (hg : thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹) :
    ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
  classical
  have : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  set E' : Subgroup (ReeTag.F4.reeGamma K a) := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'T : ∀ y ∈ E', (q1C ω)⁻¹ * thetaGamma L a y * q1C ω ∈ torusGroup ReeTag.F4.tag L := by
    rintro _ ⟨x, hx, rfl⟩
    exact q1_conj_mem_torus hg (hT x hx)
  have hE'p : ∀ y ∈ E', y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hE'card : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  let T : Subgroup (ReeTag.F4.reeGamma K a) :=
    (torusGroup ReeTag.F4.tag L).comap
      ((MulAut.conj (q1C ω)⁻¹).toMonoidHom.comp (thetaGamma L a))
  have hmemT : ∀ y, y ∈ T ↔
      (q1C ω)⁻¹ * thetaGamma L a y * q1C ω ∈ torusGroup ReeTag.F4.tag L := fun y => by
    simp only [T, Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  let W : Subgroup (ReeTag.F4.reeGamma K a) :=
    { carrier := {y | y ∈ T ∧ y ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute x y := q1_mul_comm_of_mem_torus (q1C ω) ((hmemT x).1 hx.1)
          ((hmemT y).1 hy.1)
        rw [hc.mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨T.one_mem, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨T.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hEW : E ≤ W := fun x hx => ⟨(hmemT x).2 (hT x hx), hexp x hx⟩
  have hE'W : E' ≤ W := fun y hy => ⟨(hmemT y).2 (hE'T y hy), hE'p y hy⟩
  have hWab : CFSG.Open.IsElemAbelian 3 W := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hx.2⟩
    apply Subtype.ext
    exact q1_mul_comm_of_mem_torus (q1C ω) ((hmemT x).1 x.2.1) ((hmemT y).1 y.2.1)
  have hW9 : Nat.card W ≤ 9 :=
    CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK W hWab
  have hEeq : E = W := Subgroup.eq_of_le_of_card_ge hEW (by rw [hcard]; omega)
  have hE'eq : E' = W := Subgroup.eq_of_le_of_card_ge hE'W (by rw [hE'card]; omega)
  intro x hx
  have hmem : g * x * g⁻¹ ∈ E' := ⟨x, hx, rfl⟩
  rwa [hE'eq, ← hEeq] at hmem


end Plane

section Main


theorem q1_phi2_plane_three {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : p = 3) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag K), E ≤ ReeTag.F4.reeGamma K m ∧
      (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
      Subgroup.closure {k | k ∈ ReeTag.F4.reeGamma K m ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} =
        ReeTag.F4.reeGamma K m := by
  classical
  have hpq : p ∣ 2 ^ (2 * m + 1) + 1 := by
    subst hp3
    simpa using Odd.nat_add_dvd_pow_add_pow 2 1 (odd_two_mul_add_one m)
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
    q1_plane_any h hp hpq
  have hj : Function.Injective (q1SUToSL h ι) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hm : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map ι = 1 := by
      rw [← coe_q1SUToSL h ι, hu]
      rfl
    have hm' : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 :=
      Matrix.map_injective ι.injective (hm.trans (Matrix.map_one ι ι.map_zero ι.map_one).symm)
    exact Subtype.ext (Units.ext hm')
  have hinj : ∀ u ∈ E'', Ψ u = 1 → u = 1 := by
    intro u hu h1
    have h3 := (hΨ u).symm
    rw [h1, map_one, mul_inv_eq_one, mul_eq_left] at h3
    have h2 : q1SUToSL h ι u = 1 :=
      CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof.q1Psi0_injective D.isFrob
        (by rw [h3, map_one])
    exact hj (by rw [h2, map_one])
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
  have hnorm := q1_conj_mem_three hK EΓ hT (hp3 ▸ hexpΓ) (hp3 ▸ hcardΓ) g hg
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


end CFSG.RankThree.PartTwo.Sec19
