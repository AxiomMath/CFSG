module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieBorelTorus
public import CFSG.RankThree.CentralLiftU.UnitaryTorusWeylEven
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEngLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F11 (Omega1p)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

private theorem normalizerQuotient_equiv_hypTorus {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (e : hypSU h 2 0 ≃* Y) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    Nonempty (normalizerQuotient S ≃* hypTorus h 2 0) := by
  classical
  have D := CFSG.Quasithin.H13.Sec53F.Unit.borelAutData_u4 h
  obtain ⟨eC⟩ := normalizerQuotient_equiv_of_complement D.H_le D.U_inf_H D.B_eq
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (S := hypUnitriangular h 2 0)
    (S' := S) e D.sylow hS
  exact ⟨eN.symm.trans eC⟩

namespace U4Proof

variable {Y : Type} [Group Y] [Finite Y] {n : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 n K) (e : hypSU h 2 0 ≃* Y)

private def u4q (n : ℕ) : ℕ := 2 ^ n

private theorem hcard_K (n : ℕ) (h : UnitaryFieldData 2 n K) :
    Nat.card K = u4q n ^ 2 := by
  rw [UnitaryFieldData.card h]
  rw [u4q, show 2 * n = n * 2 by omega, pow_mul, pow_two]

private noncomputable def u4Coord :
    hypTorus h 2 0 →* Kˣ × Kˣ :=
  MonoidHom.prod (CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2))
    (CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2))

private theorem u4Coord_apply (t : hypTorus h 2 0) :
    u4Coord h t = (CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t,
      CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t) := rfl

private theorem u4Coord_injective : Function.Injective (u4Coord h) := by
  intro t₁ t₂ ht
  obtain ⟨a₁, d₁, -, -, hm₁⟩ := t₁.2
  obtain ⟨a₂, d₂, -, -, hm₂⟩ := t₂.2
  have h0 : ((a₁ 0 : Kˣ) : K) = ((a₂ 0 : Kˣ) : K) := by
    have hpair := congrArg (fun p : Kˣ × Kˣ => ((p.1 : K))) ht
    rw [u4Coord_apply, u4Coord_apply] at hpair
    rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hm₁,
      CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hm₂] at hpair
    simpa [torusEntries] using hpair
  have h1 : ((a₁ 1 : Kˣ) : K) = ((a₂ 1 : Kˣ) : K) := by
    have hpair := congrArg (fun p : Kˣ × Kˣ => ((p.2 : K))) ht
    rw [u4Coord_apply, u4Coord_apply] at hpair
    rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hm₁,
      CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hm₂] at hpair
    simpa [torusEntries] using hpair
  apply Subtype.ext
  apply CFSG.RankThree.CentralLiftU.hypSU_eq_of_diag h hm₁ hm₂
  · intro x
    fin_cases x
    · exact h0
    · exact h1
  · intro k
    exact k.elim0

private noncomputable def u4MulHom : Kˣ × Kˣ →* Kˣ where
  toFun p := p.1 * p.2
  map_one' := one_mul 1
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul]
    ac_rfl

private noncomputable def u4Phi : Kˣ × Kˣ →* Kˣ :=
  (powMonoidHom (u4q n - 1)).comp (u4MulHom (K := K))

private theorem u4Phi_apply (p : Kˣ × Kˣ) :
    u4Phi (n := n) p = (p.1 * p.2) ^ (u4q n - 1) := by
  simp [u4Phi, u4MulHom, powMonoidHom_apply]

private theorem u4Phi_range :
    (u4Phi (n := n) (K := K)).range = (powMonoidHom (u4q n - 1) : Kˣ →* Kˣ).range := by
  classical
  have hmul : (u4MulHom (K := K)).range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact ⟨(x, 1), by simp [u4MulHom]⟩
  rw [u4Phi, MonoidHom.range_comp, hmul, Subgroup.map_top]

private theorem u4Coord_range_eq_ker (hq2 : 2 ≤ u4q n) :
    (u4Coord h).range = (u4Phi (n := n) (K := K)).ker := by
  classical
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    have hfix : (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
        ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) ∈ h.fixedField := by
      simpa [Fin.prod_univ_two] using CFSG.RankThree.CentralLiftU.prod_tcoord_mem h t
    have hbar : h.bar (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
        ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) =
        ((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
          ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K) :=
      h.mem_fixedField.mp hfix
    have hxq : (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
        ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) ^ u4q n =
        ((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
          ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K) := by
      have hbar' : h.bar (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
          ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) =
          (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
            ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) ^ u4q n := by
        simpa [u4q] using h.bar_apply
          (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
            ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K))
      rw [hbar] at hbar'
      exact hbar'.symm
    have hx0 : (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
        ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    have hx1 : (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
        ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) ^
          (u4q n - 1) = 1 := by
      have hstep : (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
          ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) ^
            (u4q n - 1) *
          (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
            ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) = 1 *
          (((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) t : Kˣ) : K) *
            ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) t : Kˣ) : K)) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ u4q n), hxq]
        simp
      exact mul_right_cancel₀ hx0 (by simpa using hstep)
    rw [MonoidHom.mem_ker, u4Coord_apply, u4Phi_apply]
    apply Units.ext
    simpa using hx1
  · intro hp
    obtain ⟨a, b⟩ := p
    have hx1u : (a * b) ^ (u4q n - 1) = 1 := by
      have h := hp
      rw [MonoidHom.mem_ker, u4Phi_apply] at h
      exact h
    have hx1 : ((a : K) * (b : K)) ^ (u4q n - 1) = 1 := by
      have h := congrArg (fun u : Kˣ => (u : K)) hx1u
      simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h
    have hxq : ((a : K) * (b : K)) ^ u4q n = (a : K) * (b : K) := by
      rw [show u4q n = (u4q n - 1) + 1 by omega, pow_succ, hx1, one_mul]
    have hbar : h.bar ((a : K) * (b : K)) = (a : K) * (b : K) := by
      have hbar' : h.bar ((a : K) * (b : K)) = ((a : K) * (b : K)) ^ u4q n := by
        simpa [u4q] using h.bar_apply ((a : K) * (b : K))
      rw [hbar']
      exact hxq
    let aVec : Fin 2 → Kˣ := fun i => if i = 0 then a else b
    have haVec0 : aVec 0 = a := by simp [aVec]
    have haVec1 : aVec 1 = b := by simp [aVec]
    have hratio : torusRatio h aVec (fun k : Fin 0 => k.elim0) = 1 := by
      have hprod : (∏ i : Fin 2, ((aVec i : K) / h.bar (aVec i : K))) = 1 := by
        rw [Fin.prod_univ_two, haVec0, haVec1]
        rw [div_mul_div_comm, ← map_mul, hbar, div_self (mul_ne_zero a.ne_zero b.ne_zero)]
      simpa [torusRatio] using hprod
    obtain ⟨t, htT, hmat⟩ := torusMat_mem_hypSU (d := fun k : Fin 0 => k.elim0) h aVec
      (fun k => k.elim0) hratio
    have ht0 : CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) ⟨t, htT⟩ = a := by
      apply Units.ext
      rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hmat]
      simp [torusEntries, haVec0]
    have ht1 : CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) ⟨t, htT⟩ = b := by
      apply Units.ext
      rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hmat]
      simp [torusEntries, haVec1]
    refine ⟨⟨t, htT⟩, ?_⟩
    rw [u4Coord_apply, ht0, ht1]

private theorem card_hypTorus_two (hq2 : 2 ≤ u4q n) :
    Nat.card (hypTorus h 2 0) = (u4q n - 1) * (u4q n ^ 2 - 1) := by
  classical
  haveI := h.finite
  letI := Fintype.ofFinite K
  have hcoordcard : Nat.card (hypTorus h 2 0) = Nat.card (u4Phi (n := n) (K := K)).ker := by
    rw [← u4Coord_range_eq_ker h hq2]
    exact Nat.card_congr (MonoidHom.ofInjective (u4Coord_injective h)).toEquiv
  have hrange : Nat.card (u4Phi (n := n) (K := K)).range = u4q n + 1 := by
    rw [u4Phi_range, IsCyclic.card_powMonoidHom_range, Nat.card_units K, hcard_K n h]
    have hsq : u4q n ^ 2 - 1 = (u4q n - 1) * (u4q n + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    have hgcd : Nat.gcd (u4q n ^ 2 - 1) (u4q n - 1) = u4q n - 1 := by
      rw [hsq]
      exact Nat.gcd_eq_right (dvd_mul_right _ _)
    rw [hgcd, hsq, Nat.mul_div_right _ (by omega : 0 < u4q n - 1)]
  have hmul := Subgroup.card_ker_mul_card_range (u4Phi (n := n) (K := K))
  rw [hrange, Nat.card_prod, Nat.card_units K, hcard_K n h] at hmul
  have htarget : ((u4q n - 1) * (u4q n ^ 2 - 1)) * (u4q n + 1) =
      (u4q n ^ 2 - 1) * (u4q n ^ 2 - 1) := by
    rw [show u4q n ^ 2 - 1 = (u4q n - 1) * (u4q n + 1) by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]]
    ring
  rw [hcoordcard]
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < u4q n + 1)
    (hmul.trans htarget.symm)

end U4Proof

theorem k_U4CartanRank_holds : K_U4CartanRank := by
  intro Y _ _ n hY hq S hS r hr hr2 hdvd
  classical
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  haveI := h.finite
  letI := Fintype.ofFinite K
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hq
    · exact hn
  have hq2 : 2 ≤ U4Proof.u4q n := by
    rw [U4Proof.u4q]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hKq : Nat.card K = U4Proof.u4q n ^ 2 := U4Proof.hcard_K n h
  obtain ⟨eT⟩ := normalizerQuotient_equiv_hypTorus h e hS
  have hdvdK : r ∣ Nat.card K - 1 := by
    rw [hKq]
    have hsq : U4Proof.u4q n ^ 2 - 1 =
        (U4Proof.u4q n - 1) * (U4Proof.u4q n + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_left hdvd _
  have hunits : Nat.card {x : Kˣ // x ^ r = 1} = r :=
    CFSG.LocalAnalysis.RankFourTheoremC.card_units_pow_eq_one hdvdK
  have hdvdq : r ∣ U4Proof.u4q n - 1 := by simpa [U4Proof.u4q] using hdvd
  have hTtors : Nat.card {t : hypTorus h 2 0 // t ^ r = 1} = r ^ 2 := by
    classical
    let Φ : {t : hypTorus h 2 0 // t ^ r = 1} →
        {p : Kˣ × Kˣ // p.1 ^ r = 1 ∧ p.2 ^ r = 1} := fun t =>
      ⟨U4Proof.u4Coord h t.1, by
        have hpow : (U4Proof.u4Coord h t.1) ^ r = 1 := by
          rw [← map_pow, t.2, map_one]
        exact ⟨by simpa using congrArg Prod.fst hpow, by simpa using congrArg Prod.snd hpow⟩⟩
    have hbij : Function.Bijective Φ := by
      constructor
      · intro t₁ t₂ ht
        have hc : U4Proof.u4Coord h t₁.1 = U4Proof.u4Coord h t₂.1 := congrArg Subtype.val ht
        exact Subtype.ext (U4Proof.u4Coord_injective h hc)
      · rintro ⟨⟨a, b⟩, ha, hb⟩
        have hprod : (a * b) ^ (U4Proof.u4q n - 1) = 1 := by
          have haq : a ^ (U4Proof.u4q n - 1) = 1 := by
            obtain ⟨m, hm⟩ := hdvdq
            rw [hm, pow_mul, ha, one_pow]
          have hbq : b ^ (U4Proof.u4q n - 1) = 1 := by
            obtain ⟨m, hm⟩ := hdvdq
            rw [hm, pow_mul, hb, one_pow]
          rw [mul_pow, haq, hbq, one_mul]
        have hprodK : ((a : K) * (b : K)) ^ (U4Proof.u4q n - 1) = 1 := by
          have h := congrArg (fun u : Kˣ => (u : K)) hprod
          simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h
        have hxq : ((a : K) * (b : K)) ^ U4Proof.u4q n = (a : K) * (b : K) := by
          rw [show U4Proof.u4q n = (U4Proof.u4q n - 1) + 1 by omega, pow_succ, hprodK, one_mul]
        have hbar : h.bar ((a : K) * (b : K)) = (a : K) * (b : K) := by
          have hbar' : h.bar ((a : K) * (b : K)) = ((a : K) * (b : K)) ^ U4Proof.u4q n := by
            simpa [U4Proof.u4q] using h.bar_apply ((a : K) * (b : K))
          rw [hbar']
          exact hxq
        let aVec : Fin 2 → Kˣ := fun i => if i = 0 then a else b
        have haVec0 : aVec 0 = a := by simp [aVec]
        have haVec1 : aVec 1 = b := by simp [aVec]
        have hratio : torusRatio h aVec (fun k : Fin 0 => k.elim0) = 1 := by
          have hprod' : (∏ i : Fin 2, ((aVec i : K) / h.bar (aVec i : K))) = 1 := by
            rw [Fin.prod_univ_two, haVec0, haVec1, div_mul_div_comm, ← map_mul, hbar,
              div_self (mul_ne_zero a.ne_zero b.ne_zero)]
          simpa [torusRatio] using hprod'
        obtain ⟨t, htT, hmat⟩ := torusMat_mem_hypSU (d := fun k : Fin 0 => k.elim0) h aVec
          (fun k => k.elim0) hratio
        have ht0 : CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) ⟨t, htT⟩ = a := by
          apply Units.ext
          rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hmat]
          simp [torusEntries, haVec0]
        have ht1 : CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) ⟨t, htT⟩ = b := by
          apply Units.ext
          rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hmat]
          simp [torusEntries, haVec1]
        have hcoord : U4Proof.u4Coord h ⟨t, htT⟩ = (a, b) := by
          rw [U4Proof.u4Coord_apply, ht0, ht1]
        have htr : (⟨t, htT⟩ : hypTorus h 2 0) ^ r = 1 := by
          apply U4Proof.u4Coord_injective h
          rw [map_pow, hcoord, map_one]
          ext <;> simp [ha, hb]
        refine ⟨⟨⟨t, htT⟩, htr⟩, ?_⟩
        apply Subtype.ext
        exact hcoord
    rw [Nat.card_eq_of_bijective Φ hbij]
    have hcardprod : Nat.card {p : Kˣ × Kˣ // p.1 ^ r = 1 ∧ p.2 ^ r = 1} =
        Nat.card ({a : Kˣ // a ^ r = 1} × {b : Kˣ // b ^ r = 1}) :=
      Nat.card_congr (Equiv.subtypeProdEquivProd
        (p := fun a : Kˣ => a ^ r = 1) (q := fun b : Kˣ => b ^ r = 1))
    rw [hcardprod, Nat.card_prod, hunits]
    exact (pow_two r).symm
  have hAtors : Nat.card {a : normalizerQuotient S // a ^ r = 1} = r ^ 2 := by
    rw [← hTtors]
    refine Nat.card_congr (Equiv.subtypeEquiv eT.toEquiv (fun a => ?_))
    change a ^ r = 1 ↔ (eT a) ^ r = 1
    simpa only [map_pow] using (eT.map_eq_one_iff (x := a ^ r)).symm
  have hcomm : ∀ a b : normalizerQuotient S, a * b = b * a := by
    intro a b
    apply eT.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h (eT a).2 (eT b).2)
  obtain ⟨hp, ho⟩ := pRank_and_card_Omega1p_of_comm hcomm hr hAtors
  have hp' : CFSG.pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hp
  have hYcard : Nat.card Y = U4Proof.u4q n ^ 6 * (U4Proof.u4q n ^ 2 - 1) *
      (U4Proof.u4q n ^ 3 + 1) * (U4Proof.u4q n ^ 4 - 1) := by
    calc Nat.card Y = Nat.card (hypSU h 2 0) := (Nat.card_congr e.toEquiv).symm
      _ = (2 ^ n) ^ 6 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) :=
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_hypSU_four h
  have hTcard : Nat.card (hypTorus h 2 0) =
      (U4Proof.u4q n - 1) * (U4Proof.u4q n ^ 2 - 1) :=
    U4Proof.card_hypTorus_two h hq2
  have hqmod : U4Proof.u4q n ≡ 1 [MOD r] :=
    ((Nat.modEq_iff_dvd' (by omega : 1 ≤ U4Proof.u4q n)).mpr hdvdq).symm
  have hqr : ¬ r ∣ U4Proof.u4q n := by
    intro hqdiv
    have h2 : r ∣ U4Proof.u4q n - (U4Proof.u4q n - 1) := Nat.dvd_sub hqdiv hdvd
    rw [show U4Proof.u4q n - (U4Proof.u4q n - 1) = 1 by omega] at h2
    exact hr.not_dvd_one h2
  have hnot2 : ¬ r ∣ 2 := by
    intro h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  have hnot4 : ¬ r ∣ 4 := by
    intro h4
    have hpow : r ∣ 2 ^ 2 := by simpa using h4
    exact hnot2 (hr.dvd_of_dvd_pow (n := 2) hpow)
  have hq2fac : (U4Proof.u4q n ^ 2 - 1).factorization r =
      (U4Proof.u4q n - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one
        hr hr2 hq2 hdvd (by norm_num : (2 : ℕ) ≠ 0),
      Nat.factorization_eq_zero_of_not_dvd hnot2, add_zero]
  have hq4fac : (U4Proof.u4q n ^ 4 - 1).factorization r =
      (U4Proof.u4q n - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one
        hr hr2 hq2 hdvd (by norm_num : (4 : ℕ) ≠ 0),
      Nat.factorization_eq_zero_of_not_dvd hnot4, add_zero]
  have hq3fac : (U4Proof.u4q n ^ 3 + 1).factorization r = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    have h2 : U4Proof.u4q n ^ 3 + 1 ≡ 2 [MOD r] := by
      have := (hqmod.pow 3).add (Nat.ModEq.refl 1)
      simpa using this
    intro hd
    have h0 : U4Proof.u4q n ^ 3 + 1 ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.mpr hd
    have h20 : (2 : ℕ) ≡ 0 [MOD r] := h2.symm.trans h0
    have hdvd2 : r ∣ 2 := Nat.modEq_zero_iff_dvd.mp h20
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd2)
  have hqzero : (U4Proof.u4q n).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqr
  have hq1n : U4Proof.u4q n - 1 ≠ 0 := by have := hq2; omega
  have hq2n : U4Proof.u4q n ^ 2 - 1 ≠ 0 := by
    have h1 : 1 < U4Proof.u4q n ^ 2 := by
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ U4Proof.u4q n ^ 2 := Nat.pow_le_pow_left hq2 2
    omega
  have hq3n : U4Proof.u4q n ^ 3 + 1 ≠ 0 := by positivity
  have hq4n : U4Proof.u4q n ^ 4 - 1 ≠ 0 := by
    have h1 : 1 < U4Proof.u4q n ^ 4 := by
      calc 1 < 2 ^ 4 := by norm_num
        _ ≤ U4Proof.u4q n ^ 4 := Nat.pow_le_pow_left hq2 4
    omega
  have hq6n : U4Proof.u4q n ^ 6 ≠ 0 := pow_ne_zero _ (by have := hq2; omega)
  have hfacY : (Nat.card Y).factorization r = 2 * (U4Proof.u4q n - 1).factorization r := by
    rw [hYcard]
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hq6n hq2n) hq3n) hq4n,
      Finsupp.add_apply,
      Nat.factorization_mul (mul_ne_zero hq6n hq2n) hq3n, Finsupp.add_apply,
      Nat.factorization_mul hq6n hq2n, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, hqzero, hq2fac, hq3fac, hq4fac]
    ring
  have hfacT : (Nat.card (hypTorus h 2 0)).factorization r =
      2 * (U4Proof.u4q n - 1).factorization r := by
    rw [hTcard, Nat.factorization_mul hq1n hq2n, Finsupp.add_apply, hq2fac]
    ring
  have hfacT' : (Nat.card (normalizerQuotient S)).factorization r =
      2 * (U4Proof.u4q n - 1).factorization r := by
    rw [Nat.card_congr eT.toEquiv]
    exact hfacT
  exact ⟨hp', ho, hfacY.trans hfacT'.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
