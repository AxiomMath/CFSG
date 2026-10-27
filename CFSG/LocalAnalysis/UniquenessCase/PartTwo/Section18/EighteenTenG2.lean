module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)


theorem k_18_10_G2_holds : K_18_10_G2 := by
  intro W _ _ hW2 H f p hf2 hp hmod hG2 hnat v hv
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, π, hreal⟩ := hnat
  letI := hKfield
  letI := hKfin
  haveI : CharP K 2 :=
    CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hKcard
  let q : ℕ := 2 ^ f
  have hqcard : Nat.card K = q := hKcard
  let Z : Subgroup W := CFSG.Quasithin.fixV H
  have hΓ : quasithinG2 K ≤ cayleyGroup K :=
    (CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup (K := K)).le
  let LM := CFSG.Quasithin.Vol2.KGNat.linModelZorn (quasithinG2 K) hΓ
  obtain ⟨ψ, hψadd, hψker, hψonto, hψeq⟩ :=
    CFSG.Quasithin.Vol2.KGNat.exists_coord LM hreal
  have hψadd' : ∀ u u' : W, ψ (u * u') = ψ u + ψ u' :=
    fun u u' => hψadd u trivial u' trivial
  have hψker' : ∀ u : W, ψ u = 0 ↔ u ∈ Z := fun u => hψker u trivial
  have hψonto' : ∀ m : Ix3 → K, ∃ u : W, ψ u = m := by
    intro m
    obtain ⟨u, -, hu⟩ := hψonto m
    exact ⟨u, hu⟩
  have hψeq' : ∀ (γ : ↥(quasithinG2 K)) (u : W),
      ψ (((π γ : ↥H) : MulAut W) u) = LM.lin γ (ψ u) :=
    fun γ u => hψeq γ u trivial
  let ψh : W →* Multiplicative (Ix3 → K) :=
    { toFun := fun w => Multiplicative.ofAdd (ψ w)
      map_one' := by
        have h1 : ψ (1 : W) = 0 := (hψker' 1).mpr Z.one_mem
        simp [h1]
      map_mul' := fun u v => by
        rw [hψadd']
        rfl }
  have hψhker : ψh.ker = Z := by
    ext w
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (ψ w) = 1 ↔ w ∈ Z
    rw [ofAdd_eq_one]
    exact hψker' w
  have hψhsurj : Function.Surjective ψh := by
    intro m
    obtain ⟨u, hu⟩ := hψonto' (Multiplicative.toAdd m)
    exact ⟨u, by
      change Multiplicative.ofAdd (ψ u) = m
      rw [hu, ofAdd_toAdd]⟩
  have hIx3 : Nat.card Ix3 = 6 := by
    rw [show Ix3 = (Fin 3 ⊕ Fin 3) from rfl, Nat.card_sum]
    norm_num
  have hMIx3 : Nat.card (Ix3 → K) = q ^ 6 := by
    rw [Nat.card_fun, hqcard, hIx3]
  have hcardquot : Nat.card (W ⧸ Z) = q ^ 6 := by
    have h1 : Nat.card (W ⧸ Z) = Nat.card (Multiplicative (Ix3 → K)) := by
      rw [← hψhker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψh hψhsurj).toEquiv
    calc Nat.card (W ⧸ Z) = Nat.card (Multiplicative (Ix3 → K)) := h1
      _ = Nat.card (Ix3 → K) := Nat.card_congr Multiplicative.toAdd
      _ = q ^ 6 := hMIx3
  obtain ⟨c, hc0, hc1⟩ :=
    CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := K) (by
      rw [hqcard]
      have : 4 ≤ q := by
        have h : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        simpa [q] using h
      omega)
  have hcomm : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K := by
    rw [CFSG.Quasithin.Vol2.KGNat.commutator_quasithinG2_eq hc0 hc1,
      CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  have htrans : ∀ x y : Ix3 → K, x ≠ 0 → y ≠ 0 →
      ∃ γ : ↥(quasithinG2 K), LM.lin γ x = y := by
    intro x y hx hy
    obtain ⟨γ, hγ⟩ :=
      CFSG.Quasithin.Vol2.KGNat.exists_g2_lin_eq hc0 hc1 x y hx hy
    exact ⟨⟨γ.1, (le_of_eq hcomm) γ.2⟩, hγ⟩
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  have hInv : CFSG.IsInvariant ↥H W Z := by
    refine ⟨fun h w => ?_⟩
    have hsmul : h • w = (h : MulAut W) w := rfl
    rw [hsmul]
    constructor
    · intro hw
      have hza : (h : MulAut W) w = w := CFSG.Quasithin.mem_fixV.1 hw h h.2
      rw [hza]
      exact hw
    · intro hw
      have hfwd : ∀ (a : ↥H) {z : W}, z ∈ Z → a • z ∈ Z := by
        intro a z hz
        have hza : (a : MulAut W) z = z := CFSG.Quasithin.mem_fixV.1 hz a a.2
        have hz' : a • z = z := by
          rw [show a • z = (a : MulAut W) z from rfl, hza]
        rw [hz']
        exact hz
      have h1 : h⁻¹ • (h • w) ∈ Z := hfwd h⁻¹ hw
      rwa [← mul_smul, inv_mul_cancel, one_smul] at h1
  haveI : Z.Normal := inferInstance
  letI : MulDistribMulAction ↥H (W ⧸ Z) :=
    CFSG.quotientMulDistribMulAction (A := ↥H) (G := W) Z hInv
  let x0 : W ⧸ Z := QuotientGroup.mk v
  have hx0 : x0 ≠ 1 := by
    intro h1
    exact hv ((QuotientGroup.eq_one_iff v).mp h1)
  have hψinv : ∀ w : W, ψ w⁻¹ = - ψ w := by
    intro w
    have h := hψadd' w w⁻¹
    rw [mul_inv_cancel, show ψ (1 : W) = 0 from (hψker' 1).mpr Z.one_mem] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have horbit_eq : (MulAction.orbit ↥H x0 : Set (W ⧸ Z)) = {x | x ≠ 1} := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩ h1
      change QuotientGroup.mk (h • v) = 1 at h1
      have hZ : h • v ∈ Z := (QuotientGroup.eq_one_iff (h • v)).mp h1
      have hvZ : v ∈ Z := by
        have h2 := (hInv.invariant h⁻¹ (h • v)).mp hZ
        rwa [← mul_smul, inv_mul_cancel, one_smul] at h2
      exact hv hvZ
    · intro hx
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
      have hw : w ∉ Z := by
        intro hwZ
        exact hx ((QuotientGroup.eq_one_iff w).mpr hwZ)
      have hψw : ψ w ≠ 0 := fun h0 => hw ((hψker' w).mp h0)
      have hψv : ψ v ≠ 0 := fun h0 => hv ((hψker' v).mp h0)
      obtain ⟨γ, hγ⟩ := htrans (ψ v) (ψ w) hψv hψw
      refine ⟨π γ, ?_⟩
      change QuotientGroup.mk (((π γ : ↥H) : MulAut W) v) = QuotientGroup.mk w
      apply (QuotientGroup.eq_iff_div_mem).mpr
      rw [div_eq_mul_inv, ← hψker']
      rw [hψadd', hψeq' γ v, hγ, hψinv w, add_neg_cancel]
  have horbit_card : Nat.card (MulAction.orbit ↥H x0) = q ^ 6 - 1 := by
    haveI : Fintype (W ⧸ Z) := Fintype.ofFinite _
    haveI : Fintype {x : W ⧸ Z // x ≠ 1} := Fintype.ofFinite _
    rw [Nat.card_congr (Set.equivOfEq horbit_eq), Nat.card_eq_fintype_card,
      Set.card_ne_eq, ← Nat.card_eq_fintype_card, hcardquot]
  have hcardH : Nat.card ↥H = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel ↥H .G2 2 f :=
      CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hCE.2
    rw [h, CFSG.Open.ordG2]
  have hq4 : 4 ≤ q := by
    have h : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    simpa [q] using h
  have hq1 : 1 < q := by omega
  have hq6gt : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num : (6 : ℕ) ≠ 0) hq1
  have hApos : 0 < q ^ 6 - 1 := by omega
  let S : Subgroup ↥H := MulAction.stabilizer ↥H x0
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbit ↥H x0) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥H x0) := Fintype.ofFinite _
  have horb : Nat.card (MulAction.orbit ↥H x0) * Nat.card S = Nat.card ↥H := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥H) x0
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
  have hS_card : Nat.card S = q ^ 6 * (q ^ 2 - 1) := by
    have h1 : (q ^ 6 - 1) * Nat.card S = (q ^ 6 - 1) * (q ^ 6 * (q ^ 2 - 1)) := by
      rw [horbit_card, hcardH] at horb
      calc (q ^ 6 - 1) * Nat.card S = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := horb
        _ = (q ^ 6 - 1) * (q ^ 6 * (q ^ 2 - 1)) := by
            rw [mul_comm (q ^ 6) (q ^ 6 - 1), mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hApos h1
  have hpqZ : (p : ℤ) ∣ (q : ℤ) + 1 := by
    have h := hmod.dvd
    have h' : (-1 : ℤ) - (2 : ℤ) ^ f = -(((2 : ℤ) ^ f) + 1) := by ring
    rw [h'] at h
    have h2 : (p : ℤ) ∣ ((2 : ℤ) ^ f) + 1 := (dvd_neg).mp h
    have hqcast : (q : ℤ) = (2 : ℤ) ^ f := by
      rw [show q = 2 ^ f from rfl, Nat.cast_pow]
      norm_num
    rwa [hqcast]
  have hpq : p ∣ q + 1 := by
    have hcast : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
    have h' : (p : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := by rwa [hcast]
    exact_mod_cast h'
  have hpq2 : p ∣ q ^ 2 - 1 := by
    have hdiv : q + 1 ∣ q ^ 2 - 1 := by
      have h : q ^ 2 - 1 = (q + 1) * (q - 1) := by
        simpa using Nat.sq_sub_sq q 1
      rw [h]
      exact dvd_mul_right (q + 1) (q - 1)
    exact hpq.trans hdiv
  have hqeven : Even q := by
    have hf0 : f ≠ 0 := by omega
    simpa [q] using (Nat.even_pow' hf0).mpr (by norm_num : Even (2 : ℕ))
  have hq2even : Even (q ^ 2) := Even.pow_of_ne_zero hqeven (by norm_num)
  have hq2odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow 2 q (by omega : 0 < q)) hq2even (by norm_num : Odd 1)
  have hp2 : p ≠ 2 := Odd.ne_two_of_dvd_nat hq2odd hpq2
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpS : p ∣ Nat.card S := by
    rw [hS_card]
    exact dvd_mul_of_dvd_right hpq2 (q ^ 6)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hsord⟩ := exists_prime_orderOf_dvd_card' p hpS
  let hH : ↥H := s.1
  have hhordH : orderOf hH = p := (Subgroup.orderOf_coe s).trans hsord
  have hhordW : orderOf (hH : MulAut W) = p :=
    (Subgroup.orderOf_coe hH).trans hhordH
  have hfixcoset : hH • x0 = x0 := by
    have h := MulAction.mem_stabilizer_iff.mp s.2
    simpa [S, hH, Subgroup.smul_def] using h
  have hmk : QuotientGroup.mk ((hH : MulAut W) v) = QuotientGroup.mk v := hfixcoset
  have hcZ : (hH : MulAut W) v * v⁻¹ ∈ Z := by
    have hdiv : (hH : MulAut W) v / v ∈ Z :=
      (QuotientGroup.eq_iff_div_mem).mp hmk
    simpa [div_eq_mul_inv] using hdiv
  let c : W := (hH : MulAut W) v * v⁻¹
  have hcZ' : c ∈ Z := hcZ
  have hc2 : c ^ 2 = 1 := hW2 c
  have hspow : (hH : MulAut W) ^ p = 1 := by
    rw [← hhordW]
    exact pow_orderOf_eq_one _
  have hstep : ∀ k : ℕ, ((hH : MulAut W) ^ k) v = v * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc ((hH : MulAut W) ^ (k + 1)) v
            = (hH : MulAut W) (((hH : MulAut W) ^ k) v) := by
                rw [pow_succ']
                rfl
          _ = (hH : MulAut W) (v * c ^ k) := by rw [ih]
          _ = (hH : MulAut W) v * (hH : MulAut W) (c ^ k) := map_mul _ _ _
          _ = (v * c) * c ^ k := by
                have hcv : (hH : MulAut W) v = v * c := by
                  rw [show c = (hH : MulAut W) v * v⁻¹ from rfl]
                  rw [← mul_assoc, mul_comm v ((hH : MulAut W) v), mul_assoc,
                    mul_inv_cancel, mul_one]
                have hcfix : c ^ k ∈ Z := Z.pow_mem hcZ' k
                have hcapply : (hH : MulAut W) (c ^ k) = c ^ k :=
                  CFSG.Quasithin.mem_fixV.1 hcfix hH hH.2
                rw [hcv, hcapply]
          _ = v * c ^ (k + 1) := by rw [mul_assoc, ← pow_succ']
  have hcp : c ^ p = 1 := by
    have hpv := hstep p
    rw [hspow, MulAut.one_apply] at hpv
    have h1 := congrArg (fun z => v⁻¹ * z) hpv
    simpa [mul_assoc] using h1.symm
  have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hpodd
  have hdvd_order : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcp
  have hdvd_two : orderOf c ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa using hc2)
  have hdvd_one : orderOf c ∣ 1 := by
    have h := Nat.dvd_gcd hdvd_order hdvd_two
    rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd_one)
  have hfixv : (hH : MulAut W) v = v := by
    have h1 : (hH : MulAut W) v * v⁻¹ = 1 := hc1
    have h2 := congrArg (fun z => z * v) h1
    simpa [mul_assoc] using h2
  have hcent : (hH : MulAut W) ∈ centVec H v :=
    (centVec.mem_centVec).mpr ⟨hH.2, hfixv⟩
  have hdvd : p ∣ Nat.card (centVec H v) := by
    have h := Subgroup.orderOf_dvd_natCard (centVec H v) hcent
    simpa [hhordW] using h
  exact ⟨hp, hdvd⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
