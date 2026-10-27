
module

public import CFSG.Sporadic.Co1.Module.OddBuildBase1

public import CFSG.Sporadic.Co1.Module.OddNative

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix CFSG.KC.Odd73 CFSG.KC.Co1F2 CFSG.KD.Co1Odd

attribute [local instance] vecAct vecSMul

attribute [local irreducible] rr regsRows

theorem omega0_mem :
    omega0 ∈ MulAction.orbit Jmat v₄ :=
  (type4N_iff code4 (by norm_num [code4])).1 validOK_facts.2.2.2.2.2

theorem orbit_omega0 :
    MulAction.orbit NativeSporadic.Co1 omega0 = MulAction.orbit Jmat v₄ := by
  rw [orbit_eq_range, range_co1Act]
  exact MulAction.orbit_eq_iff.2 omega0_mem

theorem card_Hst :
    Nat.card Hst = 501397585920 := by
  have h := card_stabilizer_mul_ncard_orbit NativeSporadic.Co1 omega0
  rw [orbit_omega0, orbit_ncard_v₄, CFSG.Sporadic.Co1.card_Co1] at h
  have h2 : Nat.card Hst * 8292375 = 501397585920 * 8292375 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

theorem fix4_rho3 :
    {ω ∈ MulAction.orbit NativeSporadic.Co1 omega0 | rho3 • ω = ω}.ncard = 32535 := by
  rw [orbit_omega0]
  have h := ncard_fixedSet4 [rr 27]
  have e : {ω ∈ MulAction.orbit Jmat v₄ | rho3 • ω = ω} =
      {v | v ∈ MulAction.orbit Jmat v₄ ∧ ∀ M ∈ [rr 27], rowsMatrix 24 M *ᵥ v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, List.mem_singleton, forall_eq]
    exact and_congr_right fun _ => smul_reg_iff 27 v
  rw [e, h]
  exact fixOK₂_facts.2

theorem S_card_eq
    (hC : Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) = 89181388800) :
    {t : NativeSporadic.Co1 | t ∈ Hst ∧ IsConj rho3 t}.ncard = 182919 := by
  have := finite_co1
  have h := card_centralizer_mul_ncard_conj_inter (G := NativeSporadic.Co1) (Ω := Vec24) rho3
    omega0
  rw [hC, card_Hst, fix4_rho3] at h
  have h' : 89181388800 * {t : NativeSporadic.Co1 | t ∈ Hst ∧ IsConj rho3 t}.ncard =
      501397585920 * 32535 := h
  omega

theorem pair_fix_gen
    {k fx f4 : ℕ} (h : pairFixOK k fx f4 = true) :
    ({ω : Vec24 | reg 27 • ω = ω} ∩ {ω | reg (sIdx[k]!) • ω = ω}).ncard = fx ∧
    {ω ∈ MulAction.orbit NativeSporadic.Co1 omega0 |
      reg 27 • ω = ω ∧ reg (sIdx[k]!) • ω = ω}.ncard = f4 := by
  obtain ⟨h1, h2⟩ := pairFixOK_facts h
  have e1 : {ω : Vec24 | reg 27 • ω = ω} ∩ {ω | reg (sIdx[k]!) • ω = ω} =
      {v | ∀ M ∈ [rr 27, rr (sIdx[k]!)], rowsMatrix 24 M *ᵥ v = v} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, forall_mem_two]
    rw [smul_reg_iff, smul_reg_iff]
  refine ⟨?_, ?_⟩
  · rw [e1, ncard_fixedSet]
    exact h1
  · rw [orbit_omega0]
    have e2 : {ω ∈ MulAction.orbit Jmat v₄ | reg 27 • ω = ω ∧ reg (sIdx[k]!) • ω = ω} =
        {v | v ∈ MulAction.orbit Jmat v₄ ∧
          ∀ M ∈ [rr 27, rr (sIdx[k]!)], rowsMatrix 24 M *ᵥ v = v} := by
      ext v
      simp only [Set.mem_ofPred_eq, forall_mem_two]
      rw [smul_reg_iff, smul_reg_iff]
    rw [e2, ncard_fixedSet4]
    exact h2

theorem pair_fix_ncard
    (k : Fin 3) :
    ({ω : Vec24 | rho3 • ω = ω} ∩ {ω | sRep k • ω = ω}).ncard = ![1024, 256, 256] k := by
  fin_cases k
  · exact (pair_fix_gen pairFixOK_0).1
  · exact (pair_fix_gen pairFixOK_1).1
  · exact (pair_fix_gen pairFixOK_2).1

theorem pair_fix4_ncard
    (k : Fin 3) :
    {ω ∈ MulAction.orbit NativeSporadic.Co1 omega0 | rho3 • ω = ω ∧ sRep k • ω = ω}.ncard =
      ![405, 135, 75] k := by
  fin_cases k
  · exact (pair_fix_gen pairFixOK_0).2
  · exact (pair_fix_gen pairFixOK_1).2
  · exact (pair_fix_gen pairFixOK_2).2

theorem exists_cert
    (hC : Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) = 89181388800) :
    ∃ C : OddCert NativeSporadic.Co1 Vec24, C.ω₀ = omega0 ∧ C.ρ = rho3 ∧
      (∀ k, C.s k = sRep k) ∧ C.Zn = ![384, 1344, 96] ∧ C.o = ![3, 3, 5] ∧
      C.d = ![1024, 256, 256] := by
  have := finite_co1
  obtain ⟨W, hW⟩ := lit_ok
  have hH := oddHyp73
  have hHc := card_Hst
  have hS : (S73 Hst).ncard = 182919 := S_card_eq hC
  choose z hz hzinj using fun k : Fin 3 => z_tree_facts73 hW k.2
  refine ⟨{
    ω₀ := omega0
    ρ := rho3
    t₁ := t1
    s := sRep
    ρ_sq := rho3_sq
    ρ_mem := rho3_mem
    s_mem := sRep_mem
    s_conj := sRep_conj
    S_cover := fun t h1 h2 => S_cover73 hW hH hS t ⟨h1, h2⟩
    scan₁ := fun t h1 h2 hne => scan73 hW hH hHc hS t ⟨h1, h2⟩ hne
    partner := fun t h1 h2 hne hodd => by
      obtain ⟨k, hk, c, hc, e⟩ := partner73 hW hH hHc t ⟨h1, h2⟩ hne hodd
      refine ⟨⟨k, hk⟩, c, hc, ?_⟩
      rw [e, sRep, sIdx_J73 hk]
    o := ![3, 3, 5]
    d := ![1024, 256, 256]
    o_spec := fun k => by
      fin_cases k
      · exact order_rho3_sRep.1
      · exact order_rho3_sRep.2.1
      · exact order_rho3_sRep.2.2
    d_spec := pair_fix_ncard
    o_odd := fun k => by fin_cases k <;> decide
    o_gt := fun k => by fin_cases k <;> decide
    sep := by decide
    Zn := ![384, 1344, 96]
    z := z
    z_inj := fun k => hzinj k
    z_mem := fun k i hi => (hz k i hi).1
    Z_le := fun k => by
      have h := Z_le73 hW hH hHc (k := k.val) k.2
      have e : getL 0 J73 k.val = sIdx[(k : ℕ)]! := (sIdx_J73 k.2).symm
      rw [e] at h
      change Nat.card ↥(Hst ⊓ Subgroup.centralizer {rho3} ⊓ Subgroup.centralizer {sRep k}) *
        getL 0 [7168, 2048, 28672, 759] k.val ≤ 2752512 at h
      change Nat.card ↥(Hst ⊓ Subgroup.centralizer {rho3} ⊓ Subgroup.centralizer {sRep k}) ≤ _
      generalize Nat.card ↥(Hst ⊓ Subgroup.centralizer {rho3} ⊓ Subgroup.centralizer {sRep k}) = m
        at h ⊢
      fin_cases k
      · change _ * 7168 ≤ 2752512 at h
        change _ ≤ 384
        omega
      · change _ * 2048 ≤ 2752512 at h
        change _ ≤ 1344
        omega
      · change _ * 28672 ≤ 2752512 at h
        change _ ≤ 96
        omega
    faith := fun k hk i hi hfix => (hz k i hi).2 (fun h => hk (Fin.ext h)) hfix }, rfl, rfl,
    fun _ => rfl, rfl, rfl, rfl⟩

end CFSG.Sporadic.Co1.Module.Odd
