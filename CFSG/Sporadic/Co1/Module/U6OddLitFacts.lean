module

public import CFSG.Sporadic.Co1.Module.U6OddLit
public import CFSG.Monster.GMS.U6OddSylow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.U6OddNative Matrix
open CFSG.Sporadic.Co1.Module (co1Act v₂ toVecD_v₂)


theorem lSpec_labU6 :
    LSpec labU6 := lSpec_tyLab

theorem commute_cent {g n : NativeSporadic.Co1}
    (h : n ∈ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) : n * g = g * n :=
  (Subgroup.mem_centralizer_iff.1 h g (Set.mem_singleton g)).symm

theorem fixed_of_commute' {g n : NativeSporadic.Co1} (hc : n * g = g * n) {v : Fin 24 → ZMod 2}
    (hv : co1Act g v = v) : co1Act g (co1Act n v) = co1Act n v := by
  calc co1Act g (co1Act n v) = co1Act (g * n) v := (Odd.co1Act_mul' g n v).symm
    _ = co1Act (n * g) v := by rw [hc]
    _ = co1Act n (co1Act g v) := Odd.co1Act_mul' n g v
    _ = co1Act n v := by rw [hv]

theorem vstab_eq_stab (v : Fin 24 → ZMod 2) :
    vstab v = MulAction.stabilizer NativeSporadic.Co1 v := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_vstab]
  rfl

theorem y₀_mem_cls_lit
    (h : ∃ W : U6W, U6OK W) : toVecD 24 u2 ∈ Pairs.cls 3 := by
  obtain ⟨W, hW⟩ := h
  have e1 := (lSpec_labU6.2 u2 hu₂ 3 (by norm_num)).1 hW.l2
  have e2 := (lSpec_labU6.2 (u1 ^^^ u2) (Nat.xor_lt_two_pow hu₁ hu₂) 3 (by norm_num)).1 hW.l12
  refine ⟨?_, ?_⟩
  · rw [Pairs.orbit_Co1_eq]
    exact e1
  · rw [Pairs.tyOrbC_eq]
    have hx : toVecD 24 u1 = v₂ := toVecD_v₂
    rw [toVecD_xor, hx] at e2
    exact e2

theorem card_U0_lit
    (h : ∃ W : U6W, U6OK W) :
    Nat.card ↥(vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)) = 9196830720 := by
  have hc := Pairs.cls_card_stab (j := 3) (by norm_num) (y₀_mem_cls_lit h)
  rw [Pairs.cls_ncard (by norm_num)] at hc
  have h3 : dat.subSizes[3]! = 4600 := by decide
  rw [h3] at hc
  have hx : toVecD 24 u1 = v₂ := toVecD_v₂
  rw [hx, vstab_eq_stab, vstab_eq_stab]
  omega

theorem sylow_arith_lit
    (h : ∃ W : U6W, U6OK W)
    {p : ℕ} [Fact p.Prime] (hp2 : ¬ p ^ 2 ∣ 9196830720) {g : NativeSporadic.Co1}
    (hg : g ∈ vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)) (hord : orderOf g = p) :
    p ∣ Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) :
        Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) ∧
      ∃ s : ℕ, Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) :
        Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) * s =
          9196830720 ∧ s % p = 1 := by
  have hfin := finite_co1
  have hc := CFSG.Monster.GMS.U6Odd.norm_data (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)) (p := p)
    (by rw [card_U0_lit h]; exact hp2) hg hord
  rw [card_U0_lit h] at hc
  exact hc

theorem card_chain0_lit
    (h : ∃ W : U6W, U6OK W) (base : List ℕ) :
    Nat.card (chainGrp u1 u2 base 0) = 9196830720 :=
  card_U0_lit h

theorem norm_ex_five_lit
    (h : ∃ W : U6W, U6OK W) :
    ∃ g ∈ vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2), orderOf g = 5 ∧
      Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) :
        Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) ∣ 120 := by
  obtain ⟨W, hW⟩ := h
  have hfin := finite_co1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hord, hmemK⟩ := lit_g hW hW.p5
  have hord' : orderOf (regG data5.g) = 5 := hord
  have hmem := chainGrp_le_zero u1 u2 data5.base _ hmemK
  obtain ⟨h5, s, hs, hs5⟩ := sylow_arith_lit ⟨W, hW⟩ (p := 5) (by norm_num) hmem hord'
  have hup := lit_card_le_tk hW lSpec_labU6 hW.p5 (card_chain0_lit ⟨W, hW⟩ _)
    (Subgroup.normalizer ((Subgroup.zpowers (regG data5.g) : Subgroup NativeSporadic.Co1) :
      Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)))
    (fun n hn v hv => fixed_of_normalizer (Subgroup.mem_inf.1 hn).1 hv)
    (fun n hn => ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).2).1,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).2).2⟩)
  have hup' : Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers (regG data5.g) :
      Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1) ⊓
        (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) ≤ 120 := hup
  have hlo := lit_norm hW
  refine ⟨regG data5.g, hmem, hord', ?_⟩
  generalize Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers (regG data5.g) :
    Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1) ⊓
      (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) = m at h5 hs hup' hlo
  have hm : m = 120 := by
    interval_cases m <;> omega
  rw [hm]

theorem norm_ex_seven_lit
    (h : ∃ W : U6W, U6OK W) :
    ∃ g ∈ vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2), orderOf g = 7 ∧
      Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) :
        Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) ∣ 42 := by
  obtain ⟨W, hW⟩ := h
  have hfin := finite_co1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hord, hmemK⟩ := lit_g hW hW.p7
  have hord' : orderOf (regG data7.g) = 7 := hord
  have hmem := chainGrp_le_zero u1 u2 data7.base _ hmemK
  obtain ⟨h7, s, hs, hs7⟩ := sylow_arith_lit ⟨W, hW⟩ (p := 7) (by norm_num) hmem hord'
  have hup := lit_card_le_tk hW lSpec_labU6 hW.p7 (card_chain0_lit ⟨W, hW⟩ _)
    (Subgroup.normalizer ((Subgroup.zpowers (regG data7.g) : Subgroup NativeSporadic.Co1) :
      Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)))
    (fun n hn v hv => fixed_of_normalizer (Subgroup.mem_inf.1 hn).1 hv)
    (fun n hn => ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).2).1,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).2).2⟩)
  have hup' : Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers (regG data7.g) :
      Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1) ⊓
        (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) ≤ 42 := hup
  refine ⟨regG data7.g, hmem, hord', ?_⟩
  generalize Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers (regG data7.g) :
    Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1) ⊓
      (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) = m at h7 hs hup'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hs
      omega
    · exact h
  have hm : m = 42 := by
    interval_cases m <;> omega
  rw [hm]

theorem norm_ex_eleven_lit
    (h : ∃ W : U6W, U6OK W) :
    ∃ g ∈ vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2), orderOf g = 11 ∧
      Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) :
        Set NativeSporadic.Co1) ⊓ (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) ∣ 55 := by
  obtain ⟨W, hW⟩ := h
  have hfin := finite_co1
  have hp11 : Nat.Prime 11 := by norm_num
  have : Fact (Nat.Prime 11) := ⟨hp11⟩
  obtain ⟨hord, hmemK⟩ := lit_g hW hW.p11
  have hord' : orderOf (regG data11.g) = 11 := hord
  have hmem := chainGrp_le_zero u1 u2 data11.base _ hmemK
  obtain ⟨h11, s, hs, hs11⟩ := sylow_arith_lit ⟨W, hW⟩ (p := 11) (by norm_num) hmem hord'
  set U0' := vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2) with hU0'
  set N := Subgroup.normalizer ((Subgroup.zpowers (regG data11.g) : Subgroup NativeSporadic.Co1) :
    Set NativeSporadic.Co1) ⊓ U0' with hN
  refine ⟨regG data11.g, hmem, hord', ?_⟩
  set g := regG data11.g with hgdef
  set K := chainGrp u1 u2 data11.base data11.base.length with hK
  have hKle : Nat.card K ≤ 660 := lit_chain_le_k hW hW.p11 (card_chain0_lit ⟨W, hW⟩ _)
  have hcl' : 60 * Nat.card ↥(K ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) ≤
      Nat.card K := lit_class hW
  have hCK : Nat.card ↥(K ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) ≤ 11 := by
    omega
  have hCg : Nat.card ↥(U0' ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) ≤
      data11.t * Nat.card ↥((U0' ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) ⊓ K) :=
    lit_card_le_t_inf hW lSpec_labU6 hW.p11 _
      (fun n hn v hv => fixed_of_commute' (commute_cent (Subgroup.mem_inf.1 hn).2) hv)
      (fun n hn => ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).1).2⟩)
  have hCgK : Nat.card ↥((U0' ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) ⊓ K) ≤
      Nat.card ↥(K ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) :=
    Subgroup.card_le_of_le (fun x hx => ⟨(Subgroup.mem_inf.1 hx).2,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2⟩)
  have hCg11 : Nat.card ↥(U0' ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) ≤ 11 := by
    have ht : data11.t = 1 := rfl
    rw [ht] at hCg
    omega
  have hPcard : Nat.card (Subgroup.zpowers g) = 11 := by rw [Nat.card_zpowers, hord']
  have hNle : N ≤ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup _) : Set _) := inf_le_left
  have h1 := CFSG.Monster.GMS.U6Odd.card_le_mul_normalizer (Subgroup.zpowers g) N hp11 hPcard hNle
  have h2 : Nat.card ↥(N ⊓ Subgroup.centralizer ((Subgroup.zpowers g : Subgroup _) : Set _)) ≤
      Nat.card ↥(U0' ⊓ Subgroup.centralizer ({g} : Set NativeSporadic.Co1)) :=
    Subgroup.card_le_of_le (fun x hx => ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2,
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers g))
        (Subgroup.mem_inf.1 hx).2⟩)
  have hup : Nat.card N ≤ 110 := by omega
  generalize Nat.card N = m at h11 hs hup
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hs
      omega
    · exact h
  have hm : m = 55 := by
    interval_cases m <;> omega
  rw [hm]

theorem s0_exists_lit (h : ∃ W : U6W, U6OK W) :
    ∃ S : Subgroup NativeSporadic.Co1, Nat.card S = 729 ∧
      S ≤ vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2) ∧
      ∀ A : Subgroup NativeSporadic.Co1, A ≤ S → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
        Nat.card A < 243 := by
  obtain ⟨W, hW⟩ := h
  exact lit_s0 hW

end CFSG.Sporadic.Co1.Module.U6Odd

end
