module

public import CFSG.Permutation.SylowTwoNormalizer.AltTransitive
public import Mathlib.GroupTheory.GroupAction.Transitive

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_orbit_card_ge_two_of_le_alternatingGroup (h4 : 4 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) :
    ∃ x : Ω, 2 ≤ Nat.card (MulAction.orbit R x) := by
  classical
  have h2n : 2 ≤ Nat.card Ω := by omega
  have hcard : 2 * Nat.card R = 2 ^ padicValNat 2 (Nat.card Ω).factorial :=
    two_mul_card_eq_of_not_two_dvd_relIndex h2n hRA hR hRi
  have h3 : 3 ≤ padicValNat 2 (Nat.card Ω).factorial := by
    have h := padicValNat_two_factorial_add_le 4 (Nat.card Ω - 4)
    have hn : 4 + (Nat.card Ω - 4) = Nat.card Ω := by omega
    rw [hn] at h
    have h24 : padicValNat 2 (Nat.factorial 4) = 3 := by
      simpa using padicValNat_two_factorial_two_pow 2
    omega
  have h4R : 4 ≤ Nat.card R := by
    have hpow : 2 ^ 3 ≤ 2 ^ padicValNat 2 (Nat.card Ω).factorial :=
      Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hRbot : R ≠ ⊥ := by
    intro h
    have hc : Nat.card R = 1 := by rw [h]; exact Subgroup.card_bot
    omega
  have hex : ∃ g ∈ R, g ≠ 1 := by
    by_contra h
    push Not at h
    exact hRbot ((Subgroup.eq_bot_iff_forall R).mpr h)
  obtain ⟨g, hgR, hg1⟩ := hex
  have hgx : ∃ x : Ω, g x ≠ x := by
    by_contra h
    push Not at h
    exact hg1 (Equiv.ext h)
  obtain ⟨x, hx⟩ := hgx
  refine ⟨x, ?_⟩
  have hx' : x ∈ MulAction.orbit R x := MulAction.mem_orbit_self x
  have hgx' : g x ∈ MulAction.orbit R x := MulAction.mem_orbit x (⟨g, hgR⟩ : R)
  rw [Nat.card_coe_set_eq]
  calc 2 = ({x, g x} : Set Ω).ncard := (Set.ncard_pair (Ne.symm hx)).symm
    _ ≤ (MulAction.orbit R x).ncard := by
        apply Set.ncard_le_ncard
        · intro y hy
          rcases hy with rfl | rfl
          · exact hx'
          · exact hgx'
        · exact Set.toFinite _

theorem eq_one_or_exists_orbit_of_not_isPretransitive (h4 : 4 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) {σ : Perm Ω} (hσ : Odd (orderOf σ))
    (hσR : σ ∈ normalizer (R : Set (Perm Ω))) (hntr : ¬ MulAction.IsPretransitive R Ω)
    {x : Ω} {s : Set Ω} (hs : s = MulAction.orbit R x) (hx2 : 2 ≤ Nat.card s)
    [DecidablePred (· ∈ s)] :
    σ = 1 ∨ (Nat.card ↥(sᶜ) = 1 ∧ σ ∈ stabilizer (Perm Ω) s ∧
      restr R s ≤ alternatingGroup s ∧ MulAction.IsPretransitive (restr R s) s ∧
      ¬ 2 ∣ (restr R s).relIndex (alternatingGroup s) ∧
      Nat.card s = Nat.card Ω - 1 ∧ ∃ k, Nat.card s = 2 ^ k) := by
  classical
  have h2n : 2 ≤ Nat.card Ω := by omega
  have hSn : s ≠ Set.univ := by
    rw [hs]
    intro h
    exact hntr ((MulAction.isPretransitive_iff_orbit_eq_univ x).mpr h)
  haveI hneT : Nonempty ↥(sᶜ) := by
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem s).mp hSn
    exact ⟨⟨y, hy⟩⟩
  have hRs : R ≤ stabilizer (Perm Ω) s := by
    rw [hs]
    exact le_stabilizer_orbit R x
  have hσs : σ ∈ stabilizer (Perm Ω) s := by
    rw [hs]
    exact mem_stabilizer_orbit hσR (apply_mem_orbit_of_le_alternatingGroup h4 hRA hR hRi hσR x)
  have hσsc : σ ∈ stabilizer (Perm Ω) sᶜ := by
    rw [stabilizer_compl]
    exact hσs
  set v := padicValNat 2 (Nat.card Ω).factorial with hv
  set p := padicValNat 2 (Nat.card s).factorial with hp
  set q := padicValNat 2 (Nat.card ↥(sᶜ)).factorial with hq
  have hcard : 2 * Nat.card R = 2 ^ v :=
    two_mul_card_eq_of_not_two_dvd_relIndex h2n hRA hR hRi
  have hsum : Nat.card s + Nat.card ↥(sᶜ) = Nat.card Ω := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_add_ncard_compl]
  have hpq : p + q ≤ v := by
    have h := padicValNat_two_factorial_add_le (Nat.card s) (Nat.card ↥(sᶜ))
    rwa [hsum] at h
  have hv1 : 1 ≤ v := by
    rw [← Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), pow_one]
    calc 2 = 2 * 1 := by norm_num
      _ ≤ 2 * Nat.card R := by
          have hpos : 0 < Nat.card R := Nat.card_pos
          omega
      _ = 2 ^ v := hcard
  have hRcard : Nat.card R = 2 ^ (v - 1) := by
    have hv2 : 2 * 2 ^ (v - 1) = 2 ^ v := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hv1]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (hcard.trans hv2.symm)
  obtain ⟨r, hrle, hr⟩ : ∃ r ≤ p, Nat.card (restr R s) = 2 ^ r :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (card_dvd_of_isPGroup (Ω := ↥s) (R := restr R s) (isPGroup_restr hR s))
  obtain ⟨c, hcle, hc⟩ : ∃ c ≤ q, Nat.card (restr R sᶜ) = 2 ^ c :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (card_dvd_of_isPGroup (Ω := ↥(sᶜ)) (R := restr R sᶜ) (isPGroup_restr hR sᶜ))
  have hdvd : Nat.card R ∣ 2 ^ (r + c) := by
    have h := card_dvd_card_restr_mul (R := R) (s := s) hRs
    rw [hr, hc, ← pow_add] at h
    exact h
  have hle : v - 1 ≤ r + c := by
    have h : 2 ^ (v - 1) ∣ 2 ^ (r + c) := by
      rw [← hRcard]
      exact hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h
  by_cases hboth : r = p ∧ c = q
  ·
    left
    obtain ⟨hrp, hcq⟩ := hboth
    have hsylS : ¬ 2 ∣ (restr R s).index := by
      refine not_two_dvd_index_of_dvd_card (Ω := ↥s) (R := restr R s) (isPGroup_restr hR s) ?_
      rw [hr, hrp]
    have hsylT : ¬ 2 ∣ (restr R sᶜ).index := by
      refine not_two_dvd_index_of_dvd_card (Ω := ↥(sᶜ)) (R := restr R sᶜ) (isPGroup_restr hR sᶜ) ?_
      rw [hc, hcq]
    refine eq_one_of_restrictHom_eq_one hσs hσsc ?_ ?_
    · exact eq_one_of_mem_normalizer (Ω := ↥s) (R := restr R s) (isPGroup_restr hR s) hsylS
        (odd_orderOf_restrictHom hσs hσ) (restrictHom_mem_normalizer hσs hσR)
    · exact eq_one_of_mem_normalizer (Ω := ↥(sᶜ)) (R := restr R sᶜ) (isPGroup_restr hR sᶜ) hsylT
        (odd_orderOf_restrictHom hσsc hσ) (restrictHom_mem_normalizer hσsc hσR)
  · right
    have hrc_le : r + c ≤ v := le_trans (by omega) hpq
    have hrc_ne : r + c ≠ v := by
      intro h
      exact hboth (by omega)
    have hrc : r + c = v - 1 := by omega
    have hcard_eq : Nat.card R = Nat.card (restr R s) * Nat.card (restr R sᶜ) := by
      rw [hr, hc, ← pow_add, hRcard, hrc]
    have hstrict : (p - r) + (q - c) ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos (p - r) with hpr | hpr
    ·
      have hrp : r = p := by omega
      have hsylS : ¬ 2 ∣ (restr R s).index := by
        refine not_two_dvd_index_of_dvd_card (Ω := ↥s) (R := restr R s) (isPGroup_restr hR s) ?_
        rw [hr, hrp]
      exact (false_of_card_eq_mul' (s := s) hRA hR hRs hx2 hsylS hcard_eq).elim
    ·
      have hqc : c = q := by omega
      have hsylT : ¬ 2 ∣ (restr R sᶜ).index := by
        refine not_two_dvd_index_of_dvd_card (Ω := ↥(sᶜ)) (R := restr R sᶜ)
          (isPGroup_restr hR sᶜ) ?_
        rw [hc, hqc]
      have hTcard : Nat.card ↥(sᶜ) = 1 := by
        by_contra h1
        have h2T : 2 ≤ Nat.card ↥(sᶜ) := by
          have hpos : 0 < Nat.card ↥(sᶜ) := Nat.card_pos
          omega
        exact false_of_card_eq_mul (s := s) hRA hR hRs h2T hsylT hcard_eq
      have hcardT : Nat.card (restr R sᶜ) = 1 := by
        have hperm : Nat.card (Perm ↥(sᶜ)) = 1 := by
          rw [Nat.card_perm, hTcard, Nat.factorial_one]
        have hd : Nat.card (restr R sᶜ) ∣ Nat.card (Perm ↥(sᶜ)) :=
          Subgroup.card_subgroup_dvd_card _
        rw [hperm] at hd
        exact Nat.dvd_one.mp hd
      have hcardS : Nat.card (restr R s) = Nat.card R := by
        rw [hcard_eq, hcardT, mul_one]
      have htrS : MulAction.IsPretransitive (restr R s) s := by
        rw [MulAction.isPretransitive_iff]
        intro a b
        have ha : (a : Ω) ∈ MulAction.orbit R x := hs ▸ a.2
        have hb : (b : Ω) ∈ MulAction.orbit R x := hs ▸ b.2
        obtain ⟨g, hg⟩ : ∃ g : R, g • x = (a : Ω) := MulAction.mem_orbit_iff.mp ha
        obtain ⟨k, hk⟩ : ∃ k : R, k • x = (b : Ω) := MulAction.mem_orbit_iff.mp hb
        have h1 : ((g⁻¹ : R)) • (a : Ω) = x := by
          have hh := congrArg (fun z => ((g⁻¹ : R)) • z) hg
          simpa using hh.symm
        have h2 : ((k * g⁻¹ : R) : Perm Ω) (a : Ω) = (b : Ω) := by
          have hmul : ((k * g⁻¹ : R) : Perm Ω) (a : Ω) = ((k * g⁻¹ : R)) • (a : Ω) := rfl
          rw [hmul, mul_smul, h1, hk]
        refine ⟨⟨restrictHom s ⟨(k * g⁻¹ : R), hRs (k * g⁻¹).2⟩, ?_⟩, ?_⟩
        · rw [mem_restr]
          exact ⟨⟨(k * g⁻¹ : R), hRs (k * g⁻¹).2⟩, (k * g⁻¹).2, rfl⟩
        · apply Subtype.ext
          show (((restrictHom s ⟨(k * g⁻¹ : R), hRs (k * g⁻¹).2⟩ : Perm s))) a = (b : Ω)
          rw [restrictHom_apply]
          exact h2
      have hRSA : restr R s ≤ alternatingGroup s :=
        restr_le_alternatingGroup hRA hRs (by omega)
      have hp_eq : p = v := by
        have h2 : 2 ^ v ∣ 2 ^ p := by
          rw [← hcard, ← hcardS]
          exact two_mul_card_dvd_of_le_alternatingGroup hx2 hRSA (isPGroup_restr hR s)
        have hle' : v ≤ p := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
        omega
      have hSylS : ¬ 2 ∣ (restr R s).relIndex (alternatingGroup s) := by
        refine not_two_dvd_relIndex_of_dvd_two_mul_card (Ω := ↥s) hx2 hRSA
          (isPGroup_restr hR s) ?_
        rw [← hp, hcardS, hcard, hp_eq]
      have hcardΩ : Nat.card s = Nat.card Ω - 1 := by omega
      have hds : Nat.card s ∣ Nat.card (restr R s) := by
        haveI : MulAction.IsPretransitive (restr R s) s := htrS
        have hx : x ∈ s := by rw [hs]; exact MulAction.mem_orbit_self x
        haveI : Nonempty s := ⟨⟨x, hx⟩⟩
        exact TauCeti.natCard_dvd_natCard_of_isPretransitive (restr R s)
      have hk : ∃ k, Nat.card s = 2 ^ k := by
        have hd : Nat.card s ∣ 2 ^ r := by rwa [hr] at hds
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
        exact ⟨k, hk⟩
      exact ⟨hTcard, hσs, hRSA, htrS, hSylS, hcardΩ, hk⟩

theorem eq_one_of_mem_normalizer_of_le_alternatingGroup (h6 : 6 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) {σ : Perm Ω} (hσ : Odd (orderOf σ))
    (hσR : σ ∈ normalizer (R : Set (Perm Ω))) : σ = 1 := by
  classical
  have h4 : 4 ≤ Nat.card Ω := by omega
  obtain ⟨x, hx2⟩ := exists_orbit_card_ge_two_of_le_alternatingGroup h4 hRA hR hRi
  by_cases htr : MulAction.IsPretransitive R Ω
  · have hdvd : Nat.card Ω ∣ 2 ^ padicValNat 2 (Nat.card Ω).factorial :=
      haveI : Nonempty Ω := ⟨x⟩
      (TauCeti.natCard_dvd_natCard_of_isPretransitive R).trans (card_dvd_of_isPGroup hR)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdvd
    have h8 : 8 ≤ Nat.card Ω := by
      have hk3 : 3 ≤ k := by
        by_contra h
        have hle : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        _ = Nat.card Ω := hk.symm
    exact eq_one_of_mem_normalizer_of_isPretransitive h8 hRA hR hRi htr hσ hσR
  · rcases eq_one_or_exists_orbit_of_not_isPretransitive h4 hRA hR hRi hσ hσR htr rfl hx2
      (x := x) (s := MulAction.orbit R x) with
      h | ⟨hT, hσs, hRSA, htrS, hSylS, hcardΩ, k, hk⟩
    · exact h
    · have h8 : 8 ≤ Nat.card (MulAction.orbit R x) := by
        have hk3 : 3 ≤ k := by
          by_contra h
          have h5 : 5 ≤ Nat.card (MulAction.orbit R x) := by
            rw [hcardΩ]
            omega
          have hle : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
          _ = Nat.card (MulAction.orbit R x) := hk.symm
      have hres : restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩ = 1 :=
        eq_one_of_mem_normalizer_of_isPretransitive h8 hRSA (isPGroup_restr hR _) hSylS htrS
          (odd_orderOf_restrictHom hσs hσ) (restrictHom_mem_normalizer hσs hσR)
      have hσsc : σ ∈ stabilizer (Perm Ω) ((MulAction.orbit R x)ᶜ) := by
        rw [stabilizer_compl]
        exact hσs
      have hres' : restrictHom ((MulAction.orbit R x)ᶜ) ⟨σ, hσsc⟩ = 1 := by
        haveI : Subsingleton ↥((MulAction.orbit R x)ᶜ) := (Nat.card_eq_one_iff_unique.mp hT).1
        exact Subsingleton.elim _ _
      exact eq_one_of_restrictHom_eq_one hσs hσsc hres hres'

theorem pow_three_eq_one_of_mem_normalizer_of_le_alternatingGroup (h5 : Nat.card Ω = 5)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) {σ : Perm Ω} (hσ : Odd (orderOf σ))
    (hσR : σ ∈ normalizer (R : Set (Perm Ω))) : σ ^ 3 = 1 := by
  classical
  have h4 : 4 ≤ Nat.card Ω := by omega
  obtain ⟨x, hx2⟩ := exists_orbit_card_ge_two_of_le_alternatingGroup h4 hRA hR hRi
  have hntr : ¬ MulAction.IsPretransitive R Ω := by
    intro htr
    haveI : Nonempty Ω := ⟨x⟩
    have hdvd : Nat.card Ω ∣ Nat.card R := TauCeti.natCard_dvd_natCard_of_isPretransitive R
    have h5dvd : 5 ∣ Nat.card R := by
      rw [h5] at hdvd
      exact hdvd
    have h25 : 5 ∣ 2 ^ padicValNat 2 (Nat.card Ω).factorial :=
      h5dvd.trans (card_dvd_of_isPGroup hR)
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) h25
    norm_num at h52
  rcases eq_one_or_exists_orbit_of_not_isPretransitive h4 hRA hR hRi hσ hσR hntr rfl hx2
    (x := x) (s := MulAction.orbit R x) with
    h | ⟨hT, hσs, hRSA, htrS, hSylS, hcardΩ, k, hk⟩
  · rw [h, one_pow]
  · have hscard : Nat.card (MulAction.orbit R x) = 4 := by
      rw [hcardΩ, h5]
    have hτdvd : orderOf (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩) ∣ 24 := by
      have h := orderOf_dvd_natCard (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩)
      rw [Nat.card_perm, hscard] at h
      have h24 : Nat.factorial 4 = 24 := by decide
      rwa [h24] at h
    have hoddτ : Odd (orderOf (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩)) :=
      odd_orderOf_restrictHom hσs hσ
    have hcop : Nat.Coprime (orderOf (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩)) 8 := by
      have h2 : Nat.Coprime (orderOf (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩)) 2 :=
        (Nat.coprime_two_right).mpr hoddτ
      simpa using h2.pow_right 3
    have hτ3 : orderOf (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩) ∣ 3 := by
      refine hcop.dvd_of_dvd_mul_left ?_
      rw [show (8 : ℕ) * 3 = 24 by norm_num]
      exact hτdvd
    have hτpow : (restrictHom (MulAction.orbit R x) ⟨σ, hσs⟩) ^ 3 = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp hτ3
    have hσ3s : σ ^ 3 ∈ stabilizer (Perm Ω) (MulAction.orbit R x) :=
      (stabilizer (Perm Ω) (MulAction.orbit R x)).pow_mem hσs 3
    have hres3 : restrictHom (MulAction.orbit R x) ⟨σ ^ 3, hσ3s⟩ = 1 := by
      have hsub : (⟨σ ^ 3, hσ3s⟩ : stabilizer (Perm Ω) (MulAction.orbit R x)) =
          ⟨σ, hσs⟩ ^ 3 := Subtype.ext rfl
      rw [hsub, map_pow, hτpow]
    have hσ3sc : σ ^ 3 ∈ stabilizer (Perm Ω) ((MulAction.orbit R x)ᶜ) := by
      rw [stabilizer_compl]
      exact hσ3s
    have hres3' : restrictHom ((MulAction.orbit R x)ᶜ) ⟨σ ^ 3, hσ3sc⟩ = 1 := by
      haveI : Subsingleton ↥((MulAction.orbit R x)ᶜ) := (Nat.card_eq_one_iff_unique.mp hT).1
      exact Subsingleton.elim _ _
    exact eq_one_of_restrictHom_eq_one hσ3s hσ3sc hres3 hres3'

end CFSG.Permutation.SylowTwoNormalizer
