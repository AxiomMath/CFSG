module

public import CFSG.Quasithin.Recognition.CertTitsOvergroup
public import CFSG.Quasithin.Recognition.CertTwoLocalIndexTwo

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Sporadic.Schreier.Tits

abbrev titsJD : Subgroup titsD := titsJ.subgroupOf titsD

abbrev titsKD : Subgroup titsD := titsK.subgroupOf titsD

theorem card_titsSD
    : Nat.card titsSD = 2048 := by
  rw [card_subgroupOf_titsD titsS_le_titsD, titsQS_facts.2.2.2]

theorem card_titsHD
    : Nat.card titsHD = 10240 := by
  rw [card_subgroupOf_titsD titsH_le_titsD, titsQH_facts.2.2.2]

theorem card_titsND
    : Nat.card titsND = 6144 := by
  rw [card_subgroupOf_titsD titsN_le_titsD, titsQN_facts.2.2.2]

theorem card_titsJD
    : Nat.card titsJD = 512 := by
  rw [card_subgroupOf_titsD titsJ_le_titsD, titsQJ_facts.2.2.2]

theorem card_titsKD
    : Nat.card titsKD = 1024 := by
  rw [card_subgroupOf_titsD titsK_le_titsD, titsQK_facts.2.2.2]

theorem titsSD_le_titsHD
    : titsSD ≤ titsHD := fun _ hx => titsS_le_titsH hx

theorem titsSD_le_titsND
    : titsSD ≤ titsND := fun _ hx => titsS_le_titsN hx

theorem titsD_le_normalizer_of_normal {A B : Subgroup (Equiv.Perm (Fin 1755))} (hAB : A ≤ B)
    (hn : (A.subgroupOf B).Normal) :
    B.subgroupOf titsD ≤ Subgroup.normalizer ((A.subgroupOf titsD : Subgroup titsD) : Set titsD) := by
  have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).1 hn
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro j
  have h2 := Subgroup.mem_normalizer_iff.1 (h1 hh) (j : Equiv.Perm (Fin 1755))
  simpa [Subgroup.mem_subgroupOf] using h2

theorem titsD_no_normal_two_subgroup
    (Q : Subgroup titsD) (hQ : Q.Normal) (hp : IsPGroup 2 Q) :
    Q = ⊥ := by
  have := hQ
  rcases titsD_simple.eq_bot_or_eq_top_of_normal Q with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hp
    rw [h, Subgroup.card_top, card_titsD] at hn
    have h3 : 3 ∣ 2 ^ n := ⟨5990400, by rw [← hn]⟩
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

@[expose] def titsTwoLocalLattice
    : TwoLocalLattice titsD where
  S := titsSD
  P₁ := titsHD
  P₂ := titsND
  sylow := ⟨titsS_isPGroup, by rw [titsS_index]; decide⟩
  lattice := titsD_overgroups
  S_le_P₁ := titsSD_le_titsHD
  S_le_P₂ := titsSD_le_titsND
  S_ne_P₁ := fun h => by
    have := congrArg (fun K : Subgroup titsD => Nat.card K) h
    simp only [card_titsSD, card_titsHD] at this
    omega
  S_ne_P₂ := fun h => by
    have := congrArg (fun K : Subgroup titsD => Nat.card K) h
    simp only [card_titsSD, card_titsND] at this
    omega
  P₁_not_le_P₂ := fun h => by
    have := Subgroup.card_dvd_of_le h
    rw [card_titsHD, card_titsND] at this
    omega
  P₂_not_le_P₁ := fun h => by
    have := Subgroup.card_dvd_of_le h
    rw [card_titsHD, card_titsND] at this
    omega
  O₂ := titsD_no_normal_two_subgroup
  loc₁ := by
    obtain ⟨-, -, -, -, -, -, hJn, -⟩ := AT_Tits_intrinsic_local_pair
    refine ⟨titsJD, ?_, IsPGroup.of_card (n := 9) (by rw [card_titsJD]; norm_num),
      titsD_le_normalizer_of_normal titsJ_le_titsH hJn⟩
    intro h
    have := card_titsJD
    rw [h, Subgroup.card_bot] at this
    omega
  loc₂ := by
    obtain ⟨-, -, -, -, -, -, -, hKn, -⟩ := AT_Tits_intrinsic_local_pair
    refine ⟨titsKD, ?_, IsPGroup.of_card (n := 10) (by rw [card_titsKD]; norm_num),
      titsD_le_normalizer_of_normal titsK_le_titsN hKn⟩
    intro h
    have := card_titsKD
    rw [h, Subgroup.card_bot] at this
    omega
  normS := titsSD_normalizer_le

instance titsD_finite
    : Finite titsD := Nat.finite_of_card_ne_zero (by rw [card_titsD]; norm_num)

end CFSG.Quasithin
