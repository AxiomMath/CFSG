module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def Kl1h : Subgroup Ah := listSub Kl1L Kl1_check.1 Kl1_check.2.1

@[expose] def Uh : Subgroup Ah := listSub UL UL_check.1 UL_check.2.1

@[expose] def Alt1h : Subgroup Ah := listSub Alt1L Alt1_check.1 Alt1_check.2.1

theorem Kl1h_le_Uh : Kl1h ≤ Uh := by
  rintro a ⟨l, hl, hrep⟩
  exact ⟨l, (Kl1_check.2.2.2.2 l hl).1, hrep⟩

theorem Kl1h_le_Alt1h : Kl1h ≤ Alt1h := by
  rintro a ⟨l, hl, hrep⟩
  exact ⟨l, (Kl1_check.2.2.2.2 l hl).2.1, hrep⟩

theorem Uh_le_That : Uh ≤ That :=
  listSub_le_That fun l hl => (UL_check.2.2.2.2.1 l hl).1

theorem Kl1h_le_That : Kl1h ≤ That :=
  Kl1h_le_Uh.trans Uh_le_That

theorem Uh_comm_f {a : Ah} (ha : a ∈ Uh) : a * fhatA = fhatA * a := by
  obtain ⟨l, hl, hrep⟩ := ha
  exact eq_of_repL_eq (repL_mul hrep repL_fhat) (repL_mul repL_fhat hrep)
    (UL_check.2.2.2.2.1 l hl).2

theorem fhatA_not_mem_Uh : fhatA ∉ Uh := by
  rintro ⟨l, hl, hrep⟩
  have : l = fhatL := repL_unique hrep repL_fhat
  exact UL_check.2.2.2.2.2 (this ▸ hl)

theorem card_Uh : Nat.card ↥Uh = 8 := by
  unfold Uh
  rw [card_listSub UL_check.2.2.1 fun l hl => (UL_check.2.2.2.2.1 l hl).1]
  exact UL_check.2.2.2.1

theorem Dl1_complete :
    ∀ g ∈ P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah), ∃ l ∈ Dl1, RepL l (g : P45) :=
  rep_mem_D D1w Dl1 Dl1_eq (fun w hw => mem_P1h_of_repL (repL_aW w) (D1_check.2.2.1 w hw))
    D1_check.2.2.2 D1_check.1 card_C1 D1_check.2.1

theorem Alt1h_le_C1 : Alt1h ≤ P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah) := by
  rintro g ⟨l, hl, hrep⟩
  obtain ⟨w, hw, hwl⟩ := List.mem_map.1 (Dl1_eq ▸ Alt1_check.2.2.2.2 l hl)
  have hg : g = aW w := Subtype.ext (eq_of_repL hrep (hwl ▸ repL_aW w))
  rw [hg]
  refine ⟨mem_P1h_of_repL (repL_aW w) (D1_check.2.2.1 w hw), ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.2
    (comm_of_comp_comm (v := fhatA) repL_fhat (repL_aW w)
      (D1_check.2.2.2 _ (Dl1_eq ▸ List.mem_map.2 ⟨w, hw, rfl⟩)))

theorem repL_powL {σ : P45} {l : PL} (h : RepL l σ) (n : ℕ) : RepL (powL l n) (σ ^ n) := by
  induction n with
  | zero => exact repL_one 45
  | succ n ih =>
    rw [pow_succ']
    exact repL_mul h ih

theorem mem_Alt1h_of_odd {g : Ah}
    (hg : g ∈ P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) (hodd : Odd (orderOf g)) :
    g ∈ Alt1h := by
  obtain ⟨l, hl, hrep⟩ := Dl1_complete g hg
  have h12 : g ^ 12 = 1 := by
    apply Subtype.ext
    apply eq_of_repL (l := powL l 12) (repL_powL hrep 12)
    rw [Alt1_odd.1 l hl]
    exact repL_one 45
  have hd : orderOf g ∣ 12 := orderOf_dvd_of_pow_eq_one h12
  have h3 : orderOf g ∣ 3 := by
    have hc : Nat.Coprime (orderOf g) 4 := by
      simpa using (Odd.coprime_two_right hodd).pow_right 2
    exact hc.dvd_of_dvd_mul_right (by simpa using hd)
  have hg3 : g ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
  have h3' : ((g : P45) * ((g : P45) * (g : P45))) = 1 := by
    have := congrArg (fun x : Ah => (x : P45)) hg3
    simpa [pow_succ, mul_assoc] using this
  have hl3 : comp l (comp l l) = idL := by
    have h := repL_mul hrep (repL_mul hrep hrep)
    rw [h3'] at h
    exact repL_unique h (repL_one 45)
  exact ⟨l, Alt1_odd.2 l hl hl3, hrep⟩

end CFSG.Quasithin.H13.F431.U42Aut
