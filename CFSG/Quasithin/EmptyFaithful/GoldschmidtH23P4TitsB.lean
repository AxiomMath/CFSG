module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4TitsA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCore
public import CFSG.Sporadic.Schreier.TitsCentral

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat


theorem isSylowTwoOf_titsFlagStab : IsSylowTwoOf (titsFlagStab : Subgroup ↥titsD) ⊤ := by
  rw [isSylowTwoOf_top_iff]
  refine ⟨IsPGroup.of_card (n := 11) ?_, ?_⟩
  · rw [card_titsFlagStab]
    norm_num
  · rw [titsFlagStab_index]
    decide

theorem titsFlagStab_central {w : ↥titsD} (hw : w ∈ (titsFlagStab : Subgroup ↥titsD))
    (hc : ∀ s ∈ (titsFlagStab : Subgroup ↥titsD), s * w = w * s) :
    (w : Equiv.Perm (Fin 1755)) = 1 ∨ (w : Equiv.Perm (Fin 1755)) = titsZ := by
  have hwS : (w : Equiv.Perm (Fin 1755)) ∈ titsS := by
    rw [titsS_eq_stab]
    exact ⟨w, hw, rfl⟩
  have hcen : (⟨(w : Equiv.Perm (Fin 1755)), hwS⟩ : titsS) ∈ Subgroup.center titsS := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hs : (s : Equiv.Perm (Fin 1755)) ∈ titsFlagStab.map titsD.subtype := by
      rw [← titsS_eq_stab]
      exact s.2
    obtain ⟨p, hp, hps⟩ := hs
    apply Subtype.ext
    show (s : Equiv.Perm (Fin 1755)) * w = w * s
    rw [← hps]
    exact congrArg Subtype.val (hc p hp)
  have hmem : (w : Equiv.Perm (Fin 1755)) ∈
      ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) :=
    SetLike.mem_coe.2 (Subgroup.mem_map.2 ⟨_, hcen, rfl⟩)
  rw [titsS_center] at hmem
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

theorem titsPointStab_comm_central {z u : ↥titsD} (hz : z ∈ (titsFlagStab : Subgroup ↥titsD))
    (hzc : ∀ s ∈ (titsFlagStab : Subgroup ↥titsD), s * z = z * s)
    (hu : u ∈ (titsPointStab : Subgroup ↥titsD)) : u * z = z * u := by
  rcases titsFlagStab_central hz hzc with h1 | h1
  · have : z = 1 := Subtype.ext h1
    rw [this, mul_one, one_mul]
  · have hH : (u : Equiv.Perm (Fin 1755)) ∈ titsH := by
      rw [titsH_eq_stab]
      exact ⟨u, hu, rfl⟩
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hH)
    apply Subtype.ext
    show (u : Equiv.Perm (Fin 1755)) * z = z * u
    rw [h1]
    exact h2

theorem cenAt_titsFlagStab : CenAt (titsFlagStab : Subgroup ↥titsD) := by
  intro U hle b hb hidx z hz hzc u hu
  have h5 : 5 ≤ 5 ^ b := Nat.le_self_pow hb.ne' 5
  rcases tits_overgroups U hle with rfl | rfl | rfl | rfl
  · rw [Subgroup.relIndex_self] at hidx
    omega
  · exact titsPointStab_comm_central hz hzc hu
  · have h := Subgroup.relIndex_mul_card (H := titsFlagStab) (K := titsLineStab)
    rw [inf_eq_left.2 hle, card_titsFlagStab, card_titsLineStab] at h
    omega
  · rw [Subgroup.relIndex_top_right, titsFlagStab_index] at hidx
    have h3 : 3 ∣ 5 ^ b := hidx ▸ (by norm_num : 3 ∣ 8775)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem cenOvergroup_titsD : CenOvergroup ↥titsD :=
  cenOvergroup_of_cenAt isSylowTwoOf_titsFlagStab cenAt_titsFlagStab

end CFSG.Quasithin.H23P4
