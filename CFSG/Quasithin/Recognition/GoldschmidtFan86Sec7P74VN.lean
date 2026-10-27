module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Vgp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Fix

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem z_mem_ballStab (h71c : Fan71c F L) {α : V} (hα : valence Γ α = 5) {n : ℕ}
    (hn : n ≤ 4) : L.z α ∈ ballStab Γ G n α :=
  mem_ballStab.2 fun w hw => (h71c.z_smul_eq_iff hα w).2 (by omega)

theorem z_mem_zGroup (L : ZLab Γ G) {α : V} (hα : valence Γ α = 5) : L.z α ∈ L.zGroup 2 α :=
  Subgroup.subset_closure ⟨α, by simp, hα, rfl⟩

theorem z_P2_not_mem_ballStab (h71c : Fan71c F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    L.z (P.vert 2) ∈ L.zGroup 2 (P.vert 4) ∧ L.z (P.vert 2) ∉ ballStab Γ G 3 (P.vert 4) := by
  have h2 : valence Γ (P.vert 2) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  have d24 : Γ.dist (P.vert 4) (P.vert 2) = 2 := by
    rw [dist_comm]; have := dist_vert F P (i := 2) (j := 4) (by norm_num) (by norm_num); omega
  refine ⟨Subgroup.subset_closure ⟨P.vert 2, d24.le, h2, rfl⟩, fun hN => ?_⟩
  have d47 := dist_vert F P (i := 4) (j := 7) (by norm_num) (by norm_num)
  have d27 := dist_vert F P (i := 2) (j := 7) (by norm_num) (by norm_num)
  have h := mem_ballStab.1 hN (P.vert 7) (by omega)
  have := (h71c.z_smul_eq_iff h2 (P.vert 7)).1 h
  omega

theorem zGroup_inf_ballStab_three (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    L.zGroup 2 (P.vert 4) ⊓ ballStab Γ G 3 (P.vert 4) = Subgroup.zpowers (L.z (P.vert 4)) := by
  obtain ⟨α, hαdef⟩ : ∃ α, α = P.vert 4 := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x, x = xe L P := ⟨_, rfl⟩
  rw [← hαdef] at h5 ⊢
  have hx5 : x ^ 5 = 1 := by rw [hxdef]; exact xe_pow_five h71a (by rw [← hαdef]; exact h5)
  have hxmem : x ∈ MulAction.stabilizer G α := by
    rw [hxdef, hαdef]; exact xe_mem_stabilizer h71c (by rw [← hαdef]; exact h5)
  have hxα : x • α = α := MulAction.mem_stabilizer_iff.1 hxmem
  have hxz : x * L.z α = L.z α * x := L.comm_z_of_mem_stabilizer h5 hxmem
  have hcent : ∀ v ∈ L.zGroup 2 α, x * v = v * x → v = 1 ∨ v = L.z α := by
    intro v hv hc
    have := zGroup_inf_centralizer h40 h64 h71a h71c h72b (P := P) (by rw [← hαdef]; exact h5)
      (by rw [← hαdef]; exact hv) (by rw [← hxdef]; exact hc)
    rwa [← hαdef] at this
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G, U = L.zGroup 2 α ⊓ ballStab Γ G 3 α := ⟨_, rfl⟩
  rw [← hU]
  have hzU : L.z α ∈ U := by
    rw [hU]; exact ⟨z_mem_zGroup L h5, z_mem_ballStab h71c h5 (by norm_num)⟩
  have hz1 : L.z α ≠ 1 := L.z_ne_one h5
  have hVfin : Finite (L.zGroup 2 α) := by
    have : Nat.card (L.zGroup 2 α) ≠ 0 := by rw [h72b α h5]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have hUV : U ≤ L.zGroup 2 α := by rw [hU]; exact inf_le_left
  have hUfin : (U : Set G).Finite := by
    have : Finite U := Finite.of_injective (fun u : U => (⟨u.1, hUV u.2⟩ : L.zGroup 2 α))
      (fun a b h => Subtype.ext
        (show (a : G) = b from congrArg (fun m : L.zGroup 2 α => (m : G)) h))
    exact Set.toFinite _
  have hconj : ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro u hu
    rw [hU] at hu ⊢
    exact ⟨zGroup_conj F L hxα hu.1, ballStab_conj_stab F hxα hu.2⟩
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = (U : Set G) \ {1, L.z α} := ⟨_, rfl⟩
  have hmemS : ∀ s, s ∈ S ↔ s ∈ U ∧ s ≠ 1 ∧ s ≠ L.z α := by
    intro s
    rw [hS]
    simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hSclosed : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro s hs
    obtain ⟨hsU, hs1, hsz⟩ := (hmemS s).1 hs
    refine (hmemS _).2 ⟨hconj s hsU, fun h => hs1 ?_, fun h => hsz ?_⟩
    · have h' : x * s * x⁻¹ = x * 1 * x⁻¹ := by rw [h]; group
      exact mul_left_cancel (mul_right_cancel h')
    · have h' : x * s * x⁻¹ = x * L.z α * x⁻¹ := by rw [h, hxz]; group
      exact mul_left_cancel (mul_right_cancel h')
  have hnofix : ¬ ∃ s ∈ S, x * s * x⁻¹ = s := by
    rintro ⟨s, hs, hfix⟩
    obtain ⟨hsU, hs1, hsz⟩ := (hmemS s).1 hs
    have hc : x * s = s * x := by
      calc x * s = x * s * x⁻¹ * x := by group
        _ = s * x := by rw [hfix]
    rcases hcent s (hUV hsU) hc with h | h
    · exact hs1 h
    · exact hsz h
  have hdvd : 5 ∣ S.ncard := by
    by_contra hn
    refine hnofix (exists_fixed_of_not_dvd hx5 hSclosed ?_ hn)
    rw [hS]; exact hUfin.subset Set.sdiff_subset
  have hsub : ({1, L.z α} : Set G) ⊆ (U : Set G) := by
    intro g hg
    rcases hg with rfl | rfl
    · exact U.one_mem
    · exact hzU
  have hcard : (U : Set G).ncard = S.ncard + 2 := by
    have := Set.ncard_sdiff_add_ncard_of_subset hsub hUfin
    rw [Set.ncard_pair (Ne.symm hz1), ← hS] at this
    omega
  have hUc : Nat.card U = S.ncard + 2 := by
    rw [← hcard]; exact Nat.card_coe_set_eq (U : Set G)
  have hUV' : Nat.card U ∣ 2 ^ 5 := by
    rw [← h72b α h5]
    exact Subgroup.card_dvd_of_le hUV
  obtain ⟨m, hm, hmU⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hUV'
  have hcases : Nat.card U = 2 ∨ Nat.card U = 32 := by
    interval_cases m <;> omega
  have : Finite U := hUfin.to_subtype
  rcases hcases with h2 | h32
  · have hle : Subgroup.zpowers (L.z α) ≤ U := (Subgroup.zpowers_le).2 hzU
    have hzc : Nat.card (Subgroup.zpowers (L.z α)) = 2 := by
      rw [Nat.card_zpowers]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by simpa [pow_two] using L.z_mul_self h5) hz1
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  · exfalso
    have hUeq : U = L.zGroup 2 α := Subgroup.eq_of_le_of_card_ge hUV (by rw [h72b α h5]; omega)
    obtain ⟨hzV, hzN⟩ := z_P2_not_mem_ballStab (G := G) h71c (P := P) (by rw [← hαdef]; exact h5)
    have hzU2 : L.z (P.vert 2) ∈ U := by rw [hUeq, hαdef]; exact hzV
    have hzN2 : L.z (P.vert 2) ∈ ballStab Γ G 3 α := by rw [hU] at hzU2; exact hzU2.2
    rw [hαdef] at hzN2
    exact hzN hzN2

end P74

end CFSG.Quasithin.Fan86
