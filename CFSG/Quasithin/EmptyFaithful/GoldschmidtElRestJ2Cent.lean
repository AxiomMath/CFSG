module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestCount
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestSyl
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.Quasithin.ModH

open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

theorem j2_exists_conj_permTwoA {z : Equiv.Perm (Fin 315)}
    (hz : z ∈ P) (hz2 : orderOf z = 2) (h128 : 128 ∣ Nat.card (centralizerIn P z)) :
    ∃ c ∈ P, z = c * permTwoA * c⁻¹ := by
  obtain ⟨-, -, -, -, -, hUn, -, -, -, -, -, -, hcover, -, hA, -, -, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, c, hc, hzc⟩ := hcover z (P_le_R hz) hz2
  have hcard : Nat.card (centralizerIn P z) = Nat.card (centralizerIn P r) := by
    have h := centralizerIn_conj P hc r
    rw [← hzc] at h
    rw [h, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [hcard, hA] at h128
    exact absurd h128 (by norm_num)
  · exact ⟨c, hc, hzc⟩
  · exfalso
    apply hUn
    have : permU = c⁻¹ * z * c := by rw [hzc]; group
    rw [this]
    exact P.mul_mem (P.mul_mem (P.inv_mem hc) hz) hc

theorem j2_card_centralizer_eq {z : Equiv.Perm (Fin 315)}
    (hz : z ∈ P) (hz2 : orderOf z = 2) (h128 : 128 ∣ Nat.card (centralizerIn P z)) :
    Nat.card (centralizerIn P z) = 1920 := by
  obtain ⟨c, hc, hzc⟩ := j2_exists_conj_permTwoA hz hz2 h128
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have h := centralizerIn_conj P hc permTwoA
  rw [← hzc] at h
  rw [h, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact hT

theorem j2_comm_sylow_mem {T : Subgroup (Equiv.Perm (Fin 315))}
    (hTP : T ≤ P) (hT : Nat.card T = 128) {g : Equiv.Perm (Fin 315)} (hgP : g ∈ P)
    (hg : ∀ t ∈ T, g * t = t * g) : g ∈ T := by
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 7) (by rw [hT]; norm_num)
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT
    exact absurd hT (by norm_num)
  obtain ⟨z, hzT, hz1, hz2, hzc⟩ := exists_central_involution hTp hT1
  have hzP : z ∈ P := hTP hzT
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hTle : T ≤ centralizerIn P z := fun t ht =>
    mem_centralizerIn.2 ⟨hTP ht, (hzc t ht).symm⟩
  have h128 : 128 ∣ Nat.card (centralizerIn P z) := hT ▸ Subgroup.card_dvd_of_le hTle
  have hC : Nat.card (centralizerIn P z) = 1920 := j2_card_centralizer_eq hzP hzo h128
  have hodd : CFSG.oddCore ↥(centralizerIn P z) = ⊥ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      z (P_le_R hzP) hzo
  have hT'c : Nat.card (T.subgroupOf (centralizerIn P z)) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv, hT]
  let g' : ↥(centralizerIn P z) := ⟨g, mem_centralizerIn.2 ⟨hgP, hg z hzT⟩⟩
  have hg' : ∀ t ∈ T.subgroupOf (centralizerIn P z), g' * t = t * g' := fun t ht =>
    Subtype.ext (hg t (Subgroup.mem_subgroupOf.1 ht))
  have hpg := isPGroup_of_comm_sylow hC (eq_bot_of_normal_odd hodd) hT'c hg'
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hpg
  rw [Nat.card_zpowers] at he
  have hgo : orderOf g = 2 ^ e := by
    rw [← he]
    exact Subgroup.orderOf_coe g'
  have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, hgo])
  have hnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 315))) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun h hh => (hg h hh).symm))
  have hK2 : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers g) := hTp.to_sup_of_normal_left' hgp hnorm
  have hKP : T ⊔ Subgroup.zpowers g ≤ P :=
    sup_le hTP (Subgroup.zpowers_le.2 hgP)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hK2
  have hdvdP : Nat.card ↥(T ⊔ Subgroup.zpowers g) ∣ Nat.card P := Subgroup.card_dvd_of_le hKP
  rw [hj, card_P, show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num] at hdvdP
  have hj7 : j ≤ 7 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
      ((Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 4725)).dvd_of_dvd_mul_right hdvdP)
  have hTK : 128 ∣ Nat.card ↥(T ⊔ Subgroup.zpowers g) :=
    hT ▸ Subgroup.card_dvd_of_le le_sup_left
  rw [hj, show (128 : ℕ) = 2 ^ 7 by norm_num] at hTK
  have hj7' : 7 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hTK
  have hKT : T = T ⊔ Subgroup.zpowers g :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hj, hT, show j = 7 by omega]; norm_num)
  rw [hKT]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

end CFSG.Quasithin.ModH
