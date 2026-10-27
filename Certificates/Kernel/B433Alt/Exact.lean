module

public import Certificates.Kernel.B433Alt.CoverB
public import CFSG.Certificates.Kernel.B433Alt.Exact

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CFSG.YGroups.DCE.B433 CFSG.Certificates.TwDce

@[expose] noncomputable def Ev : Finset (Fin 46) :=
  Finset.univ.filter fun i => CFSG.KD.B4AT.PA.getD (nodeAt i) 0 = 0

@[expose] noncomputable def vN (i : Fin 46) : ℕ := 4089470473293004800 / CFSG.KD.B4AC.MJ (nodeAt i)

theorem pa_le : ∀ j < 64, CFSG.KD.B4AT.PA.getD j 0 ≤ 1 := by decide +kernel

theorem sum_Ev : ∑ i ∈ Ev, vN i = 1015970529280000 := by decide +kernel

theorem mj_zero : CFSG.KD.B4AC.MJ 0 = 4089470473293004800 := by decide +kernel

theorem idx0_mem : idxOf 0 ∈ Ev := by decide +kernel

theorem vN_idx0 : vN (idxOf 0) = 1 := by decide +kernel

section

noncomputable abbrev inlB : B433 →* Ghat hsw := SemidirectProduct.inl

theorem inlB_injective : Function.Injective (inlB : B433 →* Ghat hsw) :=
  SemidirectProduct.inl_injective

theorem paE_eq_one_iff {j : ℕ} (hj : j < 64) : paE j = 1 ↔ CFSG.KD.B4AT.PA.getD j 0 = 0 := by
  have h := pa_le j hj
  rw [paE]
  interval_cases h' : CFSG.KD.B4AT.PA.getD j 0
  · simp
  · exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 (by norm_num)⟩

theorem x_mem_inl_iff (i : Fin 46) : (twist).x i ∈ (inlB : B433 →* Ghat hsw).range ↔ i ∈ Ev := by
  have hmem := nodeAt_mem i
  obtain ⟨hj, hlv⟩ := (liveL_spec _).1 hmem
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  change eps (Xn (nodeAt i)) = 1 ↔ _
  rw [eps_Xn _ hj (live_tree _ hj hlv), paE_eq_one_iff hj, Ev, Finset.mem_filter]
  simp

theorem relIndex_le_v (i : Fin 46) : ((twist).S i).relIndex (Hh hsw) ≤ vN i := by
  have hmem := nodeAt_mem i
  obtain ⟨hj, hl⟩ := (liveL_spec _).1 hmem
  obtain ⟨hm0, -⟩ := data_ok.2.1 _ hj hl
  exact relIndex_le _ hm0 (node_card hj hl)

theorem card_Hh_le : Nat.card (Hh hsw) ≤ 4089470473293004800 := by
  rw [card_Hh]
  exact card_range_psi_le

theorem finite_Ghat : Finite (Ghat hsw) := by
  have := (B433_finite_card_le).1
  exact Finite.of_equiv _ (SemidirectProduct.equivProd (φ := act hsw)).symm

theorem exact (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    (∀ i ∈ Ev, ∀ j ∈ Ev, (∃ a ∈ Hh hsw, ∃ b ∈ Hh hsw, (twist).x j = a * (twist).x i * b) → i = j) ∧
    Nat.card (Hh hsw) = 4089470473293004800 ∧
    ∀ i ∈ Ev, ∀ S' : Subgroup (Ghat hsw), (∀ s ∈ S', (twist).x i * s * ((twist).x i)⁻¹ ∈ Hh hsw) →
      vN i ≤ S'.relIndex (Hh hsw) := by
  classical
  have := finite_Ghat
  have := Fintype.ofFinite (Ghat hsw)
  have htot : 4089470473293004800 * ∑ i ∈ Ev, vN i ≤ Nat.card (inlB : B433 →* Ghat hsw).range := by
    rw [sum_Ev, MonoidHom.range_eq_map, Subgroup.card_map_of_injective inlB_injective,
      Subgroup.card_top]
    calc 4089470473293004800 * 1015970529280000 = 4154781481226426191177580544000000 := by norm_num
      _ ≤ Nat.card B433 := hG
  have hHK : Hh hsw ≤ (inlB : B433 →* Ghat hsw).range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨psi y, rfl⟩
  obtain ⟨h1, h2, h3⟩ := exact_of_cover (Hh hsw) (inlB : B433 →* Ghat hsw).range (twist).S
    (twist).x vN Ev (twist).S_conj
    ((twist).exists_eq (u_mul_self hsw) (u_conj_Th hsw) (closure_Hh_u hsw))
    relIndex_le_v x_mem_inl_iff hHK _ card_Hh_le htot
  refine ⟨h2, le_antisymm card_Hh_le ?_, fun i hi S' hS' => ?_⟩
  · rw [sum_Ev] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)
  · have hdc := card_dc_le (Hh hsw) S' ((twist).x i) hS'
    rw [h1 i hi] at hdc
    exact Nat.le_of_mul_le_mul_left hdc Nat.card_pos

theorem card_psi_range (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    Nat.card psi.range = 4089470473293004800 := by
  rw [← card_Hh hsw]
  exact (exact hG).2.1

theorem ker_psi (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    psi.ker = rho432F.ker := by
  have := finite_y432
  symm
  refine Subgroup.eq_of_le_of_card_ge ker_rho432F_le_ker_psi ?_
  have h1 := Subgroup.card_ker_mul_card_range psi
  have h2 := Subgroup.card_ker_mul_card_range rho432F
  rw [card_psi_range hG] at h1
  rw [card_range_rho432F] at h2
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans h2.symm)).le

theorem relIndex_eq (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) {i : Fin 46}
    (hi : i ∈ Ev) : ((twist).S i).relIndex (Hh hsw) = vN i :=
  le_antisymm (relIndex_le_v i) ((exact hG).2.2 i hi _ ((twist).S_conj i))

end

end CertificateChecks.KernelB433

end
