module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Syl
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Frm

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace J6

theorem e1_mem_T1 : e1 ∈ T1 := (by decide +kernel : e1 ∈ T1fin)

theorem y_mem_V1 : e1 * pp * qq ∈ V1 := (by decide +kernel : e1 * pp * qq ∈ V1fin)

theorem e1_sq : e1 * e1 = 1 := by decide +kernel

theorem e1_ne_one : e1 ≠ 1 := by decide +kernel

theorem e1_comm_c2 : e1 * c₂ = c₂ * e1 := by decide +kernel

theorem y_sq : (e1 * pp * qq) * (e1 * pp * qq) = 1 := by decide +kernel

theorem y_ne_one : e1 * pp * qq ≠ 1 := by decide +kernel

theorem y_comm_c0 : (e1 * pp * qq) * c0 = c0 * (e1 * pp * qq) := by decide +kernel

theorem c0_pow_three : c0 ^ 3 = 1 := by decide +kernel

theorem c0_ne_one : c0 ≠ 1 := by decide +kernel

theorem d_not_orbitB : ∀ x ∈ orbitB, x ≠ c₁ * c₂ ∧ x ≠ (c₁ * c₂)⁻¹ := by decide +kernel

end J6

namespace Std

variable (S : Std b t b₁ b₂ J)

theorem kdata_T : S.KData J6.T1 J6.c₂ J6.e1 where
  sqA := fun s hs => J6.T1fin_sq s hs
  commA := fun a ha c hc => J6.T1fin_comm a ha c hc
  normA := fun s hs => J6.c2_norm_T1 s hs
  x3 := J6.c₂_pow_three
  x1 := J6.c₂_ne_one
  cen := fun s hs h => J6.T1_cen_c2 s hs h
  e_mem := J6.e1_mem_T1
  e_sq := J6.e1_sq
  e_ne := J6.e1_ne_one
  e_comm := J6.e1_comm_c2
  Na := S.nf_t_cl1 J6.cl1_e1
  Nb := S.nf_t_tcl1 J6.cl1_e1
  Nc := fun hc => S.nf_tcl1_cl1 J6.cl1_e1 J6.cl1_e1 hc.symm
  Nd := fun r hr => S.nf_cen_cl1 hr J6.cl1_e1

theorem kdata_V (h34 : R34Stmt b b₁ b₂) : S.KData J6.V1 J6.c0 (J6.e1 * J6.pp * J6.qq) where
  sqA := fun s hs => J6.V1fin_sq s hs
  commA := fun a ha c hc => J6.V1fin_comm a ha c hc
  normA := fun s hs => J6.c0_norm_V1 s hs
  x3 := J6.c0_pow_three
  x1 := J6.c0_ne_one
  cen := fun s hs h => J6.V1_cen_c0 s hs h
  e_mem := J6.y_mem_V1
  e_sq := J6.y_sq
  e_ne := J6.y_ne_one
  e_comm := J6.y_comm_c0
  Na := S.nf_t_cl3 J6.cl3_y
  Nb := S.nf_t_tcl3 h34 J6.cl3_y
  Nc := fun hc => S.nf_tcl3_cl3 h34 J6.cl3_y J6.cl3_y hc.symm
  Nd := fun r hr => S.nf_cen_cl3 hr J6.cl3_y


end Std

theorem conj_hom_apply (g x : H) : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by
  simp [MulAut.conj_apply]

theorem abgSylow_to_ff79 {G : Type} [Group G] [Finite G] {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 3 P K) : IsSylowOf 3 P K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h
  exact ⟨hle, hp, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hdvd⟩

namespace J6

theorem d_mem_Efin : c₁ * c₂ ∈ Efin := by decide +kernel

theorem conj_c0_d_inv : ∀ γ : S6, γ * c0 * γ⁻¹ = c₁ * c₂ → γ * c0⁻¹ * γ⁻¹ = (c₁ * c₂)⁻¹ := by
  intro γ h
  rw [← h]
  group

end J6

namespace Std

variable (S : Std b t b₁ b₂ J)

theorem not_conj_TV (h34 : R34Stmt b b₁ b₂) (g : H) :
    conjBy g (S.frame J6.T1) ≠ S.frame J6.V1 := by
  intro hg
  have hT := (S.kdata_T).isSylowOf
  have hV := abgSylow_to_ff79 (S.kdata_V h34).isSylowOf
  set w : H := g * S.ι J6.c₂ * g⁻¹ with hw
  have hwN : w ∈ Nor (S.frame J6.V1) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [← hg] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hce : (MulAut.conj g).toMonoidHom y₀ = g * y₀ * g⁻¹ := conj_hom_apply g y₀
    have h1 : S.ι J6.c₂ * y₀ * (S.ι J6.c₂)⁻¹ ∈ S.frame J6.T1 :=
      (Subgroup.mem_normalizer_iff.mp (S.kdata_T).ιx_mem_Nor y₀).mp hy₀
    have hmem : (MulAut.conj g).toMonoidHom (S.ι J6.c₂ * y₀ * (S.ι J6.c₂)⁻¹) ∈
        S.frame J6.V1 := by
      rw [← hg]
      exact ⟨_, h1, rfl⟩
    have e1 : w * ((MulAut.conj g).toMonoidHom y₀) * w⁻¹ =
        (MulAut.conj g).toMonoidHom (S.ι J6.c₂ * y₀ * (S.ι J6.c₂)⁻¹) := by
      rw [conj_hom_apply g (S.ι J6.c₂ * y₀ * (S.ι J6.c₂)⁻¹), hce, hw]
      group
    rw [e1]
    exact hmem
  have hw3 : w ^ 3 = 1 := by
    have h1 : S.ι J6.c₂ ^ 3 = 1 := by rw [← map_pow, J6.c₂_pow_three, map_one]
    have h2 : w ^ 3 = g * S.ι J6.c₂ ^ 3 * g⁻¹ := by
      have := map_pow (MulAut.conj g) (S.ι J6.c₂) 3
      simpa [MulAut.conj_apply, hw] using this
    rw [h2, h1]
    group
  have hXp : IsPGroup 3 (Subgroup.zpowers w) := isPGroup_zpowers_of_pow_three hw3
  obtain ⟨n, -, hn⟩ := L14.exists_conj_le_sylowOf hV
    (Subgroup.zpowers_le.mpr hwN) hXp
  have hnw : n * w * n⁻¹ ∈ Subgroup.zpowers (S.ι J6.c0) := hn w (Subgroup.mem_zpowers w)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnw
  rw [← map_zpow] at hk
  have hb₂ne : S.ι J6.c₂ ≠ 1 := fun h1 =>
    J6.c₂_ne_one (S.ι_injective (h1.trans (map_one S.ι).symm))
  have hconj : (n * g) * S.ι J6.c₂ * (n * g)⁻¹ = S.ι (J6.c0 ^ k) := by
    rw [hk, hw]
    group
  obtain ⟨γ, hγ⟩ := J6.conj_c0_d
  have hcases := zpow_three_cases J6.c0_pow_three k
  have hB : ∃ x₀ : J6.S6, (x₀ = J6.c₁ * J6.c₂ ∨ x₀ = (J6.c₁ * J6.c₂)⁻¹) ∧
      ∃ g'' : H, g'' * S.ι J6.c₂ * g''⁻¹ = S.ι x₀ := by
    rcases hcases with h1 | h1 | h1
    · exfalso
      rw [h1, map_one] at hconj
      apply hb₂ne
      calc S.ι J6.c₂ = (n * g)⁻¹ * ((n * g) * S.ι J6.c₂ * (n * g)⁻¹) * (n * g) := by group
        _ = 1 := by rw [hconj]; group
    · rw [h1] at hconj
      refine ⟨J6.c₁ * J6.c₂, Or.inl rfl, (S.ι γ) * (n * g), ?_⟩
      have h2 := (S.ι_conj γ J6.c0)
      rw [hγ] at h2
      calc S.ι γ * (n * g) * S.ι J6.c₂ * (S.ι γ * (n * g))⁻¹
          = S.ι γ * ((n * g) * S.ι J6.c₂ * (n * g)⁻¹) * (S.ι γ)⁻¹ := by group
        _ = S.ι γ * S.ι J6.c0 * (S.ι γ)⁻¹ := by rw [hconj]
        _ = S.ι (J6.c₁ * J6.c₂) := h2.symm
    · rw [h1] at hconj
      refine ⟨(J6.c₁ * J6.c₂)⁻¹, Or.inr rfl, (S.ι γ) * (n * g), ?_⟩
      have h2 := (S.ι_conj γ J6.c0⁻¹)
      rw [J6.conj_c0_d_inv γ hγ] at h2
      calc S.ι γ * (n * g) * S.ι J6.c₂ * (S.ι γ * (n * g))⁻¹
          = S.ι γ * ((n * g) * S.ι J6.c₂ * (n * g)⁻¹) * (S.ι γ)⁻¹ := by group
        _ = S.ι γ * S.ι J6.c0⁻¹ * (S.ι γ)⁻¹ := by rw [hconj]
        _ = S.ι (J6.c₁ * J6.c₂)⁻¹ := h2.symm
  obtain ⟨x₀, hx₀, g'', hg''⟩ := hB
  have hx₀E : x₀ ∈ J6.Efin := by
    rcases hx₀ with rfl | rfl
    · exact J6.d_mem_Efin
    · exact J6.Efin_inv _ J6.d_mem_Efin
  have hx₀B : S.ι x₀ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ ((S.mem_B₁_iff _).mpr ⟨x₀, hx₀E, rfl⟩)
  have he : g'' * b₂ * g''⁻¹ = S.ι x₀ := by
    calc g'' * b₂ * g''⁻¹ = g'' * S.ι J6.c₂ * g''⁻¹ := by rw [S.ι_c₂]
      _ = S.ι x₀ := hg''
  have hfus : g'' * b₂ * g''⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H) :=
    S.hyp.fusion_b₂ (by rw [he]; exact hx₀B)
  rw [he] at hfus
  have hx₀orb : x₀ ∈ J6.orbitB := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfus
    unfold J6.orbitB
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hfus with h1 | h1 | h1 | h1
    · left
      exact S.ι_injective (h1.trans S.ι_c₁.symm)
    · right; left
      apply S.ι_injective
      rw [map_inv, S.ι_c₁]
      exact h1
    · right; right; left
      exact S.ι_injective (h1.trans S.ι_c₂.symm)
    · right; right; right
      apply S.ι_injective
      rw [map_inv, S.ι_c₂]
      exact h1
  rcases hx₀ with rfl | rfl
  · exact (J6.d_not_orbitB _ hx₀orb).1 rfl
  · exact (J6.d_not_orbitB _ hx₀orb).2 rfl

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
