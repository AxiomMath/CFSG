module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Ctl34
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R34

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace J6

def S345fin : Finset S6 := Finset.univ.filter fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2

theorem S345fin_card : S345fin.card = 6 := by decide +kernel

theorem S345fin_mul : ∀ a ∈ S345fin, ∀ b ∈ S345fin, a * b ∈ S345fin := by decide +kernel

theorem S345fin_inv : ∀ a ∈ S345fin, a⁻¹ ∈ S345fin := by decide +kernel

theorem one_mem_S345fin : (1 : S6) ∈ S345fin := by decide +kernel

def S345 : Subgroup S6 where
  carrier := {σ | σ ∈ S345fin}
  mul_mem' := fun {a b} ha hb => S345fin_mul a ha b hb
  one_mem' := one_mem_S345fin
  inv_mem' := fun {a} ha => S345fin_inv a ha

theorem card_S345 : Nat.card S345 = 6 := by
  rw [card_of_finset S345fin S345 (fun σ => Iff.rfl), S345fin_card]

theorem c₂_mem_S345 : c₂ ∈ S345 := (by decide +kernel : c₂ ∈ S345fin)

theorem a2_mem_S345 : a2 ∈ S345 := (by decide +kernel : a2 ∈ S345fin)

theorem a2_c₂_conj : a2 * c₂ * a2⁻¹ = c₂⁻¹ := by decide +kernel

theorem S345_iso : Nonempty (↥S345 ≃* Perm (Fin 3)) := by
  refine CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three
    (⟨c₂, c₂_mem_S345⟩ : ↥S345) (⟨a2, a2_mem_S345⟩ : ↥S345) ?_ ?_ ?_ ?_ ?_ card_S345
  · exact Subtype.ext c₂_pow_three
  · intro h
    exact c₂_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext a2_sq
  · intro h
    exact a2_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext a2_c₂_conj

theorem e1_sq' : e1 * e1 = 1 := by decide +kernel

theorem e1_c₁_conj : e1 * c₁ * e1⁻¹ = c₁⁻¹ := by decide +kernel

theorem S345_comm_c₁ : ∀ σ ∈ S345fin, σ * c₁ = c₁ * σ := by decide +kernel

theorem S345_comm_e1 : ∀ σ ∈ S345fin, σ * e1 = e1 * σ := by decide +kernel

theorem cen_c₁_decomp : ∀ σ : S6, σ * c₁ * σ⁻¹ = c₁ →
    ∃ i : Fin 3, ∃ s ∈ S345fin, σ = c₁ ^ i.val * s := by decide +kernel

theorem inv_c₁_decomp : ∀ σ : S6, σ * c₁ * σ⁻¹ = c₁⁻¹ →
    ∃ i : Fin 3, ∃ s ∈ S345fin, σ = c₁ ^ i.val * e1 * s := by decide +kernel

theorem fus_c₂_c₁ : ∀ σ : S6, (σ * c₂ * σ⁻¹ = c₂ ∨ σ * c₂ * σ⁻¹ = c₂⁻¹) →
    σ * c₁ * σ⁻¹ ∈ Efin := by decide +kernel

end J6

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

noncomputable def S345sub : Subgroup H := J6.S345.map S.ι

theorem S345sub_le_J : S.S345sub ≤ J := by
  rintro _ ⟨σ, -, rfl⟩
  exact S.ι_mem σ

theorem S345sub_iso : Nonempty (↥S.S345sub ≃* Perm (Fin 3)) := by
  obtain ⟨e⟩ := J6.S345_iso
  exact ⟨(Subgroup.equivMapOfInjective J6.S345 S.ι S.ι_injective).symm.trans e⟩

theorem frame_D1 (hctl : CtlEq b b₂) :
    Ctl34.Frame b b₁ b₂ J b₁ (S.ι J6.e1) b₂ S.S345sub where
  w_mem := S.b₁_mem_B₁
  w_ne := S.b₁_ne_one
  w3 := S.b₁_pow_three
  c_mem := S.b₂_mem_B₁
  c_ne := S.b₂_ne_one
  c3 := S.b₂_pow_three
  B₁_le := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  τ_mem := S.ι_mem _
  τ2 := by rw [← map_mul, J6.e1_sq', map_one]
  τ_inv := by
    have := S.ι_conj J6.e1 J6.c₁
    rw [J6.e1_c₁_conj, map_inv, S.ι_c₁] at this
    exact this.symm
  J'_le := S.S345sub_le_J
  J'_iso := S.S345sub_iso
  c_mem_J' := ⟨J6.c₂, J6.c₂_mem_S345, S.ι_c₂⟩
  J'_comm_w := by
    rintro _ ⟨σ, hσ, rfl⟩
    have h1 : S.ι (σ * J6.c₁) = S.ι (J6.c₁ * σ) := by rw [J6.S345_comm_c₁ σ hσ]
    rwa [map_mul, map_mul, S.ι_c₁] at h1
  J'_comm_τ := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_mul, ← map_mul, J6.S345_comm_e1 σ hσ]
  decomp1 := by
    intro j₀ hj₀ hc
    obtain ⟨σ, rfl⟩ := S.exists_ι hj₀
    have hσ : σ * J6.c₁ * σ⁻¹ = J6.c₁ := by
      apply S.ι_injective
      rw [S.ι_conj, S.ι_c₁]
      exact hc
    obtain ⟨i, s, hs, rfl⟩ := J6.cen_c₁_decomp σ hσ
    refine ⟨(i.val : ℤ), S.ι s, ⟨s, hs, rfl⟩, ?_⟩
    rw [map_mul, map_pow, S.ι_c₁, zpow_natCast]
  decomp2 := by
    intro j₀ hj₀ hc
    obtain ⟨σ, rfl⟩ := S.exists_ι hj₀
    have hσ : σ * J6.c₁ * σ⁻¹ = J6.c₁⁻¹ := by
      apply S.ι_injective
      rw [S.ι_conj, map_inv, S.ι_c₁]
      exact hc
    obtain ⟨i, s, hs, rfl⟩ := J6.inv_c₁_decomp σ hσ
    refine ⟨(i.val : ℤ), S.ι s, ⟨s, hs, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_pow, S.ι_c₁, zpow_natCast]
  fusion_c := by
    intro j₁ hj₁ hmem
    obtain ⟨σ, rfl⟩ := S.exists_ι hj₁
    have hσ : σ * J6.c₂ * σ⁻¹ = J6.c₂ ∨ σ * J6.c₂ * σ⁻¹ = J6.c₂⁻¹ := by
      have h1 : S.ι (σ * J6.c₂ * σ⁻¹) ∈ Subgroup.zpowers (S.ι J6.c₂) := by
        rw [S.ι_conj, S.ι_c₂]
        exact hmem
      rcases S.mem_zpowers_ι J6.c₂_pow_three h1 with h2 | h2 | h2
      · exfalso
        apply J6.c₂_ne_one
        calc J6.c₂ = σ⁻¹ * (σ * J6.c₂ * σ⁻¹) * σ := by group
          _ = 1 := by rw [h2]; group
      · exact Or.inl h2
      · exact Or.inr h2
    have hE := J6.fus_c₂_c₁ σ hσ
    have e : S.ι σ * b₁ * (S.ι σ)⁻¹ = S.ι (σ * J6.c₁ * σ⁻¹) := by rw [S.ι_conj, S.ι_c₁]
    rw [e]
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hE
    rw [← hp, map_mul, map_pow, map_pow, S.ι_c₁, S.ι_c₂]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ S.b₁_mem_B₁ _) (Subgroup.pow_mem _ S.b₂_mem_B₁ _)
  ctl_c := hctl

end Std

theorem fs79D1K_of (hR1K : KF_FS79Prop2OneK) : FS79D1K := by
  intro H _ _ hK b t b₁ b₂ J hH
  exact (hH.std.frame_D1 (hH.N_bi b₂ (Set.mem_insert_of_mem _ rfl))).ctlEq hH hR1K hK

end CFSG.RankThree.PartTwo.Sec21.FF81
