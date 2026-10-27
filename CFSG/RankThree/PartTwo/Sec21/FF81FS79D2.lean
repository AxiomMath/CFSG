module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Ctl34
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R34K

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]

namespace Ctl34

theorem mem_zpowers_conj_iff {β g y : H} :
    y ∈ Subgroup.zpowers (g * β * g⁻¹) ↔ g⁻¹ * y * g ∈ Subgroup.zpowers β := by
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk, conj_zpow]
    group
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group

theorem mem_Nor_conj_iff {β g x : H} :
    x ∈ Nor (Subgroup.zpowers (g * β * g⁻¹)) ↔ g⁻¹ * x * g ∈ Nor (Subgroup.zpowers β) := by
  constructor
  · intro hx
    refine mem_Nor_zpowers_of_conj ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hx (g * β * g⁻¹)).mp (Subgroup.mem_zpowers _)
    rw [mem_zpowers_conj_iff] at h1
    have e : g⁻¹ * (x * (g * β * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * β * (g⁻¹ * x * g)⁻¹ := by
      group
    rwa [e] at h1
  · intro hx
    refine mem_Nor_zpowers_of_conj ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hx β).mp (Subgroup.mem_zpowers _)
    rw [mem_zpowers_conj_iff]
    have e : g⁻¹ * (x * (g * β * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * β * (g⁻¹ * x * g)⁻¹ := by
      group
    rwa [e]

theorem conjBy_Nor_zpowers' (g β : H) :
    conjBy g (Nor (Subgroup.zpowers β)) = Nor (Subgroup.zpowers (g * β * g⁻¹)) := by
  ext x
  rw [mem_Nor_conj_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem ctlEq_conj {b β g : H} (hg : g * b = b * g) (h : CtlEq b β) :
    CtlEq b (g * β * g⁻¹) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold CtlEq at h ⊢
  have hN := conjBy_Nor_zpowers' g β
  have hgN : g ∈ Nor (Subgroup.zpowers b) := mem_Nor_zpowers_of_comm hg
  have hO : conjBy g (Opp 3 (Nor (Subgroup.zpowers β))) =
      Opp 3 (Nor (Subgroup.zpowers (g * β * g⁻¹))) := by rw [L14.conjBy_Opp, hN]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨o, ho, m, hm, rfl⟩
    exact (Nor _).mul_mem (L14.Opp_le 3 _ ho) hm.2
  · intro x hx
    rw [← hN] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ setMul (Opp 3 (Nor (Subgroup.zpowers β)))
        (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers β)) := by
      rw [h]
      exact hy
    obtain ⟨o, ho, m, hm, rfl⟩ := hy'
    refine ⟨g * o * g⁻¹, ?_, g * m * g⁻¹, ⟨?_, ?_⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · rw [← hO]
      exact ⟨o, ho, by simp [MulAut.conj_apply]⟩
    · exact (Nor _).mul_mem ((Nor _).mul_mem hgN hm.1) ((Nor _).inv_mem hgN)
    · rw [← hN]
      exact ⟨m, hm.2, by simp [MulAut.conj_apply]⟩

end Ctl34

namespace J6

def rev : S6 := swap 0 5 * swap 1 4 * swap 2 3

theorem rev_sq : rev * rev = 1 := by decide +kernel

theorem rev_d_conj : rev * d * rev⁻¹ = d⁻¹ := by decide +kernel

theorem D6_comm_rev : ∀ σ ∈ D6fin, σ * rev = rev * σ := by decide +kernel

theorem cen_d_decomp : ∀ σ : S6, σ * d * σ⁻¹ = d →
    ∃ i : Fin 3, ∃ s ∈ D6fin, σ = d ^ i.val * s := by decide +kernel

theorem inv_d_decomp : ∀ σ : S6, σ * d * σ⁻¹ = d⁻¹ →
    ∃ i : Fin 3, ∃ s ∈ D6fin, σ = d ^ i.val * rev * s := by decide +kernel

theorem fus_d'_d : ∀ σ : S6, (σ * d' * σ⁻¹ = d' ∨ σ * d' * σ⁻¹ = d'⁻¹) →
    σ * d * σ⁻¹ ∈ Efin := by decide +kernel

theorem a45_d_conj : swap 4 5 * d * (swap 4 5)⁻¹ = d' := by decide +kernel

end J6

variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

theorem frame_D2 (hctl : CtlEq b (b₁ * b₂⁻¹)) :
    Ctl34.Frame b b₁ b₂ J (b₁ * b₂) (S.ι J6.rev) (b₁ * b₂⁻¹) S.Dsub where
  w_mem := S.d_mem_B₁
  w_ne := S.d_ne_one
  w3 := S.beta_pow_three
  c_mem := Subgroup.mul_mem _ S.b₁_mem_B₁ (Subgroup.inv_mem _ S.b₂_mem_B₁)
  c_ne := S.c_ne_one
  c3 := S.c_pow_three
  B₁_le := by
    rw [← S.zpowers_c_sup_Z, sup_comm]
  τ_mem := S.ι_mem _
  τ2 := by rw [← map_mul, J6.rev_sq, map_one]
  τ_inv := by
    have := S.ι_conj J6.rev J6.d
    rw [J6.rev_d_conj, map_inv, S.ι_dd] at this
    exact this.symm
  J'_le := S.Dsub_le_J
  J'_iso := S.Dsub_iso
  c_mem_J' := S.c_mem_Dsub
  J'_comm_w := fun j hj => S.Dsub_comm_beta hj
  J'_comm_τ := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_mul, ← map_mul, J6.D6_comm_rev σ hσ]
  decomp1 := by
    intro j₀ hj₀ hc
    obtain ⟨σ, rfl⟩ := S.exists_ι hj₀
    have hσ : σ * J6.d * σ⁻¹ = J6.d := by
      apply S.ι_injective
      rw [S.ι_conj, S.ι_dd]
      exact hc
    obtain ⟨i, s, hs, rfl⟩ := J6.cen_d_decomp σ hσ
    refine ⟨(i.val : ℤ), S.ι s, ⟨s, hs, rfl⟩, ?_⟩
    rw [map_mul, map_pow, S.ι_dd, zpow_natCast]
  decomp2 := by
    intro j₀ hj₀ hc
    obtain ⟨σ, rfl⟩ := S.exists_ι hj₀
    have hσ : σ * J6.d * σ⁻¹ = J6.d⁻¹ := by
      apply S.ι_injective
      rw [S.ι_conj, map_inv, S.ι_dd]
      exact hc
    obtain ⟨i, s, hs, rfl⟩ := J6.inv_d_decomp σ hσ
    refine ⟨(i.val : ℤ), S.ι s, ⟨s, hs, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_pow, S.ι_dd, zpow_natCast]
  fusion_c := by
    intro j₁ hj₁ hmem
    obtain ⟨σ, rfl⟩ := S.exists_ι hj₁
    have hσ : σ * J6.d' * σ⁻¹ = J6.d' ∨ σ * J6.d' * σ⁻¹ = J6.d'⁻¹ := by
      have h1 : S.ι (σ * J6.d' * σ⁻¹) ∈ Subgroup.zpowers (S.ι J6.d') := by
        rw [S.ι_conj, S.ι_dp]
        exact hmem
      rcases S.mem_zpowers_ι J6.d'_pow_three h1 with h2 | h2 | h2
      · exfalso
        apply J6.d'_ne_one
        calc J6.d' = σ⁻¹ * (σ * J6.d' * σ⁻¹) * σ := by group
          _ = 1 := by rw [h2]; group
      · exact Or.inl h2
      · exact Or.inr h2
    have hE := J6.fus_d'_d σ hσ
    have e : S.ι σ * (b₁ * b₂) * (S.ι σ)⁻¹ = S.ι (σ * J6.d * σ⁻¹) := by
      rw [S.ι_conj, S.ι_dd]
    rw [e]
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hE
    rw [← hp, map_mul, map_pow, map_pow, S.ι_c₁, S.ι_c₂]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ S.b₁_mem_B₁ _) (Subgroup.pow_mem _ S.b₂_mem_B₁ _)
  ctl_c := hctl

theorem ctlEq_c (h34 : R34Stmt b b₁ b₂) : CtlEq b (b₁ * b₂⁻¹) := by
  have hg : S.ι (swap 4 5) * b = b * S.ι (swap 4 5) := S.ι_comm_b _
  have h1 := Ctl34.ctlEq_conj hg h34
  have e : S.ι (swap 4 5) * (b₁ * b₂) * (S.ι (swap 4 5))⁻¹ = b₁ * b₂⁻¹ := by
    have := S.ι_conj (swap 4 5) J6.d
    rw [J6.a45_d_conj, S.ι_dp, S.ι_dd] at this
    exact this.symm
  rwa [e] at h1

end Std

theorem fs79D2K_of (hR1K : KF_FS79Prop2OneK) : FS79D2K := by
  intro H _ _ hK b t b₁ b₂ J hH
  have h34 : R34Stmt b b₁ b₂ := fs79R34K_of hR1K H hK b t b₁ b₂ J hH
  exact (hH.std.frame_D2 (hH.std.ctlEq_c h34)).ctlEq hH hR1K hK

end CFSG.RankThree.PartTwo.Sec21.FF81
