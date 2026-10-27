module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79QuoK
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R34

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

theorem r34_of_conclusion
    (hcon : ∃ O : Subgroup H, Subgroup.zpowers (b₁ * b₂) ≤ O ∧ O ≤ Cen (b₁ * b₂) ∧
      (∀ g ∈ Cen (b₁ * b₂), ∀ o ∈ O, g * o * g⁻¹ ∈ O) ∧
      (∀ o ∈ O, ∃ m : ℕ, Nat.Coprime 6 m ∧ o ^ m ∈ Subgroup.zpowers (b₁ * b₂)) ∧
      ∀ g ∈ Cen (b₁ * b₂), ∃ o ∈ O, ∃ n ∈ Cen (b₁ * b₂) ⊓
        Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)), g = o * n) :
    R34Stmt b b₁ b₂ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  obtain ⟨Ot, hZO, hOΓ, hOn, hO6, hdec⟩ := hcon
  have hZc : ∀ r ∈ Ot, ∀ z ∈ Subgroup.zpowers (b₁ * b₂), r * z = z * r := by
    intro r hr z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcm : Commute r (b₁ * b₂) := Subgroup.mem_centralizer_singleton_iff.mp (hOΓ hr)
    exact (Commute.zpow_right hcm k).eq
  have hcop : ∀ r ∈ Ot, ∃ m : ℕ, Nat.Coprime 3 m ∧ r ^ m ∈ Subgroup.zpowers (b₁ * b₂) := by
    intro r hr
    obtain ⟨m, hm6, hm⟩ := hO6 r hr
    exact ⟨m, Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) hm6, hm⟩
  obtain ⟨O, hOR, hZOb, hOdec, hOc⟩ := exists_central_complement hZO hZc S.card_Z hcop
  have hΓN : Cen (b₁ * b₂) ≤ Nor (Subgroup.zpowers (b₁ * b₂)) :=
    fun x hx => fs79_cen_le_nor_zpowers _ hx
  have hOopp : O ≤ Opp 3 (Nor (Subgroup.zpowers (b₁ * b₂))) := by
    have h1 : O ≤ Opp 3 (Cen (b₁ * b₂)) := L14.le_Opp_of_normalized (hOR.trans hOΓ)
      (fun g hg x hx => conj_mem_complement hZc S.card_Z hOR hOdec hOc hx
        (hOn g hg x (hOR hx))) hOc
    exact h1.trans (L14.Opp_le_Opp_of_normalized hΓN
      (fun g hg c hc => S.Nor_beta_normalizes_cen hg hc))
  have hΓdec : ∀ γ ∈ Cen (b₁ * b₂), ∃ x ∈ Opp 3 (Nor (Subgroup.zpowers (b₁ * b₂))),
      ∃ m ∈ Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers (b₁ * b₂)), γ = x * m := by
    intro γ hγ
    obtain ⟨o', ho', n, hn, hγ'⟩ := hdec γ hγ
    obtain ⟨z, hz, x, hx, rfl⟩ := hOdec o' ho'
    have hxz : x * z = z * x := hZc x (hOR hx) z hz
    refine ⟨x, hOopp hx, z * n, ⟨?_, ?_⟩, ?_⟩
    · exact (Nor _).mul_mem (S.hyp.J_le_Nor (S.Z_le_J hz)) (S.Nor_E_le_Nor hn.2)
    · exact (Nor _).mul_mem (Subgroup.le_normalizer hz) (hΓN hn.1)
    · rw [hγ', ← mul_assoc, ← hxz, mul_assoc]
  show setMul (Opp 3 (Nor (Subgroup.zpowers (b₁ * b₂))))
    (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers (b₁ * b₂))) =
      Nor (Subgroup.zpowers (b₁ * b₂))
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨o, ho, k, hk, rfl⟩
    exact (Nor _).mul_mem (L14.Opp_le 3 _ ho) hk.2
  · intro g hg
    have hgβ : g * (b₁ * b₂) * g⁻¹ ∈ Subgroup.zpowers (b₁ * b₂) :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp (Subgroup.mem_zpowers _)
    have hne : g * (b₁ * b₂) * g⁻¹ ≠ 1 := by
      intro h1
      apply S.d_ne_one
      calc b₁ * b₂ = g⁻¹ * (g * (b₁ * b₂) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rcases eq_or_inv_of_mem_zpowers_of_pow_three S.beta_pow_three S.d_ne_one hgβ hne with
      hcen | hinv
    · have hgΓ : g ∈ Cen (b₁ * b₂) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hcen)
      obtain ⟨x, hx, m, hm, rfl⟩ := hΓdec g hgΓ
      exact ⟨x, hx, m, hm, rfl⟩
    ·
      set a₀ : H := S.ι J6.ainv with ha₀
      have ha₀β : a₀ * (b₁ * b₂) * a₀⁻¹ = (b₁ * b₂)⁻¹ := by
        have := S.ι_conj J6.ainv J6.d
        rw [J6.ainv_d_conj, map_inv, S.ι_dd] at this
        exact this.symm
      have ha₀J : a₀ ∈ J := S.ι_mem _
      have ha₀N : a₀ ∈ Nor (Subgroup.zpowers (b₁ * b₂)) :=
        mem_Nor_zpowers_of_conj (by rw [ha₀β]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
      have hγ : g * a₀ ∈ Cen (b₁ * b₂) := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq ?_)
        calc g * a₀ * (b₁ * b₂) * (g * a₀)⁻¹ = g * (a₀ * (b₁ * b₂) * a₀⁻¹) * g⁻¹ := by group
          _ = (g * (b₁ * b₂) * g⁻¹)⁻¹ := by rw [ha₀β]; group
          _ = b₁ * b₂ := by rw [hinv]; group
      obtain ⟨x, hx, m, hm, hgm⟩ := hΓdec _ hγ
      refine ⟨x, hx, m * a₀⁻¹, ⟨?_, ?_⟩, ?_⟩
      · exact (Nor _).mul_mem hm.1 ((Nor _).inv_mem (S.hyp.J_le_Nor ha₀J))
      · exact (Nor _).mul_mem hm.2 ((Nor _).inv_mem ha₀N)
      · rw [← mul_assoc, ← hgm]
        group

theorem r34K (hR1K : KF_FS79Prop2OneK) (hK : KCore.KGroupNonab InCatalog H) :
    R34Stmt b b₁ b₂ := by
  haveI hN : ((Subgroup.zpowers (b₁ * b₂)).subgroupOf (Cen (b₁ * b₂))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using S.qdata.Z_norm (g : H) g.2 (n : H) hn⟩
  exact S.r34_of_conclusion (S.qdata.conclusionP (fun G _ _ => KCore.KGroupNonab InCatalog G)
    (fun G _ _ hG => hR1K G hG) (kGroupNonab_quotient hK _ _))

end Std

theorem fs79R34K_of (hR1K : KF_FS79Prop2OneK) : FS79R34K := by
  intro H _ _ hK b t b₁ b₂ J hH
  exact hH.std.r34K hR1K hK

end CFSG.RankThree.PartTwo.Sec21.FF81
