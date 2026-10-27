module

public import CFSG.Quasithin.Background.RonanH143NF
public import CFSG.Quasithin.Background.RonanH143Orbit
public import CFSG.Quasithin.Background.RonanH143Syl

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

theorem std_sets_of_conj {a b : Fin 24} {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ Γ : Subgroup P24} {c : P24} (hc : c ∈ AutPerm)
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hΓ : Γ ≤ M2ab a b) (hPO : PO ≤ conjSubg c (T₀ ⊓ Γ))
    (hca : (c a = 0 ∧ c b = 1) ∨ (c a = 1 ∧ c b = 0)) :
    c • O = Ostd ∧ c • S = Sstd ∧ c • B = Bstd := by
  have h0 : ∃ x ∈ ({a, b} : Finset (Fin 24)), c x = 0 := by
    rcases hca with ⟨h, -⟩ | ⟨-, h⟩
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩
  have h1 : ∃ x ∈ ({a, b} : Finset (Fin 24)), c x = 1 := by
    rcases hca with ⟨-, h⟩ | ⟨h, -⟩
    · exact ⟨b, by simp, h⟩
    · exact ⟨a, by simp, h⟩
  have hOmem : ∀ x ∈ ({a, b} : Finset (Fin 24)), x ∈ O := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hBmem : ∀ x ∈ ({a, b} : Finset (Fin 24)), x ∈ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hPOt : ∀ g ∈ PO, ∃ t ∈ T₀ ⊓ Γ, g = c * t * c⁻¹ := by
    intro g hg
    have := mem_conjSubg_iff.1 (hPO hg)
    refine ⟨c⁻¹ * g * c, this, ?_⟩
    group
  have hOinv : ∀ g ∈ PO, g • (c • O) = c • O := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := hPOt g hg
    have e : c * t * c⁻¹ * c = c * t := by group
    rw [← mul_smul, e, mul_smul, hTO t ht.1]
  have hBt : ∀ t ∈ T₀ ⊓ Γ, t • B = B := by
    intro t ht
    have htM : t • ({a, b} : Finset (Fin 24)) = {a, b} :=
      MulAction.mem_stabilizer_iff.1 (hΓ ht.2).2
    have hta : t a ∈ B := by
      have : t • a ∈ t • ({a, b} : Finset (Fin 24)) := Finset.smul_mem_smul_finset (by simp)
      rw [htM] at this
      exact hBmem _ this
    have hmem : t • B ∈ S := by
      have := Finset.smul_mem_smul_finset (a := t) hBS
      rwa [hTS t ht.1] at this
    by_contra hne
    have hdis := hS.2.2.1 _ hmem _ hBS hne
    exact Finset.disjoint_left.1 hdis (Finset.mem_smul_finset.2 ⟨a, haB, rfl⟩) hta
  have hBinv : ∀ g ∈ PO, g • (c • B) = c • B := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := hPOt g hg
    have e : c * t * c⁻¹ * c = c * t := by group
    rw [← mul_smul, e, mul_smul, hBt t ht]
  have hOstd : c • O = Ostd := by
    refine eq_Ostd_of_PO_inv (by rw [Finset.card_smul_finset, hO]) ?_ ?_ hOinv
    · obtain ⟨x, hx, hcx⟩ := h0
      rw [← hcx]
      exact Finset.smul_mem_smul_finset (hOmem x hx)
    · obtain ⟨x, hx, hcx⟩ := h1
      rw [← hcx]
      exact Finset.smul_mem_smul_finset (hOmem x hx)
  have hBstd : c • B = Bstd := by
    refine eq_Bstd_of_PO_inv (by rw [Finset.card_smul_finset]; exact hS.2.1 B hBS) ?_ ?_ hBinv
    · obtain ⟨x, hx, hcx⟩ := h0
      rw [← hcx]
      exact Finset.smul_mem_smul_finset (hBmem x hx)
    · obtain ⟨x, hx, hcx⟩ := h1
      rw [← hcx]
      exact Finset.smul_mem_smul_finset (hBmem x hx)
  refine ⟨hOstd, ?_, hBstd⟩
  have hBc : Bstd ∈ c • S := by
    rw [← hBstd]
    exact Finset.smul_mem_smul_finset hBS
  exact sext_eq_of_mem (isSextR_smul hc hS) isSext_Sstd hBc (by simp [Sstd])

theorem normal_form_core {a b : Fin 24} {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ Γ Y X : Subgroup P24} {τ γ : P24} (hτm : τ ∈ AutPerm)
    (hτa : τ a = 0) (hτb : τ b = 1) (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O)
    (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B) (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O)
    (hTS : ∀ g ∈ T₀, g • S = S) (hΓ : Γ ≤ M2ab a b) (hYle : Y ≤ mog22plus) (hXle : PO ≤ X)
    (hE : conjSubg τ Γ = Y) (hγY : γ ∈ Y) (hγP : conjSubg γ (conjSubg τ T₀ ⊓ Y) = X) :
    ∃ c ∈ AutPerm, ((c a = 0 ∧ c b = 1) ∨ (c a = 1 ∧ c b = 0)) ∧ c • O = Ostd ∧ c • S = Sstd ∧
      c • B = Bstd ∧ conjSubg c Γ = Y ∧ conjSubg c T₀ ⊓ Y = X := by
  have hγpl := hYle hγY
  have hc : γ * τ ∈ AutPerm := AutPerm.mul_mem hγpl.1 hτm
  have hca : ((γ * τ) a = 0 ∧ (γ * τ) b = 1) ∨ ((γ * τ) a = 1 ∧ (γ * τ) b = 0) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτa, hτb]
    exact hγpl.2
  have hcΓ : conjSubg (γ * τ) Γ = Y := by
    rw [conjSubg_mul, hE, conjSubg_eq_self hγY]
  have hcT : conjSubg (γ * τ) T₀ ⊓ Y = X := by
    rw [← hγP, conjSubg_inf, conjSubg_eq_self hγY, conjSubg_mul]
  have hPO : PO ≤ conjSubg (γ * τ) (T₀ ⊓ Γ) := by
    rw [conjSubg_inf, hcΓ, hcT]
    exact hXle
  obtain ⟨hO', hS', hB'⟩ := std_sets_of_conj hc hO haO hbO hS hBS haB hbB hTO hTS hΓ hPO hca
  exact ⟨γ * τ, hc, hca, hO', hS', hB', hcΓ, hcT⟩

theorem normal_form {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S)
    (hBS : B ∈ S) (haB : a ∈ B) (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O)
    (hTS : ∀ g ∈ T₀, g • S = S) (hL : M22g a b ≤ Γ) (hΓ : Γ ≤ M2ab a b)
    (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ) :
    ∃ c ∈ AutPerm, ((c a = 0 ∧ c b = 1) ∨ (c a = 1 ∧ c b = 0)) ∧ c • O = Ostd ∧ c • S = Sstd ∧
      c • B = Bstd ∧
      ((conjSubg c Γ = mog22 ∧ conjSubg c T₀ ⊓ mog22 = PO) ∨
        (conjSubg c Γ = mog22plus ∧ conjSubg c T₀ ⊓ mog22plus = P2)) := by
  obtain ⟨p, hp, hp0, hp1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
  set τ : P24 := p⁻¹ with hτ
  have hτm : τ ∈ AutPerm := AutPerm.inv_mem hp
  have hτa : τ a = 0 := by rw [hτ, Equiv.Perm.inv_eq_iff_eq, hp0]
  have hτb : τ b = 1 := by rw [hτ, Equiv.Perm.inv_eq_iff_eq, hp1]
  set Γ₁ := conjSubg τ Γ with hΓ₁
  have hΓ₁1 : mog22 ≤ Γ₁ := by
    have := (conjSubg_le_conjSubg_iff (c := τ)).2 hL
    rwa [M22g_conj hτm, hτa, hτb] at this
  have hΓ₁2 : Γ₁ ≤ mog22plus := by
    have := (conjSubg_le_conjSubg_iff (c := τ)).2 hΓ
    rwa [M2ab_conj hτm, hτa, hτb, M2ab_zero_one] at this
  have hSyl₁ : IsSylowIn 2 (conjSubg τ T₀ ⊓ Γ₁) Γ₁ := by
    rw [hΓ₁, ← conjSubg_inf]
    exact isSylowIn_conj τ hSyl
  rcases eq_mog22_or_plus hΓ₁1 hΓ₁2 with hE | hE
  ·
    rw [hE] at hSyl₁
    obtain ⟨γ, hγ, hγP⟩ := exists_conj_sylow_PO hSyl₁
    obtain ⟨c, hc, hca, hO', hS', hB', hcΓ, hcT⟩ := normal_form_core hτm hτa hτb hO haO hbO hS hBS
      haB hbB hTO hTS hΓ (hΓ₁1.trans hΓ₁2) le_rfl hE hγ hγP
    exact ⟨c, hc, hca, hO', hS', hB', Or.inl ⟨hcΓ, hcT⟩⟩
  ·
    rw [hE] at hSyl₁
    obtain ⟨γ, hγ, hγP⟩ := exists_conj_sylow_P2 hSyl₁
    obtain ⟨c, hc, hca, hO', hS', hB', hcΓ, hcT⟩ := normal_form_core hτm hτa hτb hO haO hbO hS hBS
      haB hbB hTO hTS hΓ le_rfl PO_le_P2 hE hγ hγP
    exact ⟨c, hc, hca, hO', hS', hB', Or.inr ⟨hcΓ, hcT⟩⟩

end CFSG.Quasithin.RonanH143
