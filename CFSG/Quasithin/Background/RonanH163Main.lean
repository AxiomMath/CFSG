module

public import CFSG.Quasithin.Background.RonanH163Std
public import CFSG.Quasithin.Background.RonanH163Tconj
public import CFSG.Quasithin.Background.RonanH143NF2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem M2ab_one_zero : M2ab 1 0 = mog22plus := by
  rw [← M2ab_zero_one]
  unfold M2ab
  rw [Finset.pair_comm]

theorem ePerm_one : ePerm 1 = 0 := by decide +kernel

theorem ePerm_zero : ePerm 0 = 1 := by decide +kernel

theorem ePerm_smul_Sstd : ePerm • Sstd = Sstd := by decide +kernel

theorem ePerm_smul_Bstd : ePerm • Bstd = Bstd := by decide +kernel

theorem ePerm_smul_Ostd : ePerm • Ostd = Ostd := by decide +kernel

theorem normal_form_plus
    {a b : Fin 24} (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ Γ : Subgroup P24} (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O)
    (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B) (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O)
    (hTS : ∀ g ∈ T₀, g • S = S) (hL : M22g a b ≤ Γ) (hΓ : Γ = M2ab a b)
    (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ) :
    ∃ c ∈ AutPerm, c a = 0 ∧ c b = 1 ∧ c • O = Ostd ∧ c • S = Sstd ∧ c • B = Bstd ∧
      conjSubg c Γ = mog22plus := by
  obtain ⟨c, hc, hca, hO', hS', hB', -⟩ :=
    normal_form hab hO haO hbO hS hBS haB hbB hTO hTS hL hΓ.le hSyl
  have hcΓ : conjSubg c Γ = M2ab (c a) (c b) := by
    rw [hΓ]
    exact M2ab_conj hc a b
  rcases hca with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨c, hc, h0, h1, hO', hS', hB', ?_⟩
    rw [hcΓ, h0, h1, M2ab_zero_one]
  · refine ⟨ePerm * c, AutPerm.mul_mem ePerm_mem_mog22plus.1 hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, h0, ePerm_one]
    · rw [Equiv.Perm.mul_apply, h1, ePerm_zero]
    · rw [mul_smul, hO', ePerm_smul_Ostd]
    · rw [mul_smul, hS', ePerm_smul_Sstd]
    · rw [mul_smul, hB', ePerm_smul_Bstd]
    · rw [conjSubg_mul, hcΓ, h0, h1, M2ab_one_zero, conjSubg_eq_self ePerm_mem_mog22plus]

theorem exists_std_iso {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(golayC ⊓ pairKer a b) ⧸
      (Subgroup.zpowers (G6.allOnes 24)).subgroupOf (golayC ⊓ pairKer a b)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ) (hΓ : Γ = M2ab a b)
    (hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    ∃ c : P24, c a = 0 ∧ c b = 1 ∧ c • O = Ostd ∧ c • S = Sstd ∧ c • B = Bstd ∧
      ∃ (hcΓ : conjSubg c Γ = mog22plus) (φ : ↥Γ →* ↥mog22plus),
        (∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) ∧
        ∃ e : V ≃* W10, ∀ (g : ↥Γ) (v : V), e (ρ g v) = R (φ g) (e v) := by
  obtain ⟨c, hc, hca, hcb, hcO, hcS, hcB, hcΓ⟩ :=
    normal_form_plus hab hO haO hbO hS hBS haB hbB hTO hTS hL hΓ hSyl
  set τ : P24 := c⁻¹ with hτdef
  have hτ : τ ∈ AutPerm := AutPerm.inv_mem hc
  have hτ0 : τ 0 = a := by rw [hτdef, Equiv.Perm.inv_eq_iff_eq, hca]
  have hτ1 : τ 1 = b := by rw [hτdef, Equiv.Perm.inv_eq_iff_eq, hcb]
  have hn : ∀ m, m ∈ golayC ⊓ pairKer a b ↔ G6.permAct 24 τ⁻¹ m ∈ golayC ⊓ pairKer 0 1 := by
    intro m
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine and_congr ((preserves_iff_of_mem hτ).2 m) ?_
    rw [mem_pairKer, mem_pairKer, G6.permAct_apply, G6.permAct_apply, inv_inv, hτ0, hτ1]
  have hd := zpowers_allOnes_iff τ
  have hΓ' : ∀ σ ∈ Γ, Preserves (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)) σ := by
    intro σ hσ
    have hσ' : c * σ * c⁻¹ ∈ mog22plus := by
      rw [← hcΓ, mem_conjSubg_iff]
      have e : c⁻¹ * (c * σ * c⁻¹) * c = σ := by group
      rw [e]
      exact hσ
    refine ⟨fun m hm => ?_, fun m hm => CFSG.Quasithin.H.Mathieu.permAct_mem_zpowers_allOnes σ hm⟩
    rw [hn]
    have e : G6.permAct 24 τ⁻¹ (G6.permAct 24 σ m) =
        G6.permAct 24 (c * σ * c⁻¹) (G6.permAct 24 τ⁻¹ m) := by
      rw [hτdef, inv_inv, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply,
        permAct_inv_apply_permAct]
    rw [e]
    exact (preserves_code22 hσ').1 _ ((hn m).1 hm)
  obtain ⟨e, he⟩ := (code22Coords.conj τ hn hd).exists_equiv hΓ' hreal
  obtain ⟨φ, hφ⟩ := exists_conjHom c hcΓ
  have he' : ∀ (g : ↥Γ) (v : V), e (ρ g v) = R (φ g) (e v) := by
    intro g v
    have h1 := he g v
    have h2 : (code22Coords.conj τ hn hd).rho Γ hΓ' g (e v) =
        code22Coords.rhoHom (c * (g : P24) * c⁻¹) (e v) := by
      show (code22Coords.conj τ hn hd).rhoHom (g : P24) (e v) = _
      rw [SecCoords.conj_rhoHom, hτdef, inv_inv]
    have h3 : R (φ g) (e v) = code22Coords.rhoHom (c * (g : P24) * c⁻¹) (e v) := by
      show code22Coords.rhoHom ((φ g : ↥mog22plus) : P24) (e v) = _
      rw [hφ]
    rw [h3]
    exact h1.trans h2
  exact ⟨c, hca, hcb, hcO, hcS, hcB, hcΓ, φ, hφ, e, he'⟩

theorem main163 {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(golayC ⊓ pairKer a b) ⧸
      (Subgroup.zpowers (G6.allOnes 24)).subgroupOf (golayC ⊓ pairKer a b)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ)
    (hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Γ = M2ab a b → Concl163 ρ (S.erase B) := by
  intro hΓ
  obtain ⟨c, -, -, -, hcS, hcB, hcΓ, φ, hφ, e, he'⟩ :=
    exists_std_iso hab hO haO hbO hS hBS haB hbB hTO hTS hL hSyl hΓ hreal
  have hQ : c • S.erase B = Qstd := by
    rw [smul_erase_finset_finset, hcS, hcB, Sstd_erase]
  exact Concl163_of_transport c hcΓ ρ R φ hφ e he' (S.erase B) (hQ ▸ std163)

end CFSG.Quasithin.RonanH163
