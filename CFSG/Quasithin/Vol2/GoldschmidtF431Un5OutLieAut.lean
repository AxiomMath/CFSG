module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieStab
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin CFSG.QuasithinUnique

theorem aut5_exists_conj {G : Type*} [Group G] [Finite G] {R A B : Subgroup G}
    (hAp : IsPGroup 2 A) (hA : ¬ 2 ∣ A.relIndex R) (hBR : B ≤ R) (hBp : IsPGroup 2 B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SA : Sylow 2 R := (hAp.comap_subtype (K := R)).toSylow hA
  obtain ⟨X, hX⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R X SA
  refine ⟨((r⁻¹ : R) : G), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • X : Sylow 2 R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hX (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : ((MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) : G) ∈ A := hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def Q5 : Subgroup (MulAut (hypPSU h 2 1)) :=
  Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊤

theorem Q5_le_autStab : Q5 h ≤ autStab (hypProjUnitriangular h 2 1) :=
  Ssd5_le_autStab h (fStab5_U h) le_rfl ⊤

include h in
theorem isPGroup_Q5 (hf : f = 2) : IsPGroup 2 (Q5 h) := by
  have := h.finite
  have := finite_hypPSU_five h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 (u5_sylow h).2.1
  rw [IsPGroup.iff_card]
  refine ⟨a + 2, ?_⟩
  rw [Q5, card_Ssd5 h (u5_center_eq_bot h), ha, Subgroup.card_top, fld5_card h, hf, pow_add]
  norm_num

include h in
theorem Q5_sylow (hf : f = 2) :
    IsSylowTwoOf (Q5 h) (autStab (hypProjUnitriangular h 2 1)) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := hypProjUnitriangular h 2 1 with hU
  set G₁ := autStab U with hG₁
  have hQ2 := isPGroup_Q5 h hf
  refine ⟨Q5_le_autStab h, hQ2, ?_⟩
  set Q₀ : Subgroup ↥G₁ := (Q5 h).subgroupOf G₁ with hQ₀
  have hQ₀p : IsPGroup 2 Q₀ := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (Q5_le_autStab h)).symm
  obtain ⟨P, hP⟩ := hQ₀p.exists_le_sylow
  have key : (P : Subgroup ↥G₁) ≤ Q₀ := by
    intro x hx
    have hxU : ∀ y, x.1 y ∈ U ↔ y ∈ U := fun y => (x.2 y).symm
    obtain ⟨e, he, σ', ⟨σ, hσ⟩, hxe⟩ := u5_normal_form h x.1 hxU
    subst hσ
    set s : ↥G₁ := ⟨fa5 h σ, fa5_mem_autStab h (fStab5_U h) σ⟩ with hs
    have hsQ : s ∈ Q₀ := fa5_mem_Ssd5 h (hB := fStab5_U h) (Subgroup.mem_top σ)
    have hsP : s ∈ (P : Subgroup ↥G₁) := hP hsQ
    set e' : ↥G₁ := x * s⁻¹ with he'
    have he'P : e' ∈ (P : Subgroup ↥G₁) := P.mul_mem hx (P.inv_mem hsP)
    have he'val : (e' : MulAut (hypPSU h 2 1)) = e := by
      change x.1 * (fa5 h σ)⁻¹ = e
      rw [hxe]
      group
    obtain ⟨k, hk⟩ := P.isPGroup' (⟨e', he'P⟩ : (P : Subgroup ↥G₁))
    have hek : e ^ 2 ^ k = 1 := by
      have h1 : e' ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, he'val] at h2
    obtain ⟨u, hu, hue⟩ := (borelAutDiag_u5 h).E_two e he k hek
    have he'Q : e' ∈ Q₀ := by
      change (e' : MulAut (hypPSU h 2 1)) ∈ Q5 h
      rw [he'val, hue]
      exact cj5_mem_Ssd5 h (hB := fStab5_U h) hu
    have : x = e' * s := by rw [he']; group
    rw [this]
    exact Q₀.mul_mem he'Q hsQ
  have hPQ : Q₀ = (P : Subgroup ↥G₁) := le_antisymm hP key
  have := P.not_dvd_index
  rwa [← hPQ] at this

include h in
theorem exists_conj_into_Q5 (hf : f = 2) {R : Subgroup (MulAut (hypPSU h 2 1))}
    (hR : IsPGroup 2 R) (hRU : R ≤ autStab (hypProjUnitriangular h 2 1)) :
    ∃ g ∈ autStab (hypProjUnitriangular h 2 1), ∀ y ∈ R, g⁻¹ * y * g ∈ Q5 h := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  exact aut5_exists_conj (isPGroup_Q5 h hf) (Q5_sylow h hf).2.2 hRU hR

end CFSG.Quasithin.H13.F431.Un.OL5
