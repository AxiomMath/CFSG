module

public import CFSG.Quasithin.AppendixH.H15.Vocab
public import CFSG.Quasithin.AppendixH.Common.OctadHeptad
public import CFSG.Quasithin.AppendixH.Common.OctadTwoCore

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem factorization_pow_mul {p a m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ a * m).factorization p = a := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero a hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm, smul_eq_mul, mul_one, add_zero]

theorem mctx_cases (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    (d = 24 ∧ Γ = M24g) ∨ (d = 23 ∧ Γ = M23g a) ∨ (d = 22 ∧ M22g a b ≤ Γ ∧ Γ ≤ M2ab a b) := by
  rcases hM.d_mem with rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨rfl, by simpa [Ld] using hM.L_le, by simpa [AutLd] using hM.le_Aut⟩)
  · exact Or.inr (Or.inl ⟨rfl, le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut)
      (by simpa [Ld] using hM.L_le)⟩)
  · exact Or.inl ⟨rfl, le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut)
      (by simpa [Ld] using hM.L_le)⟩

theorem eq_M22g_or_eq_M2ab {a b : Fin 24} (hab : a ≠ b) {Γ : Subgroup S24} (h1 : M22g a b ≤ Γ)
    (h2 : Γ ≤ M2ab a b) : Γ = M22g a b ∨ Γ = M2ab a b := by
  by_cases hle : Γ ≤ M22g a b
  · exact Or.inl (le_antisymm hle h1)
  · refine Or.inr (le_antisymm h2 ?_)
    have hex : ∃ s : S24, s ∈ Γ ∧ s ∉ M22g a b := by
      by_contra h
      apply hle
      intro x hx
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    obtain ⟨s, hsΓ, hsnot⟩ := hex
    have hsM2 : s ∈ M2ab a b := h2 hsΓ
    obtain ⟨hsM24, hsfix | hswap⟩ := (mem_M2ab_iff a b hab s).1 hsM2
    · exact absurd ((mem_M22g_iff a b s).2 ⟨hsM24, hsfix.1, hsfix.2⟩) hsnot
    · intro x hx
      obtain ⟨hxM24, hxfix | hxswap⟩ := (mem_M2ab_iff a b hab x).1 hx
      · exact h1 ((mem_M22g_iff a b x).2 ⟨hxM24, hxfix.1, hxfix.2⟩)
      · have hsinv_a : s⁻¹ a = b := by
          rw [← hswap.2]
          exact Equiv.symm_apply_apply s b
        have hsinv_b : s⁻¹ b = a := by
          rw [← hswap.1]
          exact Equiv.symm_apply_apply s a
        have hxs : x * s⁻¹ ∈ M22g a b := by
          rw [mem_M22g_iff]
          exact ⟨M24g.mul_mem hxM24 (M24g.inv_mem hsM24),
            by rw [Equiv.Perm.mul_apply, hsinv_a, hxswap.2],
            by rw [Equiv.Perm.mul_apply, hsinv_b, hxswap.1]⟩
        have hxΓ : x * s⁻¹ ∈ Γ := h1 hxs
        have hxeq : x = (x * s⁻¹) * s := by group
        rw [hxeq]
        exact Γ.mul_mem hxΓ hsΓ

theorem mctx_le_M24 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : Γ ≤ M24g := by
  intro g hg
  rcases mctx_cases hM with ⟨_, hΓ⟩ | ⟨_, hΓ⟩ | ⟨_, h1, h2⟩
  · rwa [hΓ] at hg
  · exact ((mem_M23g_iff a g).1 (hΓ ▸ hg)).1
  · exact ((mem_M2ab_iff a b hM.cfg.ne g).1 (h2 hg)).1

theorem mctx_octFix_le (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : octFix O ≤ Γ := by
  intro g hg
  obtain ⟨hgM, hgfix⟩ := mem_octFix_iff.1 hg
  rcases mctx_cases hM with ⟨_, hΓ⟩ | ⟨_, hΓ⟩ | ⟨_, h1, _⟩
  · rw [hΓ]
    exact hgM
  · rw [hΓ]
    exact (mem_M23g_iff a g).2 ⟨hgM, hgfix a hM.cfg.a_O⟩
  · exact h1 ((mem_M22g_iff a b g).2 ⟨hgM, hgfix a hM.cfg.a_O, hgfix b hM.cfg.b_O⟩)

theorem mctx_kY_eq (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    KY Γ (Yd d a b O) = octFix O := by
  unfold KY MY
  rcases mctx_cases hM with ⟨h24, hΓ⟩ | ⟨h23, hΓ⟩ | ⟨h22, h1, h2⟩
  · rw [hΓ, h24]
    rw [show Yd 24 a b O = O from by simp [Yd]]
    simpa [octStab] using pCoreOf_octStab hM.cfg.octad
  · rw [hΓ, h23]
    rw [show Yd 23 a b O = O.erase a from by simp [Yd]]
    exact pCoreOf_M23g_stabilizer_erase hM.cfg.octad hM.cfg.a_O
  · rw [h22]
    rw [show Yd 22 a b O = (O.erase a).erase b from by simp [Yd]]
    exact pCoreOf_between_stabilizer_erase₂ hM.cfg.octad hM.cfg.a_O hM.cfg.b_O h1 h2

theorem mctx_mY_le (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : MY Γ (Yd d a b O) ≤ octStab O := by
  unfold MY
  rcases mctx_cases hM with ⟨h24, hΓ⟩ | ⟨h23, hΓ⟩ | ⟨h22, h1, h2⟩
  · rw [hΓ, h24]
    rw [show Yd 24 a b O = O from by simp [Yd]]
    simpa [octStab]
  · rw [hΓ, h23]
    rw [show Yd 23 a b O = O.erase a from by simp [Yd]]
    rw [M23g_inf_stabilizer_erase hM.cfg.a_O]
    exact inf_le_left
  · rw [h22]
    rw [show Yd 22 a b O = (O.erase a).erase b from by simp [Yd]]
    calc Γ ⊓ MulAction.stabilizer S24 ((O.erase a).erase b)
        ≤ M2ab a b ⊓ MulAction.stabilizer S24 ((O.erase a).erase b) := inf_le_inf h2 le_rfl
      _ = octStab O ⊓ MulAction.stabilizer S24 ({a, b} : Finset (Fin 24)) :=
          M2ab_inf_stabilizer_erase₂ hM.cfg.a_O hM.cfg.b_O
      _ ≤ octStab O := inf_le_left

theorem mctx_T_le_mY (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : T₀ ⊓ Γ ≤ MY Γ (Yd d a b O) := by
  intro g hg
  obtain ⟨hgT, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hgM : g ∈ M24g := hM.cfg.sylow.le hgT
  have hgO : g ∈ octStab O := mem_octStab_iff.2 ⟨hgM, hM.cfg.stab_O g hgT⟩
  rw [MY]
  refine Subgroup.mem_inf.2 ⟨hgΓ, ?_⟩
  rcases mctx_cases hM with ⟨h24, hΓ⟩ | ⟨h23, hΓ⟩ | ⟨h22, h1, h2⟩
  · rw [h24]
    rw [show Yd 24 a b O = O from by simp [Yd]]
    exact MulAction.mem_stabilizer_iff.mpr (hM.cfg.stab_O g hgT)
  · rw [h23]
    rw [show Yd 23 a b O = O.erase a from by simp [Yd]]
    rw [hΓ] at hgΓ
    have hmem : g ∈ M23g a ⊓ MulAction.stabilizer S24 (O.erase a) := by
      rw [M23g_inf_stabilizer_erase hM.cfg.a_O]
      exact ⟨hgO, (Subgroup.mem_inf.1 hgΓ).2⟩
    exact (Subgroup.mem_inf.1 hmem).2
  · rw [h22]
    rw [show Yd 22 a b O = (O.erase a).erase b from by simp [Yd]]
    have hmem : g ∈ M2ab a b ⊓ MulAction.stabilizer S24 ((O.erase a).erase b) := by
      rw [M2ab_inf_stabilizer_erase₂ hM.cfg.a_O hM.cfg.b_O]
      exact ⟨hgO, (Subgroup.mem_inf.1 (h2 hgΓ)).2⟩
    exact (Subgroup.mem_inf.1 hmem).2

theorem mctx_octFix_le_T (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    octFix O ≤ T₀ ⊓ Γ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTO : T₀ ≤ octStab O := by
    intro g hg
    exact mem_octStab_iff.2 ⟨hM.cfg.sylow.le hg, hM.cfg.stab_O g hg⟩
  have hM24 : Nat.card M24g = 244823040 := by
    simpa [M24g] using card_AutPerm
  have hcardT : Nat.card T₀ = 2 ^ 10 := by
    rw [hM.cfg.sylow.card_eq, hM24]
    congr 1
    rw [show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num]
    exact factorization_pow_mul Nat.prime_two (by norm_num)
  have hcardO : Nat.card (octStab O) = 322560 := card_octStab hM.cfg.octad
  have hfacO : (Nat.card (octStab O)).factorization 2 = 10 := by
    rw [hcardO]
    rw [show (322560 : ℕ) = 2 ^ 10 * 315 by norm_num]
    exact factorization_pow_mul Nat.prime_two (by norm_num)
  have hSyl := CFSG.Quasithin.isSylowIn_of_card_eq hTO (by rw [hcardT, hfacO])
  have hP : octFix O ≤ T₀ :=
    hSyl.le_of_normal (octFix_le_octStab O) (normal_octFix O) (isPGroup_octFix hM.cfg.octad)
  exact le_inf hP (mctx_octFix_le hM)

theorem mem_mY_24 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 24) (g : S24) :
    g ∈ MY Γ (Yd d a b O) ↔ g ∈ octStab O := by
  rcases mctx_cases hM with ⟨_, hΓ⟩ | ⟨h23, _⟩ | ⟨h22, _, _⟩
  · rw [MY, hΓ]
    rw [show Yd d a b O = O from by simp [Yd, hd]]
    simp only [octStab]
  · exact absurd (h23.symm.trans hd) (by norm_num)
  · exact absurd (h22.symm.trans hd) (by norm_num)

theorem mem_mY_23 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 23) (g : S24) :
    g ∈ MY Γ (Yd d a b O) ↔ g ∈ octStab O ∧ g a = a := by
  rcases mctx_cases hM with ⟨h24, _⟩ | ⟨_, hΓ⟩ | ⟨h22, _, _⟩
  · exact absurd (h24.symm.trans hd) (by norm_num)
  · rw [MY, hΓ]
    rw [show Yd d a b O = O.erase a from by simp [Yd, hd]]
    rw [M23g_inf_stabilizer_erase hM.cfg.a_O]
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  · exact absurd (h22.symm.trans hd) (by norm_num)

theorem mem_mY_22a (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 22) (hΓ : Γ = M22g a b)
    (g : S24) : g ∈ MY Γ (Yd d a b O) ↔ g ∈ octStab O ∧ g a = a ∧ g b = b := by
  rw [MY, hΓ]
  rw [show Yd d a b O = (O.erase a).erase b from by simp [Yd, hd]]
  rw [M22g_inf_stabilizer_erase₂ hM.cfg.a_O hM.cfg.b_O]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, and_assoc]

theorem mem_mY_22b (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 22) (hΓ : Γ = M2ab a b)
    (g : S24) : g ∈ MY Γ (Yd d a b O) ↔
      g ∈ octStab O ∧ ((g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a)) := by
  rw [MY, hΓ]
  rw [show Yd d a b O = (O.erase a).erase b from by simp [Yd, hd]]
  rw [M2ab_inf_stabilizer_erase₂ hM.cfg.a_O hM.cfg.b_O]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, smul_pair_eq_iff g a b hM.cfg.ne]

end CFSG.ASVolI.AppH
