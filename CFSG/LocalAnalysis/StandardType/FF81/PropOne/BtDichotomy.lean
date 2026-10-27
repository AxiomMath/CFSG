module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LiftData
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
public import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLift
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLiftX

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec21.FF81.Lift (BB BO Compl)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

theorem bt_dichotomy {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hB₁ : ∀ m ∈ nB b z, ∀ y ∈ bOne z, m * y * m⁻¹ ∈ bOne z) :
    ∀ hb : b ∈ Subgroup.normalizer
        ((BB b (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) : Subgroup G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer
        ((BB b (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) : Subgroup G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer
          ((BB b (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) : Subgroup G) : Set G)) →
      (∃ t ∈ Subgroup.normalizer
          ((BB b (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) : Subgroup G) : Set G),
        t * b * t⁻¹ = b⁻¹ ∧
          ∀ y ∈ BO (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2), t * y * t⁻¹ = y) ∨
      ∃ K NL : Subgroup G, Compl b (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) K NL := by
  let b₁ := GGFF.zs z 0
  let b₂ := GGFF.zs z 1
  let b₃ := GGFF.zs z 2
  let N := Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)
  let D : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Data b b₁ b₂ b₃ := lift_data h hB₁
  obtain ⟨τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ, hMemL, M, _⟩ := exists_mono_irreducible h
  have key : ∀ (j : Fin 3) (e : ℕ), (e = 1 ∨ e = 2) →
      GGFF.zs z j ^ e ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
    intro j e he
    rcases he with rfl | rfl
    · fin_cases j <;> simp [b₁, b₂, b₃]
    · have h2 : GGFF.zs z j ^ 2 = (GGFF.zs z j)⁻¹ := GGFF.SettingCore.zs_sq h.settingCore j
      rw [h2]
      fin_cases j <;> simp [b₁, b₂, b₃]
  have hmono : ∀ m ∈ N, (m * b * m⁻¹ = b ∨ m * b * m⁻¹ = b⁻¹) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        m * x * m⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
    intro m hm hmb x hx
    have hbpow : m * b * m⁻¹ ∈ Subgroup.zpowers b := by
      rcases hmb with hmb | hmb
      · rw [hmb]; exact Subgroup.mem_zpowers b
      · rw [hmb]; exact Subgroup.zpowers_inv (g := b) ▸ Subgroup.mem_zpowers b⁻¹
    have hm' : m ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) := by
      rw [GGFF.SettingCore.Bt_eq_closure]
      exact hm
    rcases hx with rfl | rfl | rfl
    · obtain ⟨j, e, he, hje⟩ := h.facts.stab m hm' hbpow 0
      rw [hje]; exact key j e he
    · obtain ⟨j, e, he, hje⟩ := h.facts.stab m hm' hbpow 1
      rw [hje]; exact key j e he
    · obtain ⟨j, e, he, hje⟩ := h.facts.stab m hm' hbpow 2
      rw [hje]; exact key j e he
  have hself : L ⊓ Subgroup.centralizer ((BO b₁ b₂ b₃ : Subgroup G) : Set G) ≤ BO b₁ b₂ b₃ := by
    intro k hk
    obtain ⟨hkL, hkC⟩ := Subgroup.mem_inf.mp hk
    rw [Subgroup.mem_centralizer_iff] at hkC
    have hcomm : ∀ i, (⟨k, hkL⟩ : ↥L) * z i = z i * ⟨k, hkL⟩ := by
      intro i
      apply Subtype.ext
      show k * (z i : G) = (z i : G) * k
      exact (hkC (GGFF.zs z i)
        (Subgroup.subset_closure (by fin_cases i <;> simp [b₁, b₂, b₃]))).symm
    obtain ⟨v, hv⟩ := CFSG.StandardType.FF81.cen_of_model h.hypA.n_cases h.hypA.model h.model
      (⟨k, hkL⟩ : ↥L) hcomm
    have hk' : k ∈ GGFF.tor (GGFF.zs z) := by
      rw [GGFF.SettingCore.mem_torG h.settingCore]
      refine ⟨v, ?_⟩
      have h1 : k = ((vecElt z v : ↥L) : G) := congrArg Subtype.val hv
      rwa [← GGFF.SettingCore.vecElt_zs] at h1
    rw [GGFF.SettingCore.tor_eq_closure] at hk'
    exact hk'
  have hcompl : (∀ g ∈ N, g * b * g⁻¹ * b ∉ BO b₁ b₂ b₃) →
      ∃ K NL : Subgroup G, Compl b b₁ b₂ b₃ K NL := by
    intro hno
    obtain ⟨K, hKN, hKC, hK3, hCK⟩ := D.exists_K
    let NL := L ⊓ N ⊓ Subgroup.centralizer ({b} : Set G)
    have hNLN : NL ≤ N := fun l hl => hl.1.2
    have hNLb : ∀ l ∈ NL, l * b * l⁻¹ = b := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff.mp hl.2, mul_inv_cancel_right]
    have hNL : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ NL := by
      intro g hg
      obtain ⟨hgN, hgb⟩ := M.mem g (Set.mem_insert_of_mem τ hg)
      refine ⟨⟨hMemL g (Set.mem_insert_of_mem τ hg), hgN⟩, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgb)
    refine ⟨K, NL,
      { KN := hKN
        KC := hKC
        K3 := hK3
        CK := hCK
        NLN := hNLN
        NLb := hNLb
        NLC := fun x hx => hself ⟨hx.1.1.1, Subgroup.centralizer_le D.B₁_le_B hx.2⟩
        gen := fun m hm => D.gen_of_no_inv M hmono hno hNLN hNLb hNL hm }⟩
  exact D.hbt_of M (fun m hm hmb => hmono m hm (Or.inr hmb)) hcompl

end CFSG.StandardType.FF81.PropOne

end
