module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Hyp
public import CFSG.RankThree.PartTwo.Sec21.FF81S58Conj
public import CFSG.RankThree.PartTwo.Sec21.FF81S58K
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Transv
import CFSG.RankThree.PartTwo.Sec21.FF81P51
import CFSG.RankThree.PartTwo.Sec21.FF81Prop33
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
  {M : Subgroup G}

theorem mono_of_stab (hB : FF81Basis b L B b₁ b₂ b₃) :
    ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
  intro n hnL hnN x hx
  have hnb : n * b * n⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hnL), mul_inv_cancel_right]
  have hB1 : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, hB.mono.2.1] <;>
      exact Subgroup.subset_closure (by simp)
  have hBeq := hB.mono.2.1
  have key : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), n * y * n⁻¹ ∈ B := fun y hy =>
    hB1 ((Subgroup.mem_normalizer_iff.mp hnN y).mp hy)
  have hnB : n ∈ Nor B := by
    rw [hBeq]
    refine mem_nor_of_gen fun y hy => ?_
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    · rw [hnb]; exact Subgroup.subset_closure (by simp)
    · have := key b₁ (Subgroup.subset_closure (by simp))
      rwa [hBeq] at this
    · have := key b₂ (Subgroup.subset_closure (by simp))
      rwa [hBeq] at this
    · have := key b₃ (Subgroup.subset_closure (by simp))
      rwa [hBeq] at this
  have hz : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b := by
    rw [conjBy_zpowers, hnb]
  exact (hB.stab n hnB hz).2 x hx

theorem conjBy_closure_four (g a c d e : G) :
    conjBy g (Subgroup.closure ({a, c, d, e} : Set G)) =
      Subgroup.closure ({g * a * g⁻¹, g * c * g⁻¹, g * d * g⁻¹, g * e * g⁻¹} : Set G) := by
  rw [conjBy, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

theorem caseII_new {b' : G} {L' B' : Subgroup G} {c₁ c₂ c₃ : G}
    (hB : FF81Basis b' L' B' c₁ c₂ c₃)
    (haut : autOrder B' = 2 ^ 7 * 3 ^ 2 ∨ autOrder B' = 2 ^ 8 * 3 ^ 2) :
    CaseIIa b' B' c₁ c₂ c₃ ∨ CaseIIb b' B' c₁ c₂ c₃ := by
  have hset := conjLines_eq hB
  rcases kf_prop51 G B' b' c₁ c₂ c₃ hB.mono hB.cenOdd hB.stab hB.meet with
    ⟨-, h384, -⟩ | ⟨hm, h, hc, hw⟩ | ⟨hm, h, hc, hw⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
  · rcases haut with h' | h' <;> (norm_num at h'; omega)
  · exact Or.inl ⟨hm, by rw [h]; norm_num, by rw [hset]; exact hc, hw⟩
  · exact Or.inr ⟨hm, by rw [h]; norm_num, by rw [hset]; exact hc, hw⟩
  · rcases haut with h' | h' <;> (norm_num at h'; omega)
  · rcases haut with h' | h' <;> (norm_num at h'; omega)

theorem rerun
    (hMcl : KF_McLaughlin6) (hHolt : KF_HoltThm1) (hP1 : KF_FF81aProp1) (h32 : FF81_3_2)
    (h526p : FF81_5_2_6) (h57 : FF81_5_7)
    (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀)
    (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    ∃ M' : Subgroup G,
      FF81Conc5_2_6 (β' b₂ b₃) (b₂ * b₃) (b * b₁) (b⁻¹ * b₁) t₀ ∧
        FF81Conc5_7 (β' b₂ b₃) (b₂ * b₃) (b * b₁) (b⁻¹ * b₁) t₀ M' := by
  have hB := h5.basis
  have hMmodel := hM7.2.1
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hrk, -, -⟩ :=
    kf_sp6Torus G L hB.hyp.model
  have hyp := ffHyp_new hrk h5 h526 hM7
  obtain ⟨B'', c₁'', c₂'', c₃'', hB''⟩ := h32 kf_sp62Out hP1 G (β' b₂ b₃) M hyp
  have hA₁M := A₁_le_M h526 hM7
  have hc₁M : b₂ * b₃ ∈ M := hA₁M b₂b₃_mem_A₁
  have hc₂M : b * b₁ ∈ M := hA₁M (Subgroup.mul_mem _ b_mem_A₁ b₁_mem_A₁)
  have hc₃M : b⁻¹ * b₁ ∈ M :=
    hA₁M (Subgroup.mul_mem _ (Subgroup.inv_mem _ b_mem_A₁) b₁_mem_A₁)
  have hcEl : IsElemAb 3 3 (Subgroup.closure ({b₂ * b₃, b * b₁, b⁻¹ * b₁} : Set G)) := by
    rw [closure_c_eq h5]; exact isElemAb_A₁ h5
  obtain ⟨x, hxM, hx1, hx2, hx3⟩ := exists_conj_of_monomial_bases hMmodel hB''.hb₁ hB''.hb₂
    hB''.hb₃ hc₁M hc₂M hc₃M hB''.elem hcEl (mono_of_stab hB'') (M_mono h5 h526 hM7)
  have hconj := FF81Basis.conj hB'' hxM
  rw [hx1, hx2, hx3] at hconj
  have hxβ : x * β' b₂ b₃ * x⁻¹ = β' b₂ b₃ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (M_le_cen_β hM7 hxM), mul_inv_cancel_right]
  have hBx : conjBy x B'' = B := by
    rw [hB''.mono.2.1, conjBy_closure_four, hxβ, hx1, hx2, hx3, closure_β_c_eq h5,
      ← h5.basis.mono.2.1]
  rw [hBx] at hconj
  have haut : autOrder B = 2 ^ 7 * 3 ^ 2 ∨ autOrder B = 2 ^ 8 * 3 ^ 2 := by
    rcases h5.caseII with h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2.1
  have hcase := caseII_new hconj haut
  have h5' : FF81Sec5 (β' b₂ b₃) M B (b₂ * b₃) (b * b₁) (b⁻¹ * b₁) s₀ t₀ := by
    refine ⟨hconj, hcase, h5.hs₀, s₀_mem_cenS_M hM7, h5.hs₀b, h5.ht₀, t₀_mem_M h5 hM7, ?_, ?_⟩
    · have hle : Subgroup.closure ({β' b₂ b₃, b₂ * b₃, (b * b₁) * (b⁻¹ * b₁)} : Set G) ≤ L := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl | rfl)
        · exact β_mem_L h5
        · exact L.mul_mem hB.hb₂ hB.hb₃
        · rw [SetLike.mem_coe, c₂_mul_c₃ h5]
          exact L.pow_mem hB.hb₁ 2
      exact Subgroup.centralizer_le hle h5.ht₀L
    · rw [c₂_mul_c₃_sq h5, show t₀ * b⁻¹ * t₀⁻¹ = (t₀ * b * t₀⁻¹)⁻¹ by group, h5.ht₀b]
  have h51 : ControlsFusionIn B := ff81_5_1 G (β' b₂ b₃) M B _ _ _ s₀ t₀ h5'
  have h526' := h526p G (β' b₂ b₃) M B _ _ _ s₀ t₀ h5' h51
  obtain ⟨M', hM7'⟩ := h57 hMcl hHolt G (β' b₂ b₃) M B _ _ _ s₀ t₀ h5' h51 h526'
  exact ⟨M', h526', hM7'⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
