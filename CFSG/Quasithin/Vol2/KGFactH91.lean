module

public import CFSG.Quasithin.Vol2.KGFactH91C
public import CFSG.Quasithin.Vol2.Ch12Sec1H91

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Quasithin.SLnTwo CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm

namespace KGH91

variable {G : Type} [Group G] {n : ℕ}

theorem NatCoord.exists_conj_eq {L W : Subgroup G} (C : NatCoord L W n) (hn : 1 ≤ n) {v w : G}
    (hv : v ∈ W) (hw : w ∈ W) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ l : ↥L, (l : G) * v * (l : G)⁻¹ = w := by
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_eq hn fun h => hv1 (C.eq_one_of_E hv h)
  obtain ⟨g₂, hg₂⟩ := exists_mulVec_eq hn fun h => hw1 (C.eq_one_of_E hw h)
  obtain ⟨l, hl⟩ := C.ρ_surj (g₂ * g₁⁻¹)
  have h1 : ((g₁⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      C.E v = Pi.single ⟨0, by omega⟩ 1 := by
    rw [← hg₁, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
  refine ⟨l, C.inj _ (C.conj_mem l hv) w hw ?_⟩
  rw [C.conj l v hv, hl, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hg₂]

theorem graph_mulVec_of_vecMul {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    {f y : Fin n → ZMod 2} (h : f ᵥ* (g : Matrix (Fin n) (Fin n) (ZMod 2)) = y) :
    (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y = f := by
  rw [slGraphAut_matrix, Matrix.mulVec_transpose, ← h, Matrix.vecMul_vecMul, coe_mul_inv,
    Matrix.vecMul_one]

theorem exists_normal_form (hn : 2 ≤ n) {x f : Fin n → ZMod 2} (hx : x ≠ 0) (hf : f ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single ⟨0, by omega⟩ 1 = x ∧
        (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          (if f ⬝ᵥ x = 1 then Pi.single ⟨0, by omega⟩ 1 else Pi.single ⟨n - 1, by omega⟩ 1) =
            f := by
  by_cases h : f ⬝ᵥ x = 1
  · obtain ⟨g, hg, hgf⟩ := exists_nonincident (by omega) hx h
    refine ⟨g, hg, ?_⟩
    rw [ite_eq_left h]
    exact graph_mulVec_of_vecMul hgf
  · have h0 : f ⬝ᵥ x = 0 := (zmod_two_cases _).resolve_right h
    obtain ⟨g, hg, hgf⟩ := exists_incident hn hx hf h0
    refine ⟨g, hg, ?_⟩
    rw [ite_eq_right h]
    exact graph_mulVec_of_vecMul hgf

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} (S : Setting G T L V V₁ V₂ n)
include S

theorem nonsing_iff {a c : G} (ha : a ∈ V₁) (hc : c ∈ V₂) :
    IsNonsingular121 V₁ V₂ (pairing S.C₁ S.C₂) (a * c) ↔ pairing S.C₁ S.C₂ a c = 1 := by
  constructor
  · rintro ⟨a', ha', c', hc', h, h1⟩
    obtain ⟨rfl, rfl⟩ := S.decomp_unique ha ha' hc hc' h
    exact h1
  · intro h
    exact ⟨a, ha, c, hc, rfl, h⟩

theorem mem_union_iff {a c : G} (ha : a ∈ V₁) (hc : c ∈ V₂) :
    (a * c ∈ V₁ ∨ a * c ∈ V₂) ↔ (a = 1 ∨ c = 1) := by
  constructor
  · rintro (h | h)
    · right
      have h1 : c ∈ V₁ ⊓ V₂ := ⟨by
        have := V₁.mul_mem (V₁.inv_mem ha) h
        rwa [inv_mul_cancel_left] at this, hc⟩
      rw [S.hyp.inf, Subgroup.mem_bot] at h1
      exact h1
    · left
      have h1 : a ∈ V₁ ⊓ V₂ := ⟨ha, by
        have := V₂.mul_mem h (V₂.inv_mem hc)
        rwa [mul_inv_cancel_right] at this⟩
      rw [S.hyp.inf, Subgroup.mem_bot] at h1
      exact h1
  · rintro (rfl | rfl)
    · right
      rw [one_mul]
      exact hc
    · left
      rw [mul_one]
      exact ha

theorem exists_pair {a c a' c' : G} (ha : a ∈ V₁) (hc : c ∈ V₂) (ha' : a' ∈ V₁) (hc' : c' ∈ V₂)
    (ha1 : a ≠ 1) (hc1 : c ≠ 1) (ha1' : a' ≠ 1) (hc1' : c' ≠ 1)
    (hβ : pairing S.C₁ S.C₂ a c = pairing S.C₁ S.C₂ a' c') :
    ∃ l ∈ L, l * a * l⁻¹ = a' ∧ l * c * l⁻¹ = c' := by
  have hn : 2 ≤ n := by have := S.hn; omega
  have hβ' : S.C₂.E c ⬝ᵥ S.C₁.E a = S.C₂.E c' ⬝ᵥ S.C₁.E a' := by
    rw [dotProduct_comm, dotProduct_comm (S.C₂.E c')]
    exact hβ
  obtain ⟨g, hg, hgf⟩ := exists_normal_form hn (fun h => ha1 (S.C₁.eq_one_of_E ha h))
    (fun h => hc1 (S.C₂.eq_one_of_E hc h))
  obtain ⟨g', hg', hgf'⟩ := exists_normal_form hn (fun h => ha1' (S.C₁.eq_one_of_E ha' h))
    (fun h => hc1' (S.C₂.eq_one_of_E hc' h))
  rw [hβ'] at hgf
  obtain ⟨l, hl⟩ := S.C₁.ρ_surj (g' * g⁻¹)
  refine ⟨l, l.2, S.C₁.inj _ (S.C₁.conj_mem l ha) a' ha' ?_,
    S.C₂.inj _ (S.C₂.conj_mem l hc) c' hc' ?_⟩
  · have h1 : ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        S.C₁.E a = Pi.single ⟨0, by omega⟩ 1 := by
      rw [← hg, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
    rw [S.C₁.conj l a ha, hl, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hg']
  · have h1 : (((slGraphAut n (ZMod 2) g)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ S.C₂.E c =
          (if S.C₂.E c' ⬝ᵥ S.C₁.E a' = 1 then Pi.single ⟨0, by omega⟩ 1
            else Pi.single ⟨n - 1, by omega⟩ 1) := by
      rw [← hgf, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
    rw [S.C₂.conj l c hc, S.dual, hl, _root_.map_mul, _root_.map_inv,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hgf']

theorem exists_conj_union {v w : G} (hv : v ∈ V₁ ∨ v ∈ V₂) (hw : w ∈ V₁ ∨ w ∈ V₂)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ = w := by
  have hn : 1 ≤ n := by have := S.hn; omega
  obtain ⟨m₀, hm₀, hs₁, hs₂⟩ := S.exists_swap
  have hu1 : m₀ * v * m₀⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = m₀⁻¹ * (m₀ * v * m₀⁻¹) * m₀ := by group
      _ = 1 := by rw [h]; group
  have lift : ∀ {u : G} (m : G), m ∈ Subgroup.normalizer (L : Set G) →
      (∃ l : ↥L, (l : G) * (m * u * m⁻¹) * (l : G)⁻¹ = w) →
        ∃ m' ∈ Subgroup.normalizer (L : Set G), m' * u * m'⁻¹ = w := by
    rintro u m hm ⟨l, h⟩
    exact ⟨l * m, Subgroup.mul_mem _ (Subgroup.le_normalizer l.2) hm, by rw [← h]; group⟩
  have hv1' : 1 * v * 1⁻¹ ≠ 1 := by rwa [one_mul, inv_one, mul_one]
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · refine lift 1 (Subgroup.one_mem _) (S.C₁.exists_conj_eq hn ?_ hw hv1' hw1)
    rwa [one_mul, inv_one, mul_one]
  · exact lift m₀ hm₀ (S.C₂.exists_conj_eq hn ((hs₁ v).1 hv) hw hu1 hw1)
  · exact lift m₀ hm₀ (S.C₁.exists_conj_eq hn ((hs₂ v).1 hv) hw hu1 hw1)
  · refine lift 1 (Subgroup.one_mem _) (S.C₂.exists_conj_eq hn ?_ hw hv1' hw1)
    rwa [one_mul, inv_one, mul_one]

theorem orbit_iff {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    (∃ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ = w) ↔
      (((v ∈ V₁ ∨ v ∈ V₂) ↔ (w ∈ V₁ ∨ w ∈ V₂)) ∧
        (IsNonsingular121 V₁ V₂ (pairing S.C₁ S.C₂) v ↔
          IsNonsingular121 V₁ V₂ (pairing S.C₁ S.C₂) w)) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hv
    have e : m * (a * c) * m⁻¹ = (m * a * m⁻¹) * (m * c * m⁻¹) := by group
    have h1 : ∀ x, m * x * m⁻¹ = 1 ↔ x = 1 := fun x => by
      constructor
      · intro h
        calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
          _ = 1 := by rw [h]; group
      · rintro rfl
        group
    rcases S.fix_or_swap hm with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have ha' : m * a * m⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 h₁ a).1 ha
      have hc' : m * c * m⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 h₂ c).1 hc
      rw [e, S.mem_union_iff ha hc, S.mem_union_iff ha' hc', S.nonsing_iff ha hc,
        S.nonsing_iff ha' hc', S.pairing_conj hm h₁ h₂ a ha c hc, h1, h1]
      exact ⟨Iff.rfl, Iff.rfl⟩
    · have ha' : m * a * m⁻¹ ∈ V₂ := (h₁ a).1 ha
      have hc' : m * c * m⁻¹ ∈ V₁ := (h₂ c).1 hc
      have e' : (m * a * m⁻¹) * (m * c * m⁻¹) = (m * c * m⁻¹) * (m * a * m⁻¹) :=
        S.comm (S.le₂ ha') (S.le₁ hc')
      rw [e, e', S.mem_union_iff ha hc, S.mem_union_iff hc' ha', S.nonsing_iff ha hc,
        S.nonsing_iff hc' ha', S.pairing_conj_swap hm h₁ h₂ a ha c hc, h1, h1]
      exact ⟨or_comm, Iff.rfl⟩
  · rintro ⟨hU, hN⟩
    by_cases hvU : v ∈ V₁ ∨ v ∈ V₂
    · exact S.exists_conj_union hvU (hU.1 hvU) hv1 hw1
    · have hwU : ¬ (w ∈ V₁ ∨ w ∈ V₂) := fun h => hvU (hU.2 h)
      obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hv
      obtain ⟨a', ha', c', hc', rfl⟩ := S.exists_decomp hw
      rw [S.mem_union_iff ha hc, not_or] at hvU
      rw [S.mem_union_iff ha' hc', not_or] at hwU
      rw [S.nonsing_iff ha hc, S.nonsing_iff ha' hc'] at hN
      have hβ : pairing S.C₁ S.C₂ a c = pairing S.C₁ S.C₂ a' c' := by
        rcases zmod_two_cases (pairing S.C₁ S.C₂ a c) with h0 | h1
        · rcases zmod_two_cases (pairing S.C₁ S.C₂ a' c') with h0' | h1'
          · rw [h0, h0']
          · exact absurd (hN.2 h1') (by rw [h0]; exact zero_ne_one)
        · rw [h1, hN.1 h1]
      obtain ⟨l, hl, hla, hlc⟩ :=
        S.exists_pair ha hc ha' hc' hvU.1 hvU.2 hwU.1 hwU.2 hβ
      refine ⟨l, Subgroup.le_normalizer hl, ?_⟩
      have e : l * (a * c) * l⁻¹ = (l * a * l⁻¹) * (l * c * l⁻¹) := by group
      rw [e, hla, hlc]

end Setting

end KGH91

theorem lemH91_holds : LemH91 := by
  intro G _ _ T L V V₁ V₂ n hyp hTL
  obtain ⟨S⟩ := KGH91.Setting.nonempty hyp
  refine ⟨KGH91.exists_zpowers hyp hTL S.C₁, KGH91.pairing S.C₁ S.C₂,
    KGH91.isDualPairing S.C₁ S.C₂ S.dual, ?_⟩
  intro v hv w hw hv1 hw1
  exact S.orbit_iff hv hw hv1 hw1

end CFSG.Quasithin.H13
