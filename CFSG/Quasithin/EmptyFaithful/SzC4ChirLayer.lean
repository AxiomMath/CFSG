module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirConj
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem moduleAct_pow_seven {K : Subgroup G} {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} (α : ↥K →* ↥Γ) (dual : Bool) {a : G}
    (ha : a ∈ K) (h7 : a ^ 7 = 1) :
    (moduleAct dual (α ⟨a, ha⟩ : Matrix.GeneralLinearGroup (Fin 3) F)) ^ 7 = 1 := by
  have h1 : (α ⟨a, ha⟩ : Matrix.GeneralLinearGroup (Fin 3) F) ^ 7 = 1 := by
    have : α ⟨a, ha⟩ ^ 7 = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥K) ^ 7 = 1 := Subtype.ext (by simpa using h7)
      rw [this, map_one]
    exact congrArg (fun x : ↥Γ => (x : Matrix.GeneralLinearGroup (Fin 3) F)) this
  unfold moduleAct
  split_ifs
  · rw [← Matrix.transpose_pow, ← Units.val_pow_eq_pow_val, inv_pow, h1]
    simp
  · rw [← Units.val_pow_eq_pow_val, h1]
    simp

omit [Finite G] in
theorem normalizes_of_isSum {A V Z : Subgroup G} {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia A V Z α dual k) {a : G} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer (Z : Set G) := by
  obtain ⟨hAV, hZV, β, hβs, hβk, hβe⟩ := h
  have key : ∀ b ∈ A, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z := by
    intro b hb z hz
    have hzV : z ∈ V := hZV hz
    have hbV : b * z * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hAV hb) z).1 hzV
    have h1 : β ⟨z, hzV⟩ = 1 := by
      have : (⟨z, hzV⟩ : ↥V) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact hz
      exact this
    have h2 : β ⟨b * z * b⁻¹, hbV⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [hβe ⟨b, hb⟩ ⟨z, hzV⟩ ⟨b * z * b⁻¹, hbV⟩ rfl i, h1]
      simp
    have : (⟨b * z * b⁻¹, hbV⟩ : ↥V) ∈ β.ker := h2
    rw [hβk, Subgroup.mem_subgroupOf] at this
    exact this
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key a ha z
  · intro hz
    have := key a⁻¹ (A.inv_mem ha) _ hz
    simpa [mul_assoc] using this

theorem chiC_layer (A : ChiAPI) {K V Z : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)}
    {α : ↥K →* ↥Γ} {dual : Bool} {k : ℕ} (h : IsSumOfNaturalModulesVia K V Z α dual k)
    (hV : IsPGroup 2 ↥V) {a : G} (ha : a ∈ K) (h7 : a ^ 7 = 1) :
    chiC A V a = chiC A Z a +
      (k : ℤ) * A.chiMat (moduleAct dual (α ⟨a, ha⟩ : Matrix.GeneralLinearGroup (Fin 3) F)) := by
  have hgZ := normalizes_of_isSum h ha
  obtain ⟨hKV, hZV, β, hβs, hβk, hβe⟩ := h
  have hgV : a ∈ Subgroup.normalizer (V : Set G) := hKV ha
  have hB7 := moduleAct_pow_seven α dual ha h7
  have hker : ∀ y : ↥V, β y = 1 ↔ (y : G) ∈ Z := by
    intro y
    rw [← Subgroup.mem_subgroupOf, ← hβk]
    rfl
  rw [chiC_exact A hV hZV hgV hgZ h7 β hβs hker (A.vecAut k _ hB7) ?_]
  · rw [A.chi_vecAut hF k _ hB7]
  · intro y
    apply Multiplicative.toAdd.injective
    funext i
    rw [A.vecAut_apply]
    exact hβe ⟨a, ha⟩ y (conjOn V a hgV y) rfl i

end CFSG.Quasithin.SzC4
