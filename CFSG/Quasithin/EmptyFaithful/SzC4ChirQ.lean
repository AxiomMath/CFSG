module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirLayer
public import CFSG.Quasithin.EmptyFaithful.SBd5UL
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.SzC4

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem chiMat_dual (A : ChiAPI) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (x : Matrix.GeneralLinearGroup (Fin 3) F) (h7 : x ^ 7 = 1) :
    A.chiMat (moduleAct true x) = - A.chiMat (moduleAct false x) := by
  have hB7 : (moduleAct false x) ^ 7 = 1 := by
    unfold moduleAct
    simp only [Bool.false_eq_true, ite_false]
    rw [← Units.val_pow_eq_pow_val, h7]
    simp
  have hinv : ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((x : Matrix (Fin 3) (Fin 3) F)) ^ 6 := by
    have : x⁻¹ = x ^ 6 := by
      rw [inv_eq_iff_mul_eq_one, ← h7]
      group
    rw [this, Units.val_pow_eq_pow_val]
  have := A.chiMat_inv_transpose hF (moduleAct false x) hB7
  unfold moduleAct at this ⊢
  simp only [Bool.false_eq_true, ite_false, ite_true] at this ⊢
  rw [hinv]
  exact this

theorem chiC_c134Q_eq_zero (A : ChiAPI) {H S K : Subgroup G} (hq : IsLnTwoQuot K 3)
    (hcase : MS93.IsC134Case4Corr H S K) (hQ2 : IsPGroup 2 ↥(c134Q H K)) {g : G} (hg : g ∈ K)
    (hg7 : g ^ 7 = 1) : chiC A (c134Q H K) g = 0 := by
  obtain ⟨⟨n, F, iF, iFin, α, hcard, hα, -, hcen, hdisj, h1, h2, h3, h4⟩, -⟩ := hcase
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hcard hα
  set Q := c134Q H K with hQ
  set Zq := centerOf Q with hZq
  set C := c134CQ H K with hC
  set U : Subgroup G := ⁅centerOf Q, K⁆ with hU
  have hZQ : Zq ≤ Q := inf_le_left
  have hCZ : C ≤ Zq := hcen ▸ le_sup_left
  have hUZ : U ≤ Zq := hcen ▸ le_sup_right
  have hΦQ : frattiniIn Q ≤ Q := Subgroup.map_subtype_le _
  have hC2Q : Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G) ≤ Q := inf_le_left
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := h4.1 hg
  have hgU : g ∈ Subgroup.normalizer (U : Set G) := h1.1 hg
  have hgΦ : g ∈ Subgroup.normalizer (frattiniIn Q : Set G) := h2.1 hg
  have hgZ : g ∈ Subgroup.normalizer (Zq : Set G) := normalizes_of_isSum h2 hg
  have hgC2 : g ∈ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G) : Subgroup G)
      : Set G) := h3.1 hg
  have hCcent : ∀ c ∈ C, g * c * g⁻¹ = c := by
    intro c hc
    have := Subgroup.mem_centralizer_iff.1 hc.2 g hg
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [this]
      _ = c := by group
  have hgC : g ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [hCcent c hc]
      exact hc
    · intro hc
      have h := hCcent _ hc
      have h' : g * c * g⁻¹ = c := by
        calc g * c * g⁻¹ = g⁻¹ * (g * (g * c * g⁻¹) * g⁻¹) * g := by group
          _ = g⁻¹ * (g * c * g⁻¹) * g := by rw [h]
          _ = c := by group
      rw [h'] at hc
      exact hc
  have hcomm : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c := by
    intro c hc u hu
    have hcZ : c ∈ Subgroup.centralizer (Q : Set G) := (hCZ hc).2
    have huQ : u ∈ Q := hZQ (hUZ hu)
    exact (Subgroup.mem_centralizer_iff.1 hcZ u huQ).symm
  have e4 := chiC_layer A hF h4 hQ2 hg hg7
  have e3 := chiC_layer A hF h3 (hQ2.to_le hC2Q) hg hg7
  have e2 := chiC_layer A hF h2 (hQ2.to_le hΦQ) hg hg7
  have e1 := chiC_layer A hF h1 (hQ2.to_le (hUZ.trans hZQ)) hg hg7
  have hsplit := chiC_split A (hQ2.to_le hZQ) hCZ hUZ hcomm hdisj hcen.symm hgZ hgC hgU hg7
  rw [chiC_bot A g] at e1
  rw [chiC_of_centralizes A C hgC hCcent] at hsplit
  have hg7' : α ⟨g, hg⟩ ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥K) ^ 7 = 1 := Subtype.ext (by simpa using hg7)
    rw [this, map_one]
  have hd := chiMat_dual A hF (α ⟨g, hg⟩ : Matrix.GeneralLinearGroup (Fin 3) F)
    (by simpa using congrArg Subtype.val hg7')
  rw [hd] at e3 e2
  push_cast at e4 e3 e2 e1
  linarith

end CFSG.Quasithin.SzC4
