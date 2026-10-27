module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Solv
public import Certificates.Certificate810304
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.LyI301.RowR
public import CFSG.Sporadic.Recognition.LyonsLocalBasic

public noncomputable section

namespace CFSG.Sporadic.LyI301

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.LyonsSims CFSG.Certificates
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301

private theorem lyU_fix_iff : ∀ i : Fin 11, (∀ k, lyU k i = i) ↔ i.val < 3 := by decide +kernel

private theorem fix_of_lyU {i : Fin 11} (hi : ∀ k, lyU k i = i) {σ : Perm (Fin 11)}
    (hσ : σ ∈ lyVS) : σ i = i := by
  have hle : lyVS ≤ MulAction.stabilizer (Perm (Fin 11)) i := by
    rintro _ ⟨v, rfl⟩
    refine Subgroup.list_prod_mem _ fun a ha => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
    exact pow_mem (MulAction.mem_stabilizer_iff.2 (hi k)) _
  exact MulAction.mem_stabilizer_iff.1 (hle hσ)

theorem lt_three_iff_of_normalizes {π : Perm (Fin 11)} (h : ∀ σ ∈ lyVS, π * σ * π⁻¹ ∈ lyVS)
    (h' : ∀ σ ∈ lyVS, π⁻¹ * σ * π ∈ lyVS) (i : Fin 11) : i.val < 3 ↔ (π i).val < 3 := by
  rw [← lyU_fix_iff, ← lyU_fix_iff]
  constructor
  · intro hi k
    have hfix := fix_of_lyU hi (h' (lyU k) (lyU_mem k))
    simp only [Perm.mul_apply] at hfix
    calc lyU k (π i) = π (π⁻¹ (lyU k (π i))) := by simp
      _ = π i := by rw [hfix]
  · intro hi k
    have hfix := fix_of_lyU hi (h (lyU k) (lyU_mem k))
    simp only [Perm.mul_apply] at hfix
    calc lyU k i = π⁻¹ (π (lyU k (π⁻¹ (π i)))) := by simp
      _ = i := by rw [hfix]; simp

theorem exists_eq_lySplit {π : Perm (Fin 11)} (hπ : ∀ i : Fin 11, i.val < 3 ↔ (π i).val < 3) :
    ∃ σ₃ σ₈, π = lySplit σ₃ σ₈ := by
  refine ⟨π.subtypePerm fun i => (hπ i).symm, π.subtypePerm fun i => (not_congr (hπ i)).symm, ?_⟩
  apply Equiv.ext
  intro i
  unfold lySplit
  by_cases hi : i.val < 3
  · rw [Perm.subtypeCongr.apply, dif_pos hi, Perm.subtypePerm_apply]
  · rw [Perm.subtypeCongr.apply, dif_neg hi, Perm.subtypePerm_apply]

variable {G : Type} [Group G] [Finite G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem lyVS_le_alternatingGroup : lyVS ≤ alternatingGroup (Fin 11) := by
  rintro _ ⟨v, rfl⟩
  refine Subgroup.list_prod_mem _ fun a ha => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
  exact pow_mem (mem_alternatingGroup.2 (sign_lyU k)) _

theorem rho_conj_mem_lyVS (D : LyData G t ρ) {h : ↥(centralizer ({t} : Set G))}
    (hh : (h : G) ∈ Subgroup.normalizer (lyR ρ : Set G)) {σ : Perm (Fin 11)} (hσ : σ ∈ lyVS) :
    ρ h * σ * (ρ h)⁻¹ ∈ lyVS := by
  obtain ⟨r, hr⟩ := D.cover.exists_lift (lyVS_le_alternatingGroup hσ)
  have hrR : (r : G) ∈ lyR ρ := mem_lyR.2 ⟨r, hr ▸ hσ, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 hh _).1 hrR
  obtain ⟨r', hr', he⟩ := mem_lyR.1 h1
  have e : r' = h * r * h⁻¹ := Subtype.ext (by simpa using he)
  rw [← hr, ← map_inv, ← map_mul, ← map_mul, ← e]
  exact hr'

theorem lySplit_pow_24 : ∀ σ₃ σ₈, lySplit σ₃ σ₈ * lyX1 = lyX1 * lySplit σ₃ σ₈ →
    (∀ i, lySplit σ₃ σ₈ * lyU i * (lySplit σ₃ σ₈)⁻¹ ∈ lyV) → lySplit σ₃ σ₈ ^ 24 = 1 :=
  Certificates.certificate810304.1

theorem lySplit_inv_facts : ∀ σ₃ σ₈, (∀ i, lySplit σ₃ σ₈ * lyU i * (lySplit σ₃ σ₈)⁻¹ ∈ lyV) →
    lySplit σ₃ σ₈ ∉ lyV → lySplit σ₃ σ₈ * lySplit σ₃ σ₈ ∈ lyV →
    ∃ b ∈ lyConj, lySplit σ₃ σ₈ * (b * lySplit σ₃ σ₈ * b⁻¹) * (lySplit σ₃ σ₈)⁻¹ *
      (b * lySplit σ₃ σ₈ * b⁻¹)⁻¹ ∉ lyV :=
  Certificates.certificate810304.2

theorem pow_48_eq_one (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {g : G}
    (hgx : g * (x₁ : G) = (x₁ : G) * g) (hgN : g ∈ Subgroup.normalizer (lyR ρ : Set G)) :
    g ^ 48 = 1 := by
  have hgt : g ∈ centralizer ({t} : Set G) := normalizer_lyR_le D hgN
  set h : ↥(centralizer ({t} : Set G)) := ⟨g, hgt⟩
  have hhx : ρ h * lyX1 = lyX1 * ρ h := by
    have e : h * x₁ = x₁ * h := Subtype.ext hgx
    have e' := congrArg ρ e
    rw [map_mul, map_mul, S.rho₁] at e'
    exact e'
  have hconj : ∀ σ ∈ lyVS, ρ h * σ * (ρ h)⁻¹ ∈ lyVS := fun σ hσ => rho_conj_mem_lyVS D hgN hσ
  have hconj' : ∀ σ ∈ lyVS, (ρ h)⁻¹ * σ * ρ h ∈ lyVS := fun σ hσ => by
    have hi : ((h⁻¹ : ↥(centralizer ({t} : Set G))) : G) ∈
        Subgroup.normalizer (lyR ρ : Set G) := by
      rw [Subgroup.coe_inv]
      exact Subgroup.inv_mem _ hgN
    have := rho_conj_mem_lyVS D hi hσ
    rwa [map_inv, inv_inv] at this
  obtain ⟨σ₃, σ₈, hsplit⟩ := exists_eq_lySplit (lt_three_iff_of_normalizes hconj hconj')
  have h24 : (ρ h) ^ 24 = 1 := by
    rw [hsplit]
    refine lySplit_pow_24 σ₃ σ₈ (hsplit ▸ hhx) fun i => ?_
    rw [← hsplit]
    exact mem_lyVS_iff.1 (hconj _ (lyU_mem i))
  have hk : h ^ 24 = 1 ∨ h ^ 24 = lyZ t := by
    rw [← map_pow] at h24
    exact (D.cover.mem_ker_iff).1 h24
  have h48 : h ^ 48 = 1 := by
    rw [show (48 : ℕ) = 24 * 2 by norm_num, pow_mul]
    rcases hk with h1 | h1
    · rw [h1, one_pow]
    · rw [h1, pow_two]
      exact D.cover.z_mul_z
  have := congrArg Subtype.val h48
  simpa [h] using this

theorem ly_K (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    rowKOf Row.ly.prime (x₁ : G) (lyR ρ) = ⊥ := by
  haveI : Group.IsSolvable ↥(rowIOf Row.ly.prime (x₁ : G) ⊓
      Subgroup.normalizer (lyR ρ : Set G)) := isSolvable_of_pow_two_mul_three 4 1 fun g => by
    have hgI := CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le Row.ly.prime
      (centralizer ({(x₁ : G)} : Set G)) (Subgroup.mem_inf.1 g.2).1
    have hgx := (Subgroup.mem_centralizer_singleton_iff (G := G)).1 hgI
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_48_eq_one D S hgx (Subgroup.mem_inf.1 g.2).2
  exact glaPLayer_eq_bot_of_isSolvable Nat.prime_three

theorem ly_hK (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    RowK .ly Row.ly.prime (rowKOf Row.ly.prime (x₁ : G) (lyR ρ)) :=
  ly_K D S

end CFSG.Sporadic.LyI301
