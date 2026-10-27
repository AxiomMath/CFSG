module

public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ2
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ4
public import CFSG.Quasithin.Vol2.Ch3E213MP6BE

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat uElt antiUnipotent antiUnipotentCenter_comm minorAut)
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj)

variable {k : Type} [Field k] [CharP k 2] [Finite k]

theorem eq_zero_iff_of_mem {I : Subgroup (antiSp k)} (hT : ∀ x ∈ I, ¬ IsTransvection x)
    (hT' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x)) {b c : k} (h : uElt 0 b c 0 ∈ I) :
    b = 0 ↔ c = 0 := by
  constructor
  · rintro rfl
    by_contra hc
    exact hT _ h (isTransvection_zl hc)
  · rintro rfl
    by_contra hb
    refine hT' _ h ?_
    rw [P6B.minorAut_uElt_center]
    exact isTransvection_zl (pow_ne_zero 2 hb)

theorem exists_upper_conj {I : Subgroup (antiSp k)} {g : antiSp k} (hg : IsOppStd g)
    {b₀ c₀ : k} (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hx₀ : uElt 0 b₀ c₀ 0 ∈ I)
    (hy₀ : g * uElt 0 b₀ c₀ 0 * g⁻¹ ∈ I) {b c b' c' : k} (hb : b ≠ 0) (hc : c ≠ 0)
    (hb' : b' ≠ 0) (hc' : c' ≠ 0) (hx : uElt 0 b c 0 ∈ I) (hx' : uElt 0 b' c' 0 ∈ I) :
    ∃ n ∈ I, IsUpper n ∧ n * uElt 0 b c 0 * n⁻¹ = uElt 0 b' c' 0 := by
  have hconj : ∀ (w : antiSp k) (β γ : k),
      w * uElt 0 β γ 0 * w⁻¹ * (w * uElt 0 β γ 0 * w⁻¹) = 1 := fun w β γ => by
    calc w * uElt 0 β γ 0 * w⁻¹ * (w * uElt 0 β γ 0 * w⁻¹) =
        w * (uElt 0 β γ 0 * uElt 0 β γ 0) * w⁻¹ := by group
      _ = 1 := by rw [center_mul_self]; group
  obtain ⟨n₀, hn₀⟩ := exists_pow_conj_eq (center_mul_self b₀ c₀) (hconj g b₀ c₀)
    fun t h1 h2 => eq_one_of_comm_comm hg hb₀ hc₀ hb₀ hc₀ h1 h2
  set z₀ := (uElt 0 b₀ c₀ 0 * (g * uElt 0 b₀ c₀ 0 * g⁻¹)) ^ n₀ with hz₀
  have hz₀I : z₀ ∈ I := I.pow_mem (I.mul_mem hx₀ hy₀) n₀
  have hu₀ : g⁻¹ * z₀ ∈ antiUnipotent k := by
    refine mem_antiUnipotent_of_comm hb₀ hc₀ ?_
    calc g⁻¹ * z₀ * uElt 0 b₀ c₀ 0 = g⁻¹ * (z₀ * uElt 0 b₀ c₀ 0 * z₀⁻¹) * z₀ := by group
      _ = g⁻¹ * (g * uElt 0 b₀ c₀ 0 * g⁻¹) * z₀ := by rw [hn₀]
      _ = uElt 0 b₀ c₀ 0 * (g⁻¹ * z₀) := by group
  have hy : z₀ * uElt 0 b' c' 0 * z₀⁻¹ = g * uElt 0 b' c' 0 * g⁻¹ := by
    have hcomm := antiUnipotentCenter_comm ⟨b', c', rfl⟩ hu₀
    calc z₀ * uElt 0 b' c' 0 * z₀⁻¹ = g * (g⁻¹ * z₀ * uElt 0 b' c' 0) * z₀⁻¹ := by group
      _ = g * (uElt 0 b' c' 0 * (g⁻¹ * z₀)) * z₀⁻¹ := by rw [← hcomm]
      _ = g * uElt 0 b' c' 0 * g⁻¹ := by group
  have hyI : g * uElt 0 b' c' 0 * g⁻¹ ∈ I :=
    hy ▸ I.mul_mem (I.mul_mem hz₀I hx') (I.inv_mem hz₀I)
  obtain ⟨n₁, hn₁⟩ := exists_pow_conj_eq (center_mul_self b c) (hconj g b' c')
    fun t h1 h2 => eq_one_of_comm_comm hg hb hc hb' hc' h1 h2
  set z := (uElt 0 b c 0 * (g * uElt 0 b' c' 0 * g⁻¹)) ^ n₁ with hz
  have hzI : z ∈ I := I.pow_mem (I.mul_mem hx hyI) n₁
  have hn : z₀⁻¹ * z * uElt 0 b c 0 * (z₀⁻¹ * z)⁻¹ = uElt 0 b' c' 0 := by
    calc z₀⁻¹ * z * uElt 0 b c 0 * (z₀⁻¹ * z)⁻¹ = z₀⁻¹ * (z * uElt 0 b c 0 * z⁻¹) * z₀ := by
          group
      _ = z₀⁻¹ * (g * uElt 0 b' c' 0 * g⁻¹) * z₀ := by rw [hn₁]
      _ = z₀⁻¹ * (z₀ * uElt 0 b' c' 0 * z₀⁻¹) * z₀ := by rw [hy]
      _ = uElt 0 b' c' 0 := by group
  exact ⟨z₀⁻¹ * z, I.mul_mem (I.inv_mem hz₀I) hzI, isUpper_of_conj_eq hb hc hb' hc' hn, hn⟩

@[expose] def centreSystem {I : Subgroup (antiSp k)} {g : antiSp k} (hg : IsOppStd g)
    (hT : ∀ x ∈ I, ¬ IsTransvection x) (hT' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x))
    {b₀ c₀ : k} (hb₀ : b₀ ≠ 0) (hx₀ : uElt 0 b₀ c₀ 0 ∈ I)
    (hy₀ : g * uElt 0 b₀ c₀ 0 * g⁻¹ ∈ I) : CentreSystem k where
  P b c := uElt 0 b c 0 ∈ I
  add h h' := by
    have := I.mul_mem h h'
    rwa [center_mul] at this
  zero h := (eq_zero_iff_of_mem hT hT' h).mp rfl
  trans {b c b' c'} h h' hb hb' := by
    have hc : c ≠ 0 := fun h0 => hb ((eq_zero_iff_of_mem hT hT' h).mpr h0)
    have hc' : c' ≠ 0 := fun h0 => hb' ((eq_zero_iff_of_mem hT hT' h').mpr h0)
    have hc₀ : c₀ ≠ 0 := fun h0 => hb₀ ((eq_zero_iff_of_mem hT hT' hx₀).mpr h0)
    obtain ⟨n, hnI, hnU, hn⟩ := exists_upper_conj hg hb₀ hc₀ hx₀ hy₀ hb hc hb' hc' h h'
    have e := P6B.conj_uElt_center hnU b c
    rw [hn] at e
    refine ⟨glMat (n : GL (Fin 4) k) 0 0 * glMat (n : GL (Fin 4) k) 1 1,
      glMat (n : GL (Fin 4) k) 0 0 ^ 2, (uElt_inj e).2.1, (uElt_inj e).2.2.1,
      fun {β γ} hβ => ?_⟩
    have := I.mul_mem (I.mul_mem hnI hβ) (I.inv_mem hnI)
    rwa [P6B.conj_uElt_center hnU] at this
  b₀ := b₀
  c₀ := c₀
  base := hx₀
  b₀_ne := hb₀
  c₀_ne := fun h0 => hb₀ ((eq_zero_iff_of_mem hT hT' hx₀).mpr h0)

end CFSG.Quasithin.Ch3E213M.G41.CTwo
