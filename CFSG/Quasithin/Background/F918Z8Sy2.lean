module

public import CFSG.Quasithin.Background.F918Z8Sy2a
public import CFSG.Quasithin.Background.F918Z8Sy2b
public import CFSG.Quasithin.Background.F918Z8Sy2c
public import CFSG.Quasithin.Background.B1More8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem sxi_clifford (hexp : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)}
    (hAel : IsElemAbelian2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y))) {t : MulAut Y}
    (htX : ∀ x ∈ X, t * x = x * t) (htA : ∀ a ∈ A, t * a = a * t)
    {I J : Subgroup Y} (hJI : J < I) (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J)
    (hAI : A ≤ stabSub I) (hAJ : A ≤ stabSub J) (htI : ∀ w ∈ I, t w ∈ I) (htJ : ∀ w ∈ J, t w ∈ J)
    (hirrΞ : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
      (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I)
    (hnotX : ∃ T : Subgroup Y, J ≤ T ∧ T ≤ I ∧ (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) ∧ T ≠ J ∧ T ≠ I) :
    ∃ (I₀ : Subgroup Y) (A₁ : Subgroup (MulAut Y)), J < I₀ ∧ I₀ ≤ I ∧ X ≤ stabSub I₀ ∧
      (∀ T : Subgroup Y, J ≤ T → T ≤ I₀ → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) → T = J ∨ T = I₀) ∧
      A₁ ≤ A ∧ A₁ ≤ stabSub I₀ ∧ (∀ a ∈ A, a ∈ stabSub I₀ → a ∈ A₁) ∧
      ((A₁ = A ∧ I₀ < I ∧
          2 * rkIdx (fixV (autSec A I₀ J)) ≤ rkIdx (fixV (autSec A I J))) ∨
        (A₁ < A ∧ (2 ^ (rk A - rk A₁) - 1) * rk (Sec I₀ J) + rkIdx (fixV (autSec A₁ I₀ J)) ≤
          rkIdx (fixV (autSec A I J)))) := by
  classical
  have _ := htA
  have hJI' : J ≤ I := hJI.le
  have hXK : X ≤ stabSub I ⊓ stabSub J := le_inf hXI hXJ
  have hAK : A ≤ stabSub I ⊓ stabSub J := le_inf hAI hAJ
  have htK : t ∈ stabSub I ⊓ stabSub J := ⟨sxc_mem_stabSub htI, sxc_mem_stabSub htJ⟩
  have hAΛ : ∀ a ∈ autSec A I J, ∀ l ∈ autSec X I J, a * l * a⁻¹ ∈ autSec X I J := by
    intro a ha l hl
    obtain ⟨g, hgA, rfl⟩ := (Bridge.mem_autSec_iff_secHom hAK).1 ha
    obtain ⟨k, hkX, rfl⟩ := (Bridge.mem_autSec_iff_secHom hXK).1 hl
    have hmem : (g : MulAut Y) * (k : MulAut Y) * (g : MulAut Y)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 (hAX hgA) _).1 hkX
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (Bridge.mem_autSec_iff_secHom hXK).2 ⟨g * k * g⁻¹, hmem, rfl⟩
  have hτΛ : ∀ l ∈ autSec X I J,
      Bridge.secHom I J ⟨t, htK⟩ * l = l * Bridge.secHom I J ⟨t, htK⟩ := by
    intro l hl
    obtain ⟨k, hkX, rfl⟩ := (Bridge.mem_autSec_iff_secHom hXK).1 hl
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (htX _ hkX))
  obtain ⟨L, hL, hLtop, hcases⟩ := sxc_cliff_mod (sq_eq_one_sec hexp I J)
    (isElemAbelian2_autSec I J hAel) hAΛ hτΛ
    (fun T' hX hA ht' => sxc_irr_Q hJI' hXK hAK htK hirrΞ T' hX hA ht')
    (sxc_notX_Q hXK hJI' hnotX)
  have hΛL : autSec X I J ≤ stabSub L := le_stabSub_of_forall_mem ((isInv_iff _ L).1 hL.1)
  have hJI₀ : J < d321f_secPre I J L := sxc_lt_secPre hJI' hL.2.1.ne'
  have hI₀I : d321f_secPre I J L ≤ I := d321f_secPre_le L
  refine ⟨d321f_secPre I J L, A ⊓ stabSub (d321f_secPre I J L), hJI₀, hI₀I,
    (sxc_le_stab_iff hXK L).2 hΛL,
    fun T hJT hTI₀ hXT => sxc_xirr_secPre hXI hXJ hL T hJT hTI₀ hXT,
    inf_le_left, inf_le_right, fun a ha h => ⟨ha, h⟩, ?_⟩
  rcases hcases with ⟨hA₁, hdouble⟩ | ⟨hA₁lt, hcount⟩
  · have hAI₀ : A ≤ stabSub (d321f_secPre I J L) := (sxc_le_stab_iff hAK L).2 (inf_eq_left.1 hA₁)
    refine Or.inl ⟨inf_eq_left.2 hAI₀, sxc_secPre_lt hLtop, ?_⟩
    rw [sxc_nB_secPre hAI hAJ L hAI₀, sxc_nB_top] at hdouble
    exact hdouble
  · have hAI₀ : ¬ A ≤ stabSub (d321f_secPre I J L) := fun h =>
      hA₁lt.ne (inf_eq_left.2 ((sxc_le_stab_iff hAK L).1 h))
    refine Or.inr ⟨lt_of_le_of_ne inf_le_left fun h => hAI₀ (inf_eq_left.1 h), ?_⟩
    set I₀ := d321f_secPre I J L with hI₀
    rw [← sxc_autSec_inf_stab hAK L] at hcount
    have hA₁I : A ⊓ stabSub I₀ ≤ stabSub I := inf_le_left.trans hAI
    have hA₁J : A ⊓ stabSub I₀ ≤ stabSub J := inf_le_left.trans hAJ
    have hcent : (A ⊓ stabSub I₀) ⊓ centSec I J = A ⊓ centSec I J := by
      ext g
      simp only [Subgroup.mem_inf]
      exact ⟨fun ⟨⟨hA, _⟩, hc⟩ => ⟨hA, hc⟩,
        fun ⟨hA, hc⟩ => ⟨⟨hA, sxc_centSec_le_stab hJI₀.le hI₀I hc⟩, hc⟩⟩
    have r1 := sxc_rk_autSec_add hA₁I hA₁J
    have r2 := sxc_rk_autSec_add hAI hAJ
    rw [hcent] at r1
    have e4 : rk (autSec A I J) - rk (autSec (A ⊓ stabSub I₀) I J) =
        rk A - rk ↥(A ⊓ stabSub I₀) := by
      omega
    rw [e4, sxc_nB_secPre hA₁I hA₁J L inf_le_right, sxc_nB_top, sxc_rk_secPre I J L] at hcount
    exact hcount

end

end CFSG.Quasithin
