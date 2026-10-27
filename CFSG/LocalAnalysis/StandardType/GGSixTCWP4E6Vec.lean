module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Decomp

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem dtilde_full {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (m : Fin 6 → (Fin Tag.E6.rank → ℤ))
    (hnorm : ∀ i, iform (m i) (m i) = 2)
    (h01 : iform (m 0) (m 1) = -1) (h23 : iform (m 2) (m 3) = -1) (h45 : iform (m 4) (m 5) = -1)
    (horth : ∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 → iform (m i) (m j) = 0)
    {D : Type*} [Group D] (v : D → (Fin Tag.E6.rank → ℤ))
    (hmul : ∀ u u' : D, ∀ j, (p : ℤ) ∣ v (u * u') j - v u j - v u' j)
    (hinj : ∀ u : D, (∀ j, (p : ℤ) ∣ v u j) → u = 1)
    (hvan : ∀ u : D, ∀ i : Fin 6, i.val < 4 → (p : ℤ) ∣ ∑ j, m i j * v u j)
    (hcard : Nat.card D = p ^ 2) :
    ∀ s t : ℤ, ∃ u : D, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * v u j) - (s * iform γ (m 4) + t * iform γ (m 5)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdec : ∀ u : D, ∃ s t : ℤ, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * v u j) - (s * iform γ (m 4) + t * iform γ (m 5)) :=
    fun u => pair_decomp_of_frame hp hp5 m hnorm h01 h23 h45 horth (v u)
      (hvan u 0 (by decide)) (hvan u 1 (by decide)) (hvan u 2 (by decide))
      (hvan u 3 (by decide))
  choose s t hst using hdec
  let Phi : D → ZMod p × ZMod p := fun u => ((s u : ZMod p), (t u : ZMod p))
  have hPhi_inj : Function.Injective Phi := by
    intro u u' huu'
    have hs : (s u : ZMod p) = (s u' : ZMod p) := congrArg Prod.fst huu'
    have ht : (t u : ZMod p) = (t u' : ZMod p) := congrArg Prod.snd huu'
    have hs' : (p : ℤ) ∣ s u - s u' :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub (s u') (s u) p).mp hs.symm
    have ht' : (p : ℤ) ∣ t u - t u' :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub (t u') (t u) p).mp ht.symm
    have hγ : ∀ γ : Fin Tag.E6.rank → ℤ,
        (p : ℤ) ∣ (∑ j, γ j * v u j) - (∑ j, γ j * v u' j) := by
      intro γ
      have e : (∑ j, γ j * v u j) - (∑ j, γ j * v u' j)
          = ((∑ j, γ j * v u j) - (s u * iform γ (m 4) + t u * iform γ (m 5)))
            - ((∑ j, γ j * v u' j) - (s u' * iform γ (m 4) + t u' * iform γ (m 5)))
            + ((s u - s u') * iform γ (m 4) + (t u - t u') * iform γ (m 5)) := by ring
      rw [e]
      exact dvd_add (dvd_sub (hst u γ) (hst u' γ))
        (dvd_add (dvd_mul_of_dvd_left hs' _) (dvd_mul_of_dvd_left ht' _))
    have hcoord : ∀ j, (p : ℤ) ∣ v u j - v u' j := by
      intro j
      simpa [Pi.single_apply, ite_mul] using hγ (Pi.single j 1)
    have hw : u * u'⁻¹ * u' = u := inv_mul_cancel_right u u'
    have hz : u * u'⁻¹ = 1 := by
      apply hinj (u * u'⁻¹)
      intro j
      have h1 := hmul (u * u'⁻¹) u' j
      rw [hw] at h1
      have h2 := dvd_sub (hcoord j) h1
      have e : v u j - v u' j - (v u j - v (u * u'⁻¹) j - v u' j) = v (u * u'⁻¹) j := by ring
      rwa [e] at h2
    exact mul_inv_eq_one.mp hz
  have hc : Nat.card (ZMod p × ZMod p) ≤ Nat.card D :=
    le_of_eq (by rw [Nat.card_prod, Nat.card_zmod, hcard, sq])
  have hPhi_surj : Function.Surjective Phi :=
    (Function.Injective.bijective_of_nat_card_le hPhi_inj hc).2
  intro s₀ t₀
  obtain ⟨u, hu⟩ := hPhi_surj ((s₀ : ZMod p), (t₀ : ZMod p))
  have hu1 : (s u : ZMod p) = (s₀ : ZMod p) := congrArg Prod.fst hu
  have hu2 : (t u : ZMod p) = (t₀ : ZMod p) := congrArg Prod.snd hu
  have hs' : (p : ℤ) ∣ s u - s₀ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub s₀ (s u) p).mp hu1.symm
  have ht' : (p : ℤ) ∣ t u - t₀ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub t₀ (t u) p).mp hu2.symm
  refine ⟨u, fun γ => ?_⟩
  have e : (∑ j, γ j * v u j) - (s₀ * iform γ (m 4) + t₀ * iform γ (m 5))
      = ((∑ j, γ j * v u j) - (s u * iform γ (m 4) + t u * iform γ (m 5)))
        + ((s u - s₀) * iform γ (m 4) + (t u - t₀) * iform γ (m 5)) := by ring
  rw [e]
  exact dvd_add (hst u γ) (dvd_add (dvd_mul_of_dvd_left hs' _) (dvd_mul_of_dvd_left ht' _))

end CFSG.StandardType.TableCRes

end
