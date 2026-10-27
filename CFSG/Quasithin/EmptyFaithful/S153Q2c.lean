module

public import CFSG.Quasithin.EmptyFaithful.S153Q2a
public import CFSG.Quasithin.EmptyFaithful.S153Q2b
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q2

theorem not_dvd_prod {k : ℕ} (hk : k ≤ 5) : ¬ 1080 ∣ ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  interval_cases k <;> decide

theorem not_dvd_card_mulAut {K : Type} [Group K] [Finite K] (hcomm : ∀ a b : K, a * b = b * a)
    (hpow : ∀ a : K, a ^ 2 = 1) {k : ℕ} (hk : k ≤ 5) (hcard : Nat.card K = 2 ^ k) :
    ¬ 1080 ∣ Nat.card (MulAut K) := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  exact not_dvd_prod hk

end Q2

theorem hat_z_fpf {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    (hWc : Nat.card W = 2 ^ 6) {Γ Ah : Subgroup (MulAut W)} {z : MulAut W} (hG : HatGrp Γ Ah z) :
    ∀ w : W, z w = w → w = 1 := by
  intro w0 hw0
  by_contra hne
  have hinv : ∀ g ∈ Ah, ∀ v ∈ Q2.kerN z, g v ∈ Q2.kerN z ∧ g⁻¹ v ∈ Q2.kerN z := fun g hg v hv =>
    ⟨Q2.kerN_invariant (hG.z_central g hg) hv,
      Q2.kerN_invariant (Commute.inv_left (show Commute g z from hG.z_central g hg)) hv⟩
  have hfaith : ∀ g ∈ Ah, g ∈ Q2.fixK (Q2.kerN z) → g = 1 := by
    have hJ := Q2.eq_bot_of_normal hG (Ah ⊓ Q2.fixK (Q2.kerN z)) inf_le_left ?_
      (fun hzJ => hG.z_ne (Q2.z_eq_one_of_fix hW2 hG.z_cube hzJ.2))
    · intro g hg hgf
      have : g ∈ Ah ⊓ Q2.fixK (Q2.kerN z) := ⟨hg, hgf⟩
      rw [hJ] at this
      exact Subgroup.mem_bot.1 this
    · intro g hg j hj
      refine ⟨Ah.mul_mem (Ah.mul_mem hg hj.1) (Ah.inv_mem hg), fun w hw => ?_⟩
      have h1 : g⁻¹ w ∈ Q2.kerN z := (hinv g hg w hw).2
      show g (j (g⁻¹ w)) = w
      rw [hj.2 _ h1]
      simp
  have hdvd : Nat.card ↥Ah ∣ Nat.card (MulAut ↥(Q2.kerN z)) :=
    Subgroup.card_dvd_of_injective (Q2.restHom (Q2.kerN z) Ah hinv)
      (Q2.restHom_injective _ _ hinv hfaith)
  have hKdvd : Nat.card ↥(Q2.kerN z) ∣ 2 ^ 6 := by
    rw [← hWc]; exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk6, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKdvd
  have hk5 : k ≤ 5 := by
    by_contra h
    have h6 : k = 6 := by omega
    have htop : Q2.kerN z = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hkc, h6, hWc]
    have hw0K : w0 ∈ Q2.kerN z := htop ▸ Subgroup.mem_top w0
    exact hne (Q2.fixed_of_mem_kerN hW2 hw0 hw0K)
  have hpow : ∀ a : ↥(Q2.kerN z), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using hW2 a)
  rw [hG.card] at hdvd
  exact Q2.not_dvd_card_mulAut (fun a b => mul_comm a b) hpow hk5 hkc hdvd

end S153Q

end CFSG.Quasithin
