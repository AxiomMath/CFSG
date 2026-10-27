module

public import CFSG.Quasithin.H13.L32NLem1444h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem card_img_H (hRest : Lemma14323Rest) :
    Nat.card (D.img (l32nH T V)) = 36 ∨ Nat.card (D.img (l32nH T V)) = 18 := by
  obtain ⟨-, hcases, -, -⟩ := hRest G T L V S.hyp V₂ g S.plane S.gP S.gH D S.dim
  rcases hcases with hi | hii | hiii | hiv
  · obtain ⟨e⟩ := hi.iso
    left
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    rfl
  · exfalso
    have h2 := hii.card_zU
    rw [S.img_zUg, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  · exfalso
    have h2 := hiii.card_zU
    rw [S.img_zUg, Subgroup.card_bot] at h2
    rcases h2 with h2 | h2 <;> omega
  · obtain ⟨N, -, -, hN9, hN2⟩ := hiv.e9
    right
    have h := Subgroup.card_mul_index N
    rw [hN9, hN2] at h
    omega

theorem card_T_le (hRest : Lemma14323Rest) :
    Nat.card T ≤ 4 * Nat.card ↥(pCoreOf 2 (l32nH T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := card_eq_card_imageOTwoQuot_mul (l32nH T V) T S.TH
  rw [inf_eq_right.mpr S.QT] at h1
  have h2 : Nat.card (imageOTwoQuot (l32nH T V) T) ∣
      Nat.card (imageOTwoQuot (l32nH T V) (l32nH T V)) :=
    Subgroup.card_dvd_of_le (Subgroup.map_mono (Subgroup.comap_mono S.TH))
  rw [card_imageOTwoQuot_eq D S.cHat le_rfl] at h2
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp S.hyp.fsu.sylow.1
  have h3 : Nat.card (imageOTwoQuot (l32nH T V) T) ∣ 2 ^ b := by
    rw [← hb, h1]
    exact Dvd.intro _ rfl
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  rw [ha] at h2 h1
  have h4 : 2 ^ a ∣ 4 := by
    rcases card_img_H S hRest with h | h <;> rw [h] at h2
    · exact (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 9)).dvd_of_dvd_mul_right
        (by simpa using h2)
    · have h5 : 2 ^ a ∣ 2 :=
        (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 9)).dvd_of_dvd_mul_right
          (by simpa using h2)
      exact h5.trans (by norm_num)
  have h6 : 2 ^ a ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  rw [h1]
  exact Nat.mul_le_mul_right _ h6

theorem relIndex_R_le (hRest : Lemma14323Rest) {σ : G} (hσT : σ ∈ T)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) :
    (pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ).relIndex T ≤ 2 := by
  have h2 := card_T_le S hRest
  set Q := pCoreOf 2 (l32nH T V)
  set R := Q ⊔ Subgroup.zpowers σ with hR
  have hRT : R ≤ T := sup_le S.QT (Subgroup.zpowers_le.mpr hσT)
  have hQR : Q < R := lt_of_le_of_ne le_sup_left fun h => hσQ (by
    rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
  have hlt : Nat.card Q < Nat.card R := Subgroup.card_lt_of_lt hQR
  have hdvd : Nat.card Q ∣ Nat.card R := Subgroup.card_dvd_of_le hQR.le
  have h2R : 2 * Nat.card Q ≤ Nat.card R := by
    obtain ⟨m, hm⟩ := hdvd
    rw [hm] at hlt ⊢
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have : 1 < m := by
      by_contra h
      push Not at h
      interval_cases m <;> simp_all
    nlinarith
  have h1 := Subgroup.relIndex_mul_card R T
  rw [inf_eq_left.mpr hRT] at h1
  have hpos : 0 < Nat.card R := Nat.card_pos
  by_contra h
  push Not at h
  have : 3 * Nat.card R ≤ R.relIndex T * Nat.card R := Nat.mul_le_mul_right _ h
  omega

theorem mem_Q_or_of_mem_Wg {σ w : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g) :
    w ∈ pCoreOf 2 (l32nH T V) ∨ σ⁻¹ * w ∈ pCoreOf 2 (l32nH T V) := by
  have hσH := S.Wg_le_H hσW
  have hwH := S.Wg_le_H hw
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V))
  have hmem : ∀ x (hx : x ∈ l32nH T V), x ∈ CFSG.conjugate (l32nW T V V₂) g →
      π ⟨x, hx⟩ ∈ imageOTwoQuot (l32nH T V) (CFSG.conjugate (l32nW T V V₂) g) :=
    fun x hx hxW => ⟨⟨x, hx⟩, hxW, rfl⟩
  have hker : ∀ x (hx : x ∈ l32nH T V), π ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 (l32nH T V) := by
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, hyx⟩ => by
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      rwa [← this]⟩
  obtain ⟨u, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(imageOTwoQuot (l32nH T V)
    (CFSG.conjugate (l32nW T V V₂) g)))).mp S.card_Wg
  by_cases hwQ : w ∈ pCoreOf 2 (l32nH T V)
  · exact Or.inl hwQ
  right
  have hσ1 : (⟨π ⟨σ, hσH⟩, hmem σ hσH hσW⟩ : ↥(imageOTwoQuot (l32nH T V) _)) ≠ 1 := fun h =>
    hσQ ((hker σ hσH).mp (congrArg Subtype.val h))
  have hw1 : (⟨π ⟨w, hwH⟩, hmem w hwH hw⟩ : ↥(imageOTwoQuot (l32nH T V) _)) ≠ 1 := fun h =>
    hwQ ((hker w hwH).mp (congrArg Subtype.val h))
  have he := (huniq _ hσ1).trans (huniq _ hw1).symm
  have he' : π ⟨σ, hσH⟩ = π ⟨w, hwH⟩ := congrArg Subtype.val he
  have hk : π (⟨σ, hσH⟩⁻¹ * ⟨w, hwH⟩) = 1 := by rw [map_mul, map_inv, he', inv_mul_cancel]
  exact (hker _ ((l32nH T V).mul_mem ((l32nH T V).inv_mem hσH) hwH)).mp hk

end Setup

end L1444CTL

end CFSG.Quasithin.H13
