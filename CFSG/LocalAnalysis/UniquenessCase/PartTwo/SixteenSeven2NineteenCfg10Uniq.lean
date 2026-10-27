module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Ker
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {X Fs : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}

theorem s16c167_cfg10_cent_of_ker (F : Cfg10Mod X Fs I₁ I₂) {I : Subgroup W}
    (hI : I = I₁ ∨ I = I₂) {s : MulAut W} (hsX : s ∈ X) (hs2 : s * s = 1)
    (hsI : I ≤ fixV (Subgroup.zpowers s)) (hQ : ∀ q ∈ Fs ⊓ centSub I, s * q = q * s) :
    s = 1 := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsfix : ∀ w ∈ I, s w = w := fun w hw => (mem_fixV_zpowers_iff_apply).mp (hsI hw)
  have hcomm : ∀ f ∈ Fs, s * f = f * s := by
    intro f hf
    have hfstab : f ∈ stabSub I := by
      rcases hI with rfl | rfl
      · exact (s16c167_cfg10_stab F hf).1
      · exact (s16c167_cfg10_stab F hf).2
    have hfinvstab : f⁻¹ ∈ stabSub I := (stabSub I).inv_mem hfstab
    have haFs : s * f * s⁻¹ ∈ Fs := F.norm s hsX f hf
    have hcFs : (s * f * s⁻¹) * f⁻¹ ∈ Fs := Fs.mul_mem haFs (Fs.inv_mem hf)
    have hcCent : (s * f * s⁻¹) * f⁻¹ ∈ centSub I := by
      rw [mem_centSub]
      intro w hw
      have hfw : f⁻¹ w ∈ I := (mem_stabSub.mp hfinvstab w).mpr hw
      simp only [MulAut.mul_apply]
      rw [hsinv, hsfix (f⁻¹ w) hfw, MulAut.apply_inv_self, hsfix w hw]
    have hQc := hQ ((s * f * s⁻¹) * f⁻¹) (Subgroup.mem_inf.mpr ⟨hcFs, hcCent⟩)
    have hcs : s * ((s * f * s⁻¹) * f⁻¹) * s⁻¹ = (s * f * s⁻¹) * f⁻¹ := by
      rw [hQc]
      group
    have hsas : s * (s * f * s⁻¹) * s⁻¹ = f := by
      rw [hsinv]
      calc s * (s * f * s) * s = (s * s) * f * (s * s) := by group
        _ = f := by rw [hs2, one_mul, mul_one]
    have hsinv' : s * f⁻¹ * s⁻¹ = (s * f * s⁻¹)⁻¹ := by group
    have hkey : s * ((s * f * s⁻¹) * f⁻¹) * s⁻¹ = f * (s * f * s⁻¹)⁻¹ := by
      calc s * ((s * f * s⁻¹) * f⁻¹) * s⁻¹
          = (s * (s * f * s⁻¹) * s⁻¹) * (s * f⁻¹ * s⁻¹) := by group
        _ = f * (s * f * s⁻¹)⁻¹ := by rw [hsas, hsinv']
    have hca : (s * f * s⁻¹) * f⁻¹ = f * (s * f * s⁻¹)⁻¹ := by
      rw [← hcs, hkey]
    have hz2 : ((s * f * s⁻¹) * f⁻¹) * ((s * f * s⁻¹) * f⁻¹) = 1 := by
      nth_rewrite 2 [hca]
      group
    have hz3 : ((s * f * s⁻¹) * f⁻¹) * ((s * f * s⁻¹) * f⁻¹) *
        ((s * f * s⁻¹) * f⁻¹) = 1 :=
      s16c167_cfg10_F_pow F.el ((s * f * s⁻¹) * f⁻¹) hcFs
    have hz1 : (s * f * s⁻¹) * f⁻¹ = 1 := by
      have h : ((s * f * s⁻¹) * f⁻¹) * ((s * f * s⁻¹) * f⁻¹) *
          ((s * f * s⁻¹) * f⁻¹) = (s * f * s⁻¹) * f⁻¹ := by rw [hz2, one_mul]
      rw [h] at hz3
      exact hz3
    have haf : s * f * s⁻¹ = f := by
      calc s * f * s⁻¹ = (s * f * s⁻¹) * f⁻¹ * f := by group
        _ = 1 * f := by rw [hz1]
        _ = f := one_mul f
    have hsf : s * f = f * s := by
      have h := congrArg (· * s) haf
      calc s * f = (s * f * s⁻¹) * s := by group
        _ = f * s := h
    exact hsf
  have hsFs : s ∈ Fs := F.self s hsX hcomm
  have hs3 : s * s * s = 1 := s16c167_cfg10_F_pow F.el s hsFs
  have h : s * s * s = s := by rw [hs2, one_mul]
  rw [h] at hs3
  exact hs3

theorem s16c167_cfg10_inv_ker (F : Cfg10Mod X Fs I₁ I₂) {I : Subgroup W}
    (hI : I = I₁ ∨ I = I₂) {t : MulAut W} (htX : t ∈ X) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htI : I ≤ fixV (Subgroup.zpowers t)) : ∀ q ∈ Fs ⊓ centSub I, t * q * t⁻¹ = q⁻¹ := by
  set Q : Subgroup (MulAut W) := Fs ⊓ centSub I with hQ
  have hQcard : Nat.card ↥Q = 3 := s16c167_cfg10_ker_card F hI
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htfix : ∀ w ∈ I, t w = w := fun w hw => (mem_fixV_zpowers_iff_apply).mp (htI hw)
  have htQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro q hq
    rw [hQ] at hq ⊢
    rw [Subgroup.mem_inf] at hq ⊢
    refine ⟨F.norm t htX q hq.1, ?_⟩
    rw [mem_centSub]
    intro w hw
    simp only [MulAut.mul_apply]
    rw [htinv, htfix w hw, (mem_centSub.mp hq.2) w hw, htfix w hw]
  have hSbot : Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) = ⊥ := by
    by_contra hne
    have hSle : Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) ≤ Q := inf_le_left
    have hSne1 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W))) ≠ 1 := by
      intro h
      exact hne (Subgroup.card_eq_one.mp h)
    have hSdvd : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W))) ∣ 3 :=
      hQcard ▸ Subgroup.card_dvd_of_le hSle
    have hScard : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W))) = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hSdvd with h | h
      · exact absurd h hSne1
      · exact h
    have hSQ : Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) = Q := by
      refine Subgroup.eq_of_le_of_card_ge hSle ?_
      omega
    have hQt : ∀ q ∈ Q, t * q = q * t := by
      intro q hq
      have hqS : q ∈ Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) := by
        rw [hSQ]; exact hq
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hqS).2) t
        (Set.mem_singleton t)
    exact ht1 (s16c167_cfg10_cent_of_ker F hI htX ht2 htI hQt)
  intro q hq
  by_cases hq1 : q = 1
  · subst hq1
    group
  · have hxfix : t * (q * (t * q * t⁻¹)) * t⁻¹ = q * (t * q * t⁻¹) := by
      have h1 : t * (q * (t * q * t⁻¹)) * t⁻¹ = (t * q * t⁻¹) * q := by
        rw [htinv]
        calc t * (q * (t * q * t)) * t = t * q * t * q * (t * t) := by group
          _ = t * q * t * q := by rw [ht2, mul_one]
          _ = (t * q * t) * q := by group
      rw [h1]
      exact s16c167_cfg10_F_comm F.el (t * q * t⁻¹)
        (Subgroup.mem_inf.mp (htQ q hq)).1 q (Subgroup.mem_inf.mp hq).1
    have hxmem : q * (t * q * t⁻¹) ∈ Q ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) := by
      refine Subgroup.mem_inf.mpr ⟨Q.mul_mem hq (htQ q hq), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h := congrArg (· * t) hxfix
      simpa [mul_assoc] using h
    rw [hSbot, Subgroup.mem_bot] at hxmem
    exact (inv_eq_of_mul_eq_one_right hxmem).symm

theorem s16c167_cfg10_uniq19 (F : Cfg10Mod X Fs I₁ I₂) : Uniq19 X (conjSubs X I₁) := by
  intro t₁ ht₁X t₂ ht₂X ht₁ ht₂ hcomm hne₁ hne₂ I hI hf₁ hf₂
  have hI' : I = I₁ ∨ I = I₂ := by
    rw [F.orb] at hI
    simpa using hI
  have hinv₁ := s16c167_cfg10_inv_ker F hI' ht₁X ht₁ hne₁ hf₁
  have hinv₂ := s16c167_cfg10_inv_ker F hI' ht₂X ht₂ hne₂ hf₂
  have hsX : t₁ * t₂ ∈ X := X.mul_mem ht₁X ht₂X
  have hs2 : (t₁ * t₂) * (t₁ * t₂) = 1 := by
    calc (t₁ * t₂) * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by group
      _ = t₁ * (t₁ * t₂) * t₂ := by rw [hcomm]
      _ = (t₁ * t₁) * (t₂ * t₂) := by group
      _ = 1 := by rw [ht₁, ht₂, one_mul]
  have hsI : I ≤ fixV (Subgroup.zpowers (t₁ * t₂)) := by
    intro y hy
    rw [mem_fixV_zpowers_iff_apply]
    show (t₁ * t₂) y = y
    rw [MulAut.mul_apply, (mem_fixV_zpowers_iff_apply).mp (hf₂ hy),
      (mem_fixV_zpowers_iff_apply).mp (hf₁ hy)]
  have hQ : ∀ q ∈ Fs ⊓ centSub I, (t₁ * t₂) * q = q * (t₁ * t₂) := by
    intro q hq
    have hq' : q⁻¹ ∈ Fs ⊓ centSub I := (Fs ⊓ centSub I).inv_mem hq
    have h2 : t₂ * q * t₂⁻¹ = q⁻¹ := hinv₂ q hq
    have h1 : t₁ * q⁻¹ * t₁⁻¹ = q⁻¹⁻¹ := hinv₁ q⁻¹ hq'
    calc (t₁ * t₂) * q = t₁ * (t₂ * q * t₂⁻¹) * t₂ := by group
      _ = t₁ * q⁻¹ * t₂ := by rw [h2]
      _ = (t₁ * q⁻¹ * t₁⁻¹) * (t₁ * t₂) := by group
      _ = q * (t₁ * t₂) := by rw [h1, inv_inv]
  have hmul : t₁ * t₂ = 1 := s16c167_cfg10_cent_of_ker F hI' hsX hs2 hsI hQ
  calc t₁ = t₁ * (t₂ * t₂) := by rw [ht₂, mul_one]
    _ = (t₁ * t₂) * t₂ := by rw [mul_assoc]
    _ = t₂ := by rw [hmul, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
