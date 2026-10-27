module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_bstar_centralizes_center {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hCen : GGQ2S08BigCenterInput) :
    ∀ b ∈ Bs, ∀ z ∈ Subgroup.center ↥L, (b : G) * ((z : ↥L) : G) = ((z : ↥L) : G) * b := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hInn
  obtain ⟨hp, hBs, hxBs, hLx, h4⟩ := hS.1.1.tableB_facts
  obtain ⟨R, iR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hSimple, hNonAb, θ, hP⟩ := hQ
  have hBig : GGQ2S08BigLabel lab := hP.1.2
  have hCenAll : LargeEvenLabelAll lab (fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card (Subgroup.center L') ∣ 3) :=
    hCen lab hlab hBig
  have hraw2 := hCenAll _ hraw
  obtain ⟨R₂, iR₂, I₂, F₂, hQ₂⟩ := largeEvenRawDatum_exists hraw2
  obtain ⟨hQ₂_orig, hQ₂_center⟩ := hQ₂
  obtain ⟨-, -, θ₂, hP₂⟩ := hQ₂_orig
  have hZ_dvd : Nat.card (Subgroup.center ↥L) ∣ 3 := by
    refine hQ₂_center ↥L (θ₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) ?_ ?_ hperf
    ·
      intro r
      obtain ⟨x, hx⟩ := θ₂.surjective r
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
      refine ⟨y, ?_⟩
      rw [MonoidHom.comp_apply, hy]
      exact hx
    ·
      have hker : (θ₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))).ker =
          Subgroup.center ↥L := by
        rw [MonoidHom.ker_comp_of_injective _ _ θ₂.injective]
        exact QuotientGroup.ker_mk' (Subgroup.center ↥L)
      rw [hker]
  intro b hb z hz
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hP.2.2.1 hb
  have hb3 : b ^ 3 = 1 := hBs.2 b hb
  by_cases hz1 : ((z : ↥L) : G) = 1
  · rw [hz1, mul_one, one_mul]
  have hZ3 : Nat.card (Subgroup.center ↥L) = 3 := by
    rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hZ_dvd with h1 | h3
    · exfalso
      have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hzbot : z ∈ (⊥ : Subgroup ↥L) := by rwa [← hZbot]
      simp only [Subgroup.mem_bot] at hzbot
      have : ((z : ↥L) : G) = 1 := by simp [hzbot]
      exact hz1 this
    · exact h3
  let zG : G := ((z : ↥L) : G)
  have hb_conj : b * zG * b⁻¹ ∈ L := by
    have := ((Subgroup.mem_normalizer_iff.mp hbN) zG).mp z.2
    simpa [zG] using this
  let z' : ↥L := ⟨b * zG * b⁻¹, hb_conj⟩
  have hz'_center : z' ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hb_inv_conj : b⁻¹ * ((l : ↥L) : G) * b ∈ L := by
      have hb_inv_N : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hbN
      have := ((Subgroup.mem_normalizer_iff.mp hb_inv_N) ((l : ↥L) : G)).mp l.2
      simpa using this
    let l' : ↥L := ⟨b⁻¹ * ((l : ↥L) : G) * b, hb_inv_conj⟩
    have hz_comm : zG * ((l' : ↥L) : G) = ((l' : ↥L) : G) * zG := by
      have := Subgroup.mem_center_iff.mp hz l'
      have := congrArg (fun x : ↥L => ((x : G))) this
      simpa [zG] using this.symm
    calc
      ((l : ↥L) : G) * (b * zG * b⁻¹)
          = ((l : ↥L) : G) * b * zG * b⁻¹ := by group
      _ = b * ((b⁻¹ * ((l : ↥L) : G) * b) * zG) * b⁻¹ := by group
      _ = b * (zG * (b⁻¹ * ((l : ↥L) : G) * b)) * b⁻¹ := by rw [hz_comm.symm]
      _ = b * zG * b⁻¹ * ((l : ↥L) : G) := by group
  have hz_order : orderOf z = 3 := by
    have hsub : Subgroup.zpowers z ≤ Subgroup.center ↥L := by
      rw [Subgroup.zpowers_le]
      exact hz
    have hdiv : Nat.card (Subgroup.zpowers z) ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.card_dvd_of_le hsub
    rw [hZ3] at hdiv
    have hne : Nat.card (Subgroup.zpowers z) ≠ 1 := by
      intro h
      have hbot : Subgroup.zpowers z = ⊥ := Subgroup.eq_bot_of_card_eq _ h
      have hz_bot : z ∈ (⊥ : Subgroup ↥L) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers z
      simp only [Subgroup.mem_bot] at hz_bot
      exact hz1 (congrArg (fun x : ↥L => ((x : G))) hz_bot)
    have hprime : Nat.Prime 3 := by norm_num
    rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hdiv with h1 | h3
    · exact absurd h1 hne
    · rw [← Nat.card_zpowers]
      exact h3
  have hzpow_eq : Subgroup.zpowers z = Subgroup.center ↥L := by
    have hsub : Subgroup.zpowers z ≤ Subgroup.center ↥L := by
      rw [Subgroup.zpowers_le]
      exact hz
    have hcard : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers]
      exact hz_order
    exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hZ3])
  have hz'_in : z' ∈ Subgroup.zpowers z := by
    rw [hzpow_eq]
    exact hz'_center
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'_in
  have hz3 : z ^ 3 = 1 := by
    rw [← hz_order]
    exact pow_orderOf_eq_one z
  have hzG3 : zG ^ 3 = 1 := by
    have := congrArg (fun x : ↥L => ((x : G))) hz3
    simpa [zG] using this
  have hkmod : z' = z ^ (k % 3) := by
    rw [← hk]
    have h3 : ((3 : ℕ) : ℤ) = (orderOf z : ℤ) := by rw [hz_order]
    have hm := zpow_mod_orderOf z k
    rw [← h3] at hm
    simpa using hm.symm
  have hkmod_cases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hkmod_cases with h0 | h1 | h2
  ·
    have hz'_one : z' = 1 := by
      rw [hkmod, h0]
      simp
    have hzG_one : zG = 1 := by
      have := congrArg (fun x : ↥L => ((x : G))) hz'_one
      simp only [Subgroup.coe_one] at this
      calc zG = b⁻¹ * (b * zG * b⁻¹) * b := by group
        _ = b⁻¹ * 1 * b := by simpa [z'] using congrArg (fun x : G => b⁻¹ * x * b) this
        _ = 1 := by group
    exact absurd hzG_one hz1
  ·
    have hz'_eq : z' = z := by
      apply Subtype.ext
      rw [hkmod, h1]
      simp
    have hzG_eq : b * zG * b⁻¹ = zG := by
      have := congrArg (fun x : ↥L => ((x : G))) hz'_eq
      simpa [z'] using this
    calc b * zG = b * zG * b⁻¹ * b := by group
      _ = zG * b := by rw [hzG_eq]
  ·
    have hz'_sq : z' = z ^ 2 := by
      rw [hkmod, h2]
      simp
    have hconj : b * zG * b⁻¹ = zG ^ 2 := by
      have := congrArg (fun x : ↥L => ((x : G))) hz'_sq
      simpa [z', zG] using this
    have h1 : MulAut.conj b zG = zG ^ 2 := by
      simpa [MulAut.conj_apply] using hconj
    have h2' : MulAut.conj b (zG ^ 2) = zG := by
      rw [map_pow, h1, ← pow_mul]
      calc zG ^ (2 * 2) = zG ^ 3 * zG := by rw [← pow_succ]
        _ = zG := by rw [hzG3, one_mul]
    have hcb3 : MulAut.conj b (MulAut.conj b (MulAut.conj b zG)) = zG := by
      have hpow : (MulAut.conj b : MulAut G) ^ 3 = 1 := by
        rw [← map_pow, hb3, map_one]
      have h := congrArg (fun f : MulAut G => f zG) hpow
      simpa [pow_succ, MulAut.mul_apply] using h
    rw [h1, h2', h1] at hcb3
    have hmul : zG * zG = zG * 1 := by
      rw [mul_one, ← pow_two]
      exact hcb3
    exact absurd (mul_left_cancel hmul) hz1

end CFSG.StandardType

end
