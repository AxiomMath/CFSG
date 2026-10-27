module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaFourPlusPointStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

namespace OmegaModel

variable {W : Type} [CommGroup W]

theorem smul_inv_eq (S : OmegaModel W) (c : S.K) (w : W) : S.smul c w⁻¹ = (S.smul c w)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← S.smul_mul_eq, mul_inv_cancel, S.smul_one_elem])

theorem Q_ne_zero_of_line (S : OmegaModel W) {g : MulAut W} (hgQ : ∀ w, S.Q (g w) = S.Q w)
    {w : W} (hline : ∀ v, ∃ c : S.K, g v * v⁻¹ = S.smul c w) (hw : ∃ v, g v * v⁻¹ = w)
    (hw0 : w ≠ 1) : S.Q w ≠ 0 := by
  intro hQw
  have key : ∀ (v : W) (c : S.K), g v * v⁻¹ = S.smul c w → c * S.pol w v = 0 := by
    intro v c hc
    have h1 : g v = S.smul c w * v := by rw [← hc, inv_mul_cancel_right]
    have h2 := hgQ v
    rw [h1, S.Q_mul, S.Q_smul, hQw, S.pol_smul_left] at h2
    linear_combination h2
  obtain ⟨v₁, hv₁⟩ := hw
  obtain ⟨v₂, hv₂⟩ : ∃ v₂, S.pol w v₂ ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (S.eq_one_of_pol_eq_zero h)
  obtain ⟨c₂, hc₂⟩ := hline v₂
  have hk1 : S.pol w v₁ = 0 := by
    have := key v₁ 1 (by rw [S.smul_one_eq]; exact hv₁)
    rwa [one_mul] at this
  have hk2 : c₂ = 0 := (mul_eq_zero.mp (key v₂ c₂ hc₂)).resolve_right hv₂
  have h0 : g v₂ * v₂⁻¹ = 1 := by rw [hc₂, hk2, S.smul_zero_eq]
  have h3 : g (v₁ * v₂) * (v₁ * v₂)⁻¹ = S.smul 1 w := by
    rw [S.smul_one_eq, map_mul, mul_inv, mul_mul_mul_comm, hv₁, h0, mul_one]
  have h4 := key (v₁ * v₂) 1 h3
  rw [one_mul, S.pol_mul_right, hk1, zero_add] at h4
  exact hv₂ h4

theorem commHom_mem_line [Finite W] (S : OmegaModel W) {g : MulAut W}
    (hg : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w))
    (hR : Nat.card (CFSG.Quasithin.commHom g).range < Nat.card S.K ^ 2)
    {z v₀ : W} (hv₀ : g v₀ * v₀⁻¹ = z) (hz : z ≠ 1) :
    ∀ v, ∃ c : S.K, g v * v⁻¹ = S.smul c z := by
  have hcs : ∀ (c : S.K) (w : W),
      CFSG.Quasithin.commHom g (S.smul c w) = S.smul c (CFSG.Quasithin.commHom g w) := by
    intro c w
    rw [CFSG.Quasithin.commHom_apply, CFSG.Quasithin.commHom_apply, hg, ← S.smul_inv_eq,
      ← S.smul_mul_eq]
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hcon
  set u := g x * x⁻¹ with hu
  have hZ : S.vec z ≠ 0 := by
    intro h
    apply hz
    apply S.vec_injective
    rw [h, S.vec_one]
  have hmem : ∀ a b : S.K, S.smul a u * S.smul b z ∈ (CFSG.Quasithin.commHom g).range := by
    intro a b
    refine ⟨S.smul a x * S.smul b v₀, ?_⟩
    rw [map_mul, hcs, hcs, CFSG.Quasithin.commHom_apply, CFSG.Quasithin.commHom_apply, hv₀]
  let f : S.K × S.K → (CFSG.Quasithin.commHom g).range := fun p =>
    ⟨S.smul p.1 u * S.smul p.2 z, hmem p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : a • S.vec u + b • S.vec z = a' • S.vec u + b' • S.vec z := by
      have := congrArg (fun y : ↥(CFSG.Quasithin.commHom g).range => S.vec (y : W)) h
      simpa only [f, S.vec_mul, S.vec_smul] using this
    have h2 : (a - a') • S.vec u = (b' - b) • S.vec z := by
      rw [sub_smul, sub_smul]
      calc a • S.vec u - a' • S.vec u
          = (a • S.vec u + b • S.vec z) - (a' • S.vec u + b • S.vec z) := by abel
        _ = (a' • S.vec u + b' • S.vec z) - (a' • S.vec u + b • S.vec z) := by rw [h1]
        _ = b' • S.vec z - b • S.vec z := by abel
    by_cases haa : a = a'
    · subst haa
      rw [sub_self, zero_smul] at h2
      have hb : b' - b = 0 := (smul_eq_zero.mp h2.symm).resolve_right hZ
      rw [sub_eq_zero] at hb
      rw [hb]
    · exfalso
      apply hx ((b' - b) / (a - a'))
      apply S.vec_injective
      rw [S.vec_smul]
      have hne : a - a' ≠ 0 := sub_ne_zero.mpr haa
      calc S.vec u = (a - a')⁻¹ • ((a - a') • S.vec u) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = ((b' - b) / (a - a')) • S.vec z := by
            rw [h2, smul_smul, div_eq_inv_mul]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, ← pow_two] at this
  omega

end OmegaModel

namespace S18

theorem k_K_Omega4Plus_smallComm_holds : K_Omega4Plus_smallComm := by
  intro W _ _ H p n hn2 hO hNat hp hcong t ht ht2 hcard z hz1 hz
  classical
  obtain ⟨F, _, _, hF, ε, ψ, hψ⟩ := exists_natCoords_of_natOmegaPlus hNat
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine k_K_Omega4Plus_nonsingPoint_holds H p n hn2 hO hNat hp hcong F hF ε ψ hψ z ?_
  let S : OmegaModel W := omegaModelOfCoords h4 ψ
  change S.Q z ≠ 0
  have hSH : S.omega = H := by
    refine Subgroup.eq_of_le_of_card_ge (omegaModelOfCoords_omega_le h4 ε ψ hψ) ?_
    have h1 : Nat.card S.omega = Nat.card (StatedOmega (StatedQuadPlus 2 F)) :=
      Subgroup.card_map_of_injective S.actHom_injective
    rw [h1]
    exact (Nat.card_congr ε.toEquiv).le
  have htN : t ∈ OmegaModel.omegaNorm S := by
    show t ∈ Subgroup.normalizer (S.omega : Set (MulAut W))
    rw [hSH]
    exact ht
  have hW : Nat.card W = (2 ^ n) ^ 4 := by
    rw [S.card_eq]
    show Nat.card F ^ 4 = _
    rw [hF]
  have h2n : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hW, h2n] at hcard
  obtain ⟨θ, hθspec, hθker⟩ := OmegaModel.exists_twistHom S
  have hlin : t ∈ OmegaModel.linSub S := by
    rw [← hθker ⟨t, htN⟩]
    by_contra hne
    have h1 := OmegaModel.card_fixed_le_of_semilinear S (σ := θ ⟨t, htN⟩) hne (hθspec ⟨t, htN⟩)
    have h2 : Nat.card (fixV (Subgroup.zpowers t)) = Nat.card {w : W // t w = w} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_fixV_zpowers_iff_apply)
    rw [← h2] at h1
    change _ ≤ Nat.card F ^ 2 at h1
    rw [hF] at h1
    have : (2 ^ n) ^ 2 * (2 ^ n) ^ 2 < (2 ^ n) ^ 2 * (2 ^ n) ^ 2 := by
      calc (2 ^ n) ^ 2 * (2 ^ n) ^ 2 = (2 ^ n) ^ 4 := by ring
        _ < (2 ^ n) ^ 2 * Nat.card (fixV (Subgroup.zpowers t)) := hcard
        _ ≤ (2 ^ n) ^ 2 * (2 ^ n) ^ 2 := Nat.mul_le_mul_left _ h1
    exact lt_irrefl _ this
  have hiso : t ∈ OmegaModel.isoSub S := by
    obtain ⟨s, hs, h, hh, hsh⟩ := (OmegaModel.mem_scalarSub_sup_isoSub_iff S).mp
      (OmegaModel.omegaNorm_inf_linSub_le_sup S ⟨htN, hlin⟩)
    have hhlin : h ∈ OmegaModel.linSub S := ((OmegaModel.mem_isoSub_iff S).mp hh).1
    have hcomm : Commute s h := OmegaModel.scalarSub_commute S hs hhlin
    obtain ⟨k, hk⟩ := ht2
    have htk : t ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one t
    have h1 : s ^ (2 ^ k) * h ^ (2 ^ k) = 1 := by rw [← hcomm.mul_pow, hsh, htk]
    have hsp : s ^ (2 ^ k) = 1 := by
      have h2 : s ^ (2 ^ k) = (h ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hbot : s ^ (2 ^ k) ∈ (⊥ : Subgroup (MulAut W)) := by
        rw [← OmegaModel.scalarSub_inf_isoSub S]
        exact ⟨Subgroup.pow_mem _ hs _, h2 ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ hh _)⟩
      exact Subgroup.mem_bot.mp hbot
    have hsq : s ^ (Nat.card F - 1) = 1 := by
      obtain ⟨c, hc⟩ := hs
      have hc1 : c ^ (Nat.card F - 1) = 1 := by
        rw [← Nat.card_units F]
        exact pow_card_eq_one'
      rw [← hc, ← map_pow, hc1, map_one]
    have hodd : Odd (Nat.card F - 1) := by
      rw [hF]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have hcop : Nat.Coprime (2 ^ k) (Nat.card F - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have hs1 : s = 1 := by
      have hcop' : Nat.Coprime (orderOf s) (Nat.card F - 1) :=
        Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hsp) hcop
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd hcop' (orderOf_dvd_of_pow_eq_one hsq))
    rw [← hsh, hs1, one_mul]
    exact hh
  obtain ⟨hlin', hQt⟩ := (OmegaModel.mem_isoSub_iff S).mp hiso
  obtain ⟨v₀, -, hv₀⟩ : ∃ v₀ ∈ (⊤ : Subgroup W), CFSG.Quasithin.commHom t v₀ = z := by
    rw [CFSG.Quasithin.commSub_zpowers_eq_map (fun _ _ _ _ => Subgroup.mem_top _)] at hz
    exact Subgroup.mem_map.mp hz
  have hWkr : Nat.card W = Nat.card (fixV (Subgroup.zpowers t)) *
      Nat.card (CFSG.Quasithin.commHom t).range := by
    rw [← CFSG.Quasithin.ker_commHom t,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (CFSG.Quasithin.commHom t)).toEquiv,
      mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hR : Nat.card (CFSG.Quasithin.commHom t).range < Nat.card S.K ^ 2 := by
    show _ < Nat.card F ^ 2
    rw [hF]
    rw [hW] at hWkr
    rw [hWkr] at hcard
    have hpos : 0 < Nat.card (fixV (Subgroup.zpowers t)) := Nat.card_pos
    rw [mul_comm ((2 ^ n) ^ 2)] at hcard
    exact Nat.lt_of_mul_lt_mul_left hcard
  rw [CFSG.Quasithin.commHom_apply] at hv₀
  exact S.Q_ne_zero_of_line hQt (S.commHom_mem_line hlin' hR hv₀ hz1) ⟨v₀, hv₀⟩ hz1

end S18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
