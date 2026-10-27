module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0U2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddPSLCard
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Loc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
open CFSG.Blueprint (LieModel)
open scoped Pointwise

theorem r95_u3_p_subgroup_le_rootU {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : p ^ f % 3 = 1)
    {R : Subgroup (SU (unitaryInvolution F p f) 3)} (hR : IsPGroup p R) (hR1 : R ≠ ⊥)
    (hdR : tSU hF ω ∈ Subgroup.normalizer (R : Set (SU (unitaryInvolution F p f) 3))) :
    R ≤ rootU hF ∨ R.map (MulAut.conj (sSU : SU (unitaryInvolution F p f) 3)).toMonoidHom ≤ rootU hF
    := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    exact absurd hω (by norm_num)
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (SU (unitaryInvolution F p f) 3) (rootSylow hF) P
  have hroot : (rootSylow hF : Subgroup (SU (unitaryInvolution F p f) 3)) = rootU hF := rfl
  have hgsub : MulAut.conj g • (rootU hF : Subgroup (SU (unitaryInvolution F p f) 3)) =
      (P : Subgroup (SU (unitaryInvolution F p f) 3)) := by
    rw [← hroot]
    simpa [Sylow.coe_subgroup_smul] using
      congrArg (fun S : Sylow p (SU (unitaryInvolution F p f) 3) =>
        (S : Subgroup (SU (unitaryInvolution F p f) 3))) hg
  have hgsub' : MulAut.conj g⁻¹ • (P : Subgroup (SU (unitaryInvolution F p f) 3)) = rootU hF := by
    rw [← hgsub, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hconj : ∀ x ∈ (P : Subgroup (SU (unitaryInvolution F p f) 3)), g⁻¹ * x * g ∈ rootU hF := by
    intro x hxP
    have hx : MulAut.conj g⁻¹ • x ∈
        MulAut.conj g⁻¹ • (P : Subgroup (SU (unitaryInvolution F p f) 3)) :=
      Subgroup.smul_mem_pointwise_smul x (MulAut.conj g⁻¹) P hxP
    rw [hgsub'] at hx
    simpa [MulAut.smul_def, MulAut.conj_apply] using hx
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
  let aG : SU (unitaryInvolution F p f) 3 := a
  have haG1 : aG ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hu : g⁻¹ * aG * g ∈ rootU hF := hconj aG (hRP a.2)
  have hu1 : g⁻¹ * aG * g ≠ 1 := by
    intro h1
    apply haG1
    have e : aG = g * (g⁻¹ * aG * g) * g⁻¹ := by group
    rw [e, h1]; group
  have hh : (g⁻¹ * (tSU hF ω)⁻¹ * g)⁻¹ * (g⁻¹ * aG * g) * (g⁻¹ * (tSU hF ω)⁻¹ * g) ∈
      bSU (unitaryInvolution F p f) := by
    rw [show (g⁻¹ * (tSU hF ω)⁻¹ * g)⁻¹ * (g⁻¹ * aG * g) * (g⁻¹ * (tSU hF ω)⁻¹ * g)
        = g⁻¹ * (tSU hF ω * aG * (tSU hF ω)⁻¹) * g from by group]
    exact rootU_le_bSU hF
      (hconj _ (hRP ((Subgroup.mem_normalizer_iff.1 hdR aG).1 a.2)))
  have hfix : g⁻¹ * (tSU hF ω)⁻¹ * g ∈ bSU (unitaryInvolution F p f) := fix_B hF hu hu1 hh
  have hh' : g⁻¹ * tSU hF ω * g ∈ bSU (unitaryInvolution F p f) := by
    have := (bSU (unitaryInvolution F p f)).inv_mem hfix
    rwa [show (g⁻¹ * (tSU hF ω)⁻¹ * g)⁻¹ = g⁻¹ * tSU hF ω * g from by group] at this
  have hmat : mat (unitaryInvolution F p f) 3 (tSU hF ω) * mat (unitaryInvolution F p f) 3 g =
      mat (unitaryInvolution F p f) 3 g * mat (unitaryInvolution F p f) 3 (g⁻¹ * tSU hF ω * g) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 3 * m + 1 := ⟨p ^ f / 3, by omega⟩
  have d11 : ((ω ^ (p ^ f - 1) : Fˣ) : F) = 1 := by
    rw [hm, Nat.add_sub_cancel, pow_mul, hω3, one_pow, Units.val_one]
  have d22 : (((ω ^ (p ^ f))⁻¹ : Fˣ) : F) = ((ω⁻¹ : Fˣ) : F) := by
    rw [hm, pow_succ, pow_mul, hω3, one_pow, one_mul]
  rw [mat_tSU hF ω, d11, d22] at hmat
  have hbc : (1 : F) ≠ ((ω⁻¹ : Fˣ) : F) := fun h => hω1 (by
    have : ω⁻¹ = 1 := Units.ext h.symm
    simpa using this)
  have hac : (ω : F) ≠ ((ω⁻¹ : Fˣ) : F) := fun h => hω1 (by
    have h' : ω = ω⁻¹ := Units.ext h
    have h2 : ω ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 h'
    have h3 : ω ^ 3 = ω * ω ^ 2 := pow_succ' ω 2
    rw [h2, mul_one, hω3] at h3
    exact h3.symm)
  rcases fixCol_of_conj_diag hac hbc hh' hmat with ⟨h1, h2⟩ | ⟨h1, h0⟩
  · left
    intro x hxR
    have hxu : g⁻¹ * x * g ∈ rootU hF := hconj x (hRP hxR)
    have := conj_mem_rootU_of_mem_bSU hF
      (show g ∈ bSU (unitaryInvolution F p f) from ⟨h1, h2⟩) hxu
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group] at this
  · right
    rintro y ⟨x, hxR, rfl⟩
    have hxu : g⁻¹ * x * g ∈ rootU hF := hconj x (hRP hxR)
    have := conj_mem_rootU_of_mem_bSU hF (sSU_mul_mem_bSU h1 h0) hxu
    rwa [show (sSU * g) * (g⁻¹ * x * g) * (sSU * g)⁻¹ = sSU * x * sSU⁻¹ from by group] at this

theorem r95_u3_centralizer_le_of_seven {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    (hst : CFSG.Open.StatedClassicalModel (SU (unitaryInvolution F p f) 3) .PSU 3 p f) (hp2 : p ≠ 2)
    (hq3 : p ^ f % 3 = 1) (hq7 : p ^ f = 7)
    {ω : Fˣ} (hω : orderOf ω = 3) {W : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hNW : normA0 hF ω ≤ W) (hW : W ≠ ⊤) (hns : ¬ Group.IsSolvable W)
    {R : Subgroup (SU (unitaryInvolution F p f) 3)} (hRW : R ≤ W) (hR : IsPGroup p R) (hR1 : R ≠ ⊥)
    (hdR : tSU hF ω ∈ Subgroup.normalizer (R : Set (SU (unitaryInvolution F p f) 3))) :
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) ≤ W := by
  have hTW : (tSU hF).range ≤ W := (range_tSU_le_normA0 hF hω hq3).trans hNW
  have hsW : (sSU : SU (unitaryInvolution F p f) 3) ∈ W :=
    hNW ((mem_normalizer_a0_iff hF hω hq3 sSU).2 (Or.inr ⟨1, one_mem _, (one_mul _).symm⟩))
  have hmapW : R.map (MulAut.conj (sSU : SU (unitaryInvolution F p f) 3)).toMonoidHom ≤ W := by
    rintro y ⟨x, hx, rfl⟩
    exact W.mul_mem (W.mul_mem hsW (hRW hx)) (W.inv_mem hsW)
  have hSne : W ⊓ rootU hF ≠ ⊥ := by
    rcases r95_u3_p_subgroup_le_rootU hF hω hq3 hR hR1 hdR with h | h
    · intro hbot
      exact hR1 (eq_bot_iff.2 (hbot ▸ le_inf hRW h))
    · intro hbot
      have hmapbot : R.map (MulAut.conj (sSU : SU (unitaryInvolution F p f) 3)).toMonoidHom = ⊥ :=
        eq_bot_iff.2 (hbot ▸ le_inf hmapW h)
      exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R
        (MulAut.conj (sSU : SU (unitaryInvolution F p f) 3)).injective).1 hmapbot)
  have hSt : ∀ μ ∈ rootsOfUnity (p ^ f + 1) F, ∀ x ∈ W ⊓ rootU hF,
      tSU hF μ * x * (tSU hF μ)⁻¹ ∈ W ⊓ rootU hF := by
    intro μ _ x hx
    have ht : tSU hF μ ∈ W := hTW ⟨μ, rfl⟩
    exact ⟨W.mul_mem (W.mul_mem ht hx.1) (W.inv_mem ht), tSU_conj_mem_rootU hF μ hx.2⟩
  rcases eq_top_or_ca_eq_zero hF hq3 (inf_le_right : W ⊓ rootU hF ≤ rootU hF) hSt with h | h
  · exact absurd (isSolvable_of_rootU_le hF hst (h ▸ inf_le_left) hW) hns
  · have hSL : W ⊓ rootU hF ≤ W ⊓ (embSU (unitaryInvolution F p f)).range := by
      intro x hx
      exact ⟨hx.1, zU_le_range_embSU hF ((mem_zU hF).2 ⟨hx.2, h x hx⟩)⟩
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
    have hSp : IsPGroup p ↥(W ⊓ rootU hF) := (isPGroup_rootU hF).to_le inf_le_right
    have hpdvd : p ∣ orderOf a := IsPGroup.dvd_orderOf hSp ha1
    have hpdvdL : p ∣ Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) := by
      have hdvd : orderOf (a : SU (unitaryInvolution F p f) 3) ∣
          Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) :=
        Subgroup.orderOf_dvd_natCard _ (hSL a.2)
      rw [← Subgroup.orderOf_coe a] at hpdvd
      exact hpdvd.trans hdvd
    have hp7 : p = 7 := by
      have hf0 : f ≠ 0 := fun h0 => by
        have h2 := two_le_prime_pow_of_card hF
        rw [h0, pow_zero] at h2
        omega
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_seven).1
        (hq7 ▸ dvd_pow_self p hf0)
    have h7dvdL : 7 ∣ Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) :=
      hp7 ▸ hpdvdL
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    have hcount := card_inf_range_embSU_eq hζ0 hζ hF hp2 W hTW
    rw [hcount] at h7dvdL
    have h7dvdV : 7 ∣ Nat.card ((W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f))) :=
      (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 7 2)) h7dvdL
    have hA : Subgroup.normalizer (Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3)))) ≤
        (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) :=
      (normalizer_psl_le_map_comap hζ0 hζ hF hω hq3).trans
        (Subgroup.map_mono (Subgroup.comap_mono hNW))
    have h6 : 6 ∣ Nat.card ((W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f))) := by
      have hdvd := Subgroup.card_dvd_of_le hA
      rw [card_normalizer_psl hζ0 hζ hF hω hq3 hp2, hq7] at hdvd
      exact hdvd
    have hK7 : Nat.card (fixedSubfield F p f) = 7 := by rw [card_fixedSubfield hF, hq7]
    have htop : (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) = ⊤ :=
      r95_psl2_seven_eq_top hK7 h6 h7dvdV
    have hLW : (embSU (unitaryInvolution F p f)).range ≤ W :=
      r95_u3_levi_le_of_psl_top hF hp2 hζ0 hζ hTW htop
    rw [centralizer_zSU hF hp2]
    exact sup_le hLW hTW

theorem r95_u3_eq_centralizer {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    [IsSimpleGroup (SU (unitaryInvolution F p f) 3)]
    (hst : CFSG.Open.StatedClassicalModel (SU (unitaryInvolution F p f) 3) .PSU 3 p f)
    (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1) {ω : Fˣ} (hω : orderOf ω = 3)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    (hW : W ≠ ⊤) (hns : ¬ Group.IsSolvable W)
    (hcase : 13 ≤ p ^ f ∨ (p ^ f = 7 ∧ ∃ R : Subgroup (SU (unitaryInvolution F p f) 3), R ≤ W ∧
    IsPGroup p R ∧ R ≠ ⊥ ∧
      tSU hF ω ∈ Subgroup.normalizer (R : Set (SU (unitaryInvolution F p f) 3)))) :
    W = Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) := by
  have hU : rootU hF ≤ W → W = ⊤ :=
    fun hUW => (hns (isSolvable_of_rootU_le hF hst hUW hW)).elim
  have hCW : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) ≤ W := by
    rcases hcase with h13 | ⟨hq7, R, hRW, hR, hR1, hdR⟩
    · exact r95_u3_centralizer_le_of_not_isSolvable hF hp2 hq3 h13 hω hNW hns
    · exact r95_u3_centralizer_le_of_seven hF hst hp2 hq3 hq7 hω hNW hW hns hRW hR hR1 hdR
  exact r95_u3_eq_centralizer_of_le hF hp2 hq3 hCW hU hW

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
