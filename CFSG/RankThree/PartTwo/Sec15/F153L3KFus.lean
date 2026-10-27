module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KFusTorus
public import CFSG.RankThree.PartTwo.Sec15.F153L3KFusReg
public import CFSG.RankThree.PartTwo.Sec15.F153L3KFusGT
public import CFSG.RankThree.PartTwo.Sec15.F153L3KFusModel
public import CFSG.RankThree.PartTwo.Sec15.ThmDDefs

public section

section FusMain


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Fus

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.RankThreeEven (projImage)

open CFSG.Assembly.LowTwoRank (StatedScalars)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open CFSG.RankThree.PartTwo.Sec15.Proof1513Res2
open CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEV CFSG.RankThree.PartTwo.Sec15.F153L3K.FusTor CFSG.RankThree.PartTwo.Sec15.F153L3K.FusCF

theorem exists_beta {π : Bool} {f f₀ : ℕ} {K : Type} [Field K] (hK : PiField π 2 f K)
    (hq : ModThree π (2 ^ f)) (hf : f = 3 * f₀) {σ : K ≃+* K} (hσ3 : orderOf σ = 3)
    (hσ : (∀ c, σ c = c ^ piCard π (2 ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (2 ^ f₀) ^ 2))
    {ω : K} (hω3 : ω ^ 3 = 1) (hσω : σ ω = ω) (k : ℕ) :
    ∃ β : Kˣ, (π = false → β ^ (2 ^ f + 1) = 1) ∧ (β : K) = ω ^ k * σ (β : K) := by
  haveI := hK.finite
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω3
  have hωk3 : (ω ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hσωk : σ (ω ^ k) = ω ^ k := by rw [map_pow, hσω]
  cases π with
  | true =>
    obtain ⟨β, hβ0, hβ⟩ := CFSG.RankThree.PartTwo.Sec15.F153L3K.FusH90.exists_hilbert90_cube σ hσ3 hωk3 hσωk
    exact ⟨Units.mk0 β hβ0, fun h => absurd h (by simp), hβ⟩
  | false =>
    have h23 : (2 ^ f₀) ^ 3 = 2 ^ f := by rw [← pow_mul, hf, mul_comm]
    have hcard : Nat.card K = ((2 ^ f₀) ^ 3) ^ 2 := by
      rw [hK.card]
      show (2 ^ f) ^ 2 = _
      rw [h23]
    have hσ' : (∀ c, σ c = c ^ ((2 ^ f₀) ^ 2)) ∨ ∀ c, σ c = c ^ ((2 ^ f₀) ^ 4) := by
      rcases hσ with h | h
      · exact Or.inl h
      · refine Or.inr fun c => ?_
        rw [h c]
        show c ^ (((2 ^ f₀) ^ 2) ^ 2) = _
        rw [← pow_mul]
    have h3dvd : 3 ∣ (2 ^ f₀) ^ 3 + 1 := by
      rw [h23]
      have := hq
      simp only [ModThree, Bool.cond_false] at this
      omega
    obtain ⟨m, hm⟩ := h3dvd
    let ωu : Kˣ := Units.mk0 (ω ^ k) (pow_ne_zero k hω0)
    have hωu3 : ωu ^ 3 = 1 := Units.ext (by simpa [ωu] using hωk3)
    have hωu : ωu ^ ((2 ^ f₀) ^ 3 + 1) = 1 := by rw [hm, pow_mul, hωu3, one_pow]
    obtain ⟨β, hβ, hβω⟩ := CFSG.RankThree.PartTwo.Sec15.F153L3K.FusH90.exists_hilbert90_normOne hcard σ hσ' hωu hωu3
    exact ⟨β, fun _ => by rw [← h23]; exact hβ, hβω⟩

theorem mat_of_conj_scalar {K : Type} [Field K] {h D : GL (Fin 3) K} {c : Kˣ}
    (hc : h * D * h⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * D) :
    (h : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • ((D : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K)) := by
  have h1 : h * D = GeneralLinearGroup.scalar (Fin 3) c * D * h := mul_inv_eq_iff_eq_mul.mp hc
  have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h1
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
  rw [h2, Matrix.smul_eq_diagonal_mul, Matrix.mul_assoc]

theorem mk_scalar_mul {K : Type} [Field K] (u : Kˣ) (A : GL (Fin 3) K) :
    ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) u * A) = ProjGenLinGroup.mk A := by
  rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul]

theorem frame_case {π : Bool} {f f₀ : ℕ} {K : Type} [Field K] (hK : PiField π 2 f K)
    (hq : ModThree π (2 ^ f)) (hf : f = 3 * f₀) {σ : K ≃+* K} (hσ3 : orderOf σ = 3)
    (hσ : (∀ c, σ c = c ^ piCard π (2 ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (2 ^ f₀) ^ 2))
    {g : GL (Fin 3) K} {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hEP : E ≤ projImage (glPi π 3 (2 ^ f) K)) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    (hd : ∀ y : GL (Fin 3) K, ProjGenLinGroup.mk y ∈ E →
      ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i)
    (hfix : ∀ y ∈ glPi π 3 (2 ^ f) K, ProjGenLinGroup.mk y ∈ E →
      ProjGenLinGroup.mk (g * frobGL σ y * g⁻¹) = ProjGenLinGroup.mk y) :
    ∃ r ∈ E, r ≠ 1 ∧ (∀ t : ProjGenLinGroup (Fin 3) K, orderOf t = 2 → t * r ≠ r * t) ∧
      ∀ k : ℕ, ∃ s ∈ slPi π 3 (2 ^ f) K,
        (∀ a ∈ E, ProjGenLinGroup.mk s * a = a * ProjGenLinGroup.mk s) ∧
        ProjGenLinGroup.mk s * (ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹))⁻¹ = r ^ k := by
  classical
  haveI := hK.finite
  haveI hchar : CharP K 2 := hK.charP
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set D : Subgroup (GL (Fin 3) K) := E.comap ProjGenLinGroup.mk ⊓ glPi π 3 (2 ^ f) K with hD
  have hmemD : ∀ y, y ∈ D ↔ ProjGenLinGroup.mk y ∈ E ∧ y ∈ glPi π 3 (2 ^ f) K :=
    fun y => Iff.rfl
  have hDE : D.map ProjGenLinGroup.mk = E := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ((hmemD y).mp hy).1
    · intro e he
      obtain ⟨y, hy, rfl⟩ := hEP he
      exact ⟨y, (hmemD y).mpr ⟨he, hy⟩, rfl⟩
  have hcardD : Nat.card ↥(D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K))) = 9 := by
    have hker : ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp D.subtype).ker =
        ((ProjGenLinGroup.mk : GL (Fin 3) K →* _).comp D.subtype).ker := by
      ext y
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mk_eq_one_iff_mem_statedScalars.symm
    have h1 := card_range_eq_of_ker_eq _ _ hker
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, hDE, hE9] at h1
    exact h1
  have hC : IsTypeC π (2 ^ f) K D := by
    refine ⟨inf_le_right, fun a ha => ?_, hcardD, b, hb, fun a ha => hd a ((hmemD a).mp ha).1⟩
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow]
    exact hE.2 _ ((hmemD a).mp ha).1
  obtain ⟨g₀, hg₀, hconj, hsurj⟩ := isTypeC_conj_std hK hq hC
  obtain ⟨ω, hω3, hω1⟩ := exists_tau hK hq
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω3
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have hσ3' : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ3] at this
  have hσω : σ ω = ω := CFSG.RankThree.PartTwo.Sec15.F153L3K.FusH90.apply_eq_of_cube_root σ hσ3' hω2
  set ωu : Kˣ := Units.mk0 ω hω0 with hωu
  have hωuv : (ωu : K) = ω := rfl
  have hωu3' : ωu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hωuv, hω3]; rfl)
  have hωu3 : ωu ∈ rootsOfUnity 3 K := (mem_rootsOfUnity 3 ωu).mpr hωu3'
  have hωu23 : ωu ^ 2 ∈ rootsOfUnity 3 K := pow_mem hωu3 2
  have hωu1 : ωu ≠ 1 := fun h => hω1 (by rw [← hωuv, h]; rfl)
  have hσωu : Units.map (σ : K →* K) ωu = ωu := Units.ext (by simp only [Units.coe_map, MonoidHom.coe_coe, hωuv]; exact hσω)
  have hσωu2 : Units.map (σ : K →* K) (ωu ^ 2) = ωu ^ 2 := by rw [map_pow, hσωu]
  have hd01 : (1 : Kˣ) ≠ ωu := fun h => hωu1 h.symm
  have hd02 : (1 : Kˣ) ≠ ωu ^ 2 := fun h => hωu1 (by
    have h5 : ωu = ωu ^ 3 * (ωu ^ 2)⁻¹ := by group
    rw [h5, hωu3', ← h]; simp)
  have hd12 : ωu ≠ ωu ^ 2 := fun h => hωu1 (by
    have h5 : ωu * 1 = ωu * ωu := by rw [mul_one, ← sq]; exact h
    exact (mul_left_cancel h5).symm)
  obtain ⟨a₁, ha₁D, l₁, hl₁⟩ := hsurj ωu hωu3 (ωu ^ 2) hωu23
  have ha₁ : a₁ = g₀ * (GeneralLinearGroup.scalar (Fin 3) l₁ * diagUnits 1 ωu (ωu ^ 2)) * g₀⁻¹ := by
    rw [← hl₁]; group
  obtain ⟨a₂, ha₂D, l₂, hl₂⟩ := hsurj 1 (one_mem _) ωu hωu3
  have ha₂ : a₂ = g₀ * (GeneralLinearGroup.scalar (Fin 3) l₂ * diagUnits 1 1 ωu) * g₀⁻¹ := by
    rw [← hl₂]; group
  set h' : GL (Fin 3) K := g₀⁻¹ * g * frobGL σ g₀ with hh'
  have hfix₁ := hfix a₁ ((hmemD a₁).mp ha₁D).2 ((hmemD a₁).mp ha₁D).1
  obtain ⟨u₁, hu₁⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hfix₁.symm
  obtain ⟨c₁, hc₁⟩ := conj_scalar_of_fix σ g g₀ l₁ ωu (ωu ^ 2) hσωu hσωu2 (u := u₁)
    (by rw [← ha₁]; exact hu₁.symm)
  have hfix₂ := hfix a₂ ((hmemD a₂).mp ha₂D).2 ((hmemD a₂).mp ha₂D).1
  obtain ⟨u₂, hu₂⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hfix₂.symm
  obtain ⟨c₂, hc₂⟩ := conj_scalar_of_fix σ g g₀ l₂ 1 ωu (map_one _) hσωu (u := u₂)
    (by rw [← ha₂]; exact hu₂.symm)
  have hm₁ := mat_of_conj_scalar hc₁
  have hm₂ := mat_of_conj_scalar hc₂
  have hdiag1 : ((diagUnits 1 ωu (ωu ^ 2) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, ω, ω ^ 2] := by
    rw [coe_diagUnits]; simp [hωuv]
  have hdiag2 : ((diagUnits 1 1 ωu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, 1, ω] := by
    rw [coe_diagUnits]; simp [hωuv]
  rw [hdiag1] at hm₁
  rw [hdiag2] at hm₂
  have hh'diag : ∀ i j : Fin 3, i ≠ j → ((h' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
    CFSG.RankThree.PartTwo.Sec15.F153L3K.FusDiag.offdiag_eq_zero_of_conj_std hω2 hω1 h'.isUnit hm₁ hm₂
  refine ⟨ProjGenLinGroup.mk a₁, ((hmemD a₁).mp ha₁D).1, ?_, ?_, ?_⟩
  ·
    intro h1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    exact regular_not_scalar g₀ l₁ ωu hωu1 (c := c) (by rw [← ha₁]; exact hc.symm)
  ·
    intro t ht
    obtain ⟨b', d', hb', hd', hz⟩ := regular_eigen_of_conj g₀ l₁ 1 ωu (ωu ^ 2) hd01 hd02 hd12
    rw [← ha₁] at hz
    exact CFSG.RankThree.PartTwo.Sec15.F153L3K.FusNI.not_commute_involution_of_regular hb' hd' hz ht
  ·
    intro k
    obtain ⟨β, hβ, hβω⟩ := exists_beta hK hq hf hσ3 hσ hω3 hσω k
    set T : GL (Fin 3) K := g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹ with hT
    refine ⟨GeneralLinearGroup.scalar (Fin 3) β⁻¹ * T, torus_elt_mem_slPi hK hg₀ hβ, ?_, ?_⟩
    ·
      intro a ha
      obtain ⟨y, hy, rfl⟩ := hEP ha
      have hyD : y ∈ D := (hmemD y).mpr ⟨ha, hy⟩
      obtain ⟨l, s', t', hs', ht', hl⟩ := hconj y hyD
      have hy' : y = g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s' t') * g₀⁻¹ := by
        rw [← hl]; group
      have hcomm := conj_diag_comm g₀ l s' t' β
      rw [← hy', ← hT] at hcomm
      rw [mk_scalar_mul, ← map_mul, ← map_mul, hcomm]
    ·
      obtain ⟨sβ, hsβ⟩ : ∃ s : Kˣ, s = Units.map (σ : K →* K) β := ⟨_, rfl⟩
      have hβu : β = ωu ^ k * sβ := Units.ext (by
        rw [hsβ]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
          hωuv]
        exact hβω)
      have hdecomp : diagUnits 1 β (β ^ 2) =
          diagUnits 1 (ωu ^ k) ((ωu ^ k) ^ 2) * diagUnits 1 sβ (sβ ^ 2) := by
        rw [diagUnits_mul, one_mul, ← mul_pow, ← hβu]
      have hfus : g * frobGL σ T * g⁻¹ = g₀ * diagUnits 1 sβ (sβ ^ 2) * g₀⁻¹ := by
        rw [hsβ]; exact fusion_identity σ g g₀ β hh'diag
      have hTRS : T = (g₀ * diagUnits 1 (ωu ^ k) ((ωu ^ k) ^ 2) * g₀⁻¹) *
          (g₀ * diagUnits 1 sβ (sβ ^ 2) * g₀⁻¹) := by
        rw [hT, hdecomp]; group
      have hF2 : g * frobGL σ (GeneralLinearGroup.scalar (Fin 3) β⁻¹ * T) * g⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) β⁻¹) *
            (g₀ * diagUnits 1 sβ (sβ ^ 2) * g₀⁻¹) := by
        rw [map_mul, frobGL_scalar, conj_scalar_mul, hfus]
      rw [hF2, mk_scalar_mul, mk_scalar_mul, hTRS, map_mul, mul_inv_cancel_right, ← map_pow, ha₁,
        conj_diag_pow g₀ l₁ ωu (ωu ^ 2) k, conj_scalar_mul, mk_scalar_mul]
      congr 3
      rw [← pow_mul, ← pow_mul, mul_comm]

theorem slPi_le_glPi {π : Bool} {f : ℕ} {K : Type} [Field K] (hK : PiField π 2 f K) :
    slPi π 3 (2 ^ f) K ≤ glPi π 3 (2 ^ f) K := by
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  intro s hs
  exact ((mem_slPi_iff hπ).mp hs).1

theorem mmt {π : Bool} {f f₀ : ℕ} {K : Type} [Field K] (hK : PiField π 2 f K)
    (hq : ModThree π (2 ^ f)) (hf : f = 3 * f₀) {σ : K ≃+* K} (hσ3 : orderOf σ = 3)
    (hσ : (∀ c, σ c = c ^ piCard π (2 ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (2 ^ f₀) ^ 2))
    {g : GL (Fin 3) K} {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hEP : E ≤ projImage (slPi π 3 (2 ^ f) K)) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9)
    (hfix : ∀ y ∈ glPi π 3 (2 ^ f) K, ProjGenLinGroup.mk y ∈ E →
      ProjGenLinGroup.mk (g * frobGL σ y * g⁻¹) = ProjGenLinGroup.mk y) :
    ∃ r ∈ E, (∀ k : ℕ, ∃ s ∈ slPi π 3 (2 ^ f) K,
        (∀ a ∈ E, ProjGenLinGroup.mk s * a = a * ProjGenLinGroup.mk s) ∧
        ProjGenLinGroup.mk s * (ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹))⁻¹ = r ^ k) ∧
      ((r ≠ 1 ∧ ∀ t : ProjGenLinGroup (Fin 3) K, orderOf t = 2 → t * r ≠ r * t) ∨
        (r = 1 ∧ ∀ a ∈ E, a ≠ 1 → ∀ t : ProjGenLinGroup (Fin 3) K, orderOf t = 2 →
          t * a ≠ a * t)) := by
  classical
  haveI := hK.finite
  haveI hchar : CharP K 2 := hK.charP
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hc, he, hcard⟩ := map_pglEquivQuot_facts hE
  have hEP' : E ≤ projImage (glPi π 3 (2 ^ f) K) :=
    hEP.trans (Subgroup.map_mono (slPi_le_glPi hK))
  rcases frame_or_heis h3 hτ hτ1 _ hc he (by rw [hcard, hE9]; norm_num) with
    ⟨b, hb, hd, -⟩ | ⟨y₁, y₂, h₁, h₂, ζ, hζ1, hζ⟩
  · obtain ⟨r, hrE, hr1, hrt, hfus⟩ := frame_case hK hq hf hσ3 hσ hEP' hE hE9 hb
      (fun y hy => hd y (mem_map_pglEquivQuot.mpr hy)) hfix
    exact ⟨r, hrE, hfus, Or.inl ⟨hr1, hrt⟩⟩
  · refine ⟨1, one_mem _, ?_, Or.inr ⟨rfl, ?_⟩⟩
    · intro k
      refine ⟨1, one_mem _, fun a _ => by simp, ?_⟩
      simp
    · exact CFSG.RankThree.PartTwo.Sec15.F153L3K.FusHB.noInvolution_of_heis h3 hE (mem_map_pglEquivQuot.mp h₁)
        (mem_map_pglEquivQuot.mp h₂) hζ1 hζ

theorem isElemAbelian_range {Q : Type} [Group Q] {A₀ : Subgroup Q} {H : Type} [Group H]
    (hel : CFSG.Assembly.IsElemAbelian 3 A₀) (φ : A₀ →* H) :
    CFSG.Assembly.IsElemAbelian 3 φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    show (a : H) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact hel.1.is_comm.comm x y
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (hel.2 x x.2)
    rw [this, map_one]

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Fus

end FusMain

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

open CFSG.RankThree.PartTwo.Sec15.F153L3K.Fus
open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.RankThreeEven (projImage)

open CFSG.Assembly.LowTwoRank (StatedScalars)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open CFSG.RankThree.PartTwo.Sec15.Proof1513Res2
open CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEV CFSG.RankThree.PartTwo.Sec15.F153L3K.FusTor CFSG.RankThree.PartTwo.Sec15.F153L3K.FusCF
section Certs


theorem l3FieldFusionK_holds : CFSG.RankThree.PartTwo.Sec15.ThmD.L3FieldFusionK := by
  intro Q _ _ Kg x n hn hiso hxN hx3 hxK hjoin hkind A₀ hA₀K hcomm hcard hel
  have hx3' : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  obtain ⟨π, K, hF, hK, hq, e, f₀, hf, σ, hσ, g, hg, hmodel⟩ :=
    CFSG.RankThree.PartTwo.Sec15.F153L3K.FusModel.exists_fieldAct_model hn hiso hxN hx3' hkind
  haveI := hK.finite
  haveI : CharP K 2 := hK.charP
  have hσ3 : orderOf σ = 3 := CFSG.RankThree.PartTwo.Sec15.F153L3K.FusH90.orderOf_eq_three_of_frobenius_forms hK hf σ hσ
  let ψ : ↥Kg →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (2 ^ (3 * n)) K)).subtype.comp e.toMonoidHom
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp e.injective
  let φ₀ : ↥A₀ →* ProjGenLinGroup (Fin 3) K := ψ.comp (Subgroup.inclusion hA₀K)
  have hφ₀inj : Function.Injective φ₀ := hψinj.comp (Subgroup.inclusion_injective hA₀K)
  have hEP : φ₀.range ≤ projImage (slPi π 3 (2 ^ (3 * n)) K) := by
    rintro _ ⟨a, rfl⟩
    exact (e (Subgroup.inclusion hA₀K a)).2
  have hEel : CFSG.Assembly.IsElemAbelian 3 φ₀.range := isElemAbelian_range hel φ₀
  have hE9 : Nat.card φ₀.range = 9 :=
    (Nat.card_congr (MonoidHom.ofInjective hφ₀inj).toEquiv).symm.trans hcard
  have hfix : ∀ y ∈ glPi π 3 (2 ^ (3 * n)) K, ProjGenLinGroup.mk y ∈ φ₀.range →
      ProjGenLinGroup.mk (g * frobGL σ y * g⁻¹) = ProjGenLinGroup.mk y := by
    intro y hy hyE
    obtain ⟨a, ha⟩ := hyE
    set k : ↥Kg := Subgroup.inclusion hA₀K a with hk
    have hk1 : ((e k : projImage (slPi π 3 (2 ^ (3 * n)) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y := ha
    obtain ⟨⟨s, hs⟩, hsk⟩ := projOf_surjective (slPi π 3 (2 ^ (3 * n)) K) (e k)
    have hmks : ProjGenLinGroup.mk s = ProjGenLinGroup.mk y := by
      rw [← hk1, ← hsk, coe_projOf]
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmks.symm
    have hxk : x * (k : Q) * x⁻¹ = (k : Q) := by
      have h1 := hcomm (a : Q) a.2
      calc x * (k : Q) * x⁻¹ = x * (a : Q) * x⁻¹ := rfl
        _ = (a : Q) := by rw [← h1]; group
    have h1 := hmodel k k s hs hsk.symm hxk
    rw [hk1, ← hu, map_mul (frobGL σ) y, frobGL_scalar, ← scalar_mul_comm, conj_scalar_mul,
      mk_scalar_mul] at h1
    exact h1.symm
  obtain ⟨rM, hrM, hfusM, hnoinv⟩ := mmt hK hq hf hσ3 hσ hEP hEel hE9 hfix
  obtain ⟨rA, hrA⟩ := hrM
  have key : ∀ (a : ↥A₀) (t : Q) (ht : t ∈ Kg), orderOf t = 2 → t * (a : Q) = (a : Q) * t →
      ∃ t' : ProjGenLinGroup (Fin 3) K, orderOf t' = 2 ∧ t' * φ₀ a = φ₀ a * t' := by
    intro a t ht ht2 hca
    refine ⟨ψ ⟨t, ht⟩, ?_, ?_⟩
    · rw [orderOf_injective ψ hψinj, ← Subgroup.orderOf_coe]
      exact ht2
    · have h1 : (⟨t, ht⟩ : ↥Kg) * Subgroup.inclusion hA₀K a =
          Subgroup.inclusion hA₀K a * ⟨t, ht⟩ := Subtype.ext hca
      show ψ ⟨t, ht⟩ * ψ (Subgroup.inclusion hA₀K a) = ψ (Subgroup.inclusion hA₀K a) * ψ ⟨t, ht⟩
      rw [← map_mul, ← map_mul, h1]
  refine ⟨(rA : Q), rA.2, ?_, ?_⟩
  ·
    intro k
    obtain ⟨s, hs, hsE, hsfus⟩ := hfusM k
    set yK : ↥Kg := e.symm (projOf _ ⟨s, hs⟩) with hyK
    have hyKe : e yK = projOf _ ⟨s, hs⟩ := by rw [hyK, MulEquiv.apply_symm_apply]
    have hψy : ψ yK = ProjGenLinGroup.mk s := by
      show ((e yK : projImage (slPi π 3 (2 ^ (3 * n)) K)) : ProjGenLinGroup (Fin 3) K) = _
      rw [hyKe, coe_projOf]
    refine ⟨(yK : Q), yK.2, ?_, ?_⟩
    · intro a ha
      have haE : ψ (Subgroup.inclusion hA₀K ⟨a, ha⟩) ∈ φ₀.range := ⟨⟨a, ha⟩, rfl⟩
      have hc := hsE _ haE
      rw [← hψy] at hc
      have h1 : yK * Subgroup.inclusion hA₀K ⟨a, ha⟩ = Subgroup.inclusion hA₀K ⟨a, ha⟩ * yK :=
        hψinj (by rw [map_mul, map_mul]; exact hc)
      exact congrArg Subtype.val h1
    · set yK' : ↥Kg := Kg.normalizerMonoidHom ⟨x, hxN⟩ yK⁻¹ with hyK'
      have hyK'c : (yK' : Q) = x * (yK : Q)⁻¹ * x⁻¹ :=
        coe_normalizerMonoidHom (L := Kg) ⟨x, hxN⟩ yK⁻¹
      have hinv : e yK⁻¹ = projOf _ ⟨s⁻¹, inv_mem hs⟩ := by
        rw [map_inv, hyKe]
        rfl
      have h1 := hmodel yK⁻¹ yK' s⁻¹ (inv_mem hs) hinv hyK'c.symm
      have hψy' : ψ yK' = (ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹))⁻¹ := by
        show ((e yK' : projImage (slPi π 3 (2 ^ (3 * n)) K)) : ProjGenLinGroup (Fin 3) K) = _
        rw [h1, ← map_inv ProjGenLinGroup.mk, map_inv (frobGL σ)]
        congr 1
        group
      set rK : ↥Kg := Subgroup.inclusion hA₀K rA with hrK
      have hψr : ψ rK = rM := hrA
      have h2 : yK * yK' = rK ^ k := by
        apply hψinj
        rw [map_mul, map_pow, hψy, hψy', hψr]
        exact hsfus
      have h3 := congrArg Subtype.val h2
      have h4 : (yK : Q) * (x * (yK : Q)⁻¹ * x⁻¹) = (rA : Q) ^ k := by
        rw [← hyK'c]; exact h3
      have hrx : (rA : Q) ^ k * x = x * (rA : Q) ^ k :=
        (Commute.pow_left (show Commute (rA : Q) x from hcomm (rA : Q) rA.2) k).eq
      calc (yK : Q) * x * (yK : Q)⁻¹
          = ((yK : Q) * (x * (yK : Q)⁻¹ * x⁻¹)) * x := by group
        _ = (rA : Q) ^ k * x := by rw [h4]
        _ = x * (rA : Q) ^ k := hrx
  · rcases hnoinv with ⟨hr1, hrt⟩ | ⟨hr1, hat⟩
    ·
      have hr1' : (rA : Q) ≠ 1 := by
        intro h1
        apply hr1
        rw [← hrA, show rA = 1 from Subtype.ext h1, map_one]
      exact CFSG.RankThree.PartTwo.Sec15.F153L3K.FusGT.fusion_b_of_noInvolution Kg x hx3 hxK A₀ hA₀K hcomm hcard hel rA.2 hr1'
        (fun t ht ht2 hca => by
          obtain ⟨t', ht'2, htc⟩ := key rA t ht ht2 hca
          rw [hrA] at htc
          exact hrt t' ht'2 htc)
    ·
      intro B hB hB9 hBt
      exfalso
      refine CFSG.RankThree.PartTwo.Sec15.F153L3K.FusGT.fusion_b_vacuous Kg x hx3 hxK A₀ hA₀K hcomm hcard hel
        (fun a ha ha1 t ht ht2 hca => ?_) B hB hB9 hBt
      obtain ⟨t', ht'2, htc⟩ := key ⟨a, ha⟩ t ht ht2 hca
      refine hat (φ₀ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ ?_ t' ht'2 htc
      intro h1
      exact ha1 (congrArg Subtype.val (hφ₀inj (h1.trans (map_one φ₀).symm)))

end Certs

end CFSG.RankThree.PartTwo.Sec15.F153L3K
