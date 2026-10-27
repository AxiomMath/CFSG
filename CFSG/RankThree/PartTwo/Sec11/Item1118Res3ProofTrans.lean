module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofCentS
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Cent

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof CFSG.RankThree.PartTwo.Sec21.Item219LieProof Subgroup

section Group

variable {G : Type*} [Group G]

theorem conj_sq_of_conj {t c d : G} (hd3 : d ^ 3 = 1) (htd : t * d * t⁻¹ = d)
    (htc : t * c * t⁻¹ = c * d⁻¹) :
    t ^ 2 * d * (t ^ 2)⁻¹ = d ∧ t ^ 2 * c * (t ^ 2)⁻¹ = c * d := by
  have e : ∀ x, t ^ 2 * x * (t ^ 2)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := fun x => by
    rw [sq, _root_.mul_inv_rev]
    simp only [mul_assoc]
  have hinv : t * d⁻¹ * t⁻¹ = d⁻¹ := by
    calc t * d⁻¹ * t⁻¹ = (t * d * t⁻¹)⁻¹ := by group
      _ = d⁻¹ := by rw [htd]
  have hd2 : d⁻¹ * d⁻¹ = d := by
    calc d⁻¹ * d⁻¹ = d⁻¹ * d⁻¹ * d ^ 3 := by rw [hd3, mul_one]
      _ = d := by group
  refine ⟨by rw [e, htd, htd], ?_⟩
  calc t ^ 2 * c * (t ^ 2)⁻¹ = t * (t * c * t⁻¹) * t⁻¹ := e c
    _ = t * (c * d⁻¹) * t⁻¹ := by rw [htc]
    _ = (t * c * t⁻¹) * (t * d⁻¹ * t⁻¹) := by group
    _ = c * d⁻¹ * d⁻¹ := by rw [htc, hinv]
    _ = c * d := by rw [mul_assoc, hd2]

theorem conj_transport {g s c d c₀ d₀ : G} (hc : g * c₀ * g⁻¹ = c) (hd : g * d₀ * g⁻¹ = d)
    (hsd : s * d₀ * s⁻¹ = d₀) (hsc : s * c₀ * s⁻¹ = c₀ * d₀) :
    g * s * g⁻¹ * d * (g * s * g⁻¹)⁻¹ = d ∧ g * s * g⁻¹ * c * (g * s * g⁻¹)⁻¹ = c * d := by
  subst hc hd
  constructor
  · calc g * s * g⁻¹ * (g * d₀ * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * d₀ * s⁻¹) * g⁻¹ := by group
      _ = g * d₀ * g⁻¹ := by rw [hsd]
  · calc g * s * g⁻¹ * (g * c₀ * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * c₀ * s⁻¹) * g⁻¹ := by group
      _ = g * c₀ * g⁻¹ * (g * d₀ * g⁻¹) := by rw [hsc]; group

theorem conj_mul_of_commute {x y c d c₀ d₀ : G} (hyc : y * c₀ = c₀ * y) (hxd : d * x = x * d)
    (hy : y * d₀ * y⁻¹ = d) (hx : x * c₀ * x⁻¹ = c) :
    x * y * c₀ * (x * y)⁻¹ = c ∧ x * y * d₀ * (x * y)⁻¹ = d := by
  constructor
  · calc x * y * c₀ * (x * y)⁻¹ = x * (y * c₀) * y⁻¹ * x⁻¹ := by group
      _ = x * c₀ * x⁻¹ := by rw [hyc]; group
      _ = c := hx
  · calc x * y * d₀ * (x * y)⁻¹ = x * (y * d₀ * y⁻¹) * x⁻¹ := by group
      _ = d := by rw [hy, ← hxd]; group

end Group

section Split


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime] {σ : K ≃+* K}

theorem exists_trans_split (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq1 : ℓ ^ f % 3 = 1)
    {c d : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hc : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hd : d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, t * d * t⁻¹ = d ∧ t * c * t⁻¹ = c * d := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓp (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_three).1 h')
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 := by
    refine exists_prime_orderOf_dvd_card' 3 ?_
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ (ℓ ^ f) ^ 3 := Nat.one_le_pow _ _ (pow_pos hℓp.pos f)
    have h2 : (ℓ ^ f) ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hq1]
    omega
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have hσω : σ (ω : K) = ω := by
    rw [hσ]
    obtain ⟨r, hr⟩ : ∃ r, ℓ ^ f = 3 * r + 1 := ⟨ℓ ^ f / 3, by omega⟩
    have hω3' : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    rw [hr, pow_succ, pow_mul, hω3', one_pow, one_mul]
  have hσuω : Units.map σ.toRingHom.toMonoidHom ω = ω := Units.ext hσω
  set ζ : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨(ω : K), (mem_trialityFixedField).2 hσω⟩
      (fun h => ω.ne_zero (congrArg Subtype.val h)) with hζdef
  have hζω : trialityFixedUnit K σ ζ = ω := Units.ext rfl
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have hζ3 : ζ ^ 3 = 1 := hinj (by rw [map_pow, hζω, hω3, map_one])
  have hNω : trialityNorm σ hσ3 ω = 1 := by rw [← hζω, trialityNorm_fixedUnit, hζ3]
  have hT : ∀ p, trialityTorusHom σ p ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun p =>
    graphFixedRootTorus_le _ _ _ (trialityTorusHom_mem hσ3 p)
  set d₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨trialityTorusHom σ (ω, 1), hT _⟩
    with hd₀
  set c₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨trialityTorusHom σ (ω, ζ ^ 2), hT _⟩
    with hc₀
  set t₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨rotT K, rotT_mem⟩ with ht₀
  have ht₀d : t₀ * d₀ * t₀⁻¹ = d₀ := Subtype.ext (by
    change rotT K * trialityTorusHom σ (ω, 1) * (rotT K)⁻¹ = trialityTorusHom σ (ω, 1)
    rw [rotT_conj hσ3, hNω, inv_one, one_mul, map_one, mul_one])
  have ht₀c : t₀ * c₀ * t₀⁻¹ = c₀ * d₀⁻¹ := Subtype.ext (by
    change rotT K * trialityTorusHom σ (ω, ζ ^ 2) * (rotT K)⁻¹ =
      trialityTorusHom σ (ω, ζ ^ 2) * (trialityTorusHom σ (ω, 1))⁻¹
    rw [rotT_conj hσ3, hNω, ← map_inv, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · rw [inv_one, one_mul, map_pow, hζω, Prod.fst_mul, Prod.fst_inv, mul_inv_cancel,
        ← pow_succ', hω3]
    · rw [inv_one, one_mul, Prod.snd_mul, Prod.snd_inv, inv_one, mul_one])
  have hT1 : ∀ b, trialityTorusHom σ (ω, b) ≠ 1 := fun b h => hω1 (by
    have h' := trialityTorusHom_injective_all hσ3 (h.trans (map_one _).symm)
    exact congrArg Prod.fst h')
  have hd₀3 : d₀ ^ 3 = 1 := Subtype.ext (by
    change trialityTorusHom σ (ω, 1) ^ 3 = 1
    rw [← map_pow, Prod.pow_mk, hω3, one_pow, ← Prod.one_eq_mk, map_one])
  have hc₀3 : c₀ ^ 3 = 1 := Subtype.ext (by
    change trialityTorusHom σ (ω, ζ ^ 2) ^ 3 = 1
    rw [← map_pow, Prod.pow_mk, hω3, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow,
      ← Prod.one_eq_mk, map_one])
  have hd₀1 : d₀ ≠ 1 := fun h => hT1 1 (congrArg Subtype.val h)
  have hc₀1 : c₀ ≠ 1 := fun h => hT1 _ (congrArg Subtype.val h)
  have hd₀S : d₀ ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
    rw [KS11Lie4Proof.d4ShortSL2, Subgroup.mem_comap]
    change trialityTorusHom σ (ω, 1) ∈ _
    rw [trialityTorusHom_one_right]
    exact trialityOuterTorus_mem_range hσ3 ω
  have hc₀S : c₀ ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    set L := AlgebraicClosure K with hL
    apply mem_centralizer_of_triEmb_mem (L := L)
    have htup : trialityTorusHom σ (ω, ζ ^ 2) =
        rootDiagUnit TwistTag.D4.tag (Pi.mulSingle n2 ω) := by
      rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq]
      congr 1
      have hb : trialityFixedUnit K σ (ζ ^ 2) = ω ^ 2 := by rw [map_pow, hζω]
      have h1 : ω ^ 2 * (ω ^ 2)⁻¹ = 1 := mul_inv_cancel _
      have h2 : (ω * ω * ω)⁻¹ * (ω ^ 2) ^ 2 = ω := by
        rw [show ω * ω * ω = ω ^ 3 by rw [pow_succ, sq], hω3, inv_one, one_mul, ← pow_mul,
          show 2 * 2 = 3 + 1 by rfl, pow_succ, hω3, one_mul]
      rw [hb]
      simp only [hσuω]
      rw [h1, h2]
      funext i
      fin_cases i <;> simp [d4Tuple, Pi.mulSingle_apply, n2] <;> rfl
    rw [triEmb_apply]
    change baseChangeGL (algebraMap K L) (trialityTorusHom σ (ω, ζ ^ 2)) ∈ thetaPair L
    rw [htup, baseChangeGL_rootDiagUnit]
    convert thetaHom_mem_thetaPair (HSL (Units.map (algebraMap K L).toMonoidHom ω)) using 1
    rw [thetaHom_HSL]
    congr 1
    funext i
    by_cases hi : i = n2
    · subst hi
      simp
    · simp [Pi.mulSingle_eq_of_ne hi]
  obtain ⟨y, hyS, hy⟩ := exists_conj_short hσ3 h3K hd₀S hd hd₀3 hd₀1 hd3 hd1
  obtain ⟨x, hxS, hx⟩ := exists_conj_centS hf hℓ3 hK hσ hc₀S hc hc₀3 hc₀1 hc3 hc1
  obtain ⟨hgc, hgd⟩ := conj_mul_of_commute (mem_centralizer_iff.mp hc₀S y hyS)
    (mem_centralizer_iff.mp hxS d hd) hy hx
  obtain ⟨hsd, hsc⟩ := conj_sq_of_conj hd₀3 ht₀d ht₀c
  obtain ⟨htd, htc⟩ := conj_transport hgc hgd hsd hsc
  exact ⟨_, htd, htc⟩

end Split

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
