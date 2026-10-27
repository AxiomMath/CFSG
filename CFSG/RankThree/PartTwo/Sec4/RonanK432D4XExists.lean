module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432D4XClass
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeLines
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19

section Arith

theorem exists_eps_two_pow (n : ℕ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - ε := by
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  generalize 2 ^ n = q at h3 ⊢
  have hr : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hr with hr | hr
  · exact ⟨1, Or.inl rfl, by omega⟩
  · exact ⟨-1, Or.inr rfl, by omega⟩

theorem three_dvd_cyclotomic {q : ℤ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (h : (3 : ℤ) ∣ q - ε) :
    (3 : ℤ) ∣ q ^ 2 + ε * q + 1 := by
  obtain ⟨k, hk⟩ := h
  have hq : q = ε + 3 * k := by linarith
  subst hq
  rcases hε with rfl | rfl
  · exact ⟨3 * k + 3 * k ^ 2 + 1, by ring⟩
  · exact ⟨-3 * k + 3 * k ^ 2 + 1, by ring⟩

end Arith

section Plane


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem isClassX_of_singular (P : D4Par n X σ) (hn : 2 ≤ n) (Ω : Type) [Field Ω] [Algebra X Ω]
    [IsAlgClosure X Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hqε : (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - ε) {d : ℕ}
    (hd : (d : ℤ) = ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1)
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3)
    (hSig : ∃ i, survivingRoots a = trialitySigma i) {x : C0 σ}
    (hx : threeSixEmb X Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) (hx1 : x ≠ 1) :
    IsClassX σ x := by
  classical
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hn)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : (rootDiagUnit TwistTag.D4.tag a) ^ 3 = 1 := hord ▸ pow_orderOf_eq_one _
  have hx3 : x ^ 3 = 1 := by
    apply threeSixEmb_injective X Ω σ
    rw [map_pow, hx, map_one, conj_pow, hd3]
    group
  obtain ⟨i, hi⟩ := hSig
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4,
      (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  obtain ⟨-, -, hcomm, -, -, -, hcent, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.triality_three_six_singular_fixed_centralizers_gen
      (ℓ := 2) (f := n) Nat.prime_two P.one_le X P.card σ P.frob Ω Fr hFr hε hd g hgG hFg
      Nat.prime_three (by decide) (by decide) hq2 a ha hord v hv x hx
  refine isClassX_of_layer_center_ne_one P hx3 hx1 ?_
  rw [hcomm, hcent]
  have h1 : Int.gcd 3 (((2 ^ n : ℕ) : ℤ) - ε) = 3 := by
    have h2 : Int.gcd 3 (((2 ^ n : ℕ) : ℤ) - ε) ∣ 3 := by
      have := Int.gcd_dvd_left (a := 3) (b := ((2 ^ n : ℕ) : ℤ) - ε)
      exact_mod_cast this
    have h3 : 3 ∣ Int.gcd 3 (((2 ^ n : ℕ) : ℤ) - ε) := by
      exact_mod_cast Int.dvd_gcd (dvd_refl (3 : ℤ)) hqε
    exact Nat.dvd_antisymm h2 h3
  rw [h1]
  decide

theorem exists_two_commuting_classX (P : D4Par n X σ) (hn : 2 ≤ n) :
    ∃ x₁ x₂ : C0 σ, IsClassX σ x₁ ∧ IsClassX σ x₂ ∧ x₁ * x₂ = x₂ * x₁ ∧
      x₂ ∉ Subgroup.zpowers x₁ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := P.charP
  set L := AlgebraicClosure X with hL
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  have hn1 : 1 ≤ n := P.one_le
  obtain ⟨ε, hε, hqε⟩ := exists_eps_two_pow n
  obtain ⟨d, hd⟩ : ∃ d : ℕ,
      (d : ℤ) = ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1 := by
    refine ⟨_, Int.toNat_of_nonneg ?_⟩
    have h0 : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
    rcases hε with rfl | rfl
    · positivity
    · nlinarith [sq_nonneg (((2 ^ n : ℕ) : ℤ) - 1)]
  have h3d : 3 ∣ d := by
    have : (3 : ℤ) ∣ (d : ℤ) := by
      rw [hd]
      exact three_dvd_cyclotomic hε hqε
    exact_mod_cast this
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := X) (ℓ := 2) hn1 L (threeSixN L ε)
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L ε := hFg
  have hTcι := ((triality_three_six_tori_Sylow_and_root_kernels (ℓ := 2) (f := n) Nat.prime_two
    hn1 X P.card σ P.frob L Fr hFr hε hd).2.2.2 g hgG hFg').1
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L 2] at h'
    exact absurd h' (by decide)
  haveI : NeZero ((3 : ℕ) : L) := ⟨by exact_mod_cast h3L⟩
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  have hμ : Nat.card (rootsOfUnity 3 L) = 3 := hζ.card_rootsOfUnity
  have hcardTp : Nat.card (threeSixTorsion L Fr ε 3) = 3 ^ 2 := by
    rw [threeSixTorsion_eq_map Fr hFr hε hd h3d,
      Subgroup.card_map_of_injective (injective_threeSixParam _ _),
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hμ, sq]
  have hιinj : Function.Injective (threeSixEmb X L σ) := threeSixEmb_injective X L σ
  have hle : (threeSixTorsion L Fr ε 3).map (MulAut.conj g).toMonoidHom ≤
      (threeSixEmb X L σ).range :=
    (Subgroup.map_mono (threeSixTorsion_le Fr ε 3)).trans hTcι
  have hcardE : Nat.card (threeSixFixedTorsion X L σ Fr ε 3 g) = 3 ^ 2 := by
    rw [← hcardTp, threeSixFixedTorsion, ← Subgroup.card_map_of_injective hιinj,
      Subgroup.map_comap_eq_self hle, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  set E := threeSixFixedTorsion X L σ Fr ε 3 g with hE
  have hc : E.map (MulAut.conj (1 : C0 σ)).toMonoidHom ≤ E := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  obtain ⟨x₁, hx₁E, x₂, hx₂E, hx₁1, hx₂1, hn12, hdata⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.exists_two_singular_lines_threeSix_plane
      (ℓ := 2) (f := n) X σ hε L Fr hFr E hcardE 1 hc
  obtain ⟨a₁, ha₁T, ha₁o, ha₁S, ha₁x⟩ := hdata x₁ (Set.mem_insert _ _)
  obtain ⟨a₂, ha₂T, ha₂o, ha₂S, ha₂x⟩ :=
    hdata x₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [one_mul, inv_one, mul_one] at ha₁x ha₂x
  refine ⟨x₁, x₂,
    isClassX_of_singular P hn L Fr hFr hε hqε hd hgG hFg' a₁ ha₁T ha₁o ha₁S ha₁x hx₁1,
    isClassX_of_singular P hn L Fr hFr hε hqε hd hgG hFg' a₂ ha₂T ha₂o ha₂S ha₂x hx₂1, ?_, hn12⟩
  apply hιinj
  rw [map_mul, map_mul, ha₁x, ha₂x]
  calc g * rootDiagUnit TwistTag.D4.tag a₁ * g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag a₂ * g⁻¹)
      = g * (rootDiagUnit TwistTag.D4.tag a₁ * rootDiagUnit TwistTag.D4.tag a₂) * g⁻¹ := by
        group
    _ = g * (rootDiagUnit TwistTag.D4.tag a₂ * rootDiagUnit TwistTag.D4.tag a₁) * g⁻¹ := by
        rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm a₁ a₂]
    _ = g * rootDiagUnit TwistTag.D4.tag a₂ * g⁻¹ *
          (g * rootDiagUnit TwistTag.D4.tag a₁ * g⁻¹) := by group

end Plane

end CFSG.RankThree.PartTwo.Sec4.RonanK432
