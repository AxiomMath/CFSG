module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofA2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofDescent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddA
public import CFSG.Adapters.TauCetiExceptional.ReeFrob
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.GenerationEven
public import CFSG.Adapters.TauCetiExceptional.ReeEquiv
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.CubeTorsionRoots
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.RankOneFixed
public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.RankThree.PartOne.KE.A1Centralizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.HighestRoot CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section SL2

variable {L : Type} [Field L]

theorem map_HSL' (σ : L →+* L) (t : Lˣ) :
    Matrix.SpecialLinearGroup.map σ (HSL t) = HSL (Units.map σ.toMonoidHom t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_HSL]

theorem exists_nSL_of_conj_HSL {u : Lˣ} (hu : u ^ 2 ≠ 1) {m : SL2 L}
    (hm : m * HSL u⁻¹ = HSL u * m) : ∃ a : Lˣ, m = nSL a := by
  have huu : (u : L) ≠ ((u⁻¹ : Lˣ) : L) := by
    intro h
    apply hu
    have h1 : u = u⁻¹ := Units.ext h
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel u
  have h := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L)) hm
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL] at h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  have hm00 : (m : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
    have : (((u⁻¹ : Lˣ) : L) - (u : L)) * (m : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
      simp only [Units.val_inv_eq_inv_val] at h00 ⊢
      linear_combination h00
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h').symm huu
    · exact h'
  have hm11 : (m : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
    have : ((u : L) - ((u⁻¹ : Lˣ) : L)) * (m : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
      simp only [Units.val_inv_eq_inv_val] at h11 ⊢
      linear_combination h11
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') huu
    · exact h'
  have hdet := det_SL2 m
  rw [hm00, hm11, zero_mul, zero_sub] at hdet
  have hm01 : (m : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul, neg_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 _ hm01, Subtype.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [nSL] using hm00
  · simp [nSL]
  · simp only [nSL, Units.val_inv_eq_inv_val, Units.val_mk0]
    change (m : Matrix (Fin 2) (Fin 2) L) 1 0 = -((m : Matrix (Fin 2) (Fin 2) L) 0 1)⁻¹
    field_simp
    linear_combination -hdet
  · simpa [nSL] using hm11

end SL2

section Cent


theorem rootSL2_g2v_HSL {L : Type} [Field L] (t : Lˣ) :
    rootSL2 .G2 L g2v (HSL t) = rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
  obtain ⟨tV, htV, hV⟩ :=
    CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.rootTorusSL2_tuple (L := L)
      isRoot_g2v t
  show rootTorusSL2 .G2 L g2v t = _
  rw [htV]
  congr 1
  have h0 : tV g2ia = t ^ (0 : ℤ) := by rw [hV]; congr 1
  have h1 : tV g2ir = t ^ (1 : ℤ) := by rw [hV]; congr 1
  funext i
  rcases fin_G2_cases i with rfl | rfl
  · rw [h0, zpow_zero, Pi.mulSingle_eq_of_ne (by decide)]
  · rw [h1, zpow_one, Pi.mulSingle_eq_same]

theorem nonempty_centralizer_mulEquiv_statedSU {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ f) (h3 : 3 ∣ Nat.card K + 1) {L : Type} [Field L]
    [Finite L] [Algebra K L] [CharP L p] (hdeg : Module.finrank K L = 2)
    {z : adjointGroup .G2 K} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    Nonempty (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ≃* StatedSU 3 (p ^ f) L) := by
  classical
  have hL : Nat.card L = (p ^ f) ^ 2 := by rw [KS11Lie4Proof.natCard_quadratic hdeg, hK]
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Algebra.IsAlgebraic K L := inferInstance
  set σ := unitaryInvolution L p f with hσdef
  have hσapp : ∀ c, σ c = c ^ p ^ f := unitaryInvolution_apply L p f
  have hσσ : ∀ c, (σ : L →+* L) ((σ : L →+* L) c) = c := unitaryInvolution_involutive hL
  have hσK : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L := by
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hσapp]
    have := Fintype.ofFinite K
    rw [← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσFr : ∀ c, (σ : L →+* L) c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hσapp c
  set sA : adjointGroup .G2 L →* adjointGroup .G2 L :=
    ((baseChangeGL (σ : L →+* L)).comp (adjointGroup .G2 L).subtype).codRestrict _ fun w =>
      baseChangeGL_mem_adjointGroup (σ : L →+* L) w.2 with hsA
  have hsAapp : ∀ w, (sA w : ModGL .G2 L) = baseChangeGL (σ : L →+* L) (w : ModGL .G2 L) :=
    fun w => rfl
  have hss : ∀ w, sA (sA w) = w := fun w => Subtype.ext (by
    rw [hsAapp, hsAapp]
    exact Sec4.Res417Seven.baseChangeGL_involutive hσσ _)
  set β := KS11Lie4Proof.bcG2 K L with hβdef
  have hβ : Function.Injective β := KS11Lie4Proof.bcG2_injective
  have hβs : ∀ x, sA (β x) = β x := fun x =>
    Subtype.ext (KS11Lie4Proof.baseChangeGL_bcG2 _ hσK x)
  have hdesc : ∀ w, sA w = w → ∃ x, β x = w := by
    intro w hw
    have hfix : Units.map (entrywiseHom (σ : L →+* L)) (w : ModGL .G2 L) = w :=
      (units_map_entrywiseHom_eq_baseChangeGL_self _ _).trans (congrArg Subtype.val hw)
    obtain ⟨y, hy, hyw⟩ := CFSG.TauCetiBridge.Ree.mem_map_adjointGroup_G2_of_frobenius_fixed
      (σ : L →+* L) hσFr w.2 hfix
    exact ⟨⟨y, hy⟩, Subtype.ext hyw⟩
  obtain ⟨A, hA⟩ : ∃ A : SL2 K, rootSL2 .G2 K g2v A = (z : ModGL .G2 K) := by
    have hz' : (z : ModGL .G2 K) ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := hzS
    rw [show (g2δ : Fin Tag.G2.rank → ℤ) = g2v from rfl,
      ← range_rootSL2_of_isRoot isRoot_g2v] at hz'
    exact hz'
  have hA3 : A ^ 3 = 1 := rootSL2_injective_of_field g2v (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hz3)
  have hA1 : A ≠ 1 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    rw [← hA, map_one]
    rfl
  set AL := Matrix.SpecialLinearGroup.map (algebraMap K L) A with hAL
  have hinjAL : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro X Y h
    apply Subtype.ext
    ext i j
    have h1 := congrArg (fun B : SL2 L => (B : Matrix (Fin 2) (Fin 2) L) i j) h
    exact (algebraMap K L).injective (by simpa using h1)
  have h31 : 3 ∣ Nat.card L - 1 := by
    rw [hL, ← hK]
    exact KS11Lie4Proof.three_dvd_sq_sub_one h3
  obtain ⟨Q, t, hQt⟩ := KS11Lie4Proof.exists_conj_HSL_of_three h31 AL
    ⟨1, by rw [pow_one, hAL, ← map_pow, hA3, map_one]⟩
  have ht3 : t ^ 3 = 1 := by
    apply KS11Lie4Proof.HSLHom_injective (K := L)
    rw [map_pow, map_one, KS11Lie4Proof.HSLHom_apply, ← hQt, conj_pow, hAL, ← map_pow, hA3,
      map_one, mul_one, mul_inv_cancel]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hA1
    apply hinjAL
    have h1 : Q * AL * Q⁻¹ = 1 := by rw [hQt]; exact map_one (KS11Lie4Proof.HSLHom L)
    rw [map_one]
    calc AL = Q⁻¹ * (Q * AL * Q⁻¹) * Q := by group
      _ = 1 := by rw [h1]; group
  have htord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have ht2 : t ^ 2 ≠ 1 := by
    intro h
    apply ht1
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht3, h, inv_one, one_mul]
  have hσt : Units.map (σ : L →+* L).toMonoidHom t = t⁻¹ := by
    have hq : p ^ f % 3 = 2 := by
      rw [hK] at h3
      omega
    have h1 : t ^ p ^ f = t⁻¹ := by
      rw [← Nat.div_add_mod (p ^ f) 3, hq, pow_add, pow_mul, ht3, one_pow, one_mul,
        eq_inv_iff_mul_eq_one, ← pow_succ, ht3]
    apply Units.ext
    rw [← h1, Units.val_pow_eq_pow_val]
    exact hσapp t
  have hρC : ∀ X : SL2 L, rootSL2 .G2 L g2v X ∈ adjointGroup .G2 L := fun X =>
    (exceptional_Lang_root_rank_one_data .G2 L g2v).2.2.2.2.1 X
  set y : adjointGroup .G2 L := ⟨rootSL2 .G2 L g2v Q⁻¹, hρC _⟩ with hydef
  set d : adjointGroup .G2 L := ⟨rootSL2 .G2 L g2v (HSL t), hρC _⟩ with hddef
  have hdcoe : (d : ModGL .G2 L) = rootDiagUnit .G2 (Pi.mulSingle g2ir t) := rootSL2_g2v_HSL t
  have hz : β z = y * d * y⁻¹ := by
    apply Subtype.ext
    rw [KS11Lie4Proof.coe_bcG2, ← hA, baseChangeGL_rootSL2_of_field]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hydef, hddef]
    rw [← map_inv, ← map_mul, ← map_mul, inv_inv, ← hAL]
    congr 1
    calc AL = Q⁻¹ * (Q * AL * Q⁻¹) * Q := by group
      _ = Q⁻¹ * HSL t * Q := by rw [hQt]
  set m := Q * (Matrix.SpecialLinearGroup.map (σ : L →+* L) Q)⁻¹ with hmdef
  have hn : ((y⁻¹ * sA y : adjointGroup .G2 L) : ModGL .G2 L) = rootSL2 .G2 L g2v m := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsAapp, hydef]
    rw [baseChangeGL_rootSL2_of_field, ← map_inv, ← map_mul, inv_inv, map_inv]
  have hmconj : m * HSL t⁻¹ = HSL t * m := by
    have hσAL : Matrix.SpecialLinearGroup.map (σ : L →+* L) AL = AL := by
      rw [hAL]
      apply Subtype.ext
      ext i j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
      exact congrFun (congrArg DFunLike.coe hσK) _
    have h1 := congrArg (Matrix.SpecialLinearGroup.map (σ : L →+* L)) hQt
    rw [map_mul, map_mul, map_inv, hσAL, map_HSL', hσt] at h1
    rw [hmdef, ← h1, ← hQt]
    group
  obtain ⟨a, ha⟩ := exists_nSL_of_conj_HSL ht2 hmconj
  obtain ⟨-, -, hWeyl, -⟩ := exceptional_Lang_root_rank_one_torus_transport .G2 L isRoot_g2v
  obtain ⟨hnm, hnw⟩ := hWeyl a
  have hnC : rootWeylSL2 .G2 L g2v a ∈ adjointGroup .G2 L := hρC _
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := L)
  obtain ⟨Ψ, hΨ, W, hWΨ⟩ := exists_twist_hom φ hφ hφinj (σ : L →+* L) hnC hnm hnw
  have hΨ' : ∀ X, φ (Ψ X) = (y⁻¹ * sA y) * sA (φ X) * (y⁻¹ * sA y)⁻¹ := fun X =>
    Subtype.ext (by
      rw [hΨ X, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn, ha, hsAapp]
      rfl)
  have hKer := KS11Lie4Proof.rootCharKernel_threeA (K := L) htord
  have hφd : ∀ X, φ X * d = d * φ X := by
    have hle := KS11Lie4Proof.range_le_of_a2y φ hφ
      (Subgroup.centralizer ({d} : Set (adjointGroup .G2 L))) fun γ hγ c => by
        rw [KS11Lie4Proof.mem_centralizer_iff_toral hdcoe, mem_toralCentralizer]
        refine ⟨(a2y γ c).2, ?_⟩
        rw [KS11Lie4Proof.coe_a2y hγ]
        have hmem : CFSG.LieType.Steinberg.RankTwo.g2CommRoot (a2pos (γ 0, γ 1)) ∈
            rootCharKernel (Pi.mulSingle g2ir t) := by
          rw [hKer]
          exact KS11Lie4Proof.a2_long_roots hγ
        rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
    intro X
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨X, rfl⟩)
  have hdφ : ∀ w, w * d = d * w → ∃ X, φ X = w := by
    intro w hw
    have hw' : (w : ModGL .G2 L) ∈ toralCentralizer .G2 L (Pi.mulSingle g2ir t) :=
      (KS11Lie4Proof.mem_centralizer_iff_toral hdcoe).mp
        (Subgroup.mem_centralizer_singleton_iff.mpr hw)
    obtain ⟨w', ⟨X, rfl⟩, hX⟩ := Sec4.Res417Seven.toralCentralizer_threeA_le_range_a2 φ hφ htord hw'
    exact ⟨X, Subtype.ext hX⟩
  obtain ⟨e₁⟩ := nonempty_centralizer_mulEquiv_eqLocus β hβ sA hβs hdesc hz φ hφinj hφd hdφ Ψ hΨ'
  have hΨ2 := twist_twist sA hss φ hφinj Ψ hΨ'
  obtain ⟨e₂⟩ := nonempty_eqLocus_mulEquiv_statedSU hL Ψ W hWΨ hΨ2
  exact ⟨e₁.trans e₂⟩

theorem isQuasisimple_centralizer_threeA {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K + 1) (hK4 : 4 ≤ Nat.card K) {z : adjointGroup .G2 K}
    (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' K
  have : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_statedSU hK h3 hdeg hzS hz3 hz1
  have hL : Nat.card L = (ringChar K ^ (n : ℕ)) ^ 2 := by
    rw [KS11Lie4Proof.natCard_quadratic hdeg, hK]
  have hq : (3, ringChar K ^ (n : ℕ)) ≠ (3, 2) := by
    intro h
    have h2 := (Prod.mk.inj h).2
    rw [hK, h2] at hK4
    omega
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL (by norm_num) hq).1

end Cent

theorem g2ThreeACentMinus_holds :
    KS11Lie4Proof.G2ThreeACentMinus := by
  intro K _ _ h3 hK4 z hzS hz3 hz1
  refine ⟨Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)), le_rfl,
    fun x hx y hy => mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
    isQuasisimple_centralizer_threeA h3 hK4 hzS hz3 hz1, z,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl, fun n hn => ?_, hz1, hz3⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp hn).symm

end CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
