module

public import CFSG.RankThree.PartTwo.KFacts.K71InnerSU3
public import CFSG.RankThree.PartTwo.KFacts.K71PSU3
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)
open CFSG.Assembly.LowTwoRank
open Matrix

section Diag

variable {K : Type} [Field K]

@[expose] def diag3 (x y z : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(x : K), y, z], diagonal ![((x⁻¹ : Kˣ) : K), ((y⁻¹ : Kˣ) : K), ((z⁻¹ : Kˣ) : K)],
    by
      rw [diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal],
    by
      rw [diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal]⟩

theorem coe_diag3 (x y z : Kˣ) :
    ((diag3 x y z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(x : K), y, z] :=
  rfl

theorem diag3_mul (x y z x' y' z' : Kˣ) :
    diag3 x y z * diag3 x' y' z' = diag3 (x * x') (y * y') (z * z') := by
  apply Units.ext
  rw [Units.val_mul, coe_diag3, coe_diag3, coe_diag3, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diag3_one : diag3 (1 : Kˣ) 1 1 = 1 := by
  apply Units.ext
  rw [coe_diag3, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

theorem diag3_pow (x y z : Kˣ) (k : ℕ) : diag3 x y z ^ k = diag3 (x ^ k) (y ^ k) (z ^ k) := by
  induction k with
  | zero => simp [diag3_one]
  | succ k ih => rw [pow_succ, ih, diag3_mul, pow_succ, pow_succ, pow_succ]

theorem diag3_scalar (x : Kˣ) : diag3 x x x = GeneralLinearGroup.scalar (Fin 3) x := by
  apply Units.ext
  rw [coe_diag3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

variable {p f : ℕ}

theorem diag3_mem_unitarySU (h : UnitaryFieldData p f K) {x y z : Kˣ}
    (hx : x ^ (p ^ f + 1) = 1) (hy : y ^ (p ^ f + 1) = 1) (hz : z ^ (p ^ f + 1) = 1)
    (hxyz : x * y * z = 1) : diag3 x y z ∈ unitarySU p f K 3 := by
  have hN : ∀ w : Kˣ, w ^ (p ^ f + 1) = 1 → h.bar (w : K) * w = 1 := fun w hw => by
    rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hw, Units.val_one]
  refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
  · rw [coe_diag3, det_diagonal, Fin.prod_univ_three]
    simpa using congrArg Units.val hxyz
  · rw [coe_diag3, Matrix.diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, hN x hx, hN y hy, hN z hz]

theorem diag3_inv (x y z : Kˣ) : (diag3 x y z)⁻¹ = diag3 x⁻¹ y⁻¹ z⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diag3_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, diag3_one]

theorem glAut_diag3 (σ : K ≃+* K) (x y z : Kˣ) :
    glAut σ (diag3 x y z) =
      diag3 (Units.map (σ : K →* K) x) (Units.map (σ : K →* K) y) (Units.map (σ : K →* K) z) := by
  apply Units.ext
  rw [coe_glAut, coe_diag3, coe_diag3, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diag3_ne_scalar {x y z : Kˣ} (hxy : x ≠ y) (c : Kˣ) :
    diag3 x y z ≠ GeneralLinearGroup.scalar (Fin 3) c := by
  intro hc
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  simp [coe_diag3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h0 h1
  exact hxy (Units.ext (h0.trans h1.symm))

theorem diag3_ne_scalar' {x y z : Kˣ} (hxz : x ≠ z) (c : Kˣ) :
    diag3 x y z ≠ GeneralLinearGroup.scalar (Fin 3) c := by
  intro hc
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  have h0 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 2) 2
  simp [coe_diag3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h0 h2
  exact hxz (Units.ext (h0.trans h2.symm))

end Diag

section Bar

variable {G : Type} [Group G] [Finite G]

open CFSG.Assembly.RankThreeEven (projSU) in
theorem exists_data83_of_psu3 {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    (h : Sec8.Hyp81 G A c L a) {n : ℕ} (hn : Odd n) {K : Type} [Field K]
    (hK : UnitaryFieldData 2 (3 * n) K) (hq : 2 < 2 ^ (3 * n))
    (ha : InducesKindPSU3 hK L a .field) :
    ∃ (A₀ : Subgroup G) (d : G), Sec8.Data83 G c L a A₀ d n := by
  have := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 2 := hK.charP
  obtain ⟨e, haN, hfield⟩ := id ha
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hca : c * a = a * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hout' := h.not_isInnerAut_induced
  have hcL : L ≤ Subgroup.centralizer {c} := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    exact false_of_center_eq_bot_of_mulEquiv e (center_unitaryPSU_three_eq_bot hK hq) hz hz1
  set α := inducedAutHom L e ⟨a, haN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one L e haN ha3
  have hD : α ∉ (psuConj hK).range :=
    (stdPinnedPSU3_separated hK).not_mem_inndiag_of_isField hfield
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq α hα3 hD
  obtain ⟨f₀, hf, -, hcard₀⟩ := exists_card_fixedField_of_orderOf_eq_three hK hσ3
  have hf₀ : f₀ = n := by omega
  subst hf₀
  classical
  have hf₀1 : 1 ≤ f₀ := hn.pos
  have h3dvd : 3 ∣ Nat.card (fixedField σ)ˣ := by
    rw [Nat.card_units, hcard₀, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f₀
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  set ω : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom ω₀ with hωdef
  have hω3 : orderOf ω = 3 := by
    rw [hωdef, orderOf_injective _ (Units.map_injective (fixedField σ).subtype_injective) ω₀, hω₀]
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω3
    norm_num at hω3
  have hσω : Units.map (σ : K →* K) ω = ω := by
    apply Units.ext
    exact (mem_fixedField_iff σ _).mp (ω₀ : fixedField σ).2
  have h3q : 3 ∣ 2 ^ (3 * f₀) + 1 := three_dvd_two_pow_three_mul_add_one hn
  have h3q₀ : 3 ∣ 2 ^ f₀ + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow 2 1 hn
    simpa using this
  have hωq : ω ^ (2 ^ (3 * f₀) + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hω3]; exact h3q)
  have hωq₀ : ω ^ (2 ^ f₀ + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hω3]; exact h3q₀)
  have hω3' : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  have hKcard : Nat.card K = ((2 ^ f₀) ^ 3) ^ 2 := by
    rw [hK.card, ← pow_mul, ← pow_mul]
    ring_nf
  obtain ⟨l, hlq, hl3⟩ := exists_cube_root_normOne hKcard (δ := ω ^ 2)
    (by rw [← pow_mul, mul_comm, pow_mul, hωq₀, one_pow])
  have hq3 : (2 ^ f₀) ^ 3 = 2 ^ (3 * f₀) := by rw [← pow_mul, mul_comm]
  rw [hq3] at hlq
  have hlω : (l * ω) ^ (2 ^ (3 * f₀) + 1) = 1 := by rw [mul_pow, hlq, hωq, one_mul]
  have hω2 : (ω ^ 2) ^ (2 ^ (3 * f₀) + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hωq, one_pow]
  have hmem₁ : diag3 l l (l * ω) ∈ unitarySU 2 (3 * f₀) K 3 :=
    diag3_mem_unitarySU hK hlq hlq hlω (by
      rw [show l * l * (l * ω) = l ^ 3 * ω by rw [pow_three', ← mul_assoc], hl3, ← pow_succ, hω3'])
  have hmem₂ : diag3 1 ω (ω ^ 2) ∈ unitarySU 2 (3 * f₀) K 3 :=
    diag3_mem_unitarySU hK (one_pow _) hωq hω2 (by rw [one_mul, ← pow_succ', hω3'])
  set S₁ : unitarySU 2 (3 * f₀) K 3 := ⟨_, hmem₁⟩ with hS₁
  set S₂ : unitarySU 2 (3 * f₀) K 3 := ⟨_, hmem₂⟩ with hS₂
  have hfix₂ : psuField hK σ (unitaryProj hK 3 S₂) = unitaryProj hK 3 S₂ := by
    rw [unitaryProj, QuotientGroup.mk'_apply, psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    change glAut σ (diag3 1 ω (ω ^ 2)) = diag3 1 ω (ω ^ 2)
    rw [glAut_diag3, map_one, map_pow, hσω]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, ζ = Units.map (σ : K →* K) l * l⁻¹ := ⟨_, rfl⟩
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζ, mul_pow, ← map_pow, hl3, map_pow, hσω, inv_pow, hl3, mul_inv_cancel]
  have hζq : ζ ^ (2 ^ (3 * f₀) + 1) = 1 := by
    obtain ⟨k, hk⟩ := h3q
    rw [hk, pow_mul, hζ3, one_pow]
  have hσl : Units.map (σ : K →* K) l = ζ * l := by rw [hζ, inv_mul_cancel_right]
  have hglAut₁ : glAut σ (diag3 l l (l * ω)) =
      GeneralLinearGroup.scalar (Fin 3) ζ * diag3 l l (l * ω) := by
    rw [glAut_diag3, map_mul, hσl, hσω, ← diag3_scalar, diag3_mul, mul_assoc ζ l ω]
  have hfix₁ : psuField hK σ (unitaryProj hK 3 S₁) = unitaryProj hK 3 S₁ := by
    have hX : GeneralLinearGroup.scalar (Fin 3) ζ * diag3 l l (l * ω) ∈
        unitarySU 2 (3 * f₀) K 3 := by
      rw [← hglAut₁]
      exact (suField hK σ S₁).2
    have hX' : GeneralLinearGroup.scalar (Fin 3) 1 * diag3 l l (l * ω) ∈
        unitarySU 2 (3 * f₀) K 3 := by
      rw [map_one, one_mul]
      exact hmem₁
    have h1 := unitaryProj_scalar_eq hK hζq (one_pow _) (by rw [hζ3, one_pow]) hX hX'
    have e1 : suField hK σ S₁ = ⟨_, hX⟩ := Subtype.ext (by rw [coe_suField]; exact hglAut₁)
    have e2 : S₁ = ⟨_, hX'⟩ := Subtype.ext (by
      change diag3 l l (l * ω) = GeneralLinearGroup.scalar (Fin 3) 1 * diag3 l l (l * ω)
      rw [map_one, one_mul])
    rw [unitaryProj, QuotientGroup.mk'_apply, psuField_mk, e1]
    conv_rhs => rw [e2]
    exact h1
  have hcc : ∀ y, (psuConj hK H)⁻¹ (psuConj hK H y) = y := fun y => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hmemC : ∀ S : unitarySU 2 (3 * f₀) K 3,
      psuField hK σ (unitaryProj hK 3 S) = unitaryProj hK 3 S →
      e.symm (psuConj hK H (unitaryProj hK 3 S)) ∈
        Sec8.barCentralizer (Subgroup.zpowers a) L := by
    intro S hS
    rw [mem_barCentralizer_zpowers_iff haN]
    apply e.injective
    have h1 : e (thetaQuotMulAut L (compAction L ⟨a, haN⟩)
        (e.symm (psuConj hK H (unitaryProj hK 3 S)))) =
        α (psuConj hK H (unitaryProj hK 3 S)) := rfl
    rw [h1, MulEquiv.apply_symm_apply, hαH, MulAut.mul_apply, MulAut.mul_apply, hcc, hS]
  set ψ : unitarySU 2 (3 * f₀) K 3 →* L ⧸ aschbacherSolvableCore 3 L :=
    (e.symm.toMonoidHom.comp (psuConj hK H).toMonoidHom).comp (unitaryProj hK 3) with hψ
  have hψapp : ∀ S, ψ S = e.symm (psuConj hK H (unitaryProj hK 3 S)) := fun S => rfl
  have hψ1 : ∀ S, ψ S = 1 → S ∈ unitaryScalars hK 3 := by
    intro S hS
    have h1 : unitaryProj hK 3 S = 1 := by
      apply (psuConj hK H).injective
      apply e.symm.injective
      rw [map_one, map_one, ← hψapp, hS]
    rw [← ker_unitaryProj, MonoidHom.mem_ker]
    exact h1
  have hψS : ∀ S, S ∈ unitaryScalars hK 3 → ψ S = 1 := by
    intro S hS
    have h1 : unitaryProj hK 3 S = 1 := (QuotientGroup.eq_one_iff S).mpr hS
    rw [hψapp, h1, map_one, map_one]
  have hy : ψ S₁ * ψ S₂ = ψ S₂ * ψ S₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change diag3 l l (l * ω) * diag3 1 ω (ω ^ 2) = diag3 1 ω (ω ^ 2) * diag3 l l (l * ω)
    rw [diag3_mul, diag3_mul]
    congr 1 <;> exact mul_comm _ _
  have hy₁3 : ψ S₁ ^ 3 = 1 := by
    rw [← map_pow]
    apply hψS
    refine ⟨ω ^ 2, ?_, by rw [← pow_mul]; exact (by rw [show 2 * 3 = 3 * 2 from rfl, pow_mul,
      hω3', one_pow]), ?_⟩
    · rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hω2, Units.val_one]
    · change diag3 l l (l * ω) ^ 3 = _
      rw [diag3_pow, mul_pow, hl3, hω3', mul_one, diag3_scalar]
  have hy₂3 : ψ S₂ ^ 3 = 1 := by
    rw [← map_pow]
    apply hψS
    refine ⟨1, by simp [UnitaryFieldData.norm], one_pow _, ?_⟩
    change diag3 1 ω (ω ^ 2) ^ 3 = _
    rw [diag3_pow, one_pow, hω3', ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3',
      one_pow, map_one, diag3_one]
  have hlω1 : l ≠ l * ω := by
    intro h1
    apply hω1
    exact mul_left_cancel (h1.symm.trans (mul_one l).symm)
  have hy₁1 : ψ S₁ ≠ 1 := by
    intro h1
    obtain ⟨c', -, -, hc'⟩ := hψ1 S₁ h1
    exact diag3_ne_scalar' hlω1 c' hc'
  have hy₂₁ : ψ S₂ ∉ Subgroup.zpowers (ψ S₁) := by
    intro h1
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at h1
    obtain ⟨k, hk⟩ := h1
    rw [← map_pow] at hk
    have h2 : ψ ((S₁ ^ k)⁻¹ * S₂) = 1 := by rw [map_mul, map_inv, hk, inv_mul_cancel]
    obtain ⟨c', -, -, hc'⟩ := hψ1 _ h2
    have h3 : (((S₁ ^ k)⁻¹ * S₂ : unitarySU 2 (3 * f₀) K 3) : GL (Fin 3) K) =
        diag3 ((l ^ k)⁻¹ * 1) ((l ^ k)⁻¹ * ω) (((l * ω) ^ k)⁻¹ * ω ^ 2) := by
      change (diag3 l l (l * ω) ^ k)⁻¹ * diag3 1 ω (ω ^ 2) = _
      rw [diag3_pow, diag3_inv, diag3_mul]
    rw [h3] at hc'
    refine diag3_ne_scalar (fun h4 => hω1 ?_) c' hc'
    rw [mul_one] at h4
    exact (mul_left_cancel (h4.symm.trans (mul_one _).symm))
  obtain ⟨A₀, d, hdL, hdy, hdA, hcA, haA, hA₀, hcard, hnorm, hsec⟩ :=
    exists_E81 hcL haN hca hc3 h.ne_one ha3 hout' hZ (hmemC S₁ hfix₁) (hmemC S₂ hfix₂) hy₁3
      hy₂3 hy hy₁1 hy₂₁
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hA₀.2 d hdA⟩
  set e' : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hK 3 :=
    e.trans (psuConj hK H).symm with he'
  have he'y : e' (e.symm (psuConj hK H (unitaryProj hK 3 S₁))) = unitaryProj hK 3 S₁ := by
    rw [he', MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hdA' : inducedAutHom L e' ⟨d, hdN⟩ =
      psuConj hK ⟨_, unitarySU_le_unitaryIsom3 hmem₁⟩ := by
    rw [inducedAutHom_eq_conj_of_mem e' hdL hdN, hdy, he'y]
    exact conj_mk_eq_psuConj S₁
  have hlm : (l : K) ≠ ((l * ω : Kˣ) : K) := fun h1 => hlω1 (Units.ext h1)
  have hA : (((⟨_, unitarySU_le_unitaryIsom3 hmem₁⟩ : unitaryIsom3 hK) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![(l : K), (l : K), ((l * ω : Kˣ) : K)] := rfl
  obtain ⟨hK', hKne⟩ :=
    imageModTheta_mulEquiv_projSL_of_psu3 hK (by omega) e' hdN hd3 hlm hA hdA'
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hy₁1
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨1, hdL⟩ = 1 := map_one _
    rw [hψapp]
    exact hdy.symm.trans h1
  obtain ⟨f₁, hf₁, hPGU⟩ := isoPGUThree_barCentralizer_of_field hq ha3 ha
  have hf₁' : f₁ = f₀ := by omega
  rw [hf₁'] at hPGU
  let φK : K ≃+* GaloisField 2 (2 * (3 * f₀)) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 (2 * (3 * f₀)) (by omega) hK.card
  have hLU : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * f₀)) :=
    ⟨e.trans ((unitaryPSUEquiv hK (by norm_num)).trans
      ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr φK)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φK 3 (2 ^ (3 * f₀)))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φK)).trans
        (Census.statedSUEquivProjSU 3 2 (3 * f₀))))⟩
  refine ⟨A₀, d, ⟨fun x hx => hnorm hx, hcA, haA, hA₀, hcard, hsec, hdA, hd1, ?_, hn, hKne, ?_⟩⟩
  · exact (inducesKindPSU3_inner_or_diagonal hK e' hdN _ hdA').imp
      (fun h' => InducesStdKind.psu3 hK hq h') (fun h' => InducesStdKind.psu3 hK hq h')
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hLU, hPGU, hK'⟩)))

end Bar

end CFSG.RankThree.PartTwo.KFacts
