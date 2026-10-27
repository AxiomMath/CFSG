module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedRange
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGF4N2ChartLift
import CFSG.LocalAnalysis.StandardType.GGF4N2JModelExclusions
import CFSG.LocalAnalysis.StandardType.GGF4N2RootAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
import CFSG.LieType.SpecialLinear.NormalizerLift.FieldGraph
import CFSG.Quasithin.H13.U3L14E
import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
import CFSG.Quasithin.Vol2.Ch5Sec1Lem516
import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Facts
import CFSG.Quasithin.Vol2.Ch6Sec1G22
import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4AI
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F2
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusIn
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4R

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm

section BlockGamma

theorem blockGamma_mul_blockGamma (C C' : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2))
    {δ δ' : ℕ} (hδ : δ ≤ 1) (hδ' : δ' ≤ 1) :
    ∃ (C'' : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) (δ'' : ℕ), δ'' ≤ 1 ∧
      N2KFieldCoefficient.blockGamma C δ * N2KFieldCoefficient.blockGamma C' δ' =
        N2KFieldCoefficient.blockGamma C'' δ'' := by
  simp only [N2KFieldCoefficient.blockGamma]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ' with rfl | rfl
  · exact ⟨C * C', 0, zero_le_one, by rw [pow_zero, mul_one, mul_one, mul_one, map_mul]⟩
  · exact ⟨C * C', 1, le_rfl, by rw [pow_zero, mul_one, ← mul_assoc, ← map_mul]⟩
  · refine ⟨C * Matrix.GeneralLinearGroup.inverseTranspose C', 1, le_rfl, ?_⟩
    rw [pow_zero, mul_one, mul_assoc, pow_one, CFSG.LieType.SpecialLinear.slGraphAut_mul_slConjugation, ← mul_assoc, ← map_mul]
  · refine ⟨C * Matrix.GeneralLinearGroup.inverseTranspose C', 0, zero_le_one, ?_⟩
    rw [pow_zero, mul_one, pow_one, ← mul_assoc, mul_assoc (slConjugation 4 (GaloisField 2 2) C),
      CFSG.LieType.SpecialLinear.slGraphAut_mul_slConjugation, ← mul_assoc, ← map_mul, mul_assoc,
      ← pow_two, slGraphAut_sq, mul_one]

end BlockGamma

section Power

theorem psi_rho_eq_of_conj {G : Type} [Group G] {K Bs : Subgroup G}
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* K) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _)
    (rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2))
    (hPoint : ∀ (b : Bs) (k : K), ((ψ (rho b) * k * (ψ (rho b))⁻¹ : K) : G) = b * k * b⁻¹)
    (hPow : ∀ b : Bs, rho b ^ 5 = 1) {b : Bs} (hbK : (b : G) ∈ K) (hb5 : (b : G) ^ 5 = 1) :
    ((ψ (rho b) : K) : G) = b := by
  obtain ⟨s', hs'5, hs'⟩ := N2Chart.exists_lift_five (ψ := ψ) hker (x := ⟨b, hbK⟩) (hsurj _)
    (Subtype.ext (by simpa using hb5))
  have hsame : ∀ k : K, ψ (rho b) * k * (ψ (rho b))⁻¹ = ψ s' * k * (ψ s')⁻¹ := by
    intro k
    apply Subtype.ext
    rw [hPoint b k, hs']
    simp
  have hcomm : Commute (rho b) s' := by
    apply N2Chart.commute_of_map_commute_five hker hs'5
    have h := hsame (ψ s')
    rw [mul_inv_cancel_right] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hr5 : (s'⁻¹ * rho b) ^ 5 = 1 := by
    rw [hcomm.symm.inv_left.mul_pow, inv_pow, hs'5, hPow b, inv_one, one_mul]
  have hrc : s'⁻¹ * rho b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    refine (N2Chart.commute_of_map_commute_five hker hr5 ?_).eq
    have h1 := hsame (ψ w)
    show ψ w * ψ (s'⁻¹ * rho b) = ψ (s'⁻¹ * rho b) * ψ w
    rw [map_mul, map_inv]
    calc ψ w * ((ψ s')⁻¹ * ψ (rho b)) = (ψ s')⁻¹ * (ψ s' * ψ w * (ψ s')⁻¹) * ψ (rho b) := by group
      _ = (ψ s')⁻¹ * (ψ (rho b) * ψ w * (ψ (rho b))⁻¹) * ψ (rho b) := by rw [h1]
      _ = (ψ s')⁻¹ * ψ (rho b) * ψ w := by group
  have hr3 := N2Chart.pow_three_eq_one_of_mem_center hrc
  have hr1 : s'⁻¹ * rho b = 1 := by
    calc s'⁻¹ * rho b = (s'⁻¹ * rho b) ^ 5 * (s'⁻¹ * rho b) := by rw [hr5, one_mul]
      _ = (s'⁻¹ * rho b) ^ 6 := (pow_succ _ 5).symm
      _ = ((s'⁻¹ * rho b) ^ 3) ^ 2 := pow_mul _ 3 2
      _ = 1 := by rw [hr3, one_pow]
  rw [← inv_mul_eq_one.mp hr1, hs']


theorem ggF4N2_mixed_no_residual
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x) :
    ∃ eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
      ∀ γ ∈ Subgroup.normalizer (J : Set G),
        (∃ (C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) (δ : ℕ), δ ≤ 1 ∧
          ∀ w : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
            γ * (eJ.symm w : G) * γ⁻¹ = (eJ.symm (N2KFieldCoefficient.blockGamma C δ w) : G)) →
        ¬ ((γ * y * γ⁻¹ = (g * y * g⁻¹) ^ 2 ∧ γ * (g * y * g⁻¹) * γ⁻¹ = y ^ 3) ∨
          (γ * y * γ⁻¹ = (g * y * g⁻¹) ^ 3 ∧ γ * (g * y * g⁻¹) * γ⁻¹ = y ^ 2)) := by
  classical
  obtain ⟨ψ, rho, hsurj, hker, -, hPoint, hPow, hRhoKer, -, -, -, -, hT45, -, eJ, heJ, -⟩ :=
    ggF4N2K_originalLiteralChart_of_original_data hR hNbr hL hK
  refine ⟨eJ, ?_⟩
  rintro γ hγJ ⟨C, δ, hδ, hγe⟩ hres
  obtain ⟨-, -, -, -, -, -, hxline, -⟩ := ggF4N2_mixed_lines hR hNbr hL hK hF4 hgL hgN hginv hgx
  obtain ⟨-, -, -, -, -, -, -, hgJ⟩ := ggF4N2L_swap_normalizes hR hL hgL hginv hgx
  obtain ⟨C', δ', hδ', hge⟩ := ggF4N2L_swap_field_free hR hNbr hL hK eJ hgL hginv hgx
  obtain ⟨C'', δ'', hδ'', hcomp⟩ := blockGamma_mul_blockGamma C C' hδ hδ'
  have hDle : D ≤ Subgroup.centralizer ({g ^ 2} : Set G) :=
    ggF4N2L_swap_sq_centralizes hR hL hgL hginv hgx
  obtain ⟨hxBs, hxy, hyo, hDcl, hDcard, hDE⟩ := ggF4N2_x_data hR hNbr
  obtain ⟨v, ⟨hvD, hvK⟩, hvo, hDyv, hgy, -⟩ :=
    ggF4N2_swap_exchanges_axes hR hNbr hL hK hF4 hgL hgN hginv hgx
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hDBs : D ≤ Bs := hR.1.2.2.1.1.trans hR.1.2.1.1
  have huK : g * y * g⁻¹ ∈ K := (Subgroup.zpowers_le.mpr hvK) hgy
  have huD : g * y * g⁻¹ ∈ D := (Subgroup.zpowers_le.mpr hvD) hgy
  have hgu : g * (g * y * g⁻¹) * g⁻¹ = y := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hDle hyD)
    calc g * (g * y * g⁻¹) * g⁻¹ = g ^ 2 * y * (g ^ 2)⁻¹ := by rw [pow_two]; group
      _ = y := by rw [← h, mul_inv_cancel_right]
  have hu5 : (g * y * g⁻¹) ^ 5 = 1 := hDE.2 _ huD
  have hy5 : y ^ 5 = 1 := hDE.2 _ hyD
  obtain ⟨m, m', hm, hm'm, hny, hnu⟩ : ∃ m m' : ℕ, (m = 2 ∨ m = 3) ∧ m * m' % 5 = 1 ∧
      (γ * g) * y * (γ * g)⁻¹ = y ^ m' ∧
      (γ * g) * (g * y * g⁻¹) * (γ * g)⁻¹ = (g * y * g⁻¹) ^ m := by
    have h1 : (γ * g) * y * (γ * g)⁻¹ = γ * (g * y * g⁻¹) * γ⁻¹ := by group
    have h2 : (γ * g) * (g * y * g⁻¹) * (γ * g)⁻¹ = γ * y * γ⁻¹ := by
      rw [show (γ * g) * (g * y * g⁻¹) * (γ * g)⁻¹ = γ * (g * (g * y * g⁻¹) * g⁻¹) * γ⁻¹ by group,
        hgu]
    rcases hres with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨2, 3, Or.inl rfl, by norm_num, h1.trans hb, h2.trans ha⟩
    · exact ⟨3, 2, Or.inr rfl, by norm_num, h1.trans hb, h2.trans ha⟩
  have hn₀J : γ * g ∈ Subgroup.normalizer (J : Set G) := Subgroup.mul_mem _ hγJ hgJ
  have hKc : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hR.1.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hR.1.2.2 hNbr)).1
  have hzy : Subgroup.zpowers ((γ * g) * y * (γ * g)⁻¹) = Subgroup.zpowers y := by
    rw [hny]
    exact zpowers_pow_eq_of_pow_five hy5 (m := m') (m' := m) (by rw [mul_comm]; exact hm'm)
  have hKn : CFSG.Assembly.IsComponentOf (K.map (MulAut.conj (γ * g)).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    rw [← centralizer_singleton_eq_of_zpowers_eq hzy]
    exact isComponentOf_centralizer_map_conj hKc (γ * g)
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  have hJKn : J ≤ K.map (MulAut.conj (γ * g)).toMonoidHom :=
    (map_conj_eq_of_mem_normalizer hn₀J).symm.le.trans (Subgroup.map_mono hJK)
  have hKeq : K.map (MulAut.conj (γ * g)).toMonoidHom = K := by
    obtain ⟨t₁, -, j₁, -, -, -, -, -, hj₁J, -, -, ht₁, -, ht₁o, -, h₁₁, -, -, -, -, -⟩ :=
      ggF4N2K_block_inverters hR hNbr hL hK
    rcases isComponentOf_le_or_commutator_eq_bot hKc hKn.2.1 with hle | hcomm
    · exact (Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj (γ * g)).injective).le).symm
    · exfalso
      have hc : t₁ * j₁ = j₁ * t₁ :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) (hJK hj₁J)) t₁ (hJKn ht₁.2)
      have hfix : t₁⁻¹ = t₁ := by rw [← h₁₁, ← hc, mul_inv_cancel_right]
      have h2 : t₁ ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← hfix]
        exact inv_mul_cancel t₁
      have hdvd := orderOf_dvd_of_pow_eq_one h2
      rw [ht₁o] at hdvd
      norm_num at hdvd
  have hn₀K : γ * g ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKeq
  set alphaQ : MulAut K := K.normalizerMonoidHom ⟨γ * g, hn₀K⟩ with halpha_def
  have halpha : ∀ k : K, ((alphaQ k : K) : G) = (γ * g) * k * (γ * g)⁻¹ := fun k => rfl
  have hblock : ∀ w : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
      alphaQ (ψ (CFSG.SeitzReduction.E6Pilot.blockFour w)) =
        ψ (CFSG.SeitzReduction.E6Pilot.blockFour
          ((slConjugation 4 (GaloisField 2 2) C'' * (slGraphAut 4 (GaloisField 2 2)) ^ δ'') w)) := by
    intro w
    apply Subtype.ext
    rw [halpha, heJ, heJ]
    change (γ * g) * (eJ.symm w : G) * (γ * g)⁻¹ =
      (eJ.symm (N2KFieldCoefficient.blockGamma C'' δ'' w) : G)
    rw [← hcomp, MulAut.mul_apply, ← hγe, ← hge]
    group
  have huBs : g * y * g⁻¹ ∈ Bs := hDBs huD
  have hyBs : y ∈ Bs := hDBs hyD
  have hxu : y * (g * y * g⁻¹) ∈ Subgroup.zpowers x := hxline ▸ Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxu
  have hρy : rho ⟨y, hyBs⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hRhoKer, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y
  have hρu : rho ⟨g * y * g⁻¹, huBs⟩ = rho ⟨x, hxBs⟩ ^ j := by
    have h : (⟨g * y * g⁻¹, huBs⟩ : Bs) = (⟨y, hyBs⟩ : Bs)⁻¹ * (⟨x, hxBs⟩ : Bs) ^ j :=
      Subtype.ext (by simp [hj])
    rw [h, map_mul, map_inv, hρy, inv_one, one_mul, map_zpow]
  have haT : rho ⟨g * y * g⁻¹, huBs⟩ ∈ N2KCoordinate.coordT45 := by
    rw [hρu]
    exact Subgroup.zpow_mem _ (hT45) j
  have ha5 : orderOf (rho ⟨g * y * g⁻¹, huBs⟩) = 5 := by
    refine orderOf_eq_prime (hPow _) ?_
    intro h1
    have hker' : (⟨g * y * g⁻¹, huBs⟩ : Bs) ∈ rho.ker := h1
    rw [hRhoKer, Subgroup.mem_subgroupOf] at hker'
    have huo : orderOf (g * y * g⁻¹) = 5 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
    have huv : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers v :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, hvo])
    have hle : D ≤ Subgroup.zpowers y := by
      rw [hDyv]
      exact sup_le le_rfl (huv ▸ Subgroup.zpowers_le.mpr hker')
    have := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, hyo] at this
    norm_num at this
  have hPoint' : ∀ (b : Bs) (k : K), ((ψ (rho b) * k * (ψ (rho b))⁻¹ : K) : G) = b * k * b⁻¹ :=
    fun b k => congrArg Subtype.val (hPoint b k)
  have hψa : ((ψ (rho ⟨g * y * g⁻¹, huBs⟩) : K) : G) = g * y * g⁻¹ :=
    psi_rho_eq_of_conj ψ hsurj hker rho hPoint' hPow huK hu5
  have hα : alphaQ (ψ (rho ⟨g * y * g⁻¹, huBs⟩)) = ψ ((rho ⟨g * y * g⁻¹, huBs⟩) ^ m) := by
    apply Subtype.ext
    rw [halpha, hψa, hnu, map_pow, Subgroup.coe_pow, hψa]
  have hm1 : 1 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have hm5 : m < 5 := by rcases hm with rfl | rfl <;> norm_num
  have key := N2KActualPower.power_eq_one_or_four_of_whole_block ψ hsurj hker alphaQ C'' δ'' hδ''
    hblock haT ha5 hm1 hm5 hα
  rcases hm with rfl | rfl <;> omega

end Power

end CFSG.StandardType

end
