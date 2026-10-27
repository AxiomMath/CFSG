module

public import CFSG.Quasithin.Background.C41PfY
public import CFSG.Quasithin.MS93.Burnside.C134Big
public import CFSG.Quasithin.Background.C41PfQ
public import CFSG.Quasithin.Background.C41PfX

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem burnsideC41w_c47_case3_big (h134 : MS93.burnsideC134w_AS_C_1_34_corrBig) {H R M L V K : Subgroup G}
    (hP : C41Post H R M L V K)
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hc : SBc17.C27SL3 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 < n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (ModO2 K ≃* ↥(StatedSL 3 F)) ∧ IsMSPair (K ⊔ R) R ∧
      (IsC134Case 1 (K ⊔ R) R K ∨ IsC134Case 2 (K ⊔ R) R K ∨ IsC134Case 3 (K ⊔ R) R K ∨
        MS93.IsC134Case4Corr (K ⊔ R) R K) ∧
      IsMaxParabolic2 K (M ⊓ K) ∧ IsPSL 2 2 n (ModO2 (conjClosure L M)) ∧
      (IsStabilizedLineOfNatural F R M K V ∨
        (IsC134Case 2 (K ⊔ R) R K ∧ ∃ V₁ V₂ : Subgroup G,
          IsStabilizedLineOfNatural F R M K V₁ ∧ IsStabilizedLineOfNatural F R M K V₂ ∧
            V = V₁ ⊔ V₂)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW
  set M0 := conjClosure L M with hM0
  have h := hP.hyp
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_omegaOneCenter K R
  have hM0K : M0 ≤ K := hP.le
  have hNK : M0 ≤ Subgroup.normalizer (K : Set G) := hM0K.trans Subgroup.le_normalizer
  obtain ⟨⟨n, F, iF, fF, hn1, hF, ⟨e⟩⟩, hmax, hMS⟩ := hc
  let φ : ↥K →* ↥(autOn K W) :=
    ((conjAct W).comp (Subgroup.inclusion hKN)).codRestrict (autOn K W) fun k =>
      ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφ1 : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro k
    have h0 := A4.conjAct_eq_one_iff (g := Subgroup.inclusion hKN k)
    exact ⟨fun h => h0.mp (congrArg Subtype.val h), fun h => Subtype.ext (h0.mpr h)⟩
  have hO2W : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G) :=
    pCoreOf_le_centralizer hP.le_normalizer
  have hnt : ¬ K ≤ Subgroup.centralizer (W : Set G) := by
    intro hle
    have h2 : ∀ c : ↥(StatedSL 3 F), c = 1 := by
      intro c
      obtain ⟨k, hk⟩ := hφ (e.symm c)
      have hk1 : φ k = 1 := (hφ1 k).mpr (hle k.2)
      have h3 : e.symm c = 1 := hk.symm.trans hk1
      calc c = e (e.symm c) := (e.apply_symm_apply c).symm
        _ = 1 := by rw [h3, map_one]
    have hF2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hcard := card_statedSL_three' F
    have hc1 : Nat.card ↥(StatedSL 3 F) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (h2 a).trans (h2 b).symm⟩, ⟨1⟩⟩
    rw [hc1] at hcard
    have : 2 ^ 3 ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_left hF2 3
    have h3 : 1 ≤ (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 3 - 1) := by
      have : 4 ≤ Fintype.card F ^ 2 := by nlinarith
      have : 8 ≤ Fintype.card F ^ 3 := by nlinarith
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    nlinarith
  have hsq : SQTKGroup (↥K ⧸ CFSG.pCore 2 ↥K) := S153D.sqtkGroup_quot_pCore (h.sqtk.mono hKH)
  have hL345 : IsL345Type ↥(autOn K W) :=
    Or.inl ⟨n, F, iF, inferInstance, by rw [Nat.card_eq_fintype_card, hF], ⟨e⟩⟩
  obtain ⟨f⟩ := S153D.nonempty_quot_mulEquiv_autOn asA36NoOddCover_holds hKN hP.quasi hsq hO2W
    hnt hL345
  have hmemK : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', he⟩
      rwa [show k = k' from Subtype.ext he.symm]
  have hkerφ : φ.ker = CFSG.pCore 2 ↥K := by
    have hle : CFSG.pCore 2 ↥K ≤ φ.ker := fun k hk =>
      MonoidHom.mem_ker.mpr ((hφ1 k).mpr (hO2W ((hmemK k).mp hk)))
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    have hc2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr f.toEquiv] at hc1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv] at hc2
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc1.symm.trans hc2)).symm.le
  have hCK : K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rintro x ⟨hxK, hxC⟩
    have hk : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := MonoidHom.mem_ker.mpr ((hφ1 _).mpr hxC)
    rw [hkerφ] at hk
    exact (hmemK _).mp hk
  set α₀ : ↥K →* ↥(StatedSL 3 F) := e.toMonoidHom.comp φ with hα₀
  have hα₀ : IsModO2Surj K α₀ := by
    refine ⟨e.surjective.comp hφ, ?_⟩
    rw [hα₀, MonoidHom.ker_comp_of_injective φ _ e.injective, hkerφ]
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    have hF2 : Fintype.card F = 2 := by rw [hF, hn, pow_one]
    exact false_of_isSolvable_autOn h1 hP.le (C2Nine.conjClosure_le_M h)
      (C2Nine.perfect_conjClosure_of_hyp h)
      (fun hb => ne_bot_of_mem_cComp h.comp (eq_bot_iff.mpr ((le_conjClosure L M).trans hb.le)))
      (isSolvable_of_c27SL3_two hF2 e hmax)
  have hO2KR : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 K)
        (hP.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)))
      (pCoreOf_isPGroup 2 K)
  have hKRR : pCoreOf 2 (K ⊔ R) ≤ R := pCoreOf_sup_le_of_hyp h hKH hNK
  have hO2R : pCoreOf 2 K ≤ R := hO2KR.trans hKRR
  have hCM : K ⊓ Subgroup.centralizer (W : Set G) ≤ M ⊓ K := fun x hx =>
    ⟨h.le_M (hO2R (hCK hx)), hx.1⟩
  have hMKmax : IsMaxParabolic2 K (M ⊓ K) :=
    isMaxParabolic2_of_autOn hKN inf_le_right hCM hCK hmax
  have hKc : K ∈ cComp (K ⊔ R) :=
    cComp_mem_of_le hP.comp le_sup_left (sup_le hKH (h.le_M.trans h.le_H))
  have hset : ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K R hP.le_normalizer
  obtain ⟨i, hi⟩ := h134 G (K ⊔ R) R K hMS hKc hset ⟨n, F, iF, fF, α₀, hn2, hF, hα₀⟩
  set Q := c134Q (K ⊔ R) K with hQ
  have hM0V : M0 ≤ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right V M0
    rwa [h.V_comm] at this
  have hO2M0R : pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 (M0 ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 (hKRR.trans le_sup_right)
      (sup_le ((hM0K.trans le_sup_left).trans (le_normalizer_pCoreOf 2 (K ⊔ R)))
        (le_sup_right.trans (le_normalizer_pCoreOf 2 (K ⊔ R))))
      (pCoreOf_isPGroup 2 _)
  have hVcen : ∀ v ∈ V, ∀ q ∈ pCoreOf 2 (M0 ⊔ R), q * v = v * q := fun v hv q hq =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h.V_center hv)).2 q hq
  have hVK : V ≤ K := h.V_le.trans hM0K
  have hVO : V ≤ pCoreOf 2 K := fun v hv => hP.charTwo
    ⟨hVK hv, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      hVcen v hv q (hO2M0R (hO2KR hq))⟩
  have hVKR : V ≤ pCoreOf 2 (K ⊔ R) := hVO.trans hO2KR
  have hVQ : V ≤ Q := by
    calc V = ⁅V, M0⁆ := h.V_comm.symm
      _ ≤ ⁅pCoreOf 2 (K ⊔ R), K⁆ := Subgroup.commutator_mono hVKR hM0K
  have hQO : Q ≤ pCoreOf 2 (K ⊔ R) := by
    rw [hQ, c134Q, Subgroup.commutator_le]
    intro q hq k hk
    have h3 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 (K ⊔ R) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K ⊔ R)
        (Subgroup.mem_sup_left hk)) _).mp ((pCoreOf 2 (K ⊔ R)).inv_mem hq)
    have e : ⁅q, k⁆ = q * (k * q⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 (K ⊔ R)).mul_mem hq h3
  have hVZQ : V ≤ centerOf Q := fun v hv =>
    ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun q hq => hVcen v hv q (hO2M0R (hQO hq))⟩
  have hVW0 : V ≤ W := fun v hv =>
    mem_omegaOneCenterOf (hVKR hv) (fun y hy => hVcen v hv y (hO2M0R hy)) (h.V_elem.2 v hv)
  have hVZ : V ≤ ⁅W, K⁆ := by
    calc V = ⁅V, M0⁆ := h.V_comm.symm
      _ ≤ ⁅W, K⁆ := Subgroup.commutator_mono hVW0 hM0K
  have hVZQK : V ≤ ⁅centerOf Q, K⁆ := by
    calc V = ⁅V, M0⁆ := h.V_comm.symm
      _ ≤ ⁅centerOf Q, K⁆ := Subgroup.commutator_mono hVZQ hM0K
  have hmod : ∀ {F' : Type} [Field F'] [Fintype F'] {α' : ↥K →* ↥(StatedSL 3 F')},
      IsModO2Surj K α' → Nonempty (ModO2 K ≃* ↥(StatedSL 3 F')) := fun hα' =>
    ⟨(QuotientGroup.quotientMulEquivOfEq hα'.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hα'.1)⟩
  have hn' : ∀ {F' : Type} [Field F'] [Fintype F'] {n' : ℕ} {α' : ↥K →* ↥(StatedSL 3 F')},
      Fintype.card F' = 2 ^ n' → IsModO2Surj K α' → 2 ≤ n' := by
    intro F' _ _ n' α' hF' hα'
    have := card_eq_of_modO2Surj hα₀ hα'
    rw [hF, hF'] at this
    have hnn : n = n' := Nat.pow_right_injective le_rfl this
    omega
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi =>
    have hcase : IsC134Case1 (K ⊔ R) R K := hi
    obtain ⟨hblk, n', F', iF', fF', hF', hnat⟩ := id hcase
    obtain ⟨α', β', hW'⟩ :=
      (isNaturalSection_iff_exists_with K Q ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F')).mp hnat
    have hα' : IsModO2Surj K α' := ⟨hW'.2.1, hW'.2.2.1⟩
    have h2n := hn' hF' hα'
    obtain ⟨hline, hpsl⟩ := c47_line_one hP h2n hF' α' hW' hMKmax hVQ hVZ
    exact ⟨n', F', iF', fF', by omega, hF', hmod hα', hMS, Or.inl hcase, hMKmax, hpsl,
      Or.inl hline⟩
  | 2, hi =>
    have hcase : IsC134Case2 (K ⊔ R) R K := hi
    obtain ⟨⟨n', F', iF', fF', α', hF', hα', hsum⟩, -⟩ := id hcase
    have h2n := hn' hF' hα'
    obtain ⟨hlines, hpsl⟩ := c47_line_two hP h2n hF' α' hα' hsum hMKmax hVQ hVZ
    refine ⟨n', F', iF', fF', by omega, hF', hmod hα', hMS, Or.inr (Or.inl hcase), hMKmax,
      hpsl, ?_⟩
    rcases hlines with hl | ⟨V₁, V₂, hl₁, hl₂, hV⟩
    · exact Or.inl hl
    · exact Or.inr ⟨hcase, V₁, V₂, hl₁, hl₂, hV⟩
  | 3, hi =>
    have hcase : IsC134Case3 (K ⊔ R) R K := hi
    obtain ⟨⟨n', F', iF', fF', α', hF', hα', hZ, -⟩, -⟩ := id hcase
    have h2n := hn' hF' hα'
    obtain ⟨β', hW'⟩ := natWith_of_sumOne hα' hZ
    obtain ⟨hline, hpsl⟩ := c47_line_one hP h2n hF' α' hW' hMKmax hVZQ hVZ
    exact ⟨n', F', iF', fF', by omega, hF', hmod hα', hMS, Or.inr (Or.inr (Or.inl hcase)),
      hMKmax, hpsl, Or.inl hline⟩
  | 4, hi =>
    have hcase : MS93.IsC134Case4Corr (K ⊔ R) R K := hi
    obtain ⟨⟨n', F', iF', fF', α', hF', hα', -, -, -, hU, -⟩, -⟩ := id hcase
    have h2n := hn' hF' hα'
    obtain ⟨β', hW'⟩ := natWith_of_sumOne hα' hU
    obtain ⟨hline, hpsl⟩ := c47_line_one hP h2n hF' α' hW' hMKmax hVZQK hVZ
    exact ⟨n', F', iF', fF', by omega, hF', hmod hα', hMS, Or.inr (Or.inr (Or.inr hcase)),
      hMKmax, hpsl, Or.inl hline⟩
  | 5, hi =>
    exfalso
    have hcase : IsC134Case5 (K ⊔ R) R K := hi
    obtain ⟨⟨α5, hα5, -⟩, -⟩ := id hcase
    have := card_eq_of_modO2Surj hα₀ hα5
    rw [hF, ZMod.card] at this
    have h22 : 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  | k + 6, hi => exact hi.elim

end CFSG.Quasithin.C41Pf
