module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
public import CFSG.GroupTheory.CommutatorModSection

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem chiefSeries_z2_count_eq_one
    {L1 L2 S : Subgroup G} {a c : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hser : IsChiefSeriesFrom (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) c) : c = 1 := by
  classical
  have h1 : 1 ≤ c := one_le_chiefSeries_z2_of_caseI hF hB ha hSz hL2 hZI hser
  by_cases hJ1 : thompsonJ S ≤ Q1 L1 L2 S
  ·
    have hJ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S :=
      fun hJ2 => not_thompsonJ_le_q1_inf_q2 hF.1 (le_inf hJ1 hJ2)
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
    have hQ2S : Q2 L1 L2 S ≤ S := by
      conv_rhs => rw [hS2]
      exact le_sup_right
    have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
      have h : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
      rw [h, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
    have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
      rw [hsup2]
      have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      simpa [Q1, Q2, P1, P2, bigB_comm] using h
    have hL2sup : IsL2Quot (2 * a + 1) (oTwoQuot ↥(L2 ⊔ S)) := by
      have hsupQ : L2 ⊔ S = L2 ⊔ Q1 L2 L1 S := by
        rw [hsup2]
        simp [Q1, Q2, P1, P2, bigB_comm]
      rw [hsupQ]
      obtain ⟨eL⟩ := hL2
      exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
    obtain ⟨A, hAmax, hAQ2⟩ :=
      Ch3g316.exists_isMaxElemAbelian_not_le_pCoreOf (T := S) (Q := Q2 L1 L2 S) hJ2
    have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := A4.omegaOneCenterOf_le (Q2 L1 L2 S)
    have hZ2c : Z2 L1 L2 S ≤ Subgroup.centralizer (Q2 L1 L2 S : Set G) :=
      (A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S)).trans
        (A4.centerOf_le_centralizer (Q2 L1 L2 S))
    have hcomm : ⁅Z2 L1 L2 S, A ⊓ Q2 L1 L2 S⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hZ2c.trans (Subgroup.centralizer_le inf_le_right))
    have hTR := thompsonReplacement (R := Q2 L1 L2 S) (S := S) (V := Z2 L1 L2 S) (A := A)
      hQ2S hZ2Q2 isElemAbelian_z2 hAmax hcomm
    have hbound : (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (Z2 L1 L2 S) ≤ (A ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex A := by
      rw [hpCore2]
      exact hTR.1.trans hTR.2.1
    have hZ2H : Z2 L1 L2 S ≤ L2 ⊔ S := hZ2Q2.trans (hQ2S.trans le_sup_right)
    have hAH : A ≤ L2 ⊔ S := hAmax.1.trans le_sup_right
    have hAnR : ¬ A ≤ pCoreOf 2 (L2 ⊔ S) := by
      rw [hpCore2]
      exact hAQ2
    have hc1 : c ≤ 1 :=
      lemmaFF2_c_le_one (H := L2 ⊔ S) (V := Z2 L1 L2 S) (A := A) (m := 2 * a + 1) (c := c)
        (by omega) hL2sup isElemAbelian_z2 hZ2H hAmax.2.1 hAH hAnR hbound hser
    omega
  ·
    have h2 : c ≤ 2 := card_chiefSeries_z2_le_two hF hB ha hSz hL2 hJ1 hser
    by_contra hc1
    have hc2 : c = 2 := by omega
    rw [hc2] at hser
    exact str83_c_eq_two_false hF hB ha hSz hL2 hZI hJ1 hser

private theorem exists_chiefSeries_through
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {V : Subgroup G} (hVZ : V ≤ Z2 L1 L2 S) (hstep : IsChiefStep (L2 ⊔ S) V ⊥ V) :
    ∀ N : Subgroup G, IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) N → V ≤ N →
      ∃ n, IsChiefSeriesFrom (L2 ⊔ S) (Z2 L1 L2 S) N n ∧ 1 ≤ n ∧
        (n = 1 → ⁅N, oTwoUpper (L2 ⊔ S)⁆ ≤ V) := by
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hstepZ : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ V :=
    ⟨⟨hVZ, hstep.1.2⟩, ⟨bot_le, hstep.2.1.2⟩, hstep.2.2.1,
      fun K hK _ hKV => hstep.2.2.2 K ⟨hKV, hK.2⟩ bot_le hKV⟩
  have hnc : ¬ IsCentralStep (L2 ⊔ S) ⊥ V :=
    not_isCentralStep_bot_of_caseI hF hB ha hSz hL2 hZI hstepZ
  have hVnorm : L2 ⊔ S ≤ Subgroup.normalizer (V : Set G) :=
    D14.le_normalizer_of_isNormalIn hstepZ.1
  have hcommVH : ⁅V, L2 ⊔ S⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hVnorm
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) := isElemAbelian_z2
  have hZ2c : ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ Z2 L1 L2 S, x * y = y * x :=
    fun x hx y hy => (B6.isElemAbelian_iff.mp hZ2ea).1 x hx y hy
  have hZ2sq : ∀ x ∈ Z2 L1 L2 S, x * x = 1 :=
    fun x hx => by simpa [pow_two] using (B6.isElemAbelian_iff.mp hZ2ea).2 x hx
  intro N
  induction N using WellFoundedLT.induction with
  | _ N ih =>
    intro hN hVN
    by_cases hNV : N = V
    ·
      subst hNV
      exact ⟨1, IsChiefSeriesFrom.noncentral hstepZ hnc IsChiefSeriesFrom.bot, le_rfl,
        fun _ => (Subgroup.commutator_mono le_rfl (oTwoUpper_le _)).trans hcommVH⟩
    · have hVNlt : V < N := lt_of_le_of_ne hVN (Ne.symm hNV)
      obtain ⟨L, hL⟩ := (Set.toFinite {K : Subgroup G |
        IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) K ∧ V ≤ K ∧ K < N}).exists_maximal
        ⟨V, hstepZ.1, le_rfl, hVNlt⟩
      obtain ⟨hLN, hVL, hLVN⟩ := hL.1
      have hstepL : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) L N := by
        refine ⟨hN, hLN, hLVN, fun K hK hLK hKN => ?_⟩
        by_cases hKN' : K = N
        · exact Or.inr hKN'
        · exact Or.inl (le_antisymm
            (hL.2 ⟨hK, hVL.trans hLK, lt_of_le_of_ne hKN hKN'⟩ hLK) hLK)
      obtain ⟨n, hserL, hn1, hnkey⟩ := ih L hLVN hLN hVL
      by_cases hc : IsCentralStep (L2 ⊔ S) L N
      ·
        refine ⟨n, IsChiefSeriesFrom.central hstepL hc hserL, hn1, fun hn => ?_⟩
        have hLc : ⁅L, oTwoUpper (L2 ⊔ S)⁆ ≤ V := hnkey hn
        have hNle : N ≤ Z2 L1 L2 S := hN.1
        have hcommN : ⁅N, N⁆ ≤ V := by
          refine Subgroup.commutator_le.2 fun x hx y hy => ?_
          have hxy : ⁅x, y⁆ = 1 := by
            rw [commutatorElement_def, hZ2c x (hNle hx) y (hNle hy)]
            group
          rw [hxy]
          exact V.one_mem
        have hsq : ∀ x ∈ N, x * x ∈ V := by
          intro x hx
          rw [hZ2sq x (hNle hx)]
          exact V.one_mem
        have hP : oTwoUpper (L2 ⊔ S) ≤ centralizerMod V (⊤ : Subgroup G) N := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro g ⟨hgH, hgodd⟩
          have hgO : g ∈ oTwoUpper (L2 ⊔ S) := Subgroup.subset_closure ⟨hgH, hgodd⟩
          have hgNV : g ∈ Subgroup.normalizer (V : Set G) :=
            D14.le_normalizer_of_isNormalIn hstepZ.1 hgH
          refine ⟨Subgroup.mem_top g, hgNV, fun y hy => ?_⟩
          have hW : ∀ w ∈ L, g * w * g⁻¹ * w⁻¹ ∈ V := by
            intro w hw
            have h1 : ⁅w, g⁆ ∈ V := (Subgroup.commutator_le.mp hLc) w hw g hgO
            have h2 : ⁅g, w⁆ ∈ V := by
              rw [← commutatorElement_inv]
              exact V.inv_mem h1
            rwa [commutatorElement_def] at h2
          have hgm : ∀ y ∈ N, g ^ orderOf g * y * (g ^ orderOf g)⁻¹ * y⁻¹ ∈ V := by
            intro y _
            rw [pow_orderOf_eq_one]
            simp
          exact CFSG.GroupTheory.commutator_mem_of_odd_pow (X := N) (Y := V) (W := L)
            hstepL.2.2.1.le hVN hcommN hsq hgNV hW (fun y hy => hc g hgH y hy) hgodd hgm y hy
        refine Subgroup.commutator_le.2 fun x hx g hg => ?_
        have h1 : g * x * g⁻¹ * x⁻¹ ∈ V := (hP hg).2.2 x hx
        have h2 : ⁅g, x⁆ ∈ V := by rwa [commutatorElement_def]
        have h3 : ⁅x, g⁆ ∈ V := by
          rw [← commutatorElement_inv]
          exact V.inv_mem h2
        exact h3
      ·
        exact ⟨n + 1, IsChiefSeriesFrom.noncentral hstepL hc hserL, by omega,
          fun hn => absurd hn (by omega)⟩

theorem str83G4Z2Central_holds :
    Str83G4Z2Central := by
  intro G _ _ L1 L2 S a hfr V hVZ hstep
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hHleP2 : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hHN : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    hHleP2.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hZ2norm : IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHN hg) x).mp hx⟩
  obtain ⟨n, hser, -, hnkey⟩ :=
    exists_chiefSeries_through ⟨hF, hB, ha, hSz, hL2, hZI⟩ hVZ hstep
      (Z2 L1 L2 S) hZ2norm hVZ
  have hn : n = 1 := chiefSeries_z2_count_eq_one hF hB ha hSz hL2 hZI hser
  have hcommZ : ⁅Z2 L1 L2 S, oTwoUpper (L2 ⊔ S)⁆ ≤ V := hnkey hn
  have hstepZ : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ V :=
    ⟨⟨hVZ, hstep.1.2⟩, ⟨bot_le, hstep.2.1.2⟩, hstep.2.2.1,
      fun K hK _ hKV => hstep.2.2.2 K ⟨hKV, hK.2⟩ bot_le hKV⟩
  have hO : oTwoUpper (L2 ⊔ S) ≤ centralizerMod V (⊤ : Subgroup G) (Z2 L1 L2 S) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgH, hgodd⟩
    have hgO : g ∈ oTwoUpper (L2 ⊔ S) := Subgroup.subset_closure ⟨hgH, hgodd⟩
    refine ⟨Subgroup.mem_top g, D14.le_normalizer_of_isNormalIn hstepZ.1 hgH, fun x hx => ?_⟩
    have h1 : ⁅x, g⁆ ∈ V := (Subgroup.commutator_le.mp hcommZ) x hx g hgO
    have h2 : ⁅g, x⁆ ∈ V := by
      rw [← commutatorElement_inv]
      exact V.inv_mem h1
    rwa [commutatorElement_def] at h2
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hQ : Q2 L1 L2 S ≤ centralizerMod V (⊤ : Subgroup G) (Z2 L1 L2 S) := by
    intro q hq
    have hqH : q ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) (hQ2S hq)
    have hqx : ∀ x ∈ Z2 L1 L2 S, x * q = q * x :=
      Subgroup.mem_centralizer_iff.mp (hQ2C hq)
    refine ⟨Subgroup.mem_top q, D14.le_normalizer_of_isNormalIn hstepZ.1 hqH, fun x hx => ?_⟩
    have h1 : q * x * q⁻¹ * x⁻¹ = 1 := by
      rw [show q * x = x * q from (hqx x hx).symm]
      group
    rw [h1]
    exact V.one_mem
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
    rw [h, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hsup : L2 ⊔ S = oTwoUpper (L2 ⊔ S) ⊔ Q2 L1 L2 S := by
    have h := str86_u3H_eq_oTwoUpper_sup_q2 (n := 2 * a + 1) hF (by omega) hL2
    change L2 ⊔ Q2 L1 L2 S = oTwoUpper (L2 ⊔ Q2 L1 L2 S) ⊔ Q2 L1 L2 S at h
    rw [← hsup2] at h
    exact h
  have hHc : L2 ⊔ S ≤ centralizerMod V (⊤ : Subgroup G) (Z2 L1 L2 S) := by
    rw [hsup]
    exact sup_le hO hQ
  intro g hg x hx
  exact (hHc hg).2.2 x hx

end CFSG.Quasithin.Stroth

end
