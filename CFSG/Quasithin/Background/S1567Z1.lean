module

public import CFSG.Quasithin.Background.S1567Z6
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

@[expose] def Input15368Psi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E → GoldLine153 T V₁ E s →
          G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G) →
          VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s) →
          (∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀) →
          F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E) →
          (∀ g ∈ G0_153 T Mc M E s, g ∈ Subgroup.normalizer (E : Set G) →
            ∃ n : ℕ, g ^ 2 ^ n ∈ Subgroup.centralizer (E : Set G)) →
            pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G)

namespace S1567

section B

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem pCore_G0_le_TE (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ TE153 T E := by
  have hTEsyl : IsSylowTwoOf (TE153 T E) (G0_153 T Mc M E s) := by
    have := htriple.2.2.2
    rwa [G1_inf_G2 c L r66 r67 gl] at this
  have hQD : pCoreOf 2 (G0_153 T Mc M E s) ≤ G0_153 T Mc M E s := pCoreOf_le 2 _
  exact A4.le_of_normal_of_isSylowTwoOf hTEsyl hQD
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr (le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

theorem pCore_G0_le_centralizer_F (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (FE153 E s : Set G) := by
  have hG1D : G1_153 T Mc M E s ≤ G0_153 T Mc M E s := le_sup_left
  have hQT := pCore_G0_le_TE c L r66 r67 gl htriple
  have hQG1 : pCoreOf 2 (G0_153 T Mc M E s) ≤ G1_153 T Mc M E s := hQT.trans le_sup_right
  have hQn : G1_153 T Mc M E s ≤ Subgroup.normalizer (pCoreOf 2 (G0_153 T Mc M E s) : Set G) :=
    hG1D.trans (le_normalizer_pCoreOf 2 _)
  have hQ1 : pCoreOf 2 (G0_153 T Mc M E s) ≤ pCoreOf 2 (G1_153 T Mc M E s) :=
    le_pCoreOf_of_le_normalizer 2 hQG1 hQn (pCoreOf_isPGroup 2 _)
  rw [G1_eq_conj r66 gl, ← CFSG.QuasithinUnique.C5.conjSubgroup_pCoreOf, r66.pCore_YETE,
    CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer] at hQ1
  exact hQ1.trans inf_le_right

theorem TE_inf_centralizer_E_F_le (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    TE153 T E ⊓ Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer (FE153 E s : Set G) ≤
      Subgroup.centralizer (VZ T M : Set G) := by
  have hsT : s ∈ T := gl.s_mem.1
  have hTEn : T ≤ Subgroup.normalizer (TE153 T E : Set G) := T_le_normalizer_TE r66
  have hss : s * s ∈ TE153 T E := by
    rcases coset_of_relIndex_two r66.relIndex_two (T.mul_mem hsT hsT) hsT gl.s_not_mem with h | h
    · exact h
    · exact absurd (by simpa using h) gl.s_not_mem
  have hssE : s * s ∈ Subgroup.normalizer (E : Set G) := hss.2
  have hFE : conjSubgroup (FE153 E s) s = E := by
    show conjSubgroup (conjSubgroup E s) s = E
    rw [conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr hssE
  have hFg : ∀ g ∈ TE153 T E, conjSubgroup (FE153 E s) g = FE153 E s := by
    intro g hg
    show conjSubgroup (conjSubgroup E s) g = conjSubgroup E s
    rw [conjSubgroup_conjSubgroup]
    have hg' : s * g * s⁻¹ ∈ TE153 T E := (Subgroup.mem_normalizer_iff.mp (hTEn hsT) g).mp hg
    have : s * g = (s * g * s⁻¹) * s := by group
    rw [this, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hg'.2]
  by_contra hN
  set N : Subgroup G := TE153 T E ⊓ Subgroup.centralizer (E : Set G) ⊓
    Subgroup.centralizer (FE153 E s : Set G) with hNdef
  have hNT : N ≤ T := (inf_le_left.trans inf_le_left).trans inf_le_left
  have hTEN : TE153 T E ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [← conjSubgroup_eq_iff_mem_normalizer, hNdef, CFSG.QuasithinUnique.C5.conjSubgroup_inf,
      CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg),
      conjSubgroup_eq_iff_mem_normalizer.mpr hg.2, hFg g hg]
  have hsN : s ∈ Subgroup.normalizer (N : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, hNdef, CFSG.QuasithinUnique.C5.conjSubgroup_inf,
      CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (hTEn hsT), hFE]
    show TE153 T E ⊓ Subgroup.centralizer (conjSubgroup E s : Set G) ⊓ Subgroup.centralizer (E : Set G) = _
    exact inf_right_comm _ _ _
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rcases coset_of_relIndex_two r66.relIndex_two hx hsT gl.s_not_mem with h | h
    · exact hTEN h
    · have : x = (x * s⁻¹) * s := by group
      rw [this]
      exact (Subgroup.normalizer _).mul_mem (hTEN h) hsN
  obtain ⟨q, hqN, -, -, e, he, hne⟩ := exists_central_move c L hNT hTN hN
  apply hne
  have h1 := Subgroup.mem_centralizer_iff.mp hqN.1.2 e he
  calc q * e * q⁻¹ = (e * q) * q⁻¹ := by rw [h1]
    _ = e := by group

omit [Finite G] in
theorem mul_self_mem_centralizer_of_mem_TE (r66 : Res15366B T Mc M V₁ V₂ E) {q : G}
    (hq : q ∈ TE153 T E) (hqV : q ∈ Subgroup.normalizer (VZ T M : Set G)) :
    q * q ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have h1 := conjAct_mem_autOn hqV hq
  have h2 : conjAct (VZ T M) ⟨q, hqV⟩ ^ 2 = 1 := r66.barTE_klein.1.2.2 _ h1
  have hqqV : q * q ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer _).mul_mem hqV hqV
  have h3 : conjAct (VZ T M) ⟨q * q, hqqV⟩ = 1 := by
    have : conjAct (VZ T M) ⟨q * q, hqqV⟩ = conjAct (VZ T M) ⟨q, hqV⟩ ^ 2 := by
      rw [← map_pow, pow_two]
      rfl
    rw [this, h2]
  exact (conjAct_eq_one_iff''' _ _).1 h3

theorem pCore_G0_le_centralizer_E_of_YE_le (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G))
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E))
    (hYD : YE153 Mc M E ≤ G0_153 T Mc M E s) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G) := by
  intro q hq
  have hqD : q ∈ G0_153 T Mc M E s := pCoreOf_le 2 _ hq
  have hqTE : q ∈ TE153 T E := pCore_G0_le_TE c L r66 r67 gl htriple hq
  have hqV : q ∈ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer (c.hyp.T_le hqTE.1)
  by_contra hqC
  have hmove : ∃ e ∈ E, q * e * q⁻¹ ≠ e := by
    by_contra hno
    push Not at hno
    apply hqC
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have := hno e he
    calc e * q = (q * e * q⁻¹) * q := by rw [this]
      _ = q * e := by group
  obtain ⟨y, hyY, hyc⟩ := exists_comm_not_centralizer h113 c L hqTE
    (mul_self_mem_centralizer_of_mem_TE r66 hqTE hqV) hmove
  apply hyc
  have hyD : y ∈ G0_153 T Mc M E s := hYD hyY
  have hqN : q ∈ Subgroup.normalizer (YE153 Mc M E : Set G) := h1 hqD
  have hm1 : y * q * y⁻¹ * q⁻¹ ∈ YE153 Mc M E := by
    have h3 : q * y⁻¹ * q⁻¹ ∈ YE153 Mc M E :=
      (Subgroup.mem_normalizer_iff.mp hqN y⁻¹).mp ((YE153 Mc M E).inv_mem hyY)
    have : y * q * y⁻¹ * q⁻¹ = y * (q * y⁻¹ * q⁻¹) := by group
    rw [this]
    exact (YE153 Mc M E).mul_mem hyY h3
  have hm2 : y * q * y⁻¹ * q⁻¹ ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
    have h3 : y * q * y⁻¹ ∈ pCoreOf 2 (G0_153 T Mc M E s) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hyD) q).mp hq
    exact (pCoreOf 2 _).mul_mem h3 ((pCoreOf 2 _).inv_mem hq)
  have hle : YE153 Mc M E ⊓ pCoreOf 2 (G0_153 T Mc M E s) ≤ pCoreOf 2 (YE153 Mc M E) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun y' hy' => ?_)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy', le_normalizer_pCoreOf 2 _ (hYD hy')⟩
  have h4 := hle ⟨hm1, hm2⟩
  rw [pCoreOf_YE c r66] at h4
  exact h4.2

theorem pCore_G0_le_centralizer_E_of_order_three (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s)
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E))
    {g : G} (hgD : g ∈ G0_153 T Mc M E s) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hg1 : conjAct E ⟨g, hgE⟩ ≠ 1) (hg3 : conjAct E ⟨g, hgE⟩ ^ 3 = 1) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G) := by
  have := isKleinFour_E c L
  have hQT := pCore_G0_le_TE c L r66 r67 gl htriple
  have key := eq_one_of_normal_two_group (conjAct E)
    (D := (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (Subgroup.normalizer (E : Set G)))
    (h := (⟨g, hgE⟩ : ↥(Subgroup.normalizer (E : Set G)))) ?_ ?_ hg1 hg3
  · intro q hq
    have hqN : q ∈ Subgroup.normalizer (E : Set G) := (hQT hq).2
    exact (conjAct_eq_one_iff''' E ⟨q, hqN⟩).1 (key ⟨q, hqN⟩ (Subgroup.mem_subgroupOf.mpr hq))
  · intro d hd
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 _ ⟨d.1, Subgroup.mem_subgroupOf.mp hd⟩
    refine ⟨n, ?_⟩
    rw [← map_pow]
    have : d ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [this, map_one]
  · intro d hd
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hgD) d.1).mp
      (Subgroup.mem_subgroupOf.mp hd)
    simpa using h1

end B

end S1567

theorem stage15368Two_of_named_inputs (hΨ : Input15368Psi) : Stage15368Two := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl h1 hV hSyl htriple
  have hQF := S1567.pCore_G0_le_centralizer_F c L r66 r67 gl htriple
  have hQT := S1567.pCore_G0_le_TE c L r66 r67 gl htriple
  have hQE : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G) := by
    by_cases hall : ∀ g ∈ G0_153 T Mc M E s, g ∈ Subgroup.normalizer (E : Set G) →
        ∃ n : ℕ, g ^ 2 ^ n ∈ Subgroup.centralizer (E : Set G)
    · exact hΨ G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl h1 hV hSyl htriple hall
    · push Not at hall
      obtain ⟨g, hgD, hgE, hgn⟩ := hall
      have := isKleinFour_E c L
      have hS3 : ∀ γ : MulAut ↥E, γ ^ 2 = 1 ∨ γ ^ 3 = 1 := by
        intro γ
        have key : ∀ x : Equiv.Perm (Fin 3), x ^ 2 = 1 ∨ x ^ 3 = 1 := by decide +kernel
        rcases key (CFSG.kleinFourAutomorphismEquivSymmetricThree ↥E γ) with h | h
        · left
          apply (CFSG.kleinFourAutomorphismEquivSymmetricThree ↥E).injective
          rw [map_pow, h, map_one]
        · right
          apply (CFSG.kleinFourAutomorphismEquivSymmetricThree ↥E).injective
          rw [map_pow, h, map_one]
      have hpow : ∀ m : ℕ, conjAct E ⟨g, hgE⟩ ^ m = 1 → g ^ m ∈ Subgroup.centralizer (E : Set G) := by
        intro m hm
        have hmN : g ^ m ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hgE m
        have e1 : conjAct E ⟨g, hgE⟩ ^ m = conjAct E ⟨g ^ m, hmN⟩ := by
          rw [← map_pow]
          rfl
        rw [e1] at hm
        exact (conjAct_eq_one_iff''' E ⟨g ^ m, hmN⟩).1 hm
      rcases hS3 (conjAct E ⟨g, hgE⟩) with h2 | h3
      · exact absurd (hpow 2 h2) (by simpa using hgn 1)
      · have hne : conjAct E ⟨g, hgE⟩ ≠ 1 := fun h => absurd (hpow 1 (by simpa using h)) (by simpa using hgn 0)
        exact S1567.pCore_G0_le_centralizer_E_of_order_three c L r66 r67 gl htriple hgD hgE hne h3
  exact fun x hx => S1567.TE_inf_centralizer_E_F_le c L r66 gl ⟨⟨hQT hx, hQE hx⟩, hQF hx⟩

end CFSG.Quasithin
