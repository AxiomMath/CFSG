module

public import CFSG.Quasithin.EmptyFaithful.T1531In68
public import CFSG.Quasithin.EmptyFaithful.S146Six
public import CFSG.Quasithin.EmptyFaithful.S146S3
public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.EmptyFaithful.T1531In66a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section General

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_eq_three' {A P : Subgroup G} (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (h3 : (pCoreOf 2 A).relIndex A = 3) (hsyl : IsSylowTwoOf P (A ⊔ P)) :
    P.relIndex (A ⊔ P) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOP : pCoreOf 2 A ≤ P := by
    refine A4.le_of_normal_of_isSylowTwoOf hsyl
      ((pCoreOf_le 2 A).trans le_sup_left) ?_ (pCoreOf_isPGroup 2 A)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 A).trans le_sup_left)]
    exact sup_le (le_normalizer_pCoreOf 2 A) (hPA.trans (normalizer_le_normalizer_pCoreOf 2 A))
  have h1 := Subgroup.relIndex_mul_card P (A ⊔ P)
  rw [inf_eq_left.mpr le_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (A ⊓ P) A
  rw [inf_eq_left.mpr inf_le_left] at h2
  have h3' := S143.card_sup_mul_card_inf_of_le_normalizer hPA
  have hP0 : 0 < Nat.card P := Nat.card_pos
  have hAP0 : 0 < Nat.card ↥(A ⊓ P) := Nat.card_pos
  have heq : P.relIndex (A ⊔ P) = (A ⊓ P).relIndex A := by
    have h4 : P.relIndex (A ⊔ P) * (Nat.card P * Nat.card ↥(A ⊓ P)) =
        (A ⊓ P).relIndex A * (Nat.card P * Nat.card ↥(A ⊓ P)) := by
      calc P.relIndex (A ⊔ P) * (Nat.card P * Nat.card ↥(A ⊓ P))
          = (P.relIndex (A ⊔ P) * Nat.card P) * Nat.card ↥(A ⊓ P) := by ring
        _ = Nat.card ↥(A ⊔ P) * Nat.card ↥(A ⊓ P) := by rw [h1]
        _ = Nat.card A * Nat.card P := h3'
        _ = (A ⊓ P).relIndex A * Nat.card ↥(A ⊓ P) * Nat.card P := by rw [h2]
        _ = (A ⊓ P).relIndex A * (Nat.card P * Nat.card ↥(A ⊓ P)) := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hP0 hAP0) h4
  rw [heq]
  have hdvd : (A ⊓ P).relIndex A ∣ 3 :=
    h3 ▸ Subgroup.relIndex_dvd_of_le_left A (le_inf (pCoreOf_le 2 A) hOP)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    have hAP : A ≤ P := (Subgroup.relIndex_eq_one.mp (Subgroup.inf_relIndex_left A P ▸ h)).trans
      le_rfl
    have hA2 : IsPGroup 2 A := hsyl.2.1.to_le hAP
    have hO : pCoreOf 2 A = A := by
      refine le_antisymm (pCoreOf_le 2 A) ?_
      exact le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hA2
    rw [hO, Subgroup.relIndex_self] at h3
    omega
  · exact h

theorem normalCore_eq_pCore' {A : Type*} [Group A] [Finite A] {P : Subgroup A} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) : P.normalCore = Open.pCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact le_pCore 2 (Subgroup.normalCore_normal P) (hP.to_le (Subgroup.normalCore_le P))
  · have hN : (Open.pCore 2 A).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rw [Subgroup.normal_le_normalCore]
    exact (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal (hP.toSylow hidx)

theorem nonempty_quotient_pCore_of_relIndex_eq_three' {P K : Subgroup G}
    (hsyl : IsSylowTwoOf P K) (h3 : P.relIndex K = 3)
    (hN : ¬ K ≤ Subgroup.normalizer (P : Set G)) :
    Nonempty (↥K ⧸ Open.pCore 2 ↥K ≃* Equiv.Perm (Fin 3)) := by
  rcases gold_normalCore_quotient_equiv (A := ↥K) (H := P.subgroupOf K) h3 with
    ⟨h, -⟩ | ⟨-, ⟨e⟩⟩
  · exfalso
    apply hN
    have hle := (P.subgroupOf K).normalCore_le
    have heq : (P.subgroupOf K).normalCore = P.subgroupOf K := by
      have : (P.subgroupOf K).FiniteIndex :=
        ⟨by rw [show (P.subgroupOf K).index = 3 from h3]; norm_num⟩
      have h1 := Subgroup.relIndex_mul_index hle
      rw [h, show (P.subgroupOf K).index = 3 from h3] at h1
      have h2 : (P.subgroupOf K).normalCore.relIndex (P.subgroupOf K) = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
    have hnorm : (P.subgroupOf K).Normal := heq ▸ Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsyl.1).mp hnorm
  · have hcore : (P.subgroupOf K).normalCore = Open.pCore 2 ↥K :=
      normalCore_eq_pCore' (A4.isPGroup_subgroupOf_of_le hsyl.1 hsyl.2.1) hsyl.2.2
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans e⟩

omit [Finite G] in
theorem conjSubgroup_sup' (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g :=
  Subgroup.map_sup _ _ _

theorem isPGroup_conjSubgroup' {A : Subgroup G} (hA : IsPGroup 2 A) (g : G) :
    IsPGroup 2 (conjSubgroup A g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA
  exact IsPGroup.of_card (n := n) (by rw [E3.card_conjSubgroup, hn])

theorem isSylowTwoOf_conjSubgroup' {P H : Subgroup G} (h : IsSylowTwoOf P H) (g : G) :
    IsSylowTwoOf (conjSubgroup P g) (conjSubgroup H g) := by
  refine ⟨E3.conjSubgroup_mono_left g h.1, isPGroup_conjSubgroup' h.2.1 g, ?_⟩
  show ¬ 2 ∣ (conjSubgroup P g).relIndex (conjSubgroup H g)
  rw [E3.relIndex_conjSubgroup]
  exact h.2.2

omit [Finite G] in
theorem relIndex_pCoreOf_eq_three' {L : Subgroup G}
    (e : OTwoQuot L ≃* Multiplicative (ZMod 3)) : (pCoreOf 2 L).relIndex L = 3 := by
  have h3 : (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  show ((pCoreOf 2 L).subgroupOf L).index = 3
  rw [h3, Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd]
  simp

theorem nonempty_oTwoQuot_conjSubgroup' {A : Subgroup G} (g : G)
    (h : Nonempty (OTwoQuot A ≃* Equiv.Perm (Fin 3))) :
    Nonempty (↥(conjSubgroup A g) ⧸ Open.pCore 2 ↥(conjSubgroup A g) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := h
  let φ : ↥(conjSubgroup A g) →* ↥A :=
    ((MulAut.conj g).toMonoidHom.comp (conjSubgroup A g).subtype).codRestrict A
      (fun x => mem_conjSubgroup_iff.mp x.2)
  have hφ : ∀ x : ↥(conjSubgroup A g), ((φ x : ↥A) : G) = g * (x : G) * g⁻¹ := fun x => rfl
  refine nonempty_quot_perm3_of_surjective ((psiOf e).comp φ) ?_ ?_
  · intro σ
    obtain ⟨a, ha⟩ := psiOf_surjective e σ
    have hx : g⁻¹ * (a : G) * g ∈ conjSubgroup A g := by
      rw [mem_conjSubgroup_iff]
      have : g * (g⁻¹ * (a : G) * g) * g⁻¹ = a := by group
      rw [this]
      exact a.2
    refine ⟨⟨_, hx⟩, ?_⟩
    have : φ ⟨_, hx⟩ = a := Subtype.ext (by rw [hφ]; group)
    show psiOf e (φ ⟨_, hx⟩) = σ
    rw [this, ha]
  · intro y
    have hy : (psiOf e) (φ (y : ↥(conjSubgroup A g))) = 1 := y.2
    have hmem := (psiOf_eq_one_iff e (φ y)).mp hy
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 A ⟨_, hmem⟩
    refine ⟨k, ?_⟩
    have h1 : ((φ (y : ↥(conjSubgroup A g)) : ↥A) : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥(pCoreOf 2 A) => ((z : ↥(pCoreOf 2 A)) : G)) hk
      simpa using this
    rw [hφ] at h1
    have h2 : (g * (y : G) * g⁻¹) ^ 2 ^ k = g * (y : G) ^ 2 ^ k * g⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow]; rfl
    rw [h2] at h1
    have h3 : (y : G) ^ 2 ^ k = 1 := by
      calc (y : G) ^ 2 ^ k = g⁻¹ * (g * (y : G) ^ 2 ^ k * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    apply Subtype.ext
    apply Subtype.ext
    simpa using h3

end General

section Stage68b

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem isPGroup_TE (c : Ctx153 G T Mc M V₁ V₂ t) : IsPGroup 2 (TE153 T E) :=
  c.hyp.qtfe.sylow.1.to_le inf_le_left

theorem TE_ne_bot (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E) :
    TE153 T E ≠ ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, ⟨t₀, ht₀, e, -, hne⟩, -⟩ := line_facts c L
  intro h
  rw [h, Subgroup.mem_bot] at ht₀
  apply hne
  rw [ht₀]
  group

theorem normalizer_TE_le (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) : Subgroup.normalizer (TE153 T E : Set G) ≤ M :=
  (normalizer_le_normalizer_thompsonJ _).trans
    ((S1414.normalizer_thompsonJ_le_CGS (isPGroup_TE c) (TE_ne_bot c L)).trans r67.CGS_le)

omit [Finite G] in
theorem T_le_normalizer_TE (r66 : Res15366B T Mc M V₁ V₂ E) :
    T ≤ Subgroup.normalizer (TE153 T E : Set G) := by
  have hn : ((TE153 T E).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two r66.relIndex_two
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

omit [Finite G] in
theorem card_T_eq_two_mul_TE (r66 : Res15366B T Mc M V₁ V₂ E) :
    Nat.card T = 2 * Nat.card (TE153 T E) := by
  have hr := Subgroup.relIndex_mul_card (TE153 T E) T
  rw [inf_eq_left.2 (inf_le_left : TE153 T E ≤ T), r66.relIndex_two] at hr
  exact hr.symm

omit [Finite G] in
theorem centralizer_le_TE (L : LineData153 T M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) :
    Subgroup.centralizer (VZ T M : Set G) ≤ TE153 T E := by
  intro g hg
  refine ⟨?_, ((Subgroup.centralizer_le L.le_V).trans (Subgroup.centralizer_le_normalizer _)) hg⟩
  have : g ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rw [r67.R_eq]
    exact hg
  exact this.1

theorem sylow_of_inM_153 (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r45 : Res15345 T Mc M V₁ V₂) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    {M₀ : Subgroup G} (hM₀ : InM (G0_153 T Mc M E s) M₀) : IsSylowTwoOf (TE153 T E) M₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  have hTEp : IsPGroup 2 (TE153 T E) := isPGroup_TE c
  have hTEG1 : TE153 T E ≤ G1_153 T Mc M E s := le_sup_right
  have hTEG0 : TE153 T E ≤ G0_153 T Mc M E s := hTEG1.trans le_sup_left
  have hTEM₀ : TE153 T E ≤ M₀ := hTEG0.trans hM₀.2
  obtain ⟨S₀, hS₀, hTES₀⟩ := exists_isSylowTwoOf_ge' hTEM₀ hTEp
  have hlt : TE153 T E < S₀ :=
    lt_of_le_of_ne hTES₀ (fun h => hns (by rw [h]; exact hS₀))
  obtain ⟨x, hxS₀, hxTE, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hS₀.2.1 hlt
  have hxM : x ∈ M := normalizer_TE_le c L r67 hxN
  set T₁ : Subgroup G := TE153 T E ⊔ Subgroup.zpowers x with hT₁
  have hT₁S₀ : T₁ ≤ S₀ := sup_le hTES₀ (Subgroup.zpowers_le.2 hxS₀)
  have hT₁p : IsPGroup 2 T₁ := hS₀.2.1.to_le hT₁S₀
  have hT₁M₀ : T₁ ≤ M₀ := hT₁S₀.trans hS₀.1
  have hT₁M : T₁ ≤ M := sup_le (inf_le_left.trans c.hyp.T_le) (Subgroup.zpowers_le.2 hxM)
  have hTElt : TE153 T E < T₁ := by
    refine lt_of_le_of_ne le_sup_left fun h => hxTE ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hdvd : Nat.card (TE153 T E) ∣ Nat.card T₁ := Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card (TE153 T E) ≠ Nat.card T₁ := fun h =>
    hTElt.ne (Subgroup.eq_of_le_of_card_ge le_sup_left h.symm.le)
  have h2 : 2 * Nat.card (TE153 T E) ≤ Nat.card T₁ := by
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < Nat.card (TE153 T E) := Nat.card_pos
    have hk1 : k ≠ 1 := fun h1 => hne (by rw [hk, h1, mul_one])
    have hk0 : k ≠ 0 := fun h0 => by
      have : 0 < Nat.card T₁ := Nat.card_pos
      rw [hk, h0, mul_zero] at this
      exact lt_irrefl _ this
    have hk2 : 2 ≤ k := by omega
    rw [hk]
    nlinarith
  have hTcard : Nat.card T = twoPart M := c.hyp.isSylowTwoOf.card_eq
  have hle : Nat.card T₁ ≤ twoPart M := card_le_twoPart hT₁M hT₁p
  have hT₁syl : IsSylowTwoOf T₁ M := by
    refine isSylowTwoOf_of_card_eq hT₁M hT₁p ?_
    have := card_T_eq_two_mul_TE r66 (E := E) (Mc := Mc) (V₁ := V₁) (V₂ := V₂)
    omega
  obtain ⟨hV, L₁, L₂, tb, hS, -, -, -⟩ := c.decomp.model
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer
  have hT₁' : IsSylowTwoOf (autI hV T₁) (autI hV M) := B2F.isSylowTwoOf_autI hV hMN hT₁syl
  obtain ⟨y, hyYE, ⟨e, heE, hye⟩, hy3⟩ := (Y_facts h113 c L).2
  have hsT : s ∈ T := gl.s_mem.1
  have hsN : s ∈ Subgroup.normalizer (VZ T M : Set G) := hMN (c.hyp.T_le hsT)
  set y' : G := s⁻¹ * y * s with hy'
  have hy'YF : y' ∈ YF153 Mc M E s := by
    show y' ∈ conjSubgroup (YE153 Mc M E) s
    rw [mem_conjSubgroup_iff]
    have : s * y' * s⁻¹ = y := by rw [hy']; group
    rw [this]
    exact hyYE
  have hy'G0 : y' ∈ G0_153 T Mc M E s :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hy'YF)
  have hy'M₀ : y' ∈ M₀ := hM₀.2 hy'G0
  have hy'M : y' ∈ M := Y153_le Mc M (YF_le_Y c gl hy'YF)
  have hy'N : y' ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hy'M
  set K : Subgroup G := T₁ ⊔ Subgroup.zpowers y' with hK
  have hKM₀ : K ≤ M₀ := sup_le hT₁M₀ (Subgroup.zpowers_le.2 hy'M₀)
  have hKM : K ≤ M := sup_le hT₁M (Subgroup.zpowers_le.2 hy'M)
  have hy'K : y' ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers y')
  have hpK : convI hV ⟨y', hy'N⟩ ∈ autI hV K := convI_mem_autI hV hy'K hy'N
  have hconj : ∀ v ∈ VZ T M, s * v * s⁻¹ ∈ VZ T M := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hsN v).mp hv
  have hy'3 : y' ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' := hconj v hv
    have h1 := Subgroup.mem_centralizer_iff.mp hy3 _ hv'
    have e1 : y' ^ 3 = s⁻¹ * y ^ 3 * s := by
      have := conj_pow (a := s⁻¹) (b := y) (i := 3)
      simpa [hy'] using this
    rw [e1]
    calc v * (s⁻¹ * y ^ 3 * s) = s⁻¹ * ((s * v * s⁻¹) * y ^ 3) * s := by group
      _ = s⁻¹ * (y ^ 3 * (s * v * s⁻¹)) * s := by rw [h1]
      _ = s⁻¹ * y ^ 3 * s * v := by group
  have hp3 : convI hV ⟨y', hy'N⟩ ^ 3 = 1 := by
    have e1 : (⟨y', hy'N⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 3 =
        ⟨y' ^ 3, (Subgroup.normalizer _).pow_mem hy'N 3⟩ := Subtype.ext rfl
    rw [← map_pow, e1]
    exact (convI_eq_one_iff hV _).2 hy'3
  have hp1 : convI hV ⟨y', hy'N⟩ ≠ 1 := by
    intro h
    have hc := (convI_eq_one_iff hV _).1 h
    have heV : e ∈ VZ T M := L.le_V heE
    have hs'V : s⁻¹ * e * s ∈ VZ T M := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hsN) e).mp heV
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hs'V
    apply hye
    have e1 : (s⁻¹ * e * s) * y' = y' * (s⁻¹ * e * s) := h1
    have hcomm : e * y = y * e := by
      have h2 : s⁻¹ * (e * y) * s = s⁻¹ * (y * e) * s := by
        calc s⁻¹ * (e * y) * s = (s⁻¹ * e * s) * y' := by rw [hy']; group
          _ = y' * (s⁻¹ * e * s) := e1
          _ = s⁻¹ * (y * e) * s := by rw [hy']; group
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← hcomm]
    group
  have hpT : convI hV ⟨y', hy'N⟩ ∉ autI hV T₁ := by
    intro hp
    obtain ⟨g, hgT₁, hg⟩ := (mem_autI hV).1 hp
    obtain ⟨n, hn⟩ := hT₁p ⟨g, hgT₁⟩
    have hgn : g ^ 2 ^ n = 1 := by
      have := congrArg (fun z : ↥T₁ => ((z : ↥T₁) : G)) hn
      apply Subtype.ext
      simpa using this
    have hp2 : convI hV ⟨y', hy'N⟩ ^ 2 ^ n = 1 := by
      rw [← hg, ← map_pow, hgn, map_one]
    have hcop : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
    have := pow_gcd_eq_one.2 ⟨hp3, hp2⟩
    rw [hcop, pow_one] at this
    exact hp1 this
  have hmax := hS.maximal hT₁' (autI_mono hV (le_sup_left : T₁ ≤ K)) (autI_mono hV hKM)
  have hKX : autI hV K = autI hV M := by
    rcases hmax with h | h
    · exact absurd (by rw [← h]; exact hpK) hpT
    · exact h
  have hMK : M ≤ K := by
    intro m hm
    have hmN := hMN hm
    have h1 : convI hV ⟨m, hmN⟩ ∈ autI hV K := by
      rw [hKX]
      exact convI_mem_autI hV hm hmN
    obtain ⟨k, hkK, hk⟩ := (mem_autI hV).1 h1
    have hk1 : convI hV (⟨m, hmN⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, hk, mul_inv_cancel]
    have hc : m * (k : G)⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
      (convI_eq_one_iff hV _).1 hk1
    have hcTE : m * (k : G)⁻¹ ∈ TE153 T E := centralizer_le_TE L r67 hc
    have e : m = (m * (k : G)⁻¹) * k := by group
    rw [e]
    have hTEK : TE153 T E ≤ K := (le_sup_left : TE153 T E ≤ T₁).trans le_sup_left
    exact K.mul_mem (hTEK hcTE) hkK
  have hMM₀ : M ≤ M₀ := hMK.trans hKM₀
  have hX₁ : ((Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁) ≤ M₀ :=
    r45.unique₁.1.2.trans hMM₀
  have hM₀M : M₀ = M := r45.unique₁.2 M₀ ⟨hM₀.1, hX₁⟩
  apply r67.XE_not_le
  rw [← hM₀M]
  exact ((le_sup_left : XE153 E ≤ G2_153 T E).trans
    (le_sup_right : G2_153 T E ≤ G0_153 T Mc M E s)).trans hM₀.2

omit [Finite G] in
theorem G2_le_normalizer_E : G2_153 T E ≤ Subgroup.normalizer (E : Set G) :=
  sup_le ((oTwoUpper_le _).trans (Subgroup.centralizer_le_normalizer _)) inf_le_right

theorem isSylowTwoOf_TE_G2 (r67 : Res15367 T Mc M V₁ V₂ E) :
    IsSylowTwoOf (TE153 T E) (G2_153 T E) :=
  A4.isSylowTwoOf_mono r67.sylow_GE le_sup_right G2_le_normalizer_E

theorem relIndex_TE_G2 (r67 : Res15367 T Mc M V₁ V₂ E) :
    (TE153 T E).relIndex (G2_153 T E) = 3 := by
  obtain ⟨e⟩ := r67.XE_quot
  exact relIndex_sup_eq_three' (inf_le_right.trans r67.XE_normal) (relIndex_pCoreOf_eq_three' e)
    (isSylowTwoOf_TE_G2 r67)

theorem quot_G2 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) :
    Nonempty (↥(G2_153 T E) ⧸ Open.pCore 2 ↥(G2_153 T E) ≃* Equiv.Perm (Fin 3)) :=
  nonempty_quotient_pCore_of_relIndex_eq_three' (isSylowTwoOf_TE_G2 r67) (relIndex_TE_G2 r67)
    fun h => r67.XE_not_le fun _ hx =>
      normalizer_TE_le c L r67 (h ((le_sup_left : XE153 E ≤ G2_153 T E) hx))

theorem YE_TE_le_ME (c : Ctx153 G T Mc M V₁ V₂ t) :
    YE153 Mc M E ⊔ TE153 T E ≤ M ⊓ Subgroup.normalizer (E : Set G) :=
  sup_le (le_inf (((oTwoUpper_le _).trans inf_le_left).trans (Y153_le Mc M))
      ((oTwoUpper_le _).trans inf_le_right))
    (le_inf (inf_le_left.trans c.hyp.T_le) inf_le_right)

theorem isSylowTwoOf_TE_HE (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E) :
    IsSylowTwoOf (TE153 T E) (YE153 Mc M E ⊔ TE153 T E) :=
  A4.isSylowTwoOf_mono L.sylow le_sup_right (YE_TE_le_ME c)

theorem relIndex_TE_HE (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) :
    (TE153 T E).relIndex (YE153 Mc M E ⊔ TE153 T E) = 3 := by
  obtain ⟨e⟩ := r67.YE_quot
  exact relIndex_sup_eq_three' (TE153_le_normalizer_YE153 c) (relIndex_pCoreOf_eq_three' e)
    (isSylowTwoOf_TE_HE c L)

omit [Finite G] in
theorem G1_eq_conj (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    G1_153 T Mc M E s = conjSubgroup (YE153 Mc M E ⊔ TE153 T E) s := by
  have hTEs : conjSubgroup (TE153 T E) s = TE153 T E :=
    conjSubgroup_eq_iff_mem_normalizer.2 (T_le_normalizer_TE r66 gl.s_mem.1)
  rw [conjSubgroup_sup', hTEs]

theorem isSylowTwoOf_TE_G1 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    IsSylowTwoOf (TE153 T E) (G1_153 T Mc M E s) := by
  have hTEs : conjSubgroup (TE153 T E) s = TE153 T E :=
    conjSubgroup_eq_iff_mem_normalizer.2 (T_le_normalizer_TE r66 gl.s_mem.1)
  have h := isSylowTwoOf_conjSubgroup' (isSylowTwoOf_TE_HE c L) s
  rw [hTEs, ← G1_eq_conj r66 gl] at h
  exact h

theorem relIndex_TE_G1 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    (TE153 T E).relIndex (G1_153 T Mc M E s) = 3 := by
  have hTEs : conjSubgroup (TE153 T E) s = TE153 T E :=
    conjSubgroup_eq_iff_mem_normalizer.2 (T_le_normalizer_TE r66 gl.s_mem.1)
  have h := E3.relIndex_conjSubgroup (TE153 T E) (YE153 Mc M E ⊔ TE153 T E) s
  rw [hTEs, ← G1_eq_conj r66 gl] at h
  rw [h]
  exact relIndex_TE_HE c L r67

theorem quot_G1 (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    Nonempty (↥(G1_153 T Mc M E s) ⧸ Open.pCore 2 ↥(G1_153 T Mc M E s) ≃* Equiv.Perm (Fin 3)) := by
  have h := nonempty_oTwoQuot_conjSubgroup' s r66.quot_S3
  rwa [← G1_eq_conj r66 gl] at h

theorem G1_le_M (c : Ctx153 G T Mc M V₁ V₂ t) (gl : GoldLine153 T V₁ E s) :
    G1_153 T Mc M E s ≤ M :=
  sup_le ((YF_le_Y c gl).trans (Y153_le Mc M)) (inf_le_left.trans c.hyp.T_le)

theorem G1_inf_G2 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    G1_153 T Mc M E s ⊓ G2_153 T E = TE153 T E := by
  have hle : TE153 T E ≤ G1_153 T Mc M E s ⊓ G2_153 T E := le_inf le_sup_right le_sup_right
  have h3 := relIndex_TE_G1 c L r66 r67 gl
  have htower := Subgroup.relIndex_mul_relIndex (TE153 T E) (G1_153 T Mc M E s ⊓ G2_153 T E)
    (G1_153 T Mc M E s) hle inf_le_left
  rw [h3] at htower
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ htower) with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
  · exfalso
    rw [h] at htower
    have h1 : (G1_153 T Mc M E s ⊓ G2_153 T E).relIndex (G1_153 T Mc M E s) = 1 := by omega
    have hG : G1_153 T Mc M E s ≤ G2_153 T E :=
      (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    rcases eq_or_eq_of_relIndex_prime Nat.prime_three (le_sup_right : TE153 T E ≤ G1_153 T Mc M E s)
      hG (relIndex_TE_G2 r67) with h2 | h2
    · have h2' : G1_153 T Mc M E s = TE153 T E := h2
      rw [h2', Subgroup.relIndex_self] at h3
      omega
    · have h2' : G1_153 T Mc M E s = G2_153 T E := h2
      apply r67.XE_not_le
      intro x hx
      have hxG1 : x ∈ G1_153 T Mc M E s := by
        rw [h2']
        exact (le_sup_left : XE153 E ≤ G2_153 T E) hx
      exact G1_le_M c gl hxG1

theorem triple_153 (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r45 : Res15345 T Mc M V₁ V₂) (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E) := by
  refine ⟨rfl, quot_G1 r66 gl, quot_G2 c L r67, ?_⟩
  rw [G1_inf_G2 c L r66 r67 gl]
  have hV := V_le_pCoreOf_G0 c r49 L r66 r67 gl
  have hne : pCoreOf 2 (G0_153 T Mc M E s) ≠ ⊥ := by
    intro h
    have hE : E ≤ ⊥ := (L.le_V.trans hV).trans h.le
    have := L.card_eq
    rw [le_bot_iff.mp hE, Subgroup.card_bot] at this
    omega
  obtain ⟨M₀, hM₀, hle⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (pCoreOf 2 (G0_153 T Mc M E s) : Set G))
    ⟨pCoreOf 2 (G0_153 T Mc M E s), hne, pCoreOf_isPGroup 2 _, rfl⟩
  have hInM : InM (G0_153 T Mc M E s) M₀ := ⟨hM₀, (le_normalizer_pCoreOf 2 _).trans hle⟩
  exact A4.isSylowTwoOf_mono (sylow_of_inM_153 h113 c r45 L r66 r67 gl hInM)
    (le_sup_right.trans le_sup_left) hInM.2

end Stage68b

structure Res15368Rest2 {G : Type} [Group G] (T Mc M E : Subgroup G) (s : G) : Prop where
  pCore_le_centralizer : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G)
  pCore_eq : pCoreOf 2 (G0_153 T Mc M E s) =
    (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map (G0_153 T Mc M E s).subtype

@[expose] def Stage15368Rest2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E → GoldLine153 T V₁ E s →
          G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G) →
          VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s) →
          (∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀) →
          F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E) →
            Res15368Rest2 T Mc M E s

theorem stage15368B_of_rest2 (h113 : StageLemma14113) (i : Stage15368Rest2) : Stage15368B := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl
  have h1 := G0_le_normalizer_YE c r49 L r67 gl
  have h2 := V_le_pCoreOf_G0 c r49 L r66 r67 gl
  have h3 : ∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀ :=
    fun M₀ hM₀ => sylow_of_inM_153 h113 c r45 L r66 r67 gl hM₀
  have h4 := triple_153 h113 c r45 r49 L r66 r67 gl
  have hr := i G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl h1 h2 h3 h4
  exact ⟨h1, h2, hr.pCore_le_centralizer, h3, h4, hr.pCore_eq⟩

end CFSG.Quasithin
