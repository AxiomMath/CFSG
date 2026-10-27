module

public import CFSG.Quasithin.EmptyFaithful.T1531InspBasic
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.T1531In68b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section PCore

theorem pCoreOf_map_le_of_injective {A B : Type*} [Group A] [Group B] [Finite B] (f : A →* B)
    (hf : Function.Injective f) (P : Subgroup A) :
    pCoreOf 2 (P.map f) ≤ (pCoreOf 2 P).map f := by
  set P' := pCoreOf 2 (P.map f) with hP'
  have hP'le : P' ≤ P.map f := pCoreOf_le 2 _
  set P'' : Subgroup A := P'.comap f ⊓ P with hP''
  have hmap : P''.map f = P' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hP'le hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hnormal : (P''.subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, (g * x * g⁻¹).2⟩
    have h1 : f (g : A) ∈ Subgroup.normalizer (P' : Set B) :=
      le_normalizer_pCoreOf 2 (P.map f) ⟨g, g.2, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp h1 (f x)).mp (hx.1 : f (x : A) ∈ P')
    simpa using h2
  have hp : IsPGroup 2 ↥P'' := by
    have : IsPGroup 2 ↥(P''.map f) := hmap ▸ pCoreOf_isPGroup 2 (P.map f)
    exact this.of_equiv (Subgroup.equivMapOfInjective P'' f hf).symm
  have := le_pCoreOf 2 inf_le_right hnormal hp
  rw [← hmap]
  exact Subgroup.map_mono this

theorem pCoreOf_le_pCore_of_normal {D : Type*} [Group D] [Finite D] (N : Subgroup D)
    [hN : N.Normal] : pCoreOf 2 N ≤ Open.pCore 2 D := by
  have h1 := normalizer_le_normalizer_pCoreOf 2 N
  have h2 : Subgroup.normalizer (pCoreOf 2 N : Set D) = ⊤ := by
    rw [Subgroup.normalizer_eq_top (H := N)] at h1
    exact top_le_iff.mp h1
  have hn : (pCoreOf 2 N).Normal := Subgroup.normalizer_eq_top_iff.mp h2
  exact le_pCore 2 hn (pCoreOf_isPGroup 2 N)

end PCore

section Module

variable {G : Type} [Group G] {I V : Subgroup G} (hV : IsElemAbelian 2 V)
  (hIN : I ≤ Subgroup.normalizer (V : Set G)) (Q : Subgroup ↥I) [Q.Normal]
  (hQ : Q = (I ⊓ Subgroup.centralizer (V : Set G)).subgroupOf I)

noncomputable def rhoOf : (↥I ⧸ Q) →* MulAut (IntMod V hV) :=
  QuotientGroup.lift Q (convHom hV I hIN) (hQ.le.trans (ker_convHom hV I hIN).ge)

theorem rhoOf_comp : (rhoOf hV hIN Q hQ).comp (QuotientGroup.mk' Q) = convHom hV I hIN :=
  QuotientGroup.lift_comp_mk' _ _ _

theorem rhoOf_injective : Function.Injective (rhoOf hV hIN Q hQ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    have h1 : convHom hV I hIN g = 1 := by simpa [rhoOf] using hx
    have h2 : g ∈ (convHom hV I hIN).ker := h1
    rw [ker_convHom hV I hIN, ← hQ] at h2
    exact (QuotientGroup.eq_one_iff g).mpr h2

theorem map_rhoOf_barQ {A : Subgroup G} (hAI : A ≤ I) :
    (barQ I Q A).map (rhoOf hV hIN Q hQ) = autI hV A := by
  rw [autI_eq_map_convHom hV hIN hAI]
  unfold barQ
  rw [Subgroup.map_map, rhoOf_comp]

variable [Finite G]

theorem autI_thompsonJ_eq_ffJ (hIN : I ≤ Subgroup.normalizer (V : Set G)) (hVI : V ≤ I) :
    ffJ (autI hV (thompsonJ I)) = autI hV (thompsonJ I) := by
  apply le_antisymm
  · unfold ffJ
    exact iSup₂_le fun A hA => hA.1
  · have hJ : thompsonJ I = ⨆ (A : Subgroup G), ⨆ (_ : IsMaxElemAbelian I A), A := rfl
    conv_lhs => rw [hJ, autI_iSup₂ hV (P := IsMaxElemAbelian I) (fun A hA => hA.1.trans hIN)]
    refine iSup₂_le fun A hA => ?_
    by_cases hAc : A ≤ Subgroup.centralizer (V : Set G)
    · rw [autI_eq_bot_of_le_centralizer hV hAc]
      exact bot_le
    · have hmem : autI hV A ∈ offenderImages hV I := ⟨A, ⟨hA, hAc⟩, rfl⟩
      have h := offenderImages_isFFStarOffender hV hVI hIN hmem
      have hle : autI hV A ≤ autI hV (thompsonJ I) := autI_mono hV (B6.le_thompsonJ hA)
      exact le_iSup₂_of_le (autI hV A) ⟨hle, h.2.1, h.2.2.1, h.2.2.2⟩ le_rfl

omit [Finite G] in
theorem barQ_thompsonJ_normal (I : Subgroup G) (Q : Subgroup ↥I) [Q.Normal] :
    (barQ I Q (thompsonJ I)).Normal := by
  have h1 : ((thompsonJ I).subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (B6.thompsonJ_le I)).mpr
      (B6.le_normalizer_thompsonJ I)
  exact h1.map (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)

theorem pCoreOf_autI_thompsonJ_eq_bot (hIN : I ≤ Subgroup.normalizer (V : Set G))
    (Q : Subgroup ↥I) [Q.Normal] (hQ : Q = (I ⊓ Subgroup.centralizer (V : Set G)).subgroupOf I)
    (hD : Open.pCore 2 (↥I ⧸ Q) = ⊥) :
    pCoreOf 2 (autI hV (thompsonJ I)) = ⊥ := by
  have h1 := map_rhoOf_barQ hV hIN Q hQ (B6.thompsonJ_le I)
  have hN := barQ_thompsonJ_normal I Q
  rw [← h1]
  refine le_bot_iff.mp ((pCoreOf_map_le_of_injective _ (rhoOf_injective hV hIN Q hQ) _).trans ?_)
  have := pCoreOf_le_pCore_of_normal (barQ I Q (thompsonJ I))
  rw [hD] at this
  rw [le_bot_iff.mp this, Subgroup.map_bot]

end Module

section SQTK

variable {G : Type} [Group G] [Finite G]

theorem sqtkGroup_of_le {P L : Subgroup G} (hS : SQTKGroup ↥P) (hLP : L ≤ P) : SQTKGroup ↥L := by
  refine ⟨fun p hp hp2 => ?_, ?_⟩
  · have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥P) :=
      CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (Subgroup.inclusion hLP)
        (Subgroup.inclusion_injective hLP)
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := hS.1 p hp hp2
    show CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 2
    omega
  · exact (hS.2.subgroup (L.subgroupOf P)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLP).symm

theorem b53Hyp_autI_thompsonJ {I V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hIN : I ≤ Subgroup.normalizer (V : Set G)) (hVI : V ≤ I) (Q : Subgroup ↥I) [Q.Normal]
    (hQ : Q = (I ⊓ Subgroup.centralizer (V : Set G)).subgroupOf I)
    (hD : Open.pCore 2 (↥I ⧸ Q) = ⊥) (hS : SQTKGroup ↥(thompsonJ I)) :
    B53Hyp (autI hV (thompsonJ I)) := by
  refine ⟨pCoreOf_autI_thompsonJ_eq_bot hV hIN Q hQ hD,
    (autI_thompsonJ_eq_ffJ hV hIN hVI).symm, ?_⟩
  set ψ : ↥(thompsonJ I) →* MulAut (IntMod V hV) :=
    (convHom hV I hIN).comp (Subgroup.inclusion (B6.thompsonJ_le I)) with hψ
  have hrange : ψ.range = autI hV (thompsonJ I) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range,
      ← autI_eq_map_convHom hV hIN (B6.thompsonJ_le I)]
  exact ⟨↥(thompsonJ I), inferInstance, inferInstance, ψ.ker, inferInstance, hS,
    ⟨(MulEquiv.subgroupCongr hrange.symm).trans (QuotientGroup.quotientKerEquivRange ψ).symm⟩⟩

end SQTK

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

abbrev V0_153 (T Mc M E : Subgroup G) (s : G) : Subgroup G :=
  conjClosure (VZ T M) (G0_153 T Mc M E s)

theorem isSylowTwoOf_TE_G0 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368 T Mc M E s) : IsSylowTwoOf (TE153 T E) (G0_153 T Mc M E s) := by
  have h := r68.triple.2.2.2
  rwa [G1_inf_G2 c L r66 r67 gl] at h

omit [Finite G] in
theorem thompsonJ_TE_le_R (r67 : Res15367 T Mc M V₁ V₂ E) :
    thompsonJ (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
  (B6.thompsonJ_le_baum _).trans r67.baum_le

omit [Finite G] in
theorem R_le_TE (L : LineData153 T M V₁ V₂ E) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ TE153 T E := fun _ hx =>
  ⟨hx.1, Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (fun _ he => L.le_V he) hx.2)⟩

theorem thompsonJ_R_eq (r67 : Res15367 T Mc M V₁ V₂ E) (L : LineData153 T M V₁ V₂ E) :
    thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) = thompsonJ (TE153 T E) :=
  B6.thompsonJ_eq_of_le (thompsonJ_TE_le_R r67) (R_le_TE L)

theorem G1_le_normalizer_thompsonJ_TE (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    G1_153 T Mc M E s ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) := by
  have hM : M ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
    rw [r67.R_eq]
    exact B6.le_normalizer_centralizer c.hyp.le_normalizer
  rw [← thompsonJ_R_eq r67 L]
  exact (G1_le_M c gl).trans (hM.trans (normalizer_le_normalizer_thompsonJ _))

theorem XE_le_thompsonJ (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368 T Mc M E s) : XE153 E ≤ thompsonJ (G0_153 T Mc M E s) := by
  have hT := isSylowTwoOf_TE_G0 c L r66 r67 gl r68
  have hJR : thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      thompsonJ (G0_153 T Mc M E s) :=
    (thompsonJ_R_eq r67 L).le.trans (B6.thompsonJ_le_of_sylow hT)
  have hXG : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hN := B6.le_normalizer_thompsonJ (G0_153 T Mc M E s)
  calc XE153 E = ⁅XE153 E, thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G))⁆ := r67.XE_comm
    _ ≤ thompsonJ (G0_153 T Mc M E s) := by
      rw [Subgroup.commutator_le]
      intro x hx j hj
      rw [commutatorElement_def]
      have h1 : x * j * x⁻¹ ∈ thompsonJ (G0_153 T Mc M E s) :=
        (Subgroup.mem_normalizer_iff.mp (hN (hXG hx)) j).mp (hJR hj)
      exact (thompsonJ (G0_153 T Mc M E s)).mul_mem h1 ((thompsonJ _).inv_mem (hJR hj))

theorem pCoreOf_G0_ne_bot (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368 T Mc M E s) :
    pCoreOf 2 (G0_153 T Mc M E s) ≠ ⊥ := by
  intro hbot
  have h0 : VZ T M ≤ ⊥ := hbot ▸ r68.V_le_pCore
  have h16 := c.hyp.card_VZ
  rw [le_bot_iff.mp h0, Subgroup.card_bot] at h16
  omega

omit [Finite G] in
theorem V0_le_pCore (r68 : Res15368 T Mc M E s) :
    V0_153 T Mc M E s ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh) z).mp (r68.V_le_pCore hz)

omit [Finite G] in
theorem V0_le_centralizer_of_mem_pCore (r68 : Res15368 T Mc M E s) {q : G}
    (hq : q ∈ pCoreOf 2 (G0_153 T Mc M E s)) :
    V0_153 T Mc M E s ≤ Subgroup.centralizer ({q} : Set G) := by
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hq' : h⁻¹ * y * h ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 _ ((G0_153 T Mc M E s).inv_mem hh)) y).mp hq
    simpa using this
  have hz' : z * (h⁻¹ * y * h) = (h⁻¹ * y * h) * z :=
    Subgroup.mem_centralizer_iff.mp (r68.pCore_le_centralizer hq') z hz
  calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [hz']
    _ = (h * z * h⁻¹) * y := by group

theorem isElemAbelian_V0 (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368 T Mc M E s) :
    IsElemAbelian 2 (V0_153 T Mc M E s) := by
  have hV := c.hyp.elemAbelian
  refine B2F.isElemAbelian_closure
    (S := {x | ∃ h ∈ G0_153 T Mc M E s, ∃ z ∈ VZ T M, h * z * h⁻¹ = x}) ?_ ?_
  · intro a ha b hb
    have haV : a ∈ V0_153 T Mc M E s := Subgroup.subset_closure ha
    have hbV : b ∈ V0_153 T Mc M E s := Subgroup.subset_closure hb
    have h1 := V0_le_centralizer_of_mem_pCore r68 (V0_le_pCore r68 hbV) haV
    exact (Subgroup.mem_centralizer_iff.mp h1 b rfl).symm
  · intro a ha
    obtain ⟨h, hh, z, hz, rfl⟩ := ha
    rw [conj_pow, hV.2 z hz]
    simp

omit [Finite G] in
theorem V0_normal : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] in
theorem V_le_V0 : VZ T M ≤ V0_153 T Mc M E s := le_conjClosure _ _

omit [Finite G] in
theorem V0_le_G0 (r68 : Res15368 T Mc M E s) : V0_153 T Mc M E s ≤ G0_153 T Mc M E s :=
  (V0_le_pCore r68).trans (pCoreOf_le 2 _)

theorem inf_centralizer_V0_le_pCore (c : Ctx153 G T Mc M V₁ V₂ t) (r67 : Res15367 T Mc M V₁ V₂ E) :
    G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) ≤
      pCoreOf 2 (G0_153 T Mc M E s) := by
  set N₁ := G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) with hN₁
  have hCV : Subgroup.centralizer (VZ T M : Set G) ≤ T := r67.R_eq.symm.le.trans inf_le_left
  have hN₁T : N₁ ≤ T := fun x hx => hCV (Subgroup.centralizer_le (fun v hv => V_le_V0 hv) hx.2)
  have hp : IsPGroup 2 ↥N₁ := c.hyp.isSylowTwoOf.2.1.to_le hN₁T
  have key : ∀ g ∈ G0_153 T Mc M E s, ∀ x ∈ N₁, g * x * g⁻¹ ∈ N₁ := fun g hg x hx =>
    ⟨(G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).mul_mem hg hx.1)
        ((G0_153 T Mc M E s).inv_mem hg),
      B6.conj_mem_centralizer_of_mem_normalizer (V0_normal hg) hx.2⟩
  have hnorm : G0_153 T Mc M E s ≤ Subgroup.normalizer (N₁ : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (key g hg) (fun x hx => by
      simpa using key g⁻¹ ((G0_153 T Mc M E s).inv_mem hg) x hx)
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hp

theorem pCoreOf_G0_eq (c : Ctx153 G T Mc M V₁ V₂ t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (r68 : Res15368 T Mc M E s) :
    pCoreOf 2 (G0_153 T Mc M E s) =
      G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) :=
  le_antisymm
    (le_inf (pCoreOf_le 2 _) fun q hq => Subgroup.mem_centralizer_iff.mpr fun _ hx =>
      ((Subgroup.mem_centralizer_iff.mp (V0_le_centralizer_of_mem_pCore r68 hq hx) q
        (Set.mem_singleton q)).symm))
    (inf_centralizer_V0_le_pCore c r67)

theorem pPrimeCore_G0_eq (c : Ctx153 G T Mc M V₁ V₂ t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (r68 : Res15368 T Mc M E s) :
    CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
      (G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)).subgroupOf
        (G0_153 T Mc M E s) := by
  rw [← pCoreOf_G0_eq c r67 r68, r68.pCore_eq]
  exact (Subgroup.comap_map_eq_self_of_injective (G0_153 T Mc M E s).subtype_injective _).symm

theorem sqtkGroup_G0 (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368 T Mc M E s) :
    SQTKGroup ↥(G0_153 T Mc M E s) :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot c.hyp.qtfe.qtke (pCoreOf_G0_ne_bot c r68),
    kGroup_of_pCoreOf_ne_bot c.hyp.qtfe.qtke c.hyp.qtfe.simple c.hyp.qtfe.nonabelian
      (pCoreOf_G0_ne_bot c r68)⟩

omit [Finite G] in
theorem not_isPGroup_XE (r67 : Res15367 T Mc M V₁ V₂ E) : ¬ IsPGroup 2 ↥(XE153 E) := by
  intro hp
  obtain ⟨e⟩ := r67.XE_quot
  have h1 : IsPGroup 2 (OTwoQuot (XE153 E)) :=
    hp.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have h2 : IsPGroup 2 (Multiplicative (ZMod 3)) := h1.of_equiv e
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
  rw [hcard] at hn
  rcases n with _ | _ | n
  · simp at hn
  · simp at hn
  · rw [pow_succ, pow_succ] at hn
    omega

theorem barQ_XE_ne_bot (r67 : Res15367 T Mc M V₁ V₂ E) (r68 : Res15368 T Mc M E s)
    (hXI : XE153 E ≤ G0_153 T Mc M E s) :
    barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E) ≠ ⊥ := by
  intro hbot
  apply not_isPGroup_XE r67
  have hle : XE153 E ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) ⟨x, hXI hx⟩ ∈
        barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E) :=
      Subgroup.mem_map.mpr ⟨⟨x, hXI hx⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [r68.pCore_eq]
    exact ⟨⟨x, hXI hx⟩, h1, rfl⟩
  exact (pCoreOf_isPGroup 2 _).to_le hle

end Setting

end CFSG.Quasithin
