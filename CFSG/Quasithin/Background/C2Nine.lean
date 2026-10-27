module

public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.A1bLemma126
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M L V T : Subgroup G}

namespace C2Nine

theorem eq_of_perfect_of_pow_mem {X N : Subgroup G} (hX : ⁅X, X⁆ = X) (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = X := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  have := hN
  have hp : IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  have : Group.IsNilpotent (↥X ⧸ N.subgroupOf X) := hp.isNilpotent
  have hsub : Subsingleton (↥X ⧸ N.subgroupOf X) := by
    by_contra hns
    have : Nontrivial (↥X ⧸ N.subgroupOf X) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent (↥X ⧸ N.subgroupOf X) inferInstance
  refine le_antisymm hNX fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : X) : ↥X ⧸ N.subgroupOf X) = QuotientGroup.mk 1 :=
    Subsingleton.elim _ _
  rw [QuotientGroup.eq] at h1
  simpa [Subgroup.mem_subgroupOf] using h1

theorem oTwoUpper_eq_of_perfect {X : Subgroup G} (hX : ⁅X, X⁆ = X) : oTwoUpper X = X :=
  eq_of_perfect_of_pow_mem hX (oTwoUpper_le X)
    (Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper X))
    fun _ hx => exists_pow_mem_oTwoUpper X hx

theorem opResidual_eq_of_perfect {X : Subgroup G} (hX : ⁅X, X⁆ = X) : opResidual 2 X = X :=
  eq_of_perfect_of_pow_mem hX (opResidual_le 2 X) (opResidual_normal 2 X)
    fun _ hx => exists_pow_mem_opResidual hx

theorem conjClosure_le_M (h : HypC28 H R M L V) : conjClosure L M ≤ M := by
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  exact conjClosure_le fun m hm z hz => M.mul_mem (M.mul_mem hm (hLM hz)) (M.inv_mem hm)

theorem perfect_conjClosure_of_hyp (h : HypC28 H R M L V) :
    ⁅conjClosure L M, conjClosure L M⁆ = conjClosure L M :=
  perfect_conjClosure (perfect_of_mem_cComp h.comp)

omit [Finite G] in
theorem normal_conjClosure (L M : Subgroup G) : ((conjClosure L M).subgroupOf M).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_conjClosure L M)

theorem subnormal_conjClosure (h : HypC28 H R M L V) : IsSubnormal (conjClosure L M) M :=
  A4.subnormal_of_normal (conjClosure_le_M h) (normal_conjClosure L M)

theorem comp_conjClosure (h : HypC28 H R M L V) : L ∈ cComp (conjClosure L M) :=
  cComp_mem_of_le h.comp (le_conjClosure L M) (conjClosure_le_M h)

theorem ne_bot_of_hyp (h : HypC28 H R M L V) : R ≠ ⊥ := by
  intro hR
  have hM0M := conjClosure_le_M h
  have hPC : pCoreOf 2 (conjClosure L M) ≤
      centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) :=
    pCoreOf_le_centralizerSection hM0M
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
  have hP0 : pCoreOf 2 (conjClosure L M) ≤ R :=
    hmax _ hPC (pCoreOf_isPGroup 2 _) (hR ▸ bot_le)
  have hP : pCoreOf 2 (conjClosure L M) = ⊥ := le_bot_iff.mp (hR ▸ hP0)
  have hV := h.V_center
  rw [hR, sup_bot_eq, hP] at hV
  have : centerOf (⊥ : Subgroup G) = ⊥ := by
    unfold centerOf
    simp
  rw [this] at hV
  exact h.V_ne (le_bot_iff.mp hV)

theorem inf_normalizer_le_M (h : HypC28 H R M L V) :
    H ⊓ Subgroup.normalizer (R : Set G) ≤ M :=
  (inf_normalizer_le_cgsIn (ne_bot_of_hyp h)).trans h.cgs

theorem pCoreOf_conjClosure_eq (h : HypC28 H R M L V) :
    pCoreOf 2 (conjClosure L M) = conjClosure L M ⊓ pCoreOf 2 M := by
  refine le_antisymm (le_inf (pCoreOf_le 2 _)
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_conjClosure h))) ?_
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
  intro g hg
  have hgM := conjClosure_le_M h hg
  exact A4.mem_normalizer_inf (le_normalizer_conjClosure L M hgM) (le_normalizer_pCoreOf 2 M hgM)

omit [Finite G] in
theorem conjByElt_mem_cComp {X : Subgroup G} {t : G} (hL : L ∈ cComp X)
    (ht : t ∈ Subgroup.normalizer (X : Set G)) : conjByElt t L ∈ cComp X := by
  have h1 := cComp_map_mulEquiv (MulAut.conj t) hL
  have h2 : X.map (MulAut.conj t).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  rw [h2] at h1
  exact h1

omit [Finite G] in
theorem inf_sup_eq_of_pCore {A B M₀ Q : Subgroup G} (hA : A ≤ M₀)
    (hint : (A ⊔ Q) ⊓ (B ⊔ Q) = Q) :
    (A ⊔ (M₀ ⊓ Q)) ⊓ (B ⊔ (M₀ ⊓ Q)) = M₀ ⊓ Q := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_right)
  have hxM : x ∈ M₀ := sup_le hA inf_le_left hx.1
  have hxQ : x ∈ Q := by
    rw [← hint]
    exact ⟨sup_le_sup_left inf_le_right A hx.1, sup_le_sup_left inf_le_right B hx.2⟩
  exact ⟨hxM, hxQ⟩

omit [Finite G] in
theorem cgsIn_mono_left {X Y : Subgroup G} (hXY : X ≤ Y) (S : Subgroup G) :
    cgsIn X S ≤ cgsIn Y S :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_right _ hXY

end C2Nine

open C2Nine

theorem c2_9_one (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M) :
    conjSubgroupsBy M L = conjSubgroupsBy T L ∧
    (conjClosure L M = L ∨
      ∃ L₂ : Subgroup G, L₂ ∈ conjSubgroupsBy T L ∧ L₂ ≠ L ∧ conjClosure L M = L ⊔ L₂ ∧
        L ∈ cComp (conjClosure L M) ∧ L₂ ∈ cComp (conjClosure L M) ∧
        ⁅L, L₂⁆ ≤ pCoreOf 2 (conjClosure L M) ∧
        (L ⊔ pCoreOf 2 (conjClosure L M)) ⊓ (L₂ ⊔ pCoreOf 2 (conjClosure L M)) =
          pCoreOf 2 (conjClosure L M)) ∧
    ⁅conjClosure L M, conjClosure L M⁆ = conjClosure L M := by
  obtain ⟨hconj, hcase⟩ := hA3 M T L (h.sqtk.mono h.le_H) hT h.comp
  have hM0M := conjClosure_le_M h
  refine ⟨hconj, ?_, perfect_conjClosure_of_hyp h⟩
  rcases hcase with hall | ⟨t, htT, htn, hset, hcomm, hint, -⟩
  · left
    refine le_antisymm (conjClosure_le fun m hm z hz => ?_) (le_conjClosure L M)
    have hmem : L.map (MulAut.conj m).toMonoidHom ∈ conjSubgroupsBy M L := ⟨m, hm, rfl⟩
    rw [hconj] at hmem
    obtain ⟨t, ht, hteq⟩ := hmem
    have hn : L.map (MulAut.conj t).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hall t ht)
    rw [hn] at hteq
    have : m * z * m⁻¹ ∈ L.map (MulAut.conj m).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rwa [hteq] at this
  · right
    have htM : t ∈ M := hT.1 htT
    have hL2M0 : conjByElt t L ≤ conjClosure L M := conjByElt_le_conjClosure htM
    refine ⟨conjByElt t L, ⟨t, htT, rfl⟩, fun heq => htn
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq), ?_, comp_conjClosure h,
      cComp_mem_of_le (conjByElt_mem_cComp h.comp (Subgroup.le_normalizer htM)) hL2M0 hM0M, ?_, ?_⟩
    · refine le_antisymm (conjClosure_le fun m hm z hz => ?_) (sup_le (le_conjClosure L M) hL2M0)
      have hmem : conjByElt m L ∈ conjSubgroupsBy M L := ⟨m, hm, rfl⟩
      rw [hconj, hset] at hmem
      have hz' : m * z * m⁻¹ ∈ conjByElt m L := by
        rw [mem_conjByElt]
        have : m⁻¹ * (m * z * m⁻¹) * m = z := by group
        rw [this]
        exact hz
      rcases hmem with hmem | hmem
      · rw [hmem] at hz'
        exact Subgroup.mem_sup_left hz'
      · rw [hmem] at hz'
        exact Subgroup.mem_sup_right hz'
    · rw [pCoreOf_conjClosure_eq h]
      exact le_inf ((Subgroup.commutator_mono (le_conjClosure L M) hL2M0).trans
        (A3.commutator_self_le _)) hcomm
    · rw [pCoreOf_conjClosure_eq h]
      exact inf_sup_eq_of_pCore (le_conjClosure L M) hint

theorem c2_9_two (h : HypC28 H R M L V) :
    conjClosure L M ≤ Subgroup.normalizer (R : Set G) ∧ IsTwoRadicalIn H R := by
  have hM0M := conjClosure_le_M h
  have hup : conjClosure L M = oTwoUpper (conjClosure L M) :=
    (oTwoUpper_eq_of_perfect (perfect_conjClosure_of_hyp h)).symm
  have hmax : IsMaxSignalizer M (conjClosure L M) R :=
    (a4_2_4 hup (subnormal_conjClosure h) R).mpr h.sylow
  refine ⟨hmax.1.2.2, ?_⟩
  have hrad := (c1_2_four hup hM0M (normal_conjClosure L M) h.sylow (ne_bot_of_hyp h)).2
  exact isTwoRadicalIn_of_le_of_normalizer_le h.le_H hrad (inf_normalizer_le_M h)

namespace C2Nine

theorem conjClosure_inf_eq (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M)
    {X : Subgroup G} (hTX : T ≤ X) : conjClosure L (M ⊓ X) = conjClosure L M := by
  refine le_antisymm (conjClosure_mono le_rfl inf_le_left) ?_
  have hconj := (hA3 M T L (h.sqtk.mono h.le_H) hT h.comp).1
  refine conjClosure_le fun m hm z hz => ?_
  have hmem : L.map (MulAut.conj m).toMonoidHom ∈ conjSubgroupsBy M L := ⟨m, hm, rfl⟩
  rw [hconj] at hmem
  obtain ⟨t, ht, hteq⟩ := hmem
  have hz' : m * z * m⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := by
    rw [← hteq]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  obtain ⟨w, hw, hwz⟩ := hz'
  have hwz' : t * w * t⁻¹ = m * z * m⁻¹ := by simpa [MulAut.conj_apply] using hwz
  rw [← hwz']
  exact mem_conjClosure ⟨hT.1 ht, hTX ht⟩ hw

end C2Nine

theorem c2_9_three (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M) (hRT : R ≤ T)
    {X : Subgroup G} (hX : conjClosure L M ⊔ T ≤ X) (hXH : X ≤ H) :
    HypC28 X R (M ⊓ X) L V := by
  have hTX : T ≤ X := le_sup_right.trans hX
  have hM0X : conjClosure L M ≤ X := le_sup_left.trans hX
  have hRX : R ≤ X := hRT.trans hTX
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  have hLX : L ≤ X := (le_conjClosure L M).trans hM0X
  have hcc : conjClosure L (M ⊓ X) = conjClosure L M := conjClosure_inf_eq hA3 h hT hTX
  have hRMX : R ≤ M ⊓ X := le_inf h.le_M hRX
  have hOM : pCoreOf 2 M ≤ M ⊓ X :=
    le_inf (pCoreOf_le 2 M) ((B6.pCoreOf_two_le_of_isSylowTwoOf hT).trans hTX)
  have hOMO : pCoreOf 2 M ≤ pCoreOf 2 (M ⊓ X) :=
    le_pCoreOf_of_le_normalizer 2 hOM (fun g hg => le_normalizer_pCoreOf 2 M hg.1)
      (pCoreOf_isPGroup 2 M)
  have hOH : pCoreOf 2 H ≤ pCoreOf 2 X := by
    have hOHR : pCoreOf 2 H ≤ R := c2_1_pCore_le (c2_9_two h).2
    exact le_pCoreOf_of_le_normalizer 2 (hOHR.trans hRX)
      (fun g hg => le_normalizer_pCoreOf 2 H (hXH hg)) (pCoreOf_isPGroup 2 H)
  refine
    { sqtk := h.sqtk.mono hXH
      pgroup := h.pgroup
      le_M := hRMX
      le_H := inf_le_right
      charTwo := ?_
      pCore_ne := fun hbot => h.pCore_ne (le_bot_iff.mp (hbot ▸ hOH))
      comp := cComp_mem_of_le h.comp (le_inf hLM hLX) inf_le_left
      sylow := ?_
      cgs := le_inf ((cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le X R)
      V_le := ?_
      V_ne := h.V_ne
      V_elem := h.V_elem
      V_comm := ?_
      V_center := ?_
      V_norm := le_inf ((inf_le_inf_right _ hXH).trans h.V_norm) inf_le_left }
  · intro y hy
    have hyM : y ∈ M := hy.1.1
    have hyC : y ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
      Subgroup.centralizer_le hOMO hy.2
    exact hOMO (h.charTwo ⟨hyM, hyC⟩)
  · rw [hcc]
    have hK : R ≤ centralizerSection (M ⊓ X) (conjClosure L M) (pCoreOf 2 (conjClosure L M)) :=
      fun r hr => ⟨hRMX hr, (h.sylow.1 hr).2⟩
    exact A4.isSylowTwoOf_mono h.sylow hK (centralizerSection_mono inf_le_left _ _)
  · rw [hcc]
    exact h.V_le
  · rw [hcc]
    exact h.V_comm
  · rw [hcc]
    exact h.V_center

namespace C2Nine

omit [Finite G] in
theorem oddCoreIn_le_self (K : Subgroup G) : oddCoreIn K ≤ K := Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_oddCoreIn (K : Subgroup G) :
    K ≤ Subgroup.normalizer (oddCoreIn K : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : (fusionOddCore K).Normal) y hy ⟨k, hk⟩, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    refine ⟨⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : (fusionOddCore K).Normal) y hy ⟨k, hk⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hyg ⊢
      rw [hyg]
      group

theorem odd_card_oddCoreIn (K : Subgroup G) : Odd (Nat.card (oddCoreIn K)) := by
  rw [oddCoreIn, Nat.card_congr ((fusionOddCore K).equivMapOfInjective K.subtype
    K.subtype_injective).toEquiv.symm]
  exact CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
    (fun _ hmem => hmem.1) (fun _ hmem => hmem.2)

theorem oddCoreIn_inf_eq_bot {Q : Subgroup G} (hQ : IsPGroup 2 Q) (K : Subgroup G) :
    oddCoreIn K ⊓ Q = ⊥ := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (oddCoreIn K)) (Nat.card Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (odd_card_oddCoreIn K))
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

omit [Finite G] in
theorem isPGroup_two_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) : IsPGroup 2 V :=
  CFSG.Open.IsElemAbelian.isPGroup hV

theorem frattiniIn_eq_bot_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    frattiniIn V = ⊥ := by
  have hel : CFSG.IsElementaryAbelian 2 V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mpr hV
  have : Fact (IsPGroup 2 V) := ⟨isPGroup_two_of_isElemAbelian hV⟩
  have h1 : frattini V = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := V) (p := 2)
  simp [frattiniIn, h1]

end C2Nine

theorem c2_10_one (h : HypC28 H R M L V) : oddCoreIn H = ⊥ := by
  have hM0M := conjClosure_le_M h
  have hM0H : conjClosure L M ≤ H := hM0M.trans h.le_H
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p H) ≤ 2 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := sqt_iff.mp h.sqtk.1 p hp hp2
    rw [pRank_top_subtype] at h1
    exact (CFSG.SectionRank.pRank_mono hp.one_lt (pCoreOf_le p H)).trans h1
  have hV : V ≤ Subgroup.centralizer (fusionOddCoreOf H : Set G) :=
    a126_one hM0H (opResidual_eq_of_perfect (perfect_conjClosure_of_hyp h)) (h.V_le.trans hM0H)
      (isPGroup_two_of_isElemAbelian h.V_elem) h.V_comm hrank
      (frattiniIn_eq_bot_of_isElemAbelian h.V_elem)
  have hYM : oddCoreIn H ≤ M := by
    intro y hy
    have hyC : y ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact ((Subgroup.mem_centralizer_iff.mp (hV hv)) y hy).symm
    exact h.V_norm ⟨oddCoreIn_le_self H hy, Subgroup.centralizer_le_normalizer _ hyC⟩
  have hMn : M ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    h.le_H.trans (le_normalizer_oddCoreIn H)
  have hQ : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hYC : oddCoreIn H ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hyM := hYM hy
    have hqM : q ∈ M := pCoreOf_le 2 M hq
    have h1 : q * y⁻¹ * q⁻¹ ∈ oddCoreIn H :=
      (Subgroup.mem_normalizer_iff.mp (hMn hqM) y⁻¹).mp ((oddCoreIn H).inv_mem hy)
    have h2 : y * q * y⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hyM) q).mp hq
    have h3 : y * q * y⁻¹ * q⁻¹ ∈ oddCoreIn H ⊓ pCoreOf 2 M := by
      refine ⟨?_, (pCoreOf 2 M).mul_mem h2 ((pCoreOf 2 M).inv_mem hq)⟩
      have := (oddCoreIn H).mul_mem hy h1
      simpa [mul_assoc] using this
    rw [oddCoreIn_inf_eq_bot hQ H] at h3
    have h4 : y * q * y⁻¹ * q⁻¹ = 1 := h3
    calc q * y = y * q * y⁻¹ * q⁻¹ * (q * y) := by rw [h4, one_mul]
      _ = y * q := by group
  have hYQ : oddCoreIn H ≤ pCoreOf 2 M := fun y hy => h.charTwo ⟨hYM hy, hYC hy⟩
  rw [eq_bot_iff, ← oddCoreIn_inf_eq_bot hQ H]
  exact le_inf le_rfl hYQ

theorem c2_10_two (h : HypC28 H R M L V) : ∀ K : Subgroup G, IsComponentOf K H → ¬ K ≤ M := by
  intro K hK hKM
  have hsubM : IsSubnormal K M := by
    have := A3.subnormal_inf_right hK.2.1 h.le_H
    rwa [inf_eq_left.mpr hKM] at this
  have hKq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hK'q : CFSG.IsQuasisimple ↥(K.subgroupOf M) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKM).symm hKq
  have hK'sub : (K.subgroupOf M).IsSubnormal := (isSubnormal_iff_subgroupOf hKM).mp hsubM
  have hR2 : (CFSG.Open.pCore 2 ↥M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hRsolv : Group.IsSolvable (CFSG.Open.pCore 2 ↥M) := by
    have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥M) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).isNilpotent
    infer_instance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRsolv hR2.isSubnormal).1
    (K.subgroupOf M) ⟨hK'q, hK'sub⟩
  have hKC : K ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have h1 : (⟨k, hKM hk⟩ : ↥M) ∈ K.subgroupOf M := hk
    have h2 := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm h1) r hr
    exact congrArg Subtype.val h2
  have hKO : K ≤ pCoreOf 2 M := fun k hk => h.charTwo ⟨hKM hk, hKC hk⟩
  have hKp : IsPGroup 2 K := (pCoreOf_isPGroup 2 M).to_le hKO
  have : Group.IsNilpotent K := hKp.isNilpotent
  have := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have : Group.IsPerfect K := hKq.1
  exact Group.IsPerfect.not_isNilpotent K inferInstance

theorem c2_10_three (h : HypC28 H R M L V) :
    IsSylowTwoOf R (centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))) := by
  have hNM := inf_normalizer_le_M h
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
  have hRC' : R ≤ centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M)) :=
    h.sylow.1.trans (centralizerSection_mono h.le_H _ _)
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨hRC', h.pgroup, fun P hPC hP hRP => ?_⟩
  by_contra hPR
  have hlt : R < P := lt_of_le_of_ne hRP (fun heq => hPR (heq ▸ le_rfl))
  obtain ⟨s, hsP, hsN, hsR⟩ := A4.exists_mem_normalizer_not_mem hP hlt
  have hPN : P ⊓ Subgroup.normalizer (R : Set G) ≤
      centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) := by
    intro x hx
    have hxC := hPC hx.1
    exact ⟨hNM ⟨hxC.1, hx.2⟩, hxC.2⟩
  have := hmax _ hPN (hP.to_le inf_le_left) (le_inf hRP Subgroup.le_normalizer)
  exact hsR (this ⟨hsP, hsN⟩)

theorem c2_10_four (h : HypC28 H R M L V) : HypC23 H R M := by
  have hRC := h.sylow.1
  have hcl : conjClosure R M ≤
      centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) := by
    refine conjClosure_le fun m hm r hr => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (centralizerSection_normal (le_normalizer_conjClosure L M) hm) r).mp (hRC hr)
  exact ⟨h.sqtk, (c2_9_two h).2, h.le_H, h.cgs,
    A4.isSylowTwoOf_mono h.sylow (le_conjClosure R M) hcl⟩

theorem c2_10_five (h : HypC28 H R M L V) :
    {S : Subgroup G | IsMaxSignalizer (H ⊓ Subgroup.normalizer (R : Set G))
      (conjClosure L M) S} = {R} := by
  have hM0M := conjClosure_le_M h
  have hNM := inf_normalizer_le_M h
  have hM0N : conjClosure L M ≤ H ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf (hM0M.trans h.le_H) (c2_9_two h).1
  have hNn : ((conjClosure L M).subgroupOf (H ⊓ Subgroup.normalizer (R : Set G))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hNM.trans (le_normalizer_conjClosure L M))
  have hup : conjClosure L M = oTwoUpper (conjClosure L M) :=
    (oTwoUpper_eq_of_perfect (perfect_conjClosure_of_hyp h)).symm
  have hsub : IsSubnormal (conjClosure L M) (H ⊓ Subgroup.normalizer (R : Set G)) :=
    A4.subnormal_of_normal hM0N hNn
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
  have hRN : R ≤ H ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf (h.le_M.trans h.le_H) Subgroup.le_normalizer
  have hRK : R ≤ centralizerSection (H ⊓ Subgroup.normalizer (R : Set G)) (conjClosure L M)
      (pCoreOf 2 (conjClosure L M)) := fun r hr => ⟨hRN hr, (h.sylow.1 hr).2⟩
  have hKC : centralizerSection (H ⊓ Subgroup.normalizer (R : Set G)) (conjClosure L M)
      (pCoreOf 2 (conjClosure L M)) ≤
      centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) :=
    centralizerSection_mono hNM _ _
  ext S
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [a4_2_4 hup hsub S]
  constructor
  · intro hS
    have hKN : centralizerSection (H ⊓ Subgroup.normalizer (R : Set G)) (conjClosure L M)
        (pCoreOf 2 (conjClosure L M)) ≤ Subgroup.normalizer (R : Set G) :=
      (centralizerSection_le_left _ _ _).trans inf_le_right
    have hRS : R ≤ S := A4.le_of_normal_of_isSylowTwoOf hS hRK
      (Subgroup.normal_subgroupOf_of_le_normalizer hKN) h.pgroup
    exact le_antisymm (hmax S (hS.1.trans hKC) hS.2.1 hRS) hRS
  · rintro rfl
    exact A4.isSylowTwoOf_mono h.sylow hRK hKC

end CFSG.Quasithin
