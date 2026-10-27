module

public import CFSG.Quasithin.EmptyFaithful.S1422Main
public import CFSG.Quasithin.EmptyFaithful.S1421Facts
public import CFSG.Quasithin.EmptyFaithful.S1421L246

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem card_mulAut_le_of_card_four {V : Type*} [Group V] (h : Nat.card V = 4) :
    Nat.card (MulAut V) ≤ 6 := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  classical
  let f : MulAut V → Equiv.Perm {v : V // v ≠ 1} := fun σ =>
    σ.toEquiv.subtypeEquiv (fun a => by simp)
  have hf : Function.Injective f := by
    intro σ τ hστ
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · have := congrArg (fun p => (p ⟨v, hv⟩ : V)) hστ
      simpa [f] using this
  have h3 : Fintype.card {v : V // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, h]
  have hperm : Nat.card (Equiv.Perm {v : V // v ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]
    rfl
  exact (Nat.card_le_card_of_injective f hf).trans hperm.le


theorem exists_central_involution_of_normal {G : Type*} [Group G] [Finite G] {T C : Subgroup G}
    (hT : IsPGroup 2 T) (hCT : C ≤ T) (hCn : ∀ t ∈ T, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (hC : C ≠ ⊥) : ∃ x ∈ C, x ≠ 1 ∧ x ^ 2 = 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let Cs : Subgroup ↥T := C.subgroupOf T
  have : Cs.Normal := ⟨fun n hn g => by
    simpa [Cs, Subgroup.mem_subgroupOf] using hCn g g.2 n hn⟩
  have hCs : Cs ≠ ⊥ := by
    intro h
    apply hC
    rw [eq_bot_iff]
    intro c hc
    have hc' : (⟨c, hCT hc⟩ : ↥T) ∈ Cs := hc
    rw [h, Subgroup.mem_bot] at hc'
    have := congrArg Subtype.val hc'
    simpa using this
  have hW : Cs ⊓ Subgroup.center ↥T ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hCs
  have hWp : IsPGroup 2 ↥(Cs ⊓ Subgroup.center ↥T) := hT.to_subgroup _
  have h2 : 2 ∣ Nat.card ↥(Cs ⊓ Subgroup.center ↥T) := by
    rcases hWp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hW
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨(((w : ↥(Cs ⊓ Subgroup.center ↥T)) : ↥T) : G), w.2.1, ?_, ?_, ?_⟩
  · intro h1
    have : w = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    rw [this, orderOf_one] at hw
    omega
  · have := pow_orderOf_eq_one w
    rw [hw] at this
    have := congrArg (fun u : ↥(Cs ⊓ Subgroup.center ↥T) => (((u : ↥T)) : G)) this
    simpa using this
  · intro t ht
    have := Subgroup.mem_center_iff.mp w.2.2 ⟨t, ht⟩
    exact congrArg Subtype.val this


theorem mem_autOn_iff_exists_conj {G : Type*} [Group G] {X V : Subgroup G} {a : MulAut V} :
    a ∈ autOn X V ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ X ∧
      conjAct V ⟨x, hx⟩ = a :=
  CFSG.Quasithin.AutOn.mem_autOn_iff_exists

namespace Hyp1421

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem inf_centralizer_yOfL22_eq_bot (h : Hyp1421 G T M) (f : Facts1422 T M) :
    T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) = ⊥ := by
  by_contra hne
  have hTM : T ≤ M := h.m_max.1.2
  have hMY := le_normalizer_yOfL22 T M
  have hYM := yOfL22_le T M
  have hCn : ∀ t ∈ T, ∀ c ∈ T ⊓ Subgroup.centralizer (yOfL22 T M : Set G),
      t * c * t⁻¹ ∈ T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) := by
    intro t ht c hc
    refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem ht hc.1) (T.inv_mem ht), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : t⁻¹ * y * t ∈ yOfL22 T M := by
      have := (Subgroup.mem_normalizer_iff.mp (hMY (hTM (T.inv_mem ht))) y).mp hy
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hc.2 _ hy'
    calc y * (t * c * t⁻¹) = t * ((t⁻¹ * y * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * y * t)) * t⁻¹ := by rw [this]
      _ = t * c * t⁻¹ * y := by group
  obtain ⟨x, hxC, hx1, hx2, hxc⟩ := exists_central_involution_of_normal (T := T)
    (C := T ⊓ Subgroup.centralizer (yOfL22 T M : Set G)) h.sylow.1 inf_le_left hCn hne
  have hxZ : x ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hxC.1, Subgroup.mem_centralizer_iff.mpr fun t ht => hxc t ht⟩, hx2⟩
  have hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x := by
    obtain ⟨x', hx'⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp
      h.card_omegaOneCenter
    intro z hz
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    · right
      have e1 : (⟨z, hz⟩ : ↥(quasithinOmegaOneCenter T)) = x' :=
        hx'.2 ⟨z, hz⟩ (fun e => hz1 (congrArg Subtype.val e))
      have e2 : (⟨x, hxZ⟩ : ↥(quasithinOmegaOneCenter T)) = x' :=
        hx'.2 ⟨x, hxZ⟩ (fun e => hx1 (congrArg Subtype.val e))
      exact congrArg Subtype.val (e1.trans e2.symm)
  have hVC : VZ T M ≤ Subgroup.centralizer (yOfL22 T M : Set G) := by
    refine conjClosure_le fun m hm w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hZ w hw with rfl | rfl
    · simp
    · have hy' : m⁻¹ * y * m ∈ yOfL22 T M := by
        have := (Subgroup.mem_normalizer_iff.mp (hMY (M.inv_mem hm)) y).mp hy
        simpa using this
      have := Subgroup.mem_centralizer_iff.mp hxC.2 _ hy'
      calc y * (m * w * m⁻¹) = m * ((m⁻¹ * y * m) * w) * m⁻¹ := by group
        _ = m * (w * (m⁻¹ * y * m)) * m⁻¹ := by rw [this]
        _ = m * w * m⁻¹ * y := by group
  have hbot : autOn (yOfL22 T M) (VZ T M) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨g, hgN, hgY, rfl⟩ := mem_autOn_iff_exists_conj.mp hσ
    exact A4.conjAct_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hVC hv) g hgY).symm)
  have := f.y_card
  rw [hbot] at this
  simp at this

theorem le_sup_centralizer_of_facts1422 (h : Hyp1421 G T M) (f : Facts1422 T M) :
    M ≤ (yOfL22 T M ⊔ T) ⊔ (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  have hTM : T ≤ M := h.m_max.1.2
  have hXM : yOfL22 T M ⊔ T ≤ M := sup_le (yOfL22_le T M) hTM
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ M
  have hXN : yOfL22 T M ⊔ T ≤ Subgroup.normalizer (VZ T M : Set G) := hXM.trans hMV
  set φ : ↥(yOfL22 T M ⊔ T) →* MulAut ↥(VZ T M) :=
    (conjAct (VZ T M)).comp (Subgroup.inclusion hXN) with hφ
  have hC := f.centralizer_yT
  have hker : CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ T) = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxO : (x : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ T) := ⟨x, hx, rfl⟩
      rw [← hC] at hxO
      exact A4.conjAct_eq_one_iff.mpr hxO.2
    · intro hx
      have hxC : (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) := A4.conjAct_eq_one_iff.mp hx
      have hxO : (x : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ T) := by
        rw [← hC]
        exact ⟨x.2, hxC⟩
      obtain ⟨y, hy, hyx⟩ := hxO
      have hyx' : y = x := Subtype.ext hyx
      rwa [← hyx']
  have hrange : Nat.card φ.range = 6 := by
    obtain ⟨e3⟩ := f.sThree
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      Nat.card_congr e3.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hA := card_mulAut_le_of_card_four h.rank_two
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm (Subgroup.card_le_card_group _) (by omega)
  intro m hm
  have hmN := hMV hm
  obtain ⟨x, hx⟩ : ∃ x : ↥(yOfL22 T M ⊔ T), φ x = conjAct (VZ T M) ⟨m, hmN⟩ := by
    have : conjAct (VZ T M) ⟨m, hmN⟩ ∈ φ.range := by rw [htop]; trivial
    exact this
  have hxm : (x : G)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) := by
    have key : conjAct (VZ T M) ((⟨(x : G), hXN x.2⟩ :
        Subgroup.normalizer (VZ T M : Set G))⁻¹ * ⟨m, hmN⟩) = 1 := by
      rw [map_mul, map_inv]
      change (φ x)⁻¹ * conjAct (VZ T M) ⟨m, hmN⟩ = 1
      rw [hx, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.mp key
  have hxM : (x : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (hXM x.2)) hm
  have : m = (x : G) * ((x : G)⁻¹ * m) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right ⟨hxM, hxm⟩)

theorem isSylow_charTwo_of_isHStar (h : Hyp1421 G T M) {H : Subgroup G} (hH : IsHStar T M H) :
    IsSylowTwoOf T H ∧ CharTwo H := by
  obtain ⟨P, hP⟩ := h.toQTFE14.exists_sylow
  refine ⟨?_, ?_⟩
  · subst hP
    exact isSylowTwoOf_of_sylow P hH.1.1
  · exact charTwo_of_le h.qtke.2.1 P (hP ▸ hH.1.1) le_rfl (hP ▸ hH.1 : InH (P : Subgroup G) H)

theorem vz_le_pCoreOf (h : Hyp1421 G T M) (f : Facts1422 T M) {H : Subgroup G}
    (hH : IsHStar T M H) : VZ T M ≤ pCoreOf 2 H := by
  obtain ⟨hsyl, hchar⟩ := h.isSylow_charTwo_of_isHStar hH
  have h26 := lemma_14_2_6_two h f hH.1 hH.2.1
  have h261 := lemma_14_2_6_one h f hH.1 hH.2.1
  have hZQ : quasithinOmegaOneCenter T ≤ pCoreOf 2 H :=
    omegaOneCenter_le_pCoreOf_of_charTwo hsyl hchar
  intro v hv
  have hvN : v ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := h261.elemAbelian.1.is_comm.comm (⟨z, h261.le_V hz⟩ : ↥(VZ T M)) ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hvU : v ∈ conjClosure (VZ T M) H := le_conjClosure (VZ T M) H hv
  have h1 := secMk_mem_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (x := ⟨v, hvN⟩) hvU
  have h2 := omegaOneCenterOf_le _ (h26.1 h1)
  exact (secMk_mem_secImg_iff hZQ).mp h2

theorem lemma1422Data (h : Hyp1421 G T M) (f : Facts1422 T M) :
    Lemma1422Data T M (yOfL22 T M) where
  le := yOfL22_le T M
  normalizes := le_normalizer_yOfL22 T M
  quot := f.sThree
  unique := f.unique
  centralizes := h.inf_centralizer_yOfL22_eq_bot f
  generate := h.le_sup_centralizer_of_facts1422 f

end Hyp1421

theorem stage1422Data_of_facts1422Input (hF : Facts1422Input) : Stage1422Data :=
  fun G _ _ T M h => ⟨yOfL22 T M, h.lemma1422Data (hF G T M h)⟩

theorem stage1426VleQ_of_facts1422Input (hF : Facts1422Input) : Stage1426VleQ :=
  fun G _ _ T M h _ hH => h.vz_le_pCoreOf (hF G T M h) hH

theorem stageTheorem14220_of_facts1422 (hFacts : Facts1422Input) (hF112 : F112LegacyPrintedError)
    (hLoc : Lemma14221Local) (hF431 : F431Statement) (hNS : ModelNotSimple)
    (hABG : ABGWreathedRecognition) (hG22p : G22pAmalgamFacts)
    (hI46 : CFSG.GH74.M12.S_Asc03_simple) (hM12 : M12AmalgamFacts)
    (hAut : AutM12AmalgamFacts) : StageTheorem14220 :=
  stageTheorem14220_of_inputs hF112 (stage1422Data_of_facts1422Input hFacts)
    (stage1426VleQ_of_facts1422Input hFacts) hLoc hF431 hNS hABG hG22p hI46 hM12 hAut

theorem stageTheorem14220_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF112 : F112LegacyPrintedError) (hLoc : Lemma14221Local) (hF431 : F431Statement)
    (hNS : ModelNotSimple) (hABG : ABGWreathedRecognition) (hG22p : G22pAmalgamFacts)
    (hI46 : CFSG.GH74.M12.S_Asc03_simple) (hM12 : M12AmalgamFacts)
    (hAut : AutM12AmalgamFacts) : StageTheorem14220 :=
  stageTheorem14220_of_facts1422 (facts1422Input_of_stages h11 h113) hF112 hLoc hF431 hNS hABG
    hG22p hI46 hM12 hAut

end CFSG.Quasithin
