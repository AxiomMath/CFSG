module

public import CFSG.Milestones.ASVolI.C5

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_exists_comm_partner {G : Type} [Group G] {H TH R K₁ : Subgroup G}
    (cfg : BlockConfig H TH R K₁) :
    ∃ L' : Subgroup G, (∀ a ∈ K₁, ∀ b ∈ L', a * b = b * a) ∧ K₁ ⊔ L' = oTwoUpper H := by
  classical
  have h1 : conjByElt (1 : G) K₁ = K₁ := by
    ext x
    rw [mem_conjByElt]
    simp
  set L' : Subgroup G :=
    ⨆ (t : G) (_ : t ∈ TH) (_ : conjByElt t K₁ ≠ K₁), conjByElt t K₁ with hL'
  refine ⟨L', ?_, ?_⟩
  · have hle : L' ≤ Subgroup.centralizer (K₁ : Set G) := by
      refine iSup₂_le fun t ht => iSup_le fun hne => ?_
      have h := cfg.commute t ht 1 TH.one_mem (by rw [h1]; exact hne)
      rw [h1] at h
      exact h
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hb) a ha)
  · rw [cfg.prod]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · have := le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) => conjByElt t K₁) 1 TH.one_mem
        rwa [h1] at this
      · refine iSup₂_le fun t ht => iSup_le fun hne => ?_
        exact le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) => conjByElt t K₁) t ht
    · refine iSup₂_le fun t ht => ?_
      by_cases h : conjByElt t K₁ = K₁
      · rw [h]
        exact le_sup_left
      · refine le_sup_of_le_right ?_
        exact le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) =>
          ⨆ (_ : conjByElt t K₁ ≠ K₁), conjByElt t K₁) t ht |>.trans' (le_iSup (fun _ => conjByElt t K₁) h)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c55_main {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) :
    ¬ CFSG.Quasithin.conjClosure (blockU K₁) M₀ ≤ pCoreOf 2 H := by
  classical
  intro hX
  have hyp1 := hset.hyp1
  have hyp2 := hset.hyp2
  have cfg := hset.config
  have hshort : IsShort2 K₁ := cfg.chi0.1.1
  have hK₁H : K₁ ≤ H := cfg.chi0.1.2.1
  have hUne : blockU K₁ ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.Campbell.blockU_ne_bot_of_isShort2 hshort
  obtain ⟨L', hcomm, hjoin⟩ := burnsideC5h_exists_comm_partner cfg
  have hTM : TH ≤ M₀ := hyp1.TH_le
  have hMR : M₀ ≤ Subgroup.normalizer (R : Set G) := hyp1.R_norm
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hKjoin : oTwoUpper H = K₁ ⊔ L' := hjoin.symm
  have hQK₁ : blockQ K₁ ≤ pCoreOf 2 (oTwoUpper H) := by
    refine C1.le_pCoreOf_of_normalized ((C1.blockQ_le K₁).trans (hKjoin ▸ le_sup_left)) ?_
      (C1.blockQ_isPGroup K₁)
    rw [hKjoin]
    refine sup_le (C1.le_normalizer_blockQ K₁) ?_
    exact Setup.Campbell.le_normalizer_of_commute (C1.blockQ_le K₁) fun x hx y hy => hcomm x hx y hy
  have hQKR : pCoreOf 2 (oTwoUpper H) ≤ R := by
    have hRK : R ⊔ oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) := by
      refine sup_le ?_ (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
      exact (hyp1.R_le.trans hyp1.sylow.1).trans
        (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)))
    have h1 : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (R ⊔ oTwoUpper H) :=
      C1.le_pCoreOf_of_normalized
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans le_sup_right) hRK
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    exact h1.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hyp1.sylow_R)
  have hUR : blockU K₁ ≤ R := (C1.blockU_le_blockQ hshort).trans (hQK₁.trans hQKR)
  set X : Subgroup G := CFSG.Quasithin.conjClosure (blockU K₁) M₀ with hXdef
  have hXR : X ≤ R := by
    refine CFSG.Quasithin.conjClosure_le fun h hh z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hMR hh) z).mp (hUR hz)
  have hXne : X ≠ ⊥ := fun h =>
    hUne (le_bot_iff.mp ((CFSG.Quasithin.le_conjClosure _ _).trans h.le))
  have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) := CFSG.Quasithin.le_normalizer_conjClosure _ _
  have hUX : blockU K₁ ≤ X := CFSG.Quasithin.le_conjClosure _ _
  have key : ∀ k ∈ K₁, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
    intro k hk x hx
    have hHN : H ≤ Subgroup.normalizer ((K₁ ⊔ L' : Subgroup G) : Set G) := by
      rw [← hKjoin]; exact hHK
    have hc := C1.commutator_mem_blockU_double hshort (L' := L') hcomm hK₁H hHN (hX hx) hk
    have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUX hc)) hx
  have hK₁X : K₁ ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => key k hk x hx, fun h => by simpa [mul_assoc] using key k⁻¹ (inv_mem hk) _ h⟩
  have hconj : ∀ t ∈ TH, conjByElt t K₁ ≤ Subgroup.normalizer (X : Set G) := by
    intro t ht y hy
    rw [mem_conjByElt] at hy
    have htX : t ∈ Subgroup.normalizer (X : Set G) := hM₀X (hTM ht)
    have e : y = t * (t⁻¹ * y * t) * t⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htX (hK₁X hy)) (Subgroup.inv_mem _ htX)
  have hKX : oTwoUpper H ≤ Subgroup.normalizer (X : Set G) := by
    rw [cfg.prod]
    exact iSup₂_le fun t ht => hconj t ht
  have hHKT : TH ⊔ oTwoUpper H = H := by
    rw [← CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hyp1.sylow
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hHKT]
    exact sup_le (hTM.trans hM₀X) hKX
  exact hyp2 X hXR hXne (sup_le hM₀X hHX)

theorem as_C_5_5 : C_5_5 := by
  intro G _ _ H M₀ TH R K₁ hset
  exact burnsideC5h_c55_main hset

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_oTwoUpper_eq_bot {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hchar : CharTwo H) (hodd : ¬ 2 ∣ Nat.card (oTwoUpper H)) : oTwoUpper H = ⊥ := by
  set K := oTwoUpper H with hK
  set P := pCoreOf 2 H with hP
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hKH : K ≤ H := oTwoUpper_le H
  have hPn : H ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hPH : P ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hKP : K ⊓ P = ⊥ := by
    have h2 : IsPGroup 2 (K ⊓ P : Subgroup G) := hP2.to_le inf_le_right
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdvd : Nat.card (K ⊓ P : Subgroup G) ∣ Nat.card K :=
      Subgroup.card_dvd_of_le inf_le_left
    have hn0 : n = 0 := by
      by_contra hne
      rw [hn] at hdvd
      exact hodd ((dvd_pow_self 2 hne).trans hdvd)
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  have hKc : K ≤ Subgroup.centralizer (P : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 : k * p * k⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hPn (hKH hk)) p).mp hp
    have h2 : p * k⁻¹ * p⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKn (hPH hp)) k⁻¹).mp (K.inv_mem hk)
    have h3 : k * p * k⁻¹ * p⁻¹ ∈ K ⊓ P := by
      refine ⟨?_, ?_⟩
      · have : k * p * k⁻¹ * p⁻¹ = k * (p * k⁻¹ * p⁻¹) := by group
        rw [this]
        exact K.mul_mem hk h2
      · exact P.mul_mem h1 (P.inv_mem hp)
    rw [hKP, Subgroup.mem_bot] at h3
    have h5 : k * p * k⁻¹ = p := by
      calc k * p * k⁻¹ = (k * p * k⁻¹ * p⁻¹) * p := by group
        _ = p := by rw [h3, one_mul]
    calc p * k = (k * p * k⁻¹) * k := by rw [h5]
      _ = k * p := by group
  refine le_bot_iff.mp ?_
  rw [← hKP]
  exact le_inf le_rfl (fun k hk => hchar ⟨hKH hk, hKc hk⟩)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_ne_bot {G : Type} [Group G] [Finite G] {H M₀ T R : Subgroup G}
    (hH : HypC_5_1 H M₀ T R) : R ≠ ⊥ := by
  rintro rfl
  have hs := hH.sylow_R
  rw [bot_sup_eq] at hs
  have hodd : ¬ 2 ∣ Nat.card (oTwoUpper H) := by
    have h := hs.2.2
    rwa [Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
  have hK : oTwoUpper H = ⊥ := burnsideC5h_c54_oTwoUpper_eq_bot hH.charTwo hodd
  have hHT : T ⊔ twoResidual H = H := sup_twoResidual_eq hH.sylow
  rw [CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper, hK, sup_bot_eq] at hHT
  obtain ⟨N, hN⟩ := hH.unique_max
  have hmem : N ∈ maxOver H T := by
    unfold IsUniqueMaxOver at hN
    rw [hN]
    exact Set.mem_singleton N
  obtain ⟨⟨hNH, -⟩, hTN⟩ := hmem
  exact lt_irrefl _ ((hTN.trans_lt hNH).trans_eq hHT.symm)

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c54_conjByElt_one {G : Type} [Group G] (K : Subgroup G) :
    conjByElt (1 : G) K = K := by
  ext x
  rw [mem_conjByElt]
  simp

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c54_mem_normalizer_conjClosure {G : Type} [Group G] {Z X : Subgroup G} {g : G}
    (hZ : g ∈ Subgroup.normalizer (Z : Set G)) (hX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (CFSG.Quasithin.conjClosure Z X : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (Z : Set G) → g ∈ Subgroup.normalizer (X : Set G) →
      ∀ y ∈ CFSG.Quasithin.conjClosure Z X, g * y * g⁻¹ ∈ CFSG.Quasithin.conjClosure Z X := by
    intro g hZ hX y hy
    unfold CFSG.Quasithin.conjClosure at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      have e : g * (h * z * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
      rw [e]
      exact CFSG.Quasithin.mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hX h).mp hh)
        ((Subgroup.mem_normalizer_iff.mp hZ z).mp hz)
    | one => simp
    | mul x y _ _ ihx ihy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ih =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ih
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hZ hX y hy, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hZ) (inv_mem hX) _ hy
  simpa [mul_assoc] using this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_one_core (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) :
    baum R ≤ Subgroup.normalizer (K₁ : Set G) := by
  classical
  have hyp1 := hset.hyp1
  have hyp2 := hset.hyp2
  have cfg := hset.config
  have hTM : TH ≤ M₀ := hyp1.TH_le
  have hMR : M₀ ≤ Subgroup.normalizer (R : Set G) := hyp1.R_norm
  have hRTH : R ≤ TH := hyp1.R_le
  have hTHsyl := hyp1.sylow
  have hR2 : IsPGroup 2 R := hTHsyl.2.1.to_le hRTH
  have hR1 : R ≠ ⊥ := burnsideC5h_c54_ne_bot hyp1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hTR : TH ≤ Subgroup.normalizer (R : Set G) := hTM.trans hMR
  set X : Subgroup G := oTwoUpper H ⊔ R with hXdef
  have hXH : X ≤ H := sup_le hKH (hRTH.trans hTHsyl.1)
  have hKT : TH ⊔ oTwoUpper H = H := by
    rw [← CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hTHsyl
  have hTX : TH ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    C1.mem_normalizer_sup (hHK (hTHsyl.1 ht)) (hTR ht)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hKT]
    exact sup_le hTX (le_sup_left.trans Subgroup.le_normalizer)
  have hcharX : CharTwo X := CFSG.Quasithin.A4.charTwo_of_normal hXH hHX hyp1.charTwo
  have hRX : IsSylowTwoOf R X := by
    have := hyp1.sylow_R
    rwa [sup_comm] at this
  set Z : Subgroup G := quasithinOmegaOneCenter R with hZdef
  set V : Subgroup G := CFSG.Quasithin.conjClosure Z X with hVdef
  have hred : IsTwoReducedIn X V :=
    isTwoReducedIn_conjClosure_of_sylowIn hRX.1 hR2 hRX.2.2 hcharX le_rfl
  have hhyp : HypC_1_14 X V R := ⟨hcharX, hred, hRX⟩
  have hshort : IsShort2 K₁ := cfg.chi0.1.1
  have hK₁K : K₁ ≤ oTwoUpper H := by
    rw [cfg.prod]
    have := le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) => conjByElt t K₁) 1 TH.one_mem
    rwa [burnsideC5h_c54_conjByElt_one] at this
  have hK₁X : K₁ ≤ X := hK₁K.trans le_sup_left
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z X
  have hZV : Z ≤ V := CFSG.Quasithin.le_conjClosure Z X
  have hsub : (K₁.subgroupOf X).IsSubnormal := by
    have := Subgroup.IsSubnormal.comap (Subgroup.inclusion hXH) cfg.chi0.1.2.2
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hchi : IsChiBlock2 X K₁ := by
    refine ⟨⟨hshort, hK₁X, hsub⟩, ?_⟩
    rcases cfg.chi0.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨3, by decide, h⟩
    · exact Or.inr ⟨5, by decide, h⟩
  have hZR : Z ≤ R := by
    have : omegaOneCenterOf R ≤ R := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R
    exact this
  have hZne : Z ≠ ⊥ := quasithinOmegaOneCenter_ne_bot hR2 hR1
  have hZchar : (Z.subgroupOf R).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R
  have hZcenter : Z ≤ centerOf R := by
    show omegaOneOf (centerOf R) ≤ centerOf R
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hZcent : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r := fun r hr z hz =>
    Subgroup.mem_centralizer_iff.mp (hZcenter hz).2 r hr
  have hTZ : TH ≤ Subgroup.normalizer (Z : Set G) := fun t ht =>
    normalizer_le_normalizer_of_characteristic hZR hZchar (hTR ht)
  have hTV : TH ≤ Subgroup.normalizer (V : Set G) := fun t ht =>
    burnsideC5h_c54_mem_normalizer_conjClosure (hTZ ht) (hTX ht)
  have hK₁ncent : ¬ K₁ ≤ Subgroup.centralizer (V : Set G) := by
    intro hKC
    have hKcentV : oTwoUpper H ≤ Subgroup.centralizer (V : Set G) := by
      rw [cfg.prod]
      refine iSup₂_le fun t ht y hy => ?_
      rw [mem_conjByElt] at hy
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hw : t⁻¹ * v * t ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hTV (inv_mem ht)) v).mp hv
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_centralizer_iff.mp (hKC hy)) _ hw
      calc v * y = t * (t⁻¹ * v * t * (t⁻¹ * y * t)) * t⁻¹ := by group
        _ = t * (t⁻¹ * y * t * (t⁻¹ * v * t)) * t⁻¹ := by rw [h1]
        _ = y * v := by group
    have hKcentZ : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
      hKcentV.trans (Subgroup.centralizer_le hZV)
    have hKZ : oTwoUpper H ≤ Subgroup.normalizer (Z : Set G) :=
      hKcentZ.trans (Subgroup.centralizer_le_normalizer _)
    have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := by
      rw [← hKT]
      exact sup_le hTZ hKZ
    have hM₀Z : M₀ ≤ Subgroup.normalizer (Z : Set G) := fun m hm =>
      normalizer_le_normalizer_of_characteristic hZR hZchar (hMR hm)
    exact hyp2 Z hZR hZne (sup_le hM₀Z hHZ)
  have hJX : thompsonJ R ≤ X := (B6.thompsonJ_le R).trans hRX.1
  have hcomm : ⁅autOn K₁ V, autOn (thompsonJ R) V⁆ ≠ ⊥ := by
    intro h
    have hK₁V : K₁ ≤ Subgroup.normalizer (V : Set G) := hK₁X.trans hXV
    have hJV : thompsonJ R ≤ Subgroup.normalizer (V : Set G) := hJX.trans hXV
    have h' := CFSG.Quasithin.S153D.autOn_commutator hK₁V hJV
    rw [h, cfg.comm_J] at h'
    apply hK₁ncent
    intro k hk
    have hmem : conjAct V ⟨k, hK₁V hk⟩ ∈ autOn K₁ V :=
      CFSG.Quasithin.AutOn.mem_autOn_iff_exists.mpr ⟨k, hK₁V hk, hk, rfl⟩
    rw [h', Subgroup.mem_bot] at hmem
    exact CFSG.Quasithin.A4.conjAct_eq_one_iff.mp hmem
  exact (h116 G X V R hhyp).2.1 K₁ hchi hcomm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_one (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) :
    ∀ Ki ∈ conjSubgroupsBy TH K₁, baum R ≤ Subgroup.normalizer (Ki : Set G) := by
  rintro Ki ⟨t, ht, rfl⟩ b hb
  have hcore := burnsideC5h_c54_one_core h116 hset
  have hTR : TH ≤ Subgroup.normalizer (R : Set G) := hset.hyp1.TH_le.trans hset.hyp1.R_norm
  have htB : t⁻¹ ∈ Subgroup.normalizer (baum R : Set G) :=
    inv_mem (CFSG.Quasithin.normalizer_le_normalizer_baum R (hTR ht))
  have hb' : t⁻¹ * b * t ∈ baum R := by
    have := (Subgroup.mem_normalizer_iff.mp htB b).mp hb
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h := Subgroup.mem_normalizer_iff.mp (hcore hb') (t⁻¹ * y * t)
  have e : t⁻¹ * b * t * (t⁻¹ * y * t) * (t⁻¹ * b * t)⁻¹ = t⁻¹ * (b * y * b⁻¹) * t := by group
  rw [e] at h
  change y ∈ conjByElt t K₁ ↔ b * y * b⁻¹ ∈ conjByElt t K₁
  rw [mem_conjByElt, mem_conjByElt]
  exact h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_conj_le {G : Type} [Group G] {H TH R K₁ : Subgroup G}
    (cfg : BlockConfig H TH R K₁) {L : Subgroup G} (hL : L ∈ conjSubgroupsBy TH K₁) :
    L ≤ oTwoUpper H := by
  obtain ⟨t, ht, rfl⟩ := hL
  rw [cfg.prod]
  exact le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) => conjByElt t K₁) t ht

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_isBlock2 {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {L : Subgroup G} (hL : L ∈ conjSubgroupsBy TH K₁) :
    IsBlock2 (oTwoUpper H ⊔ R) L := by
  have hyp1 := hset.hyp1
  have cfg := hset.config
  obtain ⟨t, ht, rfl⟩ := hL
  have hXH : oTwoUpper H ⊔ R ≤ H := sup_le (oTwoUpper_le H) (hyp1.R_le.trans hyp1.sylow.1)
  have hBH : IsBlock2 H (conjByElt t K₁) := by
    have h := C58.isBlock2_conjSubgroup cfg.chi0.1 (inv_mem (hyp1.sylow.1 ht))
    have e : conjSubgroup K₁ t⁻¹ = conjByElt t K₁ := by
      unfold conjSubgroup conjByElt
      rw [inv_inv]
    rwa [e] at h
  have hLK : conjByElt t K₁ ≤ oTwoUpper H :=
    burnsideC5h_c54_conj_le cfg (⟨t, ht, rfl⟩ : conjByElt t K₁ ∈ conjSubgroupsBy TH K₁)
  refine ⟨hBH.1, hLK.trans le_sup_left, ?_⟩
  have := Subgroup.IsSubnormal.comap (Subgroup.inclusion hXH) hBH.2.2
  rwa [Subgroup.comap_inclusion_subgroupOf] at this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped commutatorElement in
theorem burnsideC5h_c54_commutator_eq {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) :
    ⁅pCoreOf 2 (oTwoUpper H), oTwoUpper H⁆ = ⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki := by
  classical
  have hyp1 := hset.hyp1
  have cfg := hset.config
  have hshort : IsShort2 K₁ := cfg.chi0.1.1
  have hK₁H : K₁ ≤ H := cfg.chi0.1.2.1
  have hTHH : TH ≤ H := hyp1.sylow.1
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  obtain ⟨L', hcomm, hjoin⟩ := burnsideC5h_exists_comm_partner cfg
  set K := oTwoUpper H with hK
  set U : Subgroup G := ⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki with hU
  have hconjmem : ∀ t ∈ TH, conjByElt t K₁ ∈ conjSubgroupsBy TH K₁ := fun t ht => ⟨t, ht, rfl⟩
  have hshortc : ∀ t ∈ TH, IsShort2 (conjByElt t K₁) := fun t ht =>
    (burnsideC5h_c54_isBlock2 hset (hconjmem t ht)).1
  have hleK : ∀ t ∈ TH, conjByElt t K₁ ≤ K := fun t ht =>
    burnsideC5h_c54_conj_le cfg (hconjmem t ht)
  have hcomm' : ∀ t ∈ TH, ∀ t' ∈ TH, conjByElt t K₁ ≠ conjByElt t' K₁ →
      ∀ x ∈ conjByElt t K₁, ∀ y ∈ conjByElt t' K₁, Commute x y := by
    intro t ht t' ht' hne x hx y hy
    have h := cfg.commute t ht t' ht' hne hx
    exact (Subgroup.mem_centralizer_iff.mp h y hy).symm
  have hKjQ : ∀ t ∈ TH, ∀ t' ∈ TH,
      conjByElt t' K₁ ≤ Subgroup.normalizer (blockQ (conjByElt t K₁) : Set G) := by
    intro t ht t' ht'
    by_cases heq : conjByElt t' K₁ = conjByElt t K₁
    · rw [heq]; exact C1.le_normalizer_blockQ _
    · exact Setup.Campbell.le_normalizer_of_commute (C1.blockQ_le _)
        (fun x hx y hy => hcomm' t ht t' ht' (Ne.symm heq) x hx y hy)
  have hKjU : ∀ t ∈ TH, ∀ t' ∈ TH,
      conjByElt t' K₁ ≤ Subgroup.normalizer (blockU (conjByElt t K₁) : Set G) := by
    intro t ht t' ht'
    by_cases heq : conjByElt t' K₁ = conjByElt t K₁
    · rw [heq]; exact C1.le_normalizer_blockU _
    · exact Setup.Campbell.le_normalizer_of_commute
        (Setup.Campbell.blockU_le_self_of_isShort2 (hshortc t ht))
        (fun x hx y hy => hcomm' t ht t' ht' (Ne.symm heq) x hx y hy)
  have hKeq : K = ⨆ t : TH, conjByElt (t : G) K₁ := by
    rw [hK, cfg.prod]
    exact iSup_subtype'
  have hKiU : ∀ t ∈ TH, conjByElt t K₁ ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht x hx
    refine C58.mem_normalizer_iSup fun L => C58.mem_normalizer_iSup fun hL => ?_
    obtain ⟨t', ht', rfl⟩ := hL
    exact hKjU t' ht' t ht hx
  have hK₁K : K₁ ≤ K := by
    have := hleK 1 (one_mem TH)
    rwa [burnsideC5h_c54_conjByElt_one] at this
  have hUconj : ∀ t ∈ TH, ∀ y ∈ blockU K₁, t * y * t⁻¹ ∈ U := by
    intro t ht y hy
    have h1 : t * y * t⁻¹ ∈ blockU (conjByElt t K₁) := by
      have e : conjByElt t K₁ = conjSubgroup K₁ t⁻¹ := by
        unfold conjSubgroup conjByElt; rw [inv_inv]
      rw [e, ← Setup.Campbell.conjSubgroup_blockU, mem_conjSubgroup_iff]
      simpa [mul_assoc] using hy
    have hle : blockU (conjByElt t K₁) ≤ U :=
      le_iSup₂_of_le (f := fun (L : Subgroup G) (_ : L ∈ conjSubgroupsBy TH K₁) => blockU L)
        (conjByElt t K₁) (hconjmem t ht) le_rfl
    exact hle h1
  have hKQ : ∀ t ∈ TH, K ≤ Subgroup.normalizer (blockQ (conjByElt t K₁) : Set G) := by
    intro t ht
    rw [hKeq]
    exact iSup_le fun t' => hKjQ t ht t' t'.2
  apply le_antisymm
  ·
    rw [Subgroup.commutator_le]
    intro p hp k hk
    have hpN : ∀ t ∈ TH, t⁻¹ * p * t ∈ pCoreOf 2 K := by
      intro t ht
      have htN : t⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        inv_mem (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hHK (hTHH ht)))
      have := (Subgroup.mem_normalizer_iff.mp htN p).mp hp
      simpa using this
    rw [hKeq] at hk
    refine (Subgroup.iSup_induction (fun t : TH => conjByElt (t : G) K₁)
      (C := fun k => k ∈ Subgroup.normalizer (U : Set G) ∧ ⁅p, k⁆ ∈ U) hk ?_ ?_ ?_).2
    · rintro ⟨t, ht⟩ x hx
      refine ⟨hKiU t ht hx, ?_⟩
      have hx' : t⁻¹ * x * t ∈ K₁ := mem_conjByElt.mp hx
      have hHN : K ≤ Subgroup.normalizer ((K₁ ⊔ L' : Subgroup G) : Set G) := by
        rw [hjoin]; exact Subgroup.le_normalizer
      have hc := C1.commutator_mem_blockU_double hshort (L' := L') hcomm hK₁K hHN (hpN t ht) hx'
      have e : ⁅p, x⁆ = t * ((t⁻¹ * p * t) * (t⁻¹ * x * t) * (t⁻¹ * p * t)⁻¹ * (t⁻¹ * x * t)⁻¹) *
          t⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hUconj t ht _ hc
    · exact ⟨one_mem _, by simp⟩
    · rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
      refine ⟨mul_mem hxN hyN, ?_⟩
      have e : ⁅p, x * y⁆ = ⁅p, x⁆ * (x * ⁅p, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp hxN _).mp hy)
  · refine iSup₂_le fun Ki hKi => ?_
    obtain ⟨t, ht, rfl⟩ := hKi
    have hQ : blockQ (conjByElt t K₁) ≤ pCoreOf 2 K :=
      C1.le_pCoreOf_of_normalized ((C1.blockQ_le _).trans (hleK t ht)) (hKQ t ht)
        (C1.blockQ_isPGroup _)
    exact Subgroup.commutator_mono hQ (hleK t ht)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5h_c54_four_second (h111 : C_1_11) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) :
    R ⊓ Subgroup.centralizer
        ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) =
      pCoreOf 2 (oTwoUpper H ⊔ R) := by
  classical
  have hyp1 := hset.hyp1
  have cfg := hset.config
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hRN : R ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    (hyp1.R_le.trans hyp1.sylow.1).trans hHK
  have hRX : IsSylowTwoOf R (oTwoUpper H ⊔ R) := by
    have := hyp1.sylow_R
    rwa [sup_comm] at this
  have hprod : ((oTwoUpper H ⊔ R : Subgroup G) : Set G) = (oTwoUpper H : Set G) * (R : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRN)
  let B : Finset (Subgroup G) := (Set.toFinite (conjSubgroupsBy TH K₁)).toFinset
  have hmemB : ∀ L, L ∈ B ↔ L ∈ conjSubgroupsBy TH K₁ := fun L => Set.Finite.mem_toFinset _
  have hcent : IsCentralProductOfBlocks (oTwoUpper H ⊔ R) (oTwoUpper H) := by
    refine ⟨B, fun L hL => burnsideC5h_c54_isBlock2 hset ((hmemB L).1 hL), ?_, ?_⟩
    · intro L hL L' hL' hne
      obtain ⟨t, ht, rfl⟩ := (hmemB L).1 hL
      obtain ⟨t', ht', rfl⟩ := (hmemB L').1 hL'
      exact cfg.commute t ht t' ht' hne
    · apply le_antisymm
      · rw [cfg.prod]
        refine iSup₂_le fun t ht => ?_
        exact le_iSup₂_of_le (f := fun (L : Subgroup G) (_ : L ∈ B) => L) (conjByElt t K₁)
          ((hmemB _).2 ⟨t, ht, rfl⟩) le_rfl
      · exact iSup₂_le fun L hL => burnsideC5h_c54_conj_le cfg ((hmemB L).1 hL)
  have hX := h111 G (oTwoUpper H ⊔ R) (oTwoUpper H) R hcent hRX hprod
  rw [burnsideC5h_c54_commutator_eq hset] at hX
  have hP : pCoreOf 2 (oTwoUpper H ⊔ R) ≤ R := B6.pCoreOf_two_le_of_isSylowTwoOf hRX
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · have : g ∈ (oTwoUpper H ⊔ R) ⊓ Subgroup.centralizer
        ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) := ⟨(le_sup_right : R ≤ oTwoUpper H ⊔ R) hg.1, hg.2⟩
    rwa [hX] at this
  · have h1 : g ∈ (oTwoUpper H ⊔ R) ⊓ Subgroup.centralizer
        ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) := by
      rw [hX]; exact hg
    exact ⟨hP hg, h1.2⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_le_of_lt {G : Type} [Group G] [Finite G] {H T N X : Subgroup G}
    (hN : CFSG.Quasithin.IsUniqueMaxOver H T N) (hTX : T ≤ X) (hXH : X < H) : X ≤ N := by
  obtain ⟨N', hN', hXN'⟩ := exists_isMaxSubgroupIn hXH
  have h := (isUniqueMaxOver_iff.mp hN).2.2 N' hN' (hTX.trans hXN')
  rw [h] at hXN'
  exact hXN'

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_sup_eq {G : Type} [Group G] [Finite G] {H TH : Subgroup G}
    (hT : IsSylowTwoOf TH H) : oTwoUpper H ⊔ TH = H := by
  rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
  exact sup_twoResidual_eq hT

theorem burnsideC5h_c53_mem_normalizer_sup {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hA, Subgroup.mem_normalizer_iff_map_conj_eq.mp hB]

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_normalizer {G : Type} [Group G] [Finite G] {H M₀ TH R : Subgroup G}
    (hH : ChC.HypC_5_1 H M₀ TH R) :
    H ≤ Subgroup.normalizer ((R ⊔ oTwoUpper H : Subgroup G) : Set G) := by
  have hTR : TH ≤ Subgroup.normalizer (R : Set G) := hH.TH_le.trans hH.R_norm
  calc H = oTwoUpper H ⊔ TH := (burnsideC5h_c53_sup_eq hH.sylow).symm
    _ ≤ _ := sup_le (le_sup_right.trans Subgroup.le_normalizer)
      (fun t ht => burnsideC5h_c53_mem_normalizer_sup (hTR ht)
        (le_normalizer_oTwoUpper H (hH.sylow.1 ht)))

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_cgs_le {G : Type} [Group G] [Finite G] {H M₀ TH R N : Subgroup G}
    (hH : ChC.HypC_5_1 H M₀ TH R) (hH2 : ChC.HypC_5_2 M₀ H R)
    (hN : CFSG.Quasithin.IsUniqueMaxOver H TH N) :
    cgsIn (R ⊔ oTwoUpper H) R ≤ N ⊓ (R ⊔ oTwoUpper H) := by
  have hXH : R ⊔ oTwoUpper H ≤ H := sup_le (hH.R_le.trans hH.sylow.1) (oTwoUpper_le H)
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hCchar => ?_
  have hM₀C : M₀ ≤ Subgroup.normalizer (C : Set G) :=
    hH.R_norm.trans (normalizer_le_normalizer_of_characteristic hCR hCchar)
  have hTC : TH ≤ H ⊓ Subgroup.normalizer (C : Set G) :=
    le_inf hH.sylow.1 (hH.TH_le.trans hM₀C)
  have hlt : H ⊓ Subgroup.normalizer (C : Set G) < H := by
    refine lt_of_le_of_ne inf_le_left fun heq => hH2 C hCR hC1 ?_
    exact sup_le hM₀C (inf_eq_left.mp heq)
  have hle := burnsideC5h_c53_le_of_lt hN hTC hlt
  exact fun x hx => ⟨hle ⟨hXH hx.1, hx.2⟩, hx.1⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_exists_block (h129 : C_1_29) {G : Type} [Group G] [Finite G]
    {H M₀ TH R N : Subgroup G} (hH : ChC.HypC_5_1 H M₀ TH R) (hH2 : ChC.HypC_5_2 M₀ H R)
    (hN : CFSG.Quasithin.IsUniqueMaxOver H TH N) :
    ∃ L : Subgroup G, IsChi0Block (R ⊔ oTwoUpper H) L ∧ ⁅L, thompsonJ R⁆ = L ∧ ¬ L ≤ N := by
  have hXH : R ⊔ oTwoUpper H ≤ H := sup_le (hH.R_le.trans hH.sylow.1) (oTwoUpper_le H)
  have hHX := burnsideC5h_c53_normalizer hH
  obtain ⟨hNmax, hTN, -⟩ := isUniqueMaxOver_iff.mp hN
  have hXN : ¬ R ⊔ oTwoUpper H ≤ N := by
    intro h
    have hHN : H ≤ N := by
      rw [← burnsideC5h_c53_sup_eq hH.sylow]
      exact sup_le (le_sup_right.trans h) hTN
    exact absurd hNmax.1 (not_lt_of_ge hHN)
  have key := h129 G (R ⊔ oTwoUpper H) R (N ⊓ (R ⊔ oTwoUpper H))
    (A4.charTwo_of_normal hXH hHX hH.charTwo) hH.sylow_R (hH.sqtk.mono hXH)
    (burnsideC5h_c53_cgs_le hH hH2 hN) inf_le_right
  rcases key with h0 | ⟨L, hL, -, hJ, hset⟩ | ⟨L₁, L₂, hL₁, -, hJ₁, hL₂, -, hJ₂, hset⟩
  · exact absurd (h0.le.trans inf_le_left) hXN
  · refine ⟨L, hL, hJ, fun hLN => hXN ?_⟩
    intro x hx
    have hx' : x ∈ ((R ⊔ oTwoUpper H : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨m, hm, l, hl, rfl⟩ := Set.mem_mul.mp hx'
    exact N.mul_mem hm.1 (hLN hl)
  · by_cases h1 : L₁ ≤ N
    · by_cases h2 : L₂ ≤ N
      · exfalso
        apply hXN
        intro x hx
        have hx' : x ∈ ((R ⊔ oTwoUpper H : Subgroup G) : Set G) := hx
        rw [hset] at hx'
        obtain ⟨a, ha, l₂, hl₂, rfl⟩ := Set.mem_mul.mp hx'
        obtain ⟨m, hm, l₁, hl₁, rfl⟩ := Set.mem_mul.mp ha
        exact N.mul_mem (N.mul_mem hm.1 (h1 hl₁)) (h2 hl₂)
      · exact ⟨L₂, hL₂, hJ₂, h2⟩
    · exact ⟨L₁, hL₁, hJ₁, h1⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_le_normalizer_iSup {G : Type} [Group G] (A T : Subgroup G) :
    T ≤ Subgroup.normalizer ((⨆ t ∈ T, conjByElt t A : Subgroup G) : Set G) := by
  set Y := ⨆ t ∈ T, conjByElt t A with hY
  have hmem : ∀ s ∈ T, ∀ x ∈ Y, s * x * s⁻¹ ∈ Y := by
    intro s hs x hx
    have h1 : Y.map (MulAut.conj s).toMonoidHom ≤ Y := by
      rw [hY, Subgroup.map_iSup]
      refine iSup_le fun t => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun ht => ?_
      have h2 : (conjByElt t A).map (MulAut.conj s).toMonoidHom = conjByElt (s * t) A :=
        (C2Eleven.conjByElt_mul s t A).symm
      rw [h2]
      exact le_iSup₂_of_le (s * t) (T.mul_mem hs ht) le_rfl
    exact h1 ⟨x, hx, by simp⟩
  intro s hs
  exact B6.mem_normalizer_of_forall_mem (hmem s hs)
    (fun x hx => by simpa using hmem s⁻¹ (T.inv_mem hs) x hx)

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_card_conjByElt {G : Type} [Group G] (a : G) (L : Subgroup G) :
    Nat.card (conjByElt a L) = Nat.card L :=
  Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_three_dvd {G : Type} [Group G] {X L : Subgroup G}
    (h : IsChi0Block X L) : 3 ∣ Nat.card L :=
  C1GN.three_dvd_card_of_isChiBlock ⟨h.1, by
    rcases h.2 with hl | h3 | h5
    · exact Or.inl hl
    · exact Or.inr ⟨3, by decide, le_rfl, h3⟩
    · exact Or.inr ⟨5, by decide, by norm_num, h5⟩⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_blockConfig {G : Type} [Group G] [Finite G] {H M₀ TH R N L : Subgroup G}
    (hH : ChC.HypC_5_1 H M₀ TH R) (hN : CFSG.Quasithin.IsUniqueMaxOver H TH N)
    (hL : IsChi0Block (R ⊔ oTwoUpper H) L) (hJ : ⁅L, thompsonJ R⁆ = L) (hLN : ¬ L ≤ N) :
    ChC.BlockConfig H TH R L := by
  have hTHH : TH ≤ H := hH.sylow.1
  have hTH2 : IsPGroup 2 TH := hH.sylow.2.1
  have hXH : R ⊔ oTwoUpper H ≤ H := sup_le (hH.R_le.trans hTHH) (oTwoUpper_le H)
  have hHX := burnsideC5h_c53_normalizer hH
  have hLH : L ≤ H := hL.1.2.1.trans hXH
  have hB : IsBlock2 H L :=
    ⟨hL.1.1, hLH, C58.isSubnormal_subgroupOf_trans hL.1.2.1 hL.1.2.2
      (C58.isSubnormal_subgroupOf_of_le_normalizer hXH hHX)⟩
  have hLK : L ≤ oTwoUpper H :=
    calc L = oTwoUpper L := C1Pack.isShort2_eq_oTwoUpper hL.1.1
      _ ≤ oTwoUpper H := oTwoUpper_mono hLH
  have hconjK : ∀ t ∈ H, conjByElt t L ≤ oTwoUpper H := fun t ht =>
    calc conjByElt t L ≤ conjByElt t (oTwoUpper H) := Subgroup.map_mono hLK
      _ = oTwoUpper H := C2Eleven.mem_normalizer_iff_conjByElt.mp (le_normalizer_oTwoUpper H ht)
  have hBt : ∀ t ∈ TH, IsBlock2 H (conjByElt t L) := fun t ht =>
    IsBlock2.conjByElt_of_mem hB (hTHH ht)
  have hcomm : ∀ a ∈ TH, ∀ b ∈ TH, conjByElt a L ≠ conjByElt b L →
      ⁅conjByElt a L, conjByElt b L⁆ = ⊥ := fun a ha b hb hne =>
    distinctBlocksCommuteStatement H _ _ hH.charTwo (hBt a ha) (hBt b hb) hne
  refine ⟨⟨hB, hL.2⟩, hJ, ?_, ?_, ?_⟩
  · apply le_antisymm
    · set Y := ⨆ t ∈ TH, conjByElt t L with hY
      have hLY : L ≤ Y := le_iSup₂_of_le (1 : G) TH.one_mem (by rw [C2Eleven.conjByElt_one])
      have hYH : Y ≤ H := iSup₂_le fun t ht => (hconjK t (hTHH ht)).trans (oTwoUpper_le H)
      have hTY : TH ≤ Subgroup.normalizer (Y : Set G) := burnsideC5h_c53_le_normalizer_iSup L TH
      have hYT : H ≤ Y ⊔ TH := by
        by_contra hne
        have hlt : Y ⊔ TH < H := lt_of_le_of_ne (sup_le hYH hTHH) fun h => hne h.ge
        exact hLN ((hLY.trans le_sup_left).trans
          (burnsideC5h_c53_le_of_lt hN le_sup_right hlt))
      exact C58.oTwoUpper_le_of_le_sup hYT hTH2 hTY
    · exact iSup₂_le fun t ht => hconjK t (hTHH ht)
  · intro t ht t' ht' t'' ht''
    by_contra hcon
    push Not at hcon
    obtain ⟨h12, h13, h23⟩ := hcon
    have h3 : ∀ a : G, 3 ∣ Nat.card (conjByElt a L) := fun a => by
      rw [burnsideC5h_c53_card_conjByElt]
      exact burnsideC5h_c53_three_dvd hL
    exact C1GN.three_blocks_false (C1GN.isSQTKTC_iff_sqtkGroup.mpr hH.sqtk)
      (hBt t ht).2.1 (hBt t' ht').2.1 (hBt t'' ht'').2.1
      ⟨(hBt t ht).1.2.1, (hBt t' ht').1.2.1, (hBt t'' ht'').1.2.1⟩ ⟨h3 t, h3 t', h3 t''⟩
      h12 h13 h23 ⟨hcomm t ht t' ht' h12, hcomm t ht t'' ht'' h13, hcomm t' ht' t'' ht'' h23⟩
  · intro t ht t' ht' hne
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm t ht t' ht' hne)

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_c53_main (h129 : C_1_29) {G : Type} [Group G] [Finite G]
    {H M₀ TH R : Subgroup G} (hH : ChC.HypC_5_1 H M₀ TH R) (hH2 : ChC.HypC_5_2 M₀ H R) :
    ∃ K₁ : Subgroup G, ChC.BlockConfig H TH R K₁ := by
  obtain ⟨N, hN⟩ := hH.unique_max
  obtain ⟨L, hL, hJ, hLN⟩ := burnsideC5h_c53_exists_block h129 hH hH2 hN
  exact ⟨L, burnsideC5h_c53_blockConfig hH hN hL hJ hLN⟩

section

theorem as_C_5_3
    : C_5_3 := by
  intro G _ _ H M₀ TH R hH hH2
  exact burnsideC5h_c53_main as_C_1_29 hH hH2

end

@[expose] def burnsideC5h_p1_UMaxIn {G : Type*} [Group G] (K P : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B < K ∧ P ≤ B ∧ ∀ Y : Subgroup G, P ≤ Y → Y < K → Y ≤ B

theorem burnsideC5h_p1_umaxIn_orderIso {G : Type*} [Group G] (e : Subgroup G ≃o Subgroup G)
    {K P : Subgroup G} (h : burnsideC5h_p1_UMaxIn K P) :
    burnsideC5h_p1_UMaxIn (e K) (e P) := by
  obtain ⟨B, hBK, hPB, hmax⟩ := h
  refine ⟨e B, e.strictMono hBK, e.monotone hPB, fun Y hPY hYK => ?_⟩
  have h1 : P ≤ e.symm Y := e.le_symm_apply.mpr hPY
  have h2 : e.symm Y < K := by
    have := e.symm.strictMono hYK
    rwa [OrderIso.symm_apply_apply] at this
  exact e.symm_apply_le.mp (hmax _ h1 h2)

theorem burnsideC5h_p1_umaxIn_conjByElt {G : Type*} [Group G] (t : G) {K P : Subgroup G}
    (h : burnsideC5h_p1_UMaxIn K P) :
    burnsideC5h_p1_UMaxIn (CFSG.Quasithin.conjByElt t K) (CFSG.Quasithin.conjByElt t P) :=
  burnsideC5h_p1_umaxIn_orderIso (MulEquiv.mapSubgroup (MulAut.conj t)) h

theorem burnsideC5h_p1_umaxIn_top_orderIso {Γ : Type*} [Group Γ] (e : Subgroup Γ ≃o Subgroup Γ)
    {P : Subgroup Γ} (h : burnsideC5h_p1_UMaxIn ⊤ P) : burnsideC5h_p1_UMaxIn ⊤ (e P) := by
  have := burnsideC5h_p1_umaxIn_orderIso e h
  rwa [map_top] at this

theorem burnsideC5h_p1_umax_of_surjective {Γ Q : Type*} [Group Γ] [Group Q] (π : Γ →* Q)
    (hπ : Function.Surjective π) {S : Subgroup Γ} (hker : π.ker ≤ S)
    (h : burnsideC5h_p1_UMaxIn ⊤ (S.map π)) : burnsideC5h_p1_UMaxIn ⊤ S := by
  obtain ⟨B, hB, hSB, hmax⟩ := h
  refine ⟨B.comap π, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne le_top fun h => hB.ne ?_
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := hπ q
    have : g ∈ B.comap π := h ▸ Subgroup.mem_top g
    exact this
  · intro s hs
    exact hSB ⟨s, hs, rfl⟩
  · intro Y hSY hY
    have hY' : Y.map π < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hY.ne ?_
      rw [eq_top_iff]
      intro g _
      have h1 : π g ∈ Y.map π := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyg⟩ := h1
      have h2 : y⁻¹ * g ∈ π.ker := by simp [MonoidHom.mem_ker, hyg]
      have h3 := hSY (hker h2)
      simpa using Y.mul_mem hy h3
    have h4 := hmax _ (Subgroup.map_mono hSY) hY'
    intro y hy
    exact h4 ⟨y, hy, rfl⟩

theorem burnsideC5h_p1_umaxIn_of_subtype {G : Type*} [Group G] {K P : Subgroup G} (hPK : P ≤ K)
    (h : burnsideC5h_p1_UMaxIn (⊤ : Subgroup ↥K) (P.subgroupOf K)) :
    burnsideC5h_p1_UMaxIn K P := by
  obtain ⟨B', hB', hPB', hmax⟩ := h
  refine ⟨B'.map K.subtype, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le B') fun h => hB'.ne ?_
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ B'.map K.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hPB'
  · intro Y hPY hYK
    have hY' : Y.subgroupOf K < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hYK.ne ?_
      exact le_antisymm hYK.le (Subgroup.subgroupOf_eq_top.mp h)
    have hPY' : P.subgroupOf K ≤ Y.subgroupOf K := fun x hx => hPY hx
    have h4 := hmax _ hPY' hY'
    intro y hy
    exact ⟨⟨y, hYK.le hy⟩, h4 hy, rfl⟩

theorem burnsideC5h_p1_umax_alt3 (S : Subgroup ↥(alternatingGroup (Fin 3))) (hS : IsPGroup 2 S) :
    burnsideC5h_p1_UMaxIn ⊤ S := by
  have hcard : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  haveI : Fact (Nat.Prime (Nat.card ↥(alternatingGroup (Fin 3)))) :=
    ⟨by rw [hcard]; exact Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSbot : S = ⊥ := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hd : Nat.card S ∣ Nat.card ↥(alternatingGroup (Fin 3)) :=
      Subgroup.card_subgroup_dvd_card S
    rw [hcard, hk] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have h23 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hd
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq S hk
  subst hSbot
  refine ⟨⊥, ?_, le_rfl, fun Y _ hY => ?_⟩
  · refine lt_of_le_of_ne bot_le fun h => ?_
    have h1 : Nat.card (⊥ : Subgroup ↥(alternatingGroup (Fin 3))) = Nat.card (⊤ : Subgroup ↥(alternatingGroup (Fin 3))) := by
      rw [h]
    rw [Subgroup.card_bot, Subgroup.card_top, hcard] at h1
    omega
  · exact ((Subgroup.eq_bot_or_eq_top_of_prime_card Y).resolve_right hY.ne).le

section SL2

variable {F : Type} [Field F]

@[expose] def burnsideC5h_p1_sl (a b c d : F) (h : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem burnsideC5h_p1_coe_sl (a b c d : F) (h : a * d - b * c = 1) :
    (burnsideC5h_p1_sl a b c d h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

@[expose] def burnsideC5h_p1_utri (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  burnsideC5h_p1_sl 1 t 0 1 (by simp)

@[expose] def burnsideC5h_p1_ltri (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  burnsideC5h_p1_sl 1 0 t 1 (by simp)

theorem burnsideC5h_p1_coe_utri (t : F) :
    (burnsideC5h_p1_utri t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem burnsideC5h_p1_coe_ltri (t : F) :
    (burnsideC5h_p1_ltri t : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := rfl

theorem burnsideC5h_p1_utri_mul (s t : F) :
    burnsideC5h_p1_utri s * burnsideC5h_p1_utri t = burnsideC5h_p1_utri (s + t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem burnsideC5h_p1_utri_zero : burnsideC5h_p1_utri (0 : F) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [burnsideC5h_p1_coe_utri]

@[expose] def burnsideC5h_p1_utriHom (F : Type) [Field F] :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun t := burnsideC5h_p1_utri (Multiplicative.toAdd t)
  map_one' := burnsideC5h_p1_utri_zero
  map_mul' s t := by
    simp only [toAdd_mul]
    exact (burnsideC5h_p1_utri_mul _ _).symm

theorem burnsideC5h_p1_utriHom_apply (t : Multiplicative F) :
    burnsideC5h_p1_utriHom F t = burnsideC5h_p1_utri (Multiplicative.toAdd t) := rfl

theorem burnsideC5h_p1_utriHom_injective : Function.Injective (burnsideC5h_p1_utriHom F) := by
  intro s t h
  rw [burnsideC5h_p1_utriHom_apply, burnsideC5h_p1_utriHom_apply] at h
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [burnsideC5h_p1_coe_utri] using h1

@[expose] def burnsideC5h_p1_U (F : Type) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (burnsideC5h_p1_utriHom F).range

@[expose] def burnsideC5h_p1_B (F : Type) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha]

theorem burnsideC5h_p1_utri_mem_U (t : F) : burnsideC5h_p1_utri t ∈ burnsideC5h_p1_U F :=
  ⟨Multiplicative.ofAdd t, rfl⟩

theorem burnsideC5h_p1_U_le_B : burnsideC5h_p1_U F ≤ burnsideC5h_p1_B F := by
  rintro _ ⟨t, rfl⟩
  show (burnsideC5h_p1_utri (Multiplicative.toAdd t) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp [burnsideC5h_p1_coe_utri]

theorem burnsideC5h_p1_B_lt_top : burnsideC5h_p1_B F < ⊤ := by
  refine lt_of_le_of_ne le_top fun h => ?_
  have h1 : burnsideC5h_p1_ltri (1 : F) ∈ burnsideC5h_p1_B F := h ▸ Subgroup.mem_top _
  have h2 : (burnsideC5h_p1_ltri (1 : F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h1
  simp [burnsideC5h_p1_coe_ltri] at h2

theorem burnsideC5h_p1_sl2_eq_top {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hU : ∀ t : F, burnsideC5h_p1_utri t ∈ Y) (hL : ∀ t : F, burnsideC5h_p1_ltri t ∈ Y) :
    Y = ⊤ := by
  have key : ∀ {a b c d : F} (hdet : a * d - b * c = 1), c ≠ 0 →
      burnsideC5h_p1_sl a b c d hdet ∈ Y := by
    intro a b c d hdet hc
    have hb : b = (a * d - 1) / c := by
      field_simp
      linear_combination (-1 : F) * hdet
    subst hb
    have h : burnsideC5h_p1_sl a ((a * d - 1) / c) c d hdet =
        burnsideC5h_p1_utri ((a - 1) / c) * burnsideC5h_p1_ltri c *
          burnsideC5h_p1_utri ((d - 1) / c) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri,
          burnsideC5h_p1_coe_ltri, burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> ring
    rw [h]
    exact Y.mul_mem (Y.mul_mem (hU _) (hL _)) (hU _)
  rw [eq_top_iff]
  intro g _
  refine Matrix.SpecialLinearGroup.fin_two_induction (fun g => g ∈ Y) ?_ g
  intro a b c d hdet
  change burnsideC5h_p1_sl a b c d hdet ∈ Y
  by_cases hc : c = 0
  · subst hc
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hdet
    have hdet' : a * (b + d) - b * a = 1 := by linear_combination hdet
    have h1 := key hdet' ha
    have h : burnsideC5h_p1_sl a b 0 d hdet =
        burnsideC5h_p1_ltri (-1) * burnsideC5h_p1_sl a b a (b + d) hdet' := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_ltri,
          burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two]
    rw [h]
    exact Y.mul_mem (hL _) h1
  · exact key hdet hc

theorem burnsideC5h_p1_sl2_ltri_mem {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hU : ∀ t : F, burnsideC5h_p1_utri t ∈ Y) {a b c d : F} (hdet : a * d - b * c = 1)
    (hc : c ≠ 0) (hy : burnsideC5h_p1_sl a b c d hdet ∈ Y) :
    ∀ z : F, burnsideC5h_p1_ltri z ∈ Y := by
  have hb : b = (a * d - 1) / c := by
    field_simp
    linear_combination (-1 : F) * hdet
  subst hb
  have hwdet : (0 : F) * 0 - (-c⁻¹) * c = 1 := by field_simp; ring
  have hwY : burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet ∈ Y := by
    have h : burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet =
        burnsideC5h_p1_utri (-a / c) * burnsideC5h_p1_sl a ((a * d - 1) / c) c d hdet *
          burnsideC5h_p1_utri (-d / c) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri,
          burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> ring
    rw [h]
    exact Y.mul_mem (Y.mul_mem (hU _) hy) (hU _)
  intro z
  have hcomm : burnsideC5h_p1_ltri z * burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet =
      burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet * burnsideC5h_p1_utri (-z / c ^ 2) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri,
        burnsideC5h_p1_coe_ltri, burnsideC5h_p1_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring
  have h2 : burnsideC5h_p1_ltri z = burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet *
      burnsideC5h_p1_utri (-z / c ^ 2) * (burnsideC5h_p1_sl 0 (-c⁻¹) c 0 hwdet)⁻¹ :=
    eq_mul_inv_of_mul_eq hcomm
  rw [h2]
  exact Y.mul_mem (Y.mul_mem hwY (hU _)) (Y.inv_mem hwY)

theorem burnsideC5h_p1_sl2_eq_top_of_not_le {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hUY : burnsideC5h_p1_U F ≤ Y) (hY : ¬ Y ≤ burnsideC5h_p1_B F) : Y = ⊤ := by
  have hU : ∀ t : F, burnsideC5h_p1_utri t ∈ Y := fun t => hUY (burnsideC5h_p1_utri_mem_U t)
  obtain ⟨y, hyY, hyB⟩ := SetLike.not_le_iff_exists.mp hY
  refine burnsideC5h_p1_sl2_eq_top hU ?_
  revert hyY hyB
  refine Matrix.SpecialLinearGroup.fin_two_induction
    (fun y => y ∈ Y → y ∉ burnsideC5h_p1_B F → ∀ z : F, burnsideC5h_p1_ltri z ∈ Y) ?_ y
  intro a b c d hdet hy hyB
  have hc : c ≠ 0 := fun h => hyB (by
    show (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [h])
  exact burnsideC5h_p1_sl2_ltri_mem hU hdet hc hy

theorem burnsideC5h_p1_umax_U : burnsideC5h_p1_UMaxIn ⊤ (burnsideC5h_p1_U F) :=
  ⟨burnsideC5h_p1_B F, burnsideC5h_p1_B_lt_top, burnsideC5h_p1_U_le_B, fun Y hUY hY => by
    by_contra hYB
    exact hY.ne (burnsideC5h_p1_sl2_eq_top_of_not_le hUY hYB)⟩

theorem burnsideC5h_p1_sl2_card (F : Type) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := F)] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 := ⟨Fintype.card F - 2, by omega⟩
  rw [hm] at h ⊢
  have e1 : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (m + 2) ^ 2 - (m + 2) = (m + 2) * (m + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : m + 2 - 1 = m + 1 := by omega
  rw [e1, e2, e3] at h
  rw [e1]
  have h' : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (m + 1) =
      ((m + 2) * ((m + 1) * (m + 3))) * (m + 1) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h'

theorem burnsideC5h_p1_isSylow_U [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) :
    CFSG.QuasithinUnique.IsSylowTwoOf (burnsideC5h_p1_U F) ⊤ := by
  have hcardU : Nat.card (burnsideC5h_p1_U F) = Fintype.card F := by
    have e := MonoidHom.ofInjective (burnsideC5h_p1_utriHom_injective (F := F))
    calc Nat.card (burnsideC5h_p1_U F) = Nat.card (Multiplicative F) :=
          Nat.card_congr e.toEquiv.symm
      _ = Nat.card F := Nat.card_congr Multiplicative.toAdd
      _ = Fintype.card F := Nat.card_eq_fintype_card
  refine ⟨le_top, IsPGroup.of_card (n := n) (by rw [hcardU, hF]), ?_⟩
  have hmul := Subgroup.card_mul_index (burnsideC5h_p1_U F)
  rw [hcardU, burnsideC5h_p1_sl2_card] at hmul
  have hq0 : 0 < Fintype.card F := Fintype.card_pos
  have hidx : (burnsideC5h_p1_U F).index = Fintype.card F ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left hq0 hmul
  change ¬ 2 ∣ (burnsideC5h_p1_U F).relIndex ⊤
  rw [Subgroup.relIndex_top_right, hidx, hF]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have h3 : 0 < (2 ^ n) ^ 2 := by positivity
  omega

theorem burnsideC5h_p1_umax_sl2 [Fintype F] {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : burnsideC5h_p1_UMaxIn ⊤ S := by
  have hU := burnsideC5h_p1_isSylow_U (F := F) hn hF
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    ⟨le_top, hS, by
      change ¬ 2 ∣ S.relIndex ⊤
      rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hU hSyl
  rw [hg]
  exact burnsideC5h_p1_umaxIn_top_orderIso _ burnsideC5h_p1_umax_U

end SL2

section Alt5

open Equiv in
@[expose] def burnsideC5h_p1_Vset : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem burnsideC5h_p1_Vset_mul :
    ∀ x ∈ burnsideC5h_p1_Vset, ∀ y ∈ burnsideC5h_p1_Vset, x * y ∈ burnsideC5h_p1_Vset := by
  simp only [burnsideC5h_p1_Vset, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;> decide

theorem burnsideC5h_p1_Vset_inv : ∀ x ∈ burnsideC5h_p1_Vset, x⁻¹ ∈ burnsideC5h_p1_Vset := by
  simp only [burnsideC5h_p1_Vset, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem burnsideC5h_p1_Vset_one : (1 : Equiv.Perm (Fin 5)) ∈ burnsideC5h_p1_Vset := by
  simp [burnsideC5h_p1_Vset]

theorem burnsideC5h_p1_Vset_fix : ∀ x ∈ burnsideC5h_p1_Vset, x 4 = 4 := by
  simp only [burnsideC5h_p1_Vset, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem burnsideC5h_p1_Vset_sign : ∀ x ∈ burnsideC5h_p1_Vset, Equiv.Perm.sign x = 1 := by
  simp only [burnsideC5h_p1_Vset, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl) <;> simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem burnsideC5h_p1_Vset_trans :
    ∀ q j : Fin 5, q ≠ 4 → j ≠ 4 → ∃ v ∈ burnsideC5h_p1_Vset, v q = j := by
  unfold burnsideC5h_p1_Vset
  decide

theorem burnsideC5h_p1_Vset_card : burnsideC5h_p1_Vset.card = 4 := by
  unfold burnsideC5h_p1_Vset
  decide

@[expose] def burnsideC5h_p1_V : Subgroup ↥(alternatingGroup (Fin 5)) where
  carrier := {x | (x : Equiv.Perm (Fin 5)) ∈ burnsideC5h_p1_Vset}
  mul_mem' := fun {x y} hx hy => burnsideC5h_p1_Vset_mul _ hx _ hy
  one_mem' := burnsideC5h_p1_Vset_one
  inv_mem' := fun {x} hx => burnsideC5h_p1_Vset_inv _ hx

theorem burnsideC5h_p1_Vset_mem_alt {v : Equiv.Perm (Fin 5)} (hv : v ∈ burnsideC5h_p1_Vset) :
    v ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (burnsideC5h_p1_Vset_sign v hv)

theorem burnsideC5h_p1_V_card : Nat.card burnsideC5h_p1_V = 4 := by
  have h1 : Nat.card burnsideC5h_p1_V = (burnsideC5h_p1_V : Set ↥(alternatingGroup (Fin 5))).ncard :=
    Nat.card_coe_set_eq _
  have h2 : (burnsideC5h_p1_V : Set ↥(alternatingGroup (Fin 5))) =
      Subtype.val ⁻¹' (burnsideC5h_p1_Vset : Set (Equiv.Perm (Fin 5))) := rfl
  rw [h1, h2, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective, Set.ncard_coe_finset,
    burnsideC5h_p1_Vset_card]
  intro v hv
  exact ⟨⟨v, burnsideC5h_p1_Vset_mem_alt hv⟩, rfl⟩

theorem burnsideC5h_p1_alt5_card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem burnsideC5h_p1_alt5_smul (g : ↥(alternatingGroup (Fin 5))) (x : Fin 5) :
    g • x = (g : Equiv.Perm (Fin 5)) x := rfl

theorem burnsideC5h_p1_alt5_five_dvd {Y : Subgroup ↥(alternatingGroup (Fin 5))}
    (hVY : burnsideC5h_p1_V ≤ Y)
    (hY : ¬ Y ≤ MulAction.stabilizer ↥(alternatingGroup (Fin 5)) (4 : Fin 5)) :
    5 ∣ Nat.card Y := by
  obtain ⟨y, hyY, hy4⟩ := SetLike.not_le_iff_exists.mp hY
  have hy4' : (y : Equiv.Perm (Fin 5)) 4 ≠ 4 := fun h =>
    hy4 (by rw [MulAction.mem_stabilizer_iff, burnsideC5h_p1_alt5_smul]; exact h)
  have horbit : MulAction.orbit ↥Y (4 : Fin 5) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j
    by_cases hj : j = 4
    · rw [hj]
      exact MulAction.mem_orbit_self 4
    · obtain ⟨v, hv, hvj⟩ := burnsideC5h_p1_Vset_trans ((y : Equiv.Perm (Fin 5)) 4) j hy4' hj
      have hvA : v ∈ alternatingGroup (Fin 5) := burnsideC5h_p1_Vset_mem_alt hv
      have hvY : (⟨v, hvA⟩ : ↥(alternatingGroup (Fin 5))) ∈ Y := hVY hv
      refine ⟨⟨⟨v, hvA⟩, hvY⟩ * ⟨y, hyY⟩, ?_⟩
      show ((⟨v, hvA⟩ * y : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) 4 = j
      show v ((y : Equiv.Perm (Fin 5)) 4) = j
      exact hvj
  have h5 : (MulAction.orbit ↥Y (4 : Fin 5)).ncard = 5 := by
    rw [horbit, Set.ncard_univ]
    simp
  have := Subgroup.index_dvd_card (MulAction.stabilizer ↥Y (4 : Fin 5))
  rwa [MulAction.index_stabilizer, h5] at this

theorem burnsideC5h_p1_alt5_eq_top_of_index_le {Y : Subgroup ↥(alternatingGroup (Fin 5))}
    (h : Y.index ≤ 4) : Y = ⊤ := by
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  let φ : ↥(alternatingGroup (Fin 5)) →* Equiv.Perm (↥(alternatingGroup (Fin 5)) ⧸ Y) :=
    MulAction.toPermHom _ _
  rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h0 | h1
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h0
    have hle := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, burnsideC5h_p1_alt5_card] at hle
    have h4 : Nat.card (↥(alternatingGroup (Fin 5)) ⧸ Y) ≤ 4 := h
    have h5 := Nat.factorial_le h4
    have h24 : Nat.factorial 4 = 24 := by decide
    omega
  · rw [eq_top_iff]
    intro g _
    have h2 : φ g = 1 := by
      rw [← MonoidHom.mem_ker, h1]
      exact Subgroup.mem_top g
    have h3 : g • (QuotientGroup.mk 1 : ↥(alternatingGroup (Fin 5)) ⧸ Y) = QuotientGroup.mk 1 := by
      have := congrArg (fun f : Equiv.Perm (↥(alternatingGroup (Fin 5)) ⧸ Y) =>
        f (QuotientGroup.mk 1)) h2
      simpa [φ] using this
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h3
    simpa using Y.inv_mem h3

theorem burnsideC5h_p1_umax_V : burnsideC5h_p1_UMaxIn ⊤ burnsideC5h_p1_V := by
  refine ⟨MulAction.stabilizer ↥(alternatingGroup (Fin 5)) (4 : Fin 5), ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne le_top fun h => ?_
    have hg : (⟨Equiv.swap 0 4 * Equiv.swap 1 2, by
        rw [Equiv.Perm.mem_alternatingGroup]
        simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']⟩ : ↥(alternatingGroup (Fin 5))) ∈
        MulAction.stabilizer ↥(alternatingGroup (Fin 5)) (4 : Fin 5) := h ▸ Subgroup.mem_top _
    rw [MulAction.mem_stabilizer_iff, burnsideC5h_p1_alt5_smul] at hg
    revert hg
    decide
  · intro x hx
    rw [MulAction.mem_stabilizer_iff, burnsideC5h_p1_alt5_smul]
    exact burnsideC5h_p1_Vset_fix _ hx
  · intro Y hVY hY
    by_contra hYB
    have h5 := burnsideC5h_p1_alt5_five_dvd hVY hYB
    have h4 : 4 ∣ Nat.card Y := burnsideC5h_p1_V_card ▸ Subgroup.card_dvd_of_le hVY
    have h20 : 20 ∣ Nat.card Y :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 5) h4 h5
    have hmul := Subgroup.card_mul_index Y
    rw [burnsideC5h_p1_alt5_card] at hmul
    obtain ⟨k, hk⟩ := h20
    rw [hk] at hmul
    have h3 : k * Y.index = 3 := by
      have : 20 * (k * Y.index) = 20 * 3 := by rw [← mul_assoc]; exact hmul
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    have hidx : Y.index ≤ 3 := Nat.le_of_dvd (by norm_num) ⟨k, by rw [mul_comm]; exact h3.symm⟩
    exact hY.ne (burnsideC5h_p1_alt5_eq_top_of_index_le (by omega))

theorem burnsideC5h_p1_isSylow_V :
    CFSG.QuasithinUnique.IsSylowTwoOf burnsideC5h_p1_V ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 2) (by rw [burnsideC5h_p1_V_card]; norm_num), ?_⟩
  have hmul := Subgroup.card_mul_index burnsideC5h_p1_V
  rw [burnsideC5h_p1_V_card, burnsideC5h_p1_alt5_card] at hmul
  change ¬ 2 ∣ burnsideC5h_p1_V.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  omega

theorem burnsideC5h_p1_umax_alt5 {S : Subgroup ↥(alternatingGroup (Fin 5))} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : burnsideC5h_p1_UMaxIn ⊤ S := by
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    ⟨le_top, hS, by
      change ¬ 2 ∣ S.relIndex ⊤
      rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj burnsideC5h_p1_isSylow_V hSyl
  rw [hg]
  exact burnsideC5h_p1_umaxIn_top_orderIso _ burnsideC5h_p1_umax_V

end Alt5

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_p1_umaxIn_of_quotient {G Q : Type} [Group G] [Finite G] [Group Q]
    {K P : Subgroup G} (hP : IsSylowTwoOf P K) (α : ↥K →* Q) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K)
    (hQ : ∀ S : Subgroup Q, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S) :
    burnsideC5h_p1_UMaxIn K P := by
  have hPK : P ≤ K := hP.1
  have hpc : pCoreOf 2 K ≤ P := B6.pCoreOf_two_le_of_isSylowTwoOf hP
  have hkerP : α.ker ≤ P.subgroupOf K := by
    intro x hx
    rw [hker] at hx
    exact hpc ⟨x, hx, rfl⟩
  have hP2 : IsPGroup 2 ↥(P.subgroupOf K) :=
    hP.2.1.comap_of_injective K.subtype K.subtype_injective
  have hS2 : IsPGroup 2 ↥((P.subgroupOf K).map α) := hP2.map α
  have hSi : ¬ 2 ∣ ((P.subgroupOf K).map α).index := by
    rw [Subgroup.index_map, sup_eq_left.mpr hkerP, MonoidHom.range_eq_top.mpr hα,
      Subgroup.index_top, mul_one]
    exact hP.2.2
  exact burnsideC5h_p1_umaxIn_of_subtype hPK
    (burnsideC5h_p1_umax_of_surjective α hα hkerP (hQ _ hS2 hSi))

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_p1_blockMax {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hK : IsShort2 K)
    (hT : (∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 3 ∨ IsAltType K 5)
    (hP : IsSylowTwoOf P K) :
    ∃ B : Subgroup G, B < K ∧ P ≤ B ∧ ∀ Y : Subgroup G, P ≤ Y → Y < K → Y ≤ B := by
  clear hK
  rcases hT with ⟨n, hn, F, hF, hFin, hcard, α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩ |
    ⟨α, hα, hker, -⟩
  · exact burnsideC5h_p1_umaxIn_of_quotient hP α hα hker fun S hS hSi =>
      burnsideC5h_p1_umax_sl2 (F := F) (n := n) (by omega) hcard hS hSi
  · exact burnsideC5h_p1_umaxIn_of_quotient hP α hα hker fun S hS _ =>
      burnsideC5h_p1_umax_alt3 S hS
  · exact burnsideC5h_p1_umaxIn_of_quotient hP α hα hker fun S hS hSi =>
      burnsideC5h_p1_umax_alt5 hS hSi

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_conj_le {G : Type} [Group G] {H TH R K₁ : Subgroup G}
    (cfg : BlockConfig H TH R K₁) {t : G} (ht : t ∈ TH) : conjByElt t K₁ ≤ oTwoUpper H := by
  rw [cfg.prod]
  exact le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) => conjByElt t K₁) t ht

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_K_le_normalizer {G : Type} [Group G] {H TH R K₁ : Subgroup G}
    (cfg : BlockConfig H TH R K₁) {t : G} (ht : t ∈ TH) :
    oTwoUpper H ≤ Subgroup.normalizer (conjByElt t K₁ : Set G) := by
  rw [cfg.prod]
  refine iSup₂_le fun t' ht' => ?_
  by_cases h : conjByElt t' K₁ = conjByElt t K₁
  · rw [h]
    exact Subgroup.le_normalizer
  · exact (cfg.commute t' ht' t ht h).trans (Subgroup.centralizer_le_normalizer _)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_isSylow_inf {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {t : G} (ht : t ∈ TH) :
    IsSylowTwoOf (R ⊓ conjByElt t K₁) (conjByElt t K₁) := by
  have hyp1 := hset.hyp1
  have cfg := hset.config
  have hRH : R ≤ H := hyp1.R_le.trans hyp1.sylow.1
  have hRK : R ⊔ oTwoUpper H ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le (hRH.trans (le_normalizer_oTwoUpper H)) Subgroup.le_normalizer
  have h1 : IsSylowTwoOf (R ⊓ oTwoUpper H) (oTwoUpper H) :=
    B6.isSylowTwoOf_inf_normal hyp1.sylow_R le_sup_right hRK
  have hKi : conjByElt t K₁ ≤ oTwoUpper H := burnsideC5h_p1_conj_le cfg ht
  have h2 := B6.isSylowTwoOf_inf_normal h1 hKi (burnsideC5h_p1_K_le_normalizer cfg ht)
  rwa [inf_assoc, inf_eq_right.mpr hKi] at h2

open CFSG.Quasithin CFSG.QuasithinUnique in
open scoped Pointwise in
theorem burnsideC5h_p1_isSylow_sup {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hB2 : IsPGroup 2 B) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hAB : IsSylowTwoOf (A ⊓ B) A) : IsSylowTwoOf B (A ⊔ B) := by
  obtain ⟨T, hBT, hT⟩ := exists_isSylowTwoOf_of_le (le_sup_right : B ≤ A ⊔ B) hB2
  have hMA : A ⊔ B ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBA
  have hTA : IsSylowTwoOf (T ⊓ A) A := B6.isSylowTwoOf_inf_normal hT le_sup_left hMA
  have hle : A ⊓ B ≤ T ⊓ A := fun x hx => ⟨hBT hx.2, hx.1⟩
  have heq : T ⊓ A = A ⊓ B := hAB.eq_of_le hle inf_le_right (hT.2.1.to_le inf_le_left)
  have hTB : T ≤ B := by
    intro x hx
    have hxM : x ∈ B ⊔ A := by
      rw [sup_comm]
      exact hT.1 hx
    have hset : ((B ⊔ A : Subgroup G) : Set G) = (B : Set G) * (A : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B A hBA
    have hx' : x ∈ ((B ⊔ A : Subgroup G) : Set G) := hxM
    rw [hset] at hx'
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hx'
    have haT : a ∈ T := by
      have : b⁻¹ * (b * a) ∈ T := T.mul_mem (T.inv_mem (hBT hb)) hx
      simpa using this
    have h3 : a ∈ T ⊓ A := ⟨haT, ha⟩
    rw [heq] at h3
    exact B.mul_mem hb h3.2
  have hTeq : T = B := le_antisymm hTB hBT
  rw [hTeq] at hT
  exact hT

open CFSG.Quasithin CFSG.QuasithinUnique in
open scoped Pointwise in
theorem burnsideC5h_p1_uniqueMax_sup {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hU : burnsideC5h_p1_UMaxIn A (A ⊓ B)) :
    ∃ N : Subgroup G, CFSG.Quasithin.IsUniqueMaxOver (A ⊔ B) B N := by
  obtain ⟨B₀, hB₀A, hPB₀, hmax⟩ := hU
  have hconj : ∀ x ∈ B, conjByElt x B₀ ≤ B₀ := by
    intro x hx
    have hxA : conjByElt x A = A := C2Eleven.mem_normalizer_iff_conjByElt.mp (hBA hx)
    have hxB : conjByElt x B = B := C2Eleven.mem_normalizer_iff_conjByElt.mp
      (Subgroup.le_normalizer hx)
    have hxP : conjByElt x (A ⊓ B) = A ⊓ B := by
      have e : conjByElt x (A ⊓ B) = conjByElt x A ⊓ conjByElt x B :=
        Subgroup.map_inf A B (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
      rw [e, hxA, hxB]
    have hlt : conjByElt x B₀ < A := by
      have := (MulEquiv.mapSubgroup (MulAut.conj x)).strictMono hB₀A
      change conjByElt x B₀ < conjByElt x A at this
      rwa [hxA] at this
    have hPle : A ⊓ B ≤ conjByElt x B₀ := by
      calc A ⊓ B = conjByElt x (A ⊓ B) := hxP.symm
        _ ≤ conjByElt x B₀ := Subgroup.map_mono hPB₀
    exact hmax _ hPle hlt
  have hnorm : B ≤ Subgroup.normalizer (B₀ : Set G) := by
    intro x hx
    rw [C2Eleven.mem_normalizer_iff_conjByElt]
    refine le_antisymm (hconj x hx) ?_
    have h1 := hconj x⁻¹ (B.inv_mem hx)
    have h2 : conjByElt x (conjByElt x⁻¹ B₀) = B₀ := by
      rw [← C2Eleven.conjByElt_mul, mul_inv_cancel, C2Eleven.conjByElt_one]
    calc B₀ = conjByElt x (conjByElt x⁻¹ B₀) := h2.symm
      _ ≤ conjByElt x B₀ := Subgroup.map_mono h1
  have hsup : ∀ z ∈ A ⊔ B, ∃ b ∈ B, ∃ a ∈ A, z = b * a := by
    intro z hz
    have hset : ((B ⊔ A : Subgroup G) : Set G) = (B : Set G) * (A : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B A hBA
    have hz' : z ∈ ((B ⊔ A : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hz
    rw [hset] at hz'
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨b, hb, a, ha, rfl⟩
  have hsup0 : ∀ z ∈ B₀ ⊔ B, ∃ b ∈ B, ∃ c ∈ B₀, z = b * c := by
    intro z hz
    have hset : ((B ⊔ B₀ : Subgroup G) : Set G) = (B : Set G) * (B₀ : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B B₀ hnorm
    have hz' : z ∈ ((B ⊔ B₀ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hz
    rw [hset] at hz'
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨b, hb, c, hc, rfl⟩
  have K1 : ∀ Y : Subgroup G, B ≤ Y → Y < A ⊔ B → Y ≤ B₀ ⊔ B := by
    intro Y hBY hY
    have hYA : Y ⊓ A < A := by
      refine lt_of_le_of_ne inf_le_right fun h => ?_
      have hAY : A ≤ Y := inf_eq_right.mp h
      exact hY.ne (le_antisymm hY.le (sup_le hAY hBY))
    have hPY : A ⊓ B ≤ Y ⊓ A := fun x hx => ⟨hBY hx.2, hx.1⟩
    have hYB₀ : Y ⊓ A ≤ B₀ := hmax _ hPY hYA
    intro z hz
    obtain ⟨b, hb, a, ha, rfl⟩ := hsup z (hY.le hz)
    have haY : a ∈ Y := by
      have : b⁻¹ * (b * a) ∈ Y := Y.mul_mem (Y.inv_mem (hBY hb)) hz
      simpa using this
    have haB₀ : a ∈ B₀ := hYB₀ ⟨haY, ha⟩
    exact (B₀ ⊔ B).mul_mem (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left haB₀)
  have K2 : B₀ ⊔ B < A ⊔ B := by
    refine lt_of_le_of_ne (sup_le_sup_right hB₀A.le B) fun h => ?_
    have hAle : A ≤ B₀ ⊔ B := h ▸ le_sup_left
    apply hB₀A.ne
    refine le_antisymm hB₀A.le fun a ha => ?_
    obtain ⟨b, hb, c, hc, hbc⟩ := hsup0 a (hAle ha)
    have hcA : c ∈ A := hB₀A.le hc
    have hbA : b ∈ A := by
      have : a * c⁻¹ ∈ A := A.mul_mem ha (A.inv_mem hcA)
      rw [hbc] at this
      simpa using this
    have hbB₀ : b ∈ B₀ := hPB₀ ⟨hbA, hb⟩
    rw [hbc]
    exact B₀.mul_mem hbB₀ hc
  refine ⟨B₀ ⊔ B, isUniqueMaxOver_iff.mpr ⟨⟨K2, fun Z hZ1 hZ2 => ?_⟩, le_sup_right, fun N' hN' hBN' => ?_⟩⟩
  · by_contra hne
    have hZ : Z < A ⊔ B := lt_of_le_of_ne hZ2 hne
    exact absurd (K1 Z (le_sup_right.trans hZ1.le) hZ) (not_le_of_gt hZ1)
  · have hle : N' ≤ B₀ ⊔ B := K1 N' hBN' hN'.1
    by_contra hne
    have hlt : N' < B₀ ⊔ B := lt_of_le_of_ne hle hne
    exact K2.ne (hN'.2 _ hlt K2.le)

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_p1_card_conjByElt {G : Type} [Group G] (a : G) (L : Subgroup G) :
    Nat.card (conjByElt a L) = Nat.card L :=
  Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5h_p1_three_dvd {G : Type} [Group G] {X L : Subgroup G}
    (h : IsChi0Block X L) : 3 ∣ Nat.card L :=
  C1GN.three_dvd_card_of_isChiBlock ⟨h.1, by
    rcases h.2 with hl | h3 | h5
    · exact Or.inl hl
    · exact Or.inr ⟨3, by decide, le_rfl, h3⟩
    · exact Or.inr ⟨5, by decide, by norm_num, h5⟩⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_comm_J {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {t : G} (ht : t ∈ TH) :
    ⁅conjByElt t K₁, thompsonJ R⁆ = conjByElt t K₁ := by
  have hTR : t ∈ Subgroup.normalizer (R : Set G) := (hset.hyp1.TH_le.trans hset.hyp1.R_norm) ht
  have hJ : conjByElt t (thompsonJ R) = thompsonJ R :=
    C2Eleven.mem_normalizer_iff_conjByElt.mp (normalizer_le_normalizer_thompsonJ R hTR)
  calc ⁅conjByElt t K₁, thompsonJ R⁆ = ⁅conjByElt t K₁, conjByElt t (thompsonJ R)⁆ := by
        rw [hJ]
    _ = conjByElt t ⁅K₁, thompsonJ R⁆ := (Subgroup.map_commutator _ _ _).symm
    _ = conjByElt t K₁ := by rw [hset.config.comm_J]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_not_normal {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {t : G} (ht : t ∈ TH)
    (hS : baum R ≤ Subgroup.normalizer (conjByElt t K₁ : Set G)) :
    ¬ (conjByElt t K₁ ⊔ (R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G)) ≤
      Subgroup.normalizer ((R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G) : Subgroup G) :
        Set G)) := by
  intro hN
  have hyp1 := hset.hyp1
  have hJR : thompsonJ R ≤ R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G) :=
    le_inf (B6.thompsonJ_le R) ((C5.thompsonJ_le_baum' R).trans hS)
  have hcomm : ⁅conjByElt t K₁, thompsonJ R⁆ ≤ R := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    have hg₂R : g₂ ∈ R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G) := hJR hg₂
    have h1 : g₁ * g₂ * g₁⁻¹ ∈ R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_left hg₁)) g₂).mp hg₂R
    rw [commutatorElement_def]
    exact R.mul_mem h1.1 (R.inv_mem hg₂R.1)
  have hKiR : conjByElt t K₁ ≤ R := by
    have := burnsideC5h_p1_comm_J hset ht
    rw [this] at hcomm
    exact hcomm
  have hR2 : IsPGroup 2 R := hyp1.sylow.2.1.to_le hyp1.R_le
  have h2 : IsPGroup 2 ↥(conjByElt t K₁) := hR2.to_le hKiR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have h3 : 3 ∣ Nat.card (conjByElt t K₁) := by
    rw [burnsideC5h_p1_card_conjByElt]
    exact burnsideC5h_p1_three_dvd hset.config.chi0
  rw [hk] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_umax_conj {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {t : G} (ht : t ∈ TH) :
    burnsideC5h_p1_UMaxIn (conjByElt t K₁) (R ⊓ conjByElt t K₁) := by
  have hyp1 := hset.hyp1
  have cfg := hset.config
  have hTR : t ∈ Subgroup.normalizer (R : Set G) := (hyp1.TH_le.trans hyp1.R_norm) ht
  have hsyl1 : IsSylowTwoOf (R ⊓ K₁) K₁ := by
    have := burnsideC5h_p1_isSylow_inf hset (TH.one_mem)
    rwa [C2Eleven.conjByElt_one] at this
  obtain ⟨B, hBK, hPB, hmax⟩ := burnsideC5h_p1_blockMax cfg.chi0.1.1 cfg.chi0.2 hsyl1
  have h := burnsideC5h_p1_umaxIn_conjByElt t ⟨B, hBK, hPB, hmax⟩
  have hRt : R.map (MulAut.conj t).toMonoidHom = R := C2Eleven.mem_normalizer_iff_conjByElt.mp hTR
  have e : conjByElt t (R ⊓ K₁) = R ⊓ conjByElt t K₁ := by
    change (R ⊓ K₁).map (MulAut.conj t).toMonoidHom = R ⊓ K₁.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hRt]
  rwa [e] at h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p1_minParabolic {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁)
    (hS : ∀ Ki ∈ conjSubgroupsBy TH K₁, baum R ≤ Subgroup.normalizer (Ki : Set G)) :
    ∀ Ki ∈ conjSubgroupsBy TH K₁, ∃ N : Subgroup G,
      MinParabolic (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G)))
        (R ⊓ Subgroup.normalizer (Ki : Set G)) N := by
  rintro Ki ⟨t, ht, hKi⟩
  have hKi' : Ki = conjByElt t K₁ := hKi
  subst hKi'
  have hyp1 := hset.hyp1
  have hR2 : IsPGroup 2 R := hyp1.sylow.2.1.to_le hyp1.R_le
  have hinf : conjByElt t K₁ ⊓ (R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G)) =
      R ⊓ conjByElt t K₁ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2, -⟩
      exact ⟨hx2, hx1⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, hx1, Subgroup.le_normalizer hx2⟩
  have hsyl : IsSylowTwoOf (R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G))
      (conjByElt t K₁ ⊔ (R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G))) := by
    refine burnsideC5h_p1_isSylow_sup (hR2.to_le inf_le_left) inf_le_right ?_
    rw [hinf]
    exact burnsideC5h_p1_isSylow_inf hset ht
  obtain ⟨N, hN⟩ := burnsideC5h_p1_uniqueMax_sup (A := conjByElt t K₁)
    (B := R ⊓ Subgroup.normalizer (conjByElt t K₁ : Set G)) inf_le_right
    (by rw [hinf]; exact burnsideC5h_p1_umax_conj hset ht)
  exact ⟨N, hsyl, burnsideC5h_p1_not_normal hset ht (hS _ ⟨t, ht, rfl⟩), hN⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p2_thompsonJ_eq {G : Type} [Group G] [Finite G] {R Ri : Subgroup G}
    (hJ : thompsonJ R ≤ Ri) (hRiR : Ri ≤ R) : thompsonJ Ri = thompsonJ R :=
  B6.thompsonJ_eq_of_le hJ hRiR

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p2_baum_eq {G : Type} [Group G] [Finite G] {R Ri : Subgroup G}
    (hJ : thompsonJ R ≤ Ri) (hRiR : Ri ≤ R) (hS : baum R ≤ Ri) : baum Ri = baum R := by
  have hJeq := burnsideC5h_p2_thompsonJ_eq hJ hRiR
  unfold baum
  rw [hJeq]
  refine le_antisymm (inf_le_inf_right _ hRiR) (le_inf ?_ inf_le_right)
  exact (hS : baum R ≤ Ri)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p2_comm_conj {G : Type} [Group G] {K J : Subgroup G} {t : G}
    (hK : ⁅K, J⁆ = K) (ht : t ∈ Subgroup.normalizer (J : Set G)) :
    ⁅conjByElt t K, J⁆ = conjByElt t K := by
  have hJ : J.map (MulAut.conj t).toMonoidHom = J := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  calc ⁅conjByElt t K, J⁆ = ⁅K.map (MulAut.conj t).toMonoidHom, J.map (MulAut.conj t).toMonoidHom⁆ := by
        unfold conjByElt; rw [hJ]
    _ = (⁅K, J⁆).map (MulAut.conj t).toMonoidHom := (Subgroup.map_commutator K J (MulAut.conj t).toMonoidHom).symm
    _ = conjByElt t K := by rw [hK]; rfl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p2_isMinimalParabolic {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
    (h : MinParabolic H T M) : IsMinimalParabolic T H :=
  ⟨h.isSylow, h.not_normal, M, h.le, h.maximal.1, fun _ hTX hXH => h.le_of_lt hTX hXH⟩

theorem burnsideC5h_p2_perm3_of_card_six {Y : Type} [Group Y] [Finite Y] (hcard : Nat.card Y = 6)
    (hnc : ∃ a b : Y, a * b ≠ b * a) : Nonempty (Y ≃* Equiv.Perm (Fin 3)) := by
  classical
  have h2 : 2 ∣ Nat.card Y := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' Y _ _ 2 ⟨Nat.prime_two⟩ h2
  set P : Subgroup Y := Subgroup.zpowers x with hP
  have hPcard : Nat.card P = 2 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 3 := by
    have := Subgroup.card_mul_index P
    rw [hPcard, hcard] at this
    omega
  have hQcard : Nat.card (Y ⧸ P) = 3 := hidx
  let φ : Y →* Equiv.Perm (Y ⧸ P) := MulAction.toPermHom Y (Y ⧸ P)
  have hker : φ.ker ≤ P := by
    intro g hg
    have h1 : φ g = 1 := hg
    have h2 : g • (QuotientGroup.mk (1 : Y) : Y ⧸ P) = QuotientGroup.mk 1 := by
      have := congrArg (fun σ : Equiv.Perm (Y ⧸ P) => σ (QuotientGroup.mk (1 : Y))) h1
      exact this
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h2
    have h3 := QuotientGroup.eq.mp h2
    rw [mul_one] at h3
    simpa using P.inv_mem h3
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hne
    have hgP : g ∈ P := hker hg
    have hkerP : φ.ker = P := by
      refine le_antisymm hker ?_
      have hle : φ.ker ≤ P := hker
      have hcard1 : Nat.card φ.ker ∣ Nat.card P := by
        have := Subgroup.card_dvd_of_le hle
        simpa using this
      have hne1 : Nat.card φ.ker ≠ 1 := by
        intro h1
        have hmem : g ∈ φ.ker := hg
        rw [Subgroup.eq_bot_of_card_eq _ h1] at hmem
        exact hne (Subgroup.mem_bot.mp hmem)
      have hcard2 : Nat.card φ.ker = 2 := by
        rw [hPcard] at hcard1
        rcases (Nat.dvd_prime Nat.prime_two).mp hcard1 with h | h
        · exact absurd h hne1
        · exact h
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hPcard])).ge
    have hPn : P.Normal := hkerP ▸ φ.normal_ker
    have hcentral : P ≤ Subgroup.center Y := by
      intro p hp
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      rw [Subgroup.mem_center_iff]
      intro y
      have hyx : y * x * y⁻¹ ∈ P := hPn.conj_mem x (Subgroup.mem_zpowers x) y
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyx
      have hm' : x ^ (m % 2) = y * x * y⁻¹ := by
        have := zpow_mod_orderOf x m
        rw [hx] at this
        simpa using this.trans hm
      have hxne : x ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hx
        omega
      have hyx' : y * x * y⁻¹ = x := by
        rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with h | h
        · rw [h, zpow_zero] at hm'
          exact absurd (by simpa using (conj_eq_one_iff.mp hm'.symm)) hxne
        · rw [h, zpow_one] at hm'
          exact hm'.symm
      have hyk : y * x ^ k * y⁻¹ = x ^ k := by
        have := conj_zpow (a := y) (b := x) (i := k)
        rw [← this, hyx']
      calc y * x ^ k = (y * x ^ k * y⁻¹) * y := by group
        _ = x ^ k * y := by rw [hyk]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic (Y ⧸ P) := isCyclic_of_prime_card hQcard
    have hf : (QuotientGroup.mk' P).ker ≤ Subgroup.center Y := by
      rw [QuotientGroup.ker_mk']; exact hcentral
    obtain ⟨a, b, hab⟩ := hnc
    haveI := (QuotientGroup.mk' P).isMulCommutative_of_isCyclic_of_ker_le_center hf
    exact hab (IsMulCommutative.is_comm.comm a b)
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_perm, hQcard]
    decide
  haveI : Fintype (Y ⧸ P) := Fintype.ofFinite _
  let e : Y ⧸ P ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hQcard)
  exact ⟨(MulEquiv.ofBijective φ hbij).trans (Equiv.permCongrHom e)⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped commutatorElement in
theorem burnsideC5h_p2_A3_S3 {G : Type} [Group G] [Finite G] {Ki S J : Subgroup G}
    (hshort : IsShort2 Ki) (h3 : IsAltType Ki 3) (hSN : S ≤ Subgroup.normalizer (Ki : Set G))
    (hS2 : IsPGroup 2 S) (hSyl : IsSylowTwoOf S (Ki ⊔ S)) (hJS : J ≤ S) (hcomm : ⁅Ki, J⁆ = Ki)
    (hq : (S ⊓ Subgroup.centralizer (blockU Ki : Set G)).relIndex S = 2) :
    Nonempty ((↥(Ki ⊔ S) ⧸ CFSG.pCore 2 ↥(Ki ⊔ S)) ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨hQU, hU4, -, -, hK12, -⟩ := hshort.alt3_structure h3
  set X := Ki ⊔ S with hX
  set Q := pCoreOf 2 X with hQ
  have hKX : Ki ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (Ki : Set G) := sup_le Subgroup.le_normalizer hSN
  have hQeq : S ⊓ Subgroup.centralizer (blockU Ki : Set G) = Q :=
    C56.baum_inf_centralizer_eq hshort hS2 hSN hSyl
  have hQS : Q ≤ S := fun g hg => hSyl.pCoreOf_le hg
  have hUK : blockU Ki ≤ Ki := Setup.Campbell.blockU_le_self_of_isShort2 hshort
  have hUQ : blockU Ki ≤ Q := by
    refine C1.le_pCoreOf_of_normalized (hUK.trans hKX) ?_ (C1.isPGroup_blockU hshort)
    exact sup_le (C1.le_normalizer_blockU Ki) fun g hg => C1.mem_normalizer_blockU (hSN hg)
  have hidxU : (blockU Ki).relIndex Ki = 3 := by
    have := Subgroup.relIndex_mul_card (blockU Ki) Ki
    rw [inf_eq_left.mpr hUK, hU4, hK12] at this
    omega
  have hSK : S ⊓ Ki = blockU Ki := by
    refine le_antisymm ?_ (le_inf (hUQ.trans hQS) hUK)
    have hUW : blockU Ki ≤ S ⊓ Ki := le_inf (hUQ.trans hQS) hUK
    have hmul := Subgroup.relIndex_mul_relIndex (blockU Ki) (S ⊓ Ki) Ki hUW inf_le_right
    rw [hidxU] at hmul
    have hdvd : (S ⊓ Ki).relIndex Ki ∣ 3 := Dvd.intro_left _ hmul
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exfalso
      have hKS : Ki ≤ S ⊓ Ki := Subgroup.relIndex_eq_one.mp h1
      have hK2 : IsPGroup 2 Ki := hS2.to_le (hKS.trans inf_le_left)
      obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hK2 (blockU Ki)
      rw [hidxU] at hn
      have : 3 ∣ 2 ^ n := by rw [← hn]
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      omega
    · rw [h3'] at hmul
      have : (blockU Ki).relIndex (S ⊓ Ki) = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp this
  have hSidx : S.relIndex X = 3 := by
    have h := B6.relIndex_inf_eq_relIndex_sup hSN
    rw [hSK, hidxU] at h
    rw [hX, sup_comm]
    exact h.symm
  have hQidx : Q.relIndex X = 6 := by
    have h := Subgroup.relIndex_mul_relIndex Q S X hQS hSX
    rw [← hQeq, hq, hSidx] at h
    rw [hQeq] at h
    omega
  have hcard : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 6 := by
    have h1 : (Q.subgroupOf X) = CFSG.pCore 2 ↥X :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf 2 X
    show (CFSG.pCore 2 ↥X).index = 6
    rw [← h1]
    exact hQidx
  have hnc : ∃ a b : ↥X ⧸ CFSG.pCore 2 ↥X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm' : ∀ k ∈ Ki, ∀ j ∈ J, ⁅k, j⁆ ∈ blockU Ki := by
      intro k hk j hj
      have hjS : j ∈ S := hJS hj
      have hq1 : (⁅(⟨k, hKX hk⟩ : ↥X), (⟨j, hSX hjS⟩ : ↥X)⁆) ∈ CFSG.pCore 2 ↥X := by
        rw [← QuotientGroup.eq_one_iff]
        have e : (QuotientGroup.mk ⁅(⟨k, hKX hk⟩ : ↥X), (⟨j, hSX hjS⟩ : ↥X)⁆ :
            ↥X ⧸ CFSG.pCore 2 ↥X) =
            ⁅(QuotientGroup.mk (⟨k, hKX hk⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X),
              (QuotientGroup.mk (⟨j, hSX hjS⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X)⁆ :=
          map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) _ _
        rw [e]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon _ _)
      have hkQ : ⁅k, j⁆ ∈ Q := Subgroup.mem_map.mpr ⟨_, hq1, rfl⟩
      have hkK : ⁅k, j⁆ ∈ Ki := by
        have hjk : j * k⁻¹ * j⁻¹ ∈ Ki := (Subgroup.mem_normalizer_iff.mp (hSN hjS) k⁻¹).mp
          (Subgroup.inv_mem _ hk)
        have : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact Subgroup.mul_mem _ hk hjk
      have hQK : Q ⊓ Ki ≤ pCoreOf 2 Ki := by
        refine C1.le_pCoreOf_of_normalized inf_le_right ?_
          ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X).to_le inf_le_left)
        intro g hg
        exact C5.mem_normalizer_inf
          (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X (hKX hg))
          (Subgroup.le_normalizer hg)
      have : ⁅k, j⁆ ∈ pCoreOf 2 Ki := hQK ⟨hkQ, hkK⟩
      have hQK' : pCoreOf 2 Ki = blockU Ki := hQU
      rwa [hQK'] at this
    have hle : Ki ≤ blockU Ki := by
      have h := Subgroup.commutator_le.mpr hcomm'
      rwa [hcomm] at h
    have := Subgroup.relIndex_eq_one.mpr hle
    omega
  exact burnsideC5h_p2_perm3_of_card_six hcard hnc

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5h_p2_lin2A3 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hP1 : ∀ Ki ∈ conjSubgroupsBy TH K₁, ∃ N : Subgroup G,
      MinParabolic (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G)))
        (R ⊓ Subgroup.normalizer (Ki : Set G)) N) :
    ∀ Ki ∈ conjSubgroupsBy TH K₁, ((∃ n : ℕ, 1 < n ∧ IsLin2Type Ki n) ∨ IsAltType Ki 3) →
      IsSylowTwoOf (baum R ⊓ Ki) Ki ∧
      ((∃ n : ℕ, 1 < n ∧ IsLin2Type Ki n) →
        (baum R : Set G) = ((baum R ⊓ Ki : Subgroup G) : Set G) *
          (pCoreOf 2 (Ki ⊔ baum R) : Set G)) ∧
      (IsAltType Ki 3 →
        Nonempty ((↥(Ki ⊔ baum R) ⧸ CFSG.pCore 2 ↥(Ki ⊔ baum R)) ≃* Equiv.Perm (Fin 3))) ∧
      (blockU Ki ≤ pCoreOf 2 (Ki ⊔ baum R) ∧
        pCoreOf 2 (Ki ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU Ki : Set G)) := by
  classical
  intro Ki hKi hL
  have hyp1 := hset.hyp1
  have cfg := hset.config
  obtain ⟨N, hmin⟩ := hP1 Ki hKi
  have hshort : IsShort2 Ki := (burnsideC5h_c54_isBlock2 hset hKi).1
  set Ri : Subgroup G := R ⊓ Subgroup.normalizer (Ki : Set G) with hRi
  have hS1 : baum R ≤ Subgroup.normalizer (Ki : Set G) := burnsideC5h_c54_one h116 hset Ki hKi
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hSRi : baum R ≤ Ri := le_inf hSR hS1
  have hJRi : thompsonJ R ≤ Ri := (C5.thompsonJ_le_baum' R).trans hSRi
  have hRiR : Ri ≤ R := inf_le_left
  have hJeq : thompsonJ Ri = thompsonJ R := burnsideC5h_p2_thompsonJ_eq hJRi hRiR
  have hbeq : baum Ri = baum R := burnsideC5h_p2_baum_eq hJRi hRiR hSRi
  have hth : ⁅Ki, thompsonJ Ri⁆ = Ki := by
    rw [hJeq]
    obtain ⟨t, ht, rfl⟩ := hKi
    refine burnsideC5h_p2_comm_conj cfg.comm_J ?_
    exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ R
      (hyp1.TH_le.trans hyp1.R_norm ht)
  have hHiN : Ki ⊔ Ri ≤ Subgroup.normalizer (Ki : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hblk : IsChi0Block (Ki ⊔ Ri) Ki := by
    refine ⟨⟨hshort, le_sup_left, ?_⟩, ?_⟩
    · exact ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHiN).isSubnormal
    · rcases hL with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hminc : IsMinimalParabolic Ri (Ki ⊔ Ri) := burnsideC5h_p2_isMinimalParabolic hmin
  obtain ⟨hBN', hBsyl'⟩ := C56.baumann_single hminc hblk hL hth rfl inf_le_right
  rw [hbeq] at hBN' hBsyl'
  have hSyl : IsSylowTwoOf (baum R) (Ki ⊔ baum R) := hBsyl'
  have hB2 : IsPGroup 2 (baum R) := (hyp1.sylow.2.1.to_le (hyp1.R_le)).to_le hSR
  have hX : Ki ⊔ baum R ≤ Subgroup.normalizer (Ki : Set G) := sup_le Subgroup.le_normalizer hS1
  have hQS : pCoreOf 2 (Ki ⊔ baum R) ≤ baum R := fun g hg => hSyl.pCoreOf_le hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact B6.isSylowTwoOf_inf_normal hSyl le_sup_left hX
  · rintro ⟨n, hn, hlin⟩
    have hc := C56.baumann_c542 hminc hblk hn hlin hth rfl inf_le_right
    rw [hbeq] at hc
    have hBQ : baum R ⊓ Ki ≤ Subgroup.normalizer (pCoreOf 2 (Ki ⊔ baum R) : Set G) := fun g hg =>
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
        (Subgroup.mem_sup_right (hg.1))
    have hsup : baum R = (baum R ⊓ Ki) ⊔ pCoreOf 2 (Ki ⊔ baum R) :=
      le_antisymm hc (sup_le inf_le_left hQS)
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBQ, ← hsup]
  · intro h3
    obtain ⟨q, W, hq2, -, hidxQ, -, -, -, hZ, -⟩ :=
      C56.natural_A3 hminc hblk h3 hth rfl inf_le_right
    obtain ⟨-, hU4, -, -, -, hcen, -⟩ := hshort.alt3_structure h3
    have hbot : blockU Ki ⊓ Subgroup.centralizer (Ki : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      refine hcen g ((Setup.Campbell.blockU_le_self_of_isShort2 hshort) hg.1) fun l hl => ?_
      exact (Subgroup.mem_centralizer_iff.mp hg.2 l hl).symm
    rw [hbot, Subgroup.relIndex_bot_left, hU4] at hZ
    have hq : q = 2 := by
      have : q ^ 2 = 2 ^ 2 := by omega
      exact Nat.pow_left_injective (by norm_num) this
    rw [hbeq, hq] at hidxQ
    exact burnsideC5h_p2_A3_S3 hshort h3 hS1 hB2 hSyl (C5.thompsonJ_le_baum' R)
      (by rw [← hJeq]; exact hth) hidxQ
  · refine C1.le_pCoreOf_of_normalized ?_ ?_ (C1.isPGroup_blockU hshort)
    · exact (Setup.Campbell.blockU_le_self_of_isShort2 hshort).trans le_sup_left
    · refine sup_le (C1.le_normalizer_blockU Ki) fun g hg => C1.mem_normalizer_blockU (hS1 hg)
  · exact (C56.baum_inf_centralizer_eq hshort hB2 hS1 hSyl).symm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
structure burnsideC5h_p3_Setting {G : Type} [Group G] (L S : Subgroup G) : Prop where
  short : IsShort2 L
  alt5 : IsAltType L 5
  norm : S ≤ Subgroup.normalizer (L : Set G)
  sylow : IsSylowTwoOf S (L ⊔ S)
  comm : ⁅L, thompsonJ S⁆ = L

section Stage1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G}

theorem burnsideC5h_p3_sup_le_normalizer (h : burnsideC5h_p3_Setting L S) :
    L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer h.norm

theorem burnsideC5h_p3_blockU_le_pCoreOf (h : burnsideC5h_p3_Setting L S) :
    blockU L ≤ pCoreOf 2 (L ⊔ S) := by
  have hL := h.short
  refine C1.le_pCoreOf_of_normalized
    ((Setup.Campbell.blockU_le_self_of_isShort2 hL).trans le_sup_left) ?_ (C1.isPGroup_blockU hL)
  exact sup_le (C1.le_normalizer_blockU L) fun g hg => C1.mem_normalizer_blockU (h.norm hg)

theorem burnsideC5h_p3_blockU_le (h : burnsideC5h_p3_Setting L S) : blockU L ≤ S :=
  (burnsideC5h_p3_blockU_le_pCoreOf h).trans h.sylow.pCoreOf_le

theorem burnsideC5h_p3_sylow_card_perm_five (P : Sylow 2 (Equiv.Perm (Fin 5))) :
    Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)),
    Fintype.card_perm]
  have h120 : (Nat.factorial (Fintype.card (Fin 5))) = 2 ^ 3 * 15 := by
    rw [Fintype.card_fin]; decide
  rw [h120, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

theorem burnsideC5h_p3_thompsonJ_conj_mem {s y : G} (hs : s ∈ S) (hy : y ∈ thompsonJ S) :
    s * y * s⁻¹ ∈ thompsonJ S :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ S (Subgroup.le_normalizer hs)) y).mp hy

theorem burnsideC5h_p3_card_im_S (hHN : L ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf S (L ⊔ S)) (D : AppC.PiData L)
    (hsurj : Function.Surjective (D.π.comp (Subgroup.inclusion hHN))) :
    Nat.card (D.im S) = 8 := by
  have hS' : IsPGroup 2 (S.subgroupOf (L ⊔ S)) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 ↥(L ⊔ S) := hS'.toSylow hS.2.2
  have h1 := burnsideC5h_p3_sylow_card_perm_five (P.mapSurjective hsurj)
  have h2 : ((P.mapSurjective hsurj : Sylow 2 (Equiv.Perm (Fin 5))) :
      Subgroup (Equiv.Perm (Fin 5))) =
      (S.subgroupOf (L ⊔ S)).map (D.π.comp (Subgroup.inclusion hHN)) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : (S.subgroupOf (L ⊔ S)).map (D.π.comp (Subgroup.inclusion hHN)) = D.im S := by
    ext g
    rw [D.mem_im, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hHN x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hS.1 hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  rw [← h3, ← h2]
  exact h1

theorem burnsideC5h_p3_exists_mem_thompsonJ_pi_ne_one (h : burnsideC5h_p3_Setting L S)
    (D : AppC.PiData L) (hLQ : ¬ L ≤ blockQ L) :
    ∃ y : ↥(Subgroup.normalizer (L : Set G)), (y : G) ∈ thompsonJ S ∧ D.π y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hLQ
  have hL : IsShort2 L := h.short
  have hSN := h.norm
  have hJS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hLQ' : L ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 L :=
    C1.inf_centralizer_blockU_eq hL le_rfl Subgroup.le_normalizer
      (fun g hg => ⟨0, by simpa using hg⟩)
  calc L = ⁅L, thompsonJ S⁆ := h.comm.symm
    _ ≤ blockQ L := by
      rw [Subgroup.commutator_le]
      intro ℓ hℓ y hy
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := hSN (hJS hy)
      have hyL : y * ℓ⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hℓ)
      have hcom : ⁅ℓ, y⁆ = ℓ * (y * ℓ⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      have hcL : ⁅ℓ, y⁆ ∈ L := by rw [hcom]; exact mul_mem hℓ hyL
      have hπ : D.π (⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
          ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
        have hy1 := hcon ⟨y, hyN⟩ hy
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
        simp
      have hc := (D.hker _).1 hπ
      have hcC : ⁅ℓ, y⁆ ∈ Subgroup.centralizer (blockU L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 := hc u hu
        have h2 : (((⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
            ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹ :
              ↥(Subgroup.normalizer (L : Set G))) : ↥(Subgroup.normalizer (L : Set G))) : G) =
            ⁅ℓ, y⁆ := by
          simp [commutatorElement_def]
        rw [h2] at h1
        calc u * ⁅ℓ, y⁆ = (⁅ℓ, y⁆ * u * ⁅ℓ, y⁆⁻¹) * ⁅ℓ, y⁆ := by rw [h1]
          _ = ⁅ℓ, y⁆ * u := by group
      have h3 : ⁅ℓ, y⁆ ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hcL, hcC⟩
      rw [hLQ'] at h3
      exact h3

theorem burnsideC5h_p3_swapGen_imJ (h : burnsideC5h_p3_Setting L S) (D : AppC.PiData L) :
    ∀ g ∈ D.im (thompsonJ S),
      g ∈ Subgroup.closure {s : Equiv.Perm (Fin 5) | s ∈ D.im (thompsonJ S) ∧ s.IsSwap} := by
  have hL := h.short
  have hSN := h.norm
  have hUS : blockU L ≤ S := burnsideC5h_p3_blockU_le h
  have hU := AppC.isElemAbelian_blockU hL
  set Cl := Subgroup.closure {s : Equiv.Perm (Fin 5) | s ∈ D.im (thompsonJ S) ∧ s.IsSwap} with hCl
  have hW : thompsonJ S ≤ (Cl.comap D.π).map (Subgroup.normalizer (L : Set G)).subtype := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hSN (hA.1 ha)
    refine Subgroup.mem_map.2 ⟨⟨a, haN⟩, ?_, rfl⟩
    show D.π ⟨a, haN⟩ ∈ Cl
    have hmem : D.π ⟨a, haN⟩ ∈ D.im A := D.pi_mem_im ha
    have := D.swapGen_im hU hUS hSN hA _ hmem
    refine Subgroup.closure_mono ?_ this
    intro s hs
    exact ⟨D.im_mono (GammaExtra.le_thompsonJ hA) hs.1, hs.2⟩
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.1 (hW hy)
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact hy'

theorem burnsideC5h_p3_mem_omegaOneCenter (h : burnsideC5h_p3_Setting L S) {u : G}
    (hu : u ∈ blockU L) (hc : ∀ y ∈ thompsonJ S, y * u = u * y) :
    u ∈ omegaOneCenterOf (thompsonJ S) := by
  have hL := h.short
  have hU := AppC.isElemAbelian_blockU hL
  have hUS : blockU L ≤ S := burnsideC5h_p3_blockU_le h
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
  have huA : u ∈ A :=
    inf_centralizer_le_of_isMaxElemAbelian hU hUS hA
      ⟨hu, Subgroup.mem_centralizer_iff.2 fun a ha => hc a (GammaExtra.le_thompsonJ hA ha)⟩
  have huJ : u ∈ thompsonJ S := GammaExtra.le_thompsonJ hA huA
  exact Subgroup.subset_closure ⟨⟨huJ, Subgroup.mem_centralizer_iff.2 fun y hy => hc y hy⟩,
    C1.blockU_sq hL u hu⟩

theorem burnsideC5h_p3_a5_core (h : burnsideC5h_p3_Setting L S) (P : AppC.A5Pi L) :
    ∃ τ₁ τ₂ : Equiv.Perm (Fin 5), τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      P.im (thompsonJ S) = Subgroup.closure {τ₁, τ₂} ∧
      P.im (baum S) = Subgroup.closure {τ₁, τ₂} ∧ Nat.card (P.im S) = 8 ∧
      (∃ d ∈ P.im S, d * τ₁ * d⁻¹ = τ₂) ∧ P.im (L ⊔ baum S) = ⊤ ∧
      (∀ d ∈ P.im S, ∀ j ∈ P.im (thompsonJ S), d * j * d⁻¹ ∈ P.im (thompsonJ S)) ∧
      ∀ g : Equiv.Perm (Fin 5),
        (∀ w ∈ AppC.FixΔ (P.im (thompsonJ S)), A5.Delta5.vact g w = w) →
          g ∈ P.im (thompsonJ S) := by
  classical
  have hL : IsShort2 L := h.short
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := h.norm
  have hHN := burnsideC5h_p3_sup_le_normalizer h
  have hUS : blockU L ≤ S := burnsideC5h_p3_blockU_le h
  have hU := AppC.isElemAbelian_blockU hL
  have hBS : baum S ≤ S := inf_le_left
  have hJB : thompsonJ S ≤ baum S := C5.thompsonJ_le_baum' S
  have hJS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hXN : L ⊔ baum S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (hBS.trans hSN)
  have hXH : L ⊔ baum S ≤ L ⊔ S := sup_le_sup_left hBS L
  let D : AppC.PiData L := P.toPiData
  let β := D.β
  let π := D.π
  have hcomp := D.hcomp
  have hα := P.hα
  have hαk := P.hαk
  have hπα := P.hπα
  have hLQ : ¬ L ≤ blockQ L := by
    intro hle
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [A5.Delta5.a5_card]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨ℓ, rfl⟩ := hα a
    apply ha
    have h1 : ℓ ∈ P.α.ker := by
      rw [hαk, AppC.mem_pCore_iff_mem_blockQ]
      exact hle ℓ.2
    exact h1
  obtain ⟨y₀, hy₀J, hy₀⟩ := burnsideC5h_p3_exists_mem_thompsonJ_pi_ne_one h D hLQ
  have hJ1 : ∃ j ∈ D.im (thompsonJ S), j ≠ 1 := ⟨D.π y₀, D.pi_mem_im hy₀J, hy₀⟩
  have hJsw := burnsideC5h_p3_swapGen_imJ h D
  obtain ⟨t, htJ, htsw⟩ := AppC.exists_swap_of_swapGen _ hJ1 hJsw
  have hπX : ∀ σ : Equiv.Perm (Fin 5), ∃ x : ↥(L ⊔ baum S), π ⟨x, hXN x.2⟩ = σ := by
    intro σ
    by_cases hs : Equiv.Perm.sign σ = 1
    · obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
      refine ⟨⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩, ?_⟩
      have := hπα ℓ ℓ.2
      rw [hℓ] at this
      exact this
    · obtain ⟨y, hyJ, hyt⟩ := (D.mem_im).1 htJ
      have hsg : Equiv.Perm.sign (σ * t⁻¹) = 1 := by
        obtain ⟨a, b, hab, rfl⟩ := htsw
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hs
        · rw [h]; decide
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ * t⁻¹, Equiv.Perm.mem_alternatingGroup.mpr hsg⟩
      have hyB : (y : G) ∈ baum S := hJB hyJ
      refine ⟨⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩ * ⟨y, Subgroup.mem_sup_right hyB⟩, ?_⟩
      have h1 := hπα ℓ ℓ.2
      rw [hℓ] at h1
      have h2 : π (⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * ⟨(y : G), y.2⟩) =
          π ⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * π y := by
        rw [← map_mul]
      show π (⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * ⟨(y : G), y.2⟩) = σ
      rw [h2, hyt]
      have h3 : π ⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ = σ * t⁻¹ := h1
      rw [h3]
      exact inv_mul_cancel_right σ t
  have hfsurj : Function.Surjective (D.π.comp (Subgroup.inclusion hHN)) := by
    intro σ
    obtain ⟨x, hx⟩ := hπX σ
    exact ⟨⟨x, hXH x.2⟩, hx⟩
  have hD8 : Nat.card (D.im S) = 8 := burnsideC5h_p3_card_im_S hHN h.sylow D hfsurj
  have hJn : ∀ d ∈ D.im S, ∀ j ∈ D.im (thompsonJ S), d * j * d⁻¹ ∈ D.im (thompsonJ S) := by
    intro d hd j hj'
    obtain ⟨s, hs, rfl⟩ := (D.mem_im).1 hd
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hj'
    have h1 : (s : G) * y * (s : G)⁻¹ ∈ thompsonJ S := burnsideC5h_p3_thompsonJ_conj_mem hs hy
    have : D.π s * D.π y * (D.π s)⁻¹ = D.π (s * y * s⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact D.pi_mem_im (K := thompsonJ S) (y := s * y * s⁻¹) (by simpa using h1)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hswap, hfix⟩ :=
    AppC.swap_core (D.im S) (D.im (thompsonJ S)) hD8 (D.im_mono hJS) hJn hJ1 hJsw
  have hBJ : D.im (baum S) ≤ D.im (thompsonJ S) := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := (D.mem_im).1 hg
    apply hfix
    intro w hw
    set u : ↥(blockU L) := β.symm (Multiplicative.ofAdd w) with hu
    have hwu : Multiplicative.toAdd (β u) = w := by simp [hu]
    have hcJ : ∀ y ∈ thompsonJ S, (y : G) * u = u * y := by
      intro y hy
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := hSN (hJS hy)
      have hmem : y * (u : G) * y⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) hyN) u).mp u.2
      have h := hcomp ⟨y, hyN⟩ u ⟨_, hmem⟩ rfl
      have hfy : A5.Delta5.vact (π ⟨y, hyN⟩) w = w :=
        hw _ (D.pi_mem_im (K := thompsonJ S) hy)
      rw [hwu, hfy] at h
      have h' : Multiplicative.toAdd (β ⟨y * (u : G) * y⁻¹, hmem⟩) =
          Multiplicative.toAdd (β u) := by rw [h, hwu]
      have h2 : (⟨_, hmem⟩ : ↥(blockU L)) = u := β.injective (Multiplicative.toAdd.injective h')
      have h3 : y * (u : G) * y⁻¹ = u := congrArg Subtype.val h2
      calc (y : G) * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h3]
    have huΩ : (u : G) ∈ omegaOneCenterOf (thompsonJ S) :=
      burnsideC5h_p3_mem_omegaOneCenter h u.2 hcJ
    have hbc : (u : G) * b = b * u := Subgroup.mem_centralizer_iff.1 hb.2 u huΩ
    have h := hcomp b u u (by
      show (u : G) = (b : G) * (u : G) * (b : G)⁻¹
      rw [← hbc]; group)
    rw [hwu] at h
    exact h.symm
  have hBeq : D.im (baum S) = D.im (thompsonJ S) := le_antisymm hBJ (D.im_mono hJB)
  refine ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq.trans hJeq, hD8, hswap, ?_, hJn, hfix⟩
  refine eq_top_iff.2 fun σ _ => ?_
  obtain ⟨x, hx⟩ := hπX σ
  exact (D.mem_im).2 ⟨⟨x, hXN x.2⟩, x.2, hx⟩

theorem burnsideC5h_p3_S5 (h : burnsideC5h_p3_Setting L S) :
    ∃ (θ : ↥(L ⊔ baum S) →* Equiv.Perm (Fin 5)) (τ₁ τ₂ : Equiv.Perm (Fin 5)),
      Function.Surjective θ ∧
      θ.ker = (pCoreOf 2 (L ⊔ baum S)).subgroupOf (L ⊔ baum S) ∧
      τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      ((baum S).subgroupOf (L ⊔ baum S)).map θ =
        Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5))) := by
  classical
  have hL : IsShort2 L := h.short
  obtain ⟨α, hα, hαk, -⟩ := h.alt5
  obtain ⟨P, -⟩ := AppC.exists_a5pi hL h.alt5 α hα hαk
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, -, hBeq, -, -, htop, -, -⟩ := burnsideC5h_p3_a5_core h P
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := h.norm
  have hBS : baum S ≤ S := inf_le_left
  have hXN : L ⊔ baum S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (hBS.trans hSN)
  let D : AppC.PiData L := P.toPiData
  have hBX : baum S ≤ L ⊔ baum S := le_sup_right
  have himB : ((baum S).subgroupOf (L ⊔ baum S)).map
      (D.π.comp (Subgroup.inclusion hXN)) = D.im (baum S) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact D.pi_mem_im (K := baum S) (y := Subgroup.inclusion hXN x)
        (Subgroup.mem_subgroupOf.1 hx)
    · intro hg
      obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
      exact ⟨⟨(y : G), hBX hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hX2 : IsPGroup 2 (baum S) := h.sylow.2.1.to_le hBS
  have hXeq : (L ⊔ baum S) ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ baum S) :=
    C1.inf_centralizer_blockU_eq hL le_sup_left hXN
      (fun g hg => C1.exists_pow_mem_of_mem_sup hX2 (hBS.trans hSN) hg)
  refine ⟨D.π.comp (Subgroup.inclusion hXN), τ₁, τ₂, ?_, ?_, hτ₁, hτ₂, hdisj, ?_⟩
  · intro σ
    have hσ : σ ∈ D.im (L ⊔ baum S) := by rw [htop]; trivial
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hσ
    exact ⟨⟨(y : G), hy⟩, rfl⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hXeq]
    constructor
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have h1 : (x : G) * u * (x : G)⁻¹ = u := (D.hker (Subgroup.inclusion hXN x)).1 hx u hu
      calc u * (x : G) = ((x : G) * u * (x : G)⁻¹) * x := by rw [h1]
        _ = x * u := by group
    · rintro ⟨-, hxc⟩
      apply (D.hker (Subgroup.inclusion hXN x)).2
      intro u hu
      have h1 := Subgroup.mem_centralizer_iff.1 hxc u hu
      calc (x : G) * u * (x : G)⁻¹ = (u * x) * (x : G)⁻¹ := by rw [h1]
        _ = u := by group
  · rw [himB, hBeq]

theorem burnsideC5h_p3_baum_facts (h : burnsideC5h_p3_Setting L S) :
    baum S ≤ S ∧ baum S ≤ Subgroup.normalizer (L : Set G) ∧ IsPGroup 2 (baum S) ∧
      L ⊔ baum S ≤ Subgroup.normalizer (L : Set G) ∧ L ⊔ baum S ≤ L ⊔ S :=
  have hBS : baum S ≤ S := inf_le_left
  ⟨hBS, hBS.trans h.norm, h.sylow.2.1.to_le hBS,
    sup_le Subgroup.le_normalizer (hBS.trans h.norm), sup_le_sup_left hBS L⟩

theorem burnsideC5h_p3_Q_le_S (h : burnsideC5h_p3_Setting L S) :
    pCoreOf 2 (L ⊔ baum S) ≤ S := by
  obtain ⟨hBS, hBN, hB2, hXN, hXH⟩ := burnsideC5h_p3_baum_facts h
  have hXQ : L ⊔ baum S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ baum S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hSX : S ≤ Subgroup.normalizer ((L ⊔ baum S : Subgroup G) : Set G) := fun g hg =>
    C1.mem_normalizer_sup (h.norm hg)
      (CFSG.Quasithin.normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg))
  have hQH : pCoreOf 2 (L ⊔ baum S) ≤ L ⊔ S :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans hXH
  have hHQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ baum S) : Set G) := by
    refine sup_le (le_sup_left.trans hXQ) fun g hg => ?_
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ baum S) (hSX hg)
  have := C1.le_pCoreOf_of_normalized hQH hHQ
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact this.trans h.sylow.pCoreOf_le

theorem burnsideC5h_p3_alpha_le_centralizer (h : burnsideC5h_p3_Setting L S)
    (D : AppC.PiData L) :
    omegaOneCenterOf (thompsonJ S) ≤ Subgroup.centralizer (blockU L : Set G) := by
  classical
  have hL := h.short
  have hSN := h.norm
  have hUS : blockU L ≤ S := burnsideC5h_p3_blockU_le h
  have hU := AppC.isElemAbelian_blockU hL
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hA.1.trans hSN
  set K := A ⊓ Subgroup.centralizer (blockU L : Set G) with hK
  have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hcomm : ∀ k ∈ K, ∀ u ∈ blockU L, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe hU hcomm
  have hB1S : K ⊔ blockU L ≤ S := sup_le (inf_le_left.trans hA.1) hUS
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K ⊓ blockU L) ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA.2.1 ha hx.1.1
  have h4 := D.card_im_mul hAN
  have h5 := D.card_fix hAN
  have h6 := D.card_blockU
  have hle := AppC.card_mul_fix_le (D.im A) (D.im_elemAbelian hA.2.1).1
    (D.im_elemAbelian hA.2.1).2
  rw [h5] at h3
  have hcpos : 0 < Nat.card ↥(K ⊓ blockU L) := Nat.card_pos
  set p := Nat.card (D.im A)
  set f := Nat.card (AppC.FixΔ (D.im A))
  have hAle : Nat.card A ≤ Nat.card ↥(K ⊔ blockU L) := by
    have hf : 0 < f := lt_of_lt_of_le hcpos h3
    refine Nat.le_of_mul_le_mul_right ?_ hf
    calc Nat.card A * f = (p * Nat.card ↥K) * f := by rw [h4]
      _ = Nat.card ↥K * (p * f) := by ring
      _ ≤ Nat.card ↥K * 16 := Nat.mul_le_mul_left _ hle
      _ = Nat.card ↥(K ⊔ blockU L) * Nat.card ↥(K ⊓ blockU L) := by rw [h2, h6]
      _ ≤ Nat.card ↥(K ⊔ blockU L) * f := Nat.mul_le_mul_left _ h3
  have hmax : IsMaxElemAbelian S (K ⊔ blockU L) :=
    ⟨hB1S, hB1e, fun B hB hBe => (hA.2.2 B hB hBe).trans hAle⟩
  have hα : omegaOneCenterOf (thompsonJ S) ≤ K ⊔ blockU L :=
    ((omegaOne_centralizer_thompsonJ S).2).le.trans (iInf₂_le (K ⊔ blockU L) hmax)
  refine hα.trans (sup_le inf_le_right fun u hu => ?_)
  exact Subgroup.mem_centralizer_iff.2 fun v hv => B2F.isElemAbelian_comm hU hv hu

theorem burnsideC5h_p3_Q_structure (h : burnsideC5h_p3_Setting L S) (D : AppC.PiData L) :
    pCoreOf 2 (L ⊔ baum S) ≤ baum S ∧
    ∃ T : Subgroup G, IsSylowTwoOf T (L ⊔ baum S) ∧ baum S ≤ T ∧
      pCoreOf 2 (L ⊔ baum S) = blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      blockU L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
  classical
  have hL := h.short
  obtain ⟨hBS, hBN, hB2, hXN, hXH⟩ := burnsideC5h_p3_baum_facts h
  have hJB : thompsonJ S ≤ baum S := C5.thompsonJ_le_baum' S
  have hXeq : (L ⊔ baum S) ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ baum S) :=
    C1.inf_centralizer_blockU_eq hL le_sup_left hXN
      (fun g hg => C1.exists_pow_mem_of_mem_sup hB2 hBN hg)
  have hαC := burnsideC5h_p3_alpha_le_centralizer h D
  have hαJ : omegaOneCenterOf (thompsonJ S) ≤ thompsonJ S := Setup.omegaOneCenterOf_le _
  have hαQ : omegaOneCenterOf (thompsonJ S) ≤ pCoreOf 2 (L ⊔ baum S) := by
    rw [← hXeq]
    exact le_inf (hαJ.trans (hJB.trans le_sup_right)) hαC
  have hαcent : ∀ a ∈ omegaOneCenterOf (thompsonJ S), ∀ j ∈ thompsonJ S, j * a = a * j := by
    intro a ha j hj
    have hz : omegaOneCenterOf (thompsonJ S) ≤ centerOf (thompsonJ S) := by
      show omegaOneOf (centerOf (thompsonJ S)) ≤ centerOf (thompsonJ S)
      exact (Subgroup.closure_le _).mpr fun x hx => hx.1
    exact Subgroup.mem_centralizer_iff.mp (hz ha).2 j hj
  obtain ⟨T, hT, hBT⟩ := B6.exists_isSylowTwoOf_ge hB2 (le_sup_right : baum S ≤ L ⊔ baum S)
  have hLT : L ⊔ T = L ⊔ baum S :=
    le_antisymm (sup_le le_sup_left hT.1) (sup_le_sup_left hBT L)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hT.1.trans hXN
  have hT' : IsSylowTwoOf T (L ⊔ T) := by rw [hLT]; exact hT
  obtain ⟨hQ, hUD, -⟩ :=
    CFSG.Quasithin.H13.VolI.asC113c_holds G L T hT' hTN hL 5 (Or.inr rfl) h.alt5
  rw [hLT] at hQ
  have hUL : blockU L ≤ L := Setup.Campbell.blockU_le_self_of_isShort2 hL
  have hDC : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (blockU L : Set G) :=
    fun d hd => Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subgroup.mem_centralizer_iff.mp hd.2 y (hUL hy)
  have hDN : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) :=
    hDC.trans (Subgroup.centralizer_le_normalizer _)
  have hdec : ∀ a ∈ pCoreOf 2 (L ⊔ baum S), ∃ u ∈ blockU L,
      ∃ d ∈ T ⊓ Subgroup.centralizer (L : Set G), a = u * d := by
    intro a ha
    rw [hQ, sup_comm] at ha
    obtain ⟨d, hd, u, hu, rfl⟩ := C5.mem_sup_of_le_normalizer hDN ha
    refine ⟨u, hu, d, hd, ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hDC hd) u hu).symm
  have hmain : ∀ a ∈ omegaOneCenterOf (thompsonJ S), ∀ q ∈ pCoreOf 2 (L ⊔ baum S),
      q * a = a * q := by
    intro a ha q hq
    obtain ⟨u, hu, d, hd, rfl⟩ := hdec a (hαQ ha)
    have hu' : ∀ j ∈ thompsonJ S, j * u * j⁻¹ = u := by
      intro j hj
      have hjN : j ∈ Subgroup.normalizer (L : Set G) := h.norm (GammaExtra.thompsonJ_le_self S hj)
      have hjT : j ∈ T := hBT (hJB hj)
      have hjU : j * u * j⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) hjN) u).mp hu
      have hjD : j * d * j⁻¹ ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨mul_mem (mul_mem hjT hd.1) (Subgroup.inv_mem _ hjT),
          Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
        have hl' : j⁻¹ * l * j ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hjN) l).mp hl
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hd.2 _ hl'
        calc l * (j * d * j⁻¹) = j * ((j⁻¹ * l * j) * d) * j⁻¹ := by group
          _ = j * (d * (j⁻¹ * l * j)) * j⁻¹ := by rw [h1]
          _ = (j * d * j⁻¹) * l := by group
      have hja : j * (u * d) * j⁻¹ = u * d := by
        have := hαcent _ ha j hj
        calc j * (u * d) * j⁻¹ = (u * d) * j * j⁻¹ := by rw [this]
          _ = u * d := by group
      have hmem : (j * u * j⁻¹)⁻¹ * u ∈ blockU L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) := by
        refine ⟨mul_mem (Subgroup.inv_mem _ hjU) hu, ?_⟩
        have e : (j * u * j⁻¹)⁻¹ * u = (j * d * j⁻¹) * d⁻¹ := by
          have e2 : (j * u * j⁻¹) * (j * d * j⁻¹) = u * d := by
            rw [← hja]; group
          calc (j * u * j⁻¹)⁻¹ * u = (j * u * j⁻¹)⁻¹ * (u * d) * d⁻¹ := by group
            _ = (j * u * j⁻¹)⁻¹ * ((j * u * j⁻¹) * (j * d * j⁻¹)) * d⁻¹ := by rw [e2]
            _ = (j * d * j⁻¹) * d⁻¹ := by group
        rw [e]
        exact mul_mem hjD (Subgroup.inv_mem _ hd)
      rw [hUD, Subgroup.mem_bot] at hmem
      exact inv_mul_eq_one.mp hmem
    have huα : u ∈ omegaOneCenterOf (thompsonJ S) :=
      burnsideC5h_p3_mem_omegaOneCenter h hu fun y hy => by
        have := hu' y hy
        calc y * u = (y * u * y⁻¹) * y := by group
          _ = u * y := by rw [this]
    have hdα : d ∈ omegaOneCenterOf (thompsonJ S) := by
      have h1 : u⁻¹ * (u * d) ∈ omegaOneCenterOf (thompsonJ S) :=
        mul_mem (Subgroup.inv_mem _ huα) ha
      simpa using h1
    have hXd : L ⊔ baum S ≤ Subgroup.centralizer ({d} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp hd.2 l hl).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp hb.2 y hdα)
    have hqX : q ∈ L ⊔ baum S := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _) hq
    have hqd : d * q = q * d := Subgroup.mem_centralizer_iff.mp (hXd hqX) d rfl
    have hqU : u * q = q * u := by
      have : q ∈ (L ⊔ baum S) ⊓ Subgroup.centralizer (blockU L : Set G) := by rw [hXeq]; exact hq
      exact Subgroup.mem_centralizer_iff.mp this.2 u hu
    calc q * (u * d) = (q * u) * d := by group
      _ = (u * q) * d := by rw [hqU]
      _ = u * (q * d) := by group
      _ = u * (d * q) := by rw [hqd]
      _ = (u * d) * q := by group
  refine ⟨?_, T, hT, hBT, hQ, hUD⟩
  intro q hq
  exact ⟨(burnsideC5h_p3_Q_le_S h) hq, Subgroup.mem_centralizer_iff.2 fun a ha =>
    (hmain a ha q hq).symm⟩

theorem burnsideC5h_p3_swap_fix :
    ∀ a c d : Fin 5, c ≠ d → Equiv.swap c d a = a → a ≠ c ∧ a ≠ d := by
  decide +kernel

theorem burnsideC5h_p3_swap_disjoint {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d)
    (h : (Equiv.swap a b).Disjoint (Equiv.swap c d)) : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have ha := h a
  have hb := h b
  rw [Equiv.swap_apply_left] at ha
  rw [Equiv.swap_apply_right] at hb
  have ha' : Equiv.swap c d a = a := ha.resolve_left hab.symm
  have hb' : Equiv.swap c d b = b := hb.resolve_left hab
  obtain ⟨h1, h2⟩ := burnsideC5h_p3_swap_fix a c d hcd ha'
  obtain ⟨h3, h4⟩ := burnsideC5h_p3_swap_fix b c d hcd hb'
  exact ⟨h1, h2, h3, h4⟩

theorem burnsideC5h_p3_main (h : burnsideC5h_p3_Setting L S) :
    ((pCoreOf 2 (L ⊔ baum S) = blockU L ⊔ (baum S ⊓ Subgroup.centralizer (L : Set G)) ∧
        blockU L ⊓ (baum S ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
        blockU L ≤ Subgroup.centralizer ((baum S ⊓ Subgroup.centralizer (L : Set G) :
          Subgroup G) : Set G)) ∧
      pCoreOf 2 (L ⊔ baum S) ≤ baum S ∧
      ∃ φ : ↥(L ⊔ baum S) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
        φ.ker = CFSG.pCore 2 ↥(L ⊔ baum S) ∧
        ∃ a b c d : Fin 5, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
          ((baum S).subgroupOf (L ⊔ baum S)).map φ =
            Subgroup.closure {Equiv.swap a b, Equiv.swap c d}) ∧
    (blockU L ≤ pCoreOf 2 (L ⊔ baum S) ∧
      pCoreOf 2 (L ⊔ baum S) = baum S ⊓ Subgroup.centralizer (blockU L : Set G)) := by
  classical
  have hL := h.short
  obtain ⟨α, hα, hαk, -⟩ := h.alt5
  obtain ⟨P, -⟩ := AppC.exists_a5pi hL h.alt5 α hα hαk
  obtain ⟨hQB, T, hT, hBT, hQ, hUD⟩ := burnsideC5h_p3_Q_structure h P.toPiData
  obtain ⟨θ, τ₁, τ₂, hθs, hθk, hτ₁, hτ₂, hdisj, himg⟩ := burnsideC5h_p3_S5 h
  obtain ⟨hBS, hBN, hB2, hXN, hXH⟩ := burnsideC5h_p3_baum_facts h
  have hUL : blockU L ≤ L := Setup.Campbell.blockU_le_self_of_isShort2 hL
  have hXeq : (L ⊔ baum S) ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ baum S) :=
    C1.inf_centralizer_blockU_eq hL le_sup_left hXN
      (fun g hg => C1.exists_pow_mem_of_mem_sup hB2 hBN hg)
  have hDT :
      baum S ⊓ Subgroup.centralizer (L : Set G) = T ⊓ Subgroup.centralizer (L : Set G) := by
    refine le_antisymm (inf_le_inf_right _ hBT) fun d hd => ⟨hQB ?_, hd.2⟩
    rw [hQ]
    exact Subgroup.mem_sup_right hd
  have hUQ : blockU L ≤ pCoreOf 2 (L ⊔ baum S) := by
    refine C1.le_pCoreOf_of_normalized (hUL.trans le_sup_left) ?_ (C1.isPGroup_blockU hL)
    exact sup_le (C1.le_normalizer_blockU L) fun g hg => C1.mem_normalizer_blockU (hBN hg)
  refine ⟨⟨⟨?_, ?_, ?_⟩, hQB, ?_⟩, hUQ, ?_⟩
  · rw [hDT]; exact hQ
  · rw [hDT]; exact hUD
  · exact fun u hu => Subgroup.mem_centralizer_iff.2 fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hx.2 u (hUL hu)).symm
  · refine ⟨θ, hθs, hθk.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf 2 _), ?_⟩
    obtain ⟨a, b, hab, rfl⟩ := hτ₁
    obtain ⟨c, d, hcd, rfl⟩ := hτ₂
    obtain ⟨h1, h2, h3, h4⟩ := burnsideC5h_p3_swap_disjoint hab hcd hdisj
    exact ⟨a, b, c, d, hab, h1, h2, h3, h4, hcd, himg⟩
  · apply le_antisymm
    · intro g hg
      refine ⟨hQB hg, ?_⟩
      have : g ∈ (L ⊔ baum S) ⊓ Subgroup.centralizer (blockU L : Set G) := by
        rw [hXeq]; exact hg
      exact this.2
    · intro g hg
      rw [← hXeq]
      exact ⟨(le_sup_right : baum S ≤ L ⊔ baum S) hg.1, hg.2⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p3_sylow {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G} (hKi : Ki ∈ conjSubgroupsBy TH K₁) :
    IsSylowTwoOf (R ⊓ Subgroup.normalizer (Ki : Set G))
      (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G))) := by
  classical
  have hyp1 := hset.hyp1
  have cfg := hset.config
  set K : Subgroup G := oTwoUpper H with hKdef
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hRH : R ≤ H := hyp1.R_le.trans hyp1.sylow.1
  have hRN : R ≤ Subgroup.normalizer (K : Set G) := hRH.trans hHK
  have hRK : IsSylowTwoOf R (K ⊔ R) := by
    have := hyp1.sylow_R
    rwa [sup_comm] at this
  have hKiK : Ki ≤ K := burnsideC5h_c54_conj_le cfg hKi
  have hKN : K ≤ Subgroup.normalizer (Ki : Set G) := by
    obtain ⟨t₀, ht₀, rfl⟩ := hKi
    rw [hKdef, cfg.prod]
    refine iSup₂_le fun t ht => ?_
    by_cases heq : conjByElt t K₁ = conjByElt t₀ K₁
    · rw [heq]
      exact Subgroup.le_normalizer
    · exact (cfg.commute t ht t₀ ht₀ heq).trans (Subgroup.centralizer_le_normalizer _)
  have hRKsyl : IsSylowTwoOf (R ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hRK le_sup_left (sup_le Subgroup.le_normalizer hRN)
  have hle1 : R ⊓ K ≤ Ki ⊔ (R ⊓ K) := le_sup_right
  have hle2 : Ki ⊔ (R ⊓ K) ≤ K := sup_le hKiK inf_le_right
  have hsyl1 : IsSylowTwoOf (R ⊓ K) (Ki ⊔ (R ⊓ K)) := B6.isSylowTwoOf_mono hRKsyl hle1 hle2
  have hsyl2 : IsSylowTwoOf ((R ⊓ K) ⊓ Ki) Ki :=
    B6.isSylowTwoOf_inf_normal hsyl1 le_sup_left (hle2.trans hKN)
  have hRKi : (R ⊓ K) ⊓ Ki = R ⊓ Ki := by
    rw [inf_assoc, inf_eq_right.mpr hKiK]
  set Ri : Subgroup G := R ⊓ Subgroup.normalizer (Ki : Set G) with hRi
  have hRiN : Ri ≤ Subgroup.normalizer (Ki : Set G) := inf_le_right
  have hRiKi : Ri ⊓ Ki = R ⊓ Ki := by
    rw [hRi, inf_assoc, inf_eq_right.mpr
      (Subgroup.le_normalizer : Ki ≤ Subgroup.normalizer (Ki : Set G))]
  have hidx := B6.relIndex_inf_eq_relIndex_sup hRiN
  rw [hRiKi, sup_comm] at hidx
  refine ⟨le_sup_right, hyp1.sylow.2.1.to_le (inf_le_left.trans hyp1.R_le), ?_⟩
  rw [hRKi] at hsyl2
  have hodd : ¬ 2 ∣ (R ⊓ Ki).relIndex Ki := hsyl2.2.2
  rw [hidx] at hodd
  exact hodd

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p3_a5_of_sylow (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hsyl : ∀ Ki ∈ conjSubgroupsBy TH K₁,
      IsSylowTwoOf (R ⊓ Subgroup.normalizer (Ki : Set G))
        (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G)))) :
    ∀ Ki ∈ conjSubgroupsBy TH K₁, IsAltType Ki 5 →
      ((pCoreOf 2 (Ki ⊔ baum R) = blockU Ki ⊔ (baum R ⊓ Subgroup.centralizer (Ki : Set G)) ∧
          blockU Ki ⊓ (baum R ⊓ Subgroup.centralizer (Ki : Set G)) = ⊥ ∧
          blockU Ki ≤ Subgroup.centralizer ((baum R ⊓ Subgroup.centralizer (Ki : Set G) :
            Subgroup G) : Set G)) ∧
        pCoreOf 2 (Ki ⊔ baum R) ≤ baum R ∧
        ∃ φ : ↥(Ki ⊔ baum R) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
          φ.ker = CFSG.pCore 2 ↥(Ki ⊔ baum R) ∧
          ∃ a b c d : Fin 5, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            ((baum R).subgroupOf (Ki ⊔ baum R)).map φ =
              Subgroup.closure {Equiv.swap a b, Equiv.swap c d}) ∧
      (blockU Ki ≤ pCoreOf 2 (Ki ⊔ baum R) ∧
        pCoreOf 2 (Ki ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU Ki : Set G)) := by
  classical
  intro Ki hKi h5
  have hyp1 := hset.hyp1
  have cfg := hset.config
  have hshort : IsShort2 Ki := (burnsideC5h_c54_isBlock2 hset hKi).1
  set Ri : Subgroup G := R ⊓ Subgroup.normalizer (Ki : Set G) with hRi
  have hS1 : baum R ≤ Subgroup.normalizer (Ki : Set G) := burnsideC5h_c54_one h116 hset Ki hKi
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hSRi : baum R ≤ Ri := le_inf hSR hS1
  have hJRi : thompsonJ R ≤ Ri := (C5.thompsonJ_le_baum' R).trans hSRi
  have hRiR : Ri ≤ R := inf_le_left
  have hJeq : thompsonJ Ri = thompsonJ R := burnsideC5h_p2_thompsonJ_eq hJRi hRiR
  have hbeq : baum Ri = baum R := burnsideC5h_p2_baum_eq hJRi hRiR hSRi
  have hth : ⁅Ki, thompsonJ Ri⁆ = Ki := by
    rw [hJeq]
    obtain ⟨t, ht, rfl⟩ := hKi
    refine burnsideC5h_p2_comm_conj cfg.comm_J ?_
    exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ R
      (hyp1.TH_le.trans hyp1.R_norm ht)
  have hmain := burnsideC5h_p3_main
    (⟨hshort, h5, inf_le_right, hsyl Ki hKi, hth⟩ : burnsideC5h_p3_Setting Ki Ri)
  rw [hbeq] at hmain
  exact hmain

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_p3_a5_unconditional (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) :
    ∀ Ki ∈ conjSubgroupsBy TH K₁, IsAltType Ki 5 →
      ((pCoreOf 2 (Ki ⊔ baum R) = blockU Ki ⊔ (baum R ⊓ Subgroup.centralizer (Ki : Set G)) ∧
          blockU Ki ⊓ (baum R ⊓ Subgroup.centralizer (Ki : Set G)) = ⊥ ∧
          blockU Ki ≤ Subgroup.centralizer ((baum R ⊓ Subgroup.centralizer (Ki : Set G) :
            Subgroup G) : Set G)) ∧
        pCoreOf 2 (Ki ⊔ baum R) ≤ baum R ∧
        ∃ φ : ↥(Ki ⊔ baum R) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
          φ.ker = CFSG.pCore 2 ↥(Ki ⊔ baum R) ∧
          ∃ a b c d : Fin 5, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            ((baum R).subgroupOf (Ki ⊔ baum R)).map φ =
              Subgroup.closure {Equiv.swap a b, Equiv.swap c d}) ∧
      (blockU Ki ≤ pCoreOf 2 (Ki ⊔ baum R) ∧
        pCoreOf 2 (Ki ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU Ki : Set G)) :=
  burnsideC5h_p3_a5_of_sylow h116 hset fun _ hKi => burnsideC5h_p3_sylow hset hKi

end Stage1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5h_c54_isChi0Block {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G} (hKi : Ki ∈ conjSubgroupsBy TH K₁) :
    IsChi0Block H Ki := by
  obtain ⟨t, ht, rfl⟩ := hKi
  exact A5.G3.isChi0Block_conj hset.config.chi0 (hset.hyp1.sylow.1 ht)

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_5_4
    : C_5_4 := by
  intro G _ _ H M₀ TH R K₁ hset
  have h116 : C_1_16 := as_C_1_16
  have hS := burnsideC5h_c54_one h116 hset
  have hP1 := burnsideC5h_p1_minParabolic hset hS
  have hP2 := burnsideC5h_p2_lin2A3 h116 hset hP1
  have hP3 := burnsideC5h_p3_a5_unconditional h116 hset
  refine ⟨fun Ki hKi => ⟨hS Ki hKi, ?_, ?_, ?_⟩,
    burnsideC5h_c54_four_second as_C_1_11 hset⟩
  · intro hL
    obtain ⟨a, b, c, -⟩ := hP2 Ki hKi hL
    exact ⟨a, b, c⟩
  · intro h5
    exact (hP3 Ki hKi h5).1
  · rcases (burnsideC5h_c54_isChi0Block hset hKi).2 with h | h | h
    · exact (hP2 Ki hKi (Or.inl h)).2.2.2
    · exact (hP2 Ki hKi (Or.inr h)).2.2.2
    · exact (hP3 Ki hKi h).2

end

end CFSG.ASVolI
