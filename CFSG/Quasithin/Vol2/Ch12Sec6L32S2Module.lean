module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs
public import CFSG.Quasithin.H13.A6S13821zz31
public import CFSG.Quasithin.Background.F918C8
public import CFSG.Quasithin.EmptyFaithful.F918C5
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.A6S13821zz27
public import CFSG.Quasithin.H13.A6S1385b

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.A6

attribute [local instance] commGroupOfFact

theorem isQuasisimple_KQ {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}
    (h : HypF918 T V L V₁ Vp H K) : CFSG.IsQuasisimple (KQ K) := by
  have e : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq e)
    h.K_quasisimple

theorem leafModule_of_inputs
    (inp : Inputs32) : LeafModule inp := by
  classical
  intro G _ _ T L V _ F H K h hSQ hK₀ hker hPSL hZ hHKT'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hTH : T ≤ H := h.T_le_H
  have hq := isQuasisimple_KQ h
  have hcQZ := A5.card_of_isPSL34 hPSL
  have hcQ : Nat.card (KQ K) = 20160 * Nat.card (Subgroup.center (KQ K)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (KQ K)), hcQZ]
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU h
  have hirrT := isIrrPlusTildeT_of_ambient h hIU W hW hirrU
  have hFe := factElem h hIU
  have hirr' : subM F.V1 (conjClosure I H) I ∈
      IrrPlusOn (autIH F.V1 I H (conjClosure K T))
        (orbSup (autIH F.V1 I H T) (subM F.V1 (conjClosure I H) I))
        (autIH F.V1 I H T) := hirrT
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hne : autIH F.V1 I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  have hker0 : CFSG.pCore 2 ↥K ≤ (toAutI h I).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    apply h.actH_eq_one_of_mem_pCoreOf hIU
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
      assumption
    have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hx1
  let φ : KQ K →* ↥(autIH F.V1 I H K) := QuotientGroup.lift _ (toAutI h I) hker0
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := toAutI_surjective h I y
    exact ⟨QuotientGroup.mk x, hx⟩
  have : Nontrivial ↥(autIH F.V1 I H K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨⟨eZ⟩, hdZ⟩ := A6S20.quotCenter_of_surjective hq hφs
  have hL'34 : IsPSL 3 2 2 (↥(autIH F.V1 I H K) ⧸ Subgroup.center ↥(autIH F.V1 I H K)) :=
    IsPSL.of_mulEquiv eZ hPSL
  have hDD := d31_of_hyp h hSQ hIU hV₁I hirr'
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  have hMp : autIH F.V1 I H (conjClosure K T) = autIH F.V1 I H K := by rw [hK₀]
  have hD3 : D3Std (autIH F.V1 I H H) (autIH F.V1 I H (conjClosure K T))
      (autIH F.V1 I H T) (autIH F.V1 I H K) (subM F.V1 (conjClosure I H) I) :=
    ⟨hDD, hA.qhat_VT hDD.exp, hirr'⟩
  have hqM := hA.qhat_M hDD.sylow.1
  have hq2 := hA.qOf_VT hDD.exp
  have hdZ3 : Nat.card (Subgroup.center ↥(autIH F.V1 I H K)) ∣ 3 := hdZ.trans hZ
  have hZ3 : Nat.card (Subgroup.center (KQ K)) = 3 ∧
      Nat.card ↥(autIH F.V1 I H K) = 60480 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autIH F.V1 I H K))
    rw [A5.card_of_isPSL34 hL'34] at hc
    rcases (Nat.dvd_prime Nat.prime_three).mp hdZ3 with h1 | h1
    · exfalso
      have hb : Subgroup.center ↥(autIH F.V1 I H K) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      let e2 : ↥(autIH F.V1 I H K) ≃*
          (↥(autIH F.V1 I H K) ⧸ Subgroup.center ↥(autIH F.V1 I H K)) :=
        QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hb.symm)
      exact A5.false_of_insp4_L34 inp.a21 inp.g2 inp.b42 inp.b45 inp.d310 hD3 hMp hqM hq2
        (IsPSL.of_mulEquiv e2.symm hL'34)
    · rw [h1] at hc hdZ
      exact ⟨Nat.dvd_antisymm hZ hdZ, hc⟩
  obtain ⟨hZQ3, hcL⟩ := hZ3
  have hcQ' : Nat.card (KQ K) = 60480 := by rw [hcQ, hZQ3]
  have hkerK : ∀ k ∈ K, (∀ u ∈ conjClosure I H, k * u * k⁻¹ * u⁻¹ ∈ F.V1) →
      k ∈ pCoreOf 2 H := by
    intro k hk hku
    have hFU := factElem h (le_conjClosure F.V5 H)
    have hsU : Function.Surjective (toAutI h F.V5) := toAutI_surjective h F.V5
    have hsI : Function.Surjective (toAutI h I) := toAutI_surjective h I
    have hcU : Nat.card ↥(autIH F.V1 F.V5 H K) = 60480 := by
      rw [← hcQ']
      exact Nat.card_congr ((QuotientGroup.quotientKerEquivOfSurjective _ hsU).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker)).toEquiv
    have hkerU : ∀ x : ↥K, toAutI h F.V5 x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
      intro x
      rw [toAutI_eq_one_iff]
      exact ⟨fun hx => mem_pCoreOf_of_actH_eq_one h hx,
        fun hx => h.actH_eq_one_of_mem_pCoreOf (le_conjClosure F.V5 H) hx⟩
    have hle : (toAutI h F.V5).ker ≤ (toAutI h I).ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [toAutI_eq_one_iff]
      exact h.actH_eq_one_of_mem_pCoreOf hIU ((hkerU x).mp hx)
    have hidx : (toAutI h F.V5).ker.index = (toAutI h I).ker.index := by
      rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsU,
        MonoidHom.range_eq_top.mpr hsI, Subgroup.card_top, Subgroup.card_top, hcU, hcL]
    have heq : (toAutI h F.V5).ker = (toAutI h I).ker := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      have h2 := (toAutI h F.V5).ker.card_mul_index
      have h3 := (toAutI h I).ker.card_mul_index
      rw [hidx] at h2
      have hpos : 0 < (toAutI h I).ker.index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact (Nat.eq_of_mul_eq_mul_right hpos (h2.trans h3.symm)).symm.le
    have hkI : toAutI h I ⟨k, hk⟩ = 1 := by
      rw [toAutI_eq_one_iff, A6Tv.actH_eq_one_iff h.H_le_normalizer_V₁
        (h.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H)]
      exact hku
    have hkU : (⟨k, hk⟩ : ↥K) ∈ (toAutI h F.V5).ker := by
      rw [heq]
      exact hkI
    exact (hkerU _).mp hkU
  refine ⟨I, hV₁I, hIU, ?_, hKI', hZQ3, hkerK, ?_⟩
  · have := isIrrPlusTilde_of_module h hV₁I hIU hirrT
    rwa [hK₀] at this
  have hW2 : ∀ w : ↥(tildeOf F.V1 (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by
      simpa using (Fact.out : IsElemAbelian 2 (tildeOf F.V1 (conjClosure I H))).2 w w.2)
  have hcomm : commV (autIH F.V1 I H K) = ⊤ := A6S20.commV_eq_top_of_d31 hDD hMp
  have hVinv : ∀ l ∈ autIH F.V1 I H K, ∀ v ∈ subM F.V1 (conjClosure I H) I,
      l v ∈ subM F.V1 (conjClosure I H) I := fun l hl v hv =>
    (insp5a_le_stabSub hDD hl v).2 hv
  have hTL : ∀ a ∈ autIH F.V1 I H T, ∀ l ∈ autIH F.V1 I H K,
      a * l * a⁻¹ ∈ autIH F.V1 I H K := by
    intro a ha l hl
    rw [autIH_eq_map h hTH] at ha
    rw [autIH_eq_map h hKH] at hl ⊢
    obtain ⟨t', ht', rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := hl
    refine ⟨t' * k * t'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hK₀n : H ≤ Subgroup.normalizer (K : Set G) := by
      have h0 := h.K₀_normal
      rwa [hK₀] at h0
    exact (Subgroup.mem_normalizer_iff.mp (hK₀n (hTH (Subgroup.mem_subgroupOf.mp ht'))) _).mp
      (Subgroup.mem_subgroupOf.mp hk)
  have hTL' : ∀ a ∈ autIH F.V1 I H T, ∀ l ∈ autIH F.V1 I H K,
      a⁻¹ * l * a ∈ autIH F.V1 I H K := by
    intro a ha l hl
    have h1 := hTL a⁻¹ ((autIH F.V1 I H T).inv_mem ha) l hl
    simpa using h1
  have hC0 : ∀ z ∈ autIH F.V1 I H K, z ^ 3 = 1 →
      (∀ l ∈ autIH F.V1 I H K, z * l = l * z) →
      (∀ w, z w * w⁻¹ ∈ fixV (autIH F.V1 I H K) → w ∈ fixV (autIH F.V1 I H K)) →
      fixV (autIH F.V1 I H K) = ⊥ := fun z hzL hz3 hzc hfp =>
    A6S20.fixV_eq_bot_of_scalar hW2 hcomm hzL hz3 hzc hfp
  have hnatural : H ≤ Subgroup.normalizer (I : Set G) →
      BinaryNaturalSL (autIH F.V1 I H K) ⊤ ⊥ 3 2 := by
    intro hHI
    have hMst : autIH F.V1 I H H ≤ stabSub (subM F.V1 (conjClosure I H) I) := by
      rw [autIH_eq_map h (le_refl H)]
      exact (map_actH_le_stabSub_iff h.H_le_normalizer_V₁
        (h.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I).mpr hHI
    have hVtop : subM F.V1 (conjClosure I H) I = ⊤ := by
      have hgen := hDD.gen
      rw [eq_top_iff, ← hgen]
      refine iSup₂_le fun m hm => ?_
      rintro _ ⟨v, hv, rfl⟩
      exact (hMst hm v).2 hv
    have hTle : autIH F.V1 I H T ≤ autIH F.V1 I H H := by
      rw [autIH_eq_map h hTH, autIH_eq_map h (le_refl H)]
      exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr (hTH
        (Subgroup.mem_subgroupOf.mp hx)))
    have hfaith : autIH F.V1 I H K ⊓ centSub (subM F.V1 (conjClosure I H) I) = ⊥ := by
      rw [hVtop]
      refine eq_bot_iff.2 fun g hg => ?_
      have : g = 1 := MulEquiv.ext fun u => hg.2 u trivial
      exact this ▸ Subgroup.one_mem _
    have hnat := A6S20.natural_sl34_of_d3Std inp.a21 hD3 hMp (hTle.trans hMst) hfaith hcL hL'34
    rw [hVtop, top_inf_eq] at hnat
    obtain ⟨z, hzL, hz3, hzc, hfp⟩ := A6S20.exists_scalar_sl34 hnat
    rw [hC0 z hzL hz3 hzc fun w hw => hfp w trivial hw] at hnat
    exact hnat
  have hF4 := (F918_4' h hSQ hK₀ hV₁I hIU W hW hirrU inp.d310 inp.d391 inp.insp4).2
  rcases hF4 with hHI | (⟨hVT, -⟩ | h3)
  ·
    exact Or.inl ⟨hHI, hnatural hHI⟩
  ·
    have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
      intro t' ht'
      have hst := stab_of_orbSup_eq hVT.symm _ (actH_mem_autIH_of_mem (I := I) h hTH ht')
      exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁
        (h.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
        (le_conjClosure I H) ⟨t', hTH ht'⟩).mp hst
    have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
      rw [hHKT' hZQ3]
      exact sup_le hKI' hTI
    exact Or.inl ⟨hHI, hnatural hHI⟩
  ·
    right
    obtain ⟨hfirst, ⟨t, htT, htns⟩, hrest⟩ := h3
    obtain ⟨hsum, hniso⟩ := hrest t htT htns
    have hnat := A6S20.natural_sl34_of_d310Two hcL hfirst
    obtain ⟨z, hzL, hz3, hzc, hfp⟩ := A6S20.exists_scalar_sl34 hnat
    set Vs := subM F.V1 (conjClosure I H) I with hVs
    set Lk := autIH F.V1 I H K with hLk
    set C := fixV Lk with hCdef
    have hzC : ∀ c ∈ C, z c = c := fun c hc => hc z hzL
    have hz1 : z ≠ 1 := by
      intro h1
      apply (lt_iff_le_not_ge.mp hirr'.1.2.2.2.1).2
      intro v hv
      have h2 := hfp v hv (by
        rw [h1, MulAut.one_apply, mul_inv_cancel]
        exact Subgroup.one_mem _)
      exact ⟨hv, fun a => h2.2 (a : MulAut _) (hMp ▸ a.2)⟩
    have htC : ∀ c ∈ C, t c ∈ C := by
      intro c hc l hl
      have h1 := hc _ (hTL' t htT l hl)
      calc l (t c) = t ((t⁻¹ * l * t) c) := by simp [MulAut.mul_apply]
        _ = t c := by rw [h1]
    have htCinv : ∀ c ∈ C, t⁻¹ c ∈ C := by
      intro c hc l hl
      have h1 := hc _ (hTL t htT l hl)
      calc l (t⁻¹ c) = t⁻¹ ((t * l * t⁻¹) c) := by simp [MulAut.mul_apply]
        _ = t⁻¹ c := by rw [h1]
    have hVtinv : ∀ l ∈ Lk, ∀ v ∈ Vs.map t.toMonoidHom, l v ∈ Vs.map t.toMonoidHom := by
      rintro l hl _ ⟨u, hu, rfl⟩
      refine ⟨(t⁻¹ * l * t) u, hVinv _ (hTL' t htT l hl) u hu, ?_⟩
      simp [MulAut.mul_apply]
    have hcZ : Nat.card (Subgroup.center ↥Lk) = 3 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Lk)
      rw [hcL, A5.card_of_isPSL34 hL'34] at h1
      omega
    have hzZ : (⟨z, hzL⟩ : ↥Lk) ∈ Subgroup.center ↥Lk := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2).symm
    have hz1' : (⟨z, hzL⟩ : ↥Lk) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have hz'L : t⁻¹ * z * t ∈ Lk := hTL' t htT z hzL
    have hz'Z : (⟨t⁻¹ * z * t, hz'L⟩ : ↥Lk) ∈ Subgroup.center ↥Lk := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      obtain ⟨g, hg⟩ := g
      show g * (t⁻¹ * z * t) = t⁻¹ * z * t * g
      have h1 := hzc _ (hTL t htT g hg)
      calc g * (t⁻¹ * z * t) = t⁻¹ * ((t * g * t⁻¹) * z) * t := by group
        _ = t⁻¹ * (z * (t * g * t⁻¹)) * t := by rw [h1]
        _ = t⁻¹ * z * t * g := by group
    have hz' : t⁻¹ * z * t = z ∨ t⁻¹ * z * t = z⁻¹ := by
      rcases A6S20.eq_of_card_center_three hcZ hzZ hz1' hz'Z with h | h | h
      · exfalso
        apply hz1
        have h2 : t⁻¹ * z * t = 1 := congrArg Subtype.val h
        calc z = t * (t⁻¹ * z * t) * t⁻¹ := by group
          _ = 1 := by rw [h2]; group
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    have hfpVs : ∀ v ∈ Vs, z v * v⁻¹ ∈ C → v ∈ C := fun v hv h1 =>
      (hfp v hv ⟨Vs.mul_mem (hVinv z hzL v hv) (Vs.inv_mem hv), h1⟩).2
    have hfpinv : ∀ v ∈ Vs, z⁻¹ v * v⁻¹ ∈ C → v ∈ C := by
      intro v hv h1
      apply hfpVs v hv
      have h2 := hzC _ h1
      have e : z (z⁻¹ v * v⁻¹) = v * (z v)⁻¹ := by
        rw [map_mul, map_inv, MulAut.apply_inv_self]
      rw [e] at h2
      have h3 : z v * v⁻¹ = (v * (z v)⁻¹)⁻¹ := by group
      rw [h3, h2]
      exact C.inv_mem h1
    have hfpz' : ∀ v ∈ Vs, (t⁻¹ * z * t) v * v⁻¹ ∈ C → v ∈ C := by
      rcases hz' with h | h <;> rw [h]
      exacts [hfpVs, hfpinv]
    have hfpVt : ∀ w ∈ Vs.map t.toMonoidHom, z w * w⁻¹ ∈ C → w ∈ C := by
      rintro _ ⟨v, hv, rfl⟩ h1
      have e : z (t v) = t ((t⁻¹ * z * t) v) := by simp [MulAut.mul_apply]
      change z (t v) * (t v)⁻¹ ∈ C at h1
      rw [e, ← map_inv, ← map_mul] at h1
      have h2 : (t⁻¹ * z * t) v * v⁻¹ ∈ C := by
        have h3 := htCinv _ h1
        simpa using h3
      exact htC _ (hfpz' v hv h2)
    have hfpE := A6S20.fpf_of_isSumMod hsum hzC (hVinv z hzL) (hVtinv z hzL) hfpVs hfpVt
    have hC0' := hC0 z hzL hz3 hzc hfpE
    rw [hC0', inf_bot_eq] at hnat
    rw [hC0'] at hsum
    refine ⟨t, htT, hnat, ?_, ?_⟩
    · have h1 := hsum.2
      rw [sup_bot_eq, sup_bot_eq] at h1
      exact le_bot_iff.mp h1
    · have h1 := hsum.1
      rw [sup_bot_eq] at h1
      exact h1.symm

end CFSG.Quasithin.H13.L1232S2
