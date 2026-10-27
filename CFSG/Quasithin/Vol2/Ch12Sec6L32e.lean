module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32c
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Claim
public import CFSG.Quasithin.Vol2.Ch12Sec6L32b
public import CFSG.Quasithin.Vol2.Ch12Sec6L32d

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  S126 S126P S126E S126L24 F126 L1233 Equiv

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem mk_mem_oTwoRes {Y : Subgroup G} (hYH : oTwoRes Y ≤ H) {l : G} (hl : l ∈ oTwoRes Y) :
    (QuotientGroup.mk ⟨l, hYH hl⟩ : S126.HStar H) ∈ oTwoRes (⊤ : Subgroup (S126.HStar H)) := by
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨-, m, hm, hxm⟩ := id hx
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, m, hm, ?_⟩
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hYH (Subgroup.subset_closure hx)⟩ : ↥H) ^ m = 1 :=
      Subtype.ext (by simpa using hxm)
    rw [this, QuotientGroup.mk_one]
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have := Subgroup.mul_mem _ ihx ihy
    rwa [← QuotientGroup.mk_mul] at this
  | inv x hx ihx =>
    have := Subgroup.inv_mem _ ihx
    rwa [← QuotientGroup.mk_inv] at this

omit [Finite G] [IsMulCommutative ↥V] in
theorem eq_one_of_pow_two_pow {Q : Type*} [Group Q] {f : Q} (h5 : f ^ 5 = 1) {a : ℕ}
    (h : f ^ 2 ^ a = 1) : f = 1 := by
  have e : f = (f ^ 2 ^ a) ^ 2 ^ (3 * a) := by
    rw [← pow_mul, ← pow_add, show a + 3 * a = 4 * a by ring, pow_mul,
      pow_eq_pow_mod _ h5, Nat.pow_mod]
    norm_num
  rw [e, h, one_pow]

theorem false_of_case1 (hcl : Claim12_6_32) (h1262 : Theorem12_6_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (h1 : Case1 T L H K) :
    False := by
  classical
  have h := h918.toHypF98.toHypF91
  obtain ⟨I, t, ht, hV₁I, hIU, hKI, hinf, hsup, hnat⟩ := hcl G T L V F hH hZ H K hIs h1 h918
  obtain ⟨E, _, _, hE4, π, hR⟩ := hnat
  have : Fintype E := Fintype.ofFinite E
  have hE4' : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card, hE4]; norm_num
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hTH : T ≤ H := h.T_le_H
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
    refine le_normalizer_of_conj fun x hx k hk => ?_
    rw [← h1.1]
    exact mem_conjClosure hx hk
  have hX : autOn (tildeOf F.V1 K) (UT F.V1 F.V5 H) = (S126.star H K).map (psiH h) := by
    rw [← range_thetaH h hKH, S126.star, Subgroup.map_map]
    rfl
  have hXc := @card_of_nat _ _ _
    (commGroupOfElemAbelian h918.toHypF98.toHypF91.isElemAbelian_tilde) _ _ _ hR _ hE4'
  have hKc : Nat.card ↥(S126.star H K) = 60480 := by
    rw [← hXc, hX, Subgroup.card_map_of_injective (psiH_injective h)]
  obtain ⟨hidx, hsq⟩ : (S126.star H K).index = 4 ∧ ∀ x : S126.HStar H, x ^ 2 ∈ S126.star H K := by
    rcases h1.2.1 with ⟨F', _, _, hF', ⟨e⟩, -⟩ | ⟨-, -, -, -, -, hidx, hsq⟩
    · exfalso
      have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F') (n := 3)
        (by norm_num)
      rw [hF'] at hc
      have h20160 : Nat.card (S126.PSL3Model F') = 20160 := hc.trans (by decide)
      rw [← Nat.card_congr e.toEquiv, hKc] at h20160
      norm_num at h20160
    · exact ⟨hidx, hsq⟩
  have hHc : Nat.card (S126.HStar H) = 241920 := by
    rw [← (S126.star H K).card_mul_index, hKc, hidx]
  have hKn : (S126.star H K).Normal := by
    have : (K.subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgN := h918.K₀_normal g.2
      rw [h1.1] at hgN
      exact (Subgroup.mem_normalizer_iff.1 hgN n).1 hn⟩
    exact this.map _ (QuotientGroup.mk'_surjective _)
  have hTs := card_star_of_sylow h.sylow_H
  have hS64 : Nat.card ↥(S126.star H T ⊓ S126.star H K) = 64 := card_inf_eq_64 hTs hKc hHc
  have hT2 : IsPGroup 2 ↥(S126.star H T) := IsPGroup.of_card hTs
  have hperf : ⁅S126.star H K, S126.star H K⁆ = S126.star H K :=
    perfect_of_mem_cComp (star_mem_cComp h918.K_cComp)
  have hO2 := oTwoRes_top_eq hperf hsq
  have hMH : S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) =
      S126.star H T ⊔ borel (S126.star H K) (S126.star H T) := by
    rw [h1.2.2, hO2]
  have hTN : S126.star H T ≤ Subgroup.normalizer
      ((S126.star H T ⊓ S126.star H K : Subgroup (S126.HStar H)) : Set (S126.HStar H)) :=
    le_normalizer_of_conj fun y hy z hz => ⟨(S126.star H T).mul_mem ((S126.star H T).mul_mem hy
      hz.1) ((S126.star H T).inv_mem hy), hKn.conj_mem z hz.2 y⟩
  have hMN : S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) ≤
      Subgroup.normalizer
        ((S126.star H T ⊓ S126.star H K : Subgroup (S126.HStar H)) : Set (S126.HStar H)) := by
    rw [hMH]
    exact sup_le hTN inf_le_right
  have hTB : S126.star H T ≤ Subgroup.normalizer
      ((borel (S126.star H K) (S126.star H T) : Subgroup (S126.HStar H)) : Set (S126.HStar H)) :=
    le_normalizer_of_conj fun y hy b hb => ⟨hKn.conj_mem b hb.1 y,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN hy) hb.2) (Subgroup.inv_mem _ (hTN hy))⟩
  have hSX : (S126.star H T ⊓ S126.star H K).map (psiH h) ≤
      autOn (tildeOf F.V1 K) (UT F.V1 F.V5 H) := by
    rw [hX]
    exact Subgroup.map_mono inf_le_right
  have hSc : Nat.card ↥((S126.star H T ⊓ S126.star H K).map (psiH h)) = 64 := by
    rw [Subgroup.card_map_of_injective (psiH_injective h), hS64]
  have hfix5 : ∀ s ∈ S126.star H T ⊓ S126.star H K, Fix5 F.V1 F.V5 H (psiH h s) :=
    fun s hs => fix5_of_normalizes F h inf_le_left hMN hs
  have hcomm := hWcomm h
  have htH : t ∈ H := hTH ht
  have hIUt : conjSub t I ≤ conjClosure F.V5 H := by
    intro x hx
    have hx' := mem_conjSub.1 hx
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure F.V5 H htH) _).1 (hIU hx')
    simpa [mul_assoc] using this
  have hinf' : tW F.V1 F.V5 H I ⊓ tW F.V1 F.V5 H (conjSub t I) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    have : (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 I ⊓ tildeOf F.V1 (conjSub t I) :=
      ⟨hw1, hw2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hsup' : tW F.V1 F.V5 H I ⊔ tW F.V1 F.V5 H (conjSub t I) = ⊤ := by
    have h1 : tildeOf F.V1 I ≤ UT F.V1 F.V5 H := secImg_mono hIU
    have h2 : tildeOf F.V1 (conjSub t I) ≤ UT F.V1 F.V5 H := secImg_mono hIUt
    rw [tW, tW, ← Subgroup.subgroupOf_sup h1 h2, hsup]
    exact tW_top
  have hθ : ∀ J : Subgroup G, K ≤ Subgroup.normalizer (J : Set G) → ∀ x : ↥H, (x : G) ∈ K →
      ∀ w ∈ tW F.V1 F.V5 H J, thetaH h x w ∈ tW F.V1 F.V5 H J := by
    intro J hKJ x hxK w hw
    rw [tW, Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨⟨j, hjN⟩, hjJ, hjw⟩ := mem_secImg.1 hw
    rw [thetaH_apply, ← hjw, thetaH_apply_secMk]
    exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.1 (hKJ hxK) j).1 hjJ)
  have hKJ : K ≤ Subgroup.normalizer ((conjSub t I : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj fun k hk x hx => ?_
    rw [mem_conjSub] at hx ⊢
    have hk' : t⁻¹ * k * t⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hTK (T.inv_mem ht)) k).1 hk
    rw [inv_inv] at hk'
    have := (Subgroup.mem_normalizer_iff.1 (hKI hk') _).1 hx
    convert this using 1
    group
  have hSθ : ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), ∀ J : Subgroup G,
      K ≤ Subgroup.normalizer (J : Set G) → ∀ w ∈ tW F.V1 F.V5 H J, f w ∈ tW F.V1 F.V5 H J := by
    rintro _ ⟨s, hs, rfl⟩ J hKJ' w hw
    obtain ⟨x, hxK, rfl⟩ := hs.2
    exact hθ J hKJ' x (Subgroup.mem_subgroupOf.1 hxK) w hw
  have hθt : ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h),
      thetaH h ⟨t, htH⟩ * f * (thetaH h ⟨t, htH⟩)⁻¹ ∈
        (S126.star H T ⊓ S126.star H K).map (psiH h) := by
    rintro _ ⟨s, hs, rfl⟩
    have htT : (QuotientGroup.mk ⟨t, htH⟩ : S126.HStar H) ∈ S126.star H T :=
      ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    refine ⟨_, (Subgroup.mem_normalizer_iff.1 (hTN htT) s).1 hs, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hD₁ := @card_fix_le _ _ _
    (commGroupOfElemAbelian h918.toHypF98.toHypF91.isElemAbelian_tilde) _ _ _ _ hR hE4' _ hSX hSc
  have hD₂ : Nat.card {w : ↥(tW F.V1 F.V5 H (conjSub t I)) //
      ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f (w : ↥(UT F.V1 F.V5 H)) = w} ≤ 4 := by
    have htinv : t⁻¹ ∈ H := H.inv_mem htH
    have hmem : ∀ w ∈ tW F.V1 F.V5 H (conjSub t I), thetaH h ⟨t⁻¹, htinv⟩ w ∈ tW F.V1 F.V5 H I := by
      intro w hw
      rw [tW, Subgroup.mem_subgroupOf] at hw ⊢
      obtain ⟨⟨j, hjN⟩, hjJ, hjw⟩ := mem_secImg.1 hw
      rw [thetaH_apply, ← hjw, thetaH_apply_secMk]
      refine secMk_mem_secImg ?_
      have := mem_conjSub.1 hjJ
      simpa using this
    have hti : thetaH h ⟨t⁻¹, htinv⟩ = (thetaH h ⟨t, htH⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    have hfixmap : ∀ w : {w : ↥(tW F.V1 F.V5 H (conjSub t I)) //
        ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f (w : ↥(UT F.V1 F.V5 H)) = w},
        ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h),
          f (thetaH h ⟨t⁻¹, htinv⟩ (w.1 : ↥(UT F.V1 F.V5 H))) =
            thetaH h ⟨t⁻¹, htinv⟩ (w.1 : ↥(UT F.V1 F.V5 H)) := by
      intro w f hf
      have h1 := w.2 _ (hθt f hf)
      rw [hti]
      rw [MulAut.mul_apply, MulAut.mul_apply] at h1
      apply (thetaH h ⟨t, htH⟩).injective
      rw [MulAut.apply_inv_self]
      exact h1
    have hinj : Function.Injective fun w : {w : ↥(tW F.V1 F.V5 H (conjSub t I)) //
        ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f (w : ↥(UT F.V1 F.V5 H)) = w} =>
        (⟨⟨thetaH h ⟨t⁻¹, htinv⟩ w.1, hmem _ w.1.2⟩, hfixmap w⟩ :
          {w : ↥(tW F.V1 F.V5 H I) // ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h),
            f (w : ↥(UT F.V1 F.V5 H)) = w}) := by
      intro w w' hww
      have := congrArg (fun z => ((z.1 : ↥(tW F.V1 F.V5 H I)) : ↥(UT F.V1 F.V5 H))) hww
      exact Subtype.ext (Subtype.ext ((thetaH h ⟨t⁻¹, htinv⟩).injective this))
    exact (Nat.card_le_card_of_injective _ hinj).trans hD₁
  have hD := card_fix_le_mul hcomm hinf' hsup'
    (fun f hf a ha => hSθ f hf I hKI a ha) (fun f hf b hb => hSθ f hf _ hKJ b hb)
  have : Fintype ↥(UT F.V1 F.V5 H) := Fintype.ofFinite _
  have hV5 : Nat.card {w : ↥(UT F.V1 F.V5 H) //
      (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5} = 16 := by
    have e : {w : ↥(UT F.V1 F.V5 H) // (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5} ≃
        ↥(tildeOf F.V1 F.V5) :=
      { toFun := fun w => ⟨w.1, w.2⟩
        invFun := fun x => ⟨⟨x, secImg_mono (le_conjClosure F.V5 H) x.2⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    have h1 : Nat.card ↥(tildeOf F.V1 F.V5) = F.V1.relIndex F.V5 := by
      have := relIndex_secImg (A := N1 F.V1) (B := F.V1) (T := F.V1) (H := F.V5) le_rfl
        h.V₁_le_Vp hVN
      rw [show secImg (N1 F.V1) F.V1 F.V1 = ⊥ from tildeOf_eq_bot_of_le le_rfl,
        Subgroup.relIndex_bot_left] at this
      exact this
    have h2 := Subgroup.relIndex_mul_relIndex ⊥ F.V1 F.V5 bot_le h.V₁_le_Vp
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, h.card_V₁,
      card_V5 (beta_injective F hZ)] at h2
    omega
  have hVD : ∀ w : ↥(UT F.V1 F.V5 H), (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 →
      ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f w = w := by
    rintro w hw _ ⟨s, hs, rfl⟩
    exact hfix5 s hs w hw
  have hD16 : 16 ≤ Nat.card {w : ↥(UT F.V1 F.V5 H) //
      ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f w = w} := by
    rw [← hV5]
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, hVD w.1 w.2⟩) fun w w' hww => ?_
    simp only [Subtype.mk.injEq] at hww
    exact Subtype.ext hww
  have hD₁4 : 4 ≤ Nat.card {w : ↥(tW F.V1 F.V5 H I) //
      ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f (w : ↥(UT F.V1 F.V5 H)) = w} := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hlt) hD₂
    omega
  have hDV : ∀ w : ↥(UT F.V1 F.V5 H),
      (∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f w = w) →
      (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 := by
    intro w hw
    by_contra hwV
    have hsub : insert w (Finset.univ.filter fun w : ↥(UT F.V1 F.V5 H) =>
        (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5) ⊆
        Finset.univ.filter fun w : ↥(UT F.V1 F.V5 H) =>
          ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f w = w := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hz with rfl | hz
      · exact hw
      · exact hVD z (Finset.mem_filter.1 hz).2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hwV), ← Fintype.card_subtype,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hV5] at h1
    have h2 := hD.trans (Nat.mul_le_mul hD₁ hD₂)
    omega
  let fixSub : Subgroup ↥(UT F.V1 F.V5 H) :=
    { carrier := {w | ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f w = w}
      mul_mem' := fun ha hb f hf => by rw [map_mul, ha f hf, hb f hf]
      one_mem' := fun f _ => map_one f
      inv_mem' := fun ha f hf => by rw [map_inv, ha f hf] }
  have hA4 : Nat.card ↥(tW F.V1 F.V5 H I ⊓ fixSub) = 4 := by
    have e : ↥(tW F.V1 F.V5 H I ⊓ fixSub) ≃ {w : ↥(tW F.V1 F.V5 H I) //
        ∀ f ∈ (S126.star H T ⊓ S126.star H K).map (psiH h), f (w : ↥(UT F.V1 F.V5 H)) = w} :=
      { toFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
        invFun := fun w => ⟨w.1.1, w.1.2, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    exact le_antisymm hD₁ hD₁4
  have hA5 : ∀ w ∈ tW F.V1 F.V5 H I ⊓ fixSub,
      (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 := fun w hw => hDV w hw.2
  have hAinv : ∀ l (hl : l ∈ H), l ∈ Li L F.V1 →
      ∀ w ∈ tW F.V1 F.V5 H I ⊓ fixSub, thetaH h ⟨l, hl⟩ w ∈ tW F.V1 F.V5 H I ⊓ fixSub := by
    intro l hl hlL1 w hw
    have hlK : (QuotientGroup.mk ⟨l, hl⟩ : S126.HStar H) ∈ S126.star H K := by
      rw [← hO2]
      exact mk_mem_oTwoRes (le_sup_left.trans h.L₁T_le_H) hlL1
    obtain ⟨x, hxK, hxe⟩ := hlK
    have hθl : thetaH h ⟨l, hl⟩ = thetaH h x := by
      rw [← psiH_mk, ← psiH_mk]
      exact congrArg (psiH h) hxe.symm
    have hlM : (QuotientGroup.mk ⟨l, hl⟩ : S126.HStar H) ∈
        S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) :=
      ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.2 ⟨Subgroup.le_normalizer (L1_le_L hlL1), hl⟩, rfl⟩
    have hlN := hMN hlM
    refine ⟨?_, ?_⟩
    · rw [hθl]
      exact hθ I hKI x (Subgroup.mem_subgroupOf.1 hxK) w hw.1
    · rintro _ ⟨s, hs, rfl⟩
      have hs' := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hlN) s).1 hs
      rw [inv_inv] at hs'
      have h1 := hw.2 _ ⟨_, hs', rfl⟩
      have e : psiH h s = thetaH h ⟨l, hl⟩ *
          psiH h ((QuotientGroup.mk ⟨l, hl⟩)⁻¹ * s * QuotientGroup.mk ⟨l, hl⟩) *
            (thetaH h ⟨l, hl⟩)⁻¹ := by
        rw [map_mul, map_mul, map_inv, psiH_mk]
        group
      show psiH h s (thetaH h ⟨l, hl⟩ w) = thetaH h ⟨l, hl⟩ w
      rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h1]
  obtain ⟨w, hwA, -, u, hu, -, hnon, hwu⟩ := exists_nonsing_mem F h hA4 hA5 hAinv
  obtain ⟨f, hfX, hfw, hf5, hf1⟩ := @exists_five _ _ _
    (commGroupOfElemAbelian h918.toHypF98.toHypF91.isElemAbelian_tilde) _ _ _ _ hR hE4' _ hSX
    hSc w hwA.1 hwA.2
  rw [hX] at hfX
  obtain ⟨ks, hks, rfl⟩ := hfX
  obtain ⟨x, hxK, rfl⟩ := hks
  have hx5 : ((x ^ 5 : ↥H) : G) ∈ pCoreOf 2 H := by
    rw [← mkH_eq_one_iff]
    apply psiH_injective h
    rw [QuotientGroup.mk_pow, map_pow, map_one]
    exact hf5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup (r := 2) H) ⟨_, hx5⟩
  have ha' : ((x : G) ^ 5) ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hy5 : ((x ^ 2 ^ a : ↥H) : G) ^ 5 = 1 := by
    rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, ha']
  have hy5' : (x ^ 2 ^ a : ↥H) ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hy5]; rfl)
  have hθy : thetaH h (x ^ 2 ^ a) = psiH h (QuotientGroup.mk' _ x) ^ 2 ^ a := by
    rw [map_pow]
    rfl
  have hf'1 : thetaH h (x ^ 2 ^ a) ≠ 1 := fun h0 => hf1 (eq_one_of_pow_two_pow hf5 (hθy ▸ h0))
  have hpow : ∀ n : ℕ, (psiH h (QuotientGroup.mk' _ x) ^ n) w = w := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hfw, ih]
  have hf'w : thetaH h (x ^ 2 ^ a) w = w := by
    rw [hθy]
    exact hpow _
  have hyu : ((x ^ 2 ^ a : ↥H) : G) * u * ((x ^ 2 ^ a : ↥H) : G)⁻¹ = u := by
    have h1 : ((thetaH h (x ^ 2 ^ a) w : ↥(UT F.V1 F.V5 H)) : SecQuot (N1 F.V1) F.V1) =
        (w : SecQuot (N1 F.V1) F.V1) := by rw [hf'w]
    rw [thetaH_apply, hwu, thetaH_apply_secMk, secMk_eq_secMk_iff] at h1
    refine conj_eq_of_pow_five (fun z hz => ?_) (fun z hz => ?_) hy5 h1
    · have := h.elemAbelian.2 z (h.V₁_le_V hz)
      rwa [sq] at this
    · exact (Subgroup.mem_centralizer_iff.1 (h.H_le_centralizer (x ^ 2 ^ a).2) z hz).symm
  have hyNL : ((x ^ 2 ^ a : ↥H) : G) ∈ Subgroup.normalizer (L : Set G) := by
    refine h1262 G T L V F hH u hnon (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
    rw [Set.mem_singleton_iff.1 hz]
    calc u * ((x ^ 2 ^ a : ↥H) : G) =
        ((x ^ 2 ^ a : ↥H) : G) * u * ((x ^ 2 ^ a : ↥H) : G)⁻¹ * ((x ^ 2 ^ a : ↥H) : G) := by
          rw [hyu]
      _ = ((x ^ 2 ^ a : ↥H) : G) * u := by group
  have hyM : (QuotientGroup.mk (x ^ 2 ^ a) : S126.HStar H) ∈
      S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) :=
    ⟨x ^ 2 ^ a, Subgroup.mem_subgroupOf.2 ⟨hyNL, (x ^ 2 ^ a).2⟩, rfl⟩
  rw [hMH] at hyM
  have hyB := mem_of_mem_sup hT2 hTB hyM
    (by rw [← QuotientGroup.mk_pow, hy5', QuotientGroup.mk_one])
  have hfS : ∀ s ∈ (S126.star H T ⊓ S126.star H K).map (psiH h),
      thetaH h (x ^ 2 ^ a) * s * (thetaH h (x ^ 2 ^ a))⁻¹ ∈
        (S126.star H T ⊓ S126.star H K).map (psiH h) := by
    rintro _ ⟨s₀, hs₀, rfl⟩
    refine ⟨_, (Subgroup.mem_normalizer_iff.1 hyB.2 s₀).1 hs₀, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hf'X : thetaH h (x ^ 2 ^ a) ∈ autOn (tildeOf F.V1 K) (UT F.V1 F.V5 H) := by
    rw [hX]
    exact ⟨_, ⟨x ^ 2 ^ a, Subgroup.pow_mem _ hxK _, rfl⟩, rfl⟩
  have hf'5 : thetaH h (x ^ 2 ^ a) ^ 5 = 1 := by rw [← map_pow, hy5', map_one]
  exact hf'1 (@eq_one_of_five _ _ _
    (commGroupOfElemAbelian h918.toHypF98.toHypF91.isElemAbelian_tilde) _ _ _ _ hR hE4' _ hSX
    hSc _ hf'X hf'5 hfS)

end CFSG.Quasithin.H13.L1232
