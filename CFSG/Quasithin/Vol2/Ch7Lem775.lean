module

public import CFSG.Quasithin.Vol2.Ch7Lem774
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable (S : Setup T L I)
include S

theorem mem_autI_L_of_fix {J : Subgroup G} (hJV : J ≤ fsuV T I)
    (hJL : L ≤ Subgroup.normalizer (J : Set G)) (hJ1 : J ≠ ⊥) (hJV' : J ≠ fsuV T I) {x : G}
    (hxM : x ∈ fsuM T L) {z : G} (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (hxz : x ∈ Subgroup.centralizer ({z} : Set G)) :
    convI S.hV ⟨x, S.hMN hxM⟩ ∈ autI S.hV (fsuL0 T L) := by
  obtain ⟨e, he, hMe⟩ := S.exists_model
  set J' := (intSub S.hV J).map e.toMonoidHom with hJ'
  have hinv : Pair.IsInv (pairSL (ZMod 2)) J' := by
    rintro y hy _ ⟨w, hw, rfl⟩
    rw [← he] at hy
    obtain ⟨x', hx', rfl⟩ := hy
    obtain ⟨g, hgL, rfl⟩ := (mem_autI S.hV).1 hx'
    refine ⟨convI S.hV g w, ?_, ?_⟩
    · change (convI S.hV g w).val ∈ J
      rw [convI_apply_val]
      have hgL' : (g : G) ∈ L := by rw [S.hL]; exact hgL
      have hw' : w.val ∈ J := hw
      exact (Subgroup.mem_normalizer_iff.mp (hJL hgL') _).mp hw'
    · change e (convI S.hV g w) = e ((convI S.hV g) (e.symm (e w)))
      rw [MulEquiv.symm_apply_apply]
  have hcard := S.card_eq_eight hJV hJL hJ1 hJV'
  have hJ'c : Nat.card J' = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, ← Subgroup.card_map_of_injective
      (valHom_injective S.hV), map_valHom_intSub S.hV hJV, hcard]
  have hJ'12 : J' = V₁ (ZMod 2) ∨ J' = V₂ (ZMod 2) := by
    rcases SL3One.isInv_eq hinv with h | h | h | h
    · rw [h, Subgroup.card_bot] at hJ'c
      norm_num at hJ'c
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, Subgroup.card_top, SL3One.card_pairMod_two card_zmod_two] at hJ'c
      norm_num at hJ'c
  set y := congrHom e (convI S.hV ⟨x, S.hMN hxM⟩) with hy
  have hyN : y ∈ pairNorm (ZMod 2) :=
    hMe ⟨_, convI_mem_autI S.hV (Subgroup.mem_top x) (S.hMN hxM), rfl⟩
  set z' : PairMod (ZMod 2) := e (IntMod.mk S.hV ⟨z, hJV hzJ⟩) with hz'
  have hz'J : z' ∈ J' := ⟨_, hzJ, rfl⟩
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have h2 : IntMod.mk S.hV ⟨z, hJV hzJ⟩ = 1 := e.injective (h.trans e.map_one.symm)
    exact congrArg IntMod.val h2
  have hyz : y z' = z' := by
    change e (convI S.hV ⟨x, S.hMN hxM⟩ (e.symm z')) = z'
    rw [hz', MulEquiv.symm_apply_apply]
    congr 1
    apply IntMod.val_injective
    rw [convI_apply_val]
    change x * z * x⁻¹ = z
    rw [Subgroup.mem_centralizer_singleton_iff.mp hxz, mul_inv_cancel_right]
  have hyS : y ∈ pairSub (ZMod 2) := by
    rcases SL3Pair.mem_pairSub_or hyN with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := SL3Pair.mem_pairSub_iff.mp h
      have hyz' : swapAut (ZMod 2) (y z') = pairAut a b z' := by
        rw [← hab]
        rfl
      rw [hyz, pairAut_apply] at hyz'
      have h1 : z'.2 = a z'.1 := congrArg Prod.fst hyz'
      have h2 : z'.1 = b z'.2 := congrArg Prod.snd hyz'
      apply hz'1
      rcases hJ'12 with h' | h'
      · rw [h', mem_V₁] at hz'J
        rw [hz'J, map_one] at h2
        exact Prod.ext h2 hz'J
      · rw [h', mem_V₂] at hz'J
        rw [hz'J, map_one] at h1
        exact Prod.ext hz'J h1
  have hyL : y ∈ pairSL (ZMod 2) := SL3One.mem_pairSL_of_mem_pairSub card_zmod_two hyN hyS
  rw [← he] at hyL
  obtain ⟨x', hx', hxe⟩ := hyL
  rwa [← congrHom_injective e hxe]

omit S in
theorem autI_oTwoUpper {V : Subgroup G} (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (oTwoUpper X) = oTwoUpper (autI hV X) := by
  set N := Subgroup.normalizer (V : Set G) with hN
  have h1 : (oTwoUpper X).subgroupOf N = oTwoUpper (X.subgroupOf N) := by
    have h2 := oTwoUpper_map N.subtype (X.subgroupOf N)
    rw [Subgroup.map_subgroupOf_eq_of_le hX] at h2
    rw [h2, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  unfold autI
  rw [h1, oTwoUpper_map]

theorem autI_inf_eq {J : Subgroup G} (hJV : J ≤ fsuV T I)
    (hJL : L ≤ Subgroup.normalizer (J : Set G)) (hJ1 : J ≠ ⊥) (hJV' : J ≠ fsuV T I)
    {Vp : Subgroup G} (hVpV : Vp ≤ fsuV T I) {z : G} (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (hzVp : z ∈ Vp) :
    autI S.hV (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)) =
      autI S.hV (L ⊓ Subgroup.centralizer (Vp : Set G)) := by
  refine le_antisymm ?_ (autI_mono S.hV (inf_le_inf_right _ S.L_le_fsuM))
  intro y hy
  obtain ⟨g, hgMp, rfl⟩ := (mem_autI S.hV).1 hy
  have hgz : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzVp) hgMp.2
  have hyL := S.mem_autI_L_of_fix hJV hJL hJ1 hJV' hgMp.1 hzJ hz1 hgz
  obtain ⟨l, hlL, hle⟩ := (mem_autI S.hV).1 hyL
  refine (mem_autI S.hV).2 ⟨l, ⟨by rw [S.hL]; exact hlL, ?_⟩, hle⟩
  change (l : G) ∈ Subgroup.centralizer (Vp : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun φ : MulAut (IntMod (fsuV T I) S.hV) =>
    (φ (IntMod.mk S.hV ⟨v, hVpV hv⟩)).val) hle
  simp only [convI_apply_val] at h1
  have h2 : (g : G) * v * (g : G)⁻¹ = v := by
    rw [← Subgroup.mem_centralizer_iff.mp hgMp.2 v hv, mul_inv_cancel_right]
  have h3 : (l : G) * v * (l : G)⁻¹ = v := h1.trans h2
  calc v * l = (l : G) * v * (l : G)⁻¹ * l := by rw [h3]
    _ = l * v := by group

omit S [Finite G] in
theorem isSylowTwoOf_map_range {K : Type*} [Group K] {H P : Subgroup G}
    (hP : IsSylowTwoOf P H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((P.subgroupOf H).map ρ) ρ.range := by
  have hP2 : IsPGroup 2 (P.subgroupOf H) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hP2.map ρ, ?_⟩
  have h1 : ((P.subgroupOf H).map ρ).subgroupOf ρ.range =
      (P.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  exact hP.2.2 (hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective))

theorem isSylowTwoOf_autI {P K : Subgroup G} (hPK : IsSylowTwoOf P K)
    (hK : K ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    IsSylowTwoOf (autI S.hV P) (autI S.hV K) := by
  have h := isSylowTwoOf_map_range hPK (convHom S.hV K hK)
  rwa [range_convHom, ← autI_eq_map_convHom S.hV hK hPK.1] at h

theorem autI_sup {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hB : B ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    autI S.hV (A ⊔ B) = autI S.hV A ⊔ autI S.hV B := by
  unfold autI
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem autI_eq_sup {J : Subgroup G} (hJV : J ≤ fsuV T I)
    (hJL : L ≤ Subgroup.normalizer (J : Set G)) (hJ1 : J ≠ ⊥) (hJV' : J ≠ fsuV T I)
    {Vp : Subgroup G} (hVpV : Vp ≤ fsuV T I) {z : G} (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (hzVp : z ∈ Vp) {Tp : Subgroup G}
    (hTp : IsSylowTwoOf Tp (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G))) :
    autI S.hV (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)) =
      autI S.hV (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) := by
  have hMpN : fsuM T L ⊓ Subgroup.centralizer (Vp : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := inf_le_left.trans S.hMN
  have hLpN : L ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans S.L_le_normalizer_V
  have hTpN : Tp ≤ Subgroup.normalizer (fsuV T I : Set G) := hTp.1.trans hMpN
  have hS := S.isSylowTwoOf_autI hTp hMpN
  have hX := S.autI_inf_eq hJV hJL hJ1 hJV' hVpV hzJ hz1 hzVp
  refine le_antisymm ?_ (autI_mono S.hV (sup_le ((oTwoUpper_le _).trans
    (inf_le_inf_right _ S.L_le_fsuM)) hTp.1))
  rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hS, S.autI_sup ((oTwoUpper_le _).trans hLpN) hTpN]
  refine sup_le_sup_right ?_ _
  rw [hX, ← autI_oTwoUpper S.hV hLpN]

theorem exists_fac {J : Subgroup G} (hJV : J ≤ fsuV T I)
    (hJL : L ≤ Subgroup.normalizer (J : Set G)) (hJ1 : J ≠ ⊥) (hJV' : J ≠ fsuV T I)
    {Vp : Subgroup G} (hVpV : Vp ≤ fsuV T I) {z : G} (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (hzVp : z ∈ Vp) {Tp : Subgroup G}
    (hTp : IsSylowTwoOf Tp (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)))
    {x : G} (hx : x ∈ fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)) :
    ∃ y ∈ oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp,
      x * y⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have hxN : x ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN hx.1
  have hmem : convI S.hV ⟨x, hxN⟩ ∈
      autI S.hV (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) := by
    rw [← S.autI_eq_sup hJV hJL hJ1 hJV' hVpV hzJ hz1 hzVp hTp]
    exact convI_mem_autI S.hV hx hxN
  obtain ⟨y, hyX, hye⟩ := (mem_autI S.hV).1 hmem
  refine ⟨y, hyX, ?_⟩
  have h1 : convI S.hV (⟨x, hxN⟩ * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hye, mul_inv_cancel]
  have h2 := (convI_eq_one_iff S.hV _).mp h1
  exact h2

theorem charTwo_inf_centralizer (h3108 : Stmt3_2_10_eight) {J : Subgroup G}
    (hJV : J ≤ fsuV T I) (hJL : L ≤ Subgroup.normalizer (J : Set G)) (hJ1 : J ≠ ⊥)
    (hJV' : J ≠ fsuV T I) {Vp : Subgroup G} (hVpV : Vp ≤ fsuV T I) {z : G} (hzJ : z ∈ J)
    (hz1 : z ≠ 1) (hzVp : z ∈ Vp)
    (hTp : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G))
      (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)))
    {H : Subgroup G} (hLH : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
      (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H)
    (hHG : H ≤ Subgroup.centralizer (Vp : Set G)) {w : G} (hwV : w ∈ fsuV T I) (hw1 : w ≠ 1)
    {S₀ : Subgroup G} (hS₀ : IsSylowTwoOf S₀ ⊤) (hwS₀ : w ∈ S₀)
    (hwZ : w ∈ Subgroup.centralizer (S₀ : Set G)) :
    CharTwo (H ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  set Gw := Subgroup.centralizer ({w} : Set G) with hGw
  set Gpw := Subgroup.centralizer (Vp : Set G) ⊓ Gw with hGpw
  set N := H ⊓ Gw with hNdef
  have hVcomm : ∀ a ∈ fsuV T I, ∀ b ∈ fsuV T I, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (S.hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hww : w * w = 1 := by
    rw [← sq]
    exact S.hV.2 w hwV
  have hGwc : CharTwo Gw := by
    rw [hGw, ← normalizer_zpowers_eq_centralizer hww hw1]
    refine charTwo_normalizer_of_inf_center S.hyp.fsu.qtke.2.1 hS₀
      (isPGroup_zpowers_of_mul_self hww) ?_
    intro h
    apply hw1
    have hmem : w ∈ Subgroup.zpowers w ⊓ (S₀ ⊓ Subgroup.centralizer (S₀ : Set G)) :=
      ⟨Subgroup.mem_zpowers w, hwS₀, hwZ⟩
    rw [h] at hmem
    exact hmem
  have hCV : Subgroup.centralizer (fsuV T I : Set G) ≤ Gpw := by
    intro q hq
    refine ⟨Subgroup.centralizer_le hVpV hq, ?_⟩
    change q ∈ Subgroup.centralizer ({w} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hq w hwV).symm
  obtain ⟨Tw, hTw, hQTw⟩ := A4.exists_isSylowTwoOf_ge
    ((inf_le_right : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ _).trans hCV)
    (S.hyp.fsu.sylow.1.to_le inf_le_left)
  have hJTw : thompsonJ T ≤ Tw := fun x hx =>
    hQTw ⟨(iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hx, S.hJ hx⟩
  have hVp : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 S.hL, rfl⟩
  have hNTw := (h3108 G T L I (fsuV T I) S.hyp.fsu hVp S.hJ Tw hTw.2.1 hJTw).2
  have hTwMp : Tw ≤ fsuM T L ⊓ Subgroup.centralizer (Vp : Set G) :=
    le_inf (Subgroup.le_normalizer.trans hNTw) (hTw.1.trans inf_le_left)
  obtain ⟨S', hS', hTwS'⟩ := A4.exists_isSylowTwoOf_ge hTwMp hTw.2.1
  obtain ⟨m, hm, hmS⟩ := A4.exists_conj_of_isSylowTwoOf hTp hS'
  obtain ⟨y, hy, hc⟩ := S.exists_fac hJV hJL hJ1 hJV' hVpV hzJ hz1 hzVp hTp hm
  have hcG := hCV hc
  have hconj : ∀ t ∈ Tw, (m * y⁻¹)⁻¹ * t * (m * y⁻¹) ∈ N := by
    intro t ht
    have h1 : m⁻¹ * t * m ∈ Tp := (hmS t).mp (hTwS' ht)
    have h2 : (m * y⁻¹)⁻¹ * t * (m * y⁻¹) = y * (m⁻¹ * t * m) * y⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [h2]
      exact hLH (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy (le_sup_right (a := oTwoUpper
        (L ⊓ Subgroup.centralizer (Vp : Set G))) h1)) (Subgroup.inv_mem _ hy))
    · exact Gw.mul_mem (Gw.mul_mem (Gw.inv_mem hcG.2) (hTw.1 ht).2) hcG.2
  have hVpN : Vp ≤ N := by
    intro v hv
    refine ⟨hLH (le_sup_right (a := oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)))
      ⟨S.fsuV_le_T (hVpV hv), Subgroup.mem_centralizer_iff.mpr fun u hu =>
        hVcomm u (hVpV hu) v (hVpV hv)⟩), ?_⟩
    change v ∈ Subgroup.centralizer ({w} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hVcomm v (hVpV hv) w hwV
  have hVpO : Vp ≤ pCoreOf 2 N := by
    refine le_pCoreOf_of_le_normalizer 2 hVpN ?_
      (S.isPGroup_fsuV.to_le hVpV)
    intro n hn
    exact Subgroup.centralizer_le_normalizer _ (hHG hn.1)
  have hC : pCoreOf 2 Gw ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ N := by
    intro x hx
    have hxVp : x ∈ Subgroup.centralizer (Vp : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVpO) hx.2
    have hxGpw : x ∈ Gpw := ⟨hxVp, pCoreOf_le 2 Gw hx.1⟩
    have hxO : x ∈ pCoreOf 2 Gpw := by
      have hle : pCoreOf 2 Gw ⊓ Gpw ≤ pCoreOf 2 Gpw := by
        refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
          ((pCoreOf_isPGroup 2 Gw).to_le inf_le_left)
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · rintro ⟨hu1, hu2⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Gw hg.2) u).mp hu1,
            Gpw.mul_mem (Gpw.mul_mem hg hu2) (Gpw.inv_mem hg)⟩
        · rintro ⟨hu1, hu2⟩
          refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Gw hg.2) u).mpr hu1,
            ?_⟩
          have := Gpw.mul_mem (Gpw.mul_mem (Gpw.inv_mem hg) hu2) hg
          simpa [mul_assoc] using this
      exact hle ⟨hx.1, hxGpw⟩
    have hc' : m * y⁻¹ ∈ Gpw := hcG
    have hxc : (m * y⁻¹) * x * (m * y⁻¹)⁻¹ ∈ Tw :=
      pCoreOf_le_of_isSylowTwoOf hTw
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Gpw hc') x).mp hxO)
    have := hconj _ hxc
    simpa [mul_assoc] using this
  exact charTwo_of_pCore_centralizer_le hGwc inf_le_right hC

end Setup

end CFSG.Quasithin.H13.Sec77
