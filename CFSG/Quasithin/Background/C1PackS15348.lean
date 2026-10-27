module

public import CFSG.Quasithin.EmptyFaithful.T1531Stage2
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.EmptyFaithful.S153Nine

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace C1Pack153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem le_mc_of_isHTM153 (h11 : StageLemma14111) (h : Hyp153 G T Mc M) {H : Subgroup G}
    (hH : IsHTM153 T M H) : H ≤ Mc := by
  obtain ⟨M₂, hM₂⟩ := exists_inM_of_pCoreOf_ne_bot hH.1.2
  have hTM₂ : InM T M₂ := ⟨hM₂.1, hH.1.1.trans hM₂.2⟩
  rcases (h.lemma_15_3_2_three h11).mp hTM₂ with h1 | h1
  · exact absurd (h1 ▸ hM₂.2) hH.2
  · exact h1 ▸ hM₂.2

theorem le_centralizer_Z_of_isHTM153 (h11 : StageLemma14111) (h : Hyp153 G T Mc M) {H : Subgroup G}
    (hH : IsHTM153 T M H) : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  (h.lemma_15_3_4 h11) ▸ le_mc_of_isHTM153 h11 h hH

theorem mem_centralizer_of_odd_of_mem_inf (h : Hyp153 G T Mc M) {x : G} (hx : x ∈ Mc ⊓ M)
    (hodd : Odd (orderOf x)) : x ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hx.2
  have hxe : x ∈ (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ T := by
    rw [← h.lemma_15_3_7_inf]
    exact hx
  have hC : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans hMN
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := h.T_le.trans hMN
  have hmem : convI hV ⟨x, hxN⟩ ∈ autI hV ((M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ T) :=
    convI_mem_autI hV hxe hxN
  rw [autI_sup hV hC hTN, autI_eq_bot_of_le_centralizer hV inf_le_right, bot_sup_eq] at hmem
  have h2 : IsPGroup 2 (autI hV T) := B2F.isPGroup_autI hV h.qtfe.sylow.1 hTN
  obtain ⟨k, hk⟩ := h2 ⟨convI hV ⟨x, hxN⟩, hmem⟩
  have hk' : convI hV ⟨x, hxN⟩ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hxo : convI hV ⟨x, hxN⟩ ^ orderOf x = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ orderOf x = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one]
  have hd1 : orderOf (convI hV ⟨x, hxN⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (convI hV ⟨x, hxN⟩) ∣ orderOf x := orderOf_dvd_of_pow_eq_one hxo
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf (convI hV ⟨x, hxN⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (convI_eq_one_iff hV ⟨x, hxN⟩).mp (orderOf_eq_one_iff.mp h1)

theorem mem_inf_of_odd_mem_centralizerMod (h11 : StageLemma14111) (h : Hyp153 G T Mc M)
    (r46 : Res15346 T M V₁ V₂) {H : Subgroup G} (hH : IsHTM153 T M H) {x : G}
    (hx : x ∈ centralizerMod (quasithinOmegaOneCenter T) H (ZS153 T M V₁))
    (hodd : Odd (orderOf x)) : x ∈ M ∧ x ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hHZ := le_centralizer_Z_of_isHTM153 h11 h hH
  have hHMc := le_mc_of_isHTM153 h11 h hH
  have hZS : x ∈ Subgroup.centralizer (ZS153 T M V₁ : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hz : x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := hx.2.2 u hu
    obtain ⟨z, hzdef⟩ : ∃ z, z = x * u * x⁻¹ * u⁻¹ := ⟨_, rfl⟩
    rw [← hzdef] at hz
    have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp (hHZ hx.1) z hz
    have hz2 : z * z = 1 := by
      have := h.elemAbelian.2 z (h.Z_le_VZ hz)
      simpa [pow_two] using this
    have hxu : x * u = z * u * x := by
      calc x * u = (x * u * x⁻¹) * x := by group
        _ = z * u * x := by rw [hzdef]; group
    have hx2 : x ^ 2 * u = u * x ^ 2 := by
      calc x ^ 2 * u = x * (x * u) := by rw [pow_two, mul_assoc]
        _ = x * (z * u * x) := by rw [hxu]
        _ = (x * z) * u * x := by group
        _ = (z * x) * u * x := by rw [hzx]
        _ = z * (x * u) * x := by group
        _ = z * (z * u * x) * x := by rw [hxu]
        _ = (z * z) * u * (x * x) := by group
        _ = u * x ^ 2 := by rw [hz2, pow_two]; group
    obtain ⟨m, hm⟩ := hodd
    have hxk : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul]
      have h2 : 2 * (m + 1) = orderOf x + 1 := by omega
      rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
    have hc : Commute ((x ^ 2) ^ (m + 1)) u := (Commute.pow_left (hx2 : Commute (x ^ 2) u) _)
    rw [← hxk] at hc
    exact hc.eq.symm
  have hxM : x ∈ M := r46.normalizer_ZS ((Subgroup.centralizer_le_normalizer _) hZS)
  exact ⟨hxM, mem_centralizer_of_odd_of_mem_inf h ⟨hHMc hx.1, hxM⟩ hodd⟩

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup_two {X P : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ X ⊔ P) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ X := by
  have hx' : x ∈ ((X ⊔ P : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X P hPX] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hP ⟨b, hb⟩
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hPX hb) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

omit [Finite G] in
theorem oTwoUpper_idem' (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem exists_odd_orderOf_pow' (y : G) : ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem pCoreOf_ne_bot_of_normal {H X : Subgroup G} (hF : CharTwo H) (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G)) (hX1 : X ≠ ⊥) (hX2 : oTwoUpper X = X) :
    pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have h1 : X ⊓ pCoreOf 2 H ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hQ2.to_le inf_le_right)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hQn (hXH hg)⟩
  rw [hbot, le_bot_iff] at h1
  have hXQ : X ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hqx : q * x * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXn (pCoreOf_le 2 H hq)) x).mp hx
    have hxq : x * q⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn (hXH hx)) q⁻¹).mp ((pCoreOf 2 H).inv_mem hq)
    have hcomm : q * x * q⁻¹ * x⁻¹ ∈ X ⊓ pCoreOf 2 H := by
      refine ⟨X.mul_mem hqx (X.inv_mem hx), ?_⟩
      have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 H).mul_mem hq hxq
    rw [h1, Subgroup.mem_bot] at hcomm
    have h2 := mul_inv_eq_one.mp hcomm
    calc q * x = (q * x * q⁻¹) * q := by group
      _ = x * q := by rw [h2]
  have hXle : X ≤ pCoreOf 2 H := fun x hx => hF ⟨hXH hx, hXQ hx⟩
  apply hX1
  have hle : oTwoUpper X ≤ ⊥ := oTwoUpper_le_of_pow_mem fun x hx => by
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hXle hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  rw [hX2] at hle
  exact le_bot_iff.mp hle

theorem ker_le_pCoreOf (h11 : StageLemma14111) (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (r46 : Res15346 T M V₁ V₂) {H : Subgroup G} (hH : IsHTM153 T M H) :
    coreIn (centralizerMod (quasithinOmegaOneCenter T) H (ZS153 T M V₁)) H ≤ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have hFH : CharTwo H := charTwo_of_inH' h.qtfe.qtke h.qtfe.sylow hH.1
  obtain ⟨S₀, hS₀⟩ := h.qtfe.exists_sylow
  have hPT : pCoreOf 2 M ≤ T := by
    have := pCoreOf_two_le_sylow M S₀ (hS₀ ▸ h.T_le)
    rwa [hS₀] at this
  set K := coreIn (centralizerMod (quasithinOmegaOneCenter T) H (ZS153 T M V₁)) H with hK
  have hKH : K ≤ H := coreIn_le_left _ _
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_coreIn _ _
  set X := oTwoUpper K with hX
  have hXid : oTwoUpper X = X := oTwoUpper_idem' K
  have hXK : X ≤ K := oTwoUpper_le K
  have hXH : X ≤ H := hXK.trans hKH
  have hXn : H ≤ Subgroup.normalizer (X : Set G) :=
    hKn.trans (normalizer_le_normalizer_oTwoUpper K)
  have hXC : X ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact mem_inf_of_odd_mem_centralizerMod h11 h r46 hH (coreIn_le_right _ _ hx.1) hx.2
  have hP2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hPH : pCoreOf 2 M ≤ H := hPT.trans hTH
  have hPXn : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G) := hPH.trans hXn
  have hOA : oTwoUpper (X ⊔ pCoreOf 2 M) = X := by
    refine le_antisymm
      (oTwoUpper_le_of_pow_mem fun a ha => exists_pow_mem_of_mem_sup_two hP2 hPXn ha) ?_
    calc X = oTwoUpper X := hXid.symm
      _ ≤ oTwoUpper (X ⊔ pCoreOf 2 M) := oTwoUpper_mono le_sup_left
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left X (pCoreOf 2 M) hPXn
  have hY : ∀ y ∈ Y153 Mc M, ∀ a ∈ X ⊔ pCoreOf 2 M, y * a * y⁻¹ ∈ X ⊔ pCoreOf 2 M := by
    intro y hy a ha
    have ha' : a ∈ ((X : Set G) * (pCoreOf 2 M : Set G)) := by
      rw [← hcoe]
      exact ha
    obtain ⟨x, hx, p, hp, rfl⟩ := Set.mem_mul.mp ha'
    have hcomm : y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 M := h.commutator_Y153_le hy (hXC hx)
    have hyp : y * p * y⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M (Y153_le Mc M hy)) p).mp hp
    have e : y * (x * p) * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x * (y * p * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm)
      (Subgroup.mem_sup_left hx)) (Subgroup.mem_sup_right hyp)
  have hT : ∀ t ∈ T, ∀ a ∈ X ⊔ pCoreOf 2 M, t * a * t⁻¹ ∈ X ⊔ pCoreOf 2 M := by
    intro t ht a ha
    have ha' : a ∈ ((X : Set G) * (pCoreOf 2 M : Set G)) := by
      rw [← hcoe]
      exact ha
    obtain ⟨x, hx, p, hp, rfl⟩ := Set.mem_mul.mp ha'
    have htx : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXn (hTH ht)) x).mp hx
    have htp : t * p * t⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M (h.T_le ht)) p).mp hp
    have e : t * (x * p) * t⁻¹ = (t * x * t⁻¹) * (t * p * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htx) (Subgroup.mem_sup_right htp)
  have hYTA : Y153 Mc M ⊔ T ≤ Subgroup.normalizer ((X ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
    sup_le (fun y hy => A4.mem_normalizer_of_conj_mem (hY y hy))
      (fun t ht => A4.mem_normalizer_of_conj_mem (hT t ht))
  have hAX : Subgroup.normalizer ((X ⊔ pCoreOf 2 M : Subgroup G) : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    have := normalizer_le_normalizer_oTwoUpper (X ⊔ pCoreOf 2 M)
    rwa [hOA] at this
  have hYTX : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (X : Set G) := hYTA.trans hAX
  have hX1 : X = ⊥ := by
    by_contra hne
    have hO2 : pCoreOf 2 X ≠ ⊥ := pCoreOf_ne_bot_of_normal hFH hXH hXn hne hXid
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
      ⟨pCoreOf 2 X, hO2, pCoreOf_isPGroup 2 X, rfl⟩
    obtain ⟨M₀, hM₀, hle⟩ := exists_maxTwoLocal_ge hloc
    have hYT : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      hYTX.trans (normalizer_le_normalizer_pCoreOf 2 X)
    have hM₀M : M₀ = M := (h.lemma_15_3_7_unique h113).2 M₀ ⟨hM₀, hYT.trans hle⟩
    apply hH.2
    rw [← hM₀M]
    exact (hXn.trans (normalizer_le_normalizer_pCoreOf 2 X)).trans hle
  have hK2 : IsPGroup 2 K := by
    intro x
    obtain ⟨k, hk⟩ := exists_odd_orderOf_pow' (x : G)
    have hxk : (x : G) ^ 2 ^ k ∈ X := Subgroup.subset_closure ⟨K.pow_mem x.2 _, hk⟩
    rw [hX1, Subgroup.mem_bot] at hxk
    exact ⟨k, Subtype.ext (by simpa using hxk)⟩
  exact le_pCoreOf_of_le_normalizer 2 hKH hKn hK2

theorem charTwo_M (h : Hyp153 G T Mc M) : CharTwo M := by
  obtain ⟨S₀, hS₀⟩ := h.qtfe.exists_sylow
  exact h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S₀, hS₀ ▸ h.T_le⟩

theorem T_le_normalizer_ZS (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (ZS153 T M V₁ : Set G) := by
  have hi : ((T ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf T).index = 2 := D.relIndex_nS h
  have hnorm : ((T ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two hi
  have hSn : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnorm
  intro t ht
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨h.le_normalizer (h.T_le ht), B2F.le_normalizer_centralizer hSn ht⟩

theorem Z_le_ZS (h : Hyp153 G T Mc M) :
    quasithinOmegaOneCenter T ≤ ZS153 T M V₁ := by
  refine le_inf h.Z_le_VZ fun z hz => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  exact (Subgroup.mem_centralizer_iff.mp (h.T_le_centralizer_Z hs.1) z hz).symm

theorem L₁_le_inf (h11 : StageLemma14111) (h : Hyp153 G T Mc M) :
    L₁Of (Y153 Mc M) (quasithinOmegaOneCenter T) ≤
      Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  unfold L₁Of
  rw [oTwoRes_eq_oTwoUpper]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hxY : x ∈ Y153 Mc M := hx.1.1
  have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    normalizer_le_centralizer_of_card_two h.lemma_15_3_2_two.2 hx.1.2
  have hxMc : x ∈ Mc := (h.lemma_15_3_4 h11) ▸ hxC
  exact ⟨hxY, mem_centralizer_of_odd_of_mem_inf h ⟨hxMc, Y153_le Mc M hxY⟩ hx.2⟩

theorem hypF91_of_153 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂) {H : Subgroup G}
    (hH : IsHTM153 T M H) (hL₁ : L₁Of (Y153 Mc M) (quasithinOmegaOneCenter T) ≤ H) :
    HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H := by
  have h := c.hyp
  have hV := h.elemAbelian
  have hZ2 := h.lemma_15_3_2_two
  have hc4 : Nat.card (ZS153 T M V₁) = 4 := c.decomp.card_ZS h
  have hYM := Y153_le Mc M
  have hYT : Y153 Mc M ⊔ T ≤ M := sup_le hYM h.T_le
  have hYTN : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (VZ T M : Set G) := hYT.trans h.le_normalizer
  have hL₁C := (L₁_le_inf h11 h).trans inf_le_right
  refine
    { sylow := isSylowTwoOf_of_quasithinIsSylowTwo h.qtfe.sylow le_top
      elemAbelian := hV
      normalizes_L := h.T_le.trans (le_normalizer_Y153 Mc M)
      oTwoRes_eq := by
        rw [oTwoRes_eq_oTwoUpper]
        exact oTwoUpper_idem' _
      charTwo_L := CT.CharTwo.of_normal (charTwo_M h) hYM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr (le_normalizer_Y153 Mc M))
      reduced := ?_
      cT := (h.lemma_15_3_7_pCore h113).symm
      card_V₁ := hZ2.2
      V₁_lt_Vp := ?_
      Vp_le_V := inf_le_left
      T_normalizes_V₁ := h.T_le_centralizer_Z.trans (Subgroup.centralizer_le_normalizer _)
      H_le_centralizer := le_centralizer_Z_of_isHTM153 h11 h hH
      L₁T_le_H := sup_le hL₁ hH.1.1
      charTwo_H := charTwo_of_inH' h.qtfe.qtke h.qtfe.sylow hH.1
      ker_le := ker_le_pCoreOf h11 h113 h r46 hH
      L₁T_normalizes_Vp := ?_
      irred := ?_
      normalizer_le := inf_le_right.trans (r46.normalizer_ZS.trans h.le_normalizer)
      o2_trivial := ?_
      weak_e := ?_ }
  ·
    refine A4.isTwoReducedIn_of_pCoreOf_autOn_eq_bot ((h.VZ_le_Y153 h113).trans le_sup_left) hYTN hV ?_
    rw [h.autOn_Y153_sup_T h113]
    have hQ : pCoreOf 2 (autI hV M) ≤ autI hV M := pCoreOf_le 2 _
    have hQn : ((pCoreOf 2 (autI hV M)).subgroupOf (autI hV M)).Normal := inferInstance
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact B2F.eq_bot_of_normal_isPGroup hV h.twoReduced.1 hQ hQn (pCoreOf_isPGroup 2 _)
  ·
    refine lt_of_le_of_ne (Z_le_ZS h) fun heq => ?_
    have := hc4
    rw [← heq, hZ2.2] at this
    omega
  ·
    refine sup_le ?_ (T_le_normalizer_ZS h c.decomp)
    exact hL₁C.trans ((Subgroup.centralizer_le (inf_le_left : ZS153 T M V₁ ≤ VZ T M)).trans
      (Subgroup.centralizer_le_normalizer _))
  ·
    intro W hZW hWZS _
    have h1 : Nat.card W ∣ 4 := hc4 ▸ Subgroup.card_dvd_of_le hWZS
    have h2 : 2 ∣ Nat.card W := hZ2.2 ▸ Subgroup.card_dvd_of_le hZW
    have hle : Nat.card W ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    have hpos : 0 < Nat.card W := Nat.card_pos
    obtain ⟨k, hk⟩ := h2
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · left
      exact (Subgroup.eq_of_le_of_card_ge hZW (by rw [hZ2.2]; omega)).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hWZS (by rw [hc4]; omega)
  ·
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 ((Y153 Mc M ⊔ T) ⊔ H) : Set G)) :=
      ⟨pCoreOf 2 ((Y153 Mc M ⊔ T) ⊔ H), hne, pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨M₀, hM₀, hle⟩ := exists_maxTwoLocal_ge hloc
    have hYT₀ : Y153 Mc M ⊔ T ≤ M₀ :=
      (le_sup_left.trans (le_normalizer_pCoreOf 2 ((Y153 Mc M ⊔ T) ⊔ H))).trans hle
    have hM₀M : M₀ = M := (h.lemma_15_3_7_unique h113).2 M₀ ⟨hM₀, hYT₀⟩
    exact hH.2 (hM₀M ▸ (le_sup_right.trans (le_normalizer_pCoreOf 2 ((Y153 Mc M ⊔ T) ⊔ H))).trans hle)
  ·
    intro g _ h1 _ _
    have hMV : M = Subgroup.normalizer (VZ T M : Set G) := h.isHv_of_inM' h.inM
    have hVg : ∀ w ∈ conjSub g⁻¹ (VZ T M), w ∈ M := by
      intro w hw
      rw [hMV]
      refine A4.mem_normalizer_of_conj_mem fun v hv => ?_
      have hvw : v⁻¹ * w * v * w⁻¹ ∈ VZ T M := by
        have := (h1 (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hv) hw)).1
        simpa [commutatorElement_def] using this
      have hinv : w * v * w⁻¹ ∈ VZ T M := by
        have e : w * v * w⁻¹ = v * (v⁻¹ * w * v * w⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hv hvw
      exact hinv
    have hc : conjSub g⁻¹ (VZ T M) ≤ Subgroup.centralizer (VZ T M : Set G) := by
      rw [conjSub_inv_eq_conjSubgroup]
      exact r46.conj_le_centralizer g (by
        rw [← conjSub_inv_eq_conjSubgroup]
        exact hVg)
    refine ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((conjSub_mono g⁻¹ inf_le_left).trans hc)⟩
    intro v hv
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hc hw) v ((inf_le_left : ZS153 T M V₁ ≤ VZ T M) hv)).symm

end C1Pack153

theorem stage15348 (h11 : StageLemma14111) (h113 : StageLemma14113) : Stage15348 := by
  intro G _ _ T Mc M V₁ V₂ t c _ r46 _ H hH hcase
  refine C1Pack153.hypF91_of_153 h11 h113 c r46 hH ?_
  have hL₁ := C1Pack153.L₁_le_inf h11 c.hyp
  rcases c.hyp.lemma_15_3_7_cases h113 with h1 | h2
  · refine hL₁.trans ?_
    rw [← h1.1]
    exact (c.hyp.pCoreOf_Y153_le_Sgp153 h113 c.decomp).trans (inf_le_left.trans hH.1.1)
  · exact hL₁.trans (hcase h2)

end CFSG.Quasithin
