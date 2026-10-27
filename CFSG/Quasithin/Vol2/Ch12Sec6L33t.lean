module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33a
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126f

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P F126 Equiv
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Fix

variable {T V L V₁ Vp H : Subgroup G}

@[expose] def Fix5 (V₁ Vp H : Subgroup G) (f : MulAut ↥(UT V₁ Vp H)) : Prop :=
  ∀ w : ↥(UT V₁ Vp H), (w : SecQuot (N1 V₁) V₁) ∈ tildeOf V₁ Vp → f w = w

omit [Finite G] in
theorem Fix5.mul {f g : MulAut ↥(UT V₁ Vp H)} (hf : Fix5 V₁ Vp H f) (hg : Fix5 V₁ Vp H g) :
    Fix5 V₁ Vp H (f * g) := fun w hw => by rw [MulAut.mul_apply, hg w hw, hf w hw]

omit [Finite G] in
theorem thetaH_mem_tilde (h : HypF91 T V L V₁ Vp H) {z : ↥H}
    (hz : (z : G) ∈ Subgroup.normalizer (Vp : Set G)) (w : ↥(UT V₁ Vp H))
    (hw : (w : SecQuot (N1 V₁) V₁) ∈ tildeOf V₁ Vp) :
    ((thetaH h z w : ↥(UT V₁ Vp H)) : SecQuot (N1 V₁) V₁) ∈ tildeOf V₁ Vp := by
  obtain ⟨⟨v, hvN⟩, hv, hvw⟩ := mem_secImg.1 hw
  rw [thetaH_apply, ← hvw, thetaH_apply_secMk]
  exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.1 hz v).1 hv)

omit [Finite G] in
theorem Fix5.conj (h : HypF91 T V L V₁ Vp H) {z : ↥H}
    (hz : (z : G) ∈ Subgroup.normalizer (Vp : Set G)) {f : MulAut ↥(UT V₁ Vp H)}
    (hf : Fix5 V₁ Vp H f) : Fix5 V₁ Vp H (thetaH h z * f * (thetaH h z)⁻¹) := by
  intro w hw
  have hz' : ((z⁻¹ : ↥H) : G) ∈ Subgroup.normalizer (Vp : Set G) := Subgroup.inv_mem _ hz
  have h1 := thetaH_mem_tilde h hz' w hw
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, hf _ h1, ← MulAut.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, MulAut.one_apply]

omit [Finite G] in
theorem fix5_thetaH_iff (h : HypF91 T V L V₁ Vp H) (z : ↥H) (hVN : Vp ≤ N1 V₁) :
    Fix5 V₁ Vp H (thetaH h z) ↔ ∀ v ∈ Vp, ((z : G) * v * (z : G)⁻¹)⁻¹ * v ∈ V₁ := by
  constructor
  · intro hf v hv
    have hw : secMk (N1 V₁) V₁ ⟨v, hVN hv⟩ ∈ UT V₁ Vp H :=
      secImg_mono (le_conjClosure Vp H) (secMk_mem_secImg hv)
    have h1 := congrArg Subtype.val (hf ⟨_, hw⟩ (secMk_mem_secImg hv))
    rw [thetaH_apply] at h1
    change toSec h z * secMk (N1 V₁) V₁ ⟨v, hVN hv⟩ * (toSec h z)⁻¹ = _ at h1
    rw [thetaH_apply_secMk, secMk_eq_secMk_iff] at h1
    exact h1
  · intro hc w hw
    obtain ⟨⟨v, hvN⟩, hv, hvw⟩ := mem_secImg.1 hw
    apply Subtype.ext
    rw [thetaH_apply, ← hvw, thetaH_apply_secMk, secMk_eq_secMk_iff]
    exact hc v hv

end Fix

section Three

variable {T L V H K : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
omit [Finite G] in
theorem conjSub_mem_cComp {H K : Subgroup G} (hK : K ∈ cComp H) {g : G} (hg : g ∈ H) :
    conjSub g K ∈ cComp H := by
  have h := cComp_map_mulEquiv (MulAut.conj g) hK
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact H.mul_mem (H.mul_mem hg hz) (H.inv_mem hg)
    · intro hx
      refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  rwa [hH] at h

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {g : G} {K : Subgroup G} (h : conjSub g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact mul_mem_conjSub hx
  · intro hx
    rw [← h] at hx
    have := mem_conjSub.1 hx
    simpa [mul_assoc] using this

theorem a5_pow_three : ∀ a : ↥(alternatingGroup (Fin 5)), a ^ 9 = 1 → a ^ 3 = 1 := by
  decide +kernel

theorem pow_three_of_mulEquiv {X : Type*} [Group X] (e : X ≃* ↥(alternatingGroup (Fin 5))) {x : X}
    (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  exact a5_pow_three _ (by rw [← map_pow, hx, map_one])

theorem exists_three_elt (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (h2 : Case2 T L H K) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    ∃ x ∈ S126.star H (Li L F.V1), x ∈ S126.star H K ∧ x ^ 3 = 1 ∧
      ¬ Fix5 F.V1 F.V5 H (psiH h918.toHypF98.toHypF91 x) := by
  set h := h918.toHypF98.toHypF91 with hh
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTH : T ≤ H := le_sup_right.trans h.L₁T_le_H
  have htH : t ∈ H := hTH ht
  have hKc : K ∈ cComp H := h918.K_cComp
  set K₂ := conjSub t⁻¹ K with hK₂
  have hK₂c : K₂ ∈ cComp H := conjSub_mem_cComp hKc (H.inv_mem htH)
  have hne : K ≠ K₂ := fun he => htK (by
    have h1 : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSub_eq he.symm
    simpa using Subgroup.inv_mem _ h1)
  obtain ⟨-, ⟨e₁⟩, ⟨e₀⟩, -, hcardH, -⟩ := h2
  have hA5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥(S126.star H K) := e₁.isSimpleGroup
  set tb : S126.HStar H := QuotientGroup.mk ⟨t, htH⟩ with htb
  have hK₂s : S126.star H K₂ = (S126.star H K).map (MulAut.conj tb⁻¹).toMonoidHom := by
    rw [hK₂, star_conjSub (H.inv_mem htH)]
    rfl
  set e₂ : ↥(S126.star H K) ≃* ↥(S126.star H K₂) :=
    ((S126.star H K).equivMapOfInjective _ (MulAut.conj tb⁻¹).injective).trans
      (MulEquiv.subgroupCongr hK₂s.symm)
  have hs₂ : IsSimpleGroup ↥(S126.star H K₂) := e₂.symm.isSimpleGroup
  have hcomm := commute_star hKc hK₂c hne hs hs₂
  have hnonab : ¬ ∀ a b : ↥(S126.star H K), a * b = b * a := by
    intro hab
    have : ∀ a b : ↥(alternatingGroup (Fin 5)), a * b = b * a := fun a b => by
      have := congrArg e₁ (hab (e₁.symm a) (e₁.symm b))
      simpa using this
    exact absurd (this ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
      ⟨swap 1 2 * swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩) (by decide)
  have hi : S126.star H K ⊓ S126.star H K₂ = ⊥ := by
    have hn : ((S126.star H K₂).subgroupOf (S126.star H K)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hcomm g g.2 n hn
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, this, mul_inv_cancel_right]
      exact hn⟩
    rcases hn.eq_bot_or_eq_top with hb | ht'
    · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hb
      rw [inf_comm]
      exact hb
    · exfalso
      apply hnonab
      intro a b
      have hb : (b : S126.HStar H) ∈ S126.star H K₂ := by
        have : b ∈ (S126.star H K₂).subgroupOf (S126.star H K) := ht' ▸ Subgroup.mem_top b
        exact this
      exact Subtype.ext (hcomm a a.2 b hb)
  have hc60 : Nat.card ↥(S126.star H K) = 60 := by
    rw [Nat.card_congr e₁.toEquiv, S126.card_alternatingGroup_five]
  have hc60' : Nat.card ↥(S126.star H K₂) = 60 := by rw [← Nat.card_congr e₂.toEquiv, hc60]
  have hc3600 : Nat.card ↥(S126.star H (conjClosure K T)) = 3600 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_prod, S126.card_alternatingGroup_five]
  have hKK₀ : K ≤ conjClosure K T := le_conjClosure K T
  have hK₂K₀ : K₂ ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_conjClosure (T.inv_mem ht) hk
  have hstar_mono : ∀ {X Y : Subgroup G}, X ≤ Y → S126.star H X ≤ S126.star H Y :=
    fun hXY => Subgroup.map_mono fun x hx => hXY hx
  have hsup : S126.star H K ⊔ S126.star H K₂ = S126.star H (conjClosure K T) :=
    Subgroup.eq_of_le_of_card_ge (sup_le (hstar_mono hKK₀) (hstar_mono hK₂K₀)) (by
      rw [card_sup_of_commute hcomm hi, hc60, hc60', hc3600])
  have hK₀n : (S126.star H (conjClosure K T)).Normal := by
    have : ((conjClosure K T).subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (h918.K₀_normal g.2) n).1 hn⟩
    exact this.map _ (QuotientGroup.mk'_surjective _)
  have hidx : (S126.star H (conjClosure K T)).index ∣ 8 := by
    have hc := (S126.star H (conjClosure K T)).card_mul_index
    rw [hc3600] at hc
    rcases hcardH with h1 | h1 <;> rw [h1] at hc
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  have hmem₀ : ∀ x : S126.HStar H, x ^ 9 = 1 → x ∈ S126.star H (conjClosure K T) := by
    intro x hx
    have h1 : orderOf (QuotientGroup.mk x : S126.HStar H ⧸ S126.star H (conjClosure K T)) ∣ 9 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
    have h2 : orderOf (QuotientGroup.mk x : S126.HStar H ⧸ S126.star H (conjClosure K T)) ∣ 8 :=
      (orderOf_dvd_natCard _).trans hidx
    have h3 := Nat.dvd_gcd h1 h2
    have h4 : orderOf (QuotientGroup.mk x : S126.HStar H ⧸ S126.star H (conjClosure K T)) = 1 :=
      Nat.dvd_one.1 (by simpa using h3)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
    exact h4
  have h9 := nine_dvd_card_star_L1 F hH h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L1s := S126.star H (Li L F.V1) with hL1s
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L1s) 3 (n := 2) h9
  set P := P₀.map L1s.subtype with hP
  have hPc : Nat.card P = 9 := by
    rw [hP, Subgroup.card_map_of_injective L1s.subtype_injective, hP₀]
    rfl
  have hPL : P ≤ L1s := Subgroup.map_subtype_le _
  have hPK : P ≤ S126.star H K ⊔ S126.star H K₂ := by
    rw [hsup]
    intro p hp
    apply hmem₀
    have := pow_card_eq_one' (G := ↥P) (x := ⟨p, hp⟩)
    rw [hPc] at this
    exact congrArg Subtype.val this
  have hdec := exists_mul_of_le_sup hcomm hi hPK hPc (by rw [hc60]; norm_num)
    (by rw [hc60']; norm_num)
  have hL15 : Li L F.V1 ≤ Subgroup.normalizer (F.V5 : Set G) :=
    le_sup_left.trans h.L₁T_normalizes_Vp
  have hT5 : T ≤ Subgroup.normalizer (F.V5 : Set G) := le_sup_right.trans h.L₁T_normalizes_Vp
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hFixT : ∀ s (hs : s ∈ T), ∀ f : MulAut ↥(UT F.V1 F.V5 H), Fix5 F.V1 F.V5 H f →
      Fix5 F.V1 F.V5 H (psiH h (QuotientGroup.mk ⟨s, hTH hs⟩) * f *
        (psiH h (QuotientGroup.mk ⟨s, hTH hs⟩))⁻¹) := fun s hs _ hf =>
    Fix5.conj h (hT5 hs) hf
  have hFixL : ∀ g ∈ L1s, ∀ f : MulAut ↥(UT F.V1 F.V5 H), Fix5 F.V1 F.V5 H f →
      Fix5 F.V1 F.V5 H (psiH h g * f * (psiH h g)⁻¹) := by
    rintro _ ⟨z, hz, rfl⟩ f hf
    exact Fix5.conj h (hL15 hz) hf
  have hPnt : ∃ p ∈ P, ¬ Fix5 F.V1 F.V5 H (psiH h p) := by
    by_contra hall
    push Not at hall
    obtain ⟨l, hl1, hlV, hla⟩ := S126L1b.exists_mem_L1 F aP_mem aP_pow_three aP_block
    have hlH : l ∈ H := le_sup_left.trans h.L₁T_le_H hl1
    set N := Nat.card (S126.HStar H) / 9 with hN
    have hN9 : 9 * N = Nat.card (S126.HStar H) := by
      rcases hcardH with h1 | h1 <;> rw [hN, h1]
    have hN3 : N % 3 ≠ 0 := by
      rcases hcardH with h1 | h1 <;> rw [hN, h1] <;> norm_num
    have hxL : (QuotientGroup.mk ⟨l, hlH⟩ : S126.HStar H) ^ N ∈ L1s :=
      L1s.pow_mem ⟨⟨l, hlH⟩, hl1, rfl⟩ N
    set xx : ↥L1s := ⟨_, hxL⟩ with hxx
    have hx9 : xx ^ 9 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hxx, ← pow_mul, mul_comm, hN9, pow_card_eq_one']
      rfl
    have hL1c : ¬ 27 ∣ Nat.card ↥L1s := by
      intro h27
      have h1 := h27.trans (Subgroup.card_dvd_of_le (le_top : L1s ≤ ⊤))
      rw [Subgroup.card_top] at h1
      rcases hcardH with h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1
    have hfac : (Nat.card ↥L1s).factorization 3 = 2 := by
      have hne : Nat.card ↥L1s ≠ 0 := Nat.card_pos.ne'
      have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1
        (show 3 ^ 2 ∣ Nat.card ↥L1s from h9)
      have h2 : ¬ 3 ≤ (Nat.card ↥L1s).factorization 3 := fun h3 =>
        hL1c ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).2 h3)
      omega
    obtain ⟨Q₁, hQ₁⟩ := (IsPGroup.of_card (p := 3) (n := 2) hP₀).exists_le_sylow
    have hQ₁c : Nat.card ↥(Q₁ : Subgroup ↥L1s) = 9 := by
      rw [Sylow.card_eq_multiplicity, hfac]
      rfl
    have hQP : (Q₁ : Subgroup ↥L1s) = P₀ :=
      (Subgroup.eq_of_le_of_card_ge hQ₁ (by rw [hQ₁c, hP₀]; rfl)).symm
    have hxp : IsPGroup 3 ↥(Subgroup.zpowers xx) := by
      have h1 : orderOf xx ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one hx9
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨Q₀, hQ₀⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L1s Q₁ Q₀
    have hxQ : xx ∈ MulAut.conj g • (Q₁ : Subgroup ↥L1s) := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hQ₀ (Subgroup.mem_zpowers xx)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hQP] at hxQ
    have hp0 : ((g⁻¹ * xx * g : ↥L1s) : S126.HStar H) ∈ P := by
      refine ⟨g⁻¹ * xx * g, ?_, rfl⟩
      convert hxQ using 1
      simp [mul_assoc]
    have hfix := hFixL g g.2 _ (hall _ hp0)
    have e : psiH h (g : S126.HStar H) * psiH h ((g⁻¹ * xx * g : ↥L1s) : S126.HStar H) *
        (psiH h (g : S126.HStar H))⁻¹ = psiH h (QuotientGroup.mk ⟨l, hlH⟩ ^ N) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      simp [mul_assoc]
      rfl
    rw [e, ← QuotientGroup.mk_pow, psiH_mk,
      fix5_thetaH_iff h _ hVN] at hfix
    have hA : ActEq (aP ^ N) 1 := by
      refine actEq_of_conj F (Subgroup.pow_mem _ hlV N) (Subgroup.one_mem _) (hla.pow hlV N)
        (ActsAs.one F) fun v hv => ?_
      have := hfix v hv
      rw [Subgroup.coe_pow] at this
      simpa using this
    rw [pow_eq_pow_mod N aP_pow_three] at hA
    have := indep_ab (i := ⟨N % 3, Nat.mod_lt _ (by norm_num)⟩) (j := 0) (by simpa using hA)
    exact hN3 (congrArg Fin.val this.1)
  have htL1 : t ∈ Subgroup.normalizer (Li L F.V1 : Set G) := by
    refine S126L19b.normalizer_le_normalizer_oTwoRes' _ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hH.hyp.normalizes ht) x
    have h2 := Subgroup.mem_normalizer_iff.1
      (Subgroup.le_normalizer (h.T_normalizes_V₁ ht)) x
    exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
  obtain ⟨p, hp, hpn⟩ := hPnt
  obtain ⟨a, ⟨haP, haK⟩, b, ⟨hbP, hbK⟩, rfl⟩ := hdec p hp
  have hpow9 : ∀ q ∈ P, q ^ 9 = 1 := fun q hq => by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨q, hq⟩)
    rw [hPc] at this
    exact congrArg Subtype.val this
  by_cases ha : Fix5 F.V1 F.V5 H (psiH h a)
  ·
    have hb : ¬ Fix5 F.V1 F.V5 H (psiH h b) := fun hb => hpn (by rw [map_mul]; exact ha.mul hb)
    have hb3 : b ^ 3 = 1 := by
      have := pow_three_of_mulEquiv (e₂.symm.trans e₁) (x := ⟨b, hbK⟩)
        (Subtype.ext (hpow9 b hbP))
      exact congrArg Subtype.val this
    refine ⟨tb * b * tb⁻¹, ?_, ?_, ?_, ?_⟩
    · obtain ⟨z, hz, hzb⟩ := hPL hbP
      refine ⟨⟨t, htH⟩ * z * ⟨t, htH⟩⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 htL1 z).1 hz
      · rw [← hzb]
        simp [htb]
    · rw [hK₂s] at hbK
      obtain ⟨k, hk, rfl⟩ := hbK
      simpa [MulAut.conj_apply, mul_assoc] using hk
    · rw [conj_pow, hb3, mul_one, mul_inv_cancel]
    · intro hx
      apply hb
      have h1 := hFixT t⁻¹ (T.inv_mem ht) _ hx
      have e : psiH h (QuotientGroup.mk ⟨t⁻¹, hTH (T.inv_mem ht)⟩) * psiH h (tb * b * tb⁻¹) *
          (psiH h (QuotientGroup.mk ⟨t⁻¹, hTH (T.inv_mem ht)⟩))⁻¹ = psiH h b := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        have : (QuotientGroup.mk ⟨t⁻¹, hTH (T.inv_mem ht)⟩ : S126.HStar H) = tb⁻¹ := by
          rw [htb, ← QuotientGroup.mk_inv]
          rfl
        rw [this]
        group
      rw [e] at h1
      exact h1
  · have ha3 : a ^ 3 = 1 := by
      have := pow_three_of_mulEquiv e₁ (x := ⟨a, haK⟩) (Subtype.ext (hpow9 a haP))
      exact congrArg Subtype.val this
    exact ⟨a, hPL haP, haK, ha3, ha⟩

end Three

end CFSG.Quasithin.H13.L1233
