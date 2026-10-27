module

public import CFSG.Quasithin.Background.ONanE68AltQ

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Quasithin.H13.KG68
open scoped commutatorElement

section Lift

variable {G H' : Type} [Group G] [Group H']

@[expose] def liftSub (L : Subgroup G) (Λ : ↥L →* H') (K' : Subgroup H') : Subgroup G :=
  (K'.comap Λ).map L.subtype

variable {L : Subgroup G} {Λ : ↥L →* H'} {K' : Subgroup H'}

theorem mem_liftSub {x : G} : x ∈ liftSub L Λ K' ↔ ∃ h : x ∈ L, Λ ⟨x, h⟩ ∈ K' := by
  unfold liftSub
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem liftSub_le : liftSub L Λ K' ≤ L := fun _ hx => (mem_liftSub.1 hx).1

theorem mem_liftSub_of_mem {l : ↥L} (h : Λ l ∈ K') : (l : G) ∈ liftSub L Λ K' :=
  mem_liftSub.2 ⟨l.2, h⟩

theorem liftSub_mono {K'' : Subgroup H'} (h : K' ≤ K'') : liftSub L Λ K' ≤ liftSub L Λ K'' :=
  fun _ hx => let ⟨hxL, hx'⟩ := mem_liftSub.1 hx; mem_liftSub.2 ⟨hxL, h hx'⟩

@[expose] def liftHom (L : Subgroup G) (Λ : ↥L →* H') (K' : Subgroup H') :
    ↥(liftSub L Λ K') →* H' :=
  Λ.comp (Subgroup.inclusion liftSub_le)

@[expose] def liftRho (L : Subgroup G) (Λ : ↥L →* H') (K' : Subgroup H') :
    ↥(liftSub L Λ K') →* ↥K' :=
  (liftHom L Λ K').codRestrict K' (fun x => (mem_liftSub.1 x.2).2)

theorem liftRho_apply (x : ↥(liftSub L Λ K')) :
    ((liftRho L Λ K' x : ↥K') : H') = Λ ⟨(x : G), liftSub_le x.2⟩ :=
  rfl

theorem liftRho_surjective (hKr : K' ≤ Λ.range) : Function.Surjective (liftRho L Λ K') := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl⟩ := hKr hk
  refine ⟨⟨(l : G), mem_liftSub_of_mem (by rw [hl]; exact hk)⟩, Subtype.ext ?_⟩
  rw [liftRho_apply]
  exact hl

theorem liftRho_ker_isPGroup (hker : ∀ l : ↥L, Λ l = 1 ↔ (l : G) ∈ pCoreOf 2 L) :
    IsPGroup 2 (liftRho L Λ K').ker := by
  rintro ⟨x, hx⟩
  have h1 : Λ ⟨(x : G), liftSub_le x.2⟩ = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact this
  obtain ⟨y, hyG, hy⟩ := mem_pCoreOf_iff'.1 ((hker _).1 h1)
  have hyx : y = ⟨(x : G), liftSub_le x.2⟩ := Subtype.ext hyG
  subst hyx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hy⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hk
  simpa using this

end Lift

section Props

variable {G H' : Type} [Group G] [Group H'] {L : Subgroup G} {Λ : ↥L →* H'} {K' : Subgroup H'}
  {m : ℕ}

structure LiftHyp (L : Subgroup G) (Λ : ↥L →* H') (K' : Subgroup H') (m : ℕ) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥L
  ker : ∀ l : ↥L, Λ l = 1 ↔ (l : G) ∈ pCoreOf 2 L
  le_range : K' ≤ Λ.range
  charTwo : CharTwo K'
  maximal : ∀ Y : Subgroup H', K' ≤ Y → Y ≤ Λ.range → Y = K' ∨ Y = Λ.range
  alt : IsAltOverElemAbelian K' 4 m
  simple : IsSimpleGroup (alternatingGroup (Fin m))
  card : Nat.card (alternatingGroup (Fin m)) = 360 ∨ Nat.card (alternatingGroup (Fin m)) = 2520

theorem LiftHyp.pCoreOf_le (h : LiftHyp L Λ K' m) : pCoreOf 2 L ≤ liftSub L Λ K' := by
  intro z hz
  obtain ⟨y, hyG, -⟩ := mem_pCoreOf_iff'.1 hz
  subst hyG
  exact mem_liftSub_of_mem (by rw [(h.ker y).2 hz]; exact K'.one_mem)

theorem LiftHyp.charTwo_lift (h : LiftHyp L Λ K' m) : CharTwo (liftSub L Λ K') :=
  charTwo_of_surj (liftRho L Λ K') (liftRho_surjective h.le_range) (liftRho_ker_isPGroup h.ker)
    h.charTwo

theorem LiftHyp.alt_lift (h : LiftHyp L Λ K' m) :
    ∃ (E' : Subgroup H') (αh : ↥(liftSub L Λ K') →* alternatingGroup (Fin m)),
      E' ≤ K' ∧ IsElemAbelian 2 E' ∧ Nat.card ↥E' = 2 ^ 4 ∧
      liftSub L Λ E' ≤ liftSub L Λ K' ∧
      IsPGroup 2 ↥(liftSub L Λ E') ∧ Function.Surjective αh ∧
      αh.ker = (liftSub L Λ E').subgroupOf (liftSub L Λ K') := by
  obtain ⟨E', α', hE'K, hE'ea, hE'c, hα', hker'⟩ := h.alt
  refine ⟨E', α'.comp (liftRho L Λ K'), hE'K, hE'ea, hE'c, liftSub_mono hE'K, ?_,
    hα'.comp (liftRho_surjective h.le_range), ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨hyL, hyE⟩ := mem_liftSub.1 hy
    have h2 : (Λ ⟨y, hyL⟩) ^ 2 = 1 := hE'ea.2 _ hyE
    have h3 : Λ ⟨y ^ 2, L.pow_mem hyL 2⟩ = 1 := by
      have : (⟨y ^ 2, L.pow_mem hyL 2⟩ : ↥L) = ⟨y, hyL⟩ ^ 2 := rfl
      rw [this, map_pow]
      exact h2
    obtain ⟨z, hzG, hz⟩ := mem_pCoreOf_iff'.1 ((h.ker _).1 h3)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨z, hz⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h4 : ((z : ↥L) : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun w : ↥(CFSG.pCore 2 ↥L) => ((w : ↥L) : G)) hk
      simpa using this
    have hz2 : (z : G) = y ^ 2 := hzG
    rw [hz2, ← pow_mul] at h4
    show y ^ 2 ^ (k + 1) = 1
    rw [pow_succ']
    exact h4
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker',
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_liftSub]
    exact ⟨fun hx => ⟨liftSub_le x.2, hx⟩, fun ⟨_, hx⟩ => hx⟩

theorem LiftHyp.not_isPGroup (h : LiftHyp L Λ K' m) :
    ¬ IsPGroup 2 (alternatingGroup (Fin m)) := by
  intro hp
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  have h3 : 3 ∣ 2 ^ n := by
    rcases h.card with h | h <;> rw [h] at hn <;> rw [← hn] <;> norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem LiftHyp.noChi0 (h : LiftHyp L Λ K' m) : ¬ HasChi0Block (liftSub L Λ K') := by
  obtain ⟨E', αh, -, -, -, -, hE2h, hαh, hkerh⟩ := h.alt_lift
  exact not_hasChi0Block_of_hom h.simple hE2h αh hαh hkerh h.card

theorem LiftHyp.residual [Finite G] (h : LiftHyp L Λ K' m) :
    liftSub L Λ K' ≤ twoPrimeResidual (liftSub L Λ K') := by
  obtain ⟨E', αh, -, -, -, -, hE2h, hαh, hkerh⟩ := h.alt_lift
  exact le_twoPrimeResidual_of_hom h.simple
    (by rcases h.card with h | h <;> rw [h] <;> norm_num) hE2h αh hαh hkerh

theorem LiftHyp.maximal_lift (h : LiftHyp L Λ K' m) :
    ∀ Y : Subgroup G, liftSub L Λ K' ≤ Y → Y ≤ L → Y = liftSub L Λ K' ∨ Y = L := by
  intro Y hKY hYL
  set Y' : Subgroup H' := (Y.subgroupOf L).map Λ with hY'
  have h1 : K' ≤ Y' := by
    intro k hk
    obtain ⟨l, hl⟩ := h.le_range hk
    exact ⟨l, hKY (mem_liftSub_of_mem (by rw [hl]; exact hk)), hl⟩
  have h2 : Y' ≤ Λ.range := fun y ⟨l, _, hl⟩ => ⟨l, hl⟩
  rcases h.maximal Y' h1 h2 with e | e
  · left
    refine le_antisymm ?_ hKY
    intro y hy
    have hyL : y ∈ L := hYL hy
    have : Λ ⟨y, hyL⟩ ∈ Y' := ⟨⟨y, hyL⟩, hy, rfl⟩
    rw [e] at this
    exact mem_liftSub.2 ⟨hyL, this⟩
  · right
    refine le_antisymm hYL fun l hl => ?_
    have : Λ ⟨l, hl⟩ ∈ Y' := by rw [e]; exact ⟨⟨l, hl⟩, rfl⟩
    obtain ⟨y, hy, hyl⟩ := this
    have hz : y⁻¹ * ⟨l, hl⟩ ∈ Λ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyl, inv_mul_cancel]
    have hzK : ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ liftSub L Λ K' := h.pCoreOf_le ((h.ker _).1 hz)
    have hl' : l = (y : G) * ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [hl']
    exact Y.mul_mem hy (hKY hzK)

theorem not_comm_of_simple {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hc : Nat.card S = 360 ∨ Nat.card S = 2520) : ¬ ∀ a b : S, a * b = b * a := by
  intro hcomm
  have h2 : 2 ∣ Nat.card S := by rcases hc with h | h <;> rw [h] <;> norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs2⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2
  have hN : (Subgroup.zpowers s).Normal :=
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by rw [hcomm g n]; group
      rw [this]
      exact hn⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.zpowers s) with h | h
  · have : s = 1 := Subgroup.zpowers_eq_bot.1 h
    rw [this, orderOf_one] at hs2
    omega
  · have h3 : Nat.card ↥(Subgroup.zpowers s) = Nat.card S := by rw [h, Subgroup.card_top]
    rw [Nat.card_zpowers, hs2] at h3
    rcases hc with h | h <;> omega

theorem commutatorElement_mul_central_left {X : Type*} [Group X] {a b z : X}
    (hz : z ∈ Subgroup.center X) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have c := Subgroup.mem_center_iff.1 hz b
  have e : z * b * z⁻¹ = b := by rw [← c]; group
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [e]; rfl

theorem commutatorElement_mul_central_right {X : Type*} [Group X] {a b z : X}
    (hz : z ∈ Subgroup.center X) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have c := Subgroup.mem_center_iff.1 hz a⁻¹
  have e : z * a⁻¹ * z⁻¹ = a⁻¹ := by rw [← c]; group
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [e]; rfl

theorem LiftHyp.eq_of_normal [Finite G] (h : LiftHyp L Λ K' m)
    (hN : L ≤ Subgroup.normalizer (liftSub L Λ K' : Set G)) : liftSub L Λ K' = L := by
  set Kl : Subgroup ↥L := K'.comap Λ with hKl
  have hKln : Kl.Normal := by
    refine ⟨fun k hk l => ?_⟩
    have hk' : (k : G) ∈ liftSub L Λ K' := mem_liftSub_of_mem hk
    have := (Subgroup.mem_normalizer_iff.1 (hN l.2) (k : G)).1 hk'
    obtain ⟨hmL, hm⟩ := mem_liftSub.1 this
    exact hm
  have hs := h.quasisimple.2.1
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' _ with hπ
  have hmapn : (Kl.map π).Normal := Subgroup.Normal.map hKln π (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (Kl.map π) with hb | ht
  · exfalso
    have hKc : ∀ k ∈ Kl, k ∈ Subgroup.center ↥L := by
      intro k hk
      have : π k ∈ Kl.map π := ⟨k, hk, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).1 this
    obtain ⟨E', α', hE'K, -, -, hα', -⟩ := h.alt
    apply not_comm_of_simple h.simple h.card
    intro s1 s2
    obtain ⟨a, rfl⟩ := hα' s1
    obtain ⟨b, rfl⟩ := hα' s2
    obtain ⟨la, hla⟩ := h.le_range a.2
    obtain ⟨lb, hlb⟩ := h.le_range b.2
    have hla' : la ∈ Kl := by show Λ la ∈ K'; rw [hla]; exact a.2
    have hcomm : lb * la = la * lb := Subgroup.mem_center_iff.1 (hKc la hla') lb
    have hab : (a * b : ↥K') = b * a := by
      apply Subtype.ext
      have h1 : Λ (la * lb) = Λ (lb * la) := by rw [hcomm]
      rw [map_mul, map_mul, hla, hlb] at h1
      exact h1
    rw [← map_mul, ← map_mul, hab]
  · have htop : commutator ↥L = ⊤ := Group.isPerfect_def.mp h.quasisimple.1
    have hKl_top : Kl = ⊤ := by
      refine eq_top_iff.2 ?_
      have hcomm : commutator ↥L ≤ Kl := by
        rw [commutator_def, Subgroup.commutator_le]
        intro g1 _ g2 _
        obtain ⟨k1, hk1, hk1'⟩ : π g1 ∈ Kl.map π := by rw [ht]; trivial
        obtain ⟨k2, hk2, hk2'⟩ : π g2 ∈ Kl.map π := by rw [ht]; trivial
        have hz1 : k1⁻¹ * g1 ∈ Subgroup.center ↥L := (QuotientGroup.eq).1 hk1'
        have hz2 : k2⁻¹ * g2 ∈ Subgroup.center ↥L := (QuotientGroup.eq).1 hk2'
        have e1 : g1 = k1 * (k1⁻¹ * g1) := by group
        have e2 : g2 = k2 * (k2⁻¹ * g2) := by group
        rw [e1, e2, commutatorElement_mul_central_left hz1, commutatorElement_mul_central_right hz2]
        simp only [commutatorElement_def]
        exact Kl.mul_mem (Kl.mul_mem (Kl.mul_mem hk1 hk2) (Kl.inv_mem hk1)) (Kl.inv_mem hk2)
      rw [← htop]
      exact hcomm
    ext x
    constructor
    · exact fun hx => liftSub_le hx
    · intro hx
      have : (⟨x, hx⟩ : ↥L) ∈ Kl := by rw [hKl_top]; trivial
      exact mem_liftSub.2 ⟨hx, this⟩

theorem LiftHyp.ne [Finite G] [Finite H'] (h : LiftHyp L Λ K' m) : liftSub L Λ K' ≠ L := by
  intro hKL
  obtain ⟨E', αh, hE'K, hE'ea, hE'c, hEK, hE2h, hαh, hkerh⟩ := h.alt_lift
  have hEn : ((liftSub L Λ E').subgroupOf (liftSub L Λ K')).Normal := hkerh ▸ αh.normal_ker
  have hle := le_pCoreOf_of_normal hEK hEn hE2h
  rw [hKL] at hle
  have : Nontrivial ↥E' := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE'c]
    norm_num
  obtain ⟨e, he⟩ := exists_ne (1 : ↥E')
  obtain ⟨l, hl⟩ := h.le_range (hE'K e.2)
  have hlE : (l : G) ∈ liftSub L Λ E' := mem_liftSub_of_mem (by rw [hl]; exact e.2)
  have := (h.ker l).2 (hle hlE)
  exact he (Subtype.ext (hl.symm.trans this))

theorem LiftHyp.centralizer_trivial [Finite G] [Finite H'] (h : LiftHyp L Λ K' m) :
    ∀ l ∈ L, (∀ k ∈ liftSub L Λ K', l * k * l⁻¹ * k⁻¹ ∈ pCoreOf 2 L) → l ∈ pCoreOf 2 L := by
  intro l hlL hcomm
  have hlN : l ∈ Subgroup.normalizer (liftSub L Λ K' : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    have e : l * k * l⁻¹ = (l * k * l⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact (liftSub L Λ K').mul_mem (h.pCoreOf_le (hcomm k hk)) hk
  have hlK : l ∈ liftSub L Λ K' := by
    rcases h.maximal_lift (L ⊓ Subgroup.normalizer (liftSub L Λ K' : Set G))
      (le_inf liftSub_le Subgroup.le_normalizer) inf_le_left with e | e
    · rw [← e]
      exact ⟨hlL, hlN⟩
    · exact absurd (h.eq_of_normal (inf_eq_left.1 e)) h.ne
  obtain ⟨E', α', hE'K, hE'ea, hE'c, hα', hker'⟩ := h.alt
  have hcK : Λ ⟨l, hlL⟩ ∈ K' := (mem_liftSub.1 hlK).2
  have hcent : ∀ k ∈ K', k * Λ ⟨l, hlL⟩ = Λ ⟨l, hlL⟩ * k := by
    intro k hk
    obtain ⟨y, hy⟩ := h.le_range hk
    have hyK : (y : G) ∈ liftSub L Λ K' := mem_liftSub_of_mem (by rw [hy]; exact hk)
    have hz : Λ (⟨l, hlL⟩ * y * ⟨l, hlL⟩⁻¹ * y⁻¹) = 1 := (h.ker _).2 (hcomm y hyK)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy] at hz
    exact (commutatorElement_eq_one_iff_mul_comm.1 hz).symm
  have hE'2 : IsPGroup 2 ↥E' := B2F.isPGroup_of_isElemAbelian hE'ea
  have hCE : K' ⊓ Subgroup.centralizer (E' : Set H') ≤ E' := by
    have h1 : K' ⊓ Subgroup.centralizer (pCoreOf 2 K' : Set H') ≤ pCoreOf 2 K' := h.charTwo
    rwa [pCoreOf_eq_of_hom h.simple h.not_isPGroup hE'K hE'2 α' hα' hker'] at h1
  have hcE : Λ ⟨l, hlL⟩ ∈ E' :=
    hCE ⟨hcK, Subgroup.mem_centralizer_iff.2 fun e he => hcent e (hE'K he)⟩
  have h5 : 5 ∣ Nat.card ↥K' := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α'.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α' hα').toEquiv] at h1
    rw [h1]
    apply Dvd.dvd.mul_right
    rcases h.card with h | h <;> rw [h] <;> norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg5⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 5 h5
  have hgo : orderOf (g : H') = 5 := by rw [Subgroup.orderOf_coe]; exact hg5
  have hc1 : Λ ⟨l, hlL⟩ = 1 :=
    eq_one_of_central_of_order_five hE'K (hker' ▸ α'.normal_ker) (by rw [hE'c]; norm_num) hCE g.2
      hgo hcE hcent
  exact (h.ker _).1 hc1

end Props

end E68Proof

end E6

end CFSG.Quasithin
