module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11K
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem relIndex_sup_ch611 {H N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN).toEquiv.symm

omit [Finite G] in
theorem out_inv_mul_mem_ch611 {K : Type*} [Group K] {H : Subgroup K} (g : K) (q : K ⧸ H) :
    (g • q).out⁻¹ * g * q.out ∈ H := by
  have h : ((g • q).out : K ⧸ H) = ((g * q.out : K) : K ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

theorem exists_mem_centralizer_of_comm_ch611 {L P V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hodd : ¬ 2 ∣ P.relIndex L) {x : G}
    (hxV : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ V) (hxP : ∀ p ∈ P, p * x = x * p) :
    ∃ w ∈ V, ∀ ℓ ∈ L, ℓ * (w * x) * ℓ⁻¹ = w * x := by
  classical
  set P' := P.subgroupOf L with hP'
  have : Fintype (↥L ⧸ P') := Fintype.ofFinite _
  have hcomm : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩
  let _ : CommGroup ↥V := .mk hcomm.is_comm.comm
  let δ : ↥L → ↥V := fun ℓ => ⟨(ℓ : G) * x * (ℓ : G)⁻¹ * x⁻¹, hxV ℓ ℓ.2⟩
  let c : ↥L → ↥V →* ↥V := fun ℓ =>
    { toFun := fun v => ⟨(ℓ : G) * v * (ℓ : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hδ : ∀ a b : ↥L, δ (a * b) = c a (δ b) * δ a := fun a b => Subtype.ext (by
    simp only [δ, c, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul]
    group)
  have hδP : ∀ p : ↥L, p ∈ P' → δ p = 1 := fun p hp => Subtype.ext (by
    have := hxP p (Subgroup.mem_subgroupOf.mp hp)
    simp only [δ, OneMemClass.coe_one]
    rw [this]
    group)
  set F : ↥V := ∏ q : ↥L ⧸ P', δ q.out with hF
  have hkey : ∀ ℓ : ↥L, c ℓ F = F * δ ℓ := by
    intro ℓ
    have hterm : ∀ q : ↥L ⧸ P', c ℓ (δ q.out) = δ (ℓ • q).out * (δ ℓ)⁻¹ := by
      intro q
      have hp : (ℓ • q).out⁻¹ * ℓ * q.out ∈ P' := out_inv_mul_mem_ch611 ℓ q
      have e : ℓ * q.out = (ℓ • q).out * ((ℓ • q).out⁻¹ * ℓ * q.out) := by group
      have h1 := hδ ℓ q.out
      rw [e, hδ, hδP _ hp, map_one, one_mul] at h1
      rw [h1, mul_inv_cancel_right]
    rw [hF, map_prod, Finset.prod_congr rfl (fun (q : ↥L ⧸ P') _ => hterm q),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have hperm : ∏ q : ↥L ⧸ P', δ (ℓ • q).out = ∏ q : ↥L ⧸ P', δ q.out :=
      Equiv.prod_comp (MulAction.toPerm ℓ) (fun q : ↥L ⧸ P' => δ q.out)
    rw [hperm]
    congr 1
    have hn : Fintype.card (↥L ⧸ P') = P.relIndex L := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    have hδ2 : δ ℓ * δ ℓ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hV2 _ (δ ℓ).2)
    have hinv : (δ ℓ)⁻¹ = δ ℓ := inv_eq_of_mul_eq_one_right hδ2
    obtain ⟨m, hm⟩ : Odd (Fintype.card (↥L ⧸ P')) :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (hn ▸ hodd))
    rw [hinv, hm, pow_succ, pow_mul, sq, hδ2, one_pow, one_mul]
  refine ⟨((F⁻¹ : ↥V) : G), (F⁻¹).2, fun ℓ hℓ => ?_⟩
  have h1 := congrArg Subtype.val (hkey ⟨ℓ, hℓ⟩)
  simp only [c, δ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul] at h1
  have hFδ : (F : G) * (ℓ * x * ℓ⁻¹ * x⁻¹) = (ℓ * x * ℓ⁻¹ * x⁻¹) * F :=
    hVab _ F.2 _ (hxV ℓ hℓ)
  rw [InvMemClass.coe_inv]
  calc ℓ * ((F : G)⁻¹ * x) * ℓ⁻¹ = (ℓ * F * ℓ⁻¹)⁻¹ * (ℓ * x * ℓ⁻¹) := by group
    _ = ((F : G) * (ℓ * x * ℓ⁻¹ * x⁻¹))⁻¹ * (ℓ * x * ℓ⁻¹) := by rw [h1]
    _ = ((ℓ * x * ℓ⁻¹ * x⁻¹) * F)⁻¹ * (ℓ * x * ℓ⁻¹) := by rw [hFδ]
    _ = (F : G)⁻¹ * x := by group

omit [Finite G] in
theorem comm_mul_ch611 {a b x y : G} (hab : a * b = b * a) (hax : a * x = x * a)
    (hay : a * y = y * a) (hbx : b * x = x * b) (hby : b * y = y * b) :
    (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hax' : Commute a x := hax
  have hab' : Commute a b := hab
  have hay' : Commute a y := hay
  have hbx' : Commute b x := hbx
  have hby' : Commute b y := hby
  have hA : Commute a (x * (b * y) * x⁻¹) :=
    (hax'.mul_right (hab'.mul_right hay')).mul_right hax'.inv_right
  have hB : Commute b (x * y * x⁻¹ * y⁻¹) :=
    ((hbx'.mul_right hby').mul_right hbx'.inv_right).mul_right hby'.inv_right
  calc (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹
      = (a * (x * (b * y) * x⁻¹) * a⁻¹) * (b * y)⁻¹ := by group
    _ = (x * (b * y) * x⁻¹) * (b * y)⁻¹ := by rw [hA.eq, mul_inv_cancel_right]
    _ = x * b * y * x⁻¹ * y⁻¹ * b⁻¹ := by group
    _ = b * x * y * x⁻¹ * y⁻¹ * b⁻¹ := by rw [show x * b = b * x from hbx.symm]
    _ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hB.eq, mul_inv_cancel_right]

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem T_le_normalizer_Q_ch611 : T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxV := h.toHyp611.T_le_normalizer hx
  constructor
  · rintro ⟨hyT, hyV⟩
    refine ⟨T.mul_mem (T.mul_mem hx hyT) (T.inv_mem hx), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 : x⁻¹ * v * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) v).mp hv
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hyV _ h1
    calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [h2]
      _ = x * y * x⁻¹ * v := by group
  · rintro ⟨hyT, hyV⟩
    have hyT' : y ∈ T := by
      have := T.mul_mem (T.mul_mem (T.inv_mem hx) hyT) hx
      simpa [mul_assoc] using this
    refine ⟨hyT', Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
    have h2 := Subgroup.mem_centralizer_iff.mp hyV _ h1
    calc v * y = x⁻¹ * ((x * v * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * v * x⁻¹)) * x := by rw [h2]
      _ = y * v := by group

theorem uCh611_le_T (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) : uCh611 T L V ≤ T := by
  obtain ⟨⟨-, hUQ, -⟩, -, -, -⟩ := h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  exact hUQ.trans (F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf (T_le_hCh611 T)))

theorem pCore_props_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2) :
    (∀ r ∈ ch6Q T V, ∃ v ∈ V, ∃ q ∈ ch6Q T V, q ∈ Subgroup.centralizer (uCh611 T L V : Set G) ∧
      r = v * q) ∧
    ⁅ch6Q T V, uCh611 T L V⁆ ≤ V := by
  obtain ⟨-, -, -, -, hCU, hTV⟩ := h.stage_e_ch611 h331 h432 h512 h614 h615 h6210 hG31 h4
  obtain ⟨-, -, hVUc, hCQ⟩ := h.step_a_ch611 h331 h432 h512 h614 h615 h6210 h4
  have hVR : V ≤ ch6Q T V := fun v hv => ⟨h.toHyp611.le_T hv,
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hw hv⟩
  have hdec : ∀ r ∈ ch6Q T V, ∃ v ∈ V, ∃ q ∈ ch6Q T V,
      q ∈ Subgroup.centralizer (uCh611 T L V : Set G) ∧ r = v * q := by
    intro r hr
    obtain ⟨v, hv, q, hq, rfl⟩ := hTV r hr
    have hqC : q ∈ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
      rw [show centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) = pCoreOf 2 (hCh611 T) from hCQ]
      exact hq
    have hqR : q ∈ ch6Q T V := by
      have := (ch6Q T V).mul_mem ((ch6Q T V).inv_mem (hVR hv)) hr
      simpa using this
    exact ⟨v, hv, q, hqR, hCU hqC, rfl⟩
  refine ⟨hdec, ?_⟩
  rw [Subgroup.commutator_le]
  intro r hr u hu
  obtain ⟨v, hv, q, -, hqU, rfl⟩ := hdec r hr
  have hqu : q * u * q⁻¹ = u := by
    rw [← Subgroup.mem_centralizer_iff.mp hqU u hu, mul_inv_cancel_right]
  have hmem : v * u * v⁻¹ * u⁻¹ ∈ V := by
    have := hVUc (Subgroup.commutator_mem_commutator hv hu)
    rw [commutatorElement_def] at this
    exact this.1
  rw [commutatorElement_def]
  have e : v * q * u * (v * q)⁻¹ * u⁻¹ = v * u * v⁻¹ * u⁻¹ := by
    calc v * q * u * (v * q)⁻¹ * u⁻¹ = v * (q * u * q⁻¹) * v⁻¹ * u⁻¹ := by group
      _ = v * u * v⁻¹ * u⁻¹ := by rw [hqu]
  rw [e]
  exact hmem

theorem TL_sub_UR_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2) :
    ∀ t ∈ T ⊓ L, ∃ u ∈ uCh611 T L V, ∃ r ∈ ch6Q T V, t = u * r := by
  obtain ⟨-, hUcomm, hU16, hCUV, -, -⟩ :=
    h.stage_e_ch611 h331 h432 h512 h614 h615 h6210 hG31 h4
  set U := uCh611 T L V with hUdef
  set R := ch6Q T V with hRdef
  have hUT : U ≤ T := h.uCh611_le_T h331 h432 h512 h614 h615
  have hZSU : ch6ZS T L V ≤ U := le_conjClosure _ _
  have hTR := h.T_le_normalizer_Q_ch611
  have hUle : U ≤ (T ⊓ L) ⊔ R := by
    intro u hu
    have huZ : u ∈ Subgroup.centralizer (ch6ZS T L V : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => hUcomm z (hZSU hz) u hu
    obtain ⟨t', ht', hr⟩ := h.exists_mem_TL_ch611 h331 h432 h512 h614 h615 (hUT hu) huZ
    have hrR : t'⁻¹ * u ∈ R := ⟨T.mul_mem (T.inv_mem ht'.1) (hUT hu), hr⟩
    have e : u = t' * (t'⁻¹ * u) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht') (Subgroup.mem_sup_right hrR)
  have hUR : R.relIndex (U ⊔ R) = 4 := by
    rw [relIndex_sup_ch611 (hUT.trans hTR)]
    have e : R.subgroupOf U = (ch6ZS T L V).subgroupOf U := by
      ext x
      simp only [Subgroup.mem_subgroupOf, hRdef]
      constructor
      · intro hx
        have : (x : G) ∈ U ⊓ Subgroup.centralizer (V : Set G) := ⟨x.2, hx.2⟩
        rwa [hCUV] at this
      · intro hx
        exact ⟨h.toHyp611.le_T hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
          B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hv hx.1⟩
    rw [Subgroup.relIndex, e]
    have h1 := Subgroup.card_mul_index ((ch6ZS T L V).subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZSU).toEquiv, h.toHyp611Nat.card_ZS,
      hU16] at h1
    norm_num at h1
    omega
  have hTLR : R.relIndex ((T ⊓ L) ⊔ R) = 4 := by
    rw [relIndex_sup_ch611 (inf_le_left.trans hTR)]
    have e : R.subgroupOf (T ⊓ L) = (Subgroup.centralizer (V : Set G)).subgroupOf (T ⊓ L) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, hRdef, Subgroup.mem_inf]
      exact ⟨fun hx => hx.2, fun hx => ⟨x.2.1, hx⟩⟩
    rw [Subgroup.relIndex, e]
    exact h.relIndex_TL_ch611
  have hle : U ⊔ R ≤ (T ⊓ L) ⊔ R := sup_le hUle le_sup_right
  have hmul := Subgroup.relIndex_mul_relIndex R (U ⊔ R) ((T ⊓ L) ⊔ R) le_sup_right hle
  rw [hUR, hTLR] at hmul
  have h1 : (U ⊔ R).relIndex ((T ⊓ L) ⊔ R) = 1 := by omega
  intro t ht
  have htUR : t ∈ U ⊔ R := Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_left ht)
  have hcoe : ((U ⊔ R : Subgroup G) : Set G) = (U : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUT.trans hTR)
  have htUR' : t ∈ (U : Set G) * (R : Set G) := hcoe ▸ htUR
  obtain ⟨u, hu, r, hr, rfl⟩ := htUR'
  exact ⟨u, hu, r, hr, rfl⟩

theorem pCore_eq_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2) :
    ch6Q T V = V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUcomm, hU16, hCUV, -, -⟩ :=
    h.stage_e_ch611 h331 h432 h512 h614 h615 h6210 hG31 h4
  obtain ⟨hdec, hRU⟩ := h.pCore_props_ch611 h331 h432 h512 h614 h615 h6210 hG31 h4
  have hTLUR := h.TL_sub_UR_ch611 h331 h432 h512 h614 h615 h6210 hG31 h4
  set U := uCh611 T L V with hUdef
  set R := ch6Q T V with hRdef
  have hV := h.toHyp611.isElemAbelian
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV ha hb
  have hVR : V ≤ R := fun v hv => ⟨h.toHyp611.le_T hv,
    Subgroup.mem_centralizer_iff.mpr fun w hw => hVab w hw v hv⟩
  have hRV : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r := fun r hr v hv =>
    (Subgroup.mem_centralizer_iff.mp hr.2 v hv).symm
  have hUT : U ≤ T := h.uCh611_le_T h331 h432 h512 h614 h615
  have hZSU : ch6ZS T L V ≤ U := le_conjClosure _ _
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := fun l hl => h.toHyp611.L_le_normalizer hl
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans h.toHyp611.T_le_normalizer
  have hLU : ⁅L, U⁆ = L := by
    refine h.commutator_eq_L_ch611 hUV (fun u hu => Subgroup.mem_centralizer_iff.mpr
      fun z hz => hUcomm z (hZSU hz) u hu) (hUT.trans h.T_le_normalizer_L) fun hle => ?_
    have h1 : U ⊓ Subgroup.centralizer (V : Set G) = U := inf_eq_left.mpr hle
    rw [hCUV] at h1
    have : Nat.card ↥(ch6ZS T L V) = Nat.card ↥U := by rw [h1]
    rw [h.toHyp611Nat.card_ZS, hU16] at this
    norm_num at this
  have hRL : ⁅R, L⁆ ≤ V := h.commutator_pCore_le_ch611 hUV hLU hRU
  have hLR : ∀ ℓ ∈ L, ∀ x ∈ R, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ V := by
    intro ℓ hℓ x hx
    have := hRL (Subgroup.commutator_mem_commutator hx hℓ)
    rw [commutatorElement_def] at this
    have h2 := V.inv_mem this
    have e : (x * ℓ * x⁻¹ * ℓ⁻¹)⁻¹ = ℓ * x * ℓ⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  have hUR : ∀ u ∈ U, ∀ x ∈ R, u * x * u⁻¹ * x⁻¹ ∈ V := by
    intro u hu x hx
    have := hRU (Subgroup.commutator_mem_commutator hx hu)
    rw [commutatorElement_def] at this
    have h2 := V.inv_mem this
    have e : (x * u * x⁻¹ * u⁻¹)⁻¹ = u * x * u⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  obtain ⟨d, hdL, -, -, -, hdV, -, -⟩ := h.exists_diag_ch611
  have hdV' : ∀ x ∈ V, d * x = x * d → x = 1 := fun x hx hdx =>
    hdV x hx (by rw [hdx, mul_inv_cancel_right])
  have hsplit : ∀ r ∈ R, ∃ w ∈ V, d * (w * r) = (w * r) * d := by
    intro r hr
    have hcg : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩
    let ψ : ↥V → ↥V := fun w =>
      ⟨d * w * d⁻¹ * w⁻¹, V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hdL) w).mp w.2)
        (V.inv_mem w.2)⟩
    have hψinj : Function.Injective ψ := by
      intro a b hab
      have hab' : d * a * d⁻¹ * (a : G)⁻¹ = d * b * d⁻¹ * (b : G)⁻¹ := congrArg Subtype.val hab
      have hda : d * (a : G) * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hdL) a).mp a.2
      have hdb : d * (b : G) * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hdL) b).mp b.2
      have hba : (b : G)⁻¹ * a ∈ V := V.mul_mem (V.inv_mem b.2) a.2
      have h1 : d * ((b : G)⁻¹ * a) * d⁻¹ = (b : G)⁻¹ * a := by
        have e1 : d * ((b : G)⁻¹ * a) * d⁻¹ = (d * b * d⁻¹)⁻¹ * (d * a * d⁻¹) := by group
        rw [e1]
        have e2 : d * (a : G) * d⁻¹ = d * b * d⁻¹ * (b : G)⁻¹ * a := by
          calc d * (a : G) * d⁻¹ = d * a * d⁻¹ * (a : G)⁻¹ * a := by group
            _ = d * b * d⁻¹ * (b : G)⁻¹ * a := by rw [hab']
        rw [e2]
        group
      have h2 := hdV _ hba h1
      apply Subtype.ext
      have := congrArg (fun y => (b : G) * y) h2
      simpa using this
    have hψsurj := Finite.injective_iff_surjective.mp hψinj
    have hdr : d * r * d⁻¹ * r⁻¹ ∈ V := hLR d hdL r hr
    obtain ⟨w, hw⟩ := hψsurj ⟨(d * r * d⁻¹ * r⁻¹)⁻¹, V.inv_mem hdr⟩
    have hw' : d * w * d⁻¹ * (w : G)⁻¹ = (d * r * d⁻¹ * r⁻¹)⁻¹ := congrArg Subtype.val hw
    refine ⟨w, w.2, ?_⟩
    have hdw : d * (w : G) * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hdL) w).mp w.2
    have hcomm1 : (d * r * d⁻¹ * r⁻¹) * (w : G) = (w : G) * (d * r * d⁻¹ * r⁻¹) :=
      hVab _ hdr _ w.2
    have h3 : d * (w : G) * d⁻¹ = (d * r * d⁻¹ * r⁻¹)⁻¹ * w := by
      calc d * (w : G) * d⁻¹ = d * w * d⁻¹ * (w : G)⁻¹ * w := by group
        _ = (d * r * d⁻¹ * r⁻¹)⁻¹ * w := by rw [hw']
    calc d * (↑w * r) = (d * w * d⁻¹) * (d * r * d⁻¹) * d := by group
      _ = (d * r * d⁻¹ * r⁻¹)⁻¹ * w * (d * r * d⁻¹) * d := by rw [h3]
      _ = (d * r * d⁻¹ * r⁻¹)⁻¹ * (w * (d * r * d⁻¹ * r⁻¹)) * r * d := by group
      _ = (d * r * d⁻¹ * r⁻¹)⁻¹ * ((d * r * d⁻¹ * r⁻¹) * w) * r * d := by rw [hcomm1]
      _ = ↑w * r * d := by group
  have hTLodd : ¬ 2 ∣ (T ⊓ L).relIndex L := by
    have hS : IsSylowTwoOf T (L ⊔ T) := h.toHyp5_0_1.isSylowTwoOf le_sup_right
    exact (A4.isSylowTwoOf_inf_normal hS le_sup_left h.toHyp5_0_1.sup_le_normalizer).2.2
  have hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    Hyp611.inf_centralizer_eq_bot h331 h432 h615 h.toHyp611
  have havg : ∀ x ∈ R, (∀ t ∈ T ⊓ L, t * x = x * t) → x ∈ V := by
    intro x hx hxP
    obtain ⟨w, hw, hwx⟩ := exists_mem_centralizer_of_comm_ch611 hLV hVab hV.2
      hTLodd (hLR · · x hx) hxP
    have hmem : w * x ∈ T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨T.mul_mem (h.toHyp611.le_T hw) hx.1, Subgroup.mem_centralizer_iff.mpr fun ℓ hℓ => by
        have := hwx ℓ hℓ
        calc ℓ * (w * x) = ℓ * (w * x) * ℓ⁻¹ * ℓ := by group
          _ = w * x * ℓ := by rw [this]⟩
    rw [hCTL, Subgroup.mem_bot] at hmem
    have : x = w⁻¹ := by
      have := congrArg (fun y => w⁻¹ * y) hmem
      simpa using this
    rw [this]
    exact V.inv_mem hw
  have hcommTL : ∀ x ∈ R, x ∈ Subgroup.centralizer (U : Set G) → ∀ t ∈ T ⊓ L,
      ∃ u ∈ U, ∃ r ∈ R, t * x * t⁻¹ * x⁻¹ = u * (r * x * r⁻¹ * x⁻¹) * u⁻¹ := by
    intro x hx hxU t ht
    obtain ⟨u, hu, r, hr, rfl⟩ := hTLUR t ht
    refine ⟨u, hu, r, hr, ?_⟩
    have hux : u * x = x * u := Subgroup.mem_centralizer_iff.mp hxU u hu
    have hux' : x * u⁻¹ * x⁻¹ = u⁻¹ := by
      calc x * u⁻¹ * x⁻¹ = (x * u⁻¹ * x⁻¹ * u) * u⁻¹ := by group
        _ = u⁻¹ := by
          have : x * u⁻¹ * x⁻¹ * u = 1 := by
            calc x * u⁻¹ * x⁻¹ * u = x * u⁻¹ * (x⁻¹ * u * x) * x⁻¹ := by group
              _ = x * u⁻¹ * (x⁻¹ * (x * u)) * x⁻¹ := by rw [mul_assoc x⁻¹ u x, hux]
              _ = 1 := by group
          rw [this, one_mul]
    calc u * r * x * (u * r)⁻¹ * x⁻¹ = u * (r * x * r⁻¹ * x⁻¹) * (x * u⁻¹ * x⁻¹) := by group
      _ = u * (r * x * r⁻¹ * x⁻¹) * u⁻¹ := by rw [hux']
  have hB : ∀ x ∈ R, d * x = x * d → x ∈ Subgroup.centralizer (U : Set G) → x = 1 := by
    intro x hx hdx hxU
    have hxV : x ∈ V := by
      refine havg x hx fun t ht => ?_
      obtain ⟨u, hu, r, hr, he⟩ := hcommTL x hx hxU t ht
      obtain ⟨w, hw, hdw⟩ := hsplit r hr
      set x' := w * r with hx'
      have hx'R : x' ∈ R := R.mul_mem (hVR hw) hr
      have hrx : r * x * r⁻¹ * x⁻¹ = x' * x * x'⁻¹ * x⁻¹ := by
        have e : r = w⁻¹ * x' := by rw [hx']; group
        have hc := comm_mul_ch611 (a := w⁻¹) (b := 1) (x := x') (y := x) (by simp)
          ((hRV x' hx'R _ (V.inv_mem hw)).symm) ((hRV x hx _ (V.inv_mem hw)).symm) (by simp)
          (by simp)
        rw [e]
        calc w⁻¹ * x' * x * (w⁻¹ * x')⁻¹ * x⁻¹
            = (w⁻¹ * x') * (1 * x) * (w⁻¹ * x')⁻¹ * (1 * x)⁻¹ := by group
          _ = x' * x * x'⁻¹ * x⁻¹ := hc
      have hTLx : t * x * t⁻¹ * x⁻¹ ∈ V := hLR t ht.2 x hx
      rw [he, hrx] at hTLx
      have hc : x' * x * x'⁻¹ * x⁻¹ ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hUV hu)) _).mp hTLx
        simpa [mul_assoc] using this
      have hcd : d * (x' * x * x'⁻¹ * x⁻¹) = (x' * x * x'⁻¹ * x⁻¹) * d := by
        have hdx'' : Commute d x' := hdw
        have hdx' : Commute d x := hdx
        exact (((hdx''.mul_right hdx').mul_right hdx''.inv_right).mul_right hdx'.inv_right).eq
      have h1 := hdV' _ hc hcd
      have h2 : t * x * t⁻¹ * x⁻¹ = 1 := by rw [he, hrx, h1]; group
      calc t * x = t * x * t⁻¹ * x⁻¹ * (x * t) := by group
        _ = x * t := by rw [h2, one_mul]
    exact hdV' x hxV hdx
  have hC : ∀ x₁ ∈ R, d * x₁ = x₁ * d → ∀ x₂ ∈ R, d * x₂ = x₂ * d → x₁ * x₂ = x₂ * x₁ := by
    intro x₁ h₁ hd₁ x₂ h₂ hd₂
    have hy : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ = 1 := by
      apply hB _ (R.mul_mem (R.mul_mem (R.mul_mem h₁ h₂) (R.inv_mem h₁)) (R.inv_mem h₂))
      · have hd₁' : Commute d x₁ := hd₁
        have hd₂' : Commute d x₂ := hd₂
        exact (((hd₁'.mul_right hd₂').mul_right hd₁'.inv_right).mul_right hd₂'.inv_right).eq
      · refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
        set a₁ := u * x₁ * u⁻¹ * x₁⁻¹ with ha₁
        set a₂ := u * x₂ * u⁻¹ * x₂⁻¹ with ha₂
        have ha₁V : a₁ ∈ V := hUR u hu x₁ h₁
        have ha₂V : a₂ ∈ V := hUR u hu x₂ h₂
        have e₁ : u * x₁ * u⁻¹ = a₁ * x₁ := by rw [ha₁]; group
        have e₂ : u * x₂ * u⁻¹ = a₂ * x₂ := by rw [ha₂]; group
        have key : u * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * u⁻¹ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by
          calc u * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * u⁻¹
              = (u * x₁ * u⁻¹) * (u * x₂ * u⁻¹) * (u * x₁ * u⁻¹)⁻¹ * (u * x₂ * u⁻¹)⁻¹ := by
                group
            _ = (a₁ * x₁) * (a₂ * x₂) * (a₁ * x₁)⁻¹ * (a₂ * x₂)⁻¹ := by rw [e₁, e₂]
            _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ :=
                comm_mul_ch611 (hVab _ ha₁V _ ha₂V) (hRV x₁ h₁ _ ha₁V).symm
                  (hRV x₂ h₂ _ ha₁V).symm (hRV x₁ h₁ _ ha₂V).symm (hRV x₂ h₂ _ ha₂V).symm
        calc u * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹)
            = u * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * u⁻¹ * u := by group
          _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ * u := by rw [key]
    calc x₁ * x₂ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ * (x₂ * x₁) := by group
      _ = x₂ * x₁ := by rw [hy, one_mul]
  have hRab : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨w₁, hw₁, hd₁⟩ := hsplit r₁ hr₁
    obtain ⟨w₂, hw₂, hd₂⟩ := hsplit r₂ hr₂
    have hx₁ : w₁ * r₁ ∈ R := R.mul_mem (hVR hw₁) hr₁
    have hx₂ : w₂ * r₂ ∈ R := R.mul_mem (hVR hw₂) hr₂
    have hc := hC _ hx₁ hd₁ _ hx₂ hd₂
    have e₁ : r₁ = w₁⁻¹ * (w₁ * r₁) := by group
    have e₂ : r₂ = w₂⁻¹ * (w₂ * r₂) := by group
    have hcomm := comm_mul_ch611 (a := w₁⁻¹) (b := w₂⁻¹) (x := w₁ * r₁) (y := w₂ * r₂)
      (hVab _ (V.inv_mem hw₁) _ (V.inv_mem hw₂)) (hRV _ hx₁ _ (V.inv_mem hw₁)).symm
      (hRV _ hx₂ _ (V.inv_mem hw₁)).symm (hRV _ hx₁ _ (V.inv_mem hw₂)).symm
      (hRV _ hx₂ _ (V.inv_mem hw₂)).symm
    rw [← e₁, ← e₂] at hcomm
    have h1 : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ = 1 := by
      rw [hcomm, hc]
      group
    calc r₁ * r₂ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ * (r₂ * r₁) := by group
      _ = r₂ * r₁ := by rw [h1, one_mul]
  have hD : ∀ x ∈ R, x ∈ Subgroup.centralizer (U : Set G) → x ∈ V := by
    intro x hx hxU
    refine havg x hx fun t ht => ?_
    obtain ⟨u, hu, r, hr, he⟩ := hcommTL x hx hxU t ht
    have h1 : t * x * t⁻¹ * x⁻¹ = 1 := by
      rw [he, hRab r hr x hx]
      group
    calc t * x = t * x * t⁻¹ * x⁻¹ * (x * t) := by group
      _ = x * t := by rw [h1, one_mul]
  refine le_antisymm (fun r hr => ?_) hVR
  obtain ⟨v, hv, q, hq, hqU, rfl⟩ := hdec r hr
  exact V.mul_mem hv (hD q hq hqU)

end Hyp6Sec2

end CFSG.Quasithin.H13
