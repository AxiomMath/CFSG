module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330H
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330H2
public import CFSG.Quasithin.H13.L32A753g
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigImages

public section

namespace CFSG.Quasithin.H13.Lem3330H

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem vPlus_le (h : Setup331 G T M L) : vPlus L T ≤ T :=
  ((Hyp331.vPlus_reduced h).1.trans inf_le_left).trans
    (pCoreOf_le_of_isSylowTwoOf h.isSylowTwoOf)

theorem cvPlus_eq_bot (h : Setup331 G T M L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTC : tC L T = ⊥) : cvPlus L T = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_subgroupOf, Hyp331.mPlus_eq_of_le hTL] at hv
  have hvT : (v : G) ∈ tC L T := ⟨vPlus_le h v.2, hv⟩
  rw [hTC, Subgroup.mem_bot] at hvT
  exact Subgroup.mem_bot.2 (Subtype.ext hvT)

theorem commVPlus_eq_top (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTC : tC L T = ⊥) : commVPlus L T L = ⊤ := by
  have hdec := (h.vPlus_decomp).2
  rw [Hyp331.mPlus_eq_of_le hTL] at hdec
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hTC]
    exact inf_le_inf_right _ hZT
  rw [hZC, sup_bot_eq] at hdec
  rw [eq_top_iff]
  intro v _
  rw [Subgroup.mem_subgroupOf, ← hdec]
  exact v.2

theorem g2Natural_top
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) (hTC : tC L T = ⊥) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      G2NaturalDerived (V := ↥(vPlus L T)) (autOn L (vPlus L T)) ⊤ ⊥ 1 := by
  obtain ⟨hc, hnat⟩ := G2Blk.exists_g2Natural h38 h39 h51 h hTL hG2
  refine ⟨hc, ?_⟩
  have h1 : cvPlus L T = ⊥ := cvPlus_eq_bot h.toSetup331 hTL hTC
  have h2 : tildeComm L T L = ⊤ := by
    rw [tildeComm, commVPlus_eq_top h hTL hTC, top_sup_eq]
  rw [h2, h1] at hnat
  exact hnat

theorem b42TypeU33_of_isPSU
    {Q : Type} [Group Q] (h : IsPSU 3 3 1 Q) : B42TypeU33 Q := by
  have hs : IsSimpleGroup Q := G2Blk.isSimple_of_isPSU h
  have hcard : Nat.card Q = 6048 := F420.card_of_u33 h
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hb | ht
    · exact hb
    · exfalso
      have hcomm : ∀ a b : Q, a * b = b * a := fun a b => by
        have ha : a ∈ Subgroup.center Q := ht ▸ trivial
        exact (Subgroup.mem_center_iff.mp ha b).symm
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hcard]; norm_num)
      have hN : (Subgroup.zpowers x).Normal :=
        ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h2
      · have : x = 1 := by
          have := Subgroup.mem_zpowers x
          rw [h1, Subgroup.mem_bot] at this
          exact this
        rw [this, orderOf_one] at hx
        exact absurd hx (by norm_num)
      · have h3 := Nat.card_zpowers x
        rw [h2, Subgroup.card_top, hcard, hx] at h3
        exact absurd h3 (by norm_num)
  exact ⟨hZ, isPSU_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm h⟩

section Image

variable {V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem card_eq_mul (hCQ : T ⊓ Subgroup.centralizer (V : Set G) = V) {B : Subgroup G} (hBT : B ≤ T)
    (hBN : B ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card B = Nat.card (autOn B V) * Nat.card ↥(B ⊓ V) := by
  have h1 := card_autOn_eq_relIndex hBN
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx => (hCQ.ge hx).2
  have h2 : B ⊓ Subgroup.centralizer (V : Set G) = B ⊓ V := by
    ext x
    constructor
    · rintro ⟨hxB, hxC⟩
      exact ⟨hxB, hCQ.le ⟨hBT hxB, hxC⟩⟩
    · rintro ⟨hxB, hxV⟩
      exact ⟨hxB, hVC hxV⟩
  rw [h2] at h1
  rw [h1]
  have h3 := Subgroup.relIndex_mul_card (B ⊓ V) B
  rw [show B ⊓ V ⊓ B = B ⊓ V by rw [inf_comm, ← inf_assoc, inf_idem]] at h3
  exact h3.symm

omit [Finite G] in
theorem card_fixV_eq {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (fixV (autOn B V)) = Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) := by
  rw [fixV_autOn hBN, ← Subgroup.inf_subgroupOf_left]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_of_autOn_eq_bot (hCQ : T ⊓ Subgroup.centralizer (V : Set G) = V) {B : Subgroup G}
    (hBT : B ≤ T) (hBN : B ≤ Subgroup.normalizer (V : Set G)) (hB : autOn B V = ⊥) : B ≤ V := by
  have h1 := card_autOn_eq_relIndex hBN
  rw [hB, Subgroup.card_bot] at h1
  have h2 := Subgroup.relIndex_eq_one.1 h1.symm
  rw [← hCQ]
  exact fun b hb => ⟨hBT hb, (h2 hb).2⟩

omit [Finite G] in
theorem isElemAbelian2_autOn' (hVe : IsElemAbelian 2 V) {B : Subgroup G} (hBe : IsElemAbelian 2 B)
    (hBN : B ≤ Subgroup.normalizer (V : Set G)) : IsElemAbelian2 (autOn B V) := by
  have := isElemAbelian2_autOn hVe hBe hBN
  exact this

end Image

theorem insp3_3_30H_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) : Insp3_3_30H := by
  intro G _ _ T M L D h hG2 hTL hTC hQV
  obtain ⟨hc, hnat⟩ := g2Natural_top h38 h39 h51 h hTL hG2 hTC
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVe : IsElemAbelian 2 (vPlus L T) := hred.2.1
  have hVT : vPlus L T ≤ T := vPlus_le h.toSetup331
  have hHV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hHV
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hHV
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = vPlus L T :=
    (h.centralizer_vPlus h38 h39).2.1.trans hQV
  set V := vPlus L T with hV
  set X := autOn (L ⊔ T) V with hX
  set K := autOn L V with hK
  set Tb := autOn T V with hTb
  have hKX : K ≤ X := autOn_mono le_sup_left
  have hXN : X ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) :=
    CFSG.QuasithinUnique.Setup.Lift.autOn_le_normalizer_autOn hHV hLV
      (sup_le Subgroup.le_normalizer hTL)
  have hTbX : Tb ≤ X := autOn_mono le_sup_right
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf Tb X :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn h.toSetup331.isSylowTwoOf hHV
  have hP : B42TypeU33 ↥K := by
    obtain ⟨hLV', hO, hbij⟩ := G2Blk.bijective_autOn h38 h39 h hTL hG2
    exact b42TypeU33_of_isPSU (isPSU_congr (MulEquiv.ofBijective _ hbij) hG2.2.1)
  obtain ⟨e, hKe, hXe, hTbS⟩ := M3330.exists_coordT hXN hnat hTbX hsyl.2.1
  have hBX : ∀ {B : Subgroup G}, B ≤ T → autOn B V ≤ X := fun hBT =>
    autOn_mono (hBT.trans le_sup_right)
  have h1 : ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥V := by
    intro B hBT hBe
    have hBN := hBT.trans hTV
    by_cases hB1 : autOn B V = ⊥
    · exact Subgroup.card_le_of_le (le_of_autOn_eq_bot hCQ hBT hBN hB1)
    · obtain ⟨hle, -⟩ := M3330.offender_facts hKe hXe hP (hBX hBT) hB1
        (isElemAbelian2_autOn' hVe hBe hBN)
      have hBV : Nat.card ↥(B ⊓ V) ≤ Nat.card (fixV (autOn B V)) := by
        rw [card_fixV_eq hBN]
        refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun b hb =>
          ?_⟩
        exact F7.isElemAbelian_comm hBe hb hx.1
      rw [card_eq_mul hCQ hBT hBN, ← (fixV (autOn B V)).card_mul_index,
        mul_comm (Nat.card (fixV _))]
      exact Nat.mul_le_mul hle hBV
  have h2data : ∀ B : Subgroup G, IsMaxElemAbelian T B → ¬ B ≤ V →
      Nat.card (autOn B V) = 8 ∧ Nat.card (fixV (autOn B V)) = 8 ∧ ¬ autOn B V ≤ K ∧
        ∃ b ∈ autOn B V, fixV (autOn B V) = fixV (Subgroup.zpowers b) := by
    intro B hB hBV
    obtain ⟨hBT, hBe, hBmax⟩ := hB
    have hBN := hBT.trans hTV
    have hB1 : autOn B V ≠ ⊥ := fun hb => hBV (le_of_autOn_eq_bot hCQ hBT hBN hb)
    obtain ⟨hle, heq⟩ := M3330.offender_facts hKe hXe hP (hBX hBT) hB1
      (isElemAbelian2_autOn' hVe hBe hBN)
    have hVB : Nat.card ↥V ≤ Nat.card ↥B := hBmax V hVT hVe
    have hBV1 := h1 B hBT hBe
    have hBVc : Nat.card ↥(B ⊓ V) ≤ Nat.card (fixV (autOn B V)) := by
      rw [card_fixV_eq hBN]
      refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun b hb =>
        ?_⟩
      exact F7.isElemAbelian_comm hBe hb hx.1
    have hmul := card_eq_mul hCQ hBT hBN
    have hidx := (fixV (autOn B V)).card_mul_index
    refine heq ?_
    by_contra hne
    have hlt : Nat.card (autOn B V) < (fixV (autOn B V)).index := lt_of_le_of_ne hle (Ne.symm hne)
    have hpos : 0 < Nat.card ↥(B ⊓ V) := Nat.card_pos
    have h3 : Nat.card ↥B < Nat.card ↥V := by
      rw [hmul, ← hidx, mul_comm (Nat.card (fixV _))]
      calc Nat.card (autOn B V) * Nat.card ↥(B ⊓ V)
          < (fixV (autOn B V)).index * Nat.card ↥(B ⊓ V) := (Nat.mul_lt_mul_right hpos).2 hlt
        _ ≤ (fixV (autOn B V)).index * Nat.card (fixV (autOn B V)) := Nat.mul_le_mul_left _ hBVc
    omega
  refine ⟨h1, ?_, ?_⟩
  · intro B hB _ hBV
    obtain ⟨-, -, -, c, hc, hfix⟩ := h2data B hB hBV
    have hBN := hB.1.trans hTV
    obtain ⟨b, hbB, hbact⟩ := exists_eq_conj_of_mem_autOn hBN hc
    refine ⟨b, hbB, ?_⟩
    ext x
    constructor
    · rintro ⟨hxV, hxC⟩
      refine ⟨hxV, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h4 : (⟨x, hxV⟩ : ↥V) ∈ fixV (autOn B V) := by
        rw [fixV_autOn hBN]
        exact hxC
      rw [hfix] at h4
      have h5 := congrArg Subtype.val (h4 c (Subgroup.mem_zpowers c))
      rw [hbact] at h5
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [show y * x * y⁻¹ = x from h5]
    · rintro ⟨hxV, hxC⟩
      refine ⟨hxV, ?_⟩
      have h4 : (⟨x, hxV⟩ : ↥V) ∈ fixV (Subgroup.zpowers c) := by
        refine L32A.M753.mem_fixV_zpowers_of (Subtype.ext ?_)
        rw [hbact]
        have h5 := Subgroup.mem_centralizer_iff.1 hxC b (Set.mem_singleton b)
        change b * x * b⁻¹ = x
        rw [h5, mul_inv_cancel_right]
      rw [← hfix, fixV_autOn hBN] at h4
      exact h4
  · intro B B' hB hB' hTB hTB' hBV hB'V
    obtain ⟨h8, hf8, hBK, -⟩ := h2data B hB hBV
    obtain ⟨h8', hf8', -, -⟩ := h2data B' hB' hB'V
    have hTbK : ¬ Tb ≤ K := fun hle => hBK ((autOn_mono hB.1).trans hle)
    have hTbeq := M3330.map_eq_sSubG hKX hKe hXe hTbS hsyl hTbK
    have hN : Tb ≤ Subgroup.normalizer (autOn B V : Set (MulAut ↥V)) :=
      CFSG.QuasithinUnique.Setup.Lift.autOn_le_normalizer_autOn hTV (hB.1.trans hTV) hTB
    have hN' : Tb ≤ Subgroup.normalizer (autOn B' V : Set (MulAut ↥V)) :=
      CFSG.QuasithinUnique.Setup.Lift.autOn_le_normalizer_autOn hTV (hB'.1.trans hTV) hTB'
    have heq := M3330.eq_of_normal_offenders hTbeq (autOn_mono hB.1) hN
      (isElemAbelian2_autOn' hVe hB.2.1 (hB.1.trans hTV)) h8 hf8 (autOn_mono hB'.1) hN'
      (isElemAbelian2_autOn' hVe hB'.2.1 (hB'.1.trans hTV)) h8' hf8'
    have key : ∀ {B B' : Subgroup G}, B ≤ T → B' ≤ T → autOn B V = autOn B' V →
        B ≤ B' ⊔ V := by
      intro B B' hBT hB'T he b hb
      obtain ⟨a, ha, hav⟩ := exists_mem_autOn_of_mem (hBT.trans hTV) hb
      rw [he] at ha
      obtain ⟨b', hb', hb'v⟩ := exists_eq_conj_of_mem_autOn (hB'T.trans hTV) ha
      have hc : b'⁻¹ * b ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
        refine ⟨T.mul_mem (T.inv_mem (hB'T hb')) (hBT hb),
          Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
        have e2 : b * v * b⁻¹ = b' * v * b'⁻¹ :=
          (hav ⟨v, hv⟩).symm.trans (hb'v ⟨v, hv⟩)
        calc v * (b'⁻¹ * b) = b'⁻¹ * (b' * v * b'⁻¹) * b := by group
          _ = b'⁻¹ * (b * v * b⁻¹) * b := by rw [e2]
          _ = b'⁻¹ * b * v := by group
      rw [hCQ] at hc
      have e3 : b = b' * (b'⁻¹ * b) := by group
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb') (Subgroup.mem_sup_right hc)
    exact le_antisymm (sup_le (key hB.1 hB'.1 heq) le_sup_right)
      (sup_le (key hB'.1 hB.1 heq.symm) le_sup_right)

end CFSG.Quasithin.H13.Lem3330H
