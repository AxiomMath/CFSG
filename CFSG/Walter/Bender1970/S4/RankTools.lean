module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Walter.Bender1970.S3.CoreExchangeRank
public import CFSG.Walter.Bender1970.S38.ActionMain
public import CFSG.Walter.Bender1970.S38.Component

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_exponent_le_upperCentral {Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQp : IsPGroup p Q) (hQ : ¬ IsCyclic Q) :
    ∃ X ≤ Q, ¬ IsCyclic X ∧ (∀ x ∈ X, x ^ p = 1) ∧
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ∀ q ∈ Q, ⁅x, q⁆ ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p Q) := ⟨hQp⟩
  obtain ⟨hcyc, hexp⟩ := CFSG.lemma_4_5_c (R := Q) (p := p) hp2 hQ
  set Z2 := Subgroup.upperCentralSeries Q 2 with hZ2
  set Ω := CFSG.omega₁ (G := Z2) (p := p) with hΩ
  set D : Subgroup Q := Ω.map Z2.subtype with hD
  have : Ω.Characteristic := CFSG.omega₁_characteristic Z2
  have : D.Characteristic := CFSG.characteristic_map_subtype_of_characteristic Z2 Ω
  refine ⟨D.map Q.subtype, Subgroup.map_subtype_le _, fun h => hcyc ?_, ?_, fun g hg => ?_, ?_⟩
  · have e1 : Ω ≃* D := Subgroup.equivMapOfInjective Ω Z2.subtype Z2.subtype_injective
    have e2 : D ≃* D.map Q.subtype :=
      Subgroup.equivMapOfInjective D Q.subtype Q.subtype_injective
    exact (e1.trans e2).isCyclic.mpr h
  · rintro _ ⟨d, ⟨ω, hω, rfl⟩, rfl⟩
    have h1 : (⟨ω, hω⟩ : Ω) ^ p = 1 := by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one _
    have h2 := congrArg (fun w : Ω => (((w : Z2) : Q) : G)) h1
    simpa using h2
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_map_of_characteristic hg hy, fun hy => ?_⟩
    have := conj_mem_map_of_characteristic (Subgroup.inv_mem _ hg) hy
    simpa [mul_assoc] using this
  · rintro _ ⟨d, ⟨ω, -, rfl⟩, rfl⟩ q hq
    have hω2 : ((ω : Z2) : Q) ∈ Subgroup.upperCentralSeries Q 2 := ω.2
    have hZ : ⁅((ω : Z2) : Q), (⟨q, hq⟩ : Q)⁆ ∈ Subgroup.center Q := by
      have := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hω2 ⟨q, hq⟩
      rwa [Subgroup.upperCentralSeries_one] at this
    have hcoe : ((⁅((ω : Z2) : Q), (⟨q, hq⟩ : Q)⁆ : Q) : G) = ⁅(((ω : Z2) : Q) : G), q⁆ := by
      simp [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · show ⁅(((ω : Z2) : Q) : G), q⁆ ∈ Q
      rw [← hcoe]
      exact SetLike.coe_mem _
    · show ⁅(((ω : Z2) : Q) : G), q⁆ ∈ Subgroup.centralizer (Q : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hZ) ⟨y, hy⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe] at h
      exact h

omit [Finite G] in
theorem isElemAbelian_map_conj {V : Subgroup G} {p : ℕ} (hV : CFSG.Open.IsElemAbelian p V)
    (g : G) : CFSG.Open.IsElemAbelian p (V.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', hae⟩ := a.2
    obtain ⟨b', hb', hbe⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hV.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hV.2 x hx, map_one]

theorem exists_isElemAbelian_rank_three_mem {Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ rank Q) {v : G} (hvQ : v ∈ Q) (hvp : v ^ p = 1)
    (hvZ : ∀ q ∈ Q, ⁅v, q⁆ ∈ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    ∃ E ≤ Q, CFSG.Open.IsElemAbelian p E ∧ 3 ≤ rank E ∧ v ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEQ, hE, hEcard⟩ := exists_isElemAbelian_of_le_rank hp hQp hQ3
  have hrank3 : ∀ F ≤ Q, CFSG.Open.IsElemAbelian p F → p ^ 3 ≤ Nat.card F → 3 ≤ rank F := by
    intro F hFQ hF hFcard
    obtain ⟨k, hk⟩ := (hQp.to_le hFQ).exists_card_eq
    have hk3 : 3 ≤ k := by
      rw [hk] at hFcard
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hFcard
    exact hk3.trans (le_rank hp le_rfl hF hk)
  by_cases hvE : v ∈ E
  · exact ⟨E, hEQ, hE, hrank3 E hEQ hE hEcard, hvE⟩
  set Z := omegaOneCenter Q p with hZdef
  have hZQ : Z ≤ Q := omegaOneCenter_le Q p
  have hZC : Z ≤ Subgroup.centralizer (Q : Set G) := omegaOneCenter_le_centralizer Q p
  have hZel : CFSG.Open.IsElemAbelian p Z := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => pow_eq_one_of_mem_omegaOneCenter hz⟩
    exact (Subgroup.mem_centralizer_iff.mp (hZC b.2)) a (hZQ a.2)
  have hvel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers v) := isElemAbelian_zpowers hvp
  have hvcomm : ∀ F : Subgroup G, F ≤ Subgroup.centralizer ({v} : Set G) →
      F ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun F hF => by
    rwa [centralizer_zpowers_eq']
  have hZv : Z ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    refine hvcomm Z fun z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hZC hz)) v hvQ).symm
  have hvQ' : Subgroup.zpowers v ≤ Q := Subgroup.zpowers_le.mpr hvQ
  have hvmem : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
  by_cases hvZ' : v ∈ Z
  ·
    have hEv : E ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      refine hvcomm E fun e he => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hZC hvZ')) e (hEQ he)
    have hF := isElemAbelian_sup hE hvel hEv
    have hFQ : E ⊔ Subgroup.zpowers v ≤ Q := sup_le hEQ hvQ'
    have hlt : E < E ⊔ Subgroup.zpowers v :=
      lt_of_le_of_ne le_sup_left fun h => hvE (h ▸ (le_sup_right : _ ≤ E ⊔ _) hvmem)
    have h1 := card_ge_of_lt' hp (hQp.to_le hFQ) hlt
    refine ⟨_, hFQ, hF, hrank3 _ hFQ hF ?_, (le_sup_right : _ ≤ E ⊔ _) hvmem⟩
    calc p ^ 3 ≤ Nat.card E := hEcard
      _ ≤ p * Nat.card E := Nat.le_mul_of_pos_left _ hp.pos
      _ ≤ _ := h1
  by_cases hZ2 : p ^ 2 ≤ Nat.card Z
  ·
    have hF := isElemAbelian_sup hZel hvel hZv
    have hFQ : Z ⊔ Subgroup.zpowers v ≤ Q := sup_le hZQ hvQ'
    have hlt : Z < Z ⊔ Subgroup.zpowers v :=
      lt_of_le_of_ne le_sup_left fun h => hvZ' (h ▸ (le_sup_right : _ ≤ Z ⊔ _) hvmem)
    have h1 := card_ge_of_lt' hp (hQp.to_le hFQ) hlt
    refine ⟨_, hFQ, hF, hrank3 _ hFQ hF ?_, (le_sup_right : _ ≤ Z ⊔ _) hvmem⟩
    calc p ^ 3 = p * p ^ 2 := by ring
      _ ≤ p * Nat.card Z := Nat.mul_le_mul_left p hZ2
      _ ≤ _ := h1
  push Not at hZ2
  have hQ1 : Q ≠ ⊥ := fun h => hvE (by
    have : v = 1 := by rw [h] at hvQ; exact Subgroup.mem_bot.mp hvQ
    rw [this]; exact E.one_mem)
  have hZ1 : Z ≠ ⊥ := omegaOneCenter_ne_bot hp hQp hQ1
  obtain ⟨z', hz'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  set z : G := (z' : G) with hzdef
  have hzZ : z ∈ Z := z'.2
  have hz1 : z ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hZp : IsPGroup p Z := hQp.to_le hZQ
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk1 : k = 1 := by
    have hk2 : k < 2 := by
      rw [hk] at hZ2
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hZ2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ1 (Subgroup.eq_bot_of_card_eq Z (by rw [hk, pow_zero]))
    omega
  have hzo : orderOf z = p := orderOf_eq_prime (pow_eq_one_of_mem_omegaOneCenter hzZ) hz1
  have hZz : Z = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [hk, hk1, pow_one, Nat.card_zpowers, hzo]
  have hcomm : ∀ q ∈ Q, ⁅v, q⁆ ∈ Subgroup.zpowers z := by
    intro q hq
    rw [← hZz]
    obtain ⟨hcQ, hcC⟩ := hvZ q hq
    refine ⟨hcQ, hcC, ?_⟩
    have hc : Commute ⁅v, q⁆ v := ((Subgroup.mem_centralizer_iff.mp hcC) v hvQ).symm
    rw [← commutatorElement_pow_left hc p, hvp, commutatorElement_one_left]
  have hzC : z ∈ Subgroup.centralizer (Q : Set G) := hZC hzZ
  obtain ⟨hcard, -⟩ := card_le_and_commutator_le_of_commutator_mem hzC hcomm hEQ
  rw [Nat.card_zpowers, hzo] at hcard
  set E₀ := E ⊓ Subgroup.centralizer ({v} : Set G) with hE₀def
  have hE₀el : CFSG.Open.IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hE.2 y hy.1⟩
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
    exact h
  have hE₀v : E₀ ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    hvcomm E₀ inf_le_right
  have hF := isElemAbelian_sup hE₀el hvel hE₀v
  have hFQ : E₀ ⊔ Subgroup.zpowers v ≤ Q := sup_le (inf_le_left.trans hEQ) hvQ'
  have hlt : E₀ < E₀ ⊔ Subgroup.zpowers v := by
    refine lt_of_le_of_ne le_sup_left fun h => hvE ?_
    have hv' : v ∈ E₀ ⊔ Subgroup.zpowers v :=
      (le_sup_right : Subgroup.zpowers v ≤ E₀ ⊔ _) hvmem
    rw [← h] at hv'
    exact hv'.1
  have h1 := card_ge_of_lt' hp (hQp.to_le hFQ) hlt
  refine ⟨_, hFQ, hF, hrank3 _ hFQ hF ?_, (le_sup_right : _ ≤ E₀ ⊔ _) hvmem⟩
  exact hEcard.trans (hcard.trans h1)

theorem rank_eq_sub_one_of_card_mul_two_eq {T E R : Subgroup G} (hTp : IsPGroup 2 T)
    (hRE : R ≤ E) (hET : E ≤ T) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcardE : Nat.card E = 2 ^ CFSG.Open.pRank 2 T) (hcardR : Nat.card R * 2 = Nat.card E) :
    rank R = rank T - 1 := by
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hRp : IsPGroup 2 R := hTp.to_le (hRE.trans hET)
  rw [rank_eq_pRank_of_isPGroup hp2 hTp, rank_eq_pRank_of_isPGroup hp2 hRp]
  set r := CFSG.Open.pRank 2 T
  have hr : 1 ≤ r := by
    by_contra h0
    push Not at h0
    rw [Nat.lt_one_iff.mp h0, pow_zero] at hcardE
    have := Nat.card_pos (α := R)
    omega
  have hcardR' : Nat.card R = 2 ^ (r - 1) := by
    have h : 2 ^ r = 2 ^ (r - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hr]
    rw [hcardE, h] at hcardR
    exact Nat.eq_of_mul_eq_mul_right two_pos hcardR
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRel : CFSG.Open.IsElemAbelian 2 R :=
    ⟨⟨⟨fun a b => Subtype.ext (hEc _ (hRE a.2) _ (hRE b.2))⟩⟩, fun x hx => hE.2 x (hRE hx)⟩
  refine le_antisymm ?_ (CFSG.SectionRank.le_pRank one_lt_two le_rfl hRel hcardR')
  refine CFSG.SectionRank.pRank_le one_lt_two fun F hFR _ => ?_
  rw [← hcardR']
  exact Subgroup.card_le_of_le hFR

theorem rank_hyperplane {T : Subgroup G} (hTp : IsPGroup 2 T)
    (hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (B : Subgroup (omegaOneOfComm 2 T hcommT))
    (hB : B.index = 2) : rank (B.map (omegaOneOfComm 2 T hcommT).subtype) = rank T - 1 := by
  have hET : omegaOneOfComm 2 T hcommT ≤ T := omegaOneOfComm_le T hcommT
  have hEel : CFSG.Open.IsElemAbelian 2 (omegaOneOfComm 2 T hcommT) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommT _ (hET a.2) _ (hET b.2))⟩⟩, fun x hx => hx.2⟩
  have hcardE : Nat.card (omegaOneOfComm 2 T hcommT) = 2 ^ CFSG.Open.pRank 2 T :=
    card_omegaOneOfComm Nat.prime_two T hcommT hTp
  have hcardR : Nat.card (B.map (omegaOneOfComm 2 T hcommT).subtype) * 2 =
      Nat.card (omegaOneOfComm 2 T hcommT) := by
    have h := B.card_mul_index
    rw [hB] at h
    rw [Subgroup.card_map_of_injective (omegaOneOfComm 2 T hcommT).subtype_injective]
    exact h
  exact rank_eq_sub_one_of_card_mul_two_eq hTp (Subgroup.map_subtype_le B) hET hEel hcardE hcardR

theorem le_of_forall_hyperplane {T : Subgroup G} (hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {t : G} (htT : t ∈ T) (ht : orderOf t = 2) {D Y : Subgroup G}
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) (hDodd : Odd (Nat.card D))
    (h : ∀ B : Subgroup (omegaOneOfComm 2 T hcommT), B.index = 2 →
      D ⊓ Subgroup.centralizer ((B.map (omegaOneOfComm 2 T hcommT).subtype : Subgroup G) :
        Set G) ≤ Y) :
    D ≤ Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := omegaOneOfComm 2 T hcommT with hEdef
  have hET : E ≤ T := omegaOneOfComm_le T hcommT
  have htE : t ∈ E := ⟨htT, by rw [← ht, pow_orderOf_eq_one]⟩
  have hEel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommT _ (hET a.2) _ (hET b.2))⟩⟩, fun x hx => hx.2⟩
  have : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEel.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEel.2 x x.2) }
  have : Nontrivial E := by
    refine ⟨⟨⟨t, htE⟩, 1, fun h => ?_⟩⟩
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  let _ : MulDistribMulAction E D :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer E D (hET.trans hTD)
  have hp : ¬ 2 ∣ Nat.card D := fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := D) hp
  set Yc : Subgroup D := Y.comap D.subtype with hYc
  have hle : ⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤ Yc := by
    refine iSup₂_le fun B hB => ?_
    intro x hx
    show (x : G) ∈ Y
    refine h B hB ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
    change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
    calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (x : G) * (b : G) := by rw [hbx]
  rw [hgen, top_le_iff] at hle
  intro x hx
  have hxY : (⟨x, hx⟩ : D) ∈ Yc := hle ▸ Subgroup.mem_top _
  exact hxY

theorem rank_eq_two_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) : rank V = 2 := by
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp2⟩
  have hcard : Nat.card V = 2 ^ 2 := by rw [hV.card_four]; norm_num
  have hVp : IsPGroup 2 V := IsPGroup.of_card hcard
  have hVel : CFSG.Open.IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun a b => mul_comm_of_exponent_two hV.exponent_two a b⟩⟩, fun x hx => ?_⟩
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : V)
    rw [hV.exponent_two] at h
    exact congrArg Subtype.val h
  rw [rank_eq_pRank_of_isPGroup hp2 hVp]
  refine le_antisymm (CFSG.SectionRank.pRank_le hp2.one_lt fun E hEV _ => ?_)
    (CFSG.SectionRank.le_pRank hp2.one_lt le_rfl hVel hcard)
  rw [← hcard]
  exact Subgroup.card_le_of_le hEV

theorem exists_conj_mem_kleinFour [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G)) (hr : rank (T : Subgroup G) = 3)
    {x a b : G} (hxT : x ∈ (T : Subgroup G)) (hx : orderOf x = 2) (haT : a ∈ (T : Subgroup G))
    (hbT : b ∈ (T : Subgroup G)) (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) :
    (∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * x * n⁻¹ = a) ∨
      (∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * x * n⁻¹ = b) ∨
      (∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * x * n⁻¹ = a * b) := by
  have hcomm : Commute a b := congrArg Subtype.val (hT.is_comm.comm ⟨a, haT⟩ ⟨b, hbT⟩)
  set L := kleinFourOfCommutingInvolutions a b ha hb hcomm with hLdef
  have hL : IsKleinFour L := isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hab hcomm
  have hLT : L ≤ T := by
    intro y hy
    change y ∈ ({a * b, a, b, 1} : Set G) at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ haT hbT
    · exact haT
    · exact hbT
    · exact Subgroup.one_mem _
  have hLr : rank L = rank (T : Subgroup G) - 1 := by rw [rank_eq_two_of_isKleinFour hL, hr]
  obtain ⟨n, hn, hnL⟩ := bender1970_1_3 hnonab T hT hLT hLr hxT hx
  change n * x * n⁻¹ ∈ ({a * b, a, b, 1} : Set G) at hnL
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnL
  rcases hnL with h | h | h | h
  · exact Or.inr (Or.inr ⟨n, hn, h⟩)
  · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (Or.inl ⟨n, hn, h⟩)
  · exfalso
    have hx1 : x = 1 := by
      calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    rw [hx1, orderOf_one] at hx
    omega

theorem exists_conj_of_rank_eq_three [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G)) (hr : rank (T : Subgroup G) = 3)
    {x y : G} (hxT : x ∈ (T : Subgroup G)) (hyT : y ∈ (T : Subgroup G)) (hx : orderOf x = 2)
    (hy : orderOf y = 2) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  classical
  set N := Subgroup.normalizer ((T : Subgroup G) : Set G) with hNdef
  by_contra hxy
  have hcommT : ∀ u ∈ (T : Subgroup G), ∀ v ∈ (T : Subgroup G), u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hT.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; omega
  have hy1 : y ≠ 1 := by rintro rfl; rw [orderOf_one] at hy; omega
  have hxy' : x ≠ y := by
    rintro rfl
    exact hxy ⟨1, N.one_mem, by group⟩
  set Ω := omegaOneOfComm 2 (T : Subgroup G) hcommT with hΩdef
  have hΩcard : Nat.card Ω = 8 := by
    rw [card_omegaOneOfComm Nat.prime_two _ hcommT T.isPGroup',
      ← rank_eq_pRank_of_isPGroup Nat.prime_two T.isPGroup', hr]
    norm_num
  obtain ⟨w, hwΩ, hwne⟩ : ∃ w ∈ Ω, w ∉ ({1, x, y, x * y} : Set G) := by
    by_contra h
    push Not at h
    have hsub : (Ω : Set G) ⊆ {1, x, y, x * y} := h
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hΩcard] at h1
    have h2 : ({1, x, y, x * y} : Set G).ncard ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
      refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
      rw [Set.ncard_singleton]
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hwne
  obtain ⟨hw1, hwx, hwy, hwxy⟩ := hwne
  have hwT : w ∈ (T : Subgroup G) := hwΩ.1
  have hww : w * w = 1 := by rw [← pow_two]; exact hwΩ.2
  have hsq : ∀ u ∈ (T : Subgroup G), ∀ v ∈ (T : Subgroup G), u * u = 1 → v * v = 1 →
      u * v * (u * v) = 1 := fun u hu v hv huu hvv => by
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hcommT v hv u hu]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [huu, hvv, one_mul]
  have hmT : ∀ u ∈ (T : Subgroup G), ∀ v ∈ (T : Subgroup G), u * v ∈ (T : Subgroup G) :=
    fun u hu v hv => Subgroup.mul_mem _ hu hv
  have hyw : y * w * (y * w) = 1 := hsq y hyT w hwT hyy hww
  have hxw : x * w * (x * w) = 1 := hsq x hxT w hwT hxx hww
  have hxyT := hmT x hxT y hyT
  have hxyy : x * y * (x * y) = 1 := hsq x hxT y hyT hxx hyy
  have hcancel : ∀ u v : G, u * u = 1 → u * v = 1 → v = u := fun u v huu huv => by
    calc v = u * u * v := by rw [huu, one_mul]
      _ = u := by rw [mul_assoc, huv, mul_one]
  have hxy1 : x * y ≠ 1 := fun h => hxy' (hcancel x y hxx h).symm
  have hyw1 : y * w ≠ 1 := fun h => hwy (hcancel y w hyy h)
  have hxw1 : x * w ≠ 1 := fun h => hwx (hcancel x w hxx h)
  have hyxw : y ≠ x * w := fun h => hwxy (by
    calc w = x * (x * w) := by rw [← mul_assoc, hxx, one_mul]
      _ = x * y := by rw [h])
  have hxyw' : x ≠ y * w := fun h => hwxy (by
    calc w = y * (y * w) := by rw [← mul_assoc, hyy, one_mul]
      _ = y * x := by rw [h]
      _ = x * y := hcommT y hyT x hxT)
  have hxyw2 : x * y ≠ w := fun h => hwxy h.symm
  have hxyxw : x * y ≠ x * w := fun h => hwy (mul_left_cancel h).symm
  have hdisj : ∀ z, (∃ n ∈ N, n * x * n⁻¹ = z) → (∃ n ∈ N, n * y * n⁻¹ = z) → False := by
    rintro z ⟨n, hn, rfl⟩ ⟨m, hm, hmz⟩
    apply hxy
    refine ⟨m⁻¹ * n, N.mul_mem (N.inv_mem hm) hn, ?_⟩
    calc m⁻¹ * n * x * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * x * n⁻¹) * m := by group
      _ = m⁻¹ * (m * y * m⁻¹) * m := by rw [hmz]
      _ = y := by group
  have hny : ¬ ∃ n ∈ N, n * y * n⁻¹ = x := by
    rintro ⟨n, hn, hnyx⟩
    apply hxy
    refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
    rw [← hnyx]
    group
  have e1 : y * (x * w) = x * y * w := by
    rw [← mul_assoc, hcommT y hyT x hxT]
  have e2 : x * (y * w) = x * y * w := by rw [mul_assoc]
  have e3 : x * y * (x * w) = y * w := by
    calc x * y * (x * w) = x * (y * x) * w := by group
      _ = x * (x * y) * w := by rw [hcommT y hyT x hxT]
      _ = (x * x) * (y * w) := by group
      _ = y * w := by rw [hxx, one_mul]
  have L1 := exists_conj_mem_kleinFour hnonab T hT hr hxT hx hyT hwT hyy hww hy1 hw1
    (Ne.symm hwy)
  have L2 := exists_conj_mem_kleinFour hnonab T hT hr hxT hx hyT (hmT x hxT w hwT) hyy hxw hy1
    hxw1 hyxw
  have L3 := exists_conj_mem_kleinFour hnonab T hT hr hyT hy hxT hwT hxx hww hx1 hw1
    (Ne.symm hwx)
  have L4 := exists_conj_mem_kleinFour hnonab T hT hr hyT hy hxT (hmT y hyT w hwT) hxx hyw hx1
    hyw1 hxyw'
  have L5x := exists_conj_mem_kleinFour hnonab T hT hr hxT hx hxyT hwT hxyy hww hxy1 hw1 hxyw2
  have L5y := exists_conj_mem_kleinFour hnonab T hT hr hyT hy hxyT hwT hxyy hww hxy1 hw1 hxyw2
  have L6x := exists_conj_mem_kleinFour hnonab T hT hr hxT hx hxyT (hmT x hxT w hwT) hxyy hxw
    hxy1 hxw1 hxyxw
  have L6y := exists_conj_mem_kleinFour hnonab T hT hr hyT hy hxyT (hmT x hxT w hwT) hxyy hxw
    hxy1 hxw1 hxyxw
  rw [e1] at L2
  rw [e2] at L4
  rw [e3] at L6x L6y
  by_cases hw : ∃ n ∈ N, n * x * n⁻¹ = w
  · have hw' : ¬ ∃ n ∈ N, n * y * n⁻¹ = w := fun h => hdisj _ hw h
    have hxw' : ∃ n ∈ N, n * y * n⁻¹ = x * w := by
      rcases L3 with h | h | h
      exacts [absurd h hny, absurd h hw', h]
    have hxw_x : ¬ ∃ n ∈ N, n * x * n⁻¹ = x * w := fun h => hdisj _ h hxw'
    have hxyw : ∃ n ∈ N, n * x * n⁻¹ = x * y * w := by
      rcases L2 with h | h | h
      exacts [absurd h hxy, absurd h hxw_x, h]
    have hxyw_y : ¬ ∃ n ∈ N, n * y * n⁻¹ = x * y * w := fun h => hdisj _ hxyw h
    have hyw' : ∃ n ∈ N, n * y * n⁻¹ = y * w := by
      rcases L4 with h | h | h
      exacts [absurd h hny, h, absurd h hxyw_y]
    have hyw_x : ¬ ∃ n ∈ N, n * x * n⁻¹ = y * w := fun h => hdisj _ h hyw'
    have he : ∃ n ∈ N, n * x * n⁻¹ = x * y := by
      rcases L6x with h | h | h
      exacts [h, absurd h hxw_x, absurd h hyw_x]
    have he' : ∃ n ∈ N, n * y * n⁻¹ = x * y := by
      rcases L5y with h | h | h
      exacts [h, absurd h hw', absurd h hxyw_y]
    exact hdisj _ he he'
  · have hyw : ∃ n ∈ N, n * x * n⁻¹ = y * w := by
      rcases L1 with h | h | h
      exacts [absurd h hxy, absurd h hw, h]
    have hyw' : ¬ ∃ n ∈ N, n * y * n⁻¹ = y * w := fun h => hdisj _ hyw h
    have hxyw' : ∃ n ∈ N, n * y * n⁻¹ = x * y * w := by
      rcases L4 with h | h | h
      exacts [absurd h hny, absurd h hyw', h]
    have hxyw_x : ¬ ∃ n ∈ N, n * x * n⁻¹ = x * y * w := fun h => hdisj _ h hxyw'
    have hxw : ∃ n ∈ N, n * x * n⁻¹ = x * w := by
      rcases L2 with h | h | h
      exacts [absurd h hxy, h, absurd h hxyw_x]
    have hxw' : ¬ ∃ n ∈ N, n * y * n⁻¹ = x * w := fun h => hdisj _ hxw h
    have hw' : ∃ n ∈ N, n * y * n⁻¹ = w := by
      rcases L3 with h | h | h
      exacts [absurd h hny, h, absurd h hxw']
    have he : ∃ n ∈ N, n * x * n⁻¹ = x * y := by
      rcases L5x with h | h | h
      exacts [h, absurd h hw, absurd h hxyw_x]
    have he' : ∃ n ∈ N, n * y * n⁻¹ = x * y := by
      rcases L6y with h | h | h
      exacts [h, absurd h hxw', absurd h hyw']
    exact hdisj _ he he'

theorem mem_center_of_forall_eq
    {H : Subgroup G} (hHA : IsAStar H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G)) {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b)
    (hO2 : qCoreOf H 2 ≤ W) (hKW : ∀ K : Subgroup G, IsComponentOf K H → (T : Subgroup G) ⊓ K ≤ W)
    {t : G} (ht : orderOf t = 2) (htF : t ∈ generalizedFittingSubgroupOf H) :
    ∀ h ∈ H, h * t * h⁻¹ = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
    rw [h, orderOf_one] at hx
    omega
  have hE : componentLayerOf H = ⊥ := by
    refine sSup_eq_bot.mpr fun K hK => ?_
    exfalso
    have hKQ := bender38Component hHA hK T hTH hTab
    obtain ⟨a, haQ, ha1, -⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
      (by have := hKQ.four_le_card; omega) 1
    obtain ⟨b, hbQ, hb1, hba⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
      (by have := hKQ.four_le_card; omega) a
    exact hba (hW b (hKW K hK hbQ) a (hKW K hK haQ) (hKQ.sq_eq_one b hbQ)
      (hKQ.sq_eq_one a haQ) hb1 ha1)
  have htFit : t ∈ CFSG.fittingSubgroupOf H := by
    have h : generalizedFittingSubgroupOf H = CFSG.fittingSubgroupOf H := by
      rw [generalizedFittingSubgroupOf, hE, sup_bot_eq]
      rfl
    rwa [h] at htF
  obtain ⟨t', ht'F, rfl⟩ := htFit
  have ht2' : orderOf (t' : G) = 2 := ht
  have ht'2 : t' ^ 2 ^ 1 = 1 := Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, ← ht2', pow_orderOf_eq_one]
    rfl)
  have ht'O : t' ∈ CFSG.pCore 2 H := mem_pCore_of_mem_normal_nilpotent Nat.prime_two
    CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent ht'F ht'2
  intro h hh
  have hconj : (⟨h, hh⟩ : H) * t' * (⟨h, hh⟩ : H)⁻¹ ∈ CFSG.pCore 2 H :=
    CFSG.pCore_normal.conj_mem t' ht'O ⟨h, hh⟩
  have h1 : h * t' * h⁻¹ ∈ W := hO2 ⟨_, hconj, rfl⟩
  have h2 : (t' : G) ∈ W := hO2 ⟨t', ht'O, rfl⟩
  have hconj2 : (h * t' * h⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← ht2', pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hconj1 : h * t' * h⁻¹ ≠ 1 := by
    intro h2
    apply hne1 _ ht
    calc (t' : G) = h⁻¹ * (h * t' * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group
  exact hW _ h1 _ h2 hconj2 (by show (t' : G) ^ 2 = 1; rw [← ht2', pow_orderOf_eq_one])
    hconj1 (hne1 _ ht)

theorem two_le_card_primesOfOrder {X : Subgroup G} {p q : ℕ} (hpq : p ≠ q)
    (hp : p ∈ primesOfOrder X) (hq : q ∈ primesOfOrder X) :
    2 ≤ Nat.card (primesOfOrder X) := by
  have hfin : (primesOfOrder X).Finite := (Nat.card X).primeFactors.finite_toSet
  rw [Nat.card_coe_set_eq, ← Set.ncard_pair hpq]
  exact Set.ncard_le_ncard (Set.insert_subset_iff.mpr ⟨hp, Set.singleton_subset_iff.mpr hq⟩) hfin

end CFSG.Walter
