module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4E
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4D

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_H_le
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {T M L Mm I H K : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (hK : IsSporadic .J4 ↥K) :
    pCoreOf 2 H ≤ pCoreOf 2 I ⊓ Subgroup.centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h41 : Hyp4_1_1 G T M (conjClosure L T) := lemma_4_2_2 h37 h38 h39 hy.toHyp4_2_1
  have h5 := lemma_4_1_4_five h41 hy.sigma hy.gammaStar c.inH c.not_le
  refine le_inf (h5.2.2.1.trans h5.2.2.2) fun p hp => ?_
  have hKn := normal hy hIH c hK
  have hs : IsSimpleGroup ↥K := isSimpleGroup_of_isSporadic hK
  have hKO : K ⊓ pCoreOf 2 H = ⊥ := by
    have hnorm : ((K ⊓ pCoreOf 2 H).subgroupOf K).Normal := by
      constructor
      intro n hn k
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨K.mul_mem (K.mul_mem k.2 hn.1) (K.inv_mem k.2), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (le_of_mem_cComp c.K_mem
        k.2)) _).mp hn.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ pCoreOf 2 H).subgroupOf K) with h1 | h1
    · rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_left : K ⊓ pCoreOf 2 H ≤ K), h1,
        Subgroup.map_bot]
    · exfalso
      have hle : K ≤ pCoreOf 2 H := by
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ pCoreOf 2 H).subgroupOf K := h1 ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
      obtain ⟨a, -, ha, -, -, -⟩ := exists_e9 hK
      have h2 : IsPGroup 2 ↥K := (pCoreOf_isPGroup 2 H).to_le hle
      obtain ⟨n, hn⟩ := h2 a
      have := orderOf_dvd_of_pow_eq_one hn
      rw [ha] at this
      have h3 : (3 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hc : k * p * k⁻¹ * p⁻¹ ∈ K ⊓ pCoreOf 2 H := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hKn (pCoreOf_le 2 H hp)) k⁻¹).mp (K.inv_mem hk)
      have e : k * p * k⁻¹ * p⁻¹ = k * (p * k⁻¹ * p⁻¹) := by group
      rw [e]
      exact K.mul_mem hk this
    · have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H
        (le_of_mem_cComp c.K_mem hk)) p).mp hp
      exact (pCoreOf 2 H).mul_mem this ((pCoreOf 2 H).inv_mem hp)
  rw [hKO, Subgroup.mem_bot] at hc
  calc k * p = (k * p * k⁻¹ * p⁻¹) * (p * k) := by group
    _ = p * k := by rw [hc, one_mul]

theorem exists_r
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hOut : J4OutTrivial)
    (hBlk : J4BlockFacts) {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I)
    (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) (hILT : I ≤ L ⊔ T) :
    ∃ r : G, r ∈ pCoreOf 2 I ⊓ Subgroup.centralizer (K : Set G) ∧ r ≠ 1 ∧ r * r = 1 ∧
      I ≤ Subgroup.centralizer ({r} : Set G) ∧
      ∀ x ∈ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G),
        x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 (perfectCore (L ⊓ H)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := h6.1
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  set R := pCoreOf 2 I with hR
  set RC := R ⊓ Subgroup.centralizer (K : Set G) with hRC
  set Rp := pCoreOf 2 (L ⊔ T) with hRp
  set R₁ := Rp ⊓ Subgroup.normalizer (R : Set G) with hR₁
  set IC := I ⊓ Subgroup.centralizer (K : Set G) with hIC
  have hRE := R_eq hOut hBlk hy hIH c h6
  have hRdec : R = E ⊔ RC := hRE.1
  have hEC : E ⊓ RC = ⊥ := hRE.2
  have hER : E ≤ R := pCoreOf_LH_le c
  have hLHI : LH ≤ I := LH_le hy hIH c
  have hEK : E ≤ K := (pCoreOf_le 2 LH).trans c.LH_le
  have hVE : ⁅reducedAggregate (L ⊔ T), L⁆ = E := v_eq hBlk c h6
  have hEZ : E ≤ centerOf Rp := by
    rw [← hVE]
    exact c.V_le_omega.trans (C1GN.omegaOneCenterOf_le_centerOf _)
  have hRRp : R ≤ Rp := c.R_le
  have hRR₁ : R ≤ R₁ := le_inf hRRp Subgroup.le_normalizer
  have hIC2 : IsPGroup 2 ↥IC := isPGroup_inf_centralizer c h6 hILT
  have hR₁2 : IsPGroup 2 ↥R₁ := (pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left
  have hICn : IC ≤ Subgroup.normalizer (R₁ : Set G) := by
    intro i hi
    refine Subgroup.mem_normalizer_fintype fun y hy' => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T) (hILT hi.1)) y).mp
        hy'.1
    · have hiR := le_normalizer_pCoreOf 2 I hi.1
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hiR hy'.2) (Subgroup.inv_mem _ hiR)
  set Q := IC ⊔ R₁ with hQ
  have hQ2 : IsPGroup 2 ↥Q := IsPGroup.to_sup_of_normal_right' hIC2 hR₁2 hICn
  have hEQ : E ≤ Q := hER.trans (hRR₁.trans le_sup_right)
  have hRQ : R ≤ Q := hRR₁.trans le_sup_right
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) := by
    refine sup_le (fun i hi => ?_) (fun x hx => ?_)
    · exact normalizer_le_normalizer_pCoreOf 2 LH (c.LH_normal ⟨hIH.2 hi.1, c.I_le hi.1⟩)
    · refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have := (Subgroup.mem_centralizer_iff.mp (hEZ he).2) x hx.1
      rw [this, mul_inv_cancel_right]
      exact he
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (fun i hi => le_normalizer_pCoreOf 2 I hi.1) fun x hx => hx.2
  have hRCne : RC ≠ ⊥ := by
    intro h
    apply c.inH.2
    have h1 : pCoreOf 2 H ≤ RC := pCoreOf_H_le h37 h38 h39 hy hIH c hK
    rw [h] at h1
    exact le_bot_iff.mp h1
  have hEn : (E.subgroupOf Q).Normal := by
    constructor
    intro n hn q
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQE q.2) n).mp hn
  have hRn : (R.subgroupOf Q).Normal := by
    constructor
    intro n hn q
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQR q.2) n).mp hn
  set Rb := (R.subgroupOf Q).map (QuotientGroup.mk' (E.subgroupOf Q)) with hRb
  have hRbn : Rb.Normal := hRn.map _ (QuotientGroup.mk'_surjective _)
  have hRbne : Rb ≠ ⊥ := by
    obtain ⟨σ, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRCne
    intro hb
    have hσR : ((σ : G)) ∈ R := σ.2.1
    have hmem : QuotientGroup.mk' (E.subgroupOf Q) (⟨σ, hRQ hσR⟩ : ↥Q) ∈ Rb :=
      ⟨⟨σ, hRQ hσR⟩, Subgroup.mem_subgroupOf.mpr hσR, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    have h1 : (σ : G) ∈ E ⊓ RC := ⟨hmem, σ.2⟩
    rw [hEC, Subgroup.mem_bot] at h1
    exact hσ1 (Subtype.ext h1)
  have hQb2 : IsPGroup 2 (↥Q ⧸ E.subgroupOf Q) := hQ2.to_quotient _
  have : Group.IsNilpotent (↥Q ⧸ E.subgroupOf Q) := hQb2.isNilpotent
  obtain ⟨⟨z, hzR, hzZ⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hRbne)
  obtain ⟨ρ', hρ'R, rfl⟩ := hzR
  have hρR : ((ρ' : ↥Q) : G) ∈ R := Subgroup.mem_subgroupOf.mp hρ'R
  have hρE : ((ρ' : ↥Q) : G) ∉ E := by
    intro h
    apply hz1
    apply Subtype.ext
    show QuotientGroup.mk' (E.subgroupOf Q) ρ' = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact h
  have hρQ : ∀ q ∈ Q, q * (ρ' : G) * q⁻¹ * (ρ' : G)⁻¹ ∈ E := by
    intro q hq
    have h1 := Subgroup.mem_center_iff.mp hzZ (QuotientGroup.mk' (E.subgroupOf Q) ⟨q, hq⟩)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 : (q * (ρ' : G))⁻¹ * ((ρ' : G) * q) ∈ E := by simpa using h1
    have e : q * (ρ' : G) * q⁻¹ * (ρ' : G)⁻¹ =
        (q * (ρ' : G)) * ((q * (ρ' : G))⁻¹ * ((ρ' : G) * q))⁻¹ * (q * (ρ' : G))⁻¹ := by group
    rw [e]
    have hqρ : q * (ρ' : G) ∈ Q := Q.mul_mem hq ρ'.2
    exact (Subgroup.mem_normalizer_iff.mp (hQE hqρ) _).mp (E.inv_mem h2)
  have hERC : E ≤ Subgroup.normalizer (RC : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun σ hσ => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I (pCoreOf_le 2 I
        (hER he))) σ).mp hσ.1
    · have hc := Subgroup.mem_centralizer_iff.mp hσ.2 e (hEK he)
      rw [hc, mul_inv_cancel_right]
      exact hσ.2
  have hρmem : ((ρ' : ↥Q) : G) ∈ E ⊔ RC := by
    rw [← hRdec]
    exact hρR
  obtain ⟨e, he, r₀, hr₀, hρe⟩ := (mem_sup_of_le_normalizer hERC).mp hρmem
  have hr₀E : r₀ ∉ E := by
    intro h
    apply hρE
    rw [← hρe]
    exact E.mul_mem he h
  have hr₀Q : ∀ q ∈ Q, q * r₀ * q⁻¹ * r₀⁻¹ ∈ E := by
    intro q hq
    have h1 := hρQ q hq
    rw [← hρe] at h1
    have hqe : q * e * q⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hQE hq) e).mp he
    have e1 : q * r₀ * q⁻¹ * r₀⁻¹ =
        (q * e * q⁻¹)⁻¹ * (q * (e * r₀) * q⁻¹ * (e * r₀)⁻¹) * e := by
      group
    rw [e1]
    exact E.mul_mem (E.mul_mem (E.inv_mem hqe) h1) he
  let F : Subgroup G :=
    { carrier := {σ | σ ∈ RC ∧ ∀ q ∈ Q, q * σ * q⁻¹ * σ⁻¹ ∈ E}
      mul_mem' := by
        rintro a b ⟨ha, haQ⟩ ⟨hb, hbQ⟩
        refine ⟨RC.mul_mem ha hb, fun q hq => ?_⟩
        have e1 : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e1]
        exact E.mul_mem (haQ q hq)
          ((Subgroup.mem_normalizer_iff.mp (hQE (hRQ ha.1)) _).mp (hbQ q hq))
      one_mem' := ⟨RC.one_mem, fun q _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, haQ⟩
        refine ⟨RC.inv_mem ha, fun q hq => ?_⟩
        have e1 : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e1]
        have := (Subgroup.mem_normalizer_iff.mp (hQE (hRQ (RC.inv_mem ha).1)) _).mp
          (E.inv_mem (haQ q hq))
        rwa [inv_inv] at this }
  have hFRC : F ≤ RC := fun σ hσ => hσ.1
  have hr₀F : r₀ ∈ F := ⟨hr₀, hr₀Q⟩
  have hF2 : IsPGroup 2 ↥F := (pCoreOf_isPGroup 2 I).to_le (hFRC.trans inf_le_left)
  have hFne : F ≠ ⊥ := by
    intro h
    apply hr₀E
    have h1 : r₀ ∈ (⊥ : Subgroup G) := h ▸ hr₀F
    rw [Subgroup.mem_bot.mp h1]
    exact E.one_mem
  have hdvd : 2 ∣ Nat.card ↥F := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF2
    rw [hk]
    rcases k with _ | k
    · exfalso
      apply hFne
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq F hk
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxF : (x : G) ∈ F := x.2
  have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  refine ⟨(x : G), hFRC hxF, fun h1 => ?_, ?_, ?_, fun y hy => hxF.2 y (Subgroup.mem_sup_right hy)⟩
  · rw [h1, orderOf_one] at hx2
    omega
  · rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  · intro i hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, hk, hkc⟩ := exists_mem_centralizer hOut hK (normal hy hIH c hK (hIH.2 hi))
    have hiN : i ∈ Subgroup.normalizer (LH : Set G) := c.LH_normal ⟨hIH.2 hi, c.I_le hi⟩
    have hkLH : k ∈ LH := mem_LH_of hBlk c h6 hiN hk hkc
    set cc := k⁻¹ * i with hcc
    have hccI : cc ∈ IC := ⟨I.mul_mem (I.inv_mem (hLHI hkLH)) hi, hkc⟩
    have h1 : cc * (x : G) * cc⁻¹ * (x : G)⁻¹ ∈ E := hxF.2 cc (Subgroup.mem_sup_left hccI)
    have h2 : cc * (x : G) * cc⁻¹ * (x : G)⁻¹ ∈ RC := by
      have hxRC := hFRC hxF
      refine RC.mul_mem ⟨?_, ?_⟩ (RC.inv_mem hxRC)
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I hccI.1) _).mp hxRC.1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkc hxRC.2) (Subgroup.inv_mem _ hkc)
    have h3 : cc * (x : G) * cc⁻¹ * (x : G)⁻¹ ∈ E ⊓ RC := ⟨h1, h2⟩
    rw [hEC, Subgroup.mem_bot] at h3
    have hccx : cc * (x : G) = (x : G) * cc := by
      calc cc * (x : G) = (cc * (x : G) * cc⁻¹ * (x : G)⁻¹) * ((x : G) * cc) := by group
        _ = (x : G) * cc := by rw [h3, one_mul]
    have hkx : k * (x : G) = (x : G) * k :=
      (Subgroup.mem_centralizer_iff.mp (hFRC hxF).2 k hk)
    have hi' : i = k * cc := by rw [hcc]; group
    rw [hi']
    calc k * cc * (x : G) = k * (cc * (x : G)) := by group
      _ = k * ((x : G) * cc) := by rw [hccx]
      _ = (k * (x : G)) * cc := by group
      _ = ((x : G) * k) * cc := by rw [hkx]
      _ = (x : G) * (k * cc) := by group

end NoJ4

end CFSG.Quasithin.H13.Ch4
