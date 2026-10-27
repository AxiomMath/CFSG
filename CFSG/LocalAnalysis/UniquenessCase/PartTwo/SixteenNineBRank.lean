module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16n9b_succ_le_two_pow_of_dvd_sub {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hba : b < a) (h : p ∣ 2 ^ a - 2 ^ b) : p + 1 ≤ 2 ^ a := by
  have hsplit : 2 ^ a - 2 ^ b = 2 ^ b * (2 ^ (a - b) - 1) := by
    have hab : a = b + (a - b) := (Nat.add_sub_cancel' (le_of_lt hba)).symm
    have h2a : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← pow_add, ← hab]
    rw [h2a, Nat.mul_sub_left_distrib, mul_one]
  have hcop : Nat.Coprime p (2 ^ b) :=
    ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right b
  have hdiv : p ∣ 2 ^ (a - b) - 1 := by
    rw [hsplit] at h
    exact hcop.dvd_of_dvd_mul_left h
  have hpos : 0 < 2 ^ (a - b) - 1 := by
    have h1 : 1 ≤ a - b := Nat.sub_pos_of_lt hba
    have h2 : 2 ≤ 2 ^ (a - b) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a - b) := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hple : p ≤ 2 ^ (a - b) - 1 := Nat.le_of_dvd hpos hdiv
  have hsub : 2 ^ (a - b) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le a b)
  omega

theorem s16n9b_exists_index_fixV {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hne : A ≠ ⊥) :
    ∃ Q : Subgroup (MulAut W), Q ≤ A ∧ Q.relIndex A = p ∧ p + 1 ≤ 2 ^ rk ↥(fixV Q) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p A := hA.isElementaryAbelian
  haveI : IsMulCommutative A := hA.1
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  have hcop : ¬ p ∣ Nat.card W := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := A) (H := W) (p := p) hcop
  have hex : ∃ B : Subgroup A, B.index = p ∧ ¬ fixedPointSubgroup B W ≤ fixV A := by
    by_contra hcon
    have hall : ∀ B : Subgroup A, B.index = p → fixedPointSubgroup B W ≤ fixV A := by
      intro B hB
      by_contra hle
      exact hcon ⟨B, hB, hle⟩
    have htop : (⊤ : Subgroup W) ≤ fixV A := by
      rw [← hgen]
      exact iSup₂_le hall
    have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro a ha
      ext w
      exact mem_fixV.mp (htop (Subgroup.mem_top w)) a ha
    exact hne hbot
  obtain ⟨B, hBindex, hBnot⟩ := hex
  have hQsub : (B.map A.subtype).subgroupOf A = B := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hbx⟩
      have hbx' : b = x := Subtype.ext hbx
      rwa [hbx'] at hb
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hrel : (B.map A.subtype).relIndex A = p := by
    simpa only [Subgroup.relIndex, hQsub] using hBindex
  have hXeq : fixV (B.map A.subtype) = fixedPointSubgroup B W := by
    ext w
    rw [FixedPoints.mem_subgroup]
    constructor
    · intro hFix b
      exact hFix (b : MulAut W) (Subgroup.mem_map_of_mem A.subtype b.2)
    · intro hFix q hq
      rw [Subgroup.mem_map] at hq
      obtain ⟨b, hb, rfl⟩ := hq
      exact hFix ⟨b, hb⟩
  have hXnotle : ¬ fixV (B.map A.subtype) ≤ fixV A := by
    rw [hXeq]
    exact hBnot
  have hFA : fixV A ≤ fixV (B.map A.subtype) := by
    intro w hw
    rw [mem_fixV] at hw ⊢
    intro q hq
    exact hw q (Subgroup.map_subtype_le B hq)
  have hlt : fixV A < fixV (B.map A.subtype) :=
    lt_of_le_of_ne hFA (fun heq => hXnotle (le_of_eq heq.symm))
  have hcardlt : Nat.card ↥(fixV A) < Nat.card ↥(fixV (B.map A.subtype)) :=
    Subgroup.card_lt_of_lt hlt
  haveI hInv : CFSG.IsInvariant A W (fixV (B.map A.subtype)) := by
    have hQA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
    have step : ∀ (b : A) (x : W),
        x ∈ fixV (B.map A.subtype) → b • x ∈ fixV (B.map A.subtype) := by
      intro b x hx
      rw [mem_fixV] at hx ⊢
      intro q hq
      have hqA : q ∈ A := hQA hq
      have hcomm : (q : MulAut W) * (b : MulAut W) = (b : MulAut W) * (q : MulAut W) :=
        congrArg Subtype.val (mul_comm' (⟨q, hqA⟩ : A) b)
      show (q : MulAut W) ((b : MulAut W) x) = (b : MulAut W) x
      calc (q : MulAut W) ((b : MulAut W) x)
          = ((q : MulAut W) * (b : MulAut W)) x := rfl
        _ = ((b : MulAut W) * (q : MulAut W)) x := by rw [hcomm]
        _ = (b : MulAut W) ((q : MulAut W) x) := rfl
        _ = (b : MulAut W) x := by rw [hx q hq]
    exact ⟨fun a w => ⟨fun hw => step a w hw, fun hw => by
      rw [← inv_smul_smul a w]
      exact step a⁻¹ (a • w) hw⟩⟩
  have hmod := hA.isPGroup.card_modEq_card_fixedPoints (↥(fixV (B.map A.subtype)))
  have hcardX : Nat.card ↥(fixV (B.map A.subtype)) = 2 ^ rk ↥(fixV (B.map A.subtype)) :=
    card_eq_two_pow hW _
  have hcardA : Nat.card ↥(fixV A) = 2 ^ rk ↥(fixV A) := card_eq_two_pow hW _
  have hsub : FixedPoints.subgroup A ↥(fixV (B.map A.subtype)) =
      (fixV A).subgroupOf (fixV (B.map A.subtype)) := by
    ext x
    rw [FixedPoints.mem_subgroup, Subgroup.mem_subgroupOf]
    constructor
    · intro h a ha
      exact congrArg Subtype.val (h ⟨a, ha⟩)
    · intro h a
      exact Subtype.ext (h a a.2)
  have hcardF : Nat.card (MulAction.fixedPoints A ↥(fixV (B.map A.subtype))) =
      Nat.card ↥(fixV A) := by
    calc Nat.card (MulAction.fixedPoints A ↥(fixV (B.map A.subtype)))
        = Nat.card ↥(FixedPoints.subgroup A ↥(fixV (B.map A.subtype))) := rfl
      _ = Nat.card ↥((fixV A).subgroupOf (fixV (B.map A.subtype))) := by rw [hsub]
      _ = Nat.card ↥(fixV A) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv
  have hmod2 : 2 ^ rk ↥(fixV (B.map A.subtype)) ≡ 2 ^ rk ↥(fixV A) [MOD p] := by
    have h := hmod
    rw [hcardX, hcardF, hcardA] at h
    exact h
  have hle : 2 ^ rk ↥(fixV A) ≤ 2 ^ rk ↥(fixV (B.map A.subtype)) :=
    Nat.pow_le_pow_right (by norm_num) (rk_mono hFA)
  have hdiv : p ∣ 2 ^ rk ↥(fixV (B.map A.subtype)) - 2 ^ rk ↥(fixV A) :=
    (Nat.modEq_iff_dvd' hle).mp hmod2.symm
  have hpowa : 2 ^ rk ↥(fixV A) < 2 ^ rk ↥(fixV (B.map A.subtype)) := by
    rw [← hcardA, ← hcardX]
    exact hcardlt
  have hba : rk ↥(fixV A) < rk ↥(fixV (B.map A.subtype)) :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpowa
  exact ⟨B.map A.subtype, Subgroup.map_subtype_le B, hrel,
    s16n9b_succ_le_two_pow_of_dvd_sub hp hp2 hba hdiv⟩

theorem s16n9b_exists_noncyclic_fix (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4) :
    ∃ p ∈ D.sig, ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup p B ∧ ¬ IsCyclic B ∧
      D.k < rk ↥(fixV (barSub V₀ V h.isElemAbelian B)) := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := D.M) hpP (k := 3) (hSg.three_le p hp)
  have h115 := uc22p22q_r115_of D hx h61
  have hCT : CFSG.Open.pRank p (F11.CTilde D.M V₀ V) ≤ 1 :=
    (h115 V₀ V (Hyp125.hyp11 h127 h) h4 p hp).1
  have hEnot : ¬ E ≤ F11.CTilde D.M V₀ V := by
    intro hEsub
    have h3 : 3 ≤ CFSG.Open.pRank p (F11.CTilde D.M V₀ V) :=
      CFSG.GH74.Uniqueness.SU.SU1.le_pRank hpP.one_lt hEsub hEel (k := 3) hEcard
    omega
  have hEst : E ≤ stabTil V₀ V := hEM.trans hMs
  have hEbar : IsElemAbelian p (barSub V₀ V hV E) :=
    (hEel.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
  have hEbar_ne : barSub V₀ V hV E ≠ ⊥ := by
    intro hbot
    apply hEnot
    intro e he
    rw [mem_cTilde_iff hV h.pairFacts.le_normalizer]
    refine ⟨hEM he, hMs (hEM he), ?_⟩
    have hmem : actTil V₀ V hV ⟨e, hMs (hEM he)⟩ ∈ barSub V₀ V hV E :=
      actTil_mem_barSub V₀ V hV he (hMs (hEM he))
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  obtain ⟨Q, hQA, hQrel, hQfix⟩ :=
    s16n9b_exists_index_fixV (W := Vtil V₀ V hV) (s15_Infra_vtil_sq_eq_one V₀ V hV)
      hpP hp2 hEbar hEbar_ne
  let B : Subgroup G := preBarSub E V₀ V hV Q
  have hBE : B ≤ E := inf_le_left
  have hBM : B ≤ D.M := hBE.trans hEM
  have hbarB : barSub V₀ V hV B = Q := by
    rw [barSub_preBarSub]
    exact inf_eq_left.mpr hQA
  have hid := s16c7_card_mul_card_preBarSub hV hEst hQA
  have hEbar_card : Nat.card (barSub V₀ V hV E) = p * Nat.card Q := by
    have hrel := Subgroup.relIndex_mul_card (H := Q) (K := barSub V₀ V hV E)
    rw [inf_eq_left.mpr hQA, hQrel] at hrel
    omega
  have hBcard : Nat.card B = p ^ 2 := by
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have h1 : p ^ 3 * Nat.card Q = Nat.card B * (p * Nat.card Q) := by
      rw [← hEcard, ← hEbar_card]
      exact hid
    have h2 : p ^ 3 = Nat.card B * p := by
      refine Nat.eq_of_mul_eq_mul_right hQpos ?_
      calc p ^ 3 * Nat.card Q = Nat.card B * (p * Nat.card Q) := h1
        _ = (Nat.card B * p) * Nat.card Q := by rw [Nat.mul_assoc]
    have h3 : p ^ 2 = Nat.card B := by
      refine Nat.eq_of_mul_eq_mul_right hpP.pos ?_
      calc p ^ 2 * p = p ^ 3 := by ring
        _ = Nat.card B * p := h2
    exact h3.symm
  have hBp : IsPGroup p B := (hEel.mono hBE).isPGroup
  have hBc : ¬ IsCyclic B := by
    refine s16c7_not_isCyclic_of_elemAbelian hpP (hEel.mono hBE) ?_
    rw [hBcard]
  have hk : D.k < rk ↥(fixV (barSub V₀ V hV B)) := by
    rw [hbarB]
    exact Sixteen24.k_lt_of_succ_le_two_pow D hSg h1219 hp hQfix
  exact ⟨p, hp, B, hBM, hBp, hBc, hk⟩

theorem s16n9b_inf_fixV_eq_bot (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p ∈ D.sig)
    {B : Subgroup G} (hBM : B ≤ D.M) (hBp : IsPGroup p B) (hBc : ¬ IsCyclic B)
    {U : Subgroup G} (hUV : U ≤ V) (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    imgTil V₀ V h.isElemAbelian U ⊓ fixV (barSub V₀ V h.isElemAbelian B) = ⊥ := by
  have hV := h.isElemAbelian
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  by_contra hq1
  obtain ⟨x, hxU, hmk⟩ := (mem_imgTil V₀ V hV U q).1 hq.1
  have hxV : x.val ∈ V := hUV hxU
  have hxV₀ : x.val ∉ V₀ := by
    intro hx0
    apply hq1
    rw [← hmk]
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2
      ((mem_modNull V₀ V hV x).2 hx0)
  have hx1 : x.val ≠ 1 := fun h1 => hxV₀ (h1 ▸ V₀.one_mem)
  have hx2 : x.val ^ 2 = 1 := hV.2 x.val hxV
  have hBle : B ≤ F11.CElt D.M V₀ x.val := by
    intro b hb
    have hbM : b ∈ D.M := hBM hb
    have hbs : b ∈ stabTil V₀ V := hMs hbM
    have hfix : actTil V₀ V hV ⟨b, hbs⟩ q = q :=
      (mem_fixV.mp hq.2) _ (actTil_mem_barSub V₀ V hV hb hbs)
    have hmem : (actStab V₀ V hV ⟨b, hbs⟩ x).val * (x.val)⁻¹ ∈ V₀ := by
      rw [← mkTil_eq_iff]
      rw [← actTil_mk]
      rw [hmk]
      exact hfix
    exact ⟨hbM, hbs.2, by rwa [actStab_apply_val] at hmem⟩
  have hu := c23_uniqueMax_of_le_cElt D h61 (Hyp125.hyp11 h127 h) h4
    hpP hp2 hp hBp hBc hxV hxV₀ hBle
  have hcent : centralizer ({x.val} : Set G) ≤ D.M :=
    (centralizer_le_of_uniqueMax D.maxLocal hx1 ⟨1, by simpa using hx2⟩ hu).1
  exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans hcent)

theorem s16n9b_k_add_lt_rMV (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) : ((D.k + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
  have hH : Hyp125 D V₀ V := h.hyp125
  have hV := hH.isElemAbelian
  have h4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h
  obtain ⟨p, hp, B, hBM, hBp, hBc, hk⟩ :=
    s16n9b_exists_noncyclic_fix D hSg h1219 hx h61 h127 hH h4
  set F : Subgroup (Vtil V₀ V hV) := fixV (barSub V₀ V hV B) with hF
  set f : ℕ := rk ↥F with hf
  set t : ℕ := rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) with ht
  have hft : f ≤ t := rk_mono le_top
  have htV : t + mSub V₀ = mSub V := rk_top_vtil_add_mSub V₀ V hV hH.pairFacts.le
  have hbc : (t - f) + (mSub V₀ + f) ≤ mSub V := by omega
  have hb : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      rk ↥(imgTil V₀ V hV U) ≤ t - f := by
    intro U hUV hUC
    have hbot : imgTil V₀ V hV U ⊓ F = ⊥ :=
      s16n9b_inf_fixV_eq_bot D h61 h127 hH h4 hp hBM hBp hBc hUV hUC
    have h1 : rk ↥(imgTil V₀ V hV U ⊔ F) + rk ↥(imgTil V₀ V hV U ⊓ F) =
        rk ↥(imgTil V₀ V hV U) + rk ↥F := rk_sup_add_rk_inf _ _
    rw [hbot, rk_bot] at h1
    have h2 : rk ↥(imgTil V₀ V hV U ⊔ F) ≤ t := rk_mono le_top
    omega
  have hle := le_rMV_of_forall_rk_imgTil_le D hH (b := t - f) (c := mSub V₀ + f) hbc hb
  have hkl : (D.k + mSub V₀ : ℕ) < mSub V₀ + f := by omega
  exact lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr hkl) hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
