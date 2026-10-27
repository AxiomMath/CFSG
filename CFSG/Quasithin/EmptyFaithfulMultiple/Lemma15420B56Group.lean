module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Blocks
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Char

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L15420

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_sup_of_inf_le {K R P : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hP : P ≤ K ⊔ R)
    (hPn : K ⊔ R ≤ Subgroup.normalizer (P : Set G)) (hKP : K ⊓ P ≤ pCoreOf 2 K) :
    P ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP hPn
    (isPGroup_of_le_sup hR hRK hP ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hKP))

omit [Finite G] in
theorem le_normalizer_inf_centralizer {H W : Subgroup G}
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) :
    H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := fun _ hh =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hh, B2F.normalizer_le_normalizer_centralizer W (hHW hh)⟩

omit [Finite G] in
theorem le_centralizer_omegaOneCenterOf (X : Subgroup G) :
    X ≤ Subgroup.centralizer (omegaOneCenterOf X : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (A4.centerOf_le_centralizer _
    (A4.omegaOneCenterOf_le_centerOf _ hv)) q hq).symm

omit [Finite G] in
theorem le_pCoreOf_or_le {K N : Subgroup G} (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hON : pCoreOf 2 K ≤ N) :
    N ≤ pCoreOf 2 K ∨ K ≤ N := by
  have hN : (N.subgroupOf K).Normal := by
    constructor
    intro n hn k
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKN k.2) n).mp hn
  have hM : ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
    ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with h | h
  · left
    intro x hx
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hNK hx⟩) ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      ⟨⟨x, hNK hx⟩, hx, rfl⟩
    have h2 := h h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact mk_eq_one_iff.mp h2
  · right
    intro k hk
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩) ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := h ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := h1
    have h2 : ((n⁻¹ * ⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥K) n)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ = 1
      rw [hnk, inv_mul_cancel]
    have h3 := hON (mk_eq_one_iff.mp h2)
    have h4 : (n : G) ∈ N := hn
    have e : k = (n : G) * ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by
      simp
    rw [e]
    exact N.mul_mem h4 h3

omit [Finite G] in
theorem nonempty_mulEquiv_autOn {K V : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K)
    (hOK : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G)) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autOn K V)) := by
  let f : ↥K →* ↥(autOn K V) :=
    ((conjAct V).comp (Subgroup.inclusion hKV)).codRestrict (autOn K V) fun k =>
      ⟨Subgroup.inclusion hKV k, k.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : conjAct V (Subgroup.inclusion hKV k) = 1 := congrArg Subtype.val h
      have h3 : (k : G) ∈ pCoreOf 2 K := hCK ⟨k.2, A4.conjAct_eq_one_iff.mp h1⟩
      exact (QuotientGroup.eq_one_iff k).mp (mk_eq_one_iff.mpr h3)
    · intro h
      have h3 : (k : G) ∈ pCoreOf 2 K := mk_eq_one_iff.mp ((QuotientGroup.eq_one_iff k).mpr h)
      exact Subtype.ext (A4.conjAct_eq_one_iff.mpr (hOK h3))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end L15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Comp15420

variable {s : Setting15419 G T} {I₀ K : Subgroup G} {y : G}

theorem pCoreOf_sup_le_R (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) (hC : Comp15420 s I₀ K y)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) ≤ pCoreOf 2 (s.X ⊔ T ⊓ I₀) :=
  c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer (c.hypC23 hyp h12).radical hC.mem
    hC.quasisimple hRK)

theorem omegaOneCenter_le_of_charTwo (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (c : Config15420 s I₀) (hC : Comp15420 s I₀ K y) (hK : CharTwo K)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G)) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  set Q := pCoreOf 2 (K ⊔ R) with hQdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQT : Q ≤ T := hC.pCoreOf_le_T hyp h12 c hRK
  have hCQ : (K ⊔ R) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    refine L15420.le_pCoreOf_sup_of_inf_le hR2 hRK inf_le_left
      (L15420.le_normalizer_inf_centralizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R))) ?_
    rintro x ⟨hxK, -, hxC⟩
    exact hK ⟨hxK, Subgroup.centralizer_le (pCoreOf_le_pCoreOf_sup hRK) hxC⟩
  intro z hz
  have hzT := L15420.omegaOneCenter_le_center T hz
  have hzC : ∀ q ∈ Q, q * z = z * q := fun q hq =>
    Subgroup.mem_centralizer_iff.mp hzT.2 q (hQT hq)
  have hzR : z ∈ R := c.omegaOneCenter_le_R hyp hz
  have hzQ : z ∈ Q :=
    hCQ ⟨Subgroup.mem_sup_right hzR, Subgroup.mem_centralizer_iff.mpr fun q hq => hzC q hq⟩
  refine Subgroup.subset_closure ⟨⟨hzQ, Subgroup.mem_centralizer_iff.mpr fun q hq => hzC q hq⟩, ?_⟩
  exact sq_eq_one_of_mem_omegaOneCenter T hz

theorem inf_centralizer_V_le (facts : Facts15420) (h8 : Stmt1548 G T)
    (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) (c : Config15420 s I₀)
    (hC : Comp15420 s I₀ K y) (hK : CharTwo K)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ Subgroup.centralizer
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀))) : Set G) ≤
      pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hZV := hC.omegaOneCenter_le_of_charTwo hyp h12 c hK hRK
  have hKRV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hOV : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup hRK).trans (L15420.le_centralizer_omegaOneCenterOf _)
  rcases L15420.le_pCoreOf_or_le hC.quasisimple (hC.center_eq_bot facts) inf_le_left
    (L15420.le_normalizer_inf_centralizer (le_sup_left.trans hKRV))
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hOV) with h | h
  · exact h
  · exfalso
    have hyC : y ∈ Subgroup.centralizer (V : Set G) := (h hC.y_mem.2).2
    have hyZ : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.centralizer_le hZV hyC
    have hyT : y ∈ T :=
      (inf_centralizer_omegaOneCenter_le h8 I₀ ⟨le_of_mem_cComp hC.mem hC.y_mem.2, hyZ⟩).1
    obtain ⟨n, hn⟩ := hyp.sylow.1 ⟨y, hyT⟩
    have hyn : y ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have h3 : 3 ∣ 2 ^ n := hC.y_order ▸ orderOf_dvd_of_pow_eq_one hyn
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem sup_inf_centralizer_V_le (facts : Facts15420) (h8 : Stmt1548 G T)
    (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) (c : Config15420 s I₀)
    (hC : Comp15420 s I₀ K y) (hK : CharTwo K)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G)) :
    (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) ⊓ Subgroup.centralizer
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀))) : Set G) ≤
      pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  have hKRV : K ⊔ R ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hCK := hC.inf_centralizer_V_le facts h8 hyp h12 c hK hRK
  refine L15420.le_pCoreOf_sup_of_inf_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hRK
    inf_le_left (L15420.le_normalizer_inf_centralizer hKRV) ?_
  rintro x ⟨hxK, -, hxC⟩
  exact hCK ⟨hxK, hxC⟩

theorem exists_ffStarOffender (facts : Facts15420) (h2 : Stmt1542Two G T) (h8 : Stmt1548 G T)
    (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) (c : Config15420 s I₀)
    (hC : Comp15420 s I₀ K y) (hK : CharTwo K)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G))
    (hV : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀))))) :
    ∃ A : Subgroup (MulAut (IntMod _ hV)),
      IsFFStarOffender (autI hV (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀))) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  set Q := pCoreOf 2 (K ⊔ R) with hQdef
  set V := omegaOneCenterOf Q with hVdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQR : Q ≤ R := hC.pCoreOf_sup_le_R hyp h12 c hRK
  have hCV := hC.sup_inf_centralizer_V_le facts h8 hyp h12 c hK hRK
  have hKRV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hVR : V ≤ R := (A4.omegaOneCenterOf_le _).trans hQR
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hKRV
  have hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G) := by
    intro hJ
    have hJR : thompsonJ R ≤ R := thompsonJ_le_self R
    have hJQ : thompsonJ R ≤ Q := fun x hx => hCV ⟨Subgroup.mem_sup_right (hJR hx), hJ hx⟩
    have heq : thompsonJ R = thompsonJ Q := thompsonJ_eq_of_le hJQ hQR
    have hN : K ⊔ R ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
      rw [heq]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
        (normalizer_le_normalizer_thompsonJ Q)
    have hM := c.normalizer_le_M₁ hyp h12 hJR
      (Setup.thompsonJ_ne_bot hR2 (c.R_ne_bot hyp)) (Setup.characteristic_thompsonJ R)
    exact hC.not_le_M₁ h2 (le_sup_left.trans (hN.trans hM))
  obtain ⟨B, hB⟩ := (offenderImages_nonempty_iff_not_le hV).2 hJ
  exact ⟨B, isFFStarOffender_mono (autI_mono hV le_sup_right)
    (offenderImages_isFFStarOffender hV hVR hRN hB)⟩

theorem two_pow_card {n : ℕ} (hn : 2 ≤ n) :
    6 < 2 ^ n * (4 ^ n - 1) ∧ 2 ^ n * (4 ^ n - 1) ≠ 360 ∧ 2 ^ n * (4 ^ n - 1) ≠ 2520 ∧
      2 ^ n * (4 ^ n - 1) ≠ 6048 := by
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> norm_num
  · have h64 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h4 : 4 ^ 7 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have : 2 ^ 7 * (4 ^ 7 - 1) ≤ 2 ^ n * (4 ^ n - 1) :=
      Nat.mul_le_mul h64 (Nat.sub_le_sub_right h4 1)
    norm_num at this
    omega

theorem prime_card {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    24 ≤ q * (q ^ 2 - 1) ∧ q * (q ^ 2 - 1) ≠ 720 := by
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  rcases Nat.lt_or_ge q 10 with h | h
  · have hq9 : q ≠ 9 := by
      rintro rfl
      norm_num at hq
    interval_cases q <;> first | exact absurd rfl hq9 | norm_num
  · have h1 : 10 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h 2
    have : 10 * (10 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h (Nat.sub_le_sub_right h1 1)
    norm_num at this
    omega

theorem card_quot (facts : Facts15420) (hC : Comp15420 s I₀ K y) :
    6 < Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∧ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≠ 360 ∧
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≠ 2520 ∧ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≠ 6048 := by
  have hpos : 0 < Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := Nat.card_pos
  rcases hC.type with (⟨n, hn, h⟩ | ⟨q, hq, hq2, h⟩) | ⟨-, h | h | h | h | h | h⟩
  · have hc := facts.cardPSL2Two _ n h
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h' | h'
      · interval_cases n
        · rw [hc] at hpos
          norm_num at hpos
        · exact absurd hn Nat.not_even_one
      · exact h'
    rw [hc]
    exact two_pow_card hn2
  · have hc := facts.cardPSL2Odd _ q hq hq2 h
    obtain ⟨h24, h720⟩ := prime_card hq hq2
    refine ⟨by omega, fun h' => h720 (by omega), fun h' => ?_, fun h' => ?_⟩
    · exact Comp15420.mul_sq_ne (Or.inl rfl) q (by rw [← hc, h'])
    · exact Comp15420.mul_sq_ne (Or.inr rfl) q (by rw [← hc, h'])
  · rw [facts.cardL33 _ (Or.inl h)]; norm_num
  · rw [facts.cardL33 _ (Or.inr h)]; norm_num
  · rw [facts.cardM11 _ h]; norm_num
  · rw [facts.cardL42 _ h]; norm_num
  · rw [facts.cardL52 _ h]; norm_num
  · rw [facts.cardHe _ h]; norm_num

end Comp15420

end CFSG.Quasithin.EmptyFaithfulMultiple
