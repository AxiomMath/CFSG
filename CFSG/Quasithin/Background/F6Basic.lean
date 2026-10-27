module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Recognition.GoldschmidtTriple

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D]

theorem twoResidual_eq_oTwoUpper [Finite D] (X : Subgroup D) : twoResidual X = oTwoUpper X := by
  apply le_antisymm
  · exact twoResidual_le_of_isTwoQuotient (oTwoUpper_le X) (le_normalizer_oTwoUpper X)
      (fun y hy => exists_pow_mem_oTwoUpper X hy)
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X x hx.1
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx.2)
    exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem twoResidual_mono [Finite D] {X Y : Subgroup D} (h : X ≤ Y) :
    twoResidual X ≤ twoResidual Y := by
  rw [twoResidual_eq_oTwoUpper, twoResidual_eq_oTwoUpper]
  exact oTwoUpper_mono h

theorem mem_twoResidual_of_odd [Finite D] {X : Subgroup D} {x : D} (hx : x ∈ X)
    (ho : Odd (orderOf x)) : x ∈ twoResidual X := by
  rw [twoResidual_eq_oTwoUpper]
  exact mem_oTwoUpper_of_odd hx ho

theorem pCoreOf_eq_self_of_isPGroup {p : ℕ} {Y : Subgroup D} (hY : IsPGroup p Y) :
    pCoreOf p Y = Y := by
  refine le_antisymm (pCoreOf_le p Y) fun y hy => ?_
  have htop : (⊤ : Subgroup Y) ≤ Open.pCore p Y :=
    le_pCore p Subgroup.normal_top (hY.of_equiv Subgroup.topEquiv.symm)
  exact ⟨⟨y, hy⟩, htop (Subgroup.mem_top _), rfl⟩

theorem le_pCoreOf_of_isSubnormal [Finite D] {p : ℕ} [Fact p.Prime] {Y K : Subgroup D}
    (hYK : IsSubnormal Y K) (hY : IsPGroup p Y) : Y ≤ pCoreOf p K := by
  have := A4.pCoreOf_le_of_subnormal p hYK
  rwa [pCoreOf_eq_self_of_isPGroup hY] at this

theorem isSylowIn_inf_of_isSubnormal [Finite D] {p : ℕ} [Fact p.Prime] {S X K : Subgroup D}
    (hX : IsSubnormal X K) (hS : IsSylowIn p S K) : IsSylowIn p (S ⊓ X) X := by
  revert hS
  induction hX with
  | refl K =>
    intro hS
    rwa [inf_eq_left.mpr hS.le]
  | @step X M K hXM hN _ ih =>
    intro hS
    have h1 := (ih hS).inf_normal hXM hN
    rwa [inf_assoc, inf_eq_right.mpr hXM] at h1

theorem le_of_isSubnormal_of_isSylowIn [Finite D] {p : ℕ} [Fact p.Prime] {P S X K : Subgroup D}
    (hX : IsSubnormal X K) (hP : IsSylowIn p P K) (hPX : P ≤ X) (hS : IsSylowIn p S K) :
    S ≤ X := by
  have h1 := isSylowIn_inf_of_isSubnormal hX hS
  have h2 := isSylowIn_inf_of_isSubnormal hX hP
  rw [inf_eq_left.mpr hPX] at h2
  have hcS := hS.card_eq
  have hcP := hP.card_eq
  have hc1 := h1.card_eq
  have hc2 := h2.card_eq
  have hcard : Nat.card ↥(S ⊓ X) = Nat.card S := by rw [hc1, ← hc2, hcP, hcS]
  have hle : S ⊓ X ≤ S := inf_le_left
  have heq : S ⊓ X = S := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [← heq]
  exact inf_le_right

theorem mem_normalizer_sup {A B : Subgroup D} {g : D} (hA : g ∈ Subgroup.normalizer (A : Set D))
    (hB : g ∈ Subgroup.normalizer (B : Set D)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup D) :
      Set D) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem exists_pow_mem_of_sup_eq_top {N T : Subgroup D} [N.Normal] (hT : IsPGroup 2 T)
    (hNT : N ⊔ T = ⊤) (x : D) : ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
  let φ := QuotientGroup.mk' N
  have hmap : T.map φ = ⊤ := by
    have h1 : (N ⊔ T).map φ = ⊤ := by
      rw [hNT, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hp : IsPGroup 2 (T.map φ) := hT.map φ
  rw [hmap] at hp
  obtain ⟨k, hk⟩ := hp ⟨φ x, Subgroup.mem_top _⟩
  refine ⟨k, ?_⟩
  have hk' : φ (x ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  exact (QuotientGroup.eq_one_iff _).mp hk'

theorem le_normalizer_inf_of_normal (G : Subgroup D) {X : Subgroup D} [hXn : X.Normal] :
    G ≤ Subgroup.normalizer ((G ⊓ X : Subgroup D) : Set D) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxG, hxX⟩
    exact ⟨G.mul_mem (G.mul_mem hg hxG) (G.inv_mem hg), hXn.conj_mem x hxX g⟩
  · rintro ⟨hxG, hxX⟩
    refine ⟨?_, ?_⟩
    · have := G.mul_mem (G.mul_mem (G.inv_mem hg) hxG) hg
      simpa [mul_assoc] using this
    · have := hXn.conj_mem _ hxX g⁻¹
      simpa [mul_assoc] using this

theorem isSubnormal_top_of_normal {X : Subgroup D} [hXn : X.Normal] : IsSubnormal X ⊤ :=
  A4.subnormal_of_normal le_top (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
    exact (Subgroup.normalizer_eq_top_iff.mpr hXn).ge)

variable [Finite D] {G₁ G₂ : Subgroup D}

theorem isSylowTwoOf_inf_top (h : IsGoldschmidtTriple G₁ G₂) : IsSylowTwoOf (G₁ ⊓ G₂) ⊤ := by
  obtain ⟨T, hT⟩ := h.sylow
  refine ⟨le_top, h.isPGroup_inf, ?_⟩
  have := T.not_dvd_index
  rw [hT] at this
  rwa [show ((G₁ ⊓ G₂).subgroupOf ⊤).index = (G₁ ⊓ G₂).index from
    Subgroup.relIndex_top_right _]

theorem isSylowTwoOf_inf_left (h : IsGoldschmidtTriple G₁ G₂) : IsSylowTwoOf (G₁ ⊓ G₂) G₁ := by
  refine ⟨inf_le_left, h.isPGroup_inf, ?_⟩
  change ¬ 2 ∣ (G₁ ⊓ G₂).relIndex G₁
  rw [h.relIndex_inf_left]
  decide

theorem isSylowTwoOf_inf_right (h : IsGoldschmidtTriple G₁ G₂) :
    IsSylowTwoOf (G₁ ⊓ G₂) G₂ := by
  have := isSylowTwoOf_inf_left h.symm
  rwa [inf_comm] at this

theorem pCoreOf_le_inf_left (h : IsGoldschmidtTriple G₁ G₂) : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pCoreOf_le_of_isSylowIn (isSylowTwoOf_inf_left h)

theorem pCoreOf_le_inf_right (h : IsGoldschmidtTriple G₁ G₂) : pCoreOf 2 G₂ ≤ G₁ ⊓ G₂ :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pCoreOf_le_of_isSylowIn (isSylowTwoOf_inf_right h)

theorem card_left (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card G₁ = 3 * Nat.card ↥(G₁ ⊓ G₂) := by
  have := Subgroup.relIndex_mul_card (H := G₁ ⊓ G₂) (K := G₁)
  rw [h.relIndex_inf_left, inf_eq_left.mpr inf_le_left] at this
  exact this.symm

theorem card_right (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card G₂ = 3 * Nat.card ↥(G₁ ⊓ G₂) := by
  have := card_left h.symm
  rwa [inf_comm] at this

omit [Finite D] in
theorem card_left_eq_six_mul (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card G₁ = 6 * Nat.card ↥(pCoreOf 2 G₁) := by
  obtain ⟨e⟩ := h.quotient₁
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥G₁)
  rw [Nat.card_congr e.toEquiv, gold_card_perm_fin_three] at h1
  have h2 : Nat.card ↥(pCoreOf 2 G₁) = Nat.card ↥(Open.pCore 2 ↥G₁) :=
    Nat.card_congr ((Open.pCore 2 ↥G₁).equivMapOfInjective G₁.subtype
      G₁.subtype_injective).toEquiv.symm
  rw [h2]
  exact h1

theorem relIndex_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂) :
    (pCoreOf 2 G₁).relIndex (G₁ ⊓ G₂) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 G₁) (K := G₁ ⊓ G₂)
  rw [inf_eq_left.mpr (pCoreOf_le_inf_left h)] at h1
  have h2 := card_left h
  have h3 := card_left_eq_six_mul h
  have hpos : 0 < Nat.card ↥(pCoreOf 2 G₁) := Nat.card_pos
  have : (pCoreOf 2 G₁).relIndex (G₁ ⊓ G₂) * Nat.card ↥(pCoreOf 2 G₁) =
      2 * Nat.card ↥(pCoreOf 2 G₁) := by omega
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem relIndex_pCoreOf_right (h : IsGoldschmidtTriple G₁ G₂) :
    (pCoreOf 2 G₂).relIndex (G₁ ⊓ G₂) = 2 := by
  have := relIndex_pCoreOf_left h.symm
  rwa [inf_comm] at this

theorem exists_card_inf_eq (h : IsGoldschmidtTriple G₁ G₂) :
    ∃ a : ℕ, Nat.card ↥(G₁ ⊓ G₂) = 2 ^ a :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  h.isPGroup_inf.exists_card_eq

theorem orderOf_dvd_three_of_odd (h : IsGoldschmidtTriple G₁ G₂) {x : D} (hx : x ∈ G₁)
    (ho : Odd (orderOf x)) : orderOf x ∣ 3 := by
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have hdvd : orderOf x ∣ Nat.card G₁ := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : G₁)
    rwa [Subgroup.orderOf_mk] at this
  rw [card_left h, ha] at hdvd
  have hcop : Nat.Coprime (orderOf x) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ho)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem inf_sup_twoResidual_left (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ G₂ ⊔ twoResidual G₁ = G₁ :=
  sup_twoResidual_eq (isSylowTwoOf_inf_left h)

theorem inf_sup_twoResidual_right (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ G₂ ⊔ twoResidual G₂ = G₂ :=
  sup_twoResidual_eq (isSylowTwoOf_inf_right h)

theorem exists_orderOf_eq_three_left (h : IsGoldschmidtTriple G₁ G₂) :
    ∃ x ∈ G₁, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := G₁) 3
    (by rw [card_left h]; exact dvd_mul_right 3 _)
  exact ⟨y, y.2, by rwa [Subgroup.orderOf_coe]⟩

theorem not_twoResidual_le_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂) :
    ¬ twoResidual G₁ ≤ pCoreOf 2 G₁ := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, h3⟩ := exists_orderOf_eq_three_left h
  have hxL : x ∈ twoResidual G₁ := mem_twoResidual_of_odd hx (by rw [h3]; decide)
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 G₁) ⟨x, hle hxL⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [h3] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
  omega

theorem not_twoResidual_le_pCoreOf_right (h : IsGoldschmidtTriple G₁ G₂) :
    ¬ twoResidual G₂ ≤ pCoreOf 2 G₂ :=
  not_twoResidual_le_pCoreOf_left h.symm

theorem twoResidual_top_eq (h : IsGoldschmidtTriple G₁ G₂) :
    twoResidual (⊤ : Subgroup D) = twoResidual G₁ ⊔ twoResidual G₂ := by
  refine le_antisymm ?_ (sup_le (twoResidual_mono le_top) (twoResidual_mono le_top))
  have hT₁ : G₁ ⊓ G₂ ≤ Subgroup.normalizer (twoResidual G₁ : Set D) :=
    inf_le_left.trans (le_normalizer_twoResidual G₁)
  have hT₂ : G₁ ⊓ G₂ ≤ Subgroup.normalizer (twoResidual G₂ : Set D) :=
    inf_le_right.trans (le_normalizer_twoResidual G₂)
  have hTL : G₁ ⊓ G₂ ≤
      Subgroup.normalizer ((twoResidual G₁ ⊔ twoResidual G₂ : Subgroup D) : Set D) :=
    fun t ht => mem_normalizer_sup (hT₁ ht) (hT₂ ht)
  have hG₁ : G₁ ≤ (twoResidual G₁ ⊔ twoResidual G₂) ⊔ G₁ ⊓ G₂ :=
    (inf_sup_twoResidual_left h).ge.trans (sup_le le_sup_right (le_sup_left.trans le_sup_left))
  have hG₂ : G₂ ≤ (twoResidual G₁ ⊔ twoResidual G₂) ⊔ G₁ ⊓ G₂ :=
    (inf_sup_twoResidual_right h).ge.trans
      (sup_le le_sup_right (le_sup_right.trans le_sup_left))
  have htop : (twoResidual G₁ ⊔ twoResidual G₂) ⊔ G₁ ⊓ G₂ = ⊤ :=
    top_le_iff.mp (h.gen ▸ sup_le hG₁ hG₂)
  have hnorm : (⊤ : Subgroup D) ≤
      Subgroup.normalizer ((twoResidual G₁ ⊔ twoResidual G₂ : Subgroup D) : Set D) := by
    rw [← htop]
    exact sup_le Subgroup.le_normalizer hTL
  have : (twoResidual G₁ ⊔ twoResidual G₂).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
  exact twoResidual_le_of_isTwoQuotient le_top hnorm fun x _ =>
    exists_pow_mem_of_sup_eq_top h.isPGroup_inf htop x

theorem twoResidual_le_of_isSubnormal (h : IsGoldschmidtTriple G₁ G₂) {Y : Subgroup D}
    (hY : IsSubnormal Y G₁) (hYQ : ¬ Y ≤ pCoreOf 2 G₁) : twoResidual G₁ ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYG : Y ≤ G₁ := A4.subnormal_le hY
  have hnot2 : ¬ IsPGroup 2 Y := fun h2 => hYQ (le_pCoreOf_of_isSubnormal hY h2)
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have h3Y : 3 ∣ Nat.card Y := by
    by_contra hn
    apply hnot2
    have hdvd : Nat.card Y ∣ 3 * 2 ^ a := by
      rw [← ha, ← card_left h]
      exact Subgroup.card_dvd_of_le hYG
    have hcop : Nat.Coprime (Nat.card Y) 3 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn))
    have := hcop.dvd_of_dvd_mul_left hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
    exact IsPGroup.of_card hm
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (H := Y) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  have hcardG : (Nat.card G₁).factorization 3 = 1 := by
    rw [card_left h, ha, Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two]
    simp
  have hcardY : (Nat.card Y).factorization 3 = 1 := by
    have hY0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card Y).factorization 3 :=
      (Nat.prime_three.dvd_iff_one_le_factorization hY0).mp h3Y
    have h2 : (Nat.card Y).factorization 3 ≤ (Nat.card G₁).factorization 3 :=
      (Nat.factorization_le_iff_dvd hY0 Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hYG) 3
    omega
  have hPG : IsSylowIn 3 P G₁ := by
    refine isSylowIn_of_card_eq (hP.le.trans hYG) ?_
    rw [hP.card_eq, hcardY, hcardG]
  rw [twoResidual_eq_oTwoUpper]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hord := orderOf_dvd_three_of_odd h hx.1 hx.2
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  obtain ⟨S, hS, hxS⟩ := exists_isSylowIn_ge 3 (H := G₁)
    (Subgroup.zpowers_le.mpr hx.1) hzp
  exact le_of_isSubnormal_of_isSylowIn hY hPG hP.le hS (hxS (Subgroup.mem_zpowers x))

theorem tfae_inf_le_pCoreOf (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D}
    (hX : IsSubnormal X ⊤) :
    [G₁ ⊓ X ≤ pCoreOf 2 G₁,
      G₁ ⊓ X = pCoreOf 2 G₁ ⊓ X ∧ pCoreOf 2 G₁ ⊓ X = G₁ ⊓ G₂ ⊓ X ∧
        IsSylowTwoOf (G₁ ⊓ G₂ ⊓ X) X,
      ¬ twoResidual G₁ ≤ X].TFAE := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT := pCoreOf_le_inf_left h
  tfae_have 1 → 2 := by
    intro h1
    have e1 : G₁ ⊓ X = pCoreOf 2 G₁ ⊓ X :=
      le_antisymm (le_inf h1 inf_le_right) (inf_le_inf_right X (pCoreOf_le 2 G₁))
    have e2 : pCoreOf 2 G₁ ⊓ X = G₁ ⊓ G₂ ⊓ X := by
      apply le_antisymm (inf_le_inf_right X hQT)
      rw [← e1]
      exact inf_le_inf_right X inf_le_left
    exact ⟨e1, e2, isSylowIn_inf_of_isSubnormal hX (isSylowTwoOf_inf_top h)⟩
  tfae_have 2 → 1 := fun ⟨e1, _, _⟩ => e1 ▸ inf_le_left
  tfae_have 1 → 3 := fun h1 hL =>
    not_twoResidual_le_pCoreOf_left h ((le_inf (twoResidual_le G₁) hL).trans h1)
  tfae_have 3 → 1 := by
    intro h3
    by_contra hn
    have hY : IsSubnormal (X ⊓ G₁) G₁ := A4.subnormal_inf_right hX le_top
    rw [inf_comm] at hY
    exact h3 ((twoResidual_le_of_isSubnormal h hY hn).trans inf_le_right)
  tfae_finish

theorem inf_le_pCore_of_normal (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D} [X.Normal]
    (h₁ : G₁ ⊓ X ≤ pCoreOf 2 G₁) (h₂ : G₂ ⊓ X ≤ pCoreOf 2 G₂) :
    G₁ ⊓ G₂ ⊓ X ≤ Open.pCore 2 D := by
  have hX : IsSubnormal X ⊤ := isSubnormal_top_of_normal
  have e₁ : G₁ ⊓ X = G₁ ⊓ G₂ ⊓ X := by
    obtain ⟨a, b, -⟩ := ((tfae_inf_le_pCoreOf h hX).out 1 2).mp h₁
    rw [a, b]
  have e₂ : G₂ ⊓ X = G₁ ⊓ G₂ ⊓ X := by
    obtain ⟨a, b, -⟩ := ((tfae_inf_le_pCoreOf h.symm hX).out 1 2).mp h₂
    rw [a, b, inf_comm G₂ G₁]
  have hnorm : (⊤ : Subgroup D) ≤ Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ X : Subgroup D) : Set D) := by
    rw [← h.gen]
    refine sup_le ?_ ?_
    · rw [← e₁]
      exact le_normalizer_inf_of_normal G₁
    · rw [← e₂]
      exact le_normalizer_inf_of_normal G₂
  have : (G₁ ⊓ G₂ ⊓ X).Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
  exact h.le_pCore_of_normal_le_inf inf_le_left

theorem odd_card_map_of_normal (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D} [X.Normal]
    (h₁ : G₁ ⊓ X ≤ pCoreOf 2 G₁) (h₂ : G₂ ⊓ X ≤ pCoreOf 2 G₂) :
    Odd (Nat.card ↥(X.map (QuotientGroup.mk' (Open.pCore 2 D)))) := by
  have hX : IsSubnormal X ⊤ := isSubnormal_top_of_normal
  have hTX := inf_le_pCore_of_normal h h₁ h₂
  have hQX : Open.pCore 2 D ⊓ X = G₁ ⊓ G₂ ⊓ X :=
    le_antisymm (inf_le_inf_right X h.pCore_le_inf) (le_inf hTX inf_le_right)
  have hsyl : IsSylowTwoOf (G₁ ⊓ G₂ ⊓ X) X := by
    obtain ⟨-, -, hs⟩ := ((tfae_inf_le_pCoreOf h hX).out 1 2).mp h₁
    exact hs
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have hidx : ¬ 2 ∣ (Open.pCore 2 D).relIndex X := by
    have := hsyl.2.2
    rwa [← hQX, Subgroup.inf_subgroupOf_right] at this
  exact Nat.not_even_iff_odd.mp fun he => hidx (even_iff_two_dvd.mp he)

theorem isSolvable_map_of_normal (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D} [X.Normal]
    (h₁ : G₁ ⊓ X ≤ pCoreOf 2 G₁) (h₂ : G₂ ⊓ X ≤ pCoreOf 2 G₂) :
    Group.IsSolvable ↥(X.map (QuotientGroup.mk' (Open.pCore 2 D))) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_map_of_normal h h₁ h₂)

end F6

end CFSG.Quasithin
