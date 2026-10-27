module

public import CFSG.LocalAnalysis.StandardType.GGStdSubExistDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Elementary

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_pow {p : ℕ} (hp : p.Prime) {g : G} {k : ℕ} (hk : g ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem commute_of_mem_isCyclic {P : Subgroup G} (hP : IsCyclic P) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : a * b = b * a := by
  obtain ⟨g, hg⟩ := hP.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h : (⟨a, ha⟩ : P) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  exact congrArg Subtype.val h

theorem mem_zpowers_of_isCyclic {p : ℕ} (hp : p.Prime) {P : Subgroup G} [Finite P]
    (hP : IsCyclic P) {x z : G} (hxP : x ∈ P) (hzP : z ∈ P) (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hz : z ^ p = 1) : z ∈ Subgroup.zpowers x := by
  have := Fact.mk hp
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ c ∈ Subgroup.zpowers z, a * c = c * a := by
    intro a ha c hc
    exact commute_of_mem_isCyclic hP (Subgroup.zpowers_le.mpr hxP ha)
      (Subgroup.zpowers_le.mpr hzP hc)
  have hH := isElemAbelian_sup (isElemAbelian_zpowers hx) (isElemAbelian_zpowers hz) hcomm
  have hHP : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr hzP)
  have : Finite (Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hHP)
  have hcyc : IsCyclic (Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) :=
    Subgroup.isCyclic_of_le hHP
  have hle := card_le_of_isCyclic hp.pos hcyc fun y hy => hH.2 y hy
  have heq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge le_sup_left
      (by rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]; exact hle)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

end Elementary

section Inner

variable {G : Type} [Group G] [Finite G]

theorem pow_mem_zpowers_of_centralizer {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x y : G}
    (hxL : x ∉ L) (hx : x ^ p = 1) (hx1 : x ≠ 1) (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (hyC : y ∈ Subgroup.centralizer (L : Set G)) (hyx : y * x = x * y) (hyp : y ^ p ∈ L)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    {a m : ℕ} (hn : orderOf y = p ^ a * m) : y ^ m ∈ Subgroup.zpowers x := by
  have := Fact.mk hp
  set y₁ := y ^ m with hy₁
  have hy₁a : y₁ ^ p ^ a = 1 := by
    rw [hy₁, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hP1 := isPGroup_zpowers_of_pow hp hy₁a
  have hP2 := isPGroup_zpowers_of_pow hp (k := 1) (by rw [pow_one]; exact hx)
  have hcomm : ∀ c ∈ Subgroup.zpowers x, c * y₁ = y₁ * c := by
    intro c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.pow_left hyx m).zpow_right i).symm.eq
  have hN : Subgroup.zpowers y₁ ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute d y₁ from hcomm d hd) i).eq
  have hPp : IsPGroup p (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) :=
    hP1.to_sup_of_normal_right' hP2 hN
  have hPC : (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) ≤
      Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hyC m)) (Subgroup.zpowers_le.mpr hxC)
  have hPc := hcyc _ hPC hPp
  have hy₁P : y₁ ∈ (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  have hxP : x ∈ (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hy₁a)
  by_cases hj1 : j ≤ 1
  · have hy₁p : y₁ ^ p = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hj]
      exact (Nat.pow_dvd_pow p hj1).trans (by rw [pow_one])
    exact mem_zpowers_of_isCyclic hp hPc hxP hy₁P hx hx1 hy₁p
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    set z := y₁ ^ p ^ (k + 1) with hz
    have hzp : z ^ p = 1 := by
      rw [hz, ← pow_mul, ← pow_succ, ← hj, pow_orderOf_eq_one]
    have hz1 : z ≠ 1 := by
      rw [hz]
      apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.ne_zero)
      rw [hj]
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    have hzP : z ∈ (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers x : Subgroup G) :=
      Subgroup.pow_mem _ hy₁P _
    have hzx := mem_zpowers_of_isCyclic hp hPc hxP hzP hx hx1 hzp
    have hzL : z ∈ L := by
      have h1 : z = ((y ^ p) ^ m) ^ p ^ k := by
        rw [hz, hy₁, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [h1]
      exact Subgroup.pow_mem _ (Subgroup.pow_mem _ hyp m) _
    apply hxL
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hzx
    have heq : Subgroup.zpowers z = Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx hx1,
        orderOf_eq_prime hzp hz1])
    have hxz : x ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers x
    exact Subgroup.zpowers_le.mpr hzL hxz

theorem mem_of_mem_zpowers_of_ne_one {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x g : G}
    (hx : x ^ p = 1) (hx1 : x ≠ 1) (hg : g ∈ Subgroup.zpowers x) (hgL : g ∈ L) (hg1 : g ≠ 1) :
    x ∈ L := by
  have := Fact.mk hp
  have hgp : g ^ p = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have heq : Subgroup.zpowers g = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx hx1,
        orderOf_eq_prime hgp hg1])
  exact Subgroup.zpowers_le.mpr hgL (heq ▸ Subgroup.mem_zpowers x)

theorem mem_centralizer_of_inner {p : ℕ} (hp : p.Prime) {L T : Subgroup G} {x b l : G}
    (hlL : l ∈ L) (hbl : ∀ m ∈ L, b * m * b⁻¹ = l * m * l⁻¹) (hbp : b ^ p = 1)
    (hxL : x ∉ L) (hx : x ^ p = 1) (hx1 : x ≠ 1) (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (hbx : b * x = x * b)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hTL : T ≤ Subgroup.centralizer (L : Set G)) (hTx : T ≤ Subgroup.centralizer ({x} : Set G)) :
    b ∈ Subgroup.centralizer (T : Set G) := by
  have hLT : L ≤ Subgroup.centralizer (T : Set G) := Subgroup.le_centralizer_iff.mp hTL
  have hxT : x ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
  set y := l⁻¹ * b with hy
  have hbl' : b * l = l * b := by
    have h := hbl l hlL
    calc b * l = b * l * b⁻¹ * b := by group
      _ = l * l * l⁻¹ * b := by rw [h]
      _ = l * b := by group
  have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := hbl m hm
    calc m * (l⁻¹ * b) = l⁻¹ * (l * m * l⁻¹) * b := by group
      _ = l⁻¹ * (b * m * b⁻¹) * b := by rw [h]
      _ = l⁻¹ * b * m := by group
  have hlx : l * x = x * l := Subgroup.mem_centralizer_iff.mp hxC l hlL
  have hyx : y * x = x * y := by
    calc l⁻¹ * b * x = l⁻¹ * (x * l) * l⁻¹ * b := by rw [mul_assoc l⁻¹ b x, hbx]; group
      _ = l⁻¹ * (l * x) * l⁻¹ * b := by rw [hlx]
      _ = x * (l⁻¹ * b) := by group
  have hyp : y ^ p ∈ L := by
    have hc : Commute l⁻¹ b := by
      show l⁻¹ * b = b * l⁻¹
      calc l⁻¹ * b = l⁻¹ * (b * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * b) * l⁻¹ := by rw [hbl']
        _ = b * l⁻¹ := by group
    rw [hy, hc.mul_pow, hbp, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ hlL) _
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  have hy₁ := pow_mem_zpowers_of_centralizer hp hxL hx hx1 hxC hyC hyx hyp hcyc hn
  have hy₂ : y ^ p ^ a ∈ L := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [pow_zero, pow_one]
      have hcop : p.Coprime (orderOf y) := by
        rw [hn, pow_zero, one_mul]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
      obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hk]
      exact Subgroup.pow_mem _ hyp k
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [pow_succ', pow_mul]
      exact Subgroup.pow_mem _ hyp _
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hyeq : y = (y ^ p ^ a) ^ u * (y ^ m) ^ v := by
    rw [← zpow_natCast y (p ^ a), ← zpow_natCast y m, ← zpow_mul, ← zpow_mul, ← zpow_add]
    rw [show ((p ^ a : ℕ) : ℤ) * u + (m : ℤ) * v = 1 by linear_combination huv, zpow_one]
  have hyT : y ∈ Subgroup.centralizer (T : Set G) := by
    rw [hyeq]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (hLT hy₂) _)
      (Subgroup.zpow_mem _ (Subgroup.zpowers_le.mpr hxT hy₁) _)
  have hb : b = l * y := by rw [hy]; group
  rw [hb]
  exact Subgroup.mul_mem _ (hLT hlL) hyT

end Inner

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggAdmissible_of_clauseFour {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h4 : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    GGAdmissible p L (ggGamma L hBN).range := by
  have := Fact.mk hp
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := h4
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    mem_normalizer_of_sstar hS hnc (hTx ht)
  by_cases hU : (ggGamma L hTN).range = ⊥
  · have hTL : T ≤ Subgroup.centralizer (L : Set G) := by
      intro t ht
      have h1 : ggGamma L hTN ⟨t, ht⟩ ∈ (ggGamma L hTN).range := ⟨_, rfl⟩
      rw [hU, Subgroup.mem_bot] at h1
      exact (ggGamma_eq_one_iff L hTN ⟨t, ht⟩).mp h1
    have hT1 : T ≠ ⊥ := by
      rintro rfl
      exact hTB (Subgroup.commutator_bot_left B)
    have hN2 : IsTwoLocal (Subgroup.normalizer (T : Set G)) := ⟨T, hT1, hT2, rfl⟩
    have hLN : L ≤ Subgroup.normalizer (T : Set G) := fun l hl =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mp hTL hl)
    have hcB := card_range_ggGamma_mul L hBN hp hS
    have hbound : ∀ E : Subgroup G, E ≤ Subgroup.normalizer (T : Set G) → IsElemAbelian p E →
        Nat.card E ≤ Nat.card B := fun E hEN hE => by
      rw [hS.1.2.1]
      exact card_le_of_twoLocal hp hN2 hEN hE
    have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
      mem_centralizer_of_le_centralizer hS.2.2.2.1.1
    have hx : x ^ p = 1 := hS.1.1.2 x hS.2.1
    have hx1 : x ≠ 1 := hS.2.2.1
    have hcardE : ∀ E : Subgroup L, Nat.card (E.map L.subtype) = Nat.card E := fun E =>
      (Nat.card_congr (E.equivMapOfInjective _ L.subtype_injective).toEquiv).symm
    by_cases hxL : x ∈ L
    · refine Or.inr (Or.inr ⟨?_, fun E hE => ?_⟩)
      · have hxZ : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
          rw [Subgroup.mem_center_iff]
          intro m
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC m m.2)
        have hord : orderOf (⟨⟨x, hxL⟩, hxZ⟩ : Subgroup.center L) = p := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_eq_prime hx hx1]
        rw [← hord]
        exact orderOf_dvd_natCard _
      · have h1 := hbound (E.map L.subtype) ((Subgroup.map_subtype_le E).trans hLN)
          (isElemAbelian_map hE L.subtype)
        rw [hcardE, ← hcB] at h1
        linarith [mul_comm (Nat.card (ggGamma L hBN).range) p]
    · refine Or.inr (Or.inl ⟨?_, fun E hE => ?_⟩)
      · by_contra hall
        push Not at hall
        apply hTB
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
        intro b hb
        obtain ⟨l, hl⟩ := hall _ ⟨⟨b, hb⟩, rfl⟩
        have hbl : ∀ m ∈ L, b * m * b⁻¹ = (l : G) * m * (l : G)⁻¹ := by
          intro m hm
          have h2 := congrArg (fun φ : MulAut L => ((φ ⟨m, hm⟩ : L) : G)) hl
          simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
          rw [h2, ggGamma_coe]
        exact mem_centralizer_of_inner hp l.2 hbl (hS.1.1.2 b hb) hxL hx hx1 hxC
          (IsElemAbelian.comm hS.1.1 hb hS.2.1) hS.2.2.2.2 hTL hTx
      · set E' := E.map L.subtype with hE'
        have hEL : E' ≤ L := Subgroup.map_subtype_le E
        have hcomm : ∀ e ∈ E', ∀ c ∈ Subgroup.zpowers x, e * c = c * e := by
          intro e he c hc
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
          exact (Commute.zpow_right (show Commute e x from
            Subgroup.mem_centralizer_iff.mp hxC e (hEL he)) i).eq
        have hEab := isElemAbelian_sup (isElemAbelian_map hE L.subtype)
          (isElemAbelian_zpowers hx) hcomm
        have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (E' : Set G) := by
          intro c hc
          apply Subgroup.centralizer_le_normalizer
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact hcomm e he c hc
        have hdisj : Disjoint E' (Subgroup.zpowers x) := by
          rw [Subgroup.disjoint_def]
          intro g hgE hgx
          by_contra hg1
          exact hxL (mem_of_mem_zpowers_of_ne_one hp hx hx1 hgx (hEL hgE) hg1)
        have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
          hnorm hdisj
        rw [Nat.card_zpowers, orderOf_eq_prime hx hx1, hcardE] at hcard
        have h1 := hbound _ (sup_le (hEL.trans hLN)
          (Subgroup.zpowers_le.mpr (hBT hS.2.1))) hEab
        rw [hcard, ← hcB] at h1
        exact Nat.le_of_mul_le_mul_right h1 hp.pos
  · refine Or.inl ⟨(ggGamma L hTN).range, hU,
      hT2.of_surjective (ggGamma L hTN).rangeRestrict (ggGamma L hTN).rangeRestrict_surjective, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨b, rfl⟩ _ ⟨t, rfl⟩
    have hbtb : (b : G) * t * (b : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hBT b.2) t).mp t.2
    refine ⟨⟨(b : G) * t * (b : G)⁻¹, hbtb⟩, ?_⟩
    rw [← map_inv]
    ext m
    simp only [MulAut.mul_apply, ggGamma_coe, Subgroup.coe_inv]
    group

end Main

end CFSG.StandardType
