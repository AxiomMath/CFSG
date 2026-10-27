module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_3_a

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints

/-! # Infrastructure for Proposition 4.8(b) from BG Section 4 -/

section Main

open scoped FixedPoints

public theorem CFSG.natCard_le_prime_mul_of_eq_sup_zpowers
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (y : G) (hypow : y ^ p = 1)
    (hsup : H ⊔ Subgroup.zpowers y = ⊤) :
    Nat.card G ≤ p * Nat.card H := by
  classical
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have htop_le_zpowers : (⊤ : Subgroup (G ⧸ H)) ≤ Subgroup.zpowers (q y) := by
    intro x _hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    have hg_sup : g ∈ H ⊔ Subgroup.zpowers y := by
      rw [hsup]
      simp
    rcases (Subgroup.mem_sup_of_normal_left (x := g) (s := H) (t := Subgroup.zpowers y)).1
        hg_sup with ⟨h, hh, z, hz, rfl⟩
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨k, rfl⟩
    have hq_h : q h = 1 := (QuotientGroup.eq_one_iff (N := H) h).2 hh
    change q (h * y ^ k) ∈ Subgroup.zpowers (q y)
    simp [q, map_mul, hq_h]
  have hzpowers_top : Subgroup.zpowers (q y) = ⊤ := by
    exact top_unique htop_le_zpowers
  have hqpow : (q y) ^ p = 1 := by
    simpa [q] using congrArg q hypow
  have horder_dvd : orderOf (q y) ∣ p := (orderOf_dvd_iff_pow_eq_one).2 hqpow
  have horder_le : orderOf (q y) ≤ p :=
    Nat.le_of_dvd (Fact.out : Nat.Prime p).pos horder_dvd
  have hquot_le : Nat.card (G ⧸ H) ≤ p := by
    have hcard_top :
        Nat.card (⊤ : Subgroup (G ⧸ H)) = Nat.card (G ⧸ H) :=
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ H)) ≃* (G ⧸ H)).toEquiv
    calc
      Nat.card (G ⧸ H) = Nat.card (⊤ : Subgroup (G ⧸ H)) := hcard_top.symm
      _ = Nat.card (Subgroup.zpowers (q y)) := by rw [hzpowers_top]
      _ = orderOf (q y) := by
        simp
      _ ≤ p := horder_le
  calc
    Nat.card G = Nat.card (G ⧸ H) * Nat.card H := by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := H))
    _ ≤ p * Nat.card H := Nat.mul_le_mul_right _ hquot_le

public theorem CFSG.nilpotencyClassLe_of_card_le_p_cubed
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hcard : Nat.card R ≤ p ^ 3) :
    NilpotencyClassLe 2 R := by
  let hp : Nat.Prime p := Fact.out
  let hRp : IsPGroup p R := Fact.out
  rcases subsingleton_or_nontrivial R with hsub | hnontriv
  · letI : Subsingleton R := hsub
    haveI : Group.IsNilpotent R := Group.isNilpotent_of_subsingleton
    have hnil : Group.nilpotencyClass R = 0 :=
      (Group.nilpotencyClass_zero_iff_subsingleton (G := R)).2 hsub
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := R) (n := 2)).2 <| by
      simp [hnil]
  letI : Nontrivial R := hnontriv
  letI : Group.IsNilpotent R := hRp.isNilpotent
  have hquot_p : IsPGroup p (R ⧸ Subgroup.center R) := hRp.to_quotient (Subgroup.center R)
  have hcenter_ne_bot : Subgroup.center R ≠ ⊥ := by
    exact ne_of_gt hRp.bot_lt_center
  obtain ⟨n, hn_pos, hcardR_eq⟩ := (IsPGroup.nontrivial_iff_card (p := p) (G := R) hRp).mp hnontriv
  have hcenter_card_ge : p ≤ Nat.card (Subgroup.center R) := by
    obtain ⟨k, hk, hcard_center⟩ :=
      IsPGroup.card_center_eq_prime_pow (G := R) (p := p) hcardR_eq hn_pos
    have hk_pos : 1 ≤ k := by
      have hcard_center_pos : 1 < Nat.card (Subgroup.center R) := by
        exact (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center R)).2 hcenter_ne_bot
      rw [hcard_center] at hcard_center_pos
      cases k with
      | zero =>
          simp at hcard_center hcard_center_pos
      | succ k =>
          exact Nat.succ_le_succ (Nat.zero_le _)
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ k := (Nat.pow_le_pow_iff_right hp.one_lt).2 hk_pos
      _ = Nat.card (Subgroup.center R) := hcard_center.symm
  have hquot_card_le : Nat.card (R ⧸ Subgroup.center R) ≤ p ^ 2 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := Subgroup.center R)
    have hdiv : Nat.card (R ⧸ Subgroup.center R) * p ≤ Nat.card R := by
      calc
        Nat.card (R ⧸ Subgroup.center R) * p
            ≤ Nat.card (R ⧸ Subgroup.center R) * Nat.card (Subgroup.center R) :=
              Nat.mul_le_mul_left _ hcenter_card_ge
        _ = Nat.card R := by simpa [Nat.mul_comm] using hmul.symm
    have hpow : Nat.card (R ⧸ Subgroup.center R) * p ≤ p ^ 3 := le_trans hdiv hcard
    have hcancel := Nat.le_of_mul_le_mul_right hpow hp.pos
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancel
  have hquot_comm : IsMulCommutative (R ⧸ Subgroup.center R) := by
    have hcard_quot_eq :
        Nat.card (R ⧸ Subgroup.center R) = p ^ 2 ∨
          Nat.card (R ⧸ Subgroup.center R) = p ^ 1 ∨
          Nat.card (R ⧸ Subgroup.center R) = p ^ 0 := by
      obtain ⟨n, hn⟩ := hquot_p.exists_card_eq
      have hn_le_two : n ≤ 2 := by
        have hp_one_lt : 1 < p := hp.one_lt
        have : p ^ n ≤ p ^ 2 := by simpa [hn] using hquot_card_le
        exact (Nat.pow_le_pow_iff_right hp_one_lt).1 this
      interval_cases n <;> simp [hn]
    rcases hcard_quot_eq with h2 | h1 | h0
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq
        (p := p) (G := R ⧸ Subgroup.center R) h2
    · have hcyc : IsCyclic (R ⧸ Subgroup.center R) :=
        isCyclic_of_prime_card (α := (R ⧸ Subgroup.center R)) (by simpa using h1)
      exact hcyc.isMulCommutative
    · have hsub : Subsingleton (R ⧸ Subgroup.center R) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa using h0)).1
      letI : Subsingleton (R ⧸ Subgroup.center R) := hsub
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hnil_cls : Group.nilpotencyClass R ≤ 2 := by
    letI : IsMulCommutative (R ⧸ Subgroup.center R) := hquot_comm
    letI : CommGroup (R ⧸ Subgroup.center R) := IsMulCommutative.instCommGroup
    have hquot_nil : Group.nilpotencyClass (R ⧸ Subgroup.center R) ≤ 1 := by
      simpa using (CommGroup.nilpotencyClass_le_one (G := R ⧸ Subgroup.center R))
    have hker_center : (QuotientGroup.mk' (Subgroup.center R) : R →* R ⧸ Subgroup.center R).ker ≤
        Subgroup.center R := by
      simp [QuotientGroup.ker_mk']
    have hbound :=
      Group.nilpotencyClass_le_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center R)) hker_center
    calc
      Group.nilpotencyClass R ≤ Group.nilpotencyClass (R ⧸ Subgroup.center R) + 1 := hbound
      _ ≤ 1 + 1 := Nat.add_le_add_right hquot_nil 1
      _ = 2 := by norm_num
  exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := R) (n := 2)).2 hnil_cls

public theorem CFSG.nilpotencyClassLe_of_card_le_p_four
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hcard : Nat.card R ≤ p ^ 4) :
    NilpotencyClassLe 3 R := by
  let hp : Nat.Prime p := Fact.out
  let hRp : IsPGroup p R := Fact.out
  rcases subsingleton_or_nontrivial R with hsub | hnontriv
  · letI : Subsingleton R := hsub
    haveI : Group.IsNilpotent R := Group.isNilpotent_of_subsingleton
    have hnil : Group.nilpotencyClass R = 0 :=
      (Group.nilpotencyClass_zero_iff_subsingleton (G := R)).2 hsub
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := R) (n := 3)).2 <| by
      simp [hnil]
  letI : Nontrivial R := hnontriv
  letI : Group.IsNilpotent R := hRp.isNilpotent
  have hquot_p : IsPGroup p (R ⧸ Subgroup.center R) := hRp.to_quotient (Subgroup.center R)
  have hcenter_ne_bot : Subgroup.center R ≠ ⊥ := by
    exact ne_of_gt hRp.bot_lt_center
  obtain ⟨n, hn_pos, hcardR_eq⟩ := (IsPGroup.nontrivial_iff_card (p := p) (G := R) hRp).mp hnontriv
  have hcenter_card_ge : p ≤ Nat.card (Subgroup.center R) := by
    obtain ⟨k, hk, hcard_center⟩ :=
      IsPGroup.card_center_eq_prime_pow (G := R) (p := p) hcardR_eq hn_pos
    have hk_pos : 1 ≤ k := by
      have hcard_center_pos : 1 < Nat.card (Subgroup.center R) := by
        exact (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center R)).2 hcenter_ne_bot
      rw [hcard_center] at hcard_center_pos
      cases k with
      | zero =>
          simp at hcard_center hcard_center_pos
      | succ k =>
          exact Nat.succ_le_succ (Nat.zero_le _)
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ k := (Nat.pow_le_pow_iff_right hp.one_lt).2 hk_pos
      _ = Nat.card (Subgroup.center R) := hcard_center.symm
  have hquot_card_le : Nat.card (R ⧸ Subgroup.center R) ≤ p ^ 3 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := Subgroup.center R)
    have hdiv : Nat.card (R ⧸ Subgroup.center R) * p ≤ Nat.card R := by
      calc
        Nat.card (R ⧸ Subgroup.center R) * p
            ≤ Nat.card (R ⧸ Subgroup.center R) * Nat.card (Subgroup.center R) :=
              Nat.mul_le_mul_left _ hcenter_card_ge
        _ = Nat.card R := by simpa [Nat.mul_comm] using hmul.symm
    have hpow : Nat.card (R ⧸ Subgroup.center R) * p ≤ p ^ 4 := le_trans hdiv hcard
    have hcancel := Nat.le_of_mul_le_mul_right hpow hp.pos
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancel
  letI : Fact (IsPGroup p (R ⧸ Subgroup.center R)) := ⟨hquot_p⟩
  letI : Group.IsNilpotent (R ⧸ Subgroup.center R) := hquot_p.isNilpotent
  have hquot_class : NilpotencyClassLe 2 (R ⧸ Subgroup.center R) :=
    nilpotencyClassLe_of_card_le_p_cubed (R := R ⧸ Subgroup.center R) (p := p) hquot_card_le
  have hquot_nil : Group.nilpotencyClass (R ⧸ Subgroup.center R) ≤ 2 := by
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le
      (G := R ⧸ Subgroup.center R) (n := 2)).1
      hquot_class
  have hker_center : (QuotientGroup.mk' (Subgroup.center R) : R →* R ⧸ Subgroup.center R).ker ≤
      Subgroup.center R := by
    simp [QuotientGroup.ker_mk']
  have hbound :=
    Group.nilpotencyClass_le_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center R)) hker_center
  have hnil_cls : Group.nilpotencyClass R ≤ 3 := by
    calc
      Group.nilpotencyClass R ≤ Group.nilpotencyClass (R ⧸ Subgroup.center R) + 1 := hbound
      _ ≤ 2 + 1 := Nat.add_le_add_right hquot_nil 1
      _ = 3 := by norm_num
  exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := R) (n := 3)).2 hnil_cls

public theorem CFSG.natCard_lt_of_subgroup_lt_local {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  let HK : Subgroup K := H.subgroupOf K
  have hHK_card : Nat.card HK = Nat.card H := by
    exact natCard_subgroupOf_eq H K hHK.1
  have hHK_ne_top : HK ≠ ⊤ := by
    intro htop
    apply hHK.2
    intro x hx
    have hx_top : (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) := by simp
    have hx_HK : (⟨x, hx⟩ : K) ∈ HK := by simp [htop]
    simpa [HK, Subgroup.mem_subgroupOf] using hx_HK
  have hle : Nat.card HK ≤ Nat.card K := Subgroup.card_le_card_group (H := HK)
  have hne : Nat.card HK ≠ Nat.card K := by
    intro hEq
    exact hHK_ne_top ((Subgroup.card_eq_iff_eq_top (H := HK)).1 hEq)
  have hlt : Nat.card HK < Nat.card K := lt_of_le_of_ne hle hne
  simpa [hHK_card] using hlt

public theorem CFSG.coatom_normal_of_isPGroup_local {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] [Fact (IsPGroup p G)] {K : Subgroup G} (hK : IsCoatom K) :
    K.Normal := by
  have hnil : Group.IsNilpotent G := IsPGroup.isNilpotent (p := p) (G := G) (h := Fact.out)
  letI : Group.IsNilpotent G := hnil
  have hnc : NormalizerCondition G := Group.normalizerCondition_of_isNilpotent (G := G)
  exact Subgroup.NormalizerCondition.normal_of_coatom K hnc hK


private theorem CFSG.omega₁_subgroup_map_le_global
    {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) :
    (omega₁ (G := H) (p := p)).map H.subtype ≤ omega₁ (G := G) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := omega₁ (G := G) (p := p))).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.subset_closure ?_
  simpa [pow_one] using congrArg H.subtype hx

public theorem CFSG.natCard_omega₁_subgroup_le_global
    {G : Type*} [Group G] [Finite G] {p : ℕ} (H : Subgroup G) :
    Nat.card (omega₁ (G := H) (p := p)) ≤ Nat.card (omega₁ (G := G) (p := p)) := by
  calc
    Nat.card (omega₁ (G := H) (p := p))
        = Nat.card ((omega₁ (G := H) (p := p)).map H.subtype) :=
          (Subgroup.card_map_of_injective
            (K := omega₁ (G := H) (p := p)) (f := H.subtype) H.subtype_injective).symm
    _ ≤ Nat.card (omega₁ (G := G) (p := p)) :=
      Subgroup.card_le_of_le (omega₁_subgroup_map_le_global (G := G) (p := p) H)

public theorem CFSG.omega₁_eq_top_of_forall_pow_eq_one
    {G : Type*} [Group G] {p : ℕ} (hpow : ∀ x : G, x ^ p = 1) :
    omega₁ (G := G) (p := p) = ⊤ := by
  apply eq_top_iff.2
  intro x _hx
  change x ∈ Subgroup.closure {y : G | y ^ (p ^ 1) = 1}
  refine Subgroup.subset_closure ?_
  simpa [pow_one] using hpow x

public theorem CFSG.omega₁_map_eq_of_mulEquiv
    {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H) :
    (omega₁ (G := G) (p := p)).map e.toMonoidHom = omega₁ (G := H) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [pow_one] using congrArg e.toMonoidHom hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa [pow_one] using congrArg e.symm.toMonoidHom hy

public theorem CFSG.natCard_omega₁_eq_of_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H] {p : ℕ} (e : G ≃* H) :
    Nat.card (omega₁ (G := H) (p := p)) = Nat.card (omega₁ (G := G) (p := p)) := by
  calc
    Nat.card (omega₁ (G := H) (p := p))
        = Nat.card ((omega₁ (G := G) (p := p)).map e.toMonoidHom) := by
            rw [omega₁_map_eq_of_mulEquiv (p := p) e]
    _ = Nat.card (omega₁ (G := G) (p := p)) :=
      Subgroup.card_map_of_injective
        (K := omega₁ (G := G) (p := p)) (f := e.toMonoidHom) e.injective


end Main

/-! # Proposition 4.8(b) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints
private theorem CFSG.proposition_4_8_b_aux {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] (hpgt : 3 < p) (hrank : groupRank G ≤ 2) :
    Monoid.exponent ↥(omega₁ (G := G) (p := p)) = 1 ∨
      Monoid.exponent ↥(omega₁ (G := G) (p := p)) = p := by
  classical
  have hpodd : p ≠ 2 := by omega
  let P : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H] [Fact (IsPGroup p H)],
      Nat.card H = n →
        groupRank H ≤ 2 →
          Monoid.exponent ↥(omega₁ (G := H) (p := p)) = 1 ∨
            Monoid.exponent ↥(omega₁ (G := H) (p := p)) = p
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih H _ _ _ hcardH hHrank
    by_cases hbad :
        ¬ (Monoid.exponent ↥(omega₁ (G := H) (p := p)) = 1 ∨
          Monoid.exponent ↥(omega₁ (G := H) (p := p)) = p)
    · have hnot_pair :
          ¬ ∀ x y : H, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
        intro hxy
        have hexp_dvd : Monoid.exponent ↥(omega₁ (G := H) (p := p)) ∣ p := by
          refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
          intro z
          apply Subtype.ext
          change (z : H) ^ p = 1
          refine Subgroup.closure_induction (k := {g : H | g ^ (p ^ 1) = 1}) (x := z.1) ?_ ?_ ?_ ?_
            z.2
          · intro g hg
            simpa [pow_one] using hg
          · simp
          · intro a b _ _ ha hb
            exact hxy a b ha hb
          · intro a _ ha
            simpa [inv_pow] using congrArg Inv.inv ha
        rcases (show Nat.Prime p from Fact.out).eq_one_or_self_of_dvd _ hexp_dvd with h1 | hp
        · exact hbad (Or.inl h1)
        · exact hbad (Or.inr hp)
      obtain ⟨x, y, hx, hy, hxy⟩ :
          ∃ x y : H, x ^ p = 1 ∧ y ^ p = 1 ∧ (x * y) ^ p ≠ 1 := by
        by_contra hno
        apply hnot_pair
        intro x y hx hy
        by_contra hxy'
        exact hno ⟨x, y, hx, hy, hxy'⟩
      let T : Subgroup H := Subgroup.closure ({x, y} : Set H)
      have hxT : x ∈ T := by
        change x ∈ Subgroup.closure ({x, y} : Set H)
        exact Subgroup.subset_closure (by simp)
      have hyT : y ∈ T := by
        change y ∈ Subgroup.closure ({x, y} : Set H)
        exact Subgroup.subset_closure (by simp)
      have hT_rank : groupRank T ≤ 2 :=
        (groupRank_le_of_subgroup (R := H) (S := T)).trans hHrank
      have hT_top : T = ⊤ := by
        by_contra hT_ne_top
        have hT_lt : T < ⊤ := lt_of_le_of_ne le_top hT_ne_top
        have hT_card_lt : Nat.card T < n := by
          simpa [hcardH] using natCard_lt_of_subgroup_lt_local hT_lt
        letI : Fact (IsPGroup p T) := ⟨(Fact.out : IsPGroup p H).to_subgroup T⟩
        have hTgood :
            Monoid.exponent ↥(omega₁ (G := T) (p := p)) = 1 ∨
              Monoid.exponent ↥(omega₁ (G := T) (p := p)) = p :=
          ih (Nat.card T) hT_card_lt T rfl hT_rank
        have hΩTpow :
            ∀ z : omega₁ (G := T) (p := p), z ^ p = 1 := by
          have hexp_dvd : Monoid.exponent ↥(omega₁ (G := T) (p := p)) ∣ p := by
            rcases hTgood with h1 | hp
            · rw [h1]
              exact one_dvd p
            · rw [hp]
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp_dvd
        have hxΩT : (⟨x, hxT⟩ : T) ∈ omega₁ (G := T) (p := p) := by
          change (⟨x, hxT⟩ : T) ∈ Subgroup.closure {g : T | g ^ (p ^ 1) = 1}
          refine Subgroup.subset_closure ?_
          simpa [pow_one] using hx
        have hyΩT : (⟨y, hyT⟩ : T) ∈ omega₁ (G := T) (p := p) := by
          change (⟨y, hyT⟩ : T) ∈ Subgroup.closure {g : T | g ^ (p ^ 1) = 1}
          refine Subgroup.subset_closure ?_
          simpa [pow_one] using hy
        let xyΩT : omega₁ (G := T) (p := p) :=
          ⟨(⟨x, hxT⟩ : T) * ⟨y, hyT⟩,
            (omega₁ (G := T) (p := p)).mul_mem hxΩT hyΩT⟩
        have hxyT_pow : ((⟨x, hxT⟩ : T) * ⟨y, hyT⟩) ^ p = 1 := by
          simpa [xyΩT] using congrArg Subtype.val (hΩTpow xyΩT)
        exact hxy (by simpa using congrArg Subtype.val hxyT_pow)
      by_cases hx_top : Subgroup.zpowers x = ⊤
      · have hcyc : IsCyclic H :=
          (isCyclic_iff_exists_zpowers_eq_top (α := H)).2 ⟨x, hx_top⟩
        letI : IsCyclic H := hcyc
        letI : CommGroup H := hcyc.commGroup
        have hnil : Group.nilpotencyClass H ≤ 1 := by
          simpa using (CommGroup.nilpotencyClass_le_one (G := H))
        have hclass2 : NilpotencyClassLe 2 H := by
          exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := H) (n := 2)).2
            (le_trans hnil (by decide))
        exact False.elim <| hbad (proposition_4_3_a (R := H) (p := p) hpodd (Or.inl hclass2))
      · obtain htop | ⟨M, hM_coatom, hMx⟩ := eq_top_or_exists_le_coatom (Subgroup.zpowers x)
        · exact (hx_top htop).elim
        have hM_ne_top : M ≠ ⊤ := hM_coatom.1
        have hM_lt : M < ⊤ := lt_of_le_of_ne le_top hM_ne_top
        have hM_card_lt : Nat.card M < n := by
          simpa [hcardH] using natCard_lt_of_subgroup_lt_local hM_lt
        have hM_normal : M.Normal := coatom_normal_of_isPGroup_local (p := p) (K := M) hM_coatom
        letI : M.Normal := hM_normal
        letI : Fact (IsPGroup p M) := ⟨(Fact.out : IsPGroup p H).to_subgroup M⟩
        have hM_rank : groupRank M ≤ 2 :=
          (groupRank_le_of_subgroup (R := H) (S := M)).trans hHrank
        have hMgood :
            Monoid.exponent ↥(omega₁ (G := M) (p := p)) = 1 ∨
              Monoid.exponent ↥(omega₁ (G := M) (p := p)) = p :=
          ih (Nat.card M) hM_card_lt M rfl hM_rank
        let ΩM : Subgroup M := omega₁ (G := M) (p := p)
        letI : ΩM.Characteristic := omega₁_characteristic M
        let ΩH : Subgroup H := ΩM.map M.subtype
        have hΩH_normal : ΩH.Normal := by
          exact ConjAct.normal_of_characteristic_of_normal
        letI : ΩH.Normal := hΩH_normal
        have hxM_mem : x ∈ M := hMx (Subgroup.mem_zpowers x)
        have hxΩM : (⟨x, hxM_mem⟩ : M) ∈ ΩM := by
          change (⟨x, hxM_mem⟩ : M) ∈ Subgroup.closure {g : M | g ^ (p ^ 1) = 1}
          refine Subgroup.subset_closure ?_
          simpa [pow_one] using hx
        have hxΩH : x ∈ ΩH := Subgroup.mem_map_of_mem M.subtype hxΩM
        have hMp : IsPGroup p M := Fact.out
        have hΩMp : IsPGroup p ΩM := hMp.to_subgroup ΩM
        have hΩM_rank : groupRank ΩM ≤ 2 :=
          (groupRank_le_of_subgroup (R := M) (S := ΩM)).trans hM_rank
        have hΩH_card_eq : Nat.card ΩH = Nat.card ΩM := by
          exact Subgroup.card_map_of_injective (K := ΩM) (f := M.subtype) M.subtype_injective
        have hΩH_card_le : Nat.card ΩH ≤ p ^ 3 := by
          rcases hMgood with h1 | hp
          · haveI : Subsingleton ΩM := (Monoid.exp_eq_one_iff (G := ΩM)).mp h1
            have hΩM_eq_bot : ΩM = ⊥ := by
              rw [Subgroup.eq_bot_iff_forall]
              intro z hz
              have hz' : (⟨z, hz⟩ : ΩM) = 1 := Subsingleton.elim _ _
              simpa using congrArg Subtype.val hz'
            calc
              Nat.card ΩH = Nat.card ΩM := hΩH_card_eq
              _ = 1 := by simp [hΩM_eq_bot]
              _ ≤ p ^ 3 := Nat.succ_le_of_lt (pow_pos (show 0 < p from (Fact.out : Nat.Prime p).pos) 3)
          · letI : Fact (IsPGroup p ΩM) := ⟨hΩMp⟩
            calc
              Nat.card ΩH = Nat.card ΩM := hΩH_card_eq
              _ ≤ p ^ 3 := proposition_4_8_a (R := ΩM) (p := p) hΩM_rank hp
        have hy_zpowers : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
        have hΩH_sup : ΩH ⊔ Subgroup.zpowers y = ⊤ := by
          apply top_unique
          rw [← hT_top]
          refine (Subgroup.closure_le (K := ΩH ⊔ Subgroup.zpowers y)).2 ?_
          intro z hz
          rcases hz with rfl | rfl
          · exact Subgroup.mem_sup_left hxΩH
          · exact Subgroup.mem_sup_right hy_zpowers
        have hcard_le_p_four : Nat.card H ≤ p ^ 4 := by
          calc
            Nat.card H ≤ p * Nat.card ΩH :=
              natCard_le_prime_mul_of_eq_sup_zpowers (G := H) (p := p) ΩH y hy hΩH_sup
            _ ≤ p * p ^ 3 := Nat.mul_le_mul_left p hΩH_card_le
            _ = p ^ 4 := by
              simp [pow_succ, Nat.mul_comm]
        have hclass3 : NilpotencyClassLe 3 H :=
          nilpotencyClassLe_of_card_le_p_four (R := H) (p := p) hcard_le_p_four
        exact False.elim <| hbad (proposition_4_3_a (R := H) (p := p) hpodd (Or.inr ⟨hpgt, hclass3⟩))
    · exact Classical.not_not.mp hbad
  simpa using (hP (Nat.card G) G rfl hrank)

public theorem CFSG.proposition_4_8_b {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hpgt : 3 < p) (hrank : groupRank R ≤ 2) :
    Monoid.exponent ↥(omega₁ (G := R) (p := p)) = 1 ∨
      Monoid.exponent ↥(omega₁ (G := R) (p := p)) = p := by
  exact proposition_4_8_b_aux (G := R) (p := p) hpgt hrank


end Main
