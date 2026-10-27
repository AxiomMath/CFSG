module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31a
public import CFSG.Quasithin.Vol2.Ch12Sec6L33t
public import CFSG.Quasithin.EmptyFaithful.S152XA5

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Simple

variable {Q : Type*} [Group Q]

theorem isSimpleGroup_alt5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem not_comm_alt5 : ¬ ∀ a b : ↥(alternatingGroup (Fin 5)), a * b = b * a := fun h =>
  absurd (h ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
    ⟨swap 1 2 * swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩) (by decide)

theorem not_comm_of_mulEquiv {X : Subgroup Q} (e : ↥X ≃* alternatingGroup (Fin 5)) :
    ¬ ∀ a b : ↥X, a * b = b * a := fun hab => not_comm_alt5 fun a b => by
  have := congrArg e (hab (e.symm a) (e.symm b))
  simpa using this

theorem inf_eq_bot_of_commute {X Y : Subgroup Q} (hX : IsSimpleGroup ↥X)
    (hnab : ¬ ∀ a b : ↥X, a * b = b * a) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ⊓ Y = ⊥ := by
  have hn : (Y.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hc g g.2 n hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, this, mul_inv_cancel_right]
    exact hn⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hb
    rw [inf_comm]
    exact hb
  · exfalso
    apply hnab
    intro a b
    have hb : (b : Q) ∈ Y := by
      have : b ∈ Y.subgroupOf X := ht ▸ Subgroup.mem_top b
      exact this
    exact Subtype.ext (hc a a.2 b hb)

theorem exists_card_three {X : Subgroup Q} (e : ↥X ≃* alternatingGroup (Fin 5)) :
    ∃ A : Subgroup Q, A ≤ X ∧ Nat.card A = 3 := by
  set c : ↥(alternatingGroup (Fin 5)) :=
    ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩ with hc
  have hc3 : orderOf c = 3 := by
    refine orderOf_eq_prime (Subtype.ext (by decide)) ?_
    intro h
    have := congrArg (fun z : ↥(alternatingGroup (Fin 5)) => (z : Perm (Fin 5)) 0) h
    exact absurd this (by decide)
  set f : ↥(alternatingGroup (Fin 5)) →* Q := X.subtype.comp e.symm.toMonoidHom with hf
  have hfi : Function.Injective f :=
    X.subtype_injective.comp e.symm.injective
  refine ⟨(Subgroup.zpowers c).map f, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e.symm y).2
  · rw [Subgroup.card_map_of_injective hfi, Nat.card_zpowers, hc3]

theorem card_mulAut_alt5 : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))), Nat.card_perm, Nat.card_fin]
  rfl

end Simple

section Borel

variable {Q : Type*} [Group Q] [Finite Q]

theorem isSolvable_borel {X S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S X) :
    Group.IsSolvable ↥(borel X S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := borel X S with hB
  have hSX : S ⊓ X = S := inf_of_le_left hS.1
  have hSB : S ≤ B := le_inf hS.1 (by rw [hSX]; exact Subgroup.le_normalizer)
  have hBX : B ≤ X := inf_le_left
  have hBN : B ≤ Subgroup.normalizer (S : Set Q) := by
    rw [hB, S126.borel, hSX]
    exact inf_le_right
  have hn : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).2 hBN
  have hodd : Odd (Nat.card (↥B ⧸ S.subgroupOf B)) := by
    rw [← Subgroup.index_eq_card]
    have h1 : (S.subgroupOf B).index = S.relIndex B := rfl
    have h2 : S.relIndex B ∣ S.relIndex X :=
      ⟨_, (Subgroup.relIndex_mul_relIndex S B X hSB hBX).symm⟩
    rw [h1]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => hS.2.2 (h.trans h2))
  have hq : Group.IsSolvable (↥B ⧸ S.subgroupOf B) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hSp : IsPGroup 2 ↥(S.subgroupOf B) := hS.2.1.comap_subtype
  have : Group.IsNilpotent ↥(S.subgroupOf B) := hSp.isNilpotent
  exact Group.isSolvable_of_ker_le_range (S.subgroupOf B).subtype
    (QuotientGroup.mk' (S.subgroupOf B)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_sup_borel {X T : Subgroup Q} (hT : IsPGroup 2 T)
    (hTX : T ≤ Subgroup.normalizer (X : Set Q))
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ X) X) : Group.IsSolvable ↥(T ⊔ borel X T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := borel X T with hB
  have hBe : B = borel X (T ⊓ X) := by
    rw [hB, S126.borel, S126.borel, inf_assoc, inf_idem]
  have hBs : Group.IsSolvable ↥B := hBe ▸ isSolvable_borel hS
  have hTB : T ≤ Subgroup.normalizer (B : Set Q) := by
    intro t ht
    have htS : t ∈ Subgroup.normalizer ((T ⊓ X : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.1 (hTX ht) y
      exact ⟨fun hy => ⟨T.mul_mem (T.mul_mem ht hy.1) (T.inv_mem ht), h1.1 hy.2⟩,
        fun hy => ⟨by simpa [mul_assoc] using T.mul_mem (T.mul_mem (T.inv_mem ht) hy.1) ht,
          h1.2 hy.2⟩⟩
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have h1 := Subgroup.mem_normalizer_iff.1 (hTX ht) b
    constructor
    · rintro ⟨hbX, hbN⟩
      exact ⟨h1.1 hbX, Subgroup.mul_mem _ (Subgroup.mul_mem _ htS hbN) (Subgroup.inv_mem _ htS)⟩
    · rintro ⟨hbX, hbN⟩
      refine ⟨h1.2 hbX, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htS) hbN) htS
      simpa [mul_assoc] using this
  have hle : T ⊔ B ≤ Subgroup.normalizer (B : Set Q) := sup_le hTB Subgroup.le_normalizer
  have hn : (B.subgroupOf (T ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hle
  have hq : IsPGroup 2 (↥(T ⊔ B) ⧸ B.subgroupOf (T ⊔ B)) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have htop : B.subgroupOf (T ⊔ B) ⊔ T.subgroupOf (T ⊔ B) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_right le_sup_left, sup_comm, Subgroup.subgroupOf_self]
    have hy : y ∈ B.subgroupOf (T ⊔ B) ⊔ T.subgroupOf (T ⊔ B) := htop ▸ Subgroup.mem_top y
    obtain ⟨b, hb, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
    obtain ⟨k, hk⟩ := hT ⟨(s : Q), hs⟩
    refine ⟨k, ?_⟩
    have hs1 : s ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hb, one_mul, ← QuotientGroup.mk_pow,
      hs1, QuotientGroup.mk_one]
  have : Group.IsNilpotent (↥(T ⊔ B) ⧸ B.subgroupOf (T ⊔ B)) := hq.isNilpotent
  have : Group.IsSolvable ↥(B.subgroupOf (T ⊔ B)) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : B ≤ T ⊔ B)).symm.toMonoidHom) (MulEquiv.surjective _)
  exact Group.isSolvable_of_ker_le_range (B.subgroupOf (T ⊔ B)).subtype
    (QuotientGroup.mk' (B.subgroupOf (T ⊔ B)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Borel

section Pair

variable [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem isSimple_star_conjSub (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {g : G}
    (hg : g ∈ H) : IsSimpleGroup ↥(star H (conjSub g K)) := by
  have := isSimpleGroup_alt5
  have hs : IsSimpleGroup ↥(star H K) := e₁.isSimpleGroup
  rw [L1233.star_conjSub hg]
  exact (((star H K).equivMapOfInjective _ (MulAut.conj _).injective).symm).isSimpleGroup

noncomputable def equivConjSub (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {g : G}
    (hg : g ∈ H) : ↥(star H (conjSub g K)) ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr (L1233.star_conjSub hg)).trans
    ((((star H K).equivMapOfInjective _ (MulAut.conj _).injective).symm).trans e₁)

theorem conjSub_mem_pair' {T L V : Subgroup G} (hH : Hyp126 G T L V) {V₁ Vp H K : Subgroup G}
    (h918 : HypF918 T V L V₁ Vp H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) {t : G} (ht : t ∈ T) :
    conjSub t K = K ∨ conjSub t K = conjSub t₀ K := by
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hKc : K ∈ cComp H := h918.K_cComp
  have hK₂c : conjSub t₀ K ∈ cComp H := L1233.conjSub_mem_cComp hKc (hTH ht₀)
  have hXc : conjSub t K ∈ cComp H := L1233.conjSub_mem_cComp hKc (hTH ht)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have := isSimpleGroup_alt5
  have hsK : IsSimpleGroup ↥(star H K) := e₁.isSimpleGroup
  have hsK₂ := isSimple_star_conjSub e₁ (hTH ht₀)
  have hsX := isSimple_star_conjSub e₁ (hTH ht)
  have hKK₂ : K ≠ conjSub t₀ K := fun he =>
    ht₀K (L1233.mem_normalizer_of_conjSub_eq he.symm)
  have hc12 := L1233.commute_star hKc hK₂c hKK₂ hsK hsK₂
  have hcX1 := L1233.commute_star hXc hKc hne1 hsX hsK
  have hcX2 := L1233.commute_star hXc hK₂c hne2 hsX hsK₂
  obtain ⟨A, hAK, hA⟩ := exists_card_three e₁
  obtain ⟨B, hBK, hB⟩ := exists_card_three (equivConjSub e₁ (hTH ht₀))
  obtain ⟨C, hCX, hC⟩ := exists_card_three (equivConjSub e₁ (hTH ht))
  have hAB : A ≤ Subgroup.centralizer (B : Set (HStar H)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hc12 a (hAK ha) b (hBK hb)).symm
  have hAC : A ≤ Subgroup.centralizer (C : Set (HStar H)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun c hc => hcX1 c (hCX hc) a (hAK ha)
  have hBC : B ≤ Subgroup.centralizer (C : Set (HStar H)) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun c hc => hcX2 c (hCX hc) b (hBK hb)
  have hi12 : star H K ⊓ star H (conjSub t₀ K) = ⊥ :=
    inf_eq_bot_of_commute hsK (not_comm_of_mulEquiv e₁) hc12
  have hsupC : star H K ⊔ star H (conjSub t₀ K) ≤
      Subgroup.centralizer (star H (conjSub t K) : Set (HStar H)) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => hcX1 x hx a ha)
      (fun b hb => Subgroup.mem_centralizer_iff.2 fun x hx => hcX2 x hx b hb)
  have hiX : star H (conjSub t K) ⊓ (star H K ⊔ star H (conjSub t₀ K)) = ⊥ :=
    inf_eq_bot_of_commute hsX (not_comm_of_mulEquiv (equivConjSub e₁ (hTH ht)))
      fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hsupC hy) x hx
  have hi : A ⊓ B = ⊥ := le_bot_iff.1 (hi12 ▸ inf_le_inf hAK hBK)
  have hi' : (A ⊔ B) ⊓ C = ⊥ := by
    refine le_bot_iff.1 (hiX ▸ ?_)
    rw [inf_comm]
    exact inf_le_inf hCX (sup_le_sup hAK hBK)
  exact false_of_three hH (pCoreOf_ne_bot h) hA hB hC hAB hAC hBC hi hi'

noncomputable def equivProd {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) : ↥(A ⊔ B) ≃* ↥A × ↥B :=
  ((MonoidHom.ofInjective (L1233.mulHom_injective hc hi)).trans
    (MulEquiv.subgroupCongr (L1233.range_mulHom A B hc))).symm

theorem conjClosure_eq_sup {T L V : Subgroup G} (hH : Hyp126 G T L V) {V₁ Vp H K : Subgroup G}
    (h918 : HypF918 T V L V₁ Vp H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    conjClosure K T = K ⊔ conjSub t₀ K := by
  apply le_antisymm
  · refine conjClosure_le fun t ht k hk => ?_
    have hm : t * k * t⁻¹ ∈ conjSub t K := mul_mem_conjSub hk
    rcases conjSub_mem_pair' hH h918 e₁ ht₀ ht₀K ht with h | h
    · rw [h] at hm
      exact Subgroup.mem_sup_left hm
    · rw [h] at hm
      exact Subgroup.mem_sup_right hm
  · refine sup_le (le_conjClosure K T) fun x hx => ?_
    have h2 := mem_conjClosure ht₀ (mem_conjSub.1 hx)
    simpa [mul_assoc] using h2

theorem star_conjClosure_eq_sup {T L V : Subgroup G} (hH : Hyp126 G T L V)
    {V₁ Vp H K : Subgroup G} (h918 : HypF918 T V L V₁ Vp H K)
    (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    star H (conjClosure K T) = star H K ⊔ star H (conjSub t₀ K) := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  rw [conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K, star_sup (le_of_mem_cComp h918.K_cComp)
    (le_of_mem_cComp (L1233.conjSub_mem_cComp h918.K_cComp (hTH ht₀)))]

theorem commute_pair {T V L V₁ Vp H K : Subgroup G} (h918 : HypF918 T V L V₁ Vp H K)
    (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    (∀ x ∈ star H K, ∀ y ∈ star H (conjSub t₀ K), x * y = y * x) ∧
      star H K ⊓ star H (conjSub t₀ K) = ⊥ := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  have := isSimpleGroup_alt5
  have hsK : IsSimpleGroup ↥(star H K) := e₁.isSimpleGroup
  have hKK₂ : K ≠ conjSub t₀ K := fun he =>
    ht₀K (L1233.mem_normalizer_of_conjSub_eq he.symm)
  have hc := L1233.commute_star h918.K_cComp (L1233.conjSub_mem_cComp h918.K_cComp (hTH ht₀))
    hKK₂ hsK (isSimple_star_conjSub e₁ (hTH ht₀))
  exact ⟨hc, inf_eq_bot_of_commute hsK (not_comm_of_mulEquiv e₁) hc⟩

noncomputable def equivK₀ {T L V : Subgroup G} (hH : Hyp126 G T L V) {V₁ Vp H K : Subgroup G}
    (h918 : HypF918 T V L V₁ Vp H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    ↥(star H (conjClosure K T)) ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr (star_conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K)).trans
    ((equivProd (commute_pair h918 e₁ ht₀ ht₀K).1 (commute_pair h918 e₁ ht₀ ht₀K).2).trans
      (e₁.prodCongr (equivConjSub e₁ (h918.toHypF98.toHypF91.T_le_H ht₀))))

theorem inf_centralizer_eq_bot {T L V : Subgroup G} (hH : Hyp126 G T L V)
    {V₁ Vp H K : Subgroup G} (h918 : HypF918 T V L V₁ Vp H K)
    (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    star H (conjClosure K T) ⊓
      Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) = ⊥ := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  have := isSimpleGroup_alt5
  have hsK : IsSimpleGroup ↥(star H K) := e₁.isSimpleGroup
  have hsK₂ := isSimple_star_conjSub e₁ (hTH ht₀)
  obtain ⟨hc, -⟩ := commute_pair h918 e₁ ht₀ ht₀K
  have hsup := star_conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K
  rw [eq_bot_iff]
  rintro x ⟨hx, hxC⟩
  rw [hsup, ← L1233.range_mulHom _ _ hc] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  rw [L1233.mulHom_apply] at hxC ⊢
  have hcK : ∀ k ∈ star H K, (a : HStar H) * k = k * a := by
    intro k hk
    have h1 := Subgroup.mem_centralizer_iff.1 hxC k (hsup ▸ Subgroup.mem_sup_left hk)
    have h2 := hc k hk b b.2
    rw [← mul_assoc, mul_assoc (a : HStar H) (b : HStar H) k, ← h2, ← mul_assoc] at h1
    exact (mul_right_cancel h1).symm
  have hcK₂ : ∀ k ∈ star H (conjSub t₀ K), (b : HStar H) * k = k * b := by
    intro k hk
    have h1 := Subgroup.mem_centralizer_iff.1 hxC k (hsup ▸ Subgroup.mem_sup_right hk)
    have h2 := hc a a.2 k hk
    rw [← mul_assoc, ← h2, mul_assoc, mul_assoc (a : HStar H) (b : HStar H) k] at h1
    exact (mul_left_cancel h1).symm
  have ha : (a : HStar H) = 1 := by
    have h0 := inf_eq_bot_of_commute hsK (not_comm_of_mulEquiv e₁)
      (Y := Subgroup.zpowers (a : HStar H)) fun k hk y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((Commute.zpow_right (show Commute (k : HStar H) a from (hcK k hk).symm) n))
    have : (a : HStar H) ∈ star H K ⊓ Subgroup.zpowers (a : HStar H) :=
      ⟨a.2, Subgroup.mem_zpowers _⟩
    rw [h0] at this
    exact this
  have hb : (b : HStar H) = 1 := by
    have h0 := inf_eq_bot_of_commute hsK₂ (not_comm_of_mulEquiv (equivConjSub e₁ (hTH ht₀)))
      (Y := Subgroup.zpowers (b : HStar H)) fun k hk y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((Commute.zpow_right (show Commute (k : HStar H) b from (hcK₂ k hk).symm) n))
    have : (b : HStar H) ∈ star H (conjSub t₀ K) ⊓ Subgroup.zpowers (b : HStar H) :=
      ⟨b.2, Subgroup.mem_zpowers _⟩
    rw [h0] at this
    exact this
  rw [Subgroup.mem_bot, ha, hb, mul_one]

theorem centralizer_eq_bot (h1222 : Stmt12_2_2) {T L V : Subgroup G} [IsMulCommutative ↥V]
    (F : Frame126 T L V) (hH : Hyp126 G T L V) {H K : Subgroup G} (hHK : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5))
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) = ⊥ := by
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  set C := Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) with hCdef
  have hK₀n : (star H (conjClosure K T)).Normal := normal_star h918.K₀_normal
  have hCn : C.Normal := inferInstance
  have hCK : star H (conjClosure K T) ⊓ C = ⊥ := inf_centralizer_eq_bot hH h918 e₁ ht₀ ht₀K
  obtain ⟨hc, hi⟩ := commute_pair h918 e₁ ht₀ ht₀K
  have hsup := star_conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K
  obtain ⟨A, hAK, hA⟩ := exists_card_three e₁
  obtain ⟨B, hBK, hB⟩ := exists_card_three (equivConjSub e₁ (hTH ht₀))
  have hK₀H : conjClosure K T ≤ H := by
    rw [hHK.2.2]
    exact le_sup_left
  have hAK₀ : A ≤ star H (conjClosure K T) := hsup ▸ hAK.trans le_sup_left
  have hBK₀ : B ≤ star H (conjClosure K T) := hsup ▸ hBK.trans le_sup_right
  have hCp : IsPGroup 2 C := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card C) with ⟨k, hk⟩ |
        ⟨p, hp, hpd, hpo⟩
    · exact IsPGroup.of_card hk
    · exfalso
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨c, hc'⟩ := exists_prime_orderOf_dvd_card' p hpd
      have hcc : orderOf (c : HStar H) = p := by rw [Subgroup.orderOf_coe, hc']
      by_cases hp3 : p = 3
      · set D := Subgroup.zpowers (c : HStar H) with hD
        have hDc : Nat.card D = 3 := by rw [hD, Nat.card_zpowers, hcc, hp3]
        have hDC : D ≤ C := (Subgroup.zpowers_le).2 c.2
        have hXD : ∀ {X : Subgroup (HStar H)}, X ≤ star H (conjClosure K T) →
            X ≤ Subgroup.centralizer (D : Set (HStar H)) := fun hX x hx =>
          Subgroup.mem_centralizer_iff.2 fun d hd =>
            (Subgroup.mem_centralizer_iff.1 (hDC hd) x (hX hx)).symm
        refine false_of_three hH (pCoreOf_ne_bot h) hA hB hDc ?_ (hXD hAK₀) (hXD hBK₀)
          (le_bot_iff.1 (hi ▸ inf_le_inf hAK hBK))
          (le_bot_iff.1 (hCK ▸ inf_le_inf (sup_le hAK₀ hBK₀) hDC))
        exact fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hc a (hAK ha) b (hBK hb)).symm
      · have hcop : Nat.Coprime p 6 := by
          rw [Nat.Prime.coprime_iff_not_dvd hp]
          intro h6
          rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from h6) with h2 | h2
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
            rw [this] at hpo
            exact absurd hpo (by decide)
          · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h2)
        have hc1 : (c : HStar H) ^ p = 1 := by rw [← hcc, pow_orderOf_eq_one]
        have hcK := mem_star_of_coprime h1222 F hH h.T_normalizes_V₁ hK₀H h918.K₀_normal
          h.L₁T_le_H hHK.2.2 hc1 hcop
        have hmem : (c : HStar H) ∈ star H (conjClosure K T) ⊓ C := ⟨hcK, c.2⟩
        rw [hCK] at hmem
        have hc1' : c = 1 := Subtype.ext hmem
        rw [hc1', orderOf_one] at hc'
        exact hp.one_lt.ne hc'
  exact eq_bot_of_isPGroup hCn hCp

end Pair

section BorelA5

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem card_of_alt5 {X : Subgroup Q} (e : ↥X ≃* alternatingGroup (Fin 5)) : Nat.card X = 60 :=
  (Nat.card_congr e.toEquiv).trans S152X.card_A5G

theorem card_sylow_of_alt5 {X S : Subgroup Q} (e : ↥X ≃* alternatingGroup (Fin 5))
    (hS : QuasithinUnique.IsSylowTwoOf S X) : Nat.card S = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 ↥(S.subgroupOf X) := hS.2.1.comap_subtype
  have h := (hS'.toSylow hS.2.2).card_eq_multiplicity
  rw [show Nat.card X = Nat.card S152X.A5G from (card_of_alt5 e).trans S152X.card_A5G.symm,
    S152X.factorization_sixty] at h
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv]
  exact h

theorem card_inf_normalizer {X S : Subgroup Q} (e : ↥X ≃* alternatingGroup (Fin 5))
    (hS : QuasithinUnique.IsSylowTwoOf S X) :
    Nat.card ↥(X ⊓ Subgroup.normalizer (S : Set Q)) = 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 ↥(S.subgroupOf X) := hS.2.1.comap_subtype
  have hker : IsPGroup 2 ↥(e.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact IsPGroup.of_bot
  have h3 := S152X.relIndex_normalizer_of_surj e.toMonoidHom e.surjective hker hS' hS.2.2
  rw [← Subgroup.subgroupOf_normalizer_eq hS.1,
    ← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (S : Set Q)) X,
    Subgroup.relIndex_subgroupOf inf_le_right] at h3
  have h4 := Subgroup.relIndex_mul_card (H := S) (K := Subgroup.normalizer (S : Set Q) ⊓ X)
  have hSN : S ⊓ (Subgroup.normalizer (S : Set Q) ⊓ X) = S :=
    inf_of_le_left (le_inf Subgroup.le_normalizer hS.1)
  rw [hSN, h3, card_sylow_of_alt5 e hS, inf_comm] at h4
  omega

theorem eq_or_eq_of_le_normalizer {X S Z : Subgroup Q} (e : ↥X ≃* alternatingGroup (Fin 5))
    (hS : QuasithinUnique.IsSylowTwoOf S X) (h1 : X ⊓ Subgroup.normalizer (S : Set Q) ≤ Z)
    (h2 : Z ≤ X) : Z = X ⊓ Subgroup.normalizer (S : Set Q) ∨ Z = X := by
  have hd1 : 12 ∣ Nat.card Z := card_inf_normalizer e hS ▸ Subgroup.card_dvd_of_le h1
  have hd2 : Nat.card Z ∣ 60 := card_of_alt5 e ▸ Subgroup.card_dvd_of_le h2
  obtain ⟨k, hk⟩ := hd1
  have hk5 : k ∣ 5 := by
    rw [hk] at hd2
    have h60 : 12 * k ∣ 12 * 5 := by simpa using hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h60
  rcases (Nat.dvd_prime (by norm_num)).1 hk5 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_inf_normalizer e hS, hk])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [card_of_alt5 e, hk])

omit [Finite Q] in
theorem mem_of_mul_mem {X Y P B₁ : Subgroup Q} (hX : IsSimpleGroup ↥X)
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hB₁X : B₁ ≤ X) (hB₁P : B₁ ≤ P)
    (hmax : ∀ Z : Subgroup Q, B₁ ≤ Z → Z ≤ X → Z = B₁ ∨ Z = X) (hB₁ : B₁ ≠ ⊥) (hXP : ¬ X ≤ P)
    {a b : Q} (ha : a ∈ X) (hb : b ∈ Y) (hab : a * b ∈ P) : a ∈ B₁ := by
  by_contra haB
  set N' := X ⊓ Subgroup.normalizer ((P ⊓ X : Subgroup Q) : Set Q) with hN'
  have hBN : B₁ ≤ N' := le_inf hB₁X fun x hx => by
    have hx' : x ∈ P ⊓ X := ⟨hB₁P hx, hB₁X hx⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' hy) (Subgroup.inv_mem _ hx')
    · intro hy
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx') hy) hx'
      simpa [mul_assoc] using this
  have haN : a ∈ N' := by
    refine ⟨ha, Subgroup.mem_normalizer_iff.2 fun x => ?_⟩
    have hbx : ∀ x ∈ X, b * x = x * b := fun x hx => (hc x hx b hb).symm
    constructor
    · rintro ⟨hxP, hxX⟩
      have e1 : a * x * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by
        rw [mul_inv_rev, mul_assoc a b x, hbx x hxX]
        group
      refine ⟨?_, X.mul_mem (X.mul_mem ha hxX) (X.inv_mem ha)⟩
      rw [e1]
      exact P.mul_mem (P.mul_mem hab hxP) (P.inv_mem hab)
    · rintro ⟨hxP, hxX⟩
      have hxX' : x ∈ X := by
        have := X.mul_mem (X.mul_mem (X.inv_mem ha) hxX) ha
        simpa [mul_assoc] using this
      have e1 : x = (a * b)⁻¹ * (a * x * a⁻¹) * (a * b) := by
        have h2 := hbx x hxX'
        calc x = b⁻¹ * (b * x) := by group
          _ = b⁻¹ * (x * b) := by rw [h2]
          _ = (a * b)⁻¹ * (a * x * a⁻¹) * (a * b) := by group
      refine ⟨?_, hxX'⟩
      rw [e1]
      exact P.mul_mem (P.mul_mem (P.inv_mem hab) hxP) hab
  rcases hmax N' hBN inf_le_left with h | h
  · exact haB (h ▸ haN)
  ·
    have hXN : X ≤ Subgroup.normalizer ((P ⊓ X : Subgroup Q) : Set Q) := fun x hx => by
      have hxN : x ∈ N' := by rw [h]; exact hx
      exact hxN.2
    have hn : ((P ⊓ X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hXN
    rcases hn.eq_bot_or_eq_top with hb' | ht
    · apply hB₁
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hB₁X hx⟩ : ↥X) ∈ (P ⊓ X).subgroupOf X := ⟨hB₁P hx, hB₁X hx⟩
      rw [hb'] at this
      have := congrArg Subtype.val ((Subgroup.mem_bot).1 this)
      exact (Subgroup.mem_bot).2 this
    · apply hXP
      intro x hx
      have : (⟨x, hx⟩ : ↥X) ∈ (P ⊓ X).subgroupOf X := ht ▸ Subgroup.mem_top _
      exact this.1

end BorelA5

end CFSG.Quasithin.H13.S126P31
