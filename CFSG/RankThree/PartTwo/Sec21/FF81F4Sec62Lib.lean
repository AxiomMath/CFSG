module

import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.LocalAnalysis.StandardType.GGSixFusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G]

section Sylow

variable {p : ℕ} [hp : Fact p.Prime] {P H : Subgroup G}

theorem isSylowOf_iff : IsSylowOf p P H ↔ P ≤ H ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex H := by
  unfold IsSylowOf
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]

theorem exists_sylow_of_isSylowOf (h : IsSylowOf p P H) :
    ∃ Q : Sylow p H, (Q : Subgroup H).map H.subtype = P := by
  obtain ⟨hPH, hP, hco⟩ := h
  exact ⟨IsPGroup.toSylow hP.comap_subtype ((Nat.Prime.coprime_iff_not_dvd hp.out).mp hco),
    Subgroup.map_subgroupOf_eq_of_le hPH⟩

theorem isSylowOf_map_sylow (Q : Sylow p H) : IsSylowOf p ((Q : Subgroup H).map H.subtype) H :=
  ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, by
    show Nat.Coprime p ((((Q : Subgroup H).map H.subtype).subgroupOf H).index)
    rw [show ((Q : Subgroup H).map H.subtype).subgroupOf H = Q from
      Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr Q.not_dvd_index⟩

theorem card_eq_of_isSylowOf {k m : ℕ} (h : IsSylowOf p P H) (hH : Nat.card H = p ^ k * m)
    (hm : ¬ p ∣ m) : Nat.card P = p ^ k := by
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowOf h
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  rw [Subgroup.card_map_of_injective H.subtype_injective, Q.card_eq_multiplicity, hH,
    Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem isSylowOf_of_card {k m : ℕ} (hPH : P ≤ H) (hP : IsPGroup p P)
    (hPc : Nat.card P = p ^ k) (hH : Nat.card H = p ^ k * m) (hm : ¬ p ∣ m) :
    IsSylowOf p P H := by
  refine isSylowOf_iff.mpr ⟨hPH, hP, ?_⟩
  have e := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hPH, hPc, hH] at e
  have : P.relIndex H = m :=
    Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos k) (by rw [mul_comm, e])
  rwa [this]

theorem exists_conj_le_of_isSylowOf {A : Subgroup G} (h : IsSylowOf p P H) (hAH : A ≤ H)
    (hA : IsPGroup p A) : ∃ c ∈ H, conjBy c A ≤ P := by
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowOf h
  exact exists_conjBy_le_sylow hAH hA Q

theorem card_le_of_isSylowOf {A : Subgroup G} (h : IsSylowOf p P H) (hAH : A ≤ H)
    (hA : IsPGroup p A) : Nat.card A ≤ Nat.card P := by
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf h hAH hA
  calc Nat.card A = Nat.card (conjBy c A) := (card_conjBy c A).symm
    _ ≤ Nat.card P := Subgroup.card_le_of_le hc

theorem exists_conj_eq_of_isSylowOf {P₂ : Subgroup G} (h : IsSylowOf p P H)
    (h₂ : IsSylowOf p P₂ H) : ∃ c ∈ H, conjBy c P = P₂ := by
  obtain ⟨c, hc, hle⟩ := exists_conj_le_of_isSylowOf h₂ h.1 h.2.1
  exact ⟨c, hc, Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_conjBy]; exact card_le_of_isSylowOf h h₂.1 h₂.2.1)⟩

theorem exists_sylow_top_of_isSylowOf (h : IsSylowOf p P H) (hN : Nor P ≤ H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = P := by
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowOf h
  exact CFSG.StandardType.exists_sylow_eq_map_of_normalizer_le Q hN

theorem exists_conj_eq_of_sylow {S A : Subgroup G} (hS : ∃ Q : Sylow p G, (Q : Subgroup G) = S)
    (hA : IsPGroup p A) (hle : Nat.card S ≤ Nat.card A) : ∃ g : G, conjBy g S = A := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨Q', hQ'⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  have hconj : conjBy g (Q : Subgroup G) = (Q' : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, ?_⟩
  have h1 : A = (Q' : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ' (by rw [← hconj, card_conjBy]; exact hle)
  rw [h1, hconj]

end Sylow

theorem card_mul_le_card_sup {A B : Subgroup G} (h : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  have hinj : Function.Injective (fun p : A × B => (⟨(p.1 : G) * p.2,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
        ↥(A ⊔ B))) := by
    rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ ⟨⟨a', ha'⟩, ⟨c', hc'⟩⟩ he
    have he' : a * c = a' * c' := congrArg Subtype.val he
    have h1 : a'⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
      have : a'⁻¹ * a = c' * c⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
          _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [he']
          _ = c' * c⁻¹ := by group
      rw [this]
      exact B.mul_mem hc' (B.inv_mem hc)
    rw [h, Subgroup.mem_bot] at h1
    have ha1 : a = a' := by
      have := congrArg (a' * ·) h1
      simpa using this
    subst ha1
    have : c = c' := mul_left_cancel he'
    subst this
    rfl
  calc Nat.card A * Nat.card B = Nat.card (A × B) := (Nat.card_prod A B).symm
    _ ≤ Nat.card ↥(A ⊔ B) := Nat.card_le_card_of_injective _ hinj

section Z4

theorem z4_conjMem {G : Type} [Group G] {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) {z : G} (hz : z ∈ Z) :
    g * z * g⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp hg z).1 hz

def z4_conjZ {G : Type} [Group G] {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) : Equiv.Perm Z where
  toFun z := ⟨g * (z : G) * g⁻¹, z4_conjMem hg z.2⟩
  invFun z := ⟨g⁻¹ * (z : G) * g⁻¹⁻¹, z4_conjMem (inv_mem hg) z.2⟩
  left_inv z := Subtype.ext (by simp [mul_assoc])
  right_inv z := Subtype.ext (by simp [mul_assoc])

theorem z4_conjZ_one {G : Type} [Group G] {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) : z4_conjZ hg 1 = 1 :=
  Subtype.ext (by simp [z4_conjZ])

theorem z4_conjZ_ne_one_iff {G : Type} [Group G] {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) (a : Z) :
    a ≠ 1 ↔ z4_conjZ hg a ≠ 1 := by
  have h1 := z4_conjZ_one hg
  constructor
  · intro ha h
    apply ha
    apply (z4_conjZ hg).injective
    rw [h, h1]
  · intro ha h
    apply ha
    rw [h, h1]

def z4_conjNonOne {G : Type} [Group G] {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) : Equiv.Perm {z : Z // z ≠ 1} :=
  (z4_conjZ hg).subtypeEquiv fun a => z4_conjZ_ne_one_iff hg a

theorem z4_conjZ_mul {G : Type} [Group G] {Z : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G))
    (hh : h ∈ Subgroup.normalizer (Z : Set G)) (z : Z) :
    z4_conjZ (mul_mem hg hh) z = z4_conjZ hg (z4_conjZ hh z) :=
  Subtype.ext (by simp [z4_conjZ, mul_assoc])

def z4_conjRho {G : Type} [Group G] {Z P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (Z : Set G)) : P →* Equiv.Perm {z : Z // z ≠ 1} :=
  MonoidHom.mk' (fun p : P => z4_conjNonOne (hPN p.2)) (fun a b =>
    Equiv.ext fun z => Subtype.ext (z4_conjZ_mul (hPN a.2) (hPN b.2) z.1))

theorem z4_conjRho_eq_one_iff {G : Type} [Group G] {Z P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (Z : Set G)) (x : P) :
    z4_conjRho hPN x = 1 ↔ (x : G) ∈ Subgroup.centralizer (Z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  show z4_conjNonOne (hPN x.2) = 1 ↔ ∀ h ∈ (Z : Set G), h * (x : G) = (x : G) * h
  rw [Equiv.ext_iff]
  simp only [Equiv.Perm.one_apply]
  constructor
  · intro H h hh
    by_cases h1 : h = 1
    · subst h1
      simp
    · have H' := congrArg Subtype.val (H ⟨⟨h, hh⟩, fun e => h1 (congrArg Subtype.val e)⟩)
      have H'' : (x : G) * h * (x : G)⁻¹ = h := congrArg Subtype.val H'
      exact (mul_inv_eq_iff_eq_mul.mp H'').symm
  · intro H z
    apply Subtype.ext
    apply Subtype.ext
    show (x : G) * (z.1 : G) * (x : G)⁻¹ = (z.1 : G)
    exact mul_inv_eq_iff_eq_mul.mpr (H (z.1 : G) z.1.2).symm

theorem z4_ker_conjRho {G : Type} [Group G] {Z P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (Z : Set G)) :
    (z4_conjRho hPN).ker = (P ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf P := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp only [x.2, true_and]
  exact z4_conjRho_eq_one_iff hPN x

theorem z4_card_ker_conjRho {G : Type} [Group G] {Z P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card (z4_conjRho hPN).ker = Nat.card ↥(P ⊓ Subgroup.centralizer (Z : Set G)) := by
  rw [z4_ker_conjRho hPN]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem z4_natCard_nonOne {H : Type} [Group H] [Finite H] (hH : Nat.card H = 4) :
    Nat.card {z : H // z ≠ 1} = 3 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : H))
  rw [Finite.card_option, hH] at h
  omega

theorem card_le_two_mul_of_card_four {G : Type} [Group G] [Finite G] {Z P : Subgroup G}
    (hZ : Nat.card Z = 4) (hP : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card P ≤ 2 * Nat.card ↥(P ⊓ Subgroup.centralizer (Z : Set G)) := by
  have hW : Nat.card {z : Z // z ≠ 1} = 3 := z4_natCard_nonOne hZ
  have hdvd6 : (z4_conjRho hPN).ker.index ∣ 6 := by
    rw [Subgroup.index_ker]
    have h1 := Subgroup.card_subgroup_dvd_card (z4_conjRho hPN).range
    rw [Nat.card_perm, hW] at h1
    have h6 : Nat.factorial 3 = 6 := rfl
    rw [h6] at h1
    exact h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have hdvd2 : (z4_conjRho hPN).ker.index ∣ 2 ^ n := by
    rw [← hn]
    exact Dvd.intro_left _ (Subgroup.card_mul_index (z4_conjRho hPN).ker)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have hle : (z4_conjRho hPN).ker.index ≤ 2 := by
    rw [hk] at hdvd6 ⊢
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k <;> norm_num
    · exfalso
      have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hge
      have h46 : 2 ^ 2 ∣ 6 := dvd_trans h4 hdvd6
      norm_num at h46
  have hcard : Nat.card P = Nat.card ↥(z4_conjRho hPN).ker * (z4_conjRho hPN).ker.index :=
    (Subgroup.card_mul_index (z4_conjRho hPN).ker).symm
  rw [z4_card_ker_conjRho hPN] at hcard
  calc Nat.card P
      = Nat.card ↥(P ⊓ Subgroup.centralizer (Z : Set G)) * (z4_conjRho hPN).ker.index := hcard
    _ ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (Z : Set G)) * 2 := Nat.mul_le_mul_left _ hle
    _ = 2 * Nat.card ↥(P ⊓ Subgroup.centralizer (Z : Set G)) := Nat.mul_comm _ _


end Z4

section O13

theorem le_of_dvd_two_pow_sub {a c : ℕ} (hc : c < a) (h : 13 ∣ 2 ^ a - 2 ^ c) : c + 12 ≤ a := by
  obtain ⟨k, rfl⟩ : ∃ k, a = c + k := ⟨a - c, by omega⟩
  have hk : 1 ≤ k := by omega
  have hsub : 2 ^ (c + k) - 2 ^ c = 2 ^ c * (2 ^ k - 1) := by
    rw [Nat.mul_sub, mul_one, pow_add, mul_comm]
  rw [hsub] at h
  have hcop : Nat.Coprime 13 (2 ^ c) := Nat.Coprime.pow_right c (by norm_num)
  have h1 : 13 ∣ 2 ^ k - 1 := hcop.dvd_of_dvd_mul_left h
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hmod1 : 2 ^ k % 13 = 1 := by omega
  have h12 : ∀ q : ℕ, 2 ^ (12 * q) % 13 = 1 := by
    intro q
    induction q with
    | zero => norm_num
    | succ m ih =>
      rw [show 12 * (m + 1) = 12 * m + 12 by ring, pow_add, Nat.mul_mod, ih]
      all_goals norm_num
  have key : ∀ n : ℕ, 2 ^ n % 13 = 2 ^ (n % 12) % 13 := by
    intro n
    have hn : 2 ^ n = 2 ^ (12 * (n / 12)) * 2 ^ (n % 12) := by
      rw [← pow_add, Nat.div_add_mod]
    rw [hn, Nat.mul_mod, h12 (n / 12)]
    simp
  have hmod2 : 2 ^ (k % 12) % 13 = 1 := by
    rw [← key k]
    exact hmod1
  have hr : k % 12 = 0 := by
    have hlt : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r, k % 12 = r := ⟨_, rfl⟩
    rw [hr] at hlt hmod2 ⊢
    interval_cases r <;> first | rfl | norm_num at hmod2
  have h12k : 12 ∣ k := Nat.dvd_of_mod_eq_zero hr
  have hk12 : 12 ≤ k := Nat.le_of_dvd hk h12k
  omega

theorem two_pow_thirteen_le {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) {r τ : G} (hr : orderOf r = 13)
    (hrP : r ∈ Subgroup.normalizer (P : Set G)) (hτP : τ ∈ P) (hτ1 : τ ≠ 1)
    (hτr : r * τ = τ * r) (hnc : ¬ ∀ u ∈ P, r * u = u * r) :
    2 ^ 13 ≤ Nat.card P := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  haveI : Fintype P := Fintype.ofFinite P
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card P = 2 ^ a := (IsPGroup.iff_card).mp hP
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = P ⊓ Subgroup.centralizer {r} := ⟨_, rfl⟩
  have hQ : ∀ x : G, x ∈ Q ↔ x ∈ P ∧ r * x = x * r := by
    intro x
    rw [hQdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp
  have hQP : Q ≤ P := fun x hx => ((hQ x).mp hx).1
  have hcardQP : Nat.card Q ≤ Nat.card P := Subgroup.card_le_of_le hQP
  obtain ⟨c, hc, hQc⟩ : ∃ c, c ≤ a ∧ Nat.card Q = 2 ^ c := by
    have hdvd : Nat.card Q ∣ 2 ^ a := by
      rw [← ha]
      exact Subgroup.card_dvd_of_le hQP
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk, hk'⟩
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hQc
      have hQbot : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q hQc
      have hτQ : τ ∈ Q := (hQ τ).mpr ⟨hτP, hτr⟩
      rw [hQbot, Subgroup.mem_bot] at hτQ
      exact hτ1 hτQ
    · exact h0
  have hne : Nat.card Q ≠ Nat.card P := by
    intro heq
    apply hnc
    have hQeq : Q = P := Subgroup.eq_of_le_of_card_ge hQP heq.symm.le
    intro u hu
    have huQ : u ∈ Q := by
      rw [hQeq]
      exact hu
    exact ((hQ u).mp huQ).2
  have hca : c < a := by
    refine lt_of_le_of_ne hc (fun h => hne ?_)
    rw [hQc, ha, h]
  have hconj : ∀ u : P, r * (u : G) * r⁻¹ ∈ P := fun u =>
    (Subgroup.mem_normalizer_iff.mp hrP (u : G)).mp u.2
  obtain ⟨E, hE⟩ : ∃ E : Function.End P, ∀ u : P, ((E u : P) : G) = r * (u : G) * r⁻¹ :=
    ⟨fun u => ⟨r * (u : G) * r⁻¹, hconj u⟩, fun u => rfl⟩
  have hsucc : ∀ (m : ℕ) (u : P), (E ^ (m + 1)) u = (E ^ m) (E u) := fun m u => rfl
  have hfpow : ∀ (n : ℕ) (u : P),
      (((E ^ n) u : P) : G) = r ^ n * (u : G) * (r ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro u
      show (u : G) = r ^ 0 * (u : G) * (r ^ 0)⁻¹
      simp
    | succ m ih =>
      intro u
      rw [hsucc, ih, hE]
      group
  have hr13 : r ^ 13 = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr] at this
  have hf13 : E ^ 13 = 1 := by
    funext u
    apply Subtype.ext
    show (((E ^ 13) u : P) : G) = (u : G)
    rw [hfpow 13 u, hr13]
    simp
  have hf13' : E ^ 13 ^ 1 = 1 := by
    rw [Nat.pow_one]
    exact hf13
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf13'
  let F : P → P := E
  have hF : ∀ u : P, ((F u : P) : G) = r * (u : G) * r⁻¹ := hE
  have hmod' : Fintype.card P ≡ Fintype.card (Function.fixedPoints F) [MOD 13] := hmod
  have hFix : Nat.card (Function.fixedPoints F) = Nat.card Q := by
    have hToQ : ∀ x : Function.fixedPoints F, x.1.1 ∈ Q := by
      intro x
      have hx : F x.1 = x.1 := Function.mem_fixedPoints_iff.mp x.2
      have h1 : r * x.1.1 * r⁻¹ = x.1.1 := by
        have h2 := congrArg Subtype.val hx
        rw [hF] at h2
        exact h2
      exact (hQ _).mpr ⟨x.1.2, mul_inv_eq_iff_eq_mul.mp h1⟩
    have hPQ : ∀ y : Q, y.1 ∈ P := fun y => ((hQ y.1).mp y.2).1
    have hFromQ : ∀ y : Q, (⟨y.1, hPQ y⟩ : P) ∈ Function.fixedPoints F := by
      intro y
      rw [Function.mem_fixedPoints_iff]
      apply Subtype.ext
      rw [hF]
      exact mul_inv_eq_iff_eq_mul.mpr ((hQ y.1).mp y.2).2
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, hToQ x⟩
        invFun := fun y => ⟨⟨y.1, hPQ y⟩, hFromQ y⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFix] at hmod'
  have h13 : 13 ∣ Nat.card P - Nat.card Q := (Nat.modEq_iff_dvd' hcardQP).mp hmod'.symm
  rw [ha, hQc] at h13
  have hle := le_of_dvd_two_pow_sub hca h13
  rw [ha]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)


end O13

end CFSG.RankThree.PartTwo.Sec21.FF81.S6
