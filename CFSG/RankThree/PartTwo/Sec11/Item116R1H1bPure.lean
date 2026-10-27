module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Alg
public import CFSG.RankThree.PartTwo.Sec5.Bender.Core
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Comp
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.RankThree.PartOne.S10.FiveCriticalFrattini
public import CFSG.RankThree.PartTwo.Sec11.Item116TwoStarKF
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup
public import Certificates.Data.ExceptionalSL3

public section

section

namespace CFSG.RankThree.PartTwo.Sec11

section H1bAux

variable {Γ V : Type*} [Group Γ] [AddCommGroup V] [DistribMulAction Γ V]

def h1bW_cmW (c : Γ) : AddSubgroup V where
  carrier := {w | ∃ u : V, w = c • u - u}
  add_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
    exact ⟨u + u', by rw [smul_add]; abel⟩
  zero_mem' := ⟨0, by rw [smul_zero, sub_self]⟩
  neg_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨-u, by rw [smul_neg]; abel⟩

lemma h1bW_mem_cmW {c : Γ} {x : V} : x ∈ h1bW_cmW c ↔ ∃ u : V, x = c • u - u := Iff.rfl

lemma h1bW_cmW_smul_mem {c g : Γ} (hg : c * g = g * c) {x : V} (hx : x ∈ h1bW_cmW c) :
    g • x ∈ h1bW_cmW c := by
  obtain ⟨u, rfl⟩ := h1bW_mem_cmW.mp hx
  refine h1bW_mem_cmW.mpr ⟨g • u, ?_⟩
  rw [smul_sub, ← mul_smul g c u, ← hg, mul_smul c g u]

lemma h1bW_comm_of_mem_centralizer {c g : Γ} (hg : g ∈ Subgroup.centralizer ({c} : Set Γ)) :
    c * g = g * c :=
  Subgroup.mem_centralizer_iff.mp hg c (Set.mem_singleton c)

lemma h1bW_mem_centralizer {c g : Γ} (hg : c * g = g * c) :
    g ∈ Subgroup.centralizer ({c} : Set Γ) :=
  Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact hg

instance h1bW_act (c : Γ) :
    DistribMulAction (Subgroup.centralizer ({c} : Set Γ)) (h1bW_cmW (V := V) c) where
  smul g w := ⟨(g : Γ) • (w : V), h1bW_cmW_smul_mem (h1bW_comm_of_mem_centralizer g.2) w.2⟩
  one_smul w := Subtype.ext (by
    show ((1 : Subgroup.centralizer ({c} : Set Γ)) : Γ) • (w : V) = (w : V)
    rw [Subgroup.coe_one, one_smul])
  mul_smul g h w := Subtype.ext (by
    show ((g * h : Subgroup.centralizer ({c} : Set Γ)) : Γ) • (w : V)
      = (g : Γ) • (h : Γ) • (w : V)
    rw [Subgroup.coe_mul, mul_smul])
  smul_zero g := Subtype.ext (by
    show (g : Γ) • (0 : V) = 0
    exact smul_zero _)
  smul_add g x y := Subtype.ext (by
    show (g : Γ) • ((x : V) + (y : V)) = (g : Γ) • (x : V) + (g : Γ) • (y : V)
    exact smul_add _ _ _)

lemma h1bW_cmW_fixed_eq_zero [Finite V] (hV3 : ¬ 3 ∣ Nat.card V) {c : Γ} (hc3 : c ^ 3 = 1)
    {w : V} (hw : w ∈ h1bW_cmW (V := V) c) (hcw : c • w = w) : w = 0 := by
  have hA3 : ∀ x : V, c • (c • (c • x)) = x := by
    intro x
    calc c • (c • (c • x)) = (c * (c * c)) • x := by rw [mul_smul, mul_smul]
      _ = x := by rw [← pow_three c, hc3, one_smul]
  obtain ⟨u, hu⟩ := h1bW_mem_cmW.mp hw
  have hT : (c • u - u) + c • (c • u - u) + c • (c • (c • u - u)) = 0 := by
    simp only [smul_sub]
    rw [hA3 u]
    abel
  rw [← hu] at hT
  simp only [hcw] at hT
  have h3w : (3 : ℕ) • w = 0 := by
    rw [three'_nsmul]
    exact hT
  have hd3 : addOrderOf w ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero h3w
  have hdV : addOrderOf w ∣ Nat.card V := addOrderOf_dvd_natCard w
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
  · exact AddMonoid.addOrderOf_eq_one_iff.mp h1
  · rw [h3] at hdV
    exact absurd hdV hV3

lemma h1bW_cmW_delta_fixed_eq_zero [Finite V] (hV3 : ¬ 3 ∣ Nat.card V) {c δ : Γ}
    (hc3 : c ^ 3 = 1) (e : ℕ) (he : ¬ 3 ∣ e) (hδe : ∀ v : V, δ • v = c ^ e • v)
    {w : V} (hw : w ∈ h1bW_cmW (V := V) c) (hfix : δ • w = w) : w = 0 := by
  apply h1bW_cmW_fixed_eq_zero hV3 hc3 hw
  have hce : c ^ e • w = w := (hδe w).symm.trans hfix
  have hpow : c ^ e = c ^ (e % 3) := by
    conv_lhs => rw [← Nat.div_add_mod e 3]
    rw [pow_add, pow_mul, hc3, one_pow, one_mul]
  have hmod : e % 3 = 1 ∨ e % 3 = 2 := by omega
  rcases hmod with h | h
  · rw [hpow, h, pow_one] at hce
    exact hce
  · rw [hpow, h] at hce
    calc c • w = c • (c ^ 2 • w) := by rw [hce]
      _ = (c * c ^ 2) • w := by rw [mul_smul]
      _ = (c ^ 3) • w := by rw [show c * c ^ 2 = c ^ 3 from (pow_succ' c 2).symm]
      _ = w := by rw [hc3, one_smul]

end H1bAux

theorem h1b_module_core {Γ V : Type*} [Group Γ] [AddCommGroup V] [Finite V] [DistribMulAction Γ V]
    (hV3 : ¬ 3 ∣ Nat.card V) (c a z δ : Γ) (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) (hδ3 : δ ^ 3 = 1)
    (hca : c * a = a * c) (hcz : c * z = z * c) (hcδ : c * δ = δ * c)
    (haδ : a * δ = δ * a) (hzδ : z * δ = δ * z) (haz : a * z * a⁻¹ = z * δ)
    (hδc : ∃ e : ℕ, ¬ 3 ∣ e ∧ ∀ v : V, δ • v = c ^ e • v)
    (hC : ∀ v : V, a • v = v → c • v = v) : ∀ v : V, c • v = v := by
  intro v0
  by_contra hne
  obtain ⟨e, he, hδe⟩ := hδc
  have hW1 : (⟨c • v0 - v0, h1bW_mem_cmW.mpr ⟨v0, rfl⟩⟩ : h1bW_cmW (V := V) c) ≠ 0 := by
    intro h
    apply hne
    exact sub_eq_zero.mp (congrArg Subtype.val h)
  haveI : Nontrivial (h1bW_cmW (V := V) c) := ⟨⟨_, 0, hW1⟩⟩
  obtain ⟨aH, haH⟩ : ∃ g : Subgroup.centralizer ({c} : Set Γ), (g : Γ) = a :=
    ⟨⟨a, h1bW_mem_centralizer hca⟩, rfl⟩
  obtain ⟨zH, hzH⟩ : ∃ g : Subgroup.centralizer ({c} : Set Γ), (g : Γ) = z :=
    ⟨⟨z, h1bW_mem_centralizer hcz⟩, rfl⟩
  obtain ⟨δH, hδH⟩ : ∃ g : Subgroup.centralizer ({c} : Set Γ), (g : Γ) = δ :=
    ⟨⟨δ, h1bW_mem_centralizer hcδ⟩, rfl⟩
  have hH_a3 : aH ^ 3 = 1 :=
    Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, haH]; exact ha3)
  have hH_δ3 : δH ^ 3 = 1 :=
    Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, hδH]; exact hδ3)
  have hH_aδ : aH * δH = δH * aH :=
    Subtype.ext (by simp only [Subgroup.coe_mul, haH, hδH]; exact haδ)
  have hH_zδ : zH * δH = δH * zH :=
    Subtype.ext (by simp only [Subgroup.coe_mul, hzH, hδH]; exact hzδ)
  have hH_az : aH * zH * aH⁻¹ = zH * δH :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, haH, hzH, hδH]; exact haz)
  have hfree : ∀ v : h1bW_cmW (V := V) c, δH • v = v → v = 0 := by
    intro v hv
    have hv' : δ • (v : V) = (v : V) := by
      have h := congrArg Subtype.val hv
      rw [← hδH]
      exact h
    exact Subtype.ext (h1bW_cmW_delta_fixed_eq_zero hV3 hc3 e he hδe v.2 hv')
  obtain ⟨w, hw0, hwa⟩ := exists_fixed_of_modular aH zH δH hH_a3 hH_δ3 hH_aδ hH_zδ hH_az hfree
  have hwa' : a • (w : V) = (w : V) := by
    have h := congrArg Subtype.val hwa
    rw [← haH]
    exact h
  have hcw : c • (w : V) = (w : V) := hC (w : V) hwa'
  exact hw0 (Subtype.ext (h1bW_cmW_fixed_eq_zero hV3 hc3 w.2 hcw))

end CFSG.RankThree.PartTwo.Sec11

end

section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

open scoped commutatorElement

theorem h1b_s4_comm_mul {G : Type*} [Group G] (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem h1b_s4_conj_comm {G : Type*} [Group G] (a b c : G) (hb : b * c * b⁻¹ = c) :
    b * ⁅a, c⁆ * b⁻¹ = ⁅b * a * b⁻¹, c⁆ := by
  have hb' : b * c⁻¹ * b⁻¹ = c⁻¹ := by
    rw [show b * c⁻¹ * b⁻¹ = (b * c * b⁻¹)⁻¹ by group, hb]
  simp only [commutatorElement_def]
  calc b * (a * c * a⁻¹ * c⁻¹) * b⁻¹
      = (b * a * b⁻¹) * (b * c * b⁻¹) * (b * a⁻¹ * b⁻¹) * (b * c⁻¹ * b⁻¹) := by group
    _ = (b * a * b⁻¹) * c * (b * a * b⁻¹)⁻¹ * c⁻¹ := by
      rw [hb, hb']
      group

theorem h1b_s4_comm_pow {G : Type*} [Group G] {c : G} (A T : Subgroup G)
    (hA : ∀ a ∈ A, c * a * c⁻¹ ∈ A) (hT : ∀ a ∈ A, ⁅a, c⁆ ∈ T) :
    ∀ n : ℕ, ∀ a ∈ A, ⁅a, c ^ n⁆ ∈ T := by
  have hinv : ∀ n : ℕ, ∀ a ∈ A, c ^ n * a * (c ^ n)⁻¹ ∈ A := by
    intro n
    induction n with
    | zero =>
      intro a ha
      simpa using ha
    | succ n ih =>
      intro a ha
      have e : c ^ (n + 1) * a * (c ^ (n + 1))⁻¹ = c * (c ^ n * a * (c ^ n)⁻¹) * c⁻¹ := by
        rw [pow_succ']
        generalize c ^ n = b
        group
      rw [e]
      exact hA _ (ih a ha)
  intro n
  induction n with
  | zero =>
    intro a _
    simp
  | succ n ih =>
    intro a ha
    have hcomm : c ^ n * c * (c ^ n)⁻¹ = c := by
      rw [((Commute.refl c).pow_left n).eq]
      exact mul_inv_cancel_right _ _
    rw [pow_succ, h1b_s4_comm_mul, h1b_s4_conj_comm a (c ^ n) c hcomm]
    exact T.mul_mem (ih a ha) (hT _ (hinv n a ha))

theorem h1b_s4_zpowers_nat {G : Type*} [Group G] {c : G} (hc3 : c ^ 3 = 1) :
    ∀ γ ∈ Subgroup.zpowers c, ∃ n : ℕ, c ^ n = γ := by
  intro γ hγ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
  have h3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  have hk : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  refine ⟨(k % 3).toNat, ?_⟩
  rw [zpow_eq_zpow_emod k h3, ← zpow_natCast, Int.toNat_of_nonneg hk]

theorem h1b_step4_pure {G : Type*} [Group G] [Finite G] {c : G} (hc3 : c ^ 3 = 1)
    (θa U X : Subgroup G) (hU2 : IsPGroup 2 U) {q : ℕ} (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hq : q.Prime) (hq3 : q ≠ 3) (hcX : c ∈ Subgroup.normalizer (X : Set G))
    (hXθ : ∀ x ∈ X, x * c * x⁻¹ * c⁻¹ ∈ θa)
    (hθU : ∀ t ∈ θa, t * c * t⁻¹ * c⁻¹ ∈ U) :
    ∀ x ∈ X, x * c = c * x := by
  have hXc : ∀ a ∈ X, c * a * c⁻¹ ∈ X := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hcX a).mp ha
  have hCX : Subgroup.zpowers c ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr hcX
  have hH1 : ⁅X, Subgroup.zpowers c⁆ ≤ θa := by
    rw [Subgroup.commutator_le]
    intro x hx γ hγ
    obtain ⟨n, rfl⟩ := h1b_s4_zpowers_nat hc3 γ hγ
    exact h1b_s4_comm_pow X θa hXc (fun a ha => hXθ a ha) n x hx
  have hHc : ∀ h ∈ ⁅X, Subgroup.zpowers c⁆, c * h * c⁻¹ ∈ ⁅X, Subgroup.zpowers c⁆ := by
    have hle : ⁅X, Subgroup.zpowers c⁆ ≤
        (⁅X, Subgroup.zpowers c⁆).comap (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro x hx γ hγ
      obtain ⟨n, rfl⟩ := h1b_s4_zpowers_nat hc3 γ hγ
      have hconj : c * c ^ n * c⁻¹ = c ^ n := by
        rw [((Commute.refl c).pow_right n).eq]
        exact mul_inv_cancel_right _ _
      rw [Subgroup.mem_comap]
      show c * ⁅x, c ^ n⁆ * c⁻¹ ∈ ⁅X, Subgroup.zpowers c⁆
      rw [h1b_s4_conj_comm x c (c ^ n) hconj]
      exact Subgroup.commutator_mem_commutator (hXc x hx)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) n)
    intro h hh
    exact Subgroup.mem_comap.mp (hle hh)
  have hH2 : ⁅⁅X, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro h hh γ hγ
    obtain ⟨n, rfl⟩ := h1b_s4_zpowers_nat hc3 γ hγ
    exact h1b_s4_comm_pow ⁅X, Subgroup.zpowers c⁆ U hHc (fun a ha => hθU a (hH1 ha)) n h hh
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card X) := by
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    have hdvd : Nat.card (Subgroup.zpowers c) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hc3
    rw [hk]
    exact Nat.Coprime.coprime_dvd_left hdvd
      (Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm hq3)))
  have hBen : ⁅X, Subgroup.zpowers c⁆ ≤ ⁅⁅X, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ :=
    CFSG.RankThree.PartTwo.Sec5.Bender.commutator_le_commutator_commutator X
      (Subgroup.zpowers c) hCX hcop
  have hXU : ∀ g ∈ X, g ∈ U → g = 1 := by
    intro g hgX hgU
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨a, ha⟩ := hX ⟨g, hgX⟩
    obtain ⟨b, hb⟩ := hU2 ⟨g, hgU⟩
    have ha' : g ^ q ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hb' : g ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hcop' : Nat.Coprime (q ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    have hg := pow_gcd_eq_one.mpr ⟨ha', hb'⟩
    rw [Nat.Coprime.gcd_eq_one hcop', pow_one] at hg
    exact hg
  intro x hx
  have hxX : ⁅x, c⁆ ∈ X := by
    have e : ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact X.mul_mem hx (hXc _ (X.inv_mem hx))
  have hxU : ⁅x, c⁆ ∈ U :=
    hH2 (hBen (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers c)))
  have h1 : ⁅x, c⁆ = 1 := hXU _ hxX hxU
  rw [commutatorElement_def] at h1
  calc x * c = x * c * x⁻¹ * c⁻¹ * (c * x) := by group
    _ = c * x := by rw [h1, one_mul]

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem compJ3_conj_mem_three_free {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hZ : Subgroup.center K = ⊥) {y x : X} (hy : y ∈ K)
    (hy3 : orderOf y = 3) (h2 : ¬ 3 ∣ orderOf (x * y * x⁻¹ * y⁻¹)) :
    x * y * x⁻¹ ∈ K := by
  have hK' : CFSG.IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
  have hy' : x * y * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
  by_contra hyK
  have hKK' : K ≠ K.map (MulAut.conj x).toMonoidHom := by
    intro h
    apply hyK
    rw [h]
    exact hy'
  have hbot : ⁅K, K.map (MulAut.conj x).toMonoidHom⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hKK'
  have hcomm : Commute (x * y * x⁻¹) y :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hy) (x * y * x⁻¹) hy'
  have hy3pow : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hyne : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy3
    omega
  have hyy' : x * y * x⁻¹ ≠ y := by
    intro h
    have hyI : y ∈ K ⊓ K.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨hy, by rw [← h]; exact hy'⟩
    rw [compJ3_inf_eq_bot hK hK' hKK' hZ, Subgroup.mem_bot] at hyI
    exact hyne hyI
  have he1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h => hyy' (mul_inv_eq_one.mp h)
  have hy3' : (x * y * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3pow, mul_one, mul_inv_cancel]
  have he3 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := by
    rw [hcomm.inv_right.mul_pow 3, hy3', inv_pow, hy3pow, inv_one, one_mul]
  have hdvd : orderOf (x * y * x⁻¹ * y⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one he3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact he1 (orderOf_eq_one_iff.mp h1)
  · exact h2 (h1 ▸ dvd_refl _)

theorem compJ3_fix_of_mem_three_free {X : Type*} [Group X] [Finite X]
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥) {c d : X} (hd : d ∈ K₁)
    (hc : c ∈ K₂) (hd3 : orderOf d = 3) (hc3 : orderOf c = 3) (P : Subgroup X)
    (hP3 : ∀ y ∈ P, ¬ 3 ∣ orderOf y)
    (hPc : ∀ y ∈ P, c * y * c⁻¹ ∈ P) (hPd : ∀ y ∈ P, d * y * d⁻¹ ∈ P)
    {x : X} (hx : x ∈ P) (hxcd : x * (c * d) = c * d * x) :
    x ∈ Subgroup.centralizer ({c} : Set X) ⊓ Subgroup.centralizer ({d} : Set X) := by
  have hmd : x * d * x⁻¹ * d⁻¹ ∈ P := by
    rw [show x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) by simp only [mul_assoc]]
    exact P.mul_mem hx (hPd x⁻¹ (P.inv_mem hx))
  have hmc : x * c * x⁻¹ * c⁻¹ ∈ P := by
    rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by simp only [mul_assoc]]
    exact P.mul_mem hx (hPc x⁻¹ (P.inv_mem hx))
  have hdx : x * d * x⁻¹ ∈ K₁ := compJ3_conj_mem_three_free h1 hZ1 hd hd3 (hP3 _ hmd)
  have hcx : x * c * x⁻¹ ∈ K₂ := compJ3_conj_mem_three_free h2 hZ2 hc hc3 (hP3 _ hmc)
  have hmul : (x * c * x⁻¹) * (x * d * x⁻¹) = c * d := by
    calc (x * c * x⁻¹) * (x * d * x⁻¹) = x * (c * d) * x⁻¹ := by group
      _ = c * d * x * x⁻¹ := by rw [hxcd]
      _ = c * d := by group
  have hu : (x * c * x⁻¹)⁻¹ * c = (x * d * x⁻¹) * d⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hmul, mul_inv_cancel_right]
  have hu1 : (x * c * x⁻¹)⁻¹ * c ∈ K₂ := K₂.mul_mem (K₂.inv_mem hcx) hc
  have hu2 : (x * c * x⁻¹)⁻¹ * c ∈ K₁ := by
    rw [hu]
    exact K₁.mul_mem hdx (K₁.inv_mem hd)
  have hu0 : (x * c * x⁻¹)⁻¹ * c ∈ K₁ ⊓ K₂ := Subgroup.mem_inf.mpr ⟨hu2, hu1⟩
  rw [compJ3_inf_eq_bot h1 h2 hne hZ1, Subgroup.mem_bot] at hu0
  have hcfix : x * c * x⁻¹ = c := inv_mul_eq_one.mp hu0
  have hdfix : x * d * x⁻¹ = d := mul_inv_eq_one.mp (hu.symm.trans hu0)
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [hcfix]
  · calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [hdfix]

theorem three_free_normal_le_centralizer_pair {X : Type*} [Group X] [Finite X]
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥) {c d : X} (hd : d ∈ K₁)
    (hc : c ∈ K₂) (hd3 : orderOf d = 3) (hc3 : orderOf c = 3) (N : Subgroup X)
    (hN3 : ∀ y ∈ N, ¬ 3 ∣ orderOf y) (hNC : N ≤ Subgroup.centralizer ({c * d} : Set X))
    (hNn : ∀ g ∈ Subgroup.centralizer ({c * d} : Set X), ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    N ≤ Subgroup.centralizer ({c} : Set X) ⊓ Subgroup.centralizer ({d} : Set X) := by
  have hbot : ⁅K₁, K₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h1 h2).resolve_left hne
  have hcd : c * d = d * c :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hd) c hc
  have hdC : d ∈ Subgroup.centralizer ({c * d} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← mul_assoc, ← hcd])
  have hcC : c ∈ Subgroup.centralizer ({c * d} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [mul_assoc, ← hcd])
  intro x hx
  exact compJ3_fix_of_mem_three_free h1 h2 hne hZ1 hZ2 hd hc hd3 hc3 N hN3
    (fun y hy => hNn c hcC y hy)
    (fun y hy => hNn d hdC y hy)
    hx
    (Subgroup.mem_centralizer_singleton_iff.mp (hNC hx))

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_critical_subgroup_fix_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) (hPne : P ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ P ∧ normalizer (P : Set G) ≤ normalizer (D : Set G) ∧
      (∀ d ∈ D, d ^ p = 1) ∧ (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      (∀ u ∈ normalizer (P : Set G), ∀ m : ℕ, Nat.Coprime p m → u ^ m = 1 →
        u ∈ centralizer (D : Set G) → u ∈ centralizer (P : Set G)) := by
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  obtain ⟨D', hD'char, -, hD'comm, hD'exp, hD'fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  refine ⟨D'.map P.subtype, map_subtype_le D', ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply CFSG.RankThree.PartTwo.Sec3.mem_normalizer_of_forall_conj_mem
    rintro _ ⟨d, hd, rfl⟩
    have h := Subgroup.characteristic_iff_map_eq.mp hD'char (P.normalizerMonoidHom ⟨g, hg⟩)
    have hσd : P.normalizerMonoidHom ⟨g, hg⟩ d ∈ D' := by
      rw [← h]
      exact mem_map_of_mem _ hd
    exact ⟨_, hσd, normalizerMonoidHom_apply_apply_coe _ _ _⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hD'exp d hd, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    have h := hD'comm (commutator_mem_commutator ha (mem_top b))
    have h2 := mem_centralizer_iff.mp h.2 c hc
    have h3 : ((c * ⁅a, b⁆ : P) : G) = ((⁅a, b⁆ * c : P) : G) := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h3
    simp only [Subgroup.coe_subtype, commutatorElement_def]
    exact h3.symm
  · intro u hu m hcopm hum huc
    have hσfix : P.normalizerMonoidHom ⟨u, hu⟩ ∈ fixingSubgroup (MulAut P) (D' : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      apply Subtype.ext
      change ((P.normalizerMonoidHom ⟨u, hu⟩ y : P) : G) = y
      rw [normalizerMonoidHom_apply_apply_coe]
      have := mem_centralizer_iff.mp huc (y : G) ⟨y, hy, rfl⟩
      rw [← this, mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := hD'fix ⟨_, hσfix⟩
    have hσk : P.normalizerMonoidHom ⟨u, hu⟩ ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hσm : P.normalizerMonoidHom ⟨u, hu⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨u, hu⟩ : normalizer (P : Set G)) ^ m = 1 := by
        apply Subtype.ext
        simpa using hum
      rw [this, map_one]
    have hdvd : orderOf (P.normalizerMonoidHom ⟨u, hu⟩) ∣ Nat.gcd (p ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσm)
    have hcop : Nat.Coprime (p ^ k) m := Nat.Coprime.pow_left k hcopm
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    rw [mem_centralizer_iff]
    intro g hg
    have := congrArg (fun τ : MulAut P => ((τ ⟨g, hg⟩ : P) : G)) hdvd
    simp only [MulAut.one_apply] at this
    rw [normalizerMonoidHom_apply_apply_coe, mul_inv_eq_iff_eq_mul] at this
    exact this.symm

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_fixed_lift_prime {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P]
    {L : Type*} [Group L] [IsElementaryAbelian q (P ⧸ frattini P)] (hP : IsPGroup q P)
    {r : ℕ} (hr : r.Prime) (hrq : r ≠ q) (ρ : L →* MulAut P) (l : L)
    (hl : IsPGroup r (Subgroup.zpowers (ρ l))) (v : Additive (P ⧸ frattini P))
    (hv : v ∈ Module.End.eigenspace
      (CFSG.RankThree.PartOne.FixedRank36.frattiniRep q ρ l) 1) :
    ∃ x : P, ρ l x = x ∧ Additive.ofMul (x : P ⧸ frattini P) = v := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  set Z := Subgroup.zpowers (ρ l) with hZ
  let α : Z →* MulAut P := Z.subtype
  have hN : ∀ b : Z, ∀ n ∈ frattini P, α b n ∈ frattini P := by
    intro b n hn
    have h := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (frattini P).Characteristic) (α b)
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hn
  have hcop : ¬ r ∣ Nat.card (frattini P) := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup (frattini P)).exists_card_eq
    rw [hk]
    intro h
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq.out).mp (hr.dvd_of_dvd_pow h))
  have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting r hl α (frattini P) hN hcop
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hvx : v = Additive.ofMul (x : P ⧸ frattini P) := by rw [hx]; rfl
  rw [Module.End.mem_eigenspace_iff, one_smul] at hv
  have hfixa : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN
      ⟨ρ l, Subgroup.mem_zpowers _⟩ (x : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have h := hv
    rw [hvx, CFSG.RankThree.PartOne.FixedRank36.frattiniRep_apply] at h
    exact congrArg Additive.toMul h
  have hmem : (x : P ⧸ frattini P) ∈ {c : P ⧸ frattini P | ∀ b : Z,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN b c = c} := by
    rintro ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hb' : (⟨ρ l ^ k, hb⟩ : Z) = ⟨ρ l, Subgroup.mem_zpowers _⟩ ^ k := Subtype.ext (by simp)
    rw [hb', map_zpow]
    exact CFSG.RankThree.PartOne.FixedRank36.zpow_apply_eq_self_of_apply_eq_self' hfixa k
  rw [hset] at hmem
  obtain ⟨c, hc, hcx⟩ := hmem
  refine ⟨c, hc ⟨ρ l, Subgroup.mem_zpowers _⟩, ?_⟩
  rw [hvx, ← hcx]
  rfl

theorem h1b_module_step {G : Type} [Group G] [Finite G] {q : ℕ} [hq : Fact q.Prime] (hq3 : q ≠ 3)
    {D : Subgroup G} (hD : IsPGroup q D) (c a z δ : G)
    (hc : c ∈ normalizer (D : Set G)) (ha : a ∈ normalizer (D : Set G))
    (hz : z ∈ normalizer (D : Set G)) (hδ : δ ∈ normalizer (D : Set G))
    (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) (hδ3 : δ ^ 3 = 1)
    (hca : c * a = a * c) (hcz : c * z = z * c) (hcδ : c * δ = δ * c)
    (haδ : a * δ = δ * a) (hzδ : z * δ = δ * z) (haz : a * z * a⁻¹ = z * δ)
    (hδc : ∃ e : ℕ, ¬ 3 ∣ e ∧ ∀ x ∈ D, δ * x * δ⁻¹ = c ^ e * x * (c ^ e)⁻¹)
    (hC : ∀ x ∈ D, a * x = x * a → c * x = x * c) :
    c ∈ centralizer (D : Set G) := by
  classical
  haveI hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  letI : DistribMulAction (normalizer (D : Set G)) (Additive (↥D ⧸ frattini ↥D)) :=
    DistribMulAction.compHom (Additive (↥D ⧸ frattini ↥D))
      (CFSG.RankThree.PartOne.FixedRank36.frattiniRep q D.normalizerMonoidHom :
        normalizer (D : Set G) →* Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))
  have hact : ∀ (g : normalizer (D : Set G)) (x : ↥D),
      g • (Additive.ofMul (x : ↥D ⧸ frattini ↥D)) =
        Additive.ofMul ((D.normalizerMonoidHom g x : ↥D) : ↥D ⧸ frattini ↥D) :=
    fun g x => CFSG.RankThree.PartOne.FixedRank36.frattiniRep_apply (q := q)
      D.normalizerMonoidHom g x
  have hcoe : ∀ (g : normalizer (D : Set G)) (x : ↥D),
      ((D.normalizerMonoidHom g x : ↥D) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
    fun g x => by simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  obtain ⟨c', hc'⟩ : ∃ g : normalizer (D : Set G), (g : G) = c := ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ g : normalizer (D : Set G), (g : G) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ g : normalizer (D : Set G), (g : G) = z := ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨δ', hδ'⟩ : ∃ g : normalizer (D : Set G), (g : G) = δ := ⟨⟨δ, hδ⟩, rfl⟩
  have hc3' : c' ^ 3 = 1 :=
    Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, hc']; exact hc3)
  have ha3' : a' ^ 3 = 1 :=
    Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, ha']; exact ha3)
  have hδ3' : δ' ^ 3 = 1 :=
    Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, hδ']; exact hδ3)
  have hca' : c' * a' = a' * c' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, hc', ha']; exact hca)
  have hcz' : c' * z' = z' * c' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, hc', hz']; exact hcz)
  have hcδ' : c' * δ' = δ' * c' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, hc', hδ']; exact hcδ)
  have haδ' : a' * δ' = δ' * a' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, ha', hδ']; exact haδ)
  have hzδ' : z' * δ' = δ' * z' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, hz', hδ']; exact hzδ)
  have haz' : a' * z' * a'⁻¹ = z' * δ' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha', hz', hδ']; exact haz)
  have hδc' : ∃ e : ℕ, ¬ 3 ∣ e ∧ ∀ v : Additive (↥D ⧸ frattini ↥D), δ' • v = c' ^ e • v := by
    obtain ⟨e, he, hδe⟩ := hδc
    refine ⟨e, he, fun v => ?_⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hx]; rfl
    have hAB : D.normalizerMonoidHom δ' x = D.normalizerMonoidHom (c' ^ e) x := by
      apply Subtype.ext
      rw [hcoe, hcoe, Subgroup.coe_pow, hc', hδ']
      exact hδe (x : G) x.2
    rw [hv, hact, hact, hAB]
  have hC' : ∀ v : Additive (↥D ⧸ frattini ↥D), a' • v = v → c' • v = v := by
    intro v hav
    have hl : IsPGroup 3 (Subgroup.zpowers (D.normalizerMonoidHom a')) := by
      apply IsPGroup.of_card_dvd_pow (n := 1)
      rw [Nat.card_zpowers, pow_one]
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, ha3', map_one]
    have hv : v ∈ Module.End.eigenspace
        (CFSG.RankThree.PartOne.FixedRank36.frattiniRep q D.normalizerMonoidHom a') 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact hav
    obtain ⟨x, hxa, hxv⟩ := exists_fixed_lift_prime hD Nat.prime_three (Ne.symm hq3)
      D.normalizerMonoidHom a' hl v hv
    have hax : a * (x : G) = (x : G) * a := by
      have h1 : ((D.normalizerMonoidHom a' x : ↥D) : G) = (x : G) := congrArg Subtype.val hxa
      rw [hcoe, ha'] at h1
      calc a * (x : G) = (a * (x : G) * a⁻¹) * a := by group
        _ = (x : G) * a := by rw [h1]
    have hcx : c * (x : G) = (x : G) * c := hC (x : G) x.2 hax
    have hcx2 : D.normalizerMonoidHom c' x = x := by
      apply Subtype.ext
      rw [hcoe, hc', hcx, mul_inv_cancel_right]
    rw [← hxv, hact, hcx2]
  have hcardV : Nat.card (Additive (↥D ⧸ frattini ↥D)) = Nat.card (↥D ⧸ frattini ↥D) :=
    (Nat.card_congr (Additive.ofMul : (↥D ⧸ frattini ↥D) ≃ Additive (↥D ⧸ frattini ↥D))).symm
  have hV3 : ¬ 3 ∣ Nat.card (Additive (↥D ⧸ frattini ↥D)) := by
    intro h
    rw [hcardV] at h
    obtain ⟨k, hk⟩ := hD.exists_card_eq
    have h2 : 3 ∣ q ^ k := by
      rw [← hk]
      exact Nat.dvd_trans h (Subgroup.card_quotient_dvd_card (frattini ↥D))
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    exact hq3 h3.symm
  have hall : ∀ v : Additive (↥D ⧸ frattini ↥D), c' • v = v :=
    h1b_module_core hV3 c' a' z' δ' hc3' ha3' hδ3' hca' hcz' hcδ' haδ' hzδ' haz' hδc' hC'
  have hfr : CFSG.RankThree.PartOne.FixedRank36.frattiniRep q D.normalizerMonoidHom c' = 1 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.one_apply]
    exact hall v
  have hm : (D.normalizerMonoidHom c') ^ 3 = 1 := by
    rw [← map_pow, hc3', map_one]
  have hcop : Nat.Coprime q 3 := (Nat.coprime_primes hq.out Nat.prime_three).mpr hq3
  have hρ1 : D.normalizerMonoidHom c' = 1 :=
    CFSG.RankThree.PartOne.FiveCritical.frattiniRep_eq_one_of_pow_eq_one hD
      D.normalizerMonoidHom c' hcop hm hfr
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h2 : (c : G) * y * c⁻¹ = y := by
    have h3 := congrArg (fun f : MulAut ↥D => ((f ⟨y, hy⟩ : ↥D) : G)) hρ1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply, hc'] at h3
    exact h3
  calc y * c = (c * y * c⁻¹) * c := by rw [h2]
    _ = c * y := by group

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem h1b_prime_pure {G : Type} [Group G] [Finite G] {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) {P : Subgroup G} (hP : IsPGroup q P) (c a z δ : G)
    (hc : c ∈ normalizer (P : Set G)) (ha : a ∈ normalizer (P : Set G))
    (hz : z ∈ normalizer (P : Set G)) (hδ : δ ∈ normalizer (P : Set G))
    (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) (hδ3 : δ ^ 3 = 1)
    (hca : c * a = a * c) (hcz : c * z = z * c) (hcδ : c * δ = δ * c)
    (haδ : a * δ = δ * a) (hzδ : z * δ = δ * z) (haz : a * z * a⁻¹ = z * δ)
    (hδc : ∃ e : ℕ, ¬ 3 ∣ e ∧ ∀ x ∈ P, δ * x * δ⁻¹ = c ^ e * x * (c ^ e)⁻¹)
    (hC : ∀ x ∈ P, a * x = x * a → c * x = x * c) :
    ∀ x ∈ P, c * x = x * c := by
  by_cases hPne : P = ⊥
  · intro x hx
    rw [hPne, Subgroup.mem_bot] at hx
    rw [hx]
    simp
  obtain ⟨D, hDP, hND, -, -, hfix⟩ := exists_critical_subgroup_fix_coprime hq2 hP hPne
  have hDq : IsPGroup q D := hP.to_le hDP
  have hcD : c ∈ centralizer (D : Set G) := by
    refine h1b_module_step hq3 hDq c a z δ (hND hc) (hND ha) (hND hz) (hND hδ) hc3 ha3 hδ3 hca
      hcz hcδ haδ hzδ haz ?_ ?_
    · obtain ⟨e, he, hδe⟩ := hδc
      exact ⟨e, he, fun x hx => hδe x (hDP hx)⟩
    · intro x hx hax
      exact hC x (hDP hx) hax
  have hcP := hfix c hc 3 ((Nat.coprime_primes hq.out Nat.prime_three).mpr hq3) hc3 hcD
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp hcP x hx).symm


end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem index_eq_pow_of_normal_pow_mem_aux {H : Type*} [Group H] [Finite H] {q : ℕ}
    (hq : q.Prime) {K : Subgroup H} [K.Normal] (hK : ∀ g : H, ∃ k : ℕ, g ^ q ^ k ∈ K)
    {N : Subgroup H} (hKN : K ≤ N) : ∃ j : ℕ, N.index = q ^ j := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hQ : IsPGroup q (H ⧸ K) := by
    refine isPGroup_iff_pow_pow_eq_one.mpr ?_
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective K g
    obtain ⟨k, hk⟩ := hK g'
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hcomap : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hKN
  have hidx : N.index = (N.map (QuotientGroup.mk' K)).index := by
    have h1 := Subgroup.index_comap_of_surjective (N.map (QuotientGroup.mk' K))
      (QuotientGroup.mk'_surjective K)
    rw [hcomap] at h1
    exact h1
  obtain ⟨j, hj⟩ := hQ.index (N.map (QuotientGroup.mk' K))
  exact ⟨j, hidx.trans hj⟩

theorem sylow_mul_normal_eq {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {M U P : Subgroup G} (hUM : U ≤ M) (hUn : ∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U)
    (hP : CFSG.Open.fusionIsSylowIn q P M) (hqU : ∀ x ∈ M, ∃ k : ℕ, x ^ q ^ k ∈ U) :
    ∀ x ∈ M, ∃ y ∈ P, ∃ u ∈ U, x = y * u := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hUnorm : (U.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hUM).mpr fun h k hh hk => hUn k hk h hh
  obtain ⟨T, hT⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hP
  have hPM : P.subgroupOf M = (T : Subgroup M) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hcop : ¬ q ∣ (P.subgroupOf M).index := by
    rw [hPM]
    exact T.not_dvd_index
  have hqM : ∀ g : M, ∃ k : ℕ, g ^ q ^ k ∈ U.subgroupOf M := by
    intro g
    obtain ⟨k, hk⟩ := hqU g.1 g.2
    refine ⟨k, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hk
  obtain ⟨j, hj⟩ := index_eq_pow_of_normal_pow_mem_aux hq hqM
    (le_sup_right : U.subgroupOf M ≤ P.subgroupOf M ⊔ U.subgroupOf M)
  have hdvd : (P.subgroupOf M ⊔ U.subgroupOf M).index ∣ (P.subgroupOf M).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hdvd
    exact hcop (dvd_trans (dvd_pow_self q hne) hdvd)
  have hNtop : P.subgroupOf M ⊔ U.subgroupOf M = ⊤ := by
    rw [← Subgroup.index_eq_one, hj, hj0, pow_zero]
  intro x hx
  have hxN : (⟨x, hx⟩ : M) ∈ P.subgroupOf M ⊔ U.subgroupOf M := by
    rw [hNtop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hxN
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G), Subgroup.mem_subgroupOf.mp hz, ?_⟩
  exact (congrArg Subtype.val hyz).symm

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def twoQ (q : ℕ) (X : Type*) [Group X] : Subgroup X :=
  (CFSG.pCore q (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X))

instance twoQ_characteristic (q : ℕ) (X : Type*) [Group X] : (twoQ q X).Characteristic := by
  refine Subgroup.characteristic_iff_comap_eq.mpr fun φ => ?_
  have hφ : (CFSG.pCore 2 X).map φ.toMonoidHom = CFSG.pCore 2 X :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set φ' := QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 X) φ hφ with hφ'
  have hcomp : (QuotientGroup.mk' (CFSG.pCore 2 X)).comp φ.toMonoidHom =
      φ'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    ext x
    rfl
  rw [twoQ, Subgroup.comap_comap, hcomp, ← Subgroup.comap_comap,
    Subgroup.characteristic_iff_comap_eq.mp
      (inferInstance : (CFSG.pCore q (X ⧸ CFSG.pCore 2 X)).Characteristic) φ']

theorem exists_invariant_sylow_complement' (hB1 : ∀ {G : Type} [Group G] [Finite G] {q : ℕ},
      q.Prime → ∀ {M U P : Subgroup G}, U ≤ M → (∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U) →
        CFSG.Open.fusionIsSylowIn q P M → (∀ x ∈ M, ∃ k : ℕ, x ^ q ^ k ∈ U) →
          ∀ x ∈ M, ∃ y ∈ P, ∃ u ∈ U, x = y * u)
    {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) {T : Subgroup G} (hT : IsPGroup 3 T) {Θ : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card Θ) (hTΘ : T ≤ normalizer (Θ : Set G)) :
    ∃ P : Subgroup G, IsPGroup q P ∧ P ≤ inSubgroup (twoQ q) Θ ∧ T ≤ normalizer (P : Set G) ∧
      ∀ x ∈ inSubgroup (twoQ q) Θ, ∃ y ∈ P, ∃ u ∈ inSubgroup (CFSG.pCore 2) Θ, x = y * u := by
  have hMΘ : inSubgroup (twoQ q) Θ ≤ Θ := Subgroup.map_subtype_le _
  have hUM : inSubgroup (CFSG.pCore 2) Θ ≤ inSubgroup (twoQ q) Θ := by
    refine Subgroup.map_mono ?_
    intro y hy
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Θ) y = 1 :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Θ) y).mpr hy
    show QuotientGroup.mk' (CFSG.pCore 2 ↥Θ) y ∈ CFSG.pCore q (↥Θ ⧸ CFSG.pCore 2 ↥Θ)
    rw [h1]
    exact one_mem _
  have hΘU : Θ ≤ normalizer ((inSubgroup (CFSG.pCore 2) Θ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 ↥Θ))
  have hMn : ∀ m ∈ inSubgroup (twoQ q) Θ, ∀ u ∈ inSubgroup (CFSG.pCore 2) Θ,
      m * u * m⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ := fun m hm u hu =>
    (Subgroup.mem_normalizer_iff.mp (hΘU (hMΘ hm)) u).mp hu
  have hTM : T ≤ normalizer ((inSubgroup (twoQ q) Θ : Subgroup G) : Set G) :=
    hTΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (twoQ q ↥Θ))
  have hM3 : ¬ 3 ∣ Nat.card (inSubgroup (twoQ q) Θ) := fun h =>
    h3 (dvd_trans h (Subgroup.card_dvd_of_le hMΘ))
  have hbot : T ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    have hN : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [hN]
    exact le_top
  have hqU : ∀ x ∈ inSubgroup (twoQ q) Θ, ∃ k : ℕ, x ^ q ^ k ∈ inSubgroup (CFSG.pCore 2) Θ := by
    intro x hx
    have hx' : x ∈ (twoQ q ↥Θ).map Θ.subtype := hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx'
    have hπ : QuotientGroup.mk' (CFSG.pCore 2 ↥Θ) t ∈ CFSG.pCore q (↥Θ ⧸ CFSG.pCore 2 ↥Θ) := ht
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := q) (G := ↥Θ ⧸ CFSG.pCore 2 ↥Θ)) ⟨_, hπ⟩
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥Θ) t ^ q ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have h4 : QuotientGroup.mk' (CFSG.pCore 2 ↥Θ) (t ^ q ^ k) = 1 := by
      rw [map_pow]
      exact h2
    have h5 : t ^ q ^ k ∈ CFSG.pCore 2 ↥Θ :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Θ) (t ^ q ^ k)).mp h4
    exact ⟨k, Subgroup.mem_map.mpr ⟨t ^ q ^ k, h5, map_pow Θ.subtype t (q ^ k)⟩⟩
  obtain ⟨S, hS, -, hTS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hq hT hM3 hTM bot_le IsPGroup.of_bot hbot
  exact ⟨S, hS.2.1, hS.1, hTS, hB1 (G := G) hq hUM hMn hS hqU⟩

end CFSG.RankThree.PartTwo.Sec11

end

section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG Subgroup

theorem exists_invariant_sylow_complement {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) {T : Subgroup G} (hT : IsPGroup 3 T) {Θ : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card Θ) (hTΘ : T ≤ normalizer (Θ : Set G)) :
    ∃ P : Subgroup G, IsPGroup q P ∧ P ≤ inSubgroup (twoQ q) Θ ∧ T ≤ normalizer (P : Set G) ∧
      ∀ x ∈ inSubgroup (twoQ q) Θ, ∃ y ∈ P, ∃ u ∈ inSubgroup (CFSG.pCore 2) Θ, x = y * u :=
  exists_invariant_sylow_complement' sylow_mul_normal_eq hq hq3 hT h3 hTΘ

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11


private theorem h1b_pCore_two_quotient_eq_bot {H : Type*} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore 2 H with hN
  set K : Subgroup H := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

private theorem h1b_pCore_eq_bot_of_not_dvd (Q : Type*) [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (h : ¬ p ∣ Nat.card Q) : CFSG.pCore p Q = ⊥ := by
  rcases (CFSG.pCore_isPGroup (p := p) (G := Q)).card_eq_or_dvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) h

private theorem h1b_fitting_le_map {H : Type*} [Group H] [Finite H] (hH3 : ¬ 3 ∣ Nat.card H)
    (S : Subgroup H) (hN : CFSG.pCore 2 H ≤ S)
    (hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ t ∈ twoQ p H, t ∈ S) :
    CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H) ≤ S.map (QuotientGroup.mk' (CFSG.pCore 2 H)) := by
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases h2 : p.1.1 = 2
  · rw [h2, h1b_pCore_two_quotient_eq_bot]
    exact bot_le
  by_cases h3 : p.1.1 = 3
  · have h0 : CFSG.pCore p.1.1 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
      rw [h3]
      exact h1b_pCore_eq_bot_of_not_dvd (H ⧸ CFSG.pCore 2 H)
        (fun h => hH3 (h.trans (Subgroup.card_quotient_dvd_card _)))
    rw [h0]
    exact bot_le
  intro y hy
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 H) y
  exact Subgroup.mem_map_of_mem _ (hprime p.1.1 hp h2 h3 t hy)

theorem h1b_fitting_of_primes {G : Type} [Group G] [Finite G] (Θ : Subgroup G) (c : G)
    (hc : c ∈ normalizer (Θ : Set G)) (h3 : ¬ 3 ∣ Nat.card Θ)
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ∀ x ∈ inSubgroup (twoQ q) Θ,
      c * x * c⁻¹ * x⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ) :
    ∀ v ∈ inSubgroup twoFitting Θ, c * v * c⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ := by
  have hcNorm : c ∈ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2) Θ : Subgroup G) : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 Θ hc
  have hΘU : ∀ t ∈ Θ, ∀ u ∈ inSubgroup (CFSG.pCore 2) Θ,
      t * u * t⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ := fun t ht u hu =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 Θ ht) u).mp hu
  have hcU : ∀ u ∈ inSubgroup (CFSG.pCore 2) Θ, c * u * c⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ :=
    fun u hu => (Subgroup.mem_normalizer_iff.mp hcNorm u).mp hu
  have hcomm : ∀ u ∈ inSubgroup (CFSG.pCore 2) Θ,
      c * u * c⁻¹ * u⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ := fun u hu =>
    (inSubgroup (CFSG.pCore 2) Θ).mul_mem (hcU u hu) ((inSubgroup (CFSG.pCore 2) Θ).inv_mem hu)
  let S : Subgroup G :=
    { carrier := {g : G | g ∈ Θ ∧ c * g * c⁻¹ * g⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ}
      one_mem' := ⟨Θ.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Θ.mul_mem ha hb, ?_⟩
        have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ =
            (c * a * c⁻¹ * a⁻¹) * (a * (c * b * c⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact (inSubgroup (CFSG.pCore 2) Θ).mul_mem ha' (hΘU a ha _ hb')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Θ.inv_mem ha, ?_⟩
        have e : c * a⁻¹ * c⁻¹ * a⁻¹⁻¹ = a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hΘU a⁻¹ (Θ.inv_mem ha) _ ((inSubgroup (CFSG.pCore 2) Θ).inv_mem ha') }
  let S' : Subgroup Θ := S.comap Θ.subtype
  have hS'_iff : ∀ t : Θ, t ∈ S' ↔
      c * (t : G) * c⁻¹ * (t : G)⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ := by
    intro t
    constructor
    · intro h
      obtain ⟨-, h2⟩ := Subgroup.mem_comap.mp h
      exact h2
    · intro h
      exact Subgroup.mem_comap.mpr ⟨t.2, h⟩
  have hN : CFSG.pCore 2 Θ ≤ S' := by
    intro n hn
    exact (hS'_iff n).mpr (hcomm _ (Subgroup.mem_map_of_mem Θ.subtype hn))
  have hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ t ∈ twoQ p Θ, t ∈ S' := by
    intro p hp h2 h3' t ht
    exact (hS'_iff t).mpr (hq p hp h2 h3' (t : G) (Subgroup.mem_map_of_mem Θ.subtype ht))
  intro v hv
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hv
  have ht' : QuotientGroup.mk' (CFSG.pCore 2 ↥Θ) t ∈
      CFSG.fittingSubgroup (↥Θ ⧸ CFSG.pCore 2 ↥Θ) := ht
  obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp (h1b_fitting_le_map h3 S' hN hprime ht')
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
  have htS : t ∈ S' := by
    have := S'.mul_mem hs (hN hst)
    rwa [mul_inv_cancel_left] at this
  exact (hS'_iff t).mp htS

end CFSG.RankThree.PartTwo.Sec11

end

section

open Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

lemma zElement_isPGroup_zpowers_of_orderOf {G : Type*} [Group G] {g : G} {n : ℕ}
    (h : orderOf g = 3 ^ n) : IsPGroup 3 (Subgroup.zpowers g) :=
  IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, h])

lemma zElement_isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {g : G}
    (hg : g ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 3 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hg
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  exact zElement_isPGroup_zpowers_of_orderOf hi

lemma zElement_mem_normalizer_zpowers_of_commute {G : Type*} [Group G] {g a : G}
    (hga : Commute g a) : g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  have hc : g ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Subgroup.zpowers a := hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact (hga.zpow_right k).eq.symm
  exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G) hc

lemma zElement_mem_normalizer_zpowers_of_conj {G : Type*} [Group G] {a z : G} {k : ℕ}
    (ha3 : a ^ 3 = 1) (haz : a * z * a⁻¹ = z ^ k) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  have h1 : ∀ h ∈ Subgroup.zpowers z, a * h * a⁻¹ ∈ Subgroup.zpowers z := by
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, haz]
    exact zpow_mem (pow_mem (Subgroup.mem_zpowers z) k) n
  have ha3' : a * (a * a) = 1 := (pow_three a).symm.trans ha3
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact h1 h hh
  · intro hh
    have hh' : a * h * a⁻¹ ∈ Subgroup.zpowers z := hh
    have hx : a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹ ∈ Subgroup.zpowers z :=
      h1 _ (h1 _ hh')
    have key : a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹ = h := by
      calc a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹
          = (a * (a * a)) * h * (a * (a * a))⁻¹ := by group
        _ = h := by rw [ha3', one_mul, inv_one, mul_one]
    rw [key] at hx
    exact hx

theorem zElement_pure {G : Type} [Group G] [Finite G] {c a d z : G} {v k : ℕ}
    (hv : 2 ≤ v) (hzo : orderOf z = 3 ^ v) (hzd : z ^ 3 ^ (v - 1) = d)
    (hzc : z * c = c * z) (haz : a * z * a⁻¹ = z ^ k)
    (hk1 : 3 ^ (v - 1) ∣ k - 1) (hk2 : ¬ 3 ^ v ∣ k - 1) :
    ∃ δ : G, δ ∈ zpowers z ∧ δ ^ 3 = 1 ∧ c * δ = δ * c ∧ a * δ = δ * a ∧ z * δ = δ * z ∧
      a * z * a⁻¹ = z * δ ∧ ∃ m : ℕ, ¬ 3 ∣ m ∧ δ = d ^ m := by
  have hk0 : 1 ≤ k := by
    by_contra h
    have hk : k = 0 := by omega
    apply hk2
    rw [hk]
    simp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj1 : j + 1 - 1 = j := by omega
  rw [hj1] at hk1 hk2
  have h3v : (3 : ℕ) ^ v = 3 ^ (v - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
  obtain ⟨m, hm⟩ := id hk1
  have hm3 : ¬ 3 ∣ m := by
    rintro ⟨n, rfl⟩
    apply hk2
    refine ⟨n, ?_⟩
    rw [hm, h3v]
    ring
  have hsq : 3 ^ v ∣ j * j := by
    have h1 : 3 ^ (v - 1) * 3 ^ (v - 1) ∣ j * j := mul_dvd_mul hk1 hk1
    have h2 : 3 ^ v ∣ 3 ^ (v - 1) * 3 ^ (v - 1) := by
      rw [← pow_add]
      exact pow_dvd_pow 3 (by omega)
    exact h2.trans h1
  have hzsq : z ^ (j * j) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hzo]
    exact hsq
  have hcomm : Commute z c := hzc
  have hconj : a * z ^ j * a⁻¹ = z ^ j := by
    rw [← conj_pow, haz, ← pow_mul]
    have hexp : (j + 1) * j = j * j + j := by ring
    rw [hexp, pow_add, hzsq, one_mul]
  refine ⟨z ^ j, pow_mem (Subgroup.mem_zpowers z) j, ?_, ?_, ?_, ?_, ?_, m, hm3, ?_⟩
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hzo, h3v]
    exact mul_dvd_mul_right hk1 3
  · exact (hcomm.pow_left j).symm
  · exact mul_inv_eq_iff_eq_mul.mp hconj
  · exact (Commute.refl z).pow_right j
  · rw [haz, pow_succ']
  · rw [hm, pow_mul, hzd]

theorem zElement_isPGroup {G : Type} [Group G] [Finite G] {c a z : G} {v k : ℕ}
    (hzo : orderOf z = 3 ^ v) (haz : a * z * a⁻¹ = z ^ k) (hzc : z * c = c * z)
    (hca : a * c = c * a) (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) :
    IsPGroup 3 (Subgroup.closure ({z, a, c} : Set G)) := by
  have hN : IsPGroup 3 (Subgroup.zpowers z) :=
    zElement_isPGroup_zpowers_of_orderOf hzo
  have ha' : IsPGroup 3 (Subgroup.zpowers a) :=
    zElement_isPGroup_zpowers_of_pow_three ha3
  have hc' : IsPGroup 3 (Subgroup.zpowers c) :=
    zElement_isPGroup_zpowers_of_pow_three hc3
  have hac : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    Subgroup.zpowers_le.mpr
      (zElement_mem_normalizer_zpowers_of_commute (show Commute c a from hca.symm))
  have hK : IsPGroup 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' ha' hc' hac
  have hKN : Subgroup.zpowers a ⊔ Subgroup.zpowers c
      ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (zElement_mem_normalizer_zpowers_of_conj ha3 haz))
      (Subgroup.zpowers_le.mpr
        (zElement_mem_normalizer_zpowers_of_commute (show Commute c z from hzc.symm)))
  have hS : IsPGroup 3 (Subgroup.zpowers z ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers c) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hN hK hKN
  refine IsPGroup.to_le hS ?_
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h
  · rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  · rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  · rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

theorem h1b_conj_pow_of_commute {G : Type*} [Group G] {c d x : G} (hcd : c * d = d * c)
    (hc3 : c ^ 3 = 1) (hx : x * (c * d) = (c * d) * x) (m : ℕ) :
    d ^ m * x * (d ^ m)⁻¹ = c ^ (2 * m) * x * (c ^ (2 * m))⁻¹ := by
  have hcC : Commute c d := hcd
  have h1 : d * x = c⁻¹ * x * c * d := by
    calc d * x = c⁻¹ * (c * d * x) := by group
      _ = c⁻¹ * (x * (c * d)) := by rw [hx]
      _ = c⁻¹ * x * c * d := by simp only [mul_assoc]
  have key : ∀ n : ℕ, d ^ n * x = c⁻¹ ^ n * x * c ^ n * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hE : d * c⁻¹ ^ n = c⁻¹ ^ n * d := (hcC.inv_left.pow_left n).symm
      have hF : d * c ^ n = c ^ n * d := (hcC.pow_left n).symm
      calc d ^ (n + 1) * x = d * (d ^ n * x) := by rw [pow_succ', mul_assoc]
        _ = d * (c⁻¹ ^ n * x * c ^ n * d ^ n) := by rw [ih]
        _ = (d * c⁻¹ ^ n) * x * c ^ n * d ^ n := by simp only [mul_assoc]
        _ = (c⁻¹ ^ n * d) * x * c ^ n * d ^ n := by rw [hE]
        _ = c⁻¹ ^ n * (d * x) * c ^ n * d ^ n := by simp only [mul_assoc]
        _ = c⁻¹ ^ n * (c⁻¹ * x * c * d) * c ^ n * d ^ n := by rw [h1]
        _ = c⁻¹ ^ n * (c⁻¹ * x * c) * (d * c ^ n) * d ^ n := by simp only [mul_assoc]
        _ = c⁻¹ ^ n * (c⁻¹ * x * c) * (c ^ n * d) * d ^ n := by rw [hF]
        _ = c⁻¹ ^ (n + 1) * x * c ^ (n + 1) * d ^ (n + 1) := by
          rw [pow_succ c⁻¹ n, pow_succ' c n, pow_succ' d n]
          simp only [mul_assoc]
  have hcm : c ^ m * c ^ (2 * m) = 1 := by
    rw [← pow_add, show m + 2 * m = 3 * m by ring, pow_mul, hc3, one_pow]
  have hc2 : c⁻¹ ^ m = c ^ (2 * m) := by
    rw [inv_pow]
    exact inv_eq_iff_mul_eq_one.mpr hcm
  have hc1 : c ^ m = (c ^ (2 * m))⁻¹ := eq_inv_iff_mul_eq_one.mpr hcm
  have hfin : d ^ m * x * (d ^ m)⁻¹ = c⁻¹ ^ m * x * c ^ m :=
    mul_inv_eq_of_eq_mul (key m)
  rw [hfin, hc2, hc1]

end CFSG.RankThree.PartTwo.Sec11

end
