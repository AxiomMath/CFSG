module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A1cTransfer
import CFSG.GroupTheory.BaerSuzuki
import CFSG.Assembly.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type*} [Group G]

namespace A1a

theorem le_normalizer_sup {K S₁ S₂ : Subgroup G}
    (h₁ : K ≤ Subgroup.normalizer (S₁ : Set G)) (h₂ : K ≤ Subgroup.normalizer (S₂ : Set G)) :
    K ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) := by
  intro g hg
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₁ hg)
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂ hg)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]

theorem le_normalizer_inf {K S₁ S₂ : Subgroup G}
    (h₁ : K ≤ Subgroup.normalizer (S₁ : Set G)) (h₂ : K ≤ Subgroup.normalizer (S₂ : Set G)) :
    K ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) := by
  intro g hg
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₁ hg)
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂ hg)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, e₁, e₂]

theorem le_normalizer_centralizer {K R : Subgroup G}
    (h : K ≤ Subgroup.normalizer (R : Set G)) :
    K ≤ Subgroup.normalizer ((Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro g hg c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro r hr
  have hr' : g⁻¹ * r * g ∈ R := by simpa using h g⁻¹ (K.inv_mem hg) r hr
  have := hc _ hr'
  calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * r := by group

theorem normal_centralizer_of_normal (N : Subgroup G) [N.Normal] :
    (Subgroup.centralizer (N : Set G)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_centralizer
    (K := ⊤) (R := N) (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])))

theorem exists_pow_mul_eq {L : Subgroup G} {l w : G} (hl : l ∈ L)
    (hw : w ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    ∃ l' ∈ L, (l * w) ^ n = l' * w ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hwn : w ^ n ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hw n
    refine ⟨l' * (w ^ n * l * (w ^ n)⁻¹), L.mul_mem hl' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hwn l).mp hl
    · rw [pow_succ, h]; group

theorem pow_mem_of_pow_eq_one {L : Subgroup G} {l w : G} (hl : l ∈ L)
    (hw : w ∈ Subgroup.normalizer (L : Set G)) {n : ℕ} (hwn : w ^ n = 1) : (l * w) ^ n ∈ L := by
  obtain ⟨l', hl', h⟩ := exists_pow_mul_eq hl hw n
  rw [h, hwn, mul_one]
  exact hl'

theorem conj_pow_eq {x z c : G} (hcx : c * x = x * c) (hz : z * x * z⁻¹ = c * x)
    (i : ℕ) : z * x ^ i * z⁻¹ = c ^ i * x ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : x ^ i * c = c * x ^ i := (Commute.symm (show Commute c x from hcx)).pow_left i
    calc z * x ^ (i + 1) * z⁻¹ = (z * x ^ i * z⁻¹) * (z * x * z⁻¹) := by group
      _ = (c ^ i * x ^ i) * (c * x) := by rw [ih, hz]
      _ = c ^ i * (x ^ i * c) * x := by group
      _ = c ^ (i + 1) * x ^ (i + 1) := by rw [h1]; group

theorem eq_one_of_pow_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) {c : G} {m k : ℕ}
    (hm : ¬ p ∣ m) (h1 : c ^ m = 1) (h2 : c ^ p ^ k = 1) : c = 1 := by
  have hd : orderOf c ∣ Nat.gcd m (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.Coprime m (p ^ k) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm.pow_right k
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem eq_one_of_odd_of_pow_two {c : G} {j k : ℕ} (hj : Odd j) (h1 : c ^ j = 1)
    (h2 : c ^ 2 ^ k = 1) : c = 1 :=
  eq_one_of_pow_eq_one_of_not_dvd Nat.prime_two (c := c) (m := j) (k := k)
    (fun h => (Nat.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h)) h1 h2

end A1a

open A1a

theorem three_subgroup_lemma {X Y Z : Subgroup G} (hXYZ : ⁅⁅X, Y⁆, Z⁆ = ⊥)
    (hYZX : ⁅⁅Y, Z⁆, X⁆ = ⊥) : ⁅⁅Z, X⁆, Y⁆ = ⊥ :=
  Subgroup.commutator_commutator_eq_bot_of_rotate hXYZ hYZX

@[expose] def conjugatesOf (X : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ g : G, Y = conjSubgroup X g}

@[expose] def IsTISetIn (X M : Subgroup G) : Prop :=
  X ≤ M ∧ ∀ g ∈ M, g ∉ Subgroup.normalizer (X : Set G) → X ⊓ conjSubgroup X g = ⊥

theorem conjClass_inter_eq_iff_centralizer_transitive {x : G} {X : Subgroup G} (hx : x ∈ X) :
    ({y | ∃ g : G, g⁻¹ * x * g = y} ∩ (X : Set G) =
      {y | ∃ n ∈ Subgroup.normalizer (X : Set G), n⁻¹ * x * n = y}) ↔
    ∀ Y₁ ∈ conjugatesOf X, ∀ Y₂ ∈ conjugatesOf X, x ∈ Y₁ → x ∈ Y₂ →
      ∃ c ∈ Subgroup.centralizer ({x} : Set G), conjSubgroup Y₁ c = Y₂ := by
  constructor
  · intro hEq
    have key : ∀ g : G, x ∈ conjSubgroup X g →
        ∃ u ∈ Subgroup.centralizer ({x} : Set G), conjSubgroup X u = conjSubgroup X g := by
      intro g hg
      have hg' : g * x * g⁻¹ ∈ X := mem_conjSubgroup_iff.mp hg
      have hmem : g * x * g⁻¹ ∈ {y | ∃ g' : G, g'⁻¹ * x * g' = y} ∩ (X : Set G) :=
        ⟨⟨g⁻¹, by simp⟩, hg'⟩
      obtain ⟨n, hn, hnx⟩ := hEq ▸ hmem
      refine ⟨n * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have h1 : (n * g)⁻¹ * x * (n * g) = x := by
          calc (n * g)⁻¹ * x * (n * g) = g⁻¹ * (n⁻¹ * x * n) * g := by group
            _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hnx]
            _ = x := by group
        calc x * (n * g) = (n * g) * ((n * g)⁻¹ * x * (n * g)) := by group
          _ = (n * g) * x := by rw [h1]
      · rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hn]
    rintro Y₁ ⟨g₁, rfl⟩ Y₂ ⟨g₂, rfl⟩ hx₁ hx₂
    obtain ⟨u₁, hu₁, e₁⟩ := key g₁ hx₁
    obtain ⟨u₂, hu₂, e₂⟩ := key g₂ hx₂
    refine ⟨u₁⁻¹ * u₂, (Subgroup.centralizer ({x} : Set G)).mul_mem
      ((Subgroup.centralizer ({x} : Set G)).inv_mem hu₁) hu₂, ?_⟩
    rw [← e₁, ← e₂, conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  · intro htrans
    ext y
    constructor
    · rintro ⟨⟨g, rfl⟩, hyX⟩
      have hY₂ : x ∈ conjSubgroup X g⁻¹ := by
        rw [mem_conjSubgroup_iff]
        simpa using hyX
      obtain ⟨c, hc, hcY⟩ := htrans X ⟨1, (conjSubgroup_one X).symm⟩ (conjSubgroup X g⁻¹)
        ⟨g⁻¹, rfl⟩ hx hY₂
      refine ⟨c * g, ?_, ?_⟩
      · rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, hcY,
          conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      · have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)
        have h1 : c⁻¹ * x * c = x := by rw [mul_assoc, hcx, inv_mul_cancel_left]
        calc (c * g)⁻¹ * x * (c * g) = g⁻¹ * (c⁻¹ * x * c) * g := by group
          _ = g⁻¹ * x * g := by rw [h1]
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hn) x).mp hx
      simpa using this

theorem existsUnique_conjugate_mem_of_centralizer_le {x : G} {X : Subgroup G} (hx : x ∈ X)
    (hEq : {y | ∃ g : G, g⁻¹ * x * g = y} ∩ (X : Set G) =
      {y | ∃ n ∈ Subgroup.normalizer (X : Set G), n⁻¹ * x * n = y})
    (hC : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    ∃! Y : Subgroup G, Y ∈ conjugatesOf X ∧ x ∈ Y := by
  refine ⟨X, ⟨⟨1, (conjSubgroup_one X).symm⟩, hx⟩, ?_⟩
  rintro Y ⟨hY, hxY⟩
  obtain ⟨c, hc, hcY⟩ := (conjClass_inter_eq_iff_centralizer_transitive hx).mp hEq X
    ⟨1, (conjSubgroup_one X).symm⟩ Y hY hx hxY
  rw [← hcY]
  exact conjSubgroup_eq_iff_mem_normalizer.mpr (hC hc)

theorem existsUnique_conjugate_mem_of_isTISetIn {x : G} {X M : Subgroup G} (hx : x ∈ X)
    (hx1 : x ≠ 1) (hTI : IsTISetIn X M)
    (hEq : {y | ∃ g : G, g⁻¹ * x * g = y} ∩ (X : Set G) =
      {y | ∃ n ∈ Subgroup.normalizer (X : Set G), n⁻¹ * x * n = y})
    (hCM : Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∃! Y : Subgroup G, Y ∈ conjugatesOf X ∧ x ∈ Y := by
  refine existsUnique_conjugate_mem_of_centralizer_le hx hEq fun c hc => ?_
  by_contra hcN
  have hbot := hTI.2 c (hCM hc) hcN
  have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)
  have hxc : x ∈ conjSubgroup X c := by
    rw [mem_conjSubgroup_iff, show c * x * c⁻¹ = x by rw [← hcx]; group]
    exact hx
  have : x ∈ X ⊓ conjSubgroup X c := ⟨hx, hxc⟩
  rw [hbot] at this
  exact hx1 (Subgroup.mem_bot.mp this)

theorem baer_suzuki_subgroup [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (_hX : IsPGroup p X) :
    X ≤ CFSG.Open.pCore p G ∨ ∃ g : G, ¬ IsPGroup p ↥(X ⊔ conjSubgroup X g) := by
  by_cases h : ∀ g : G, IsPGroup p ↥(X ⊔ conjSubgroup X g)
  · left
    intro x hx
    refine (CFSG.BaerSuzuki.baer_suzuki_iff x).mpr fun g => (h g⁻¹).to_le ?_
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.mem_sup_left hx
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hx
  · right
    exact not_forall.mp h

private theorem isPGroup_closure_of_involutions {t s : G} (htt : t * t = 1) (hss : s * s = 1)
    {k : ℕ} (hk : (t * s) ^ 2 ^ k = 1) : IsPGroup 2 ↥(Subgroup.closure ({t, s} : Set G)) := by
  set a : G := t * s with ha
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hta : t * a * t⁻¹ = a⁻¹ := by
    calc t * a * t⁻¹ = (t * t) * s * t := by rw [ha, hti]; group
      _ = s * t := by rw [htt]; group
      _ = a⁻¹ := by rw [ha, mul_inv_rev, hti, hsi]
  have hconj : ∀ i : ℤ, a ^ i * t = t * a ^ (-i) := by
    intro i
    have h1 : t * a ^ i * t = a ^ (-i) := by
      have : t * a ^ i * t⁻¹ = a ^ (-i) := by
        rw [← conj_zpow, hta, inv_zpow']
      rwa [hti] at this
    calc a ^ i * t = t * (t * a ^ i * t) := by
          rw [show t * (t * a ^ i * t) = (t * t) * a ^ i * t by group, htt]; group
      _ = t * a ^ (-i) := by rw [h1]
  have hmain : ∀ z ∈ Subgroup.closure ({t, s} : Set G), ∃ i : ℤ, z = a ^ i ∨ z = t * a ^ i := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨0, Or.inr (by simp)⟩
      · rw [Set.mem_singleton_iff] at hx
        refine ⟨1, Or.inr ?_⟩
        rw [hx, zpow_one, ha, ← mul_assoc, htt, one_mul]
    | one => exact ⟨0, Or.inl (by simp)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨j, hj | hj⟩ := hy
      · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
      · refine ⟨j - i, Or.inr ?_⟩
        rw [hi, hj, ← mul_assoc, hconj, mul_assoc, ← zpow_add, neg_add_eq_sub]
      · exact ⟨i + j, Or.inr (by rw [hi, hj, mul_assoc, ← zpow_add])⟩
      · refine ⟨j - i, Or.inl ?_⟩
        rw [hi, hj, mul_assoc, ← mul_assoc (a ^ i), hconj, mul_assoc t, ← mul_assoc t,
          ← mul_assoc (t * t), htt, one_mul, ← zpow_add, neg_add_eq_sub]
    | inv x _ hx =>
      obtain ⟨i, hi | hi⟩ := hx
      · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
      · refine ⟨i, Or.inr ?_⟩
        rw [hi, mul_inv_rev, hti, ← zpow_neg, hconj, neg_neg]
  intro z
  obtain ⟨i, hi | hi⟩ := hmain z z.2
  · refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  · refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    rw [hi]
    calc (t * a ^ i) ^ 2 = t * (a ^ i * t) * a ^ i := by rw [pow_two]; group
      _ = (t * t) * a ^ (-i) * a ^ i := by rw [hconj]; group
      _ = 1 := by rw [htt, one_mul, ← zpow_add, neg_add_cancel, zpow_zero]

theorem baer_suzuki_involution [Finite G] {X : Subgroup G} (hX : Nat.card X = 2)
    (hXc : ¬ X ≤ CFSG.Open.pCore 2 G) :
    ∃ y : G, y ≠ 1 ∧ Odd (orderOf y) ∧ ∀ x ∈ X, x ≠ 1 → x * y * x⁻¹ = y⁻¹ := by
  have hex : ∃ t ∈ X, t ≠ 1 := by
    by_contra hcon
    have : X = ⊥ := (Subgroup.eq_bot_iff_forall X).mpr fun x hx => by
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    rw [this] at hX
    simp at hX
  obtain ⟨t, htX, ht1⟩ := hex
  have hunique : ∀ x ∈ X, x ≠ 1 → x = t := by
    intro x hx hx1
    obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (1 : X)).mp hX
    have h1 : (⟨x, hx⟩ : X) = y := hy' _ (fun h => hx1 (by simpa using congrArg Subtype.val h))
    have h2 : (⟨t, htX⟩ : X) = y := hy' _ (fun h => ht1 (by simpa using congrArg Subtype.val h))
    simpa using congrArg Subtype.val (h1.trans h2.symm)
  have htt : t * t = 1 := by
    have h : t * t ∈ X := X.mul_mem htX htX
    by_contra hne
    have := hunique _ h hne
    exact ht1 (by simpa using this)
  have hXt : X = Subgroup.zpowers t := by
    apply le_antisymm
    · intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · rw [hunique x hx hx1]; exact Subgroup.mem_zpowers t
    · exact (Subgroup.zpowers_le).mpr htX
  have htcore : t ∉ CFSG.Open.pCore 2 G := fun h => hXc (hXt ▸ Subgroup.zpowers_le.mpr h)
  have hBS : ¬ ∀ g : G, IsPGroup 2 ↥(Subgroup.closure ({t, g * t * g⁻¹} : Set G)) := by
    intro h
    apply htcore
    exact (CFSG.BaerSuzuki.baer_suzuki_iff t).mpr h
  obtain ⟨g, hg⟩ := not_forall.mp hBS
  set s : G := g * t * g⁻¹ with hs
  have hss : s * s = 1 := by
    rw [hs]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  set a : G := t * s with ha
  have hta : t * a * t⁻¹ = a⁻¹ := by
    calc t * a * t⁻¹ = (t * t) * s * t := by rw [ha, hti]; group
      _ = s * t := by rw [htt]; group
      _ = a⁻¹ := by rw [ha, mul_inv_rev, hti, hsi]
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have hm1 : m ≠ 1 := by
    rintro rfl
    apply hg
    refine isPGroup_closure_of_involutions htt hss (k := k) ?_
    rw [← orderOf_dvd_iff_pow_eq_one, hord, mul_one]
  have hdvd : 2 ^ k ∣ orderOf a := ⟨m, hord⟩
  have hy : orderOf (a ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hord]
    exact Nat.mul_div_cancel_left m (by positivity)
  refine ⟨a ^ 2 ^ k, ?_, hy ▸ hm, ?_⟩
  · intro h
    rw [h, orderOf_one] at hy
    exact hm1 hy.symm
  · intro x hx hx1
    rw [hunique x hx hx1, ← conj_pow, hta, inv_pow]

theorem pCoreOf_top (p : ℕ) : pCoreOf p (⊤ : Subgroup G) = CFSG.Open.pCore p G := by
  unfold pCoreOf
  rw [← map_pCore_mulEquiv p (Subgroup.topEquiv (G := G)).symm, Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom =
      MonoidHom.id G := by
    ext x; rfl
  rw [this, Subgroup.map_id]

section A16

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem pCoreOf_le_pCoreOf_of_sylow {H K : Subgroup G} (hHK : H ≤ K) {T : Subgroup G}
    (hTp : IsPGroup p T) (hTH : T ≤ H) (hTK : ¬ p ∣ (T.subgroupOf K).index) :
    pCoreOf p K ≤ pCoreOf p H := by
  have hTK' : T ≤ K := hTH.trans hHK
  have hTpK : IsPGroup p (T.subgroupOf K) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTK').symm
  let S : Sylow p K := hTpK.toSylow hTK
  have hcore : CFSG.Open.pCore p K ≤ (S : Subgroup K) := by
    have := CFSG.pCore_normal (G := K) (p := p)
    exact (CFSG.pCore_isPGroup (G := K) (p := p)).le_sylow_of_normal S
  have h1 : pCoreOf p K ≤ T := by
    rintro x ⟨y, hy, rfl⟩
    have h2 := hcore hy
    have hS : (S : Subgroup K) = T.subgroupOf K := rfl
    rw [hS] at h2
    exact h2
  exact le_pCoreOf_of_le_normalizer p (h1.trans hTH) (hHK.trans (le_normalizer_pCoreOf p K))
    (pCoreOf_isPGroup p K)

theorem centralizer_pCoreOf_le_of_sylow {H K : Subgroup G} (hHK : H ≤ K) {T : Subgroup G}
    (hTp : IsPGroup p T) (hTH : T ≤ H) (hTK : ¬ p ∣ (T.subgroupOf K).index)
    (hK : K ⊓ Subgroup.centralizer (pCoreOf p K : Set G) ≤ pCoreOf p K) :
    H ⊓ Subgroup.centralizer (pCoreOf p H : Set G) ≤ pCoreOf p H := by
  have h := pCoreOf_le_pCoreOf_of_sylow hHK hTp hTH hTK
  intro x hx
  exact h (hK ⟨hHK hx.1, Subgroup.centralizer_le h hx.2⟩)

theorem not_dvd_index_subgroupOf_of_sylow (T : Sylow p G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ K) : ¬ p ∣ ((T : Subgroup G).subgroupOf K).index := by
  intro hdvd
  have h2 := Subgroup.relIndex_mul_index hTK
  exact T.not_dvd_index (h2 ▸ Dvd.dvd.mul_right hdvd _)

theorem pCore_le_pCoreOf_of_sylow (T : Sylow p G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) : CFSG.Open.pCore p G ≤ pCoreOf p H := by
  rw [← pCoreOf_top p]
  exact pCoreOf_le_pCoreOf_of_sylow le_top T.isPGroup' hTH
    (not_dvd_index_subgroupOf_of_sylow T le_top)

theorem centralizer_pCoreOf_le_of_sylow_ambient (T : Sylow p G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H)
    (hG : Subgroup.centralizer (CFSG.Open.pCore p G : Set G) ≤ CFSG.Open.pCore p G) :
    H ⊓ Subgroup.centralizer (pCoreOf p H : Set G) ≤ pCoreOf p H := by
  have h := pCore_le_pCoreOf_of_sylow T hTH
  intro x hx
  exact h (hG (Subgroup.centralizer_le h hx.2))

end A16


theorem centralizer_pCore_le_iff_pCoreOf (p : ℕ) (H : Subgroup G) :
    Subgroup.centralizer (CFSG.Open.pCore p H : Set H) ≤ CFSG.Open.pCore p H ↔
      H ⊓ Subgroup.centralizer (pCoreOf p H : Set G) ≤ pCoreOf p H := by
  constructor
  · intro h x hx
    have hy : (⟨x, hx.1⟩ : H) ∈ Subgroup.centralizer (CFSG.Open.pCore p H : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx.2 (u : G) ⟨u, hu, rfl⟩
    exact ⟨⟨x, hx.1⟩, h hy, rfl⟩
  · intro h y hy
    have hx : (y : G) ∈ H ⊓ Subgroup.centralizer (pCoreOf p H : Set G) := by
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy u hu)
    obtain ⟨u, hu, hux⟩ := h hx
    have : u = y := Subtype.ext hux
    rwa [← this]

private theorem comm_pow_eq_one {s u : G} (hc : s * u * s⁻¹ * u⁻¹ ∈ Subgroup.center G) {m : ℕ}
    (hm : s ^ m = 1) : (s * u * s⁻¹ * u⁻¹) ^ m = 1 := by
  set c := s * u * s⁻¹ * u⁻¹ with hcdef
  have hcz : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hc g).symm
  have hsu : s * u * s⁻¹ = c * u := by rw [hcdef]; group
  have key : ∀ i : ℕ, s ^ i * u * (s ^ i)⁻¹ = c ^ i * u := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc s ^ (i + 1) * u * (s ^ (i + 1))⁻¹ = s * (s ^ i * u * (s ^ i)⁻¹) * s⁻¹ := by group
        _ = s * (c ^ i * u) * s⁻¹ := by rw [ih]
        _ = c ^ i * (s * u * s⁻¹) := by
          have h1 : s * c ^ i * s⁻¹ = c ^ i := by
            have : s * c ^ i = c ^ i * s :=
              ((Commute.pow_left (show Commute c s from hcz s) i).symm).eq
            rw [this]; group
          calc s * (c ^ i * u) * s⁻¹ = (s * c ^ i * s⁻¹) * (s * u * s⁻¹) := by group
            _ = c ^ i * (s * u * s⁻¹) := by rw [h1]
        _ = c ^ (i + 1) * u := by rw [hsu]; group
  have := key m
  rw [hm] at this
  simpa using this.symm

theorem centralizer_pCore_quotient_le [Finite G] {p : ℕ} [hp : Fact p.Prime] (X : Subgroup G)
    [X.Normal] (hX : X ≤ Subgroup.center G)
    (h : Subgroup.centralizer (CFSG.Open.pCore p G : Set G) ≤ CFSG.Open.pCore p G) :
    Subgroup.centralizer (CFSG.Open.pCore p (G ⧸ X) : Set (G ⧸ X)) ≤
      CFSG.Open.pCore p (G ⧸ X) := by
  have := CFSG.pCore_normal (G := G ⧸ X) (p := p)
  have : (Subgroup.centralizer (CFSG.Open.pCore p (G ⧸ X) : Set (G ⧸ X))).Normal :=
    normal_centralizer_of_normal _
  refine le_pCore p inferInstance ?_
  rintro ⟨cbar, hcbar⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective cbar
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.out.ne_one
  have hdvd : p ^ a ∣ orderOf g := ⟨m, hord⟩
  have hs : orderOf (g ^ p ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) hdvd, hord]
    simp [pow_pos hp.out.pos]
  have hsm : (g ^ p ^ a) ^ m = 1 := by rw [← hs]; exact pow_orderOf_eq_one _
  have hsbar : ((g ^ p ^ a : G) : G ⧸ X) ∈
      Subgroup.centralizer (CFSG.Open.pCore p (G ⧸ X) : Set (G ⧸ X)) := by
    rw [QuotientGroup.mk_pow]
    exact Subgroup.pow_mem _ hcbar _
  have hcomm : ∀ u ∈ CFSG.Open.pCore p G, (g ^ p ^ a) * u = u * (g ^ p ^ a) := by
    intro u hu
    have hubar : ((u : G) : G ⧸ X) ∈ CFSG.Open.pCore p (G ⧸ X) :=
      map_pCore_le p (QuotientGroup.mk' X) (QuotientGroup.mk'_surjective X) ⟨u, hu, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hsbar _ hubar
    set s := g ^ p ^ a with hsdef
    have hcX : s * u * s⁻¹ * u⁻¹ ∈ X := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact (by simpa [mul_assoc] using h1.symm)
    have hcz : s * u * s⁻¹ * u⁻¹ ∈ Subgroup.center G := hX hcX
    have hcP : s * u * s⁻¹ * u⁻¹ ∈ CFSG.Open.pCore p G := by
      have := (CFSG.pCore_normal (G := G) (p := p)).conj_mem u hu s
      exact (CFSG.Open.pCore p G).mul_mem this ((CFSG.Open.pCore p G).inv_mem hu)
    have hpow := comm_pow_eq_one hcz hsm
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := G) (p := p) ⟨_, hcP⟩
    have hk' : (s * u * s⁻¹ * u⁻¹) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc1 := eq_one_of_pow_eq_one_of_not_dvd hp.out hm hpow hk'
    calc s * u = (s * u * s⁻¹ * u⁻¹) * u * s := by group
      _ = u * s := by rw [hc1]; group
  have hsP : g ^ p ^ a ∈ CFSG.Open.pCore p G :=
    h (Subgroup.mem_centralizer_iff.mpr fun u hu => (hcomm u hu).symm)
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := G) (p := p) ⟨_, hsP⟩
  have hk' : (g ^ p ^ a) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hs1 : g ^ p ^ a = 1 := eq_one_of_pow_eq_one_of_not_dvd hp.out hm hsm hk'
  refine ⟨a, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, hs1]
  rfl

theorem centralizer_pCore_quotient_subgroupOf_le [Finite G] {p : ℕ} [Fact p.Prime]
    {H X : Subgroup G} [(X.subgroupOf H).Normal] (hX : X ≤ H ⊓ Subgroup.centralizer (H : Set G))
    (h : H ⊓ Subgroup.centralizer (pCoreOf p H : Set G) ≤ pCoreOf p H) :
    Subgroup.centralizer (CFSG.Open.pCore p (H ⧸ X.subgroupOf H) :
        Set (H ⧸ X.subgroupOf H)) ≤ CFSG.Open.pCore p (H ⧸ X.subgroupOf H) := by
  refine centralizer_pCore_quotient_le (G := H) (X.subgroupOf H) ?_
    ((centralizer_pCore_le_iff_pCoreOf p H).mpr h)
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hX hx).2 y y.2)

theorem centralizer_pCoreOf_le_of_sup [Finite G] {H L M : Subgroup G}
    (hLn : (L.subgroupOf H).Normal) (hH : H = L ⊔ M)
    (hFL : L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L)
    (hFM : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (_hT : ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≤ M ∧ ¬ 2 ∣ (T.subgroupOf H).index)
    {Q : Subgroup G} (hQ : Q ≤ pCoreOf 2 M) (hNQ : H ⊓ Subgroup.normalizer (Q : Set G) ≤ M) :
    H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := by
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hMH : M ≤ H := hH ▸ le_sup_right
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLn
  have hML : M ≤ Subgroup.normalizer (L : Set G) := hMH.trans hHL
  have hHR : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hMB : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M
  have hAL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hBM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hAR : pCoreOf 2 L ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hAL.trans hLH)
      (hHL.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hHN : H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hHR)
  generalize hNdef : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) = N at hHN ⊢
  have hNH : N ≤ H := hNdef ▸ inf_le_left
  have hNc : ∀ x ∈ N, ∀ r ∈ pCoreOf 2 H, r * x = x * r := fun x hx r hr => by
    rw [← hNdef] at hx
    exact Subgroup.mem_centralizer_iff.mp hx.2 r hr
  have hLN : ∀ d ∈ L, d ∈ N → d ∈ pCoreOf 2 L := fun d hdL hdN =>
    hFL ⟨hdL, fun a ha => by
      rw [← hNdef] at hdN
      exact Subgroup.mem_centralizer_iff.mp hdN.2 a (hAR ha)⟩
  have hHΛ : H ≤ Subgroup.normalizer ((L ⊔ N : Subgroup G) : Set G) :=
    le_normalizer_sup hHL hHN
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = pCoreOf 2 M ⊓ (L ⊔ N) := ⟨_, rfl⟩
  have hWB : W ≤ pCoreOf 2 M := hW ▸ inf_le_left
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := hW ▸ le_normalizer_inf hMB (hMH.trans hHΛ)
  have hWL : W ≤ Subgroup.normalizer (L : Set G) := (hWB.trans hBM).trans hML
  have hHLW : H ≤ Subgroup.normalizer ((L ⊔ W : Subgroup G) : Set G) := by
    have : L ⊔ M ≤ Subgroup.normalizer ((L ⊔ W : Subgroup G) : Set G) :=
      sup_le (le_sup_left.trans Subgroup.le_normalizer) (le_normalizer_sup hML hMW)
    rwa [← hH] at this
  obtain ⟨V, hV⟩ : ∃ V : Subgroup G, V = N ⊓ (L ⊔ W) := ⟨_, rfl⟩
  have hVN : V ≤ N := hV ▸ inf_le_left
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hV ▸ le_normalizer_inf hHN hHLW
  have hVp : IsPGroup 2 V := by
    rintro ⟨v, hv⟩
    rw [hV] at hv
    obtain ⟨hvN, hvLW⟩ := hv
    have hset : ((L ⊔ W : Subgroup G) : Set G) = (L : Set G) * (W : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left L W hWL
    have hv' : v ∈ (L : Set G) * (W : Set G) := by rw [← hset]; exact hvLW
    obtain ⟨l, hl, w, hw, rfl⟩ := hv'
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 M ⟨w, hWB hw⟩
    have hwa : w ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have h1 : (l * w) ^ 2 ^ a ∈ L := pow_mem_of_pow_eq_one hl (hWL hw) hwa
    have h2 : (l * w) ^ 2 ^ a ∈ N := N.pow_mem hvN _
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 L ⟨_, hLN _ h1 h2⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((l * w) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have : (l * w) ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul]; exact hb'
    simpa using this
  have hVR : V ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 (hVN.trans hNH) hHV hVp
  have hmain : ∀ x ∈ N, Odd (orderOf x) → x = 1 := by
    intro x hxN hxodd
    have hcomm : ∀ z ∈ pCoreOf 2 M, z * x * z⁻¹ = x := by
      intro z hz
      have hzM : z ∈ M := hBM hz
      have hzH : z ∈ H := hMH hzM
      have hxH : x ∈ H := hNH hxN
      have hxLM : x ∈ L ⊔ M := hH ▸ hxH
      have hset : ((L ⊔ M : Subgroup G) : Set G) = (L : Set G) * (M : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left L M hML
      have hx' : x ∈ (L : Set G) * (M : Set G) := by rw [← hset]; exact hxLM
      obtain ⟨l, hl, m, hm, hxlm⟩ := hx'
      obtain ⟨c, hc⟩ : ∃ c : G, c = z * x * z⁻¹ * x⁻¹ := ⟨_, rfl⟩
      have hzxN : z * x * z⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hzH) x).mp hxN
      have hcN : c ∈ N := by rw [hc]; exact N.mul_mem hzxN (N.inv_mem hxN)
      have hmΛ : m ∈ L ⊔ N := by
        have : m = l⁻¹ * x := by rw [← hxlm]; group
        rw [this]
        exact (L ⊔ N).mul_mem (Subgroup.mem_sup_left (L.inv_mem hl)) (Subgroup.mem_sup_right hxN)
      have hbB : z * m * z⁻¹ * m⁻¹ ∈ pCoreOf 2 M := by
        have h1 : m * z⁻¹ * m⁻¹ ∈ pCoreOf 2 M :=
          (Subgroup.mem_normalizer_iff.mp (hMB hm) z⁻¹).mp ((pCoreOf 2 M).inv_mem hz)
        have h2 := (pCoreOf 2 M).mul_mem hz h1
        simpa [mul_assoc] using h2
      have hbΛ : z * m * z⁻¹ * m⁻¹ ∈ L ⊔ N := by
        have h3 : z * m * z⁻¹ ∈ L ⊔ N := (Subgroup.mem_normalizer_iff.mp (hHΛ hzH) m).mp hmΛ
        exact (L ⊔ N).mul_mem h3 ((L ⊔ N).inv_mem hmΛ)
      have hbW : z * m * z⁻¹ * m⁻¹ ∈ W := by rw [hW]; exact ⟨hbB, hbΛ⟩
      have hl₁ : z * l * z⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hHL hzH) l).mp hl
      have hcLW : c ∈ L ⊔ W := by
        have : c = (z * l * z⁻¹) * (z * m * z⁻¹ * m⁻¹) * l⁻¹ := by
          rw [hc, ← hxlm]; group
        rw [this]
        exact (L ⊔ W).mul_mem ((L ⊔ W).mul_mem (Subgroup.mem_sup_left hl₁)
          (Subgroup.mem_sup_right hbW)) (Subgroup.mem_sup_left (L.inv_mem hl))
      have hcV : c ∈ V := by rw [hV]; exact ⟨hcN, hcLW⟩
      have hcR : c ∈ pCoreOf 2 H := hVR hcV
      have hcx : c * x = x * c := hNc x hxN c hcR
      have hzx : z * x * z⁻¹ = c * x := by rw [hc]; group
      have hpow := conj_pow_eq hcx hzx (orderOf x)
      rw [pow_orderOf_eq_one] at hpow
      have hc1 : c ^ orderOf x = 1 := by simpa using hpow.symm
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨c, hcR⟩
      have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hc' : c = 1 := eq_one_of_odd_of_pow_two hxodd hc1 hck
      rw [hzx, hc']; simp
    have hxM : x ∈ M := by
      apply hNQ
      refine ⟨hNH hxN, ?_⟩
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
      have := hcomm q (hQ hq)
      calc q * x = (q * x * q⁻¹) * q := by group
        _ = x * q := by rw [this]
    have hxB : x ∈ pCoreOf 2 M := by
      refine hFM ⟨hxM, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have := hcomm b hb
      calc b * x = (b * x * b⁻¹) * b := by group
        _ = x * b := by rw [this]
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨x, hxB⟩
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
    exact orderOf_eq_one_iff.mp
      ((Nat.coprime_two_right.mpr hxodd).pow_right k |>.eq_one_of_dvd hd)
  have hNp : IsPGroup 2 N := by
    rintro ⟨x, hx⟩
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hdvd : 2 ^ a ∣ orderOf x := ⟨m, hord⟩
    have hy : orderOf (x ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hord]
      exact Nat.mul_div_cancel_left m (by positivity)
    have := hmain (x ^ 2 ^ a) (N.pow_mem hx _) (hy ▸ hm)
    exact ⟨a, Subtype.ext this⟩
  exact le_pCoreOf_of_le_normalizer 2 hNH hHN hNp

end CFSG.Quasithin
