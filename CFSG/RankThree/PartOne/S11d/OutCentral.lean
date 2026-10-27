module

public import CFSG.RankThree.PartOne.S11d.CyclicAut
public import CFSG.RankThree.PartOne.S11d.FinalLemmas
public import CFSG.RankThree.PGroups.PrimaryFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped Pointwise
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

theorem isCyclic_of_pRank_le_one [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L S : Subgroup G} (hSL : S ≤ L) (hS : IsPGroup p S) (hr : CFSG.pRank p ↥L ≤ 1) :
    IsCyclic S := by
  by_contra hnc
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p S) := ⟨hS⟩
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hEL : E.map S.subtype ≤ L := by
    rintro _ ⟨e, -, rfl⟩
    exact hSL e.2
  have : IsElementaryAbelian p (E.map S.subtype) := CFSG.IsElementaryAbelian.map_subtype
  have hel' : IsElementaryAbelian p ((E.map S.subtype).subgroupOf L) :=
    CFSG.IsElementaryAbelian.subgroupOf hEL
  have hcard' : Nat.card ((E.map S.subtype).subgroupOf L) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv,
      Subgroup.card_map_of_injective S.subtype_injective, hcard]
  have := CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian hp.one_lt hel' hcard'
  omega

section Normalizers

theorem mem_normalizer_of_conj_subset [Finite G] {N : Subgroup G} {g : G}
    (h : ∀ x ∈ N, g * x * g⁻¹ ∈ N) : g ∈ normalizer (N : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : N.map (MulAut.conj g).toMonoidHom ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_normalizer_inf {T J : Subgroup G} {g : G} (hT : g ∈ T)
    (hJ : g ∈ normalizer (J : Set G)) : g ∈ normalizer ((T ⊓ J : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxT, hxJ⟩
    exact ⟨T.mul_mem (T.mul_mem hT hxT) (T.inv_mem hT),
      (mem_normalizer_iff.mp hJ x).mp hxJ⟩
  · rintro ⟨hxT, hxJ⟩
    refine ⟨?_, (mem_normalizer_iff.mp hJ x).mpr hxJ⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem hT) hxT) hT
    simpa [mul_assoc] using this

theorem conj_mem_centralizer {J : Subgroup G} {g : G} (hJ : g ∈ normalizer (J : Set G)) {z : G}
    (hz : z ∈ centralizer (J : Set G)) : g * z * g⁻¹ ∈ centralizer (J : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : g⁻¹ * h * g ∈ J := by
    have := (mem_normalizer_iff.mp ((normalizer (J : Set G)).inv_mem hJ) h).mp hh
    simpa using this
  have := mem_centralizer_iff.mp hz _ hh'
  calc h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
    _ = g * z * g⁻¹ * h := by group

theorem mem_normalizer_centralizer {J : Subgroup G} {g : G} (hJ : g ∈ normalizer (J : Set G)) :
    g ∈ normalizer ((centralizer (J : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  refine ⟨conj_mem_centralizer hJ, fun hz => ?_⟩
  have := conj_mem_centralizer ((normalizer (J : Set G)).inv_mem hJ) hz
  simpa [mul_assoc] using this

theorem mem_normalizer_sup_centralizer {J : Subgroup G} {g : G} (hJ : g ∈ normalizer (J : Set G)) :
    g ∈ normalizer ((J ⊔ centralizer (J : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hJ ⊢
  rw [Subgroup.map_sup, hJ]
  congr 1
  have := mem_normalizer_centralizer (J := J) (g := g)
    (by rw [mem_normalizer_iff_map_conj_eq]; exact hJ)
  rw [mem_normalizer_iff_map_conj_eq] at this
  exact this

end Normalizers

section SylowNC

variable [Finite G]

theorem mem_of_pElement_mem_normalizer {p : ℕ} [Fact p.Prime] {J S : Subgroup G}
    (hS : IsSylowOf p S J) {j : G} (hj : j ∈ J) (hjN : j ∈ normalizer (S : Set G))
    (hjp : ∃ k : ℕ, orderOf j = p ^ k) : j ∈ S := by
  have hzN : zpowers j ≤ normalizer (S : Set G) := zpowers_le.mpr hjN
  have hzp : IsPGroup p (zpowers j) := by
    obtain ⟨k, hk⟩ := hjp
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hQp : IsPGroup p (S ⊔ zpowers j : Subgroup G) :=
    hS.isPGroup.to_sup_of_normal_left' hzp hzN
  have hQJ : S ⊔ zpowers j ≤ J := sup_le hS.le (zpowers_le.mpr hj)
  have heq : S ⊔ zpowers j = S := hS.eq_of_le le_sup_left hQJ hQp
  rw [← heq]
  exact mem_sup_right (mem_zpowers j)

omit [Finite G] in
theorem pow_conj_eq_of_conj_eq {S : Subgroup G} {a v : G}
    (hv : v ∈ normalizer (S : Set G))
    (h : ∀ s ∈ S, a * s * a⁻¹ = v * s * v⁻¹) (k : ℕ) :
    ∀ s ∈ S, a ^ k * s * (a ^ k)⁻¹ = v ^ k * s * (v ^ k)⁻¹ := by
  induction k with
  | zero => intro s hs; simp
  | succ k ih =>
    intro s hs
    have hS' : v ^ k * s * (v ^ k)⁻¹ ∈ S := by
      have := (normalizer (S : Set G)).pow_mem hv k
      exact (mem_normalizer_iff.mp this s).mp hs
    calc a ^ (k + 1) * s * (a ^ (k + 1))⁻¹
        = a * (a ^ k * s * (a ^ k)⁻¹) * a⁻¹ := by rw [pow_succ', mul_inv_rev]; group
      _ = a * (v ^ k * s * (v ^ k)⁻¹) * a⁻¹ := by rw [ih s hs]
      _ = v * (v ^ k * s * (v ^ k)⁻¹) * v⁻¹ := h _ hS'
      _ = v ^ (k + 1) * s * (v ^ (k + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]; group

theorem conj_trivial_of_conj_eq_inner {p : ℕ} [Fact p.Prime] {J S : Subgroup G}
    (hS : IsSylowOf p S J) (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {a j : G}
    (hap : a ^ p = 1) (hj : j ∈ J)
    (hjS : j ∈ normalizer (S : Set G)) (hconj : ∀ s ∈ S, a * s * a⁻¹ = j * s * j⁻¹) :
    ∀ s ∈ S, a * s * a⁻¹ = s := by
  have hjfin : IsOfFinOrder j := isOfFinOrder_of_finite j
  obtain ⟨⟨⟨u, v⟩, ⟨huv, hvu, hu, hvfin, hvc⟩, -⟩, hmem⟩ :=
    CFSG.RankThree.PGroups.prime_primary_factorization hjfin (Fact.out : p.Prime)
  dsimp only at huv hvu hu hvfin hvc
  obtain ⟨huj, hvj, -⟩ := hmem u v huv hvu hu hvfin hvc
  have hzJ : zpowers j ≤ J := zpowers_le.mpr hj
  have hzN : zpowers j ≤ normalizer (S : Set G) := zpowers_le.mpr hjS
  have huS : u ∈ S := mem_of_pElement_mem_normalizer hS (hzJ huj) (hzN huj) hu
  have hvN : v ∈ normalizer (S : Set G) := hzN hvj
  have hjv : ∀ s ∈ S, a * s * a⁻¹ = v * s * v⁻¹ := by
    intro s hs
    have hvs : v * s * v⁻¹ ∈ S := (mem_normalizer_iff.mp hvN s).mp hs
    rw [hconj s hs, ← huv]
    have := hcomm u huS _ hvs
    calc u * v * s * (u * v)⁻¹ = (u * (v * s * v⁻¹)) * u⁻¹ := by group
      _ = ((v * s * v⁻¹) * u) * u⁻¹ := by rw [this]
      _ = v * s * v⁻¹ := by group
  have hmcop : Nat.Coprime p (orderOf v) := Nat.Coprime.symm hvc
  have hamS : a ^ orderOf v ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have := pow_conj_eq_of_conj_eq hvN hjv (orderOf v) s hs
    rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at this
    have h2 : a ^ orderOf v * s = s * a ^ orderOf v := by
      have := congrArg (· * a ^ orderOf v) this
      simpa [mul_assoc] using this
    exact h2.symm
  have hapS : a ^ p ∈ centralizer (S : Set G) := by
    rw [hap]
    exact Subgroup.one_mem _
  obtain ⟨x, y, hxy⟩ := (Nat.isCoprime_iff_coprime.mpr hmcop)
  have hxy' : (p : ℤ) * x + (orderOf v : ℤ) * y = 1 := by linarith
  have haeq : a = (a ^ p) ^ x * (a ^ orderOf v) ^ y := by
    calc a = a ^ (1 : ℤ) := (zpow_one a).symm
      _ = a ^ ((p : ℤ) * x + (orderOf v : ℤ) * y) := by rw [hxy']
      _ = (a ^ p) ^ x * (a ^ orderOf v) ^ y := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have haC : a ∈ centralizer (S : Set G) := by
    rw [haeq]
    exact mul_mem (zpow_mem hapS x) (zpow_mem hamS y)
  intro s hs
  have := mem_centralizer_iff.mp haC s hs
  rw [← this]
  group

theorem not_centralizes_sylow {p : ℕ} [Fact p.Prime] {J S₀ S : Subgroup G}
    (hS₀ : IsSylowOf p S₀ J) (hS : IsSylowOf p S J)
    (hc₀ : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y = y * x) {a : G} (haJ : a ∈ normalizer (J : Set G))
    (ha₀ : a ∈ normalizer (S₀ : Set G)) (hap : a ^ p = 1)
    (hmove : ∃ s ∈ S₀, a * s * a⁻¹ ≠ s) : ¬ ∀ s ∈ S, a * s * a⁻¹ = s := by
  intro hcent
  obtain ⟨g, hgJ, hg⟩ := hS.exists_mem_conj hS₀
  have hg' : ∀ x : G, x ∈ S₀ ↔ g⁻¹ * x * g ∈ S := hg
  set j : G := g * (a * g⁻¹ * a⁻¹) with hjdef
  have hjJ : j ∈ J := by
    refine J.mul_mem hgJ ?_
    have hginv : g⁻¹ ∈ J := J.inv_mem hgJ
    have := (mem_normalizer_iff.mp haJ g⁻¹).mp hginv
    exact this
  have hcent₀ : ∀ s ∈ S₀, g * a * g⁻¹ * s * (g * a * g⁻¹)⁻¹ = s := by
    intro s hs
    have hsS : g⁻¹ * s * g ∈ S := (hg' s).mp hs
    have := hcent _ hsS
    calc g * a * g⁻¹ * s * (g * a * g⁻¹)⁻¹ = g * (a * (g⁻¹ * s * g) * a⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * s * g) * g⁻¹ := by rw [this]
      _ = s := by group
  have ha₀' : a⁻¹ ∈ normalizer (S₀ : Set G) := (normalizer (S₀ : Set G)).inv_mem ha₀
  have h2 : g * a * g⁻¹ = j * a := by rw [hjdef]; group
  have hja : ∀ s ∈ S₀, a⁻¹ * s * (a⁻¹)⁻¹ = j * s * j⁻¹ := by
    intro s hs
    have hs₁ : a⁻¹ * s * (a⁻¹)⁻¹ ∈ S₀ := (mem_normalizer_iff.mp ha₀' s).mp hs
    have h1 := hcent₀ _ hs₁
    rw [h2] at h1
    calc a⁻¹ * s * (a⁻¹)⁻¹ = j * a * (a⁻¹ * s * (a⁻¹)⁻¹) * (j * a)⁻¹ := h1.symm
      _ = j * s * j⁻¹ := by group
  have hjN : j ∈ normalizer (S₀ : Set G) := by
    refine mem_normalizer_of_conj_subset fun x hx => ?_
    rw [← hja x hx]
    exact (mem_normalizer_iff.mp ha₀' x).mp hx
  have hap' : (a⁻¹) ^ p = 1 := by rw [inv_pow, hap, inv_one]
  have hall := conj_trivial_of_conj_eq_inner hS₀ hc₀ hap' hjJ hjN hja
  obtain ⟨s, hs, hne⟩ := hmove
  apply hne
  have hs' : a * s * a⁻¹ ∈ S₀ := (mem_normalizer_iff.mp ha₀ s).mp hs
  have := hall _ hs'
  simpa [mul_assoc] using this.symm

end SylowNC

section Numeric

theorem pow_one_add_modEq {p n : ℕ} (hn : 2 ≤ n) (t : ℤ) (i : ℕ) :
    (1 + (p : ℤ) ^ (n - 1) * t) ^ i ≡ 1 + i * ((p : ℤ) ^ (n - 1) * t) [ZMOD (p : ℤ) ^ n] := by
  induction i with
  | zero => simp [Int.ModEq.refl]
  | succ i ih =>
    set X : ℤ := (p : ℤ) ^ (n - 1) * t with hX
    have hX2 : (p : ℤ) ^ n ∣ X * X := by
      have h1 : (p : ℤ) ^ n ∣ (p : ℤ) ^ (n - 1) * (p : ℤ) ^ (n - 1) := by
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      have h2 : X * X = ((p : ℤ) ^ (n - 1) * (p : ℤ) ^ (n - 1)) * (t * t) := by rw [hX]; ring
      rw [h2]
      exact dvd_mul_of_dvd_left h1 _
    calc (1 + X) ^ (i + 1) = (1 + X) ^ i * (1 + X) := pow_succ _ _
      _ ≡ (1 + i * X) * (1 + X) [ZMOD (p : ℤ) ^ n] := ih.mul_right _
      _ = 1 + ((i + 1 : ℕ) : ℤ) * X + i * (X * X) := by push_cast; ring
      _ ≡ 1 + ((i + 1 : ℕ) : ℤ) * X + 0 [ZMOD (p : ℤ) ^ n] := by
        refine Int.ModEq.add_left _ ?_
        exact (Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hX2 _))
      _ = 1 + ((i + 1 : ℕ) : ℤ) * X := by ring

theorem exists_nat_pow_modEq {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) {ka kw : ℤ}
    (hka : (p : ℤ) ^ (n - 1) ∣ ka - 1) (hkw : (p : ℤ) ^ (n - 1) ∣ kw - 1)
    (hnot : ¬ (p : ℤ) ^ n ∣ ka - 1) : ∃ i : ℕ, ka ^ i ≡ kw [ZMOD (p : ℤ) ^ n] := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ta, hta⟩ := hka
  obtain ⟨tw, htw⟩ := hkw
  have hta' : ka = 1 + (p : ℤ) ^ (n - 1) * ta := by linarith
  have htw' : kw = 1 + (p : ℤ) ^ (n - 1) * tw := by linarith
  have hpn : (p : ℤ) ^ n = (p : ℤ) ^ (n - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hpta : ¬ (p : ℤ) ∣ ta := by
    rintro ⟨u, hu⟩
    apply hnot
    refine ⟨u, ?_⟩
    rw [hpn, hta, hu]
    ring
  have hta0 : (ta : ZMod p) ≠ 0 := fun h => hpta ((ZMod.intCast_zmod_eq_zero_iff_dvd ta p).mp h)
  refine ⟨((tw : ZMod p) / (ta : ZMod p)).val, ?_⟩
  have hdiv : (p : ℤ) ∣ (((tw : ZMod p) / (ta : ZMod p)).val : ℤ) * ta - tw := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    ring
  have h1 := pow_one_add_modEq (p := p) hn ta ((tw : ZMod p) / (ta : ZMod p)).val
  rw [hta', htw']
  refine h1.trans ?_
  have : (p : ℤ) ^ n ∣ (1 + (((tw : ZMod p) / (ta : ZMod p)).val : ℤ) *
      ((p : ℤ) ^ (n - 1) * ta)) - (1 + (p : ℤ) ^ (n - 1) * tw) := by
    obtain ⟨u, hu⟩ := hdiv
    refine ⟨u, ?_⟩
    rw [hpn]
    calc (1 + (((tw : ZMod p) / (ta : ZMod p)).val : ℤ) * ((p : ℤ) ^ (n - 1) * ta)) -
        (1 + (p : ℤ) ^ (n - 1) * tw)
        = (p : ℤ) ^ (n - 1) * ((((tw : ZMod p) / (ta : ZMod p)).val : ℤ) * ta - tw) := by ring
      _ = (p : ℤ) ^ (n - 1) * (p * u) := by rw [hu]
      _ = (p : ℤ) ^ (n - 1) * p * u := by ring
  exact (Int.modEq_iff_dvd.mpr this).symm

end Numeric

section Main

variable [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf {p : ℕ} [Fact p.Prime] {x : G}
    (h : ∃ k : ℕ, orderOf x = p ^ k) : IsPGroup p (zpowers x) := by
  obtain ⟨k, hk⟩ := h
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem mem_sup_of_out_centralizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J : Subgroup G} (hJ : CFSG.pRank p ↥J ≤ 1) {a w : G}
    (haJ : a ∈ normalizer (J : Set G)) (hwJ : w ∈ normalizer (J : Set G))
    (hap : a ^ p = 1) (hwp : ∃ k : ℕ, orderOf w = p ^ k) (haw : a * w = w * a)
    (hKO : ∀ v : G, v ∈ normalizer (J : Set G) → (∃ k : ℕ, orderOf v = p ^ k) →
      a * v = v * a → a ∈ zpowers v ⊔ (J ⊔ centralizer (J : Set G)) ∨
        v ∈ zpowers a ⊔ (J ⊔ centralizer (J : Set G)))
    (hwit : ∃ S₀ : Subgroup G, IsSylowOf p S₀ J ∧ a ∈ normalizer (S₀ : Set G) ∧
      ∃ s ∈ S₀, a * s * a⁻¹ ≠ s)
    {Z : Subgroup G} (hZJ : Z ≤ J) (hZp : IsPGroup p Z) (haZ : ∀ z ∈ Z, a * z = z * a)
    (hwZ : ∀ z ∈ Z, w * z = z * w)
    (hZcard : Nat.card Z * p = p ^ (Nat.card J).factorization p)
    (hn : 2 ≤ (Nat.card J).factorization p) :
    w ∈ zpowers a ⊔ (J ⊔ centralizer (J : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀, ha₀, hmove⟩ := hwit
  have hS₀cyc : IsCyclic S₀ := isCyclic_of_pRank_le_one hp hp2 hS₀.le hS₀.isPGroup hJ
  have hS₀c : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := S₀)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hapg : ∃ k : ℕ, orderOf a = p ^ k := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hap) with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hzA := isPGroup_zpowers_of_orderOf (p := p) hapg
  have hzW := isPGroup_zpowers_of_orderOf (p := p) hwp
  have haC : a ∈ centralizer (zpowers w : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((show Commute w a from haw.symm).zpow_left m).eq
  have haN : zpowers a ≤ normalizer (zpowers w : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ haC)
  have hW₀p : IsPGroup p (zpowers a ⊔ zpowers w : Subgroup G) := hzA.to_sup_of_normal_right' hzW haN
  have haZc : a ∈ centralizer (Z : Set G) := by
    rw [mem_centralizer_iff]
    exact fun z hz => (haZ z hz).symm
  have hwZc : w ∈ centralizer (Z : Set G) := by
    rw [mem_centralizer_iff]
    exact fun z hz => (hwZ z hz).symm
  have hW₀Z : zpowers a ⊔ zpowers w ≤ normalizer (Z : Set G) :=
    sup_le (zpowers_le.mpr (centralizer_le_normalizer _ haZc))
      (zpowers_le.mpr (centralizer_le_normalizer _ hwZc))
  have hWp : IsPGroup p (zpowers a ⊔ zpowers w ⊔ Z : Subgroup G) :=
    hW₀p.to_sup_of_normal_right' hZp hW₀Z
  have hWJ : zpowers a ⊔ zpowers w ⊔ Z ≤ normalizer (J : Set G) :=
    sup_le (sup_le (zpowers_le.mpr haJ) (zpowers_le.mpr hwJ)) (hZJ.trans le_normalizer)
  obtain ⟨T, hT, hWT⟩ := exists_isSylowOf_ge (p := p) (K := J ⊔ (zpowers a ⊔ zpowers w ⊔ Z))
    (Q := zpowers a ⊔ zpowers w ⊔ Z) le_sup_right hWp
  have hKJ : J ⊔ (zpowers a ⊔ zpowers w ⊔ Z) ≤ normalizer (J : Set G) :=
    sup_le le_normalizer hWJ
  have hS : IsSylowOf p (T ⊓ J) J := hT.inf_of_le_normalizer le_sup_left hKJ
  set S : Subgroup G := T ⊓ J with hSdef
  have haT : a ∈ T := hWT (mem_sup_left (mem_sup_left (mem_zpowers a)))
  have hwT : w ∈ T := hWT (mem_sup_left (mem_sup_right (mem_zpowers w)))
  have hZT : Z ≤ T := fun z hz => hWT (mem_sup_right hz)
  have haSN : a ∈ normalizer (S : Set G) := mem_normalizer_inf haT haJ
  have hwSN : w ∈ normalizer (S : Set G) := mem_normalizer_inf hwT hwJ
  have hZS : Z ≤ S := le_inf hZT hZJ
  have hScyc : IsCyclic S := isCyclic_of_pRank_le_one hp hp2 inf_le_right hS.isPGroup hJ
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := S)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set n := (Nat.card J).factorization p with hndef
  have hcardS : Nat.card S = p ^ n := hS.card_eq
  have hpn : p ^ (n - 1) * p = p ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hcardZ : Nat.card Z = p ^ (n - 1) := by
    have : Nat.card Z * p = p ^ (n - 1) * p := by rw [hZcard, hpn]
    exact Nat.eq_of_mul_eq_mul_right hp.pos this
  have hpowZ : ∀ s ∈ S, s ^ p ∈ Z := by
    intro s hs
    let Z' : Subgroup S := Z.subgroupOf S
    have : Z'.Normal := Subgroup.normal_of_isMulCommutative Z'
    have hZ'card : Nat.card Z' = p ^ (n - 1) := by
      rw [← hcardZ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv
    have hidx : Z'.index = p := by
      have h := Subgroup.card_mul_index Z'
      rw [hZ'card, hcardS, ← hpn] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h
    have h := Subgroup.pow_index_mem Z' ⟨s, hs⟩
    rw [hidx] at h
    exact h
  obtain ⟨g, hg⟩ := hScyc.exists_generator
  set s0 : G := (g : G) with hs0
  have hs0S : s0 ∈ S := g.2
  have hmem : ∀ x ∈ S, ∃ m : ℤ, x = s0 ^ m := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa [hs0] using this.symm
  have hord : orderOf s0 = p ^ n := by
    rw [hs0, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcardS]
  have hconj_mem : ∀ x : G, x ∈ normalizer (S : Set G) → ∃ k : ℤ, x * s0 * x⁻¹ = s0 ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := hmem _ ((mem_normalizer_iff.mp hx s0).mp hs0S)
    exact ⟨k, hk⟩
  obtain ⟨ka, hka⟩ := hconj_mem a haSN
  obtain ⟨kw, hkw⟩ := hconj_mem w hwSN
  have hkap : (p : ℤ) ^ (n - 1) ∣ ka - 1 := by
    have h1 := pow_conj_eq_zpow hka p
    rw [hap, inv_one, mul_one, one_mul] at h1
    have h2 : s0 ^ (ka ^ p - 1) = 1 := by rw [zpow_sub, zpow_one, ← h1, mul_inv_cancel]
    have h3 : (p : ℤ) ^ n ∣ ka ^ p - 1 := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h2
      rw [hord] at this
      exact_mod_cast this
    exact dvd_sub_one_of_dvd_pow_sub_one hp hp2 h3
  have hkwp : (p : ℤ) ^ (n - 1) ∣ kw - 1 := by
    have hs0p : s0 ^ p ∈ Z := hpowZ s0 hs0S
    have h1 : w * s0 ^ p * w⁻¹ = s0 ^ p := by
      have := hwZ _ hs0p
      rw [this]
      group
    have h2 : w * s0 ^ p * w⁻¹ = s0 ^ (kw * (p : ℤ)) := by
      rw [← zpow_natCast, ← conj_zpow, hkw, ← zpow_mul]
    rw [h2, ← zpow_natCast] at h1
    have h3 : s0 ^ (kw * (p : ℤ) - (p : ℤ)) = 1 := by rw [zpow_sub, h1, mul_inv_cancel]
    have h4 : (p : ℤ) ^ n ∣ kw * (p : ℤ) - (p : ℤ) := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h3
      rw [hord] at this
      exact_mod_cast this
    have h5 : (p : ℤ) ^ (n - 1) * p ∣ (kw - 1) * p := by
      have : (p : ℤ) ^ n = (p : ℤ) ^ (n - 1) * p := by exact_mod_cast hpn.symm
      rw [← this]
      have e : (kw - 1) * (p : ℤ) = kw * (p : ℤ) - (p : ℤ) := by ring
      rw [e]
      exact h4
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne_zero)).mp h5
  have hnc : ¬ ∀ s ∈ S, a * s * a⁻¹ = s :=
    not_centralizes_sylow hS₀ hS hS₀c haJ ha₀ hap hmove
  have hnotp : ¬ (p : ℤ) ^ n ∣ ka - 1 := by
    intro hdvd
    apply hnc
    have h1 : s0 ^ (ka - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hord]
      exact_mod_cast hdvd
    have h2 : a * s0 * a⁻¹ = s0 := by
      rw [hka]
      rw [zpow_sub, zpow_one] at h1
      exact mul_inv_eq_one.mp h1
    intro s hs
    obtain ⟨m, rfl⟩ := hmem s hs
    rw [← conj_zpow, h2]
  obtain ⟨i, hi⟩ := exists_nat_pow_modEq hp hn hkap hkwp hnotp
  set b : G := w⁻¹ * a ^ i with hbdef
  have hb0 : b * s0 * b⁻¹ = s0 := by
    have h1 := pow_conj_eq_zpow hka i
    have h2 : s0 ^ (ka ^ i) = s0 ^ kw := by
      have : s0 ^ (ka ^ i - kw) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hord]
        have := Int.modEq_iff_dvd.mp hi.symm
        exact_mod_cast this
      rw [zpow_sub] at this
      exact mul_inv_eq_one.mp this
    calc b * s0 * b⁻¹ = w⁻¹ * (a ^ i * s0 * (a ^ i)⁻¹) * w := by rw [hbdef]; group
      _ = w⁻¹ * s0 ^ kw * w := by rw [h1, h2]
      _ = w⁻¹ * (w * s0 * w⁻¹) * w := by rw [hkw]
      _ = s0 := by group
  have hbC : b ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    obtain ⟨m, rfl⟩ := hmem s hs
    have h : b * s0 ^ m * b⁻¹ = s0 ^ m := by rw [← conj_zpow, hb0]
    calc s0 ^ m * b = (b * s0 ^ m * b⁻¹) * b := by rw [h]
      _ = b * s0 ^ m := by group
  have hbS : ∀ s ∈ S, ∀ k : ℤ, b ^ k * s * (b ^ k)⁻¹ = s := by
    intro s hs k
    have := mem_centralizer_iff.mp (zpow_mem hbC k) s hs
    rw [← this]
    group
  have hbJ : b ∈ normalizer (J : Set G) :=
    mul_mem (inv_mem hwJ) (pow_mem haJ i)
  have hbW : b ∈ zpowers a ⊔ zpowers w ⊔ Z :=
    mul_mem (inv_mem (mem_sup_left (mem_sup_right (mem_zpowers w))))
      (pow_mem (mem_sup_left (mem_sup_left (mem_zpowers a))) i)
  have hbp : ∃ k : ℕ, orderOf b = p ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hWp) ⟨b, hbW⟩
    exact ⟨k, by simpa using hk⟩
  have hab : a * b = b * a :=
    ((Commute.inv_right (show Commute a w from haw)).mul_right
      ((Commute.refl a).pow_right i)).eq
  rcases hKO b hbJ hbp hab with h1 | h2
  ·
    exfalso
    have hbN := mem_normalizer_sup_centralizer hbJ
    have hz : zpowers b ≤ normalizer ((J ⊔ centralizer (J : Set G) : Subgroup G) : Set G) :=
      zpowers_le.mpr hbN
    have hcoe := coe_mul_of_left_le_normalizer_right (zpowers b) (J ⊔ centralizer (J : Set G)) hz
    have h1' : a ∈ ((zpowers b : Subgroup G) : Set G) *
        ((J ⊔ centralizer (J : Set G) : Subgroup G) : Set G) := by
      rw [← hcoe]
      exact h1
    obtain ⟨u, hu, n', hn', hun⟩ := Set.mem_mul.mp h1'
    have hcoe2 := coe_mul_of_right_le_normalizer_left J (centralizer (J : Set G))
      (centralizer_le_normalizer _)
    have hn'' : n' ∈ (J : Set G) * (centralizer (J : Set G) : Set G) := by
      rw [← hcoe2]
      exact hn'
    obtain ⟨j, hjJ, z, hzC, hjz⟩ := Set.mem_mul.mp hn''
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have hconj : ∀ s ∈ S, a * s * a⁻¹ = j * s * j⁻¹ := by
      intro s hs
      have hsJ : s ∈ J := (inf_le_right : S ≤ J) hs
      have hzs : s * z = z * s := mem_centralizer_iff.mp hzC s hsJ
      have hs' : a * s * a⁻¹ ∈ S := (mem_normalizer_iff.mp haSN s).mp hs
      have ha_eq : a = b ^ k * (j * z) := by rw [hjz, hun]
      have h3 : a * s * a⁻¹ = b ^ k * (j * s * j⁻¹) * (b ^ k)⁻¹ := by
        rw [ha_eq]
        calc b ^ k * (j * z) * s * (b ^ k * (j * z))⁻¹
            = b ^ k * (j * (z * s * z⁻¹) * j⁻¹) * (b ^ k)⁻¹ := by group
          _ = b ^ k * (j * s * j⁻¹) * (b ^ k)⁻¹ := by
            have : z * s * z⁻¹ = s := by
              rw [← hzs]
              group
            rw [this]
      have h4 := hbS _ hs' (-k)
      rw [zpow_neg, inv_inv] at h4
      have h5 : j * s * j⁻¹ = (b ^ k)⁻¹ * (a * s * a⁻¹) * b ^ k := by
        rw [h3]
        group
      exact (h5.trans h4).symm
    have hjN : j ∈ normalizer (S : Set G) := by
      refine mem_normalizer_of_conj_subset fun x hx => ?_
      rw [← hconj x hx]
      exact (mem_normalizer_iff.mp haSN x).mp hx
    exact hnc (conj_trivial_of_conj_eq_inner hS hScomm hap hjJ hjN hconj)
  · have hwb : w = a ^ i * b⁻¹ := by rw [hbdef]; group
    rw [hwb]
    exact mul_mem (pow_mem (mem_sup_left (mem_zpowers a)) i) (inv_mem h2)

end Main

end CFSG.RankThree.PartOne
