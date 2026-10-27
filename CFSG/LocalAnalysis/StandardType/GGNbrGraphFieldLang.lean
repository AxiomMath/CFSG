module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace NbrFieldLang

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_pow_of_card {p : ℕ} (hp : p.Prime) {Bs B₀ : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hB₀ : B₀ ≤ Bs) (hcard : Nat.card B₀ * p = Nat.card Bs)
    {b₀ : G} (hb₀ : b₀ ∈ Bs) (hb₀' : b₀ ∉ B₀) {b : G} (hb : b ∈ Bs) :
    ∃ b₁ ∈ B₀, ∃ j : ℕ, b = b₁ * b₀ ^ j := by
  have := Fact.mk hp
  have : IsMulCommutative ↥Bs := hBs.1
  set N : Subgroup ↥Bs := B₀.subgroupOf Bs with hNdef
  have hN : N.Normal := Subgroup.normal_of_isMulCommutative N
  have hQ : Nat.card (↥Bs ⧸ N) = p := by
    have h1 := Subgroup.card_mul_index N
    have h2 : Nat.card N = Nat.card B₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀).toEquiv
    rw [h2, ← hcard] at h1
    rw [← Subgroup.index_eq_card]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hne : ((⟨b₀, hb₀⟩ : ↥Bs) : ↥Bs ⧸ N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf]
    exact hb₀'
  have hmem : ((⟨b, hb⟩ : ↥Bs) : ↥Bs ⧸ N) ∈
      Submonoid.powers ((⟨b₀, hb₀⟩ : ↥Bs) : ↥Bs ⧸ N) := by
    rw [mem_powers_iff_mem_zpowers, zpowers_eq_top_of_prime_card hQ hne]
    exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := hmem
  dsimp only at hj
  refine ⟨b * (b₀ ^ j)⁻¹, ?_, j, by group⟩
  have h3 : ((⟨b, hb⟩ * (⟨b₀, hb₀⟩ ^ j)⁻¹ : ↥Bs) : ↥Bs ⧸ N) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hj, mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf] at h3
  simpa using h3

omit [Finite G] in
theorem conj_mul_pow_of_lang {p : ℕ} {Bs B₀ : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hB₀ : B₀ ≤ Bs) {b₀ k e : G} (hb₀ : b₀ ∈ Bs) (hk : k ∈ Subgroup.centralizer (B₀ : Set G))
    (he : e ∈ B₀) (hkb : k * b₀ * k⁻¹ = e * b₀) {b₁ : G} (hb₁ : b₁ ∈ B₀) (j : ℕ) :
    k * (b₁ * b₀ ^ j) * k⁻¹ = e ^ j * (b₁ * b₀ ^ j) := by
  have hkc : k * b₁ * k⁻¹ = b₁ := by
    rw [← (Subgroup.mem_centralizer_iff.mp hk) b₁ hb₁, mul_inv_cancel_right]
  have heb : Commute e b₀ := TableB.IsElemAbelian.comm hBs (hB₀ he) hb₀
  have heb₁ : Commute (e ^ j) b₁ :=
    TableB.IsElemAbelian.comm hBs (Bs.pow_mem (hB₀ he) j) (hB₀ hb₁)
  calc k * (b₁ * b₀ ^ j) * k⁻¹ = (k * b₁ * k⁻¹) * (k * b₀ * k⁻¹) ^ j := by
        rw [conj_pow]; group
    _ = b₁ * (e ^ j * b₀ ^ j) := by rw [hkc, hkb, heb.mul_pow]
    _ = e ^ j * (b₁ * b₀ ^ j) := by rw [← mul_assoc, ← heb₁.eq, mul_assoc]

theorem conj_mem_of_lang {p : ℕ} (hp : p.Prime) {Bs B₀ : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hB₀ : B₀ ≤ Bs) (hcard : Nat.card B₀ * p = Nat.card Bs) {b₀ k e : G} (hb₀ : b₀ ∈ Bs)
    (hb₀' : b₀ ∉ B₀) (hk : k ∈ Subgroup.centralizer (B₀ : Set G)) (he : e ∈ B₀)
    (hkb : k * b₀ * k⁻¹ = e * b₀) {b : G} (hb : b ∈ Bs) : k * b * k⁻¹ ∈ Bs := by
  obtain ⟨b₁, hb₁, j, rfl⟩ := exists_mul_pow_of_card hp hBs hB₀ hcard hb₀ hb₀' hb
  rw [conj_mul_pow_of_lang hBs hB₀ hb₀ hk he hkb hb₁ j]
  exact Bs.mul_mem (Bs.pow_mem (hB₀ he) j) (Bs.mul_mem (hB₀ hb₁) (Bs.pow_mem hb₀ j))

theorem exists_transvection_of_lang {p : ℕ} (hp : p.Prime) {Bs B₀ : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hB₀ : B₀ ≤ Bs) (hcard : Nat.card B₀ * p = Nat.card Bs)
    {b₀ k e : G} (hb₀ : b₀ ∈ Bs) (hb₀' : b₀ ∉ B₀) (hk : k ∈ Subgroup.centralizer (B₀ : Set G))
    (he : e ∈ B₀) (he1 : e ≠ 1) (hkb : k * b₀ * k⁻¹ = e * b₀) :
    ∃ φ ∈ ggInduced ⊤ Bs, GGIsTransvection p φ := by
  have := Fact.mk hp
  have hk' : k⁻¹ ∈ Subgroup.centralizer (B₀ : Set G) := inv_mem hk
  have hkc : ∀ b ∈ B₀, k * b * k⁻¹ = b := fun b hb => by
    rw [← (Subgroup.mem_centralizer_iff.mp hk) b hb, mul_inv_cancel_right]
  have hke : k⁻¹ * e * k = e := by
    rw [mul_assoc, (Subgroup.mem_centralizer_iff.mp hk) e he, inv_mul_cancel_left]
  have hkb' : k⁻¹ * b₀ * k⁻¹⁻¹ = e⁻¹ * b₀ := by
    have h1 : b₀ = (k⁻¹ * e * k) * (k⁻¹ * b₀ * k) := by
      calc b₀ = k⁻¹ * (k * b₀ * k⁻¹) * k := by group
        _ = k⁻¹ * (e * b₀) * k := by rw [hkb]
        _ = (k⁻¹ * e * k) * (k⁻¹ * b₀ * k) := by group
    rw [hke] at h1
    rw [inv_inv]
    calc k⁻¹ * b₀ * k = e⁻¹ * (e * (k⁻¹ * b₀ * k)) := by group
      _ = e⁻¹ * b₀ := by rw [← h1]
  have hkN : k ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨conj_mem_of_lang hp hBs hB₀ hcard hb₀ hb₀' hk he hkb, fun h => ?_⟩
    have h2 := conj_mem_of_lang hp hBs hB₀ hcard hb₀ hb₀' hk' (inv_mem he) hkb' h
    rwa [show k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b by group] at h2
  set φ := Bs.normalizerMonoidHom ⟨k, hkN⟩ with hφ
  have hφb : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = k * b * k⁻¹ := fun b => rfl
  have hep : e ^ p = 1 := hBs.2 e (hB₀ he)
  have hoe : orderOf e = p := orderOf_eq_prime hep he1
  refine ⟨φ, ⟨k, Subgroup.mem_top _, hkN, hφb⟩, ?_, fun b => ?_⟩
  ·
    have hfix : ∀ b : ↥Bs, φ b = b ↔ b ∈ B₀.subgroupOf Bs := by
      intro b
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hb
        obtain ⟨b₁, hb₁, j, hbj⟩ := exists_mul_pow_of_card hp hBs hB₀ hcard hb₀ hb₀' b.2
        have h1 : k * (b : G) * k⁻¹ = b := congrArg Subtype.val hb
        rw [hbj, conj_mul_pow_of_lang hBs hB₀ hb₀ hk he hkb hb₁ j] at h1
        have hej : e ^ j = 1 := by simpa using h1
        obtain ⟨c, rfl⟩ := hoe ▸ orderOf_dvd_of_pow_eq_one hej
        rw [hbj, pow_mul, hBs.2 b₀ hb₀, one_pow, mul_one]
        exact hb₁
      · intro hb
        exact Subtype.ext ((hφb b).trans (hkc b hb))
    rw [Nat.card_congr (Equiv.subtypeEquivRight hfix),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀).toEquiv, hcard]
  ·
    obtain ⟨b₁, hb₁, j, hbj⟩ := exists_mul_pow_of_card hp hBs hB₀ hcard hb₀ hb₀' b.2
    have hval : ((b⁻¹ * φ b : ↥Bs) : G) = e ^ j := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hφb, hbj,
        conj_mul_pow_of_lang hBs hB₀ hb₀ hk he hkb hb₁ j]
      have hc : Commute (b₁ * b₀ ^ j)⁻¹ (e ^ j) := TableB.IsElemAbelian.comm hBs
        (Bs.inv_mem (Bs.mul_mem (hB₀ hb₁) (Bs.pow_mem hb₀ j))) (Bs.pow_mem (hB₀ he) j)
      rw [← mul_assoc, hc.eq, mul_assoc, inv_mul_cancel, mul_one]
    apply Subtype.ext
    rw [hφb, hval]
    exact hkc _ (B₀.pow_mem he j)

end NbrFieldLang

end CFSG.StandardType
