module

public import CFSG.RankThree.PartTwo.Sec12.Coordinates
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open CFSG CFSG.RankThree.PartTwo

variable {G : Type*} [Group G]

section Coords

variable {D : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
  (f : Multiplicative V ≃* D)

private theorem coordVec_eq_iff_apply {c : D} {w : V} :
    Sec12.coordVec f c = w ↔ f (Multiplicative.ofAdd w) = c := by
  constructor
  · rintro rfl
    simp [Sec12.coordVec]
  · rintro rfl
    simp [Sec12.coordVec]

theorem wAction_coordVec (n : Subgroup.normalizer (D : Set G)) {y : G} (hy : y ∈ D) :
    Sec12.wAction f n (Sec12.coordVec f ⟨y, hy⟩) =
      Sec12.coordVec f ⟨(n : G) * y * (n : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp n.2 y).mp hy⟩ := by
  have hv : f (Multiplicative.ofAdd (Sec12.coordVec f ⟨y, hy⟩)) = ⟨y, hy⟩ := by
    simp [Sec12.coordVec]
  symm
  rw [coordVec_eq_iff_apply]
  apply Subtype.ext
  rw [Sec12.wAction_apply, hv]

theorem coordVec_zpow {y : G} (hy : y ∈ D) (k : ℤ) :
    Sec12.coordVec f ⟨y ^ k, D.zpow_mem hy k⟩ = (k : ZMod 3) • Sec12.coordVec f ⟨y, hy⟩ := by
  have hpt : (⟨y ^ k, D.zpow_mem hy k⟩ : D) = (⟨y, hy⟩ : D) ^ k := Subtype.ext (by simp)
  unfold Sec12.coordVec
  rw [hpt, map_zpow, toAdd_zpow, Int.cast_smul_eq_zsmul]

theorem coordVec_mul {y z : G} (hy : y ∈ D) (hz : z ∈ D) :
    Sec12.coordVec f ⟨y * z, D.mul_mem hy hz⟩ =
      Sec12.coordVec f ⟨y, hy⟩ + Sec12.coordVec f ⟨z, hz⟩ := by
  have hpt : (⟨y * z, D.mul_mem hy hz⟩ : D) = (⟨y, hy⟩ : D) * ⟨z, hz⟩ := rfl
  unfold Sec12.coordVec
  rw [hpt, map_mul, toAdd_mul]

theorem exists_coordVec_eq (u : V) : ∃ (y : G) (hy : y ∈ D), Sec12.coordVec f ⟨y, hy⟩ = u := by
  exact ⟨(f (Multiplicative.ofAdd u) : G), (f (Multiplicative.ofAdd u)).2,
    (coordVec_eq_iff_apply f).mpr rfl⟩

theorem eq_of_coordVec_eq {y z : G} (hy : y ∈ D) (hz : z ∈ D)
    (h : Sec12.coordVec f ⟨y, hy⟩ = Sec12.coordVec f ⟨z, hz⟩) : y = z := by
  have h' : Multiplicative.toAdd (f.symm ⟨y, hy⟩) = Multiplicative.toAdd (f.symm ⟨z, hz⟩) := h
  have h2 : f.symm ⟨y, hy⟩ = f.symm ⟨z, hz⟩ := Multiplicative.toAdd.injective h'
  exact congrArg Subtype.val (f.symm.injective h2)

theorem wAction_eq_one_iff (n : Subgroup.normalizer (D : Set G)) :
    Sec12.wAction f n = 1 ↔ (n : G) ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h d hd
    have hφ : D.normalizerMonoidHom n = 1 := by
      apply Sec12.coordHom_injective f
      rw [map_one]
      exact h
    have hx : D.normalizerMonoidHom n ⟨d, hd⟩ = ⟨d, hd⟩ := by
      rw [hφ, MulAut.one_apply]
    have h2 : (n : G) * d * (n : G)⁻¹ = d := congrArg Subtype.val hx
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro hn
    have hφ : D.normalizerMonoidHom n = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      show (n : G) * (x : G) * (n : G)⁻¹ = (x : G)
      rw [← hn (x : G) x.2, mul_inv_cancel_right]
    show Sec12.coordHom f (D.normalizerMonoidHom n) = 1
    rw [hφ, map_one]

theorem wAction_coordVec_eq_iff (n : Subgroup.normalizer (D : Set G)) {y : G} (hy : y ∈ D) :
    Sec12.wAction f n (Sec12.coordVec f ⟨y, hy⟩) = Sec12.coordVec f ⟨y, hy⟩ ↔
      (n : G) * y = y * (n : G) := by
  rw [wAction_coordVec]
  constructor
  · intro h
    exact mul_inv_eq_iff_eq_mul.mp (eq_of_coordVec_eq f _ hy h)
  · intro h
    exact congrArg (Sec12.coordVec f) (Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h))

theorem wAction_mem_zpowers [Finite G] {A : Subgroup G}
    (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hcard : Nat.card A = 3 * Nat.card (A ⊓ Subgroup.centralizer (D : Set G) : Subgroup G))
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀D : a₀ ∉ Subgroup.centralizer (D : Set G)) {a : G}
    (ha : a ∈ A) :
    Sec12.wAction f ⟨a, hAD ha⟩ ∈ Subgroup.zpowers (Sec12.wAction f ⟨a₀, hAD ha₀⟩) := by
  let ψ : A →* (V ≃ₗ[ZMod 3] V) := (Sec12.wAction f).comp (Subgroup.inclusion hAD)
  have hψ : ∀ x : A, ψ x = Sec12.wAction f ⟨(x : G), hAD x.2⟩ := fun x => rfl
  have hker : ψ.ker = (A ⊓ Subgroup.centralizer (D : Set G)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hψ, wAction_eq_one_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hkerCard :
      Nat.card ψ.ker = Nat.card (A ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card ψ.range = 3 := by
    have h1 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hkerCard, hcard] at h1
    have hm : 0 < Nat.card (A ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hm (h1.trans (Nat.mul_comm 3 _))
  haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hg : ψ ⟨a₀, ha₀⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hg1 : ψ ⟨a₀, ha₀⟩ ≠ 1 := fun h => ha₀D ((wAction_eq_one_iff f ⟨a₀, hAD ha₀⟩).mp h)
  have hord : orderOf (ψ ⟨a₀, ha₀⟩) = 3 := by
    have hdvd := ψ.range.orderOf_dvd_natCard hg
    rw [hrange] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h1
  have hzp : Subgroup.zpowers (ψ ⟨a₀, ha₀⟩) = ψ.range := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
    exact le_of_eq (by rw [Nat.card_zpowers, hord, hrange])
  show ψ ⟨a, ha⟩ ∈ Subgroup.zpowers (ψ ⟨a₀, ha₀⟩)
  rw [hzp]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

end Coords

section Sylow

variable [Finite G]

theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R K ∧ Q ≤ R := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  have hx' : (⟨x, hQK hx⟩ : K) ∈ Q.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hQK hx⟩, hS hx', rfl⟩

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {Q R K : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ k ∈ K, ∀ q ∈ Q, k⁻¹ * q * k ∈ R := by
  obtain ⟨R', hR', hQR'⟩ := exists_isSylowOf_ge hQK hQ
  obtain ⟨k, hk, hconj⟩ := hR.exists_mem_conj hR'
  exact ⟨k, hk, fun q hq => (hconj q).mp (hQR' hq)⟩

end Sylow

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
