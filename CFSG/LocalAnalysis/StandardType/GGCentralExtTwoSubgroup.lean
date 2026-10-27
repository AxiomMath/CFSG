module

public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

private theorem sylow_sup_eq_top_of_quotient_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal] (P : Sylow p G)
    (hquot : IsPGroup p (G ⧸ N)) : (P : Subgroup G) ⊔ N = ⊤ := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hquot
  have hNindex : N.index = p ^ a := by rw [Subgroup.index_eq_card, ha]
  have hcop : Nat.Coprime P.index (p ^ a) :=
    (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd P.not_dvd_index
  have hQN : ((P : Subgroup G) ⊔ N).index ∣ N.index := Subgroup.index_dvd_of_le le_sup_right
  have hQP : ((P : Subgroup G) ⊔ N).index ∣ P.index := Subgroup.index_dvd_of_le le_sup_left
  exact Subgroup.index_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hQP (hNindex ▸ hQN))

theorem exists_normal_two_subgroup_of_central_ext {X : Type*} [Group X] [Finite X]
    {N R U : Subgroup X} (hRN : R ≤ N) (hR : ∀ n ∈ N, ∀ x ∈ R, n * x * n⁻¹ ∈ R)
    (hcent : ∀ x ∈ R ⊓ U, ∀ y ∈ R, x * y = y * x)
    (h2 : ∀ y ∈ R, ∃ k : ℕ, y ^ (2 ^ k) ∈ U) :
    ∃ P : Subgroup X, P ≤ R ∧ IsPGroup 2 P ∧ (∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P) ∧
      R ≤ P ⊔ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup R := (R ⊓ U).subgroupOf R
  have hZcenter : Z ≤ Subgroup.center R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact (Subtype.ext
      (hcent z.1 (show (z : X) ∈ R ⊓ U from hz) y.1 y.2)).symm
  haveI : Z.Normal := Subgroup.normal_of_le_center hZcenter
  have hquot : IsPGroup 2 (R ⧸ Z) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z q
    obtain ⟨k, hk⟩ := h2 x.1 x.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨(x ^ 2 ^ k).2, hk⟩
  haveI : Group.IsNilpotent R := by
    haveI : Group.IsNilpotent (R ⧸ Z) := hquot.isNilpotent
    exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk']; exact hZcenter)
  let P0 : Sylow 2 R := Classical.arbitrary _
  haveI : Finite (Sylow 2 R) := Sylow.finite_of_finiteIndex P0
  have hP0normal : (P0 : Subgroup R).Normal := inferInstance
  haveI : Unique (Sylow 2 R) := Sylow.unique_of_normal P0 hP0normal
  have hsuptop : (P0 : Subgroup R) ⊔ Z = ⊤ :=
    sylow_sup_eq_top_of_quotient_isPGroup Z P0 hquot
  let P : Subgroup X := (P0 : Subgroup R).map R.subtype
  have hPR : P ≤ R := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hP2 : IsPGroup 2 P := P0.isPGroup'.map R.subtype
  have hnorm : ∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P := by
    intro n hn x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let φ : R ≃* R :=
      { toFun := fun z => ⟨n * (z : X) * n⁻¹, hR n hn (z : X) z.2⟩
        invFun := fun z => ⟨n⁻¹ * (z : X) * (n⁻¹)⁻¹, hR n⁻¹ (N.inv_mem hn) (z : X) z.2⟩
        left_inv := by intro z; ext; group
        right_inv := by intro z; ext; group
        map_mul' := by intro z w; ext; simp only [Subgroup.coe_mul]; group }
    have hφ : φ y ∈ (P0 : Subgroup R) := by
      have hmem : φ y ∈ (P0 : Subgroup R).map φ.toMonoidHom :=
        Subgroup.mem_map_of_mem φ.toMonoidHom hy
      have hsurj : Function.Surjective ⇑φ.toMonoidHom := fun z => ⟨φ.symm z, by simp⟩
      have heq : Sylow.mapSurjective (f := φ.toMonoidHom) hsurj P0 = P0 :=
        Subsingleton.elim _ _
      rwa [← Sylow.coe_mapSurjective, heq] at hmem
    exact Subgroup.mem_map.mpr ⟨φ y, hφ, rfl⟩
  have hRle : R ≤ P ⊔ U := by
    have htop : ((⊤ : Subgroup R).map R.subtype) = R := by
      ext x
      exact ⟨fun hx => by rcases hx with ⟨y, -, rfl⟩; exact y.2,
        fun hx => ⟨⟨x, hx⟩, trivial, rfl⟩⟩
    have hle : (((P0 : Subgroup R) ⊔ Z).map R.subtype) ≤ P ⊔ U := by
      rw [Subgroup.map_sup]
      refine sup_le le_sup_left ?_
      rintro _ ⟨z, hz, rfl⟩
      exact Subgroup.mem_sup_right (show (z : X) ∈ U from hz.2)
    calc R = ((⊤ : Subgroup R).map R.subtype) := htop.symm
      _ = (((P0 : Subgroup R) ⊔ Z).map R.subtype) := by rw [hsuptop]
      _ ≤ P ⊔ U := hle
  exact ⟨P, hPR, hP2, hnorm, hRle⟩

end CFSG.StandardType
