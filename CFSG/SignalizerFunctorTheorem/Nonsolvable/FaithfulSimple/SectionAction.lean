module

public import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed

public section

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type*} [Group G] {K L A : Subgroup G}

noncomputable def sectionConjAut (hAK : A ≤ Subgroup.normalizer (K : Set G)) (a : A) :
    MulAut K :=
  K.normalizerMonoidHom ⟨a, hAK a.2⟩

theorem coe_sectionConjAut (hAK : A ≤ Subgroup.normalizer (K : Set G)) (a : A) (k : K) :
    ((sectionConjAut hAK a k : K) : G) = a * k * (a : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe K _ k

theorem sectionConjAut_mem_iff (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (k : K) :
    ((sectionConjAut hAK a k : K) : G) ∈ L ↔ (k : G) ∈ L := by
  rw [coe_sectionConjAut]
  exact ((Subgroup.mem_normalizer_iff.mp (hAL a.2)) k).symm

theorem map_sectionConjAut_eq (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) :
    (L.subgroupOf K).map (sectionConjAut hAK a : K →* K) = L.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (sectionConjAut_mem_iff hAK hAL a y).mpr hy
  · intro hx
    refine ⟨(sectionConjAut hAK a).symm x, ?_, (sectionConjAut hAK a).apply_symm_apply x⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← sectionConjAut_mem_iff hAK hAL a,
      MulEquiv.apply_symm_apply]
    exact hx

variable [(L.subgroupOf K).Normal]

noncomputable def sectionAction (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : A →* MulAut (K ⧸ L.subgroupOf K) where
  toFun a := QuotientGroup.congr (L.subgroupOf K) (L.subgroupOf K) (sectionConjAut hAK a)
    (map_sectionConjAut_eq hAK hAL a)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_sectionConjAut]
      simp
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      simp only [coe_sectionConjAut, Subgroup.coe_mul]
      group

theorem sectionAction_mk (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (k : K) :
    sectionAction hAK hAL a (QuotientGroup.mk k) = QuotientGroup.mk (sectionConjAut hAK a k) :=
  QuotientGroup.congr_mk _ _ _ (map_sectionConjAut_eq hAK hAL a) k

theorem sectionAction_mk_eq_iff (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (k : K) :
    sectionAction hAK hAL a (QuotientGroup.mk k) = QuotientGroup.mk k ↔
      (k : G)⁻¹ * (a * k * (a : G)⁻¹) ∈ L := by
  rw [sectionAction_mk, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_sectionConjAut]

theorem exists_fixed_mk [Finite G] {p : ℕ} (hp : p.Prime) (hLK : L ≤ K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {a : A} (ha : (a : G) ^ p = 1) (hcop : Nat.Coprime p (Nat.card L))
    {v : K ⧸ L.subgroupOf K} (hv : sectionAction hAK hAL a v = v) :
    ∃ y : K, (a : G) * y * (a : G)⁻¹ = y ∧ QuotientGroup.mk y = v := by
  induction v using QuotientGroup.induction_on with
  | H k =>
    rw [sectionAction_mk_eq_iff] at hv
    have hKH : K ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mp inferInstance
    have hLH : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
    let a' : Subgroup.normalizer (L : Set G) := ⟨a, hAL a.2⟩
    let w : Subgroup.normalizer (L : Set G) := ⟨k, hKH k.2⟩
    have ha' : a' ^ p = 1 := Subtype.ext (by simpa [a'] using ha)
    have hcop' : Nat.Coprime p (Nat.card (L.subgroupOf (Subgroup.normalizer (L : Set G)))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv]
      exact hcop
    have hw : a' * w * a'⁻¹ * w⁻¹ ∈ L.subgroupOf (Subgroup.normalizer (L : Set G)) := by
      rw [Subgroup.mem_subgroupOf]
      have h1 := (Subgroup.mem_normalizer_iff.mp (hKH k.2) _).mp hv
      have h2 : (a : G) * k * (a : G)⁻¹ * (k : G)⁻¹ =
          k * ((k : G)⁻¹ * (a * k * (a : G)⁻¹)) * (k : G)⁻¹ := by group
      simpa [a', w, h2] using h1
    obtain ⟨y, hy1, hy2⟩ := exists_fixed_of_coprime hp ha' _ hcop' hw
    have hyL : (y : G) * (k : G)⁻¹ ∈ L := by
      have := Subgroup.mem_subgroupOf.mp hy1
      simpa [w] using this
    have hyK : (y : G) ∈ K := by
      have : (y : G) = ((y : G) * (k : G)⁻¹) * k := by group
      rw [this]
      exact mul_mem (hLK hyL) k.2
    refine ⟨⟨y, hyK⟩, ?_, ?_⟩
    · have := congrArg Subtype.val hy2
      simpa [a'] using this
    · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h3 : y⁻¹ * w ∈ L.subgroupOf (Subgroup.normalizer (L : Set G)) := by
        have h4 := Subgroup.Normal.conj_mem Subgroup.normal_in_normalizer _ (inv_mem hy1) y⁻¹
        have h5 : y⁻¹ * (y * w⁻¹)⁻¹ * y⁻¹⁻¹ = y⁻¹ * w := by group
        rwa [h5] at h4
      simpa [w] using Subgroup.mem_subgroupOf.mp h3

end CFSG.SignalizerFunctorTheorem
